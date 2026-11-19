//! Host adapter for the pinned libLLVM. Only the caller establishes that
//! `verified` came from the checked compilation of the current input.
use llvm_sys::{analysis::*, core::*, ir_reader::*, prelude::*, target::*, target_machine::*};
use std::ffi::{CStr, CString, c_char};
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::Path;
use std::ptr;
use std::sync::OnceLock;

struct Machine(LLVMTargetMachineRef);
struct Context(LLVMContextRef);
struct Module(LLVMModuleRef);
struct Buffer(LLVMMemoryBufferRef);

impl Drop for Machine {
    fn drop(&mut self) {
        unsafe { LLVMDisposeTargetMachine(self.0) }
    }
}
impl Drop for Context {
    fn drop(&mut self) {
        unsafe { LLVMContextDispose(self.0) }
    }
}
impl Drop for Module {
    fn drop(&mut self) {
        unsafe { LLVMDisposeModule(self.0) }
    }
}
impl Drop for Buffer {
    fn drop(&mut self) {
        unsafe { LLVMDisposeMemoryBuffer(self.0) }
    }
}

unsafe fn take_message(value: *mut c_char) -> String {
    if value.is_null() {
        return "LLVM returned no diagnostic".into();
    }
    let text = unsafe { CStr::from_ptr(value).to_string_lossy().into_owned() };
    unsafe { LLVMDisposeMessage(value) };
    text
}

fn native_triple() -> Result<&'static CString, String> {
    static TRIPLE: OnceLock<Result<CString, String>> = OnceLock::new();
    TRIPLE
        .get_or_init(|| unsafe {
            let (mut major, mut minor, mut patch) = (0, 0, 0);
            LLVMGetVersion(&mut major, &mut minor, &mut patch);
            if (major, minor, patch) != (23, 1, 4) {
                return Err(format!(
                    "expected LLVM 23.1.4, linked {major}.{minor}.{patch}"
                ));
            }
            if LLVM_InitializeNativeTarget() != 0 || LLVM_InitializeNativeAsmPrinter() != 0 {
                return Err("cannot initialize LLVM native target".into());
            }
            let triple = LLVMGetDefaultTargetTriple();
            if triple.is_null() {
                return Err("missing LLVM native target triple".into());
            }
            let copy = CStr::from_ptr(triple).to_owned();
            LLVMDisposeMessage(triple);
            Ok(copy)
        })
        .as_ref()
        .map_err(String::clone)
}

impl Machine {
    fn new(triple: &CStr) -> Result<Self, String> {
        unsafe {
            let mut target = ptr::null_mut();
            let mut error = ptr::null_mut();
            if LLVMGetTargetFromTriple(triple.as_ptr(), &mut target, &mut error) != 0 {
                return Err(take_message(error));
            }
            let machine = LLVMCreateTargetMachine(
                target,
                triple.as_ptr(),
                c"generic".as_ptr(),
                c"".as_ptr(),
                LLVMCodeGenOptLevel::LLVMCodeGenLevelNone,
                LLVMRelocMode::LLVMRelocPIC,
                LLVMCodeModel::LLVMCodeModelDefault,
            );
            if machine.is_null() {
                return Err("cannot create LLVM target machine".into());
            }
            Ok(Self(machine))
        }
    }
    fn layout(&self) -> String {
        unsafe {
            let data = LLVMCreateTargetDataLayout(self.0);
            let layout = take_message(LLVMCopyStringRepOfTargetData(data));
            LLVMDisposeTargetData(data);
            layout
        }
    }
}

/// Target contract that the caller sends to the independent checker.
pub(super) fn host_target() -> Result<(String, String), String> {
    let triple = native_triple()?;
    let layout = Machine::new(triple)?.layout();
    Ok((
        triple
            .to_str()
            .map_err(|_| "non-UTF-8 LLVM target triple")?
            .into(),
        layout,
    ))
}

fn checked_readback(verified: &[u8], handoff: &Path) -> Result<CString, String> {
    // Read at most one extra byte, sufficient to reject every longer file.
    let limit = u64::try_from(verified.len())
        .ok()
        .and_then(|n| n.checked_add(1))
        .ok_or("LLVM input length overflow")?;
    let mut bytes = Vec::new();
    File::open(handoff)
        .and_then(|file| file.take(limit).read_to_end(&mut bytes))
        .map_err(|e| format!("cannot read LLVM handoff: {e}"))?;
    // Make the sentinel required by LLVM's text reader *before* comparison.
    // It is outside the compared range and is not included in the IR length.
    let input = CString::new(bytes).map_err(|_| "NUL in LLVM handoff")?;
    if input.as_bytes() != verified {
        return Err("complete LLVM byte comparison failed".into());
    }
    Ok(input)
}

/// The output is a new object in the driver's private build directory.
pub(super) fn emit_object(verified: &[u8], handoff: &Path, output: &Path) -> Result<(), String> {
    let input = checked_readback(verified, handoff)?;
    let triple = native_triple()?;
    let machine = Machine::new(triple)?;
    // The memory range borrows input, remains NUL-terminated, and outlives
    // the parsed module. No backend file re-open or text re-encoding occurs.
    let object = unsafe {
        let context = Context(LLVMContextCreate());
        let buffer = Buffer(LLVMCreateMemoryBufferWithMemoryRange(
            input.as_ptr(),
            input.as_bytes().len(),
            c"checked.ll".as_ptr(),
            1,
        ));
        let mut module = ptr::null_mut();
        let mut error = ptr::null_mut();
        if LLVMParseIRInContext2(context.0, buffer.0, &mut module, &mut error) != 0 {
            return Err(take_message(error));
        }
        let module = Module(module);
        if CStr::from_ptr(LLVMGetTarget(module.0)) != triple.as_c_str() {
            return Err("module target does not equal selected target".into());
        }
        if CStr::from_ptr(LLVMGetDataLayoutStr(module.0)).to_bytes() != machine.layout().as_bytes()
        {
            return Err("module layout does not equal selected layout".into());
        }
        if LLVMVerifyModule(
            module.0,
            LLVMVerifierFailureAction::LLVMReturnStatusAction,
            &mut error,
        ) != 0
        {
            return Err(take_message(error));
        }
        if !error.is_null() {
            LLVMDisposeMessage(error);
        }
        let mut error = ptr::null_mut();
        let mut object = ptr::null_mut();
        if LLVMTargetMachineEmitToMemoryBuffer(
            machine.0,
            module.0,
            LLVMCodeGenFileType::LLVMObjectFile,
            &mut error,
            &mut object,
        ) != 0
        {
            return Err(take_message(error));
        }
        Buffer(object)
    };
    let bytes = unsafe {
        std::slice::from_raw_parts(
            LLVMGetBufferStart(object.0).cast::<u8>(),
            LLVMGetBufferSize(object.0),
        )
    };
    let mut file =
        File::create_new(output).map_err(|e| format!("cannot create LLVM object: {e}"))?;
    if let Err(e) = file.write_all(bytes) {
        drop(file);
        let _ = fs::remove_file(output);
        return Err(format!("cannot write LLVM object: {e}"));
    }
    Ok(())
}
