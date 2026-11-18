//! Toolchain qualification. The expected bytes here come from a fixture.
#[path = "../../../../src/driver/llvm_backend.rs"]
mod backend;

use std::{env, fs, path::Path};

fn run() -> Result<(), String> {
    let args: Vec<_> = env::args_os().skip(1).collect();
    match args.as_slice() {
        [command] if command == "describe" => {
            let (triple, layout) = backend::host_target()?;
            println!("llvm=23.1.4\ntriple={triple}\nlayout={layout}");
            Ok(())
        }
        [command, authorized, handoff, output] if command == "emit" => {
            let expected =
                fs::read(authorized).map_err(|_| "cannot read authorized fixture bytes")?;
            backend::emit_object(&expected, Path::new(handoff), Path::new(output))
        }
        _ => Err(
            "usage: vastitas-llvm-qualification describe | emit AUTHORIZED.ll HANDOFF.ll OUTPUT.o"
                .into(),
        ),
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("E_LLVM_QUALIFICATION: {error}");
        std::process::exit(1);
    }
}
