"""The reproducible private build profile, shared by runner and offline audit."""
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
LOCAL = ('lifetime.h', 'lifetime.cpp', 'native_probe.cpp', 'instrument.py', 'render.py',
         'observation.py', 'profile.py', 'run.py', 'verify.py', 'test_observation.py',
         'test_record.py', 'README.md')
REPOSITORY = tuple('experiments/lean_allocation_lifetimes/' + p for p in LOCAL)
REPOSITORY += tuple('experiments/lean_allocation_diagnostic/' + p for p in (
    'Main.lean', 'probe.c', 'verify.py', 'upstream-sources.json', 'vendor/LICENSE.lean',
    'vendor/lean/runtime/mimalloc.cpp', 'vendor/lean/runtime/alloc.h',
    'vendor/lean/runtime/alloc_tls.h', 'vendor/lean/runtime/debug.h', 'vendor/lean/runtime/exception.h'))
REPOSITORY += tuple('experiments/stock_allocation_capabilities/' + p for p in (
    'verify.py', 'vendor/mimalloc-stats.h', 'vendor/LICENSE.mimalloc'))
REPOSITORY += ('lean-toolchain', 'lean-kernel/lean-toolchain')
CLAIMS = dict(private_block_lifetimes=True, calibrated_startup_live_set=True,
              calibrated_interval_usable_peak=True, timing=False, whole_process_accounting=False,
              physical_backing_peak=False, production_runtime_modified=False,
              source_program_accounting=False, stock_runtime_equivalence=False,
              native_refinement=False, upstream_allocator_sanitized=False)
AUDIT_FAILURE = b'VASTITAS_HEAP_LIFETIME_AUDIT_FAILED\n'


def commands(output, prefix, host):
    """Exact compiler/link commands; arguments are passed directly, never a shell."""
    build = output + '/build'
    source = output + '/inputs/repository/experiments/lean_allocation_lifetimes'
    original = output + '/inputs/repository/experiments/lean_allocation_diagnostic'
    allocator = build + '/mimalloc-3.4.5'
    cc, cxx, ar = (host[k] for k in ('cc', 'cxx', 'ar'))
    lean, leanc = prefix + '/bin/lean', prefix + '/bin/leanc'
    cpp = ['-std=c++20'] + (['-stdlib=libc++'] if host['system'] == 'Linux' else [])
    includes = ['-I' + p for p in (source, allocator + '/include')]
    macros = ['-DMI_STAT=2', '-DMI_PADDING=0', '-DMI_MAX_ALIGN_SIZE=8', '-DMI_SECURE=0',
              '-DMI_SHARED_LIB', '-DMI_SHARED_LIB_EXPORT', '-DVASTITAS_HEAP_LIFETIMES=1']
    cflags = ['-O3', '-Wall', '-Wextra', '-Werror', '-I' + prefix + '/include/lean',
              '-I' + source, '-I' + original]
    map_flag = '-Wl,-map,' if host['system'] == 'Darwin' else '-Wl,-Map,'
    result = {'lean-emit': [lean, '-c', 'Main.c', 'Main.lean']}
    for name in ('main', 'probe'):
        input_name = 'Main.c' if name == 'main' else 'probe.c'
        result[name + '-compile'] = [leanc, *cflags, '-c', build + '/' + input_name,
                                    '-o', build + '/' + name + '.o']
    result['runtime-compile'] = [cxx, *cpp, '-O3', '-DNDEBUG', *macros,
        '-DMI_WIN_NOREDIRECT', '-DLEAN_EXPORTING', '-fPIC', '-fvisibility=hidden',
        '-fvisibility-inlines-hidden', '-ftls-model=local-exec', '-Wno-unused-function',
        '-Wno-deprecated', '-I' + prefix + '/include', '-I' + original + '/vendor/lean',
        *includes, '-I' + allocator + '/src', '-c', original + '/vendor/lean/runtime/mimalloc.cpp',
        '-o', build + '/runtime/mimalloc.cpp.o']
    result['runtime-archive'] = [ar, 'r', build + '/runtime/libleanrt.a', build + '/runtime/mimalloc.cpp.o']
    result['observer-compile'] = [cxx, *cpp, '-O3', '-Wall', '-Wextra', '-Werror', '-c',
                                  source + '/lifetime.cpp', '-o', build + '/lifetime.o']
    result['lean-link'] = [leanc, '-v', '-L' + build + '/runtime', '-L' + prefix + '/lib',
        build + '/main.o', build + '/probe.o', build + '/lifetime.o',
        map_flag + build + '/lean-link.map', '-o', build + '/lean-probe']
    result['native-allocator-compile'] = [cc, '-std=c11', '-O2', '-DNDEBUG', *macros, *includes,
        '-I' + allocator + '/src', '-c', allocator + '/src/static.c', '-o', build + '/native-mimalloc.o']
    result['native-link'] = [cxx, *cpp, '-O2', '-g', '-Wall', '-Wextra', '-Werror', *includes,
        source + '/native_probe.cpp', build + '/lifetime.o', build + '/native-mimalloc.o',
        '-pthread', map_flag + build + '/native-link.map', '-o', build + '/native-probe']
    result['sanitized-link'] = [cxx, *cpp, '-O1', '-g', '-Wall', '-Wextra', '-Werror',
        '-fsanitize=address,undefined', '-fno-sanitize-recover=all', '-fno-omit-frame-pointer',
        *includes, source + '/native_probe.cpp', source + '/lifetime.cpp', build + '/native-mimalloc.o',
        '-pthread', '-o', build + '/sanitized-probe']
    return result
