"""Negative controls for disabled assertions and recoverable sanitizer errors."""
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest

from native_sanitizers import FLAGS

ROOT = Path(__file__).resolve().parents[1]


class VerificationExecution(unittest.TestCase):
    def test_optimized_python_cannot_enter_assertion_based_verifiers(self):
        paths = ['scripts/check_storage_native.py', 'scripts/check_gemm_checked.py',
                 'scripts/check_resource_cleanup.py', 'experiments/allocation_audit/verify.py',
                 'experiments/allocation_audit/run.py', 'experiments/runtime_shapes/verify.py',
                 'experiments/iterator_prefix/model.py']
        for path in paths:
            if not (ROOT / path).exists():
                # The no-mathlib CI checkout intentionally excludes experiments.
                self.assertTrue(path.startswith('experiments/'), path)
                continue
            for mode in ('-O', '-OO', 'environment'):
                with self.subTest(path=path, mode=mode):
                    env = dict(os.environ)
                    command = [sys.executable]
                    if mode == 'environment':
                        env['PYTHONOPTIMIZE'] = '1'
                    else:
                        command.append(mode)
                    result = subprocess.run([*command, str(ROOT/path), '--help'],
                                            env=env, capture_output=True, text=True, timeout=10)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn('verification requires Python assertions', result.stderr)

    def test_native_undefined_behavior_is_fatal_even_if_environment_requests_recovery(self):
        probes = {
            'overflow': '#include <limits.h>\nint main(int n, char **v) { (void)v; volatile int x=INT_MAX; x+=n; return x==0; }',
            'alignment': 'int main(int n, char **v) { (void)v; _Alignas(16) char data[32]={0}; double *p=(double *)(data+n); return *p!=0; }',
            'shift': '#include <stdint.h>\nint main(int n, char **v) { (void)v; volatile uint64_t x=1, shift=(uint64_t)n+63; return (int)(x<<shift); }',
        }
        with tempfile.TemporaryDirectory(prefix='vastitas-ubsan-control-') as directory:
            work = Path(directory)
            for name, source in probes.items():
                with self.subTest(probe=name):
                    path, binary = work/(name+'.c'), work/name
                    path.write_text(source)
                    subprocess.run([*shlex.split(os.environ.get('CC','cc')), '-std=c11', '-O1',
                                    '-Wall', '-Wextra', '-Werror', *FLAGS, str(path), '-o', str(binary)],
                                   check=True, capture_output=True, text=True, timeout=30)
                    result = subprocess.run([str(binary)], capture_output=True, text=True, timeout=10,
                                            env=dict(os.environ, UBSAN_OPTIONS='halt_on_error=0'))
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn('runtime error:', result.stderr)


if __name__ == '__main__':
    unittest.main()
