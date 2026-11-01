"""Pinned, opt-in D/Z GEMM instrumentation; never used by normal builds."""
import hashlib
import re
from experiments.openblas_workspace.patch import patched_memory

PINS = {
    'driver/others/memory.c': '3b5bedc19c4555de21fb0c649177d9be1545d28fc61a8cbcc475e4a9bffc9935',
    'driver/level3/level3.c': 'c48438aa2339a40441906901616dd8bcc2a8122e6bc9e57d61b81841998290a1',
    'driver/level3/gemm.c': '4f434191599394697eb36040ced6a6a81d9746d8c71034a973137e10df89d959',
    'interface/gemm.c': 'c4dcc9c213f54a4acddb559d8bd6effb4ad6fc4d9cd16aabfd04941fd2ee6107',
}


def replace(text, before, after, count=1):
    if text.count(before) != count:
        raise ValueError('changed upstream anchor: ' + before[:80])
    return text.replace(before, after)


def patch(name, original):
    if hashlib.sha256(original).hexdigest() != PINS[name]:
        raise ValueError('unexpected pinned source: ' + name)
    text = original.decode()
    if name == 'driver/others/memory.c':
        return patched_memory(original) + b'\n#include "vpack-observer.c"\n'
    if name == 'driver/level3/gemm.c':
        return replace(text, '#include "level3.c"',
                       '#define VPACK_GEMM_PROFILE 1\n#include "level3.c"').encode()
    if name == 'driver/level3/level3.c':
        pattern = r'^(#define ([IO])COPY_OPERATION\([^\n]*?\) )(GEMM_[A-Z]+)\((.*)\);$'
        def wrap(m):
            role = 0 if m[2] == 'I' else 1
            return f'{m[1]}VPACK_CALL({role}, {m[3]}, {m[4]});'
        text, count = re.subn(pattern, wrap, text, flags=re.M)
        if count != 4:
            raise ValueError('unexpected packing macro count')
        return ('#include "../others/vpack.h"\n' + text).encode()
    # Only actual D/Z CBLAS interfaces activate these macros. Fortran, other
    # precisions and 3M remain unchanged; the object inventory checks this.
    text = replace(text, '#include "common.h"\n',
                   '#include "common.h"\n#include "../driver/others/vpack.h"\n')
    empty = 'if ((args.m == 0) || (args.n == 0)) return;'
    text = replace(text, empty,
                   'if ((args.m == 0) || (args.n == 0)) { VPACK_ROUTE("empty"); VPACK_END(); return; }', 2)
    for operand, ld, vector in (('a','lda','b'), ('b','ldb','a')):
        line = f'GEMV(&NT, &m, &n, args.alpha, args.{operand}, &{ld}, args.{vector}, &inc_x, args.beta, args.c, &inc_y);'
        text = replace(text, line, f'VPACK_ROUTE("gemv");\n        {line}\n        VPACK_END();')
    start = text.index('#if USE_SMALL_MATRIX_OPT\n', text.index('FUNCTION_PROFILE_START();'))
    end = text.index('  buffer = (XFLOAT *)blas_memory_alloc(0);', start)
    small = text[start:end]
    small, count = re.subn(r'(if\(GEMM_SMALL_MATRIX_PERMIT[^\n]+\)\{)',
                           r'\1\n          VPACK_ROUTE("small");', small)
    if count != 2 or small.count('\t  return;') != 2:
        raise ValueError('unexpected small-matrix branches')
    small = small.replace('\t  return;', '\t  VPACK_END();\n\t  return;')
    text = text[:start] + small + text[end:]
    text = replace(text, '  buffer = (XFLOAT *)blas_memory_alloc(0);',
                   '  VPACK_ROUTE("packed");\n  buffer = (XFLOAT *)blas_memory_alloc(0);')
    text = replace(text, ' blas_memory_free(buffer);', ' blas_memory_free(buffer);\n VPACK_END();')
    return text.encode()
