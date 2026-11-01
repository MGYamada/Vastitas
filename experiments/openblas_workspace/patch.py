"""Exact-source diagnostic patch. Never used by ordinary builds."""
import hashlib
from pathlib import Path
import re

MEMORY_SHA256 = '3b5bedc19c4555de21fb0c649177d9be1545d28fc61a8cbcc475e4a9bffc9935'
HERE = Path(__file__).resolve().parent


def patched_memory(original: bytes) -> bytes:
    if hashlib.sha256(original).hexdigest() != MEMORY_SHA256:
        raise ValueError('memory.c is not from the pinned release archive')
    text = original.decode()
    for name in ('blas_memory_alloc', 'blas_memory_free', 'blas_memory_alloc_nolock',
                 'blas_memory_free_nolock', 'blas_shutdown'):
        text, count = re.subn(r'^(void (?:\*)?)' + name + r'\(',
                             r'\1vobs_real_' + name + '(', text, flags=re.M)
        if count != 2:  # one definition in each conditional TLS branch
            raise ValueError(f'Unexpected definitions for {name}: {count}')
    counts = {'malloc': 7, 'free': 6, 'mmap': 14, 'munmap': 12}
    for name, expected in counts.items():
        text, count = re.subn(r'\b' + name + r'\(', 'vobs_' + name + '(', text)
        if count != expected:
            raise ValueError(f'Unexpected call sites for {name}: {count}')
    anchor = '#include "common.h"\n'
    if text.count(anchor) != 1:
        raise ValueError('common.h anchor changed')
    text = text.replace(anchor, anchor + '#include "vobs-observer.c"\n')
    text += '\n#include "vobs-wrappers.c"\n'
    return text.encode()
