"""Deterministic diagnostic patches to the checksum-pinned mimalloc source.

The original release archive remains retained. Changes add observation calls;
they do not replace allocation, free, reallocation or heap-transfer decisions.
The caller must first use the existing checksum/regular-member extractor.
"""
import hashlib
from pathlib import Path


TRACK = '''#elif defined(VASTITAS_HEAP_LIFETIMES)
#include "lifetime.h"
#define MI_TRACK_ENABLED 1
#define MI_TRACK_HEAP_DESTROY 1
#define MI_TRACK_TOOL "vastitas-heap-lifetimes"
#define mi_track_malloc_size(p,reqsize,size,zero) \\
  vastitas_heap_alloc(p,reqsize,size,mi_page_heap(_mi_ptr_page(p)))
#define mi_track_free_size(p,size) vastitas_heap_free(p,size)
#define mi_track_resize(p,oldsize,newsize) vastitas_heap_resize(p,oldsize,newsize)
#define mi_track_align(p,alignedp,offset,size) vastitas_heap_align(p,alignedp,offset)
#else
// no tracking'''

PATCHES = (
    ('include/mimalloc/track.h', '#else\n// no tracking', TRACK),
    ('src/alloc.c', '// mi_track_resize(p,size,newsize)',
     '#if defined(VASTITAS_HEAP_LIFETIMES)\n'
     '        mi_track_resize(p,size,newsize);\n        #endif'),
    ('src/alloc.c', '  return p; // it fits',
     '  #if defined(VASTITAS_HEAP_LIFETIMES)\n'
     '  mi_track_resize(p,size,newsize);\n  #endif\n  return p; // it fits'),
    ('src/alloc-aligned.c',
     '    return p;  // reallocation still fits, is aligned and not more than 50% waste',
     '    #if defined(VASTITAS_HEAP_LIFETIMES)\n'
     '    mi_track_resize(p,size,newsize);\n    #endif\n'
     '    return p;  // reallocation still fits, is aligned and not more than 50% waste'),
    ('src/heap.c', '  _mi_heap_move_pages(heap, heap_main);',
     '  _mi_heap_move_pages(heap, heap_main);\n'
     '  #if defined(VASTITAS_HEAP_LIFETIMES)\n'
     '  vastitas_heap_rehome(heap, heap_main);\n  #endif'),
    ('src/heap.c', '  _mi_heap_destroy_pages(heap);',
     '  #if defined(VASTITAS_HEAP_LIFETIMES)\n'
     '  vastitas_heap_destroy(heap);\n  #endif\n  _mi_heap_destroy_pages(heap);'),
)


def transformed(originals):
    """Return the complete expected modified files, rejecting mismatched inputs."""
    result = dict(originals)
    for name, before, after in PATCHES:
        source = result[name]
        if source.count(before) != 1:
            raise ValueError('lifetime hook anchor differs: ' + name)
        result[name] = source.replace(before, after)
    return result


def apply(directory):
    directory = Path(directory)
    originals = {name: (directory / name).read_text() for name, _, _ in PATCHES}
    changed = transformed(originals)
    receipts = {}
    for name, source in changed.items():
        (directory / name).write_text(source)
        receipts[name] = {
            'before_sha256': hashlib.sha256(originals[name].encode()).hexdigest(),
            'after_sha256': hashlib.sha256(source.encode()).hexdigest(),
        }
    return receipts
