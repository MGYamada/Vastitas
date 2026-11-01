"""Extend the existing public-Lean-API calibration with lifetime snapshots.

The allocation/release workloads themselves are retained byte for byte. Replay
must reconstruct this complete emitted C from its retained original input.
"""

METRICS = (
    'allocations', 'frees', 'bulk_frees', 'resizes', 'aligns', 'rehomes',
    'allocated_requests', 'resize_requests', 'allocated_usable', 'freed_usable',
    'live_blocks', 'live_usable', 'peak_usable', 'interval_peak_usable',
)


def replace_once(text, before, after):
    if text.count(before) != 1:
        raise ValueError('Lean lifetime probe anchor differs: ' + before[:80])
    return text.replace(before, after)


def lean_probe(original):
    source = '#include "lifetime.h"\n' + original
    source = replace_once(source, '  mi_stats_t stats;',
                          '  VastitasHeapLifetimes lifetime_before, lifetime_after;\n  mi_stats_t stats;')
    source = replace_once(source, '  s->workload = workload; s->phase = phase;',
                          '  s->lifetime_before = vastitas_heap_snapshot();\n'
                          '  s->workload = workload; s->phase = phase;')
    source = replace_once(source,
        '  s->json_ok = mi_stats_as_json(&s->stats, sizeof(s->json), s->json) == s->json;',
        '  s->json_ok = mi_stats_as_json(&s->stats, sizeof(s->json), s->json) == s->json;\n'
        '  s->lifetime_after = vastitas_heap_checkpoint();')
    helper = '''static void print_lifetime(const VastitasHeapLifetimes *s) {
  putchar('{');
'''
    for i, name in enumerate(METRICS):
        helper += f'  printf("{"," if i else ""}\\"{name}\\":%" PRIu64, s->{name});\n'
    helper += "  putchar('}');\n}\n\n"
    source = replace_once(source, 'lean_obj_res lean_allocator_diagnostic_probe(void) {',
                          helper + 'lean_obj_res lean_allocator_diagnostic_probe(void) {')
    source = replace_once(source, '    const Snapshot *s = &snapshots[i];', '''    const Snapshot *s = &snapshots[i];
    ok = ok && memcmp(&s->lifetime_before, &s->lifetime_after, sizeof(s->lifetime_before)) == 0;
    ok = ok && s->lifetime_after.live_blocks == s->blocks && s->lifetime_after.live_usable == s->block_bytes;
    printf("{\\"kind\\":\\"heap_lifetime\\",\\"workload\\":\\"%s\\",\\"phase\\":\\"%s\\",\\"before\\":", s->workload, s->phase);
    print_lifetime(&s->lifetime_before);
    printf(",\\"after\\":"); print_lifetime(&s->lifetime_after); puts("}");''')
    source = replace_once(source, '  return lean_io_result_mk_ok(lean_box_uint32(ok ? 0 : 1));', '''  printf("{\\"kind\\":\\"heap_lifetime_configuration\\",\\"schema\\":1,\\"observer_static_bytes\\":%zu,\\"capacity\\":%zu}\\n",
    vastitas_heap_observer_bytes(), vastitas_heap_observer_capacity());
  return lean_io_result_mk_ok(lean_box_uint32(ok ? 0 : 1));''')
    return source
