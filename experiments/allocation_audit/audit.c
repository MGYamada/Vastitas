/* Allocation-only observer. No clock or dynamic logging allocation. */
#define AUDIT_IMPLEMENTATION
#include "audit.h"
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#ifndef AUDIT_PERSISTENT
#define AUDIT_PERSISTENT 0
#endif

enum { STARTUP, COLD, SETUP, RUN, CLEANUP, PHASES };
enum { IO_OK, EXTERNAL, GENERATED_CTOR, CONTROL, IO_ERROR, PERSISTENT, KINDS };
static const char *phase_names[] = {"startup", "cold", "setup", "run", "cleanup"};
static const char *kind_names[] = {"ffi_ok", "arena_external", "generated_ctor", "control", "ffi_error", "persistent_unit"};
typedef struct { uint64_t allocations, bytes, final_releases, released_bytes, retained_returns; } Counts;
typedef struct { lean_object *object; size_t bytes; unsigned kind; } Entry;
static Counts counts[PHASES][KINDS];
static Entry live[4096];
static unsigned phase;
static uint64_t finalized[PHASES], peak_bytes, current_bytes;
static uint64_t cycles[PHASES][8];
static lean_object *unit;
lean_obj_res allocation_persistent_unit(void);
static void require(int valid) { if (!valid) { fputs("allocation audit contract failure\n", stderr); abort(); } }

static lean_object *record(lean_object *object, unsigned kind) {
    require(!lean_is_scalar(object));
    /* Argument-list/module setup is consumed inside uninstrumented runtime
     * code, so it is outside this deliberately bounded observation window. */
    if (phase == STARTUP) return object;
    size_t size = lean_object_byte_size(object);
    for (size_t i = 0; i < 4096; ++i) require(live[i].object != object);
    for (size_t i = 0; i < 4096; ++i) {
        if (!live[i].object) {
            live[i] = (Entry){object, size, kind};
            ++counts[phase][kind].allocations; counts[phase][kind].bytes += size;
            current_bytes += size;
            if (current_bytes > peak_bytes) peak_bytes = current_bytes;
            return object;
        }
    }
    require(0); return object;
}
static void release(lean_object *object) {
    if (lean_is_scalar(object) || !lean_is_exclusive(object)) return;
    for (size_t i = 0; i < 4096; ++i) if (live[i].object == object) {
        ++counts[phase][live[i].kind].final_releases;
        counts[phase][live[i].kind].released_bytes += live[i].bytes;
        current_bytes -= live[i].bytes; live[i].object = NULL; return;
    }
}
void audit_phase(unsigned next) { require(next < PHASES); phase = next; }
void audit_finalize(void *data) { require(data != NULL); ++finalized[phase]; }
void audit_arena_cycle(uint64_t allocations, uint64_t frees, uint64_t peak,
        uint64_t written, uint64_t copied, uint64_t metadata, uint64_t metadata_peak) {
    require(allocations == frees);
    uint64_t *c = cycles[phase];
    ++c[0]; c[1] += allocations; c[2] += frees;
    if (peak > c[3]) c[3] = peak;
    c[4] += written; c[5] += copied; c[6] += metadata;
    if (metadata_peak > c[7]) c[7] = metadata_peak;
}
lean_obj_res audit_ok(lean_obj_arg value) {
    if (AUDIT_PERSISTENT && value == lean_box(0)) {
        lean_object *shared = allocation_persistent_unit();
        if (!unit) unit = record(shared, PERSISTENT);
        require(unit == shared);
        ++counts[phase][PERSISTENT].retained_returns;
        return shared;
    }
    return record(lean_io_result_mk_ok(value), IO_OK);
}
lean_obj_res audit_control_ok(lean_obj_arg value) { return record(lean_io_result_mk_ok(value), CONTROL); }
lean_obj_res audit_error(lean_obj_arg value) { return record(lean_io_result_mk_error(value), IO_ERROR); }
lean_obj_res audit_ctor(unsigned tag, unsigned objects, unsigned scalars) {
    return record(lean_alloc_ctor(tag, objects, scalars), GENERATED_CTOR);
}
lean_obj_res audit_external(lean_external_class *cls, void *data) { return record(lean_alloc_external(cls, data), EXTERNAL); }
void audit_dec(lean_obj_arg value) { release(value); lean_dec(value); }
void audit_dec_ref(lean_obj_arg value) { release(value); lean_dec_ref(value); }
void audit_dec_known(lean_obj_arg value, unsigned fields) { release(value); lean_dec_ref_known(value, fields); }
LEAN_EXPORT lean_obj_res audit_mark_lean(uint32_t next) { audit_phase(next); return audit_control_ok(lean_box(0)); }

void audit_report(void) {
    unsigned retained = 0;
    for (size_t i = 0; i < 4096; ++i) if (live[i].object) {
        if (live[i].kind != PERSISTENT || !lean_is_persistent(live[i].object))
            fprintf(stderr, "unreleased tracked object kind=%s bytes=%zu phase=%s\n", kind_names[live[i].kind], live[i].bytes, phase_names[phase]);
        require(live[i].kind == PERSISTENT && lean_is_persistent(live[i].object)); ++retained;
    }
    if (retained != (unsigned)AUDIT_PERSISTENT || current_bytes != (AUDIT_PERSISTENT ? 16 : 0))
        fprintf(stderr, "retained=%u mode=%u bytes=%" PRIu64 "\n",retained,(unsigned)AUDIT_PERSISTENT,current_bytes);
    require(retained == (unsigned)AUDIT_PERSISTENT);
    require(current_bytes == (AUDIT_PERSISTENT ? 16 : 0));
    printf("{\"audit\":true,\"persistent_experiment\":%s,\"tracked_live_bytes\":%" PRIu64 ",\"tracked_peak_bytes\":%" PRIu64 ",\"phases\":{", AUDIT_PERSISTENT ? "true" : "false",current_bytes,peak_bytes);
    for (unsigned p = 0; p < PHASES; ++p) {
        uint64_t *a = cycles[p];
        printf("%s\"%s\":{\"arena_finalizers\":%" PRIu64 ",\"closed_arena_cycles\":%" PRIu64 ",\"arena_allocations\":%" PRIu64 ",\"arena_frees\":%" PRIu64 ",\"arena_peak_bytes\":%" PRIu64 ",\"arena_written_bytes\":%" PRIu64 ",\"arena_copied_bytes\":%" PRIu64 ",\"arena_metadata_allocations\":%" PRIu64 ",\"arena_peak_metadata_bytes\":%" PRIu64 ",\"kinds\":{",p ? "," : "",phase_names[p],finalized[p],a[0],a[1],a[2],a[3],a[4],a[5],a[6],a[7]);
        for (unsigned k = 0; k < KINDS; ++k) {
            Counts c = counts[p][k];
            printf("%s\"%s\":{\"allocations\":%" PRIu64 ",\"bytes\":%" PRIu64 ",\"final_releases\":%" PRIu64 ",\"released_bytes\":%" PRIu64 ",\"retained_returns\":%" PRIu64 "}",k ? "," : "",kind_names[k],c.allocations,c.bytes,c.final_releases,c.released_bytes,c.retained_returns);
        }
        printf("}}");
    }
    printf("}}\n");
}
