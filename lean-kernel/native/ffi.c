#include "storage.h"
#include <lean/lean.h>
#include <stdatomic.h>

static lean_external_class *arena_class;
static atomic_flag class_lock = ATOMIC_FLAG_INIT;
static void finalize(void *data) { vstorage_delete(data); }
static void foreach(void *data, b_lean_obj_arg function) { (void)data; (void)function; }
/* Registration is synchronized only at arena construction, never per operation
 * or element. Individual arenas have the synchronous, single-caller contract. */
static void initialize_class(void) {
    while (atomic_flag_test_and_set_explicit(&class_lock, memory_order_acquire)) {}
    if (!arena_class) arena_class = lean_register_external_class(finalize, foreach);
    atomic_flag_clear_explicit(&class_lock, memory_order_release);
}
static VStorageArena *arena_data(b_lean_obj_arg arena) { return lean_get_external_data(arena); }
static lean_obj_res result(VStorageStatus status) {
    if (status == VS_OK) return lean_io_result_mk_ok(lean_box(0));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(vstorage_error(status))));
}

/* Lean 4.35 erases the IO world argument. Keep these signatures in agreement
 * with the generated Runtime.c declarations, including borrowed Arena values. */
LEAN_EXPORT lean_obj_res vastitas_storage_new(uint64_t budget) {
    initialize_class();
    VStorageArena *arena = vstorage_new(budget);
    if (!arena) return result(VS_ALLOCATION);
    return lean_io_result_mk_ok(lean_alloc_external(arena_class, arena));
}
LEAN_EXPORT lean_obj_res vastitas_storage_close(b_lean_obj_arg arena) {
    vstorage_close(arena_data(arena));
    return result(VS_OK);
}
LEAN_EXPORT lean_obj_res vastitas_storage_stats(b_lean_obj_arg arena) {
    VStorageStats s = vstorage_stats(arena_data(arena));
    uint64_t values[] = {s.data_allocations, s.data_frees, s.live_bytes, s.peak_bytes,
        s.written_bytes, s.copied_bytes, s.metadata_allocations, s.metadata_bytes};
    lean_object *array = lean_mk_empty_array_with_capacity(lean_box(8));
    for (unsigned i = 0; i < 8; ++i) array = lean_array_push(array, lean_box_uint64(values[i]));
    return lean_io_result_mk_ok(array);
}
LEAN_EXPORT lean_obj_res vastitas_storage_allocate(b_lean_obj_arg arena, uint32_t id, uint8_t scalar, uint64_t elements) {
    return result(vstorage_allocate(arena_data(arena), id, scalar, elements));
}
LEAN_EXPORT lean_obj_res vastitas_storage_drop(b_lean_obj_arg arena, uint32_t id) {
    return result(vstorage_drop(arena_data(arena), id));
}
LEAN_EXPORT lean_obj_res vastitas_storage_fill(b_lean_obj_arg arena, uint32_t id,
        uint64_t offset, uint64_t rows, uint64_t columns, uint64_t leading, uint8_t transposed,
        uint8_t scalar, uint64_t real, uint64_t imaginary) {
    return result(vstorage_fill(arena_data(arena), id, (VStorageLayout){offset,rows,columns,leading,transposed}, scalar, real, imaginary));
}
LEAN_EXPORT lean_obj_res vastitas_storage_store(b_lean_obj_arg arena, uint32_t id,
        uint64_t offset, uint64_t rows, uint64_t columns, uint64_t leading, uint8_t transposed,
        uint64_t row, uint64_t column, uint8_t scalar, uint64_t real, uint64_t imaginary) {
    return result(vstorage_store(arena_data(arena), id, (VStorageLayout){offset,rows,columns,leading,transposed}, row, column, scalar, real, imaginary));
}
LEAN_EXPORT lean_obj_res vastitas_storage_expect(b_lean_obj_arg arena, uint32_t id,
        uint64_t offset, uint64_t rows, uint64_t columns, uint64_t leading, uint8_t transposed,
        uint64_t row, uint64_t column, uint8_t scalar, uint64_t real, uint64_t imaginary) {
    return result(vstorage_expect(arena_data(arena), id, (VStorageLayout){offset,rows,columns,leading,transposed}, row, column, scalar, real, imaginary));
}
LEAN_EXPORT lean_obj_res vastitas_storage_copy(b_lean_obj_arg arena, uint32_t source,
        uint64_t source_offset, uint64_t source_rows, uint64_t source_columns, uint64_t source_leading, uint8_t source_transposed,
        uint32_t target, uint64_t target_offset, uint64_t target_rows, uint64_t target_columns, uint64_t target_leading, uint8_t target_transposed) {
    return result(vstorage_copy(arena_data(arena), source,
        (VStorageLayout){source_offset,source_rows,source_columns,source_leading,source_transposed}, target,
        (VStorageLayout){target_offset,target_rows,target_columns,target_leading,target_transposed}));
}
LEAN_EXPORT lean_obj_res vastitas_storage_pack3(b_lean_obj_arg arena, uint32_t source,
        uint64_t source_offset, uint64_t source_rows, uint64_t source_columns, uint64_t source_leading, uint8_t source_transposed,
        uint32_t target, uint64_t target_offset, uint64_t target_rows, uint64_t target_columns, uint64_t target_leading, uint8_t target_transposed,
        uint64_t i, uint64_t k, uint64_t j) {
    return result(vstorage_pack3(arena_data(arena), source,
        (VStorageLayout){source_offset,source_rows,source_columns,source_leading,source_transposed}, target,
        (VStorageLayout){target_offset,target_rows,target_columns,target_leading,target_transposed}, i, k, j));
}
LEAN_EXPORT lean_obj_res vastitas_storage_regroup3(b_lean_obj_arg arena, uint32_t source,
        uint64_t source_offset, uint64_t source_rows, uint64_t source_columns, uint64_t source_leading, uint8_t source_transposed,
        uint32_t target, uint64_t target_offset, uint64_t target_rows, uint64_t target_columns, uint64_t target_leading, uint8_t target_transposed,
        uint64_t d0, uint64_t d1, uint64_t d2, uint64_t input_grouping, uint64_t output_grouping) {
    return result(vstorage_regroup3(arena_data(arena), source,
        (VStorageLayout){source_offset,source_rows,source_columns,source_leading,source_transposed}, target,
        (VStorageLayout){target_offset,target_rows,target_columns,target_leading,target_transposed},
        d0, d1, d2, input_grouping, output_grouping));
}
