#include "storage.h"
#include <float.h>
#include <limits.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

_Static_assert(sizeof(double) == 8 && FLT_RADIX == 2 && DBL_MANT_DIG == 53 && DBL_MAX_EXP == 1024,
               "storage requires binary64 double");
_Static_assert(sizeof(void *) == 8 && SIZE_MAX >= INT64_MAX && PTRDIFF_MAX >= INT64_MAX,
               "storage requires the 64-bit pointer/offset profile");
_Static_assert(_Alignof(max_align_t) >= 8, "malloc must provide binary64 alignment");

typedef struct {
    double *data;
    uint64_t capacity;
    uint8_t scalar, issued, live;
} Buffer;

struct VStorageArena {
    Buffer *buffers;
    uint32_t count;
    uint8_t closed;
    uint64_t budget;
    VStorageStats stats;
};

typedef struct {
    Buffer *buffer;
    uint64_t start, end, rows, columns, row_step, column_step, components, bytes;
} Prepared;

static int add(uint64_t a, uint64_t b, uint64_t *out) {
    if (b > INT64_MAX || a > (uint64_t)INT64_MAX - b) return 0;
    *out = a + b;
    return 1;
}
static int multiply(uint64_t a, uint64_t b, uint64_t *out) {
    if (b && a > (uint64_t)INT64_MAX / b) return 0;
    *out = a * b;
    return 1;
}
static int counter_fits(uint64_t value, uint64_t extra) { return extra <= UINT64_MAX - value; }

VStorageArena *vstorage_new(uint64_t byte_budget) {
    if (byte_budget > INT64_MAX) return NULL;
    VStorageArena *arena = calloc(1, sizeof(*arena));
    if (arena) {
        arena->budget = byte_budget;
        arena->stats.metadata_allocations = 1;
        arena->stats.metadata_bytes = sizeof(*arena);
    }
    return arena;
}

static Buffer *lookup(VStorageArena *arena, uint32_t id) {
    if (!arena || arena->closed || id >= arena->count || !arena->buffers[id].live) return NULL;
    return &arena->buffers[id];
}

VStorageStatus vstorage_drop(VStorageArena *arena, uint32_t id) {
    Buffer *buffer = lookup(arena, id);
    if (!buffer) return VS_HANDLE;
    if (buffer->data) {
        free(buffer->data);
        ++arena->stats.data_frees;
    }
    arena->stats.live_bytes -= buffer->capacity;
    buffer->data = NULL;
    buffer->live = 0;
    return VS_OK;
}

void vstorage_close(VStorageArena *arena) {
    if (!arena || arena->closed) return;
    for (uint32_t id = 0; id < arena->count; ++id)
        if (arena->buffers[id].live) (void)vstorage_drop(arena, id);
    arena->closed = 1;
}

void vstorage_delete(VStorageArena *arena) {
    if (!arena) return;
    vstorage_close(arena);
    free(arena->buffers);
    free(arena);
}

VStorageStats vstorage_stats(const VStorageArena *arena) {
    return arena ? arena->stats : (VStorageStats){0};
}

const char *vstorage_error(VStorageStatus status) {
    switch (status) {
    case VS_OK: return "ok";
    case VS_ALLOCATION: return "E_NATIVE_ALLOCATION: allocation or live-byte budget failed";
    case VS_HANDLE: return "E_NATIVE_HANDLE: allocation is absent, closed or already issued";
    case VS_SCALAR: return "E_NATIVE_SCALAR: scalar representation mismatch";
    case VS_LAYOUT: return "E_NATIVE_LAYOUT: invalid layout, bounds, alignment or narrowing";
    case VS_OVERFLOW: return "E_NATIVE_OVERFLOW: native size or accounting overflow";
    case VS_BOUNDS: return "E_NATIVE_BOUNDS: cell index is outside the view";
    case VS_ALIAS: return "E_NATIVE_ALIAS: accessed regions may overlap";
    case VS_EXPECT: return "E_NATIVE_EXPECT: stored bit pattern differs";
    case VS_ABI: return "E_NATIVE_ABI: unsupported numerical backend version, ABI or threading";
    case VS_SHAPE: return "E_NATIVE_SHAPE: numerical operand dimensions differ";
    case VS_OPERATION: return "E_NATIVE_OPERATION: unsupported numerical operation or layout";
    }
    return "E_NATIVE_STATUS: unknown status";
}

VStorageStatus vstorage_allocate(VStorageArena *arena, uint32_t id, uint8_t scalar, uint64_t elements) {
    if (!arena || arena->closed || id >= 4096 || (id < arena->count && arena->buffers[id].issued))
        return VS_HANDLE;
    if (scalar > 1) return VS_SCALAR;
    uint64_t capacity;
    if (!multiply(elements, scalar ? 16 : 8, &capacity)) return VS_OVERFLOW;
    if (capacity > arena->budget - arena->stats.live_bytes) return VS_ALLOCATION;
    if (id >= arena->count) {
        uint32_t count = arena->count ? arena->count : 8;
        while (count <= id) count *= 2;
        Buffer *buffers = realloc(arena->buffers, count * sizeof(*buffers));
        if (!buffers) return VS_ALLOCATION;
        memset(buffers + arena->count, 0, (count - arena->count) * sizeof(*buffers));
        arena->buffers = buffers;
        arena->count = count;
        ++arena->stats.metadata_allocations;
        arena->stats.metadata_bytes = sizeof(*arena) + count * sizeof(*buffers);
    }
    /* Zero-size allocations form no data pointer and call no malloc(0). */
    double *data = capacity ? malloc((size_t)capacity) : NULL;
    if (capacity && !data) return VS_ALLOCATION;
    arena->buffers[id] = (Buffer){data, capacity, scalar, 1, 1};
    arena->stats.data_allocations += capacity != 0;
    arena->stats.live_bytes += capacity;
    if (arena->stats.live_bytes > arena->stats.peak_bytes) arena->stats.peak_bytes = arena->stats.live_bytes;
    return VS_OK;
}

/* Prepare all metadata before any pointer addition or element access. A
 * Prepared record is local to this synchronous call, not a reusable receipt. */
static VStorageStatus prepare(VStorageArena *arena, uint32_t id, VStorageLayout view, Prepared *out) {
    Buffer *buffer = lookup(arena, id);
    if (!buffer) return VS_HANDLE;
    if (view.transposed > 1 || view.rows > INT32_MAX || view.columns > INT32_MAX ||
        view.leading > INT32_MAX || view.leading < 1 || view.leading < view.rows || view.offset > buffer->capacity)
        return VS_LAYOUT;
    uint64_t width = buffer->scalar ? 16 : 8, components = width / 8;
    uint64_t stride, end = view.offset, row_bytes, column_bytes, bytes;
    if (!multiply(view.leading, width, &stride) || !multiply(view.rows, view.columns, &bytes) ||
        !multiply(bytes, width, &bytes)) return VS_OVERFLOW;
    if (view.rows && view.columns) {
        if (!multiply(view.rows - 1, width, &row_bytes) || !multiply(view.columns - 1, stride, &column_bytes) ||
            !add(end, row_bytes, &end) || !add(end, column_bytes, &end) || !add(end, width, &end)) return VS_OVERFLOW;
        if (end > buffer->capacity || !buffer->data) return VS_LAYOUT;
        uintptr_t base = (uintptr_t)buffer->data;
        if (end > UINTPTR_MAX - base || (base + view.offset) % 8) return VS_LAYOUT;
    }
    *out = (Prepared){buffer, view.offset, end,
        view.transposed ? view.columns : view.rows, view.transposed ? view.rows : view.columns,
        view.transposed ? stride / 8 : components, view.transposed ? components : stride / 8,
        components, bytes};
    return VS_OK;
}

static VStorageStatus typed(VStorageArena *arena, uint32_t id, VStorageLayout view, uint8_t scalar, Prepared *out) {
    VStorageStatus status = prepare(arena, id, view, out);
    if (status != VS_OK) return status;
    return scalar == out->buffer->scalar ? VS_OK : VS_SCALAR;
}

VStorageStatus vstorage_prepare_dense(VStorageArena *arena, uint32_t id,
                                     VStorageLayout view, VStorageDense *out) {
    if (!out) return VS_OPERATION;
    Prepared prepared;
    VStorageStatus status = prepare(arena, id, view, &prepared);
    if (status != VS_OK) return status;
    /* Empty views form no pointer, including an aligned or unaligned offset at
     * the allocation's end. No backend may dereference that empty descriptor. */
    double *data = prepared.bytes ? prepared.buffer->data + prepared.start / 8 : NULL;
    *out = (VStorageDense){data, prepared.start, prepared.end,
        prepared.rows, prepared.columns, view.leading, prepared.bytes, id,
        prepared.buffer->scalar, view.transposed};
    return VS_OK;
}

VStorageStatus vstorage_prepare_write(VStorageArena *arena, uint64_t bytes) {
    if (!arena || arena->closed) return VS_HANDLE;
    return counter_fits(arena->stats.written_bytes, bytes) ? VS_OK : VS_OVERFLOW;
}

/* Only after successful preflight and a synchronous infallible kernel return.
 * The arena is not shared concurrently between resource operations. */
void vstorage_record_write(VStorageArena *arena, uint64_t bytes) {
    arena->stats.written_bytes += bytes;
}

static uint64_t cell(const Prepared *view, uint64_t row, uint64_t column) {
    return view->start / 8 + row * view->row_step + column * view->column_step;
}

static double payload(uint64_t bits) {
    double value;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

VStorageStatus vstorage_fill(VStorageArena *arena, uint32_t id, VStorageLayout view,
                            uint8_t scalar, uint64_t real, uint64_t imaginary) {
    Prepared output;
    VStorageStatus status = typed(arena, id, view, scalar, &output);
    if (status != VS_OK) return status;
    if (!counter_fits(arena->stats.written_bytes, output.bytes)) return VS_OVERFLOW;
    if (!output.bytes) return VS_OK;
    double re = payload(real), im = payload(imaginary);
    /* Fill follows physical columns regardless of the logical transpose. */
    uint64_t offset = view.offset / 8, leading = view.leading * output.components;
    double *data = output.buffer->data;
    if (output.components == 1) {
        for (uint64_t column = 0; column < view.columns; ++column)
            for (uint64_t row = 0; row < view.rows; ++row)
                data[offset + column * leading + row] = re;
    } else {
        for (uint64_t column = 0; column < view.columns; ++column)
            for (uint64_t row = 0; row < view.rows; ++row) {
                uint64_t at = offset + column * leading + 2 * row;
                data[at] = re;
                data[at + 1] = im;
            }
    }
    arena->stats.written_bytes += output.bytes;
    return VS_OK;
}

VStorageStatus vstorage_store(VStorageArena *arena, uint32_t id, VStorageLayout view,
                             uint64_t row, uint64_t column, uint8_t scalar, uint64_t real, uint64_t imaginary) {
    Prepared output;
    VStorageStatus status = typed(arena, id, view, scalar, &output);
    if (status != VS_OK) return status;
    if (row >= output.rows || column >= output.columns) return VS_BOUNDS;
    if (!counter_fits(arena->stats.written_bytes, output.components * 8)) return VS_OVERFLOW;
    uint64_t at = cell(&output, row, column);
    output.buffer->data[at] = payload(real);
    if (output.components == 2) output.buffer->data[at + 1] = payload(imaginary);
    arena->stats.written_bytes += output.components * 8;
    return VS_OK;
}

VStorageStatus vstorage_expect(VStorageArena *arena, uint32_t id, VStorageLayout view,
                              uint64_t row, uint64_t column, uint8_t scalar, uint64_t real, uint64_t imaginary) {
    Prepared input;
    VStorageStatus status = typed(arena, id, view, scalar, &input);
    if (status != VS_OK) return status;
    if (row >= input.rows || column >= input.columns) return VS_BOUNDS;
    uint64_t at = cell(&input, row, column), actual;
    memcpy(&actual, &input.buffer->data[at], 8);
    if (actual != real) return VS_EXPECT;
    if (input.components == 2) {
        memcpy(&actual, &input.buffer->data[at + 1], 8);
        if (actual != imaginary) return VS_EXPECT;
    }
    return VS_OK;
}

/* restrict is scoped to this synchronous kernel, after both full envelopes
 * have been checked. It is never attached to a borrowed allocation globally. */
static void copy_kernel(const double *restrict source, double *restrict target, const Prepared *input, const Prepared *output) {
    if (input->components == 1) {
        for (uint64_t column = 0; column < input->columns; ++column)
            for (uint64_t row = 0; row < input->rows; ++row)
                target[cell(output, row, column)] = source[cell(input, row, column)];
    } else {
        for (uint64_t column = 0; column < input->columns; ++column)
            for (uint64_t row = 0; row < input->rows; ++row) {
                uint64_t src = cell(input, row, column), dst = cell(output, row, column);
                target[dst] = source[src];
                target[dst + 1] = source[src + 1];
            }
    }
}

VStorageStatus vstorage_copy(VStorageArena *arena, uint32_t source, VStorageLayout input,
                            uint32_t target, VStorageLayout output) {
    Prepared a, b;
    VStorageStatus status = prepare(arena, source, input, &a);
    if (status != VS_OK) return status;
    status = prepare(arena, target, output, &b);
    if (status != VS_OK) return status;
    if (a.buffer->scalar != b.buffer->scalar) return VS_SCALAR;
    if (a.rows != b.rows || a.columns != b.columns) return VS_LAYOUT;
    if (!a.bytes) return VS_OK;
    if (source == target) {
        if (a.start == b.start && a.row_step == b.row_step && a.column_step == b.column_step) return VS_OK;
        if (!(a.end <= b.start || b.end <= a.start)) return VS_ALIAS;
    }
    if (!counter_fits(arena->stats.written_bytes, b.bytes) || !counter_fits(arena->stats.copied_bytes, b.bytes))
        return VS_OVERFLOW;
    const double *source_data = a.buffer->data + a.start / 8;
    double *target_data = b.buffer->data + b.start / 8;
    a.start = 0;
    b.start = 0;
    copy_kernel(source_data, target_data, &a, &b);
    arena->stats.written_bytes += b.bytes;
    arena->stats.copied_bytes += b.bytes;
    return VS_OK;
}

/* Each x-block is contiguous in both nontransposed layouts. Copy bytes rather
 * than evaluating double values, preserving every real/complex payload bit. */
static void pack3_kernel(const double *restrict source, double *restrict target,
                         const Prepared *input, const Prepared *output,
                         uint64_t i, uint64_t k, uint64_t j) {
    size_t block_bytes = (size_t)(i * input->components * 8);
    for (uint64_t z = 0; z < k; ++z)
        for (uint64_t y = 0; y < j; ++y)
            memcpy(target + cell(output, i * y, z),
                   source + cell(input, 0, z + k * y), block_bytes);
}

VStorageStatus vstorage_pack3(VStorageArena *arena, uint32_t source, VStorageLayout input,
                             uint32_t target, VStorageLayout output,
                             uint64_t i, uint64_t k, uint64_t j) {
    Prepared a, b;
    VStorageStatus status = prepare(arena, source, input, &a);
    if (status != VS_OK) return status;
    status = prepare(arena, target, output, &b);
    if (status != VS_OK) return status;
    if (input.transposed || output.transposed) return VS_OPERATION;
    if (i > INT32_MAX || k > INT32_MAX || j > INT32_MAX) return VS_LAYOUT;
    uint64_t kj, ij;
    if (!multiply(k, j, &kj) || !multiply(i, j, &ij)) return VS_OVERFLOW;
    if (input.rows != i || input.columns != kj || output.rows != ij || output.columns != k)
        return VS_SHAPE;
    if (a.buffer->scalar != b.buffer->scalar) return VS_SCALAR;
    /* Even empty views passed all metadata and shape checks above. No data
     * pointer is formed and no counter is changed for any zero axis. */
    if (!a.bytes) return VS_OK;
    if (source == target && !(a.end <= b.start || b.end <= a.start)) return VS_ALIAS;
    if (!counter_fits(arena->stats.written_bytes, b.bytes) ||
        !counter_fits(arena->stats.copied_bytes, b.bytes)) return VS_OVERFLOW;
    const double *source_data = a.buffer->data + a.start / 8;
    double *target_data = b.buffer->data + b.start / 8;
    a.start = 0;
    b.start = 0;
    pack3_kernel(source_data, target_data, &a, &b, i, k, j);
    arena->stats.written_bytes += b.bytes;
    arena->stats.copied_bytes += b.bytes;
    return VS_OK;
}

typedef struct {
    unsigned order[3], split;
    uint64_t rows, columns;
} Grouping3;

static int grouping3(uint64_t code, const uint64_t dimensions[3], Grouping3 *out) {
    if (code >= 54) return 0;
    out->split = (unsigned)(code / 27) + 1;
    code %= 27;
    for (unsigned axis = 0; axis < 3; ++axis) {
        out->order[axis] = (unsigned)(code % 3);
        code /= 3;
    }
    if (out->order[0] == out->order[1] || out->order[0] == out->order[2] ||
        out->order[1] == out->order[2]) return 0;
    out->rows = dimensions[out->order[0]];
    out->columns = dimensions[out->order[2]];
    /* Each axis is bounded by INT32_MAX; a pair product fits INT64_MAX. */
    if (out->split == 1) out->columns *= dimensions[out->order[1]];
    else out->rows *= dimensions[out->order[1]];
    return 1;
}

/* Called only for nonempty, fully prepared rectangles. These physical strides
 * are bounded by their already checked envelopes; no coordinate can overflow. */
static void grouping3_strides(const Grouping3 *grouping, const uint64_t dimensions[3],
                              const Prepared *view, uint64_t strides[3]) {
    strides[grouping->order[0]] = view->row_step;
    if (grouping->split == 1) {
        strides[grouping->order[1]] = view->column_step;
        strides[grouping->order[2]] = dimensions[grouping->order[1]] * view->column_step;
    } else {
        strides[grouping->order[1]] = dimensions[grouping->order[0]] * view->row_step;
        strides[grouping->order[2]] = view->column_step;
    }
}

/* Small variable-length memcpy calls can cost more than the original cell loop.
 * Select fixed widths outside the loops so the compiler can inline short byte
 * copies. The caller leaves larger blocks on the original cell loop. All
 * envelopes and strides have already been checked, including disjoint views
 * of the same allocation. */
static void regroup3_blocks(const double *restrict source, double *restrict target,
                            const uint64_t source_stride[3], const uint64_t target_stride[3],
                            const uint64_t dimensions[3], unsigned middle, unsigned slow,
                            size_t block_bytes) {
#define COPY_BLOCKS(bytes) \
    for (uint64_t z = 0; z < dimensions[slow]; ++z) \
        for (uint64_t y = 0; y < dimensions[middle]; ++y) \
            memcpy(target + y * target_stride[middle] + z * target_stride[slow], \
                   source + y * source_stride[middle] + z * source_stride[slow], (bytes))
    switch (block_bytes) {
    case 16: COPY_BLOCKS(16); break;
    case 24: COPY_BLOCKS(24); break;
    case 32: COPY_BLOCKS(32); break;
    case 40: COPY_BLOCKS(40); break;
    case 48: COPY_BLOCKS(48); break;
    case 56: COPY_BLOCKS(56); break;
    case 64: COPY_BLOCKS(64); break;
    default: COPY_BLOCKS(block_bytes); break;
    }
#undef COPY_BLOCKS
}

VStorageStatus vstorage_regroup3(VStorageArena *arena, uint32_t source, VStorageLayout input,
                                uint32_t target, VStorageLayout output,
                                uint64_t d0, uint64_t d1, uint64_t d2,
                                uint64_t input_grouping, uint64_t output_grouping) {
    Prepared a, b;
    VStorageStatus status = prepare(arena, source, input, &a);
    if (status != VS_OK) return status;
    status = prepare(arena, target, output, &b);
    if (status != VS_OK) return status;
    if (input.transposed || output.transposed) return VS_OPERATION;
    if (d0 > INT32_MAX || d1 > INT32_MAX || d2 > INT32_MAX) return VS_LAYOUT;
    const uint64_t dimensions[3] = {d0,d1,d2};
    Grouping3 from, to;
    if (!grouping3(input_grouping, dimensions, &from) ||
        !grouping3(output_grouping, dimensions, &to)) return VS_OPERATION;
    uint64_t volume, bytes;
    if (!multiply(d0, d1, &volume) || !multiply(volume, d2, &volume) ||
        !multiply(volume, a.components * 8, &bytes)) return VS_OVERFLOW;
    if (input.rows != from.rows || input.columns != from.columns ||
        output.rows != to.rows || output.columns != to.columns) return VS_SHAPE;
    if (a.buffer->scalar != b.buffer->scalar) return VS_SCALAR;
    /* Empty descriptors still pass handles, grouping, scalar, shape and bounds
     * checks. No data pointer, write or counter change occurs for any zero axis. */
    if (!bytes) return VS_OK;
    if (source == target && !(a.end <= b.start || b.end <= a.start)) return VS_ALIAS;
    if (!counter_fits(arena->stats.written_bytes, bytes) ||
        !counter_fits(arena->stats.copied_bytes, bytes)) return VS_OVERFLOW;
    uint64_t source_stride[3], target_stride[3];
    grouping3_strides(&from, dimensions, &a, source_stride);
    grouping3_strides(&to, dimensions, &b, target_stride);
    const double *source_data = a.buffer->data + a.start / 8;
    double *target_data = b.buffer->data + b.start / 8;
    unsigned fast = from.order[0];
    size_t block_bytes = (size_t)(dimensions[fast] * a.components * 8);
    if (dimensions[fast] > 1 && block_bytes <= 64 && source_stride[fast] == a.components &&
        target_stride[fast] == a.components) {
        /* Only a physically contiguous axis common to both views is coalesced.
         * The checked nonempty volume bounds this block size; the separated
         * envelopes justify memcpy even for two views of one allocation.
         * Padding and the remaining axes are never included in a block. */
        regroup3_blocks(source_data, target_data, source_stride, target_stride,
                        dimensions, from.order[1], from.order[2], block_bytes);
    } else {
        for (uint64_t x2 = 0; x2 < d2; ++x2)
            for (uint64_t x1 = 0; x1 < d1; ++x1)
                for (uint64_t x0 = 0; x0 < d0; ++x0) {
                    uint64_t src = x0 * source_stride[0] + x1 * source_stride[1] + x2 * source_stride[2];
                    uint64_t dst = x0 * target_stride[0] + x1 * target_stride[1] + x2 * target_stride[2];
                    /* Both paths preserve signaling NaNs and signed zero bits. */
                    if (a.components == 1) memcpy(target_data + dst, source_data + src, 8);
                    else memcpy(target_data + dst, source_data + src, 16);
                }
    }
    arena->stats.written_bytes += bytes;
    arena->stats.copied_bytes += bytes;
    return VS_OK;
}
