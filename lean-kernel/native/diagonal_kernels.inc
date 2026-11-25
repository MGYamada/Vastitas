/* Instantiated for the destination component width; all weights have been
 * checked as exactly representable before the first write. */
SPECIALIZED void LOCAL(weight_kernel)(const VStorageDense *input, const VStorageDense *output,
                                 const uint8_t *weights, const int uniform, uint8_t conjugate) {
    const COMPONENT *from = input->data;
    COMPONENT *to = output->data;
    const COMPONENT fixed = uniform ? (COMPONENT)weight_at(weights, 0) : 0.0;
    /* Ordinary columns are contiguous even when their enclosing allocations
     * have padded leading dimensions. Select representation/stride once, not
     * per element. A transposed physical row retains the explicit stride path. */
    if (!input->transposed && !vstorage_is_complex(input->scalar)) {
        for (uint64_t i=0;i<input->rows;++i) to[i]=from[i]*(uniform?fixed:(COMPONENT)weight_at(weights,i));
        return;
    }
    if (!input->transposed && vstorage_is_complex(input->scalar)) {
        for (uint64_t i=0;i<input->rows;++i) {
            COMPONENT weight=uniform?fixed:(COMPONENT)weight_at(weights,i);
            to[2*i]=from[2*i]*weight;
            to[2*i+1]=(conjugate?-from[2*i+1]:from[2*i+1])*weight;
        }
        return;
    }
    for (uint64_t i = 0; i < input->rows; ++i) {
        uint64_t a = coordinate(input, i, 0), b = coordinate(output, i, 0);
        COMPONENT weight = uniform ? fixed : (COMPONENT)weight_at(weights, i);
        to[b] = from[a] * weight;
        if (vstorage_is_complex(input->scalar)) to[b + 1] = (conjugate ? -from[a + 1] : from[a + 1]) * weight;
    }
}

/* The target weight is decoded once per destination column. A nonuniform
 * source weight is one load per element; a uniform one is decoded once. */
SPECIALIZED void LOCAL(adjoint_kernel)(const VStorageDense *a, const VStorageDense *b,
                                  const uint8_t *source, const int source_uniform,
                                  VDiagonal target, uint8_t conjugate) {
    const COMPONENT *in = a->data;
    COMPONENT *out = b->data;
    const COMPONENT fixed = source_uniform ? (COMPONENT)weight_at(source, 0) : 0.0;
    const uint64_t target_step = target.uniform ? 0 : 1;
    if (!a->transposed && !vstorage_is_complex(a->scalar)) {
        for (uint64_t j=0;j<b->columns;++j) {
            COMPONENT target_weight=(COMPONENT)weight_at(target.data,j*target_step);
            for (uint64_t i=0;i<b->rows;++i)
                out[j*b->leading+i]=(in[i*a->leading+j]*target_weight)/
                    (source_uniform?fixed:(COMPONENT)weight_at(source,i));
        }
    } else if (!a->transposed && vstorage_is_complex(a->scalar)) {
        for (uint64_t j=0;j<b->columns;++j) {
            COMPONENT target_weight=(COMPONENT)weight_at(target.data,j*target_step);
            for (uint64_t i=0;i<b->rows;++i) {
                uint64_t from=2*(i*a->leading+j),to=2*(j*b->leading+i);
                COMPONENT source_weight=source_uniform?fixed:(COMPONENT)weight_at(source,i);
                out[to]=(in[from]*target_weight)/source_weight;
                out[to+1]=((conjugate?-in[from+1]:in[from+1])*target_weight)/source_weight;
            }
        }
    } else {
        for (uint64_t j = 0; j < b->columns; ++j) {
            COMPONENT target_weight = (COMPONENT)weight_at(target.data, j * target_step);
            for (uint64_t i = 0; i < b->rows; ++i) {
                uint64_t from = coordinate(a, j, i), to = coordinate(b, i, j);
                COMPONENT source_weight = source_uniform ? fixed : (COMPONENT)weight_at(source, i);
                out[to] = (in[from] * target_weight) / source_weight;
                if (vstorage_is_complex(a->scalar)) out[to + 1] = ((conjugate ? -in[from + 1] : in[from + 1]) * target_weight) / source_weight;
            }
        }
    }
}
