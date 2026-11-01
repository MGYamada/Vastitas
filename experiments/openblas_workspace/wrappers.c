/* Appended to the private memory.c. Definitions, rather than all occurrences,
 * were renamed, so calls from constructors in that same TU are observed too. */
#if defined(SMP) || defined(COMPILE_TLS) || defined(USE_OPENMP) || defined(INTERFACE64)
#error "Only the pinned sequential LP64 non-TLS profile is calibrated"
#endif
#if !defined(ALLOC_MMAP) || !defined(ALLOC_MALLOC) || defined(ALLOC_SHM) || \
    defined(ALLOC_HUGETLB) || defined(ALLOC_HUGETLBFILE) || defined(ALLOC_WINDOWS) || \
    defined(ALLOC_QALLOC) || defined(ALLOC_DEVICEDRIVER)
#error "Unobserved backing allocator enabled"
#endif
_Static_assert(sizeof(void *) == 8 && sizeof(blasint) == 4, "64-bit LP64 host required");
void *blas_memory_alloc(int position) {
    void *p = vobs_real_blas_memory_alloc(position);
    vobs_record("borrow", p, BUFFER_SIZE, p != NULL, 0);
    return p;
}
void blas_memory_free(void *p) {
    vobs_record("return", p, BUFFER_SIZE, 1, 0);
    vobs_real_blas_memory_free(p);
}
void *blas_memory_alloc_nolock(int position) {
    void *p = vobs_real_blas_memory_alloc_nolock(position);
    vobs_record("direct_borrow", p, BUFFER_SIZE, p != NULL, 0);
    return p;
}
void blas_memory_free_nolock(void *p) {
    vobs_record("direct_return", p, BUFFER_SIZE, 1, 0);
    vobs_real_blas_memory_free_nolock(p);
}
void blas_shutdown(void) {
    vobs_record("shutdown_begin", NULL, 0, 1, 0);
    vobs_real_blas_shutdown();
    vobs_record("shutdown_end", NULL, 0, 1, 0);
}
