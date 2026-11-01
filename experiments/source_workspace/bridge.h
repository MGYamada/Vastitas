#ifndef VASTITAS_SOURCE_WORKSPACE_BRIDGE_H
#define VASTITAS_SOURCE_WORKSPACE_BRIDGE_H
void source_workspace_mark(unsigned phase);
void source_workspace_begin(unsigned scalar, int order, int ta, int tb,
    int m, int n, int k, int lda, int ldb, int ldc,
    double ar, double ai, double br, double bi, const void *a, const void *b, const void *c);
void source_workspace_end(void);
void source_workspace_report(void);
#endif
