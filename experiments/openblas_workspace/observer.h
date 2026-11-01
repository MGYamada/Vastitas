#ifndef VASTITAS_WORKSPACE_OBSERVER_H
#define VASTITAS_WORKSPACE_OBSERVER_H
/* Diagnostic build only: callbacks allocate nothing and collect no timings. */
void vobs_mark(unsigned phase);
void vobs_dump(void);
void blas_shutdown(void);
#endif
