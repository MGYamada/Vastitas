#ifndef VASTITAS_WORKSPACE_OBSERVER_H
#define VASTITAS_WORKSPACE_OBSERVER_H
#include <stddef.h>
/* Diagnostic build only: callbacks allocate nothing and collect no timings. */
void vobs_mark(unsigned phase);
void vobs_dump(void);
/* Event boundary for the same caller, after its first marker and before dump. */
size_t vobs_cursor(void);
void blas_shutdown(void);
#endif
