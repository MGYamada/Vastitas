#ifndef DIAGONAL_EXPERIMENT_DIRECT_H
#define DIAGONAL_EXPERIMENT_DIRECT_H
#include "storage.h"
#include "diagonal.h"
VStorageStatus direct_preflight(VStorageArena *arena, unsigned pair,
    const VStorageLayout *layouts, VDiagonal source, VDiagonal target);
void direct_adjoint(const VStorageDense *a, const VStorageDense *b,
                    const double *source, const double *target, unsigned uniform);
void direct_pair(const VStorageDense *a, const VStorageDense *b,
                 const VStorageDense *scratch, const VStorageDense *out,
                 const double *weights, unsigned uniform);
#endif
