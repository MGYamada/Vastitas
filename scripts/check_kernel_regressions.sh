#!/usr/bin/env bash
set -euo pipefail
# Keep retained legacy API tests and current indexed/public JSON tests distinct.
# LegacySourceRegression, VastitasPublicTest.AuthorityRegression and
# VastitasPromotion.IndexedRegression exercise Main's current source routes.
cd "$(dirname "$0")/.."
lake -d lean-kernel build \
  VastitasKernel.TypeAuditRegression \
  VastitasKernel.DispatchRegression \
  VastitasKernel.FunctionRegression \
  VastitasKernel.NamespaceRegression \
  VastitasKernel.PairRegression \
  VastitasKernel.AbstractRegression \
  VastitasKernel.ContractRegression \
  VastitasKernel.AuthorityRegression \
  VastitasKernel.IndexedRegression \
  VastitasKernel.IndexedPackageRegression \
  VastitasKernel.IndexedPrimitiveRegression \
  VastitasKernel.IndexedCoreRegression \
  VastitasKernel.LegacyIndexedRegression \
  VastitasKernel.IndexedSemanticRegression \
  VastitasKernel.IndexedPackageSemanticRegression \
  VastitasKernel.IndexedSourceRegression \
  VastitasKernel.IndexedNumericalRegression \
  VastitasKernel.AffineDeclarationRegression \
  VastitasKernel.AffineMorphismRegression \
  VastitasKernel.IndexedSourceTypeRegression \
  VastitasKernel.IndexedSourceBodyRegression \
  VastitasKernel.IndexedFunctionRegression \
  VastitasKernel.GraphRegression \
  VastitasKernel.IndexedDispatchRegression \
  VastitasKernel.IndexedAuthorityRegression \
  VastitasKernel.IndexedWireRegression \
  VastitasKernel.GeometryCompatibilityRegression \
  VastitasKernel.LegacySourceRegression \
  VastitasPublicTest.AuthorityRegression \
  VastitasKernel.StorageRegression \
  VastitasStorageTest.Regression \
  VastitasStorageTest.NativeRegression \
  VastitasStorageTest.FunctionRegression \
  VastitasStorageTest.SourceRegression \
  VastitasStorageTest.ValueFlowRegression \
  VastitasStorageTest.ShapeRegression \
  VastitasStorageTest.GemmRegression \
  VastitasStorageTest.NumericalRegression \
  VastitasStorageTest.NumericalCoverageRegression \
  VastitasStorageTest.TransformRegression \
  VastitasStorageTest.NetworkRegression \
  VastitasStorageTest.EvaluationRegression \
  VastitasStorageTest.TensorRegression \
  VastitasStorageTest.TreeRegression \
  VastitasStorageTest.DependencyRegression \
  VastitasStorageTest.MetricRegression \
  VastitasStorageTest.OwnedPackageRegression \
  VastitasAlgebraTest.BasisRegression \
  VastitasPromotion.Regression \
  VastitasPromotion.IndexedRegression
