#!/usr/bin/env bash
set -euo pipefail
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
  VastitasKernel.IndexedSourceTypeRegression \
  VastitasKernel.IndexedSourceBodyRegression \
  VastitasKernel.IndexedFunctionRegression \
  VastitasKernel.GraphRegression \
  VastitasKernel.IndexedDispatchRegression \
  VastitasKernel.IndexedAuthorityRegression \
  VastitasKernel.IndexedWireRegression \
  VastitasKernel.GeometryCompatibilityRegression \
  VastitasKernel.LegacySourceRegression \
  VastitasKernel.StorageRegression \
  VastitasStorageTest.Regression \
  VastitasStorageTest.NativeRegression \
  VastitasStorageTest.FunctionRegression \
  VastitasStorageTest.SourceRegression \
  VastitasStorageTest.GemmRegression \
  VastitasStorageTest.NumericalRegression \
  VastitasStorageTest.TransformRegression \
  VastitasStorageTest.NetworkRegression \
  VastitasStorageTest.EvaluationRegression \
  VastitasStorageTest.TensorRegression \
  VastitasPromotion.Regression
