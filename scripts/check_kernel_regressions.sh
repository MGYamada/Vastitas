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
  VastitasKernel.IndexedSourceTypeRegression \
  VastitasKernel.IndexedSourceBodyRegression \
  VastitasKernel.IndexedFunctionRegression \
  VastitasPromotion.Regression
