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
  VastitasPromotion.Regression
