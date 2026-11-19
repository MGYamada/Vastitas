import IndexedRuntime

/- This probe uses the repository's unmodified IndexedRuntime source, copied
into the private build directory. It is foreign-library qualification, not
an accepted Vastitas program or a compiler refinement theorem. -/
@[export vastitas_qual_indexed]
def indexedProbe (n : Nat) : Nat :=
  let object := VastitasKernel.IndexedRuntime.descriptor n
  let map := VastitasKernel.IndexedRuntime.identity object
  (VastitasKernel.IndexedRuntime.apply map
    (VastitasKernel.IndexedRuntime.origin object
      VastitasKernel.IndexedRuntime.baseObject)).target.dimension
