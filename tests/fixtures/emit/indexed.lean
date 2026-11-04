import VastitasKernel.IndexedRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

structure Package_0 where
  witness : VastitasKernel.IndexedRuntime.Object
  field_0 : VastitasKernel.IndexedRuntime.Point

def f_0 (v_1 : Nat) : Package_0 :=
  (let v_4 := (VastitasKernel.IndexedRuntime.descriptor v_1); (Package_0.mk v_4 (VastitasKernel.IndexedRuntime.origin v_4 VastitasKernel.IndexedRuntime.baseObject)))

def f_1 (v_2 : Int) : Int :=
  (v_2 + (1 : Int))

def f_2 : Int :=
  (let v_6 := (let v_5 := (41 : Nat); (f_0 v_5)); (let packed_7 := v_6; let v_7 := packed_7.witness; let v_8 := packed_7.field_0; (let v_9 := (VastitasKernel.IndexedRuntime.apply (VastitasKernel.IndexedRuntime.identity v_7) v_8); (let v_10 := (); (let v_11 := (Int.ofNat (v_7).dimension); (f_1 v_11))))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_2)
