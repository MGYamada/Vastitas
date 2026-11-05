import VastitasKernel.IndexedRuntime
import VastitasKernel.AlgebraRuntime
import VastitasKernel.SmoothRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

def f_3 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.jacobianStep 1 ([([([(VastitasKernel.AlgebraRuntime.Term.mk [0] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly)) v_0 v_1 v_2)

def f_0 (v_1 : Bool) (v_2 : Int) : Int :=
  (if v_1 then (0 : Int) else v_2)

def f_1 (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) (v_4 : VastitasKernel.SmoothRuntime.Program) (v_5 : Int) : Bool :=
  (((VastitasKernel.SmoothRuntime.fiberAt v_3 v_4) && ((Prod.fst (VastitasKernel.SmoothRuntime.component v_3 0)) == v_5)) && ((Prod.snd (VastitasKernel.SmoothRuntime.component v_3 0)) == (1 : Int)))

def f_2 : Int :=
  (let v_6 := (VastitasKernel.SmoothRuntime.intPoint [(2 : Int)]); (let v_7 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(12 : Int)]) [(1 : Int)]); ((((let v_11 := (let v_8 := (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (3 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))) (VastitasKernel.SmoothRuntime.Program.primitive (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)))) v_6 v_7); (let v_9 := v_6; (let v_10 := (12 : Int); (f_1 v_8 v_9 v_10)))); (let v_12 := (2 : Int); (f_0 v_11 v_12))) + (let v_16 := (let v_13 := (VastitasKernel.SmoothRuntime.differential (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (3 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))) (VastitasKernel.SmoothRuntime.Program.primitive (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)))) v_6); (let v_14 := v_6; (let v_15 := (12 : Int); (f_1 v_13 v_14 v_15)))); (let v_17 := (4 : Int); (f_0 v_16 v_17)))) + (let v_21 := (let v_18 := (let v_23 := v_6; (let v_24 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(4 : Int)]) [(1 : Int)]); (let v_25 := (VastitasKernel.SmoothRuntime.applyPoint (VastitasKernel.SmoothRuntime.Program.primitive (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))) v_23); (f_3 v_23 v_25 v_24)))); (let v_19 := v_6; (let v_20 := (2 : Int); (f_1 v_18 v_19 v_20)))); (let v_22 := (8 : Int); (f_0 v_21 v_22)))) + (42 : Int))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_2)
