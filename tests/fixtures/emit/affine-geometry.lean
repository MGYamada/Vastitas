import VastitasKernel.IndexedRuntime
import VastitasKernel.AlgebraRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

def basis_0 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)

def basis_1 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([] : List VastitasKernel.AlgebraRuntime.Poly)

def basis_2 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 2] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (-1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)

def basis_3 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)

def basis_4 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([([(VastitasKernel.AlgebraRuntime.Term.mk [2, 1] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (-1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)

def basis_5 : List VastitasKernel.AlgebraRuntime.Poly :=
  ([([(VastitasKernel.AlgebraRuntime.Term.mk [1, 1] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (-1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)

def map_0 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_0 ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_1 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_0 ([([] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_2 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 0 basis_1 ([([] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_3 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_1 ([([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_4 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_1 ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_5 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_0 ([([] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_6 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 basis_2 ([([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_7 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 basis_0 ([] : List VastitasKernel.AlgebraRuntime.Poly))

def map_8 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 basis_3 ([([] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_9 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 basis_4 ([([(VastitasKernel.AlgebraRuntime.Term.mk [2, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_10 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 basis_5 ([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def f_0 (v_1 : Bool) (v_2 : Int) : Int :=
  (if v_1 then (0 : Int) else v_2)

def f_1 : Int :=
  ((((((((((((42 : Int) + (let v_3 := (!(VastitasKernel.AlgebraRuntime.Map.same map_0 map_1)); (let v_4 := (1 : Int); (f_0 v_3 v_4)))) + (let v_5 := (VastitasKernel.AlgebraRuntime.Map.same (VastitasKernel.AlgebraRuntime.Map.compose map_0 map_2) (VastitasKernel.AlgebraRuntime.Map.compose map_1 map_2)); (let v_6 := (2 : Int); (f_0 v_5 v_6)))) + (let v_7 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient map_0 0 [1])) == (1 : Int)); (let v_8 := (3 : Int); (f_0 v_7 v_8)))) + (let v_9 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient (VastitasKernel.AlgebraRuntime.Map.compose map_3 map_4) 0 [1])) == (2 : Int)); (let v_10 := (4 : Int); (f_0 v_9 v_10)))) + (let v_11 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient (VastitasKernel.AlgebraRuntime.Map.compose map_4 map_3) 0 [1])) == (0 : Int)); (let v_12 := (5 : Int); (f_0 v_11 v_12)))) + (let v_13 := (VastitasKernel.AlgebraRuntime.Map.same (VastitasKernel.AlgebraRuntime.Map.compose map_6 map_5) map_1); (let v_14 := (6 : Int); (f_0 v_13 v_14)))) + (let v_15 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient (VastitasKernel.AlgebraRuntime.Map.compose map_3 (VastitasKernel.AlgebraRuntime.Map.intPoint [(3 : Int)])) 0 [])) == (9 : Int)); (let v_16 := (7 : Int); (f_0 v_15 v_16)))) + (let v_17 := (VastitasKernel.AlgebraRuntime.Map.same (VastitasKernel.AlgebraRuntime.Map.compose map_8 (VastitasKernel.AlgebraRuntime.Map.pair map_5 map_7)) map_5); (let v_18 := (8 : Int); (f_0 v_17 v_18)))) + (let v_19 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient (VastitasKernel.AlgebraRuntime.Map.pair map_5 map_7) 1 [1])) == (1 : Int)); (let v_20 := (9 : Int); (f_0 v_19 v_20)))) + (let v_21 := ((Prod.fst (VastitasKernel.AlgebraRuntime.Map.coefficient map_9 1 [0, 1])) == (1 : Int)); (let v_22 := (10 : Int); (f_0 v_21 v_22)))) + (let v_23 := (VastitasKernel.AlgebraRuntime.Map.same (VastitasKernel.AlgebraRuntime.Map.compose map_10 map_10) (VastitasKernel.AlgebraRuntime.Map.compose map_10 map_10)); (let v_24 := (11 : Int); (f_0 v_23 v_24))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_1)
