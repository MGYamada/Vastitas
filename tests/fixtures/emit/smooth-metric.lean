import VastitasKernel.IndexedRuntime
import VastitasKernel.AlgebraRuntime
import VastitasKernel.SmoothRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

def matrix_0 : VastitasKernel.SmoothRuntime.Matrix :=
  ([[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)

def matrix_1 : VastitasKernel.SmoothRuntime.Matrix :=
  ([[(mkRat (2 : Int) 1), (mkRat (1 : Int) 1)], [(mkRat (1 : Int) 1), (mkRat (1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)

def matrix_2 : VastitasKernel.SmoothRuntime.Matrix :=
  ([[(mkRat (1 : Int) 1), (mkRat (-1 : Int) 1)], [(mkRat (-1 : Int) 1), (mkRat (2 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)

def matrix_3 : VastitasKernel.SmoothRuntime.Matrix :=
  ([[(mkRat (1 : Int) 1), (mkRat (0 : Int) 1)], [(mkRat (0 : Int) 1), (mkRat (-1 : Int) 1)]] : VastitasKernel.SmoothRuntime.Matrix)

def map_0 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2, 0] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def f_6 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_3)

def f_7 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_3)

def f_8 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_3)

def f_9 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.jacobianStep 1 ([([([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly), ([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly)) v_0 v_1 v_2)

def f_0 (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.sharp matrix_0 (let v_3 := v_2; (let v_5 := (VastitasKernel.SmoothRuntime.applyPoint v_1 v_3); (let v_4 := (VastitasKernel.SmoothRuntime.vector v_5 [(1 : Int)]); (f_6 v_1 v_3 v_5 v_4)))))

def f_1 (v_3 : VastitasKernel.SmoothRuntime.Program) (v_4 : VastitasKernel.SmoothRuntime.Program) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.sharp matrix_2 (let v_5 := v_4; (let v_7 := (VastitasKernel.SmoothRuntime.applyPoint v_3 v_5); (let v_6 := (VastitasKernel.SmoothRuntime.vector v_7 [(1 : Int)]); (f_7 v_3 v_5 v_7 v_6)))))

def f_2 (v_5 : VastitasKernel.SmoothRuntime.Program) (v_6 : VastitasKernel.SmoothRuntime.Program) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.sharp matrix_3 (let v_7 := v_6; (let v_9 := (VastitasKernel.SmoothRuntime.applyPoint v_5 v_7); (let v_8 := (VastitasKernel.SmoothRuntime.vector v_9 [(1 : Int)]); (f_8 v_5 v_7 v_9 v_8)))))

def f_3 (v_7 : Bool) (v_8 : Int) : Int :=
  (if v_7 then (0 : Int) else v_8)

def f_4 (v_9 : (Option VastitasKernel.SmoothRuntime.Fiber)) (v_10 : Int) (v_11 : Int) : Bool :=
  (((((Prod.fst (VastitasKernel.SmoothRuntime.component v_9 0)) == v_10) && ((Prod.snd (VastitasKernel.SmoothRuntime.component v_9 0)) == (1 : Int))) && ((Prod.fst (VastitasKernel.SmoothRuntime.component v_9 1)) == v_11)) && ((Prod.snd (VastitasKernel.SmoothRuntime.component v_9 1)) == (1 : Int)))

def f_5 : Int :=
  (let v_12 := (VastitasKernel.SmoothRuntime.intPoint [(1 : Int), (2 : Int)]); (let v_13 := (let v_72 := v_12; (let v_74 := (VastitasKernel.SmoothRuntime.applyPoint (VastitasKernel.SmoothRuntime.Program.primitive map_0) v_72); (let v_73 := (VastitasKernel.SmoothRuntime.vector v_74 [(1 : Int)]); (f_9 v_72 v_74 v_73)))); (let v_14 := (VastitasKernel.SmoothRuntime.vector v_12 [(5 : Int), (-(7 : Int))]); (((((((((((((42 : Int) + (let v_15 := ((((Prod.fst (VastitasKernel.SmoothRuntime.component v_13 0)) == (2 : Int)) && ((Prod.fst (VastitasKernel.SmoothRuntime.component v_13 1)) == (1 : Int))) && ((Prod.snd (VastitasKernel.SmoothRuntime.component v_13 1)) == (1 : Int))); (let v_16 := (1 : Int); (f_3 v_15 v_16)))) + (let v_22 := (let v_19 := (let v_17 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_18 := v_12; (f_0 v_17 v_18))); (let v_20 := (2 : Int); (let v_21 := (1 : Int); (f_4 v_19 v_20 v_21)))); (let v_23 := (2 : Int); (f_3 v_22 v_23)))) + (let v_29 := (let v_26 := (let v_24 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_25 := v_12; (f_1 v_24 v_25))); (let v_27 := (1 : Int); (let v_28 := (0 : Int); (f_4 v_26 v_27 v_28)))); (let v_30 := (3 : Int); (f_3 v_29 v_30)))) + (let v_36 := (let v_33 := (let v_31 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_32 := v_12; (f_2 v_31 v_32))); (let v_34 := (2 : Int); (let v_35 := (-(1 : Int)); (f_4 v_33 v_34 v_35)))); (let v_37 := (4 : Int); (f_3 v_36 v_37)))) + (let v_42 := (!(VastitasKernel.SmoothRuntime.fiberEqual (let v_38 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_39 := v_12; (f_0 v_38 v_39))) (let v_40 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_41 := v_12; (f_1 v_40 v_41))))); (let v_43 := (5 : Int); (f_3 v_42 v_43)))) + (let v_48 := ((VastitasKernel.SmoothRuntime.fiberAt (let v_44 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_45 := v_12; (f_1 v_44 v_45))) v_12) && (VastitasKernel.SmoothRuntime.fiberAt (let v_46 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_47 := v_12; (f_2 v_46 v_47))) v_12)); (let v_49 := (6 : Int); (f_3 v_48 v_49)))) + (let v_50 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.SmoothRuntime.sharp matrix_0 (VastitasKernel.SmoothRuntime.flat matrix_0 v_14)) v_14); (let v_51 := (7 : Int); (f_3 v_50 v_51)))) + (let v_52 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.SmoothRuntime.sharp matrix_2 (VastitasKernel.SmoothRuntime.flat matrix_1 v_14)) v_14); (let v_53 := (8 : Int); (f_3 v_52 v_53)))) + (let v_54 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.SmoothRuntime.flat matrix_1 v_14) (VastitasKernel.SmoothRuntime.vector v_12 [(3 : Int), (-(2 : Int))])); (let v_55 := (9 : Int); (f_3 v_54 v_55)))) + (let v_60 := (((Prod.fst (VastitasKernel.SmoothRuntime.pairing v_13 (let v_56 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_57 := v_12; (f_1 v_56 v_57))))) == (2 : Int)) && ((Prod.snd (VastitasKernel.SmoothRuntime.pairing v_13 (let v_58 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_59 := v_12; (f_1 v_58 v_59))))) == (1 : Int))); (let v_61 := (10 : Int); (f_3 v_60 v_61)))) + (let v_66 := ((Prod.fst (VastitasKernel.SmoothRuntime.pairing (VastitasKernel.SmoothRuntime.flat matrix_1 (let v_62 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_63 := v_12; (f_1 v_62 v_63)))) (let v_64 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_65 := v_12; (f_1 v_64 v_65))))) == (2 : Int)); (let v_67 := (11 : Int); (f_3 v_66 v_67)))) + (let v_70 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.SmoothRuntime.flat matrix_1 (let v_68 := (VastitasKernel.SmoothRuntime.Program.primitive map_0); (let v_69 := v_12; (f_1 v_68 v_69)))) v_13); (let v_71 := (12 : Int); (f_3 v_70 v_71)))))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_5)
