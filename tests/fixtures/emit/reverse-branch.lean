import VastitasKernel.IndexedRuntime
import VastitasKernel.AlgebraRuntime
import VastitasKernel.SmoothRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

def map_0 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_1 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2, 0] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_2 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (6 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def map_3 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 1 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def f_7 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_3)

def f_8 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.recomputed v_0 v_1 v_2)

def f_9 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : VastitasKernel.SmoothRuntime.Program) (v_4 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (let v_5 := (VastitasKernel.SmoothRuntime.jacobianStep 1 ([([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly)) v_2 v_3 v_4); (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_5))

def f_10 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.pullback VastitasKernel.SmoothRuntime.PullbackMode.saved v_0 v_1 v_3)

def f_0 (v_1 : Bool) (v_2 : VastitasKernel.SmoothRuntime.Program) (v_3 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (let v_17 := (if v_1 then (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive map_1) (VastitasKernel.SmoothRuntime.Program.primitive map_0)) else (VastitasKernel.SmoothRuntime.Program.primitive map_2)); (let v_18 := v_2; (let v_19 := v_3; (let v_20 := (VastitasKernel.SmoothRuntime.applyPoint v_17 v_18); (f_7 v_17 v_18 v_20 v_19)))))

def f_1 (v_4 : Bool) (v_5 : VastitasKernel.SmoothRuntime.Program) (v_6 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (let v_7 := (if v_4 then (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive map_1) (VastitasKernel.SmoothRuntime.Program.primitive map_0)) else (VastitasKernel.SmoothRuntime.Program.primitive map_2)); (let v_8 := v_5; (let v_9 := v_6; (f_8 v_7 v_8 v_9))))

def f_2 (v_7 : Bool) (v_8 : VastitasKernel.SmoothRuntime.Program) (v_9 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (let v_10 := (if v_7 then (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive map_1) (VastitasKernel.SmoothRuntime.Program.primitive map_0)) else (VastitasKernel.SmoothRuntime.Program.primitive map_2)); (let v_11 := v_8; (let v_12 := v_9; (let v_13 := (VastitasKernel.SmoothRuntime.applyPoint v_10 v_11); (let v_14 := (VastitasKernel.SmoothRuntime.applyPoint (VastitasKernel.SmoothRuntime.Program.primitive map_3) v_13); (f_9 v_10 v_11 v_13 v_14 v_12))))))

def f_3 (v_10 : Bool) (v_11 : VastitasKernel.SmoothRuntime.Program) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (let v_12 := (if v_10 then (VastitasKernel.SmoothRuntime.Program.compose (VastitasKernel.SmoothRuntime.Program.primitive map_1) (VastitasKernel.SmoothRuntime.Program.primitive map_0)) else (VastitasKernel.SmoothRuntime.Program.primitive map_2)); (let v_13 := v_11; (let v_15 := (VastitasKernel.SmoothRuntime.applyPoint v_12 v_13); (let v_14 := (VastitasKernel.SmoothRuntime.vector v_15 [(1 : Int)]); (f_10 v_12 v_13 v_15 v_14)))))

def f_4 (v_12 : Bool) (v_13 : Int) : Int :=
  (if v_12 then (0 : Int) else v_13)

def f_5 (v_14 : (Option VastitasKernel.SmoothRuntime.Fiber)) (v_15 : VastitasKernel.SmoothRuntime.Program) (v_16 : Int) : Bool :=
  (((VastitasKernel.SmoothRuntime.fiberAt v_14 v_15) && ((Prod.fst (VastitasKernel.SmoothRuntime.component v_14 0)) == v_16)) && ((Prod.snd (VastitasKernel.SmoothRuntime.component v_14 0)) == (1 : Int)))

def f_6 : Int :=
  (let v_18 := (VastitasKernel.SmoothRuntime.intPoint [(3 : Int)]); (let v_19 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(18 : Int)]) [(1 : Int)]); (let v_20 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(324 : Int)]) [(1 : Int)]); (((((((((((42 : Int) + (let v_27 := (let v_24 := (let v_21 := true; (let v_22 := v_18; (let v_23 := v_19; (f_0 v_21 v_22 v_23)))); (let v_25 := v_18; (let v_26 := (12 : Int); (f_5 v_24 v_25 v_26)))); (let v_28 := (1 : Int); (f_4 v_27 v_28)))) + (let v_35 := (let v_32 := (let v_29 := false; (let v_30 := v_18; (let v_31 := v_19; (f_0 v_29 v_30 v_31)))); (let v_33 := v_18; (let v_34 := (6 : Int); (f_5 v_32 v_33 v_34)))); (let v_36 := (2 : Int); (f_4 v_35 v_36)))) + (let v_43 := (let v_40 := (let v_37 := true; (let v_38 := v_18; (let v_39 := v_19; (f_1 v_37 v_38 v_39)))); (let v_41 := v_18; (let v_42 := (12 : Int); (f_5 v_40 v_41 v_42)))); (let v_44 := (4 : Int); (f_4 v_43 v_44)))) + (let v_51 := (let v_48 := (let v_45 := false; (let v_46 := v_18; (let v_47 := v_19; (f_1 v_45 v_46 v_47)))); (let v_49 := v_18; (let v_50 := (6 : Int); (f_5 v_48 v_49 v_50)))); (let v_52 := (8 : Int); (f_4 v_51 v_52)))) + (let v_59 := (let v_56 := (let v_53 := true; (let v_54 := v_18; (let v_55 := v_20; (f_2 v_53 v_54 v_55)))); (let v_57 := v_18; (let v_58 := (432 : Int); (f_5 v_56 v_57 v_58)))); (let v_60 := (16 : Int); (f_4 v_59 v_60)))) + (let v_67 := (let v_64 := (let v_61 := false; (let v_62 := v_18; (let v_63 := v_20; (f_2 v_61 v_62 v_63)))); (let v_65 := v_18; (let v_66 := (216 : Int); (f_5 v_64 v_65 v_66)))); (let v_68 := (32 : Int); (f_4 v_67 v_68)))) + (let v_74 := (let v_71 := (let v_69 := true; (let v_70 := v_18; (f_3 v_69 v_70))); (let v_72 := v_18; (let v_73 := (12 : Int); (f_5 v_71 v_72 v_73)))); (let v_75 := (64 : Int); (f_4 v_74 v_75)))) + (let v_81 := (let v_78 := (let v_76 := false; (let v_77 := v_18; (f_3 v_76 v_77))); (let v_79 := v_18; (let v_80 := (6 : Int); (f_5 v_78 v_79 v_80)))); (let v_82 := (128 : Int); (f_4 v_81 v_82)))) + (let v_86 := (!(VastitasKernel.SmoothRuntime.fiberAt (let v_83 := true; (let v_84 := v_18; (let v_85 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(17 : Int)]) [(1 : Int)]); (f_0 v_83 v_84 v_85)))) v_18)); (let v_87 := (256 : Int); (f_4 v_86 v_87)))) + (let v_91 := (!(VastitasKernel.SmoothRuntime.fiberAt (let v_88 := false; (let v_89 := v_18; (let v_90 := (VastitasKernel.SmoothRuntime.vector (VastitasKernel.SmoothRuntime.intPoint [(17 : Int)]) [(1 : Int)]); (f_0 v_88 v_89 v_90)))) v_18)); (let v_92 := (512 : Int); (f_4 v_91 v_92)))))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_6)
