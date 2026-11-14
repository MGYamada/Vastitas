import VastitasKernel.IndexedRuntime
import VastitasKernel.AlgebraRuntime
import VastitasKernel.SmoothRuntime
import VastitasKernel.FrameRuntime

set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace VastitasGenerated

def frame_0 : List (List VastitasKernel.AlgebraRuntime.Poly) :=
  ([([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (-1 : Int) 2))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly), ([([] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 2))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly))

def frame_1 : List (List VastitasKernel.AlgebraRuntime.Poly) :=
  ([([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly), ([([] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly))

def frame_2 : List (List VastitasKernel.AlgebraRuntime.Poly) :=
  ([([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly), ([([] : VastitasKernel.AlgebraRuntime.Poly), ([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly))

def frame_3 : List (List VastitasKernel.AlgebraRuntime.Poly) :=
  ([([([(VastitasKernel.AlgebraRuntime.Term.mk [0] (mkRat (1 : Int) 2))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly))

def map_0 : VastitasKernel.AlgebraRuntime.Map :=
  (VastitasKernel.AlgebraRuntime.Map.mk 2 ([] : List VastitasKernel.AlgebraRuntime.Poly) ([([(VastitasKernel.AlgebraRuntime.Term.mk [2, 0] (mkRat (1 : Int) 1)), (VastitasKernel.AlgebraRuntime.Term.mk [0, 1] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly))

def jacobian_0 : List (List VastitasKernel.AlgebraRuntime.Poly) :=
  ([([([(VastitasKernel.AlgebraRuntime.Term.mk [1, 0] (mkRat (2 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly), ([([(VastitasKernel.AlgebraRuntime.Term.mk [0, 0] (mkRat (1 : Int) 1))] : VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] : List (List VastitasKernel.AlgebraRuntime.Poly))

def f_3 (v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) (v_2 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=
  (VastitasKernel.SmoothRuntime.jacobianStep 1 jacobian_0 v_0 v_1 v_2)

def f_0 (v_1 : Bool) (v_2 : Int) : Int :=
  (if v_1 then (0 : Int) else v_2)

def f_1 (v_3 : (Prod Int Int)) (v_4 : Int) : Bool :=
  (((Prod.fst v_3) == v_4) && ((Prod.snd v_3) == (1 : Int)))

def f_2 : Int :=
  (let v_5 := (VastitasKernel.SmoothRuntime.intPoint [(1 : Int), (2 : Int)]); (let v_6 := (VastitasKernel.SmoothRuntime.vector v_5 [(1 : Int), (2 : Int)]); (let v_7 := (VastitasKernel.FrameRuntime.decodeTangent frame_2 v_6); (let v_8 := (VastitasKernel.FrameRuntime.encodeTangent frame_0 v_7); (let v_9 := (let v_31 := v_5; (let v_33 := (VastitasKernel.SmoothRuntime.applyPoint (VastitasKernel.SmoothRuntime.Program.primitive map_0) v_31); (let v_32 := (VastitasKernel.SmoothRuntime.vector v_33 [(1 : Int)]); (f_3 v_31 v_33 v_32)))); (let v_10 := (VastitasKernel.FrameRuntime.encodeCotangent frame_1 v_9); (((((((42 : Int) + (let v_13 := (((let v_11 := (VastitasKernel.SmoothRuntime.component v_8 0); (let v_12 := (2 : Int); (f_1 v_11 v_12))) && (VastitasKernel.SmoothRuntime.fiberAt v_8 v_5)) && (VastitasKernel.SmoothRuntime.fiberAt v_6 v_5)); (let v_14 := (1 : Int); (f_0 v_13 v_14)))) + (let v_15 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.FrameRuntime.apply (VastitasKernel.FrameRuntime.transition v_5 frame_2 frame_0) v_6) v_8); (let v_16 := (2 : Int); (f_0 v_15 v_16)))) + (let v_21 := ((let v_17 := (VastitasKernel.SmoothRuntime.pairing v_10 v_8); (let v_18 := (8 : Int); (f_1 v_17 v_18))) && (let v_19 := (VastitasKernel.SmoothRuntime.pairing (VastitasKernel.FrameRuntime.coapply (VastitasKernel.FrameRuntime.transition v_5 frame_2 frame_0) v_10) v_6); (let v_20 := (8 : Int); (f_1 v_19 v_20)))); (let v_22 := (4 : Int); (f_0 v_21 v_22)))) + (let v_23 := (VastitasKernel.SmoothRuntime.fiberEqual (VastitasKernel.FrameRuntime.decodeCotangent frame_0 v_10) v_9); (let v_24 := (8 : Int); (f_0 v_23 v_24)))) + (let v_27 := (let v_25 := (VastitasKernel.FrameRuntime.entry (VastitasKernel.FrameRuntime.frameMatrix (VastitasKernel.SmoothRuntime.Program.primitive map_0) v_5 frame_1 frame_3) 0 1); (let v_26 := (2 : Int); (f_1 v_25 v_26))); (let v_28 := (16 : Int); (f_0 v_27 v_28)))) + (let v_29 := (VastitasKernel.FrameRuntime.matrixEqual (VastitasKernel.FrameRuntime.compose (VastitasKernel.FrameRuntime.frameMatrix (VastitasKernel.SmoothRuntime.Program.primitive map_0) v_5 frame_1 frame_3) (VastitasKernel.FrameRuntime.transition v_5 frame_2 frame_0)) (VastitasKernel.FrameRuntime.frameMatrix (VastitasKernel.SmoothRuntime.Program.primitive map_0) v_5 frame_2 frame_3)); (let v_30 := (32 : Int); (f_0 v_29 v_30))))))))))

end VastitasGenerated

def main : IO Unit :=
  IO.println (VastitasGenerated.f_2)
