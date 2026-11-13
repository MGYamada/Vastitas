import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedDeclarationProtocol
import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedSemantics

set_option autoImplicit false

/-! The frame bindings (Stage 4, #759) through the actual common source
checker, the independent declaration and Core audits, the role table of a
rejected call, the Core semantics and its erasure, code generation and the
protocol decoder. These are executable regressions, not proofs.

The frames are on the plane: `b` with columns `(1, 0)` and `(1, 2)`
(`det = 2`, `P ≠ Pᵀ`), `c` with columns `(1, 1)` and `(0, 3)` (`det = 3`),
the coordinate frame `e`, and `bx` with columns `(1, 0)` and `(x, 1)`, which
depends on the point. `d` is the coordinate frame of a second plane and `z`
the empty frame of a point. The map `F(x, y) = (x + y, x y)` has the Jacobian
`[[1, 1], [2, 1]]` at `p = (1, 2)`. `frameFixture` checks adequacy,
transitions, the pairing, the roadmap identity, the matrix of a composite,
the point-dependent frame at two points and the degenerate cases; the native
fixture script compiles it. -/
namespace VastitasKernel.Indexed.FrameRegression

open AlgebraRuntime

private def pkg : Namespace.PackageId := ⟨"/frames/Vastitas.toml", "frames", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def c (name : String) : Source.PolyExpr := .coordinate name
private def n (value : Nat) : Source.PolyExpr := .natural value
private def space (name : String) (dimension : Nat) (coordinates : List String) : Source.Declaration :=
  decl name (.smoothAffine (path "SmoothR") dimension coordinates)
private def morphism (name x y : String) (definition : Source.MorphismDefinition) : Source.Declaration :=
  decl name (.morphism (path "Smooth") [path x, path y] definition)
private def primitive (name : String) (binding : Source.Primitive) : Source.Declaration :=
  decl name (.primitive binding)
private def ref (field name : String) : String × Source.WireArgument := (field, .path (path name))
private def nat (field : String) (value : Nat) : String × Source.WireArgument := (field, .natural value)
private def objectFamily (name : String) (representation : FamilyRepresentation) (arity : Nat)
    (constraints : List Constraint) : Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .object (path "CInfAffine"), constraints, representation⟩)
private def frameFamily (name : String) (representation : FamilyRepresentation) (arity : Nat) :
    Source.Declaration :=
  decl name (.family ⟨(List.range arity).map fun _ => .frame (path "Frame"), [], representation⟩)
private def frame (name object : String) (columns : Option (List (List Source.PolyExpr)))
    (inverse : Option (List (List Source.PolyExpr)) := none) : Source.Declaration :=
  decl name (.frame (path "Frame") [path object] columns inverse)

private def encode (name fiber coords frameName : String) : Source.Declaration :=
  primitive name ⟨"frame_encode", [ref "fiber" fiber, ref "coords" coords, ref "frame" frameName]⟩
private def decode (name coords fiber frameName : String) : Source.Declaration :=
  primitive name ⟨"frame_decode", [ref "coords" coords, ref "fiber" fiber, ref "frame" frameName]⟩
private def vector (name coords frameName : String) : Source.Declaration :=
  primitive name ⟨"frame_vector", [ref "coords" coords, ref "map_family" "Smooth", ref "frame" frameName]⟩
private def matrix (name source target : String) (maps := "FrameMap") : Source.Declaration :=
  primitive name ⟨"frame_matrix", [ref "map_family" "Smooth", ref "frame_map" maps, ref "source" source,
    ref "target" target]⟩
private def transition (name source target : String) : Source.Declaration :=
  primitive name ⟨"frame_transition", [ref "map_family" "Smooth", ref "frame_map" "FrameMap",
    ref "source" source, ref "target" target]⟩

/-- The smooth profile, the frame families, the frames and the maps. -/
private def base : List Source.Declaration := [
  decl "CInfReal" .marker,
  decl "SmoothR" (.implementation (path "CInfReal") .smoothAffine []),
  decl "CInfAffine" (.classification [] [path "SmoothR"]),
  objectFamily "Smooth" .smooth 2 [.canonical 0, .canonical 1],
  objectFamily "Tangent" (.fiber .tangent) 1 [.canonical 0],
  objectFamily "Cotangent" (.fiber .cotangent) 1 [.canonical 0],
  objectFamily "Frame" .frame 1 [.canonical 0],
  frameFamily "Coords" (.frameFiber .tangent) 1,
  frameFamily "CoCoords" (.frameFiber .cotangent) 1,
  frameFamily "FrameMap" .frameMap 2,
  space "Pt" 0 [],
  space "Plane" 2 ["x", "y"],
  space "Plane2" 2 ["u", "w"],
  frame "b" "Plane" (some [[n 1, n 0], [n 1, n 2]]),
  frame "c" "Plane" (some [[n 1, n 1], [n 0, n 3]]),
  frame "e" "Plane" none,
  frame "bx" "Plane" (some [[n 1, n 0], [c "x", n 1]]) (some [[n 1, n 0], [.neg (c "x"), n 1]]),
  frame "d" "Plane2" none,
  frame "z" "Pt" (some []),
  morphism "F" "Plane" "Plane" (.pullback [("x", .sum [c "x", c "y"]), ("y", .product [c "x", c "y"])]),
  morphism "G" "Plane" "Plane" (.pullback [("x", .product [c "x", c "y"]), ("y", .sum [c "x", c "y"])]),
  morphism "R" "Plane" "Plane" (.pullback [("x", .sum [c "x", c "y"]), ("y", .sum [.product [n 2, c "x"],
    .product [n 2, c "y"]])]),
  morphism "idPt" "Pt" "Pt" .identity,
  morphism "toPt" "Plane" "Pt" (.pullback []),
  morphism "fromPt" "Pt" "Plane" (.pullback [("x", n 1), ("y", n 2)]),
  primitive "compose" ⟨"smooth_compose", [ref "family" "Smooth"]⟩,
  primitive "plane_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Plane", ref "point" "Pt"]⟩,
  primitive "plane2_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Plane2", ref "point" "Pt"]⟩,
  primitive "pt_at" ⟨"smooth_int_point", [ref "family" "Smooth", ref "object" "Pt", ref "point" "Pt"]⟩,
  primitive "vplane" ⟨"fiber_vector", [ref "family" "Tangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "dplane" ⟨"fiber_vector", [ref "family" "Cotangent", ref "map_family" "Smooth", ref "object" "Plane"]⟩,
  primitive "pairing" ⟨"fiber_pairing", [ref "cotangent" "Cotangent", ref "tangent" "Tangent"]⟩,
  primitive "same_vector" ⟨"fiber_equal", [ref "family" "Tangent"]⟩,
  primitive "same_covector" ⟨"fiber_equal", [ref "family" "Cotangent"]⟩,
  primitive "pullback" ⟨"cotangent_pullback", [ref "map_family" "Smooth", ref "cotangent" "Cotangent",
    ("mode", .pullbackMode .recomputed)]⟩ ]

/-- One binding of every frame primitive, most of them in several frames. -/
private def frames : List Source.Declaration := [
  encode "enc_b" "Tangent" "Coords" "b", decode "dec_b" "Coords" "Tangent" "b",
  encode "coenc_b" "Cotangent" "CoCoords" "b", decode "codec_b" "CoCoords" "Cotangent" "b",
  encode "enc_c" "Tangent" "Coords" "c", encode "coenc_c" "Cotangent" "CoCoords" "c",
  encode "enc_e" "Tangent" "Coords" "e",
  encode "enc_bx" "Tangent" "Coords" "bx", encode "coenc_bx" "Cotangent" "CoCoords" "bx",
  encode "enc_d" "Tangent" "Coords" "d",
  vector "vec_b" "Coords" "b", vector "covec_b" "CoCoords" "b", vector "vec_c" "Coords" "c",
  vector "vec_e" "Coords" "e", vector "vec_bx" "Coords" "bx", vector "vec_z" "Coords" "z",
  matrix "mat_bc" "b" "c", matrix "mat_cb" "c" "b", matrix "mat_bb" "b" "b", matrix "mat_ee" "e" "e",
  matrix "mat_bxbx" "bx" "bx", matrix "mat_zz" "z" "z", matrix "mat_bz" "b" "z", matrix "mat_zb" "z" "b",
  transition "tr_bb" "b" "b", transition "tr_bc" "b" "c", transition "tr_cb" "c" "b",
  transition "tr_be" "b" "e", transition "tr_eb" "e" "b", transition "tr_ce" "c" "e",
  primitive "apply" ⟨"frame_apply", [ref "frame_map" "FrameMap", ref "coords" "Coords"]⟩,
  primitive "coapply" ⟨"frame_coapply", [ref "frame_map" "FrameMap", ref "cocoords" "CoCoords"]⟩,
  primitive "fcompose" ⟨"frame_compose", [ref "frame_map" "FrameMap"]⟩,
  primitive "fpairing" ⟨"frame_pairing", [ref "cocoords" "CoCoords", ref "coords" "Coords"]⟩,
  primitive "comp0" ⟨"frame_component", [ref "family" "Coords", nat "index" 0]⟩,
  primitive "comp1" ⟨"frame_component", [ref "family" "Coords", nat "index" 1]⟩,
  primitive "comp2" ⟨"frame_component", [ref "family" "Coords", nat "index" 2]⟩,
  primitive "entry00" ⟨"frame_entry", [ref "frame_map" "FrameMap", nat "row" 0, nat "column" 0]⟩,
  primitive "entry01" ⟨"frame_entry", [ref "frame_map" "FrameMap", nat "row" 0, nat "column" 1]⟩,
  primitive "entry10" ⟨"frame_entry", [ref "frame_map" "FrameMap", nat "row" 1, nat "column" 0]⟩,
  primitive "entry11" ⟨"frame_entry", [ref "frame_map" "FrameMap", nat "row" 1, nat "column" 1]⟩,
  primitive "entry20" ⟨"frame_entry", [ref "frame_map" "FrameMap", nat "row" 2, nat "column" 0]⟩,
  primitive "same_coords" ⟨"frame_equal", [ref "family" "Coords"]⟩,
  primitive "same_cocoords" ⟨"frame_equal", [ref "family" "CoCoords"]⟩,
  primitive "same_map" ⟨"frame_equal", [ref "family" "FrameMap"]⟩,
  primitive "at" ⟨"frame_at", [ref "family" "Coords", ref "map_family" "Smooth"]⟩ ]

private def declarations : List Source.Declaration := base ++ frames

private def program (ds := declarations) : Source.Program := {
  file := "frames", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }

private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"frame regression failed: {label}")

private def with' (extra : List Source.Declaration) : Source.Program := program (declarations ++ extra)

private def code (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => "accepted"
  | .error e => e.code

private def message (p : Source.Program) : String :=
  match Source.checkDeclarations p with
  | .ok _ => ""
  | .error e => e.message

private def mentions (text part : String) : Bool := (text.splitOn part).length > 1

private def rejectsWith (p : Source.Program) (expected text : String) : Bool :=
  code p == expected && mentions (message p) text

private def resolvedOf (p : Source.Program) : Option Core.Declarations :=
  match Source.checkDeclarations p with
  | .ok checked => some checked.resolved.declarations
  | .error _ => none

private def resolved : Option Core.Declarations := resolvedOf program
private def env : Core.Declarations := resolved.getD default
private def binding (name : String) : Option PrimitiveBinding := resolved.bind (·.primitive? (id name))
private def frameRef (name : String) : FrameRef :=
  match frameData? env.indexed (id name) with
  | some (_, object, matrix, inverse) => ⟨id name, object, matrix, inverse⟩
  | none => default

private def q (numerator : Int) (denominator : Nat := 1) : Rat := mkRat numerator denominator

#eval check "the common source checker accepts the frames and every frame binding" (code program == "accepted")
#eval check "declaration order independent" (code (program declarations.reverse) == "accepted")
#eval check "the profile without frame bindings is accepted on its own" (code (program base) == "accepted")

/-! ## The bindings embed their frames -/

#eval check "frame_encode and frame_decode embed the frame and take the variance of their fiber family"
  (binding "enc_b" == some (.frameEncode .tangent (id "Tangent") (id "Coords") (frameRef "b")) &&
    binding "coenc_b" == some (.frameEncode .cotangent (id "Cotangent") (id "CoCoords") (frameRef "b")) &&
    binding "dec_b" == some (.frameDecode .tangent (id "Coords") (id "Tangent") (frameRef "b")) &&
    binding "codec_b" == some (.frameDecode .cotangent (id "CoCoords") (id "Cotangent") (frameRef "b")))
#eval check "the embedded frame is the declaration: its object, P and Q"
  ((frameRef "b").object == id "Plane" &&
    FrameRuntime.matrixAt (frameRef "b").matrix [0, 0] == [[1, 1], [0, 2]] &&
    FrameRuntime.matrixAt (frameRef "b").inverse [0, 0] == [[1, q (-1) 2], [0, q 1 2]] &&
    FrameRuntime.matrixAt (frameRef "bx").matrix [3, 0] == [[1, 3], [0, 1]] &&
    FrameRuntime.matrixAt (frameRef "bx").inverse [3, 0] == [[1, -3], [0, 1]])
#eval check "frame_vector takes its object from its frame"
  (binding "vec_b" == some (.frameVector (id "Coords") (id "Smooth") (id "Plane") (id "b")) &&
    binding "vec_z" == some (.frameVector (id "Coords") (id "Smooth") (id "Pt") (id "z")))
#eval check "frame_matrix and frame_transition embed both frames"
  (binding "mat_bc" == some (.frameMatrix (id "Smooth") (id "FrameMap") (frameRef "b") (frameRef "c")) &&
    binding "mat_bz" == some (.frameMatrix (id "Smooth") (id "FrameMap") (frameRef "b") (frameRef "z")) &&
    binding "tr_bc" == some (.frameTransition (id "Smooth") (id "FrameMap") (frameRef "b") (frameRef "c")))
#eval check "the observations keep their family and indices"
  (binding "comp1" == some (.frameComponent (id "Coords") 1) &&
    binding "entry10" == some (.frameEntry (id "FrameMap") 1 0) &&
    binding "same_map" == some (.frameEqual (id "FrameMap")) &&
    binding "at" == some (.frameAt (id "Coords") (id "Smooth")))
#eval check "every frame binding is valid and none allocates"
  (env.primitives.all fun entry => validPrimitiveBinding env.indexed entry.binding && !entry.binding.allocates)
#eval check "the operand counts"
  ((["enc_b", "dec_b", "mat_bc", "tr_bc", "apply", "fcompose", "comp0", "entry01", "same_map", "at"].map
      fun name => (binding name).map (·.arity env.indexed)) ==
    [some 1, some 1, some 2, some 1, some 2, some 2, some 1, some 1, some 2, some 2] &&
    (binding "vec_b").map (·.arity env.indexed) == some 3 && (binding "vec_z").map (·.arity env.indexed) == some 1)

/-! ## An executable Core module -/

private def frameIndex (name : String) : Index := .frame (id name)
private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (x y : String) : Core.Result := ⟨.indexed ⟨id "Smooth", [obj x, obj y]⟩, none⟩
private def tangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Tangent", [obj x]⟩, none⟩
private def cotangentType (x : String) : Core.Result := ⟨.indexed ⟨id "Cotangent", [obj x]⟩, none⟩
private def coordsType (b : String) : Core.Result := ⟨.indexed ⟨id "Coords", [frameIndex b]⟩, none⟩
private def cocoordsType (b : String) : Core.Result := ⟨.indexed ⟨id "CoCoords", [frameIndex b]⟩, none⟩
private def mapType (b c : String) : Core.Result := ⟨.indexed ⟨id "FrameMap", [frameIndex b, frameIndex c]⟩, none⟩
private def bool : Core.Result := ⟨.pure .bool, none⟩
private def pairType : Core.Result := ⟨.pure (.pair .int), none⟩
private def prim (name : String) (arguments : List Core.Term) (result : Core.Result) : Core.Term :=
  .primitive (id name) arguments result
private def planeAt (x y : Int) : Core.Term := prim "plane_at" [.integer x, .integer y] (smoothType "Pt" "Plane")
private def vplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "vplane" [point, .integer x, .integer y] (tangentType "Plane")
private def dplane (point : Core.Term) (x y : Int) : Core.Term :=
  prim "dplane" [point, .integer x, .integer y] (cotangentType "Plane")
private def vec (name frameName : String) (point : Core.Term) (x y : Int) : Core.Term :=
  prim name [point, .integer x, .integer y] (coordsType frameName)
private def covec (frameName : String) (point : Core.Term) (x y : Int) : Core.Term :=
  prim "covec_b" [point, .integer x, .integer y] (cocoordsType frameName)
private def enc (frameName : String) (value : Core.Term) : Core.Term :=
  prim s!"enc_{frameName}" [value] (coordsType frameName)
private def coenc (frameName : String) (value : Core.Term) : Core.Term :=
  prim s!"coenc_{frameName}" [value] (cocoordsType frameName)
private def smoothMap (name x y : String) : Core.Term := prim name [] (smoothType x y)
private def composeSmooth (after before : Core.Term) (x y : String) : Core.Term :=
  prim "compose" [after, before] (smoothType x y)
private def frameMatrix (name : String) (map point : Core.Term) (b c : String) : Core.Term :=
  prim name [map, point] (mapType b c)
private def frameTransition (b c : String) (point : Core.Term) : Core.Term :=
  prim s!"tr_{b}{c}" [point] (mapType b c)
private def apply (matrix array : Core.Term) (c : String) : Core.Term := prim "apply" [matrix, array] (coordsType c)
private def coapply (matrix array : Core.Term) (b : String) : Core.Term :=
  prim "coapply" [matrix, array] (cocoordsType b)
private def fcompose (after before : Core.Term) (b d : String) : Core.Term :=
  prim "fcompose" [after, before] (mapType b d)
private def sameCoords (left right : Core.Term) : Core.Term := prim "same_coords" [left, right] bool
private def sameCocoords (left right : Core.Term) : Core.Term := prim "same_cocoords" [left, right] bool
private def sameMap (left right : Core.Term) : Core.Term := prim "same_map" [left, right] bool
private def sameVector (left right : Core.Term) : Core.Term := prim "same_vector" [left, right] bool
private def sameCovector (left right : Core.Term) : Core.Term := prim "same_covector" [left, right] bool
private def entry (row column : Nat) (matrix : Core.Term) : Core.Term := prim s!"entry{row}{column}" [matrix] pairType
private def numerator (value : Core.Term) : Core.Term := .project .int true value
private def denominator (value : Core.Term) : Core.Term := .project .int false value
private def equals (left : Core.Term) (right : Int) : Core.Term := .binary .eq left (.integer right) bool
/-- A pair equals the reduced fraction `a / b`. -/
private def isFraction (value : Core.Term) (a b : Int) : Core.Term :=
  .binary .and (equals (numerator value) a) (equals (denominator value) b) bool
private def guarded (condition : Core.Term) (code : Int) (rest : Core.Term) : Core.Term :=
  .branch condition rest (.integer code) ⟨.pure .int, none⟩
private def notE (value : Core.Term) : Core.Term := .unary .not value bool

private def p : Core.Term := planeAt 1 2
private def q' : Core.Term := planeAt 3 (-1)
private def F : Core.Term := smoothMap "F" "Plane" "Plane"
private def G : Core.Term := smoothMap "G" "Plane" "Plane"
private def R : Core.Term := smoothMap "R" "Plane" "Plane"
private def Fp : Core.Term := composeSmooth F p "Pt" "Plane"
/-- `v = (5, -6)` and `α = (2, 3)` at `p`. -/
private def v : Core.Term := vplane p 5 (-6)
private def alpha : Core.Term := dplane p 2 3
private def ptAt : Core.Term := prim "pt_at" [] (smoothType "Pt" "Pt")

private def frameMain : Core.Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    -- Adequacy (C4): Q_b v = (8, -3) and P_bᵀ α = (2, 8); decoding recovers v and α.
    guarded (sameCoords (enc "b" v) (vec "vec_b" "b" p 8 (-3))) 1 <|
    guarded (sameVector (prim "dec_b" [vec "vec_b" "b" p 8 (-3)] (tangentType "Plane")) v) 2 <|
    guarded (sameCocoords (coenc "b" alpha) (covec "b" p 2 8)) 3 <|
    guarded (sameCovector (prim "codec_b" [covec "b" p 2 8] (cotangentType "Plane")) alpha) 4 <|
    guarded (sameCoords (enc "e" v) (vec "vec_e" "e" p 5 (-6))) 5 <|
    -- The frame bx at p: Q_bx(p) v = (11, -6).
    guarded (sameCoords (enc "bx" v) (vec "vec_bx" "bx" p 11 (-6))) 6 <|
    -- Pairing (C6): -8 in the coordinate frame, in b and in bx.
    guarded (isFraction (prim "pairing" [alpha, v] pairType) (-8) 1) 7 <|
    guarded (isFraction (prim "fpairing" [coenc "b" alpha, enc "b" v] pairType) (-8) 1) 8 <|
    guarded (isFraction (prim "fpairing" [coenc "bx" alpha, enc "bx" v] pairType) (-8) 1) 9 <|
    -- Mismatched points read (0, 0).
    guarded (isFraction (prim "fpairing" [coenc "b" alpha, enc "b" (vplane q' 5 (-6))] pairType) 0 0) 10 <|
    -- Transitions (C5): b → b is the identity, b → c → b is b → b, b → c → e is b → e,
    -- and T_bc carries the array in b to the array in c.
    guarded (sameCoords (apply (frameTransition "b" "b" p) (enc "b" v) "b") (enc "b" v)) 11 <|
    guarded (sameMap (fcompose (frameTransition "c" "b" p) (frameTransition "b" "c" p) "b" "b")
      (frameTransition "b" "b" p)) 12 <|
    guarded (sameMap (fcompose (frameTransition "c" "e" p) (frameTransition "b" "c" p) "b" "e")
      (frameTransition "b" "e" p)) 13 <|
    guarded (sameCoords (apply (frameTransition "b" "c" p) (enc "b" v) "c") (enc "c" v)) 14 <|
    -- The roadmap identity (C7): M_bc = [[1, 3], [1/3, 1/3]] differs from M_ee = J; both
    -- decode to J, and coapply in frames is the pullback.
    guarded (isFraction (entry 0 1 (frameMatrix "mat_bc" F p "b" "c")) 3 1) 15 <|
    guarded (isFraction (entry 1 0 (frameMatrix "mat_bc" F p "b" "c")) 1 3) 16 <|
    guarded (isFraction (entry 0 1 (frameMatrix "mat_ee" F p "e" "e")) 1 1) 17 <|
    guarded (isFraction (entry 1 0 (frameMatrix "mat_ee" F p "e" "e")) 2 1) 18 <|
    guarded (sameMap (fcompose (frameTransition "c" "e" Fp)
        (fcompose (frameMatrix "mat_bc" F p "b" "c") (frameTransition "e" "b" p) "e" "c") "e" "e")
      (frameMatrix "mat_ee" F p "e" "e")) 19 <|
    guarded (sameCocoords (coapply (frameMatrix "mat_bc" F p "b" "c") (coenc "c" (dplane Fp 1 1)) "b")
      (coenc "b" (prim "pullback" [F, p, dplane Fp 1 1] (cotangentType "Plane")))) 20 <|
    guarded (sameCocoords (coapply (frameMatrix "mat_bc" F p "b" "c") (coenc "c" (dplane Fp 1 1)) "b")
      (covec "b" p 3 7)) 21 <|
    -- The matrix of a composite (C8): M_bb(G ∘ F at p) = M_cb(G at F(p)) · M_bc(F at p).
    guarded (sameMap (fcompose (frameMatrix "mat_cb" G Fp "c" "b") (frameMatrix "mat_bc" F p "b" "c") "b" "b")
      (frameMatrix "mat_bb" (composeSmooth G F "Plane" "Plane") p "b" "b")) 22 <|
    -- The point-dependent frame at two points (C9): the target frame is read at F(p).
    guarded (isFraction (entry 0 0 (frameMatrix "mat_bxbx" F p "bx" "bx")) (-5) 1) 23 <|
    guarded (isFraction (entry 0 0 (frameMatrix "mat_bxbx" F q' "bx" "bx")) 3 1) 24 <|
    guarded (prim "at" [enc "bx" v, p] bool) 25 <|
    guarded (notE (prim "at" [enc "bx" v, q'] bool)) 26 <|
    guarded (notE (sameCoords (apply (frameMatrix "mat_bxbx" F q' "bx" "bx") (enc "bx" v) "bx")
      (apply (frameMatrix "mat_bxbx" F q' "bx" "bx") (enc "bx" v) "bx"))) 27 <|
    -- Composing maps whose middle points differ gives the failure value (C10).
    guarded (notE (sameMap (fcompose (frameTransition "c" "b" q') (frameTransition "b" "c" p) "b" "b")
      (fcompose (frameTransition "c" "b" q') (frameTransition "b" "c" p) "b" "b"))) 28 <|
    -- Degenerate cases (C11): a rank-deficient map sends (3, -1) in b to 0 in c, and maps
    -- of sizes 0 × 0, 0 × 2 and 2 × 0 are values.
    guarded (sameCoords (apply (frameMatrix "mat_bc" R p "b" "c") (vec "vec_b" "b" p 3 (-1)) "c")
      (vec "vec_c" "c" (composeSmooth R p "Pt" "Plane") 0 0)) 29 <|
    guarded (sameMap (frameMatrix "mat_zz" (smoothMap "idPt" "Pt" "Pt") ptAt "z" "z")
      (frameMatrix "mat_zz" (smoothMap "idPt" "Pt" "Pt") ptAt "z" "z")) 30 <|
    guarded (sameMap (frameMatrix "mat_bz" (smoothMap "toPt" "Plane" "Pt") p "b" "z")
      (frameMatrix "mat_bz" (smoothMap "toPt" "Plane" "Pt") p "b" "z")) 31 <|
    guarded (sameMap (frameMatrix "mat_zb" (smoothMap "fromPt" "Pt" "Plane") ptAt "z" "b")
      (frameMatrix "mat_zb" (smoothMap "fromPt" "Pt" "Plane") ptAt "z" "b")) 32 <|
    guarded (sameCoords (prim "vec_z" [ptAt] (coordsType "z")) (prim "vec_z" [ptAt] (coordsType "z"))) 33 <|
    -- Components.
    guarded (isFraction (prim "comp1" [enc "c" v] pairType) (-11) 3) 34 <|
    .integer 42 }

/-- The frames of this regression as one audited Core module. -/
def frameFixture : Core.Module := ⟨env, [frameMain], some 0⟩

private def evaluate (term : Core.Term) : Option Core.Semantics.Value :=
  Core.Semantics.eval frameFixture 64 (fun _ => none) term

#eval check "the frame Core module is accepted" (Core.Typing.checkModule frameFixture true).isOk
#eval check "the frame Core module evaluates to 42" (evaluate frameMain.body == some (.integer 42))
#eval check "the array of v in b is (8, -3) at p, a frame array and not a fiber"
  (evaluate (enc "b" v) == some (.indexed (.frameArray .tangent (some ⟨[1, 2], [8, -3]⟩))))
#eval check "the matrix of F at p in (b, c) keeps both points"
  (evaluate (frameMatrix "mat_bc" F p "b" "c") ==
    some (.indexed (.frameMatrix (some ⟨[1, 2], [3, 2], [[1, 3], [q 1 3, q 1 3]]⟩))))
#eval check "the transition b → c at p is Q_c P_b over p"
  (evaluate (frameTransition "b" "c" p) ==
    some (.indexed (.frameMatrix (some ⟨[1, 2], [1, 2], [[1, 1], [q (-1) 3, q 1 3]]⟩))))
#eval check "the empty frame of a point gives the 0 × 0, 0 × 2 and 2 × 0 maps"
  (evaluate (frameMatrix "mat_zz" (smoothMap "idPt" "Pt" "Pt") ptAt "z" "z") ==
      some (.indexed (.frameMatrix (some ⟨[], [], []⟩))) &&
    evaluate (frameMatrix "mat_bz" (smoothMap "toPt" "Plane" "Pt") p "b" "z") ==
      some (.indexed (.frameMatrix (some ⟨[1, 2], [], []⟩))) &&
    evaluate (frameMatrix "mat_zb" (smoothMap "fromPt" "Pt" "Plane") ptAt "z" "b") ==
      some (.indexed (.frameMatrix (some ⟨[], [1, 2], [[], []]⟩))))
#eval check "applying a map to an array over another point gives the failure value"
  (evaluate (apply (frameTransition "b" "c" q') (enc "b" v) "c") == some (.indexed (.frameArray .tangent none)))

/-! ## Erasure: the runtime evaluator agrees on the erased values -/

private def agrees (name : String) (values : List Core.Semantics.Value) : Bool :=
  match binding name with
  | some b => match Core.Semantics.evalPrimitive env.indexed b values with
    | some value => match values.mapM Core.Semantics.erasePrimitiveValue, Core.Semantics.erasePrimitiveValue value with
      | some inputs, some output => Core.Semantics.evalRuntimePrimitive b inputs == some output
      | _, _ => false
    | none => false
  | none => false

private def pointValue (x y : Int) : Core.Semantics.Value := .indexed (.smooth (SmoothRuntime.intPoint [x, y]))
private def fiberValue (variance : Variance) (x y : Int) : Core.Semantics.Value :=
  .indexed (.fiber variance (some ⟨[1, 2], [(x : Rat), (y : Rat)]⟩))
private def arrayValue (variance : Variance) (x y : Rat) : Core.Semantics.Value :=
  .indexed (.frameArray variance (some ⟨[1, 2], [x, y]⟩))
private def matrixValue : Core.Semantics.Value :=
  .indexed (.frameMatrix (some ⟨[1, 2], [1, 2], [[1, 1], [q (-1) 3, q 1 3]]⟩))
private def fValue : Option Core.Semantics.Value := evaluate F

#eval check "every frame entry erases to its runtime evaluator"
  (agrees "enc_b" [fiberValue .tangent 5 (-6)] && agrees "coenc_b" [fiberValue .cotangent 2 3] &&
    agrees "dec_b" [arrayValue .tangent 8 (-3)] && agrees "codec_b" [arrayValue .cotangent 2 8] &&
    agrees "vec_b" [pointValue 1 2, .integer 8, .integer (-3)] &&
    agrees "tr_bc" [pointValue 1 2] &&
    (fValue.map fun f => agrees "mat_bc" [f, pointValue 1 2]) == some true &&
    agrees "apply" [matrixValue, arrayValue .tangent 8 (-3)] &&
    agrees "coapply" [matrixValue, arrayValue .cotangent 2 8] &&
    agrees "fcompose" [matrixValue, matrixValue] &&
    agrees "fpairing" [arrayValue .cotangent 2 8, arrayValue .tangent 8 (-3)] &&
    agrees "comp1" [arrayValue .tangent 8 (-3)] && agrees "entry10" [matrixValue] &&
    agrees "same_coords" [arrayValue .tangent 8 (-3), arrayValue .tangent 8 (-3)] &&
    agrees "same_map" [matrixValue, matrixValue] &&
    agrees "at" [arrayValue .tangent 8 (-3), pointValue 1 2])
#eval check "a fiber is not a frame array: the frame entries take only frame values"
  (((binding "dec_b").all fun b =>
      (Core.Semantics.evalPrimitive env.indexed b [fiberValue .tangent 8 (-3)]).isNone) &&
    ((binding "enc_b").all fun b =>
      (Core.Semantics.evalPrimitive env.indexed b [arrayValue .tangent 5 (-6)]).isNone))

/-! ## Static frame identity in Core (C3, C10) -/

private def rejected (body : Core.Term) : Bool :=
  !(Core.Typing.checkModule ⟨env, [{ frameMain with body := guarded body 1 (.integer 42) }], some 0⟩ true).isOk

#eval check "an array in c where the map's source frame is b is rejected"
  (rejected (sameCoords (apply (frameTransition "b" "c" p) (enc "c" v) "c") (enc "c" v)))
#eval check "composing maps whose middle frames differ is rejected"
  (rejected (sameMap (fcompose (frameTransition "b" "c" p) (frameTransition "b" "c" p) "b" "c")
    (frameTransition "b" "c" p)))
#eval check "pairing arrays of two frames is rejected"
  (rejected (equals (numerator (prim "fpairing" [coenc "b" alpha, enc "c" v] pairType)) 0))
#eval check "coapply of an array in the map's source frame is rejected"
  (rejected (sameCocoords (coapply (frameMatrix "mat_bc" F p "b" "c") (coenc "b" alpha) "b") (coenc "b" alpha)))
#eval check "a frame on another object of the same dimension is rejected"
  (rejected (sameCoords (enc "d" v) (enc "d" v)))
#eval check "Coords against Tangent and CoCoords against Coords are rejected"
  (rejected (sameVector (prim "dec_b" [v] (tangentType "Plane")) v) &&
    rejected (sameCoords (enc "b" (coenc "b" alpha)) (enc "b" v)) &&
    rejected (equals (numerator (prim "fpairing" [enc "b" v, enc "b" v] pairType)) 0) &&
    rejected (sameCoords (coenc "b" alpha) (coenc "b" alpha)))
#eval check "an array checked at a point of another object is rejected"
  (rejected (prim "at" [enc "b" v, prim "plane2_at" [.integer 1, .integer 2] (smoothType "Pt" "Plane2")] bool))
#eval check "a matrix of a map from another object is rejected"
  (rejected (sameMap (frameMatrix "mat_bc" (smoothMap "toPt" "Plane" "Pt") p "b" "c")
    (frameMatrix "mat_bc" (smoothMap "toPt" "Plane" "Pt") p "b" "c")))
#eval check "a component or an entry beyond the dimension of its frame is rejected"
  (rejected (equals (numerator (prim "comp2" [enc "b" v] pairType)) 0) &&
    rejected (equals (numerator (entry 2 0 (frameTransition "b" "c" p))) 0) &&
    rejected (equals (numerator (entry 0 0 (frameMatrix "mat_zz" (smoothMap "idPt" "Pt" "Pt") ptAt "z" "z"))) 0) &&
    !rejected (equals (numerator (entry 1 1 (frameTransition "b" "c" p))) 0))
#eval check "a result type with the wrong frame is rejected"
  (rejected (sameCoords (apply (frameTransition "b" "c" p) (enc "b" v) "b") (enc "b" v)) &&
    rejected (sameMap (prim "tr_bc" [p] (mapType "c" "b")) (prim "tr_bc" [p] (mapType "c" "b"))))

/-! ## The role table names both frames -/

private def explain (name : String) (operands : List ValueType) (result : ValueType) :
    Option Source.Diagnostics.PrimitiveFailure :=
  (binding name).bind fun b => Source.Diagnostics.explainPrimitive env.indexed b [] 0 operands result

private def explained (name : String) (operands : List ValueType) (result : ValueType) : String :=
  match explain name operands result with
  | some failure => Source.Diagnostics.explainFailure env none {} name "" failure
  | none => ""

private def coordsValue (b : String) : ValueType := .indexed ⟨id "Coords", [frameIndex b]⟩
private def cocoordsValue (b : String) : ValueType := .indexed ⟨id "CoCoords", [frameIndex b]⟩
private def mapValue (b c : String) : ValueType := .indexed ⟨id "FrameMap", [frameIndex b, frameIndex c]⟩

#eval check "frame_apply names the map's source frame and the array's frame"
  (explain "apply" [mapValue "b" "c", coordsValue "c"] (coordsValue "c") ==
      some (.role (.frame "array" "frame" (id "b") (id "c") "the map's source frame")) &&
    explained "apply" [mapValue "b" "c", coordsValue "c"] (coordsValue "c") ==
      "apply requires an array with frame b (the map's source frame), but the supplied array has frame c")
#eval check "frame_compose names the middle frames"
  (explained "fcompose" [mapValue "c" "e", mapValue "b" "b"] (mapValue "b" "e") ==
    "fcompose requires a second map with target frame c (the first map's source frame), but the supplied " ++
      "second map has target frame b")
#eval check "frame_pairing and frame_coapply name both frames"
  (explained "fpairing" [cocoordsValue "b", coordsValue "c"] .integerPair ==
      "fpairing requires a vector array with frame b (the covector array's frame), but the supplied vector " ++
        "array has frame c" &&
    explained "coapply" [mapValue "b" "c", cocoordsValue "b"] (cocoordsValue "b") ==
      "coapply requires an array with frame c (the map's target frame), but the supplied array has frame b")
#eval check "frame_decode names its declared frame"
  (explained "dec_b" [coordsValue "c"] (.indexed ⟨id "Tangent", [obj "Plane"]⟩) ==
    "dec_b requires an array with frame b (the primitive's frame), but the supplied array has frame c")
#eval check "frame_encode names the frame's object"
  (explained "enc_b" [.indexed ⟨id "Tangent", [obj "Plane2"]⟩] (coordsValue "b") ==
    "enc_b requires a vector with object Plane (the frame's object), but the supplied vector has object Plane2")
#eval check "a component beyond the dimension names the frame and its dimension"
  (explain "comp2" [coordsValue "b"] .integerPair == some (.role (.bound "array" "frame" "component" (id "b") 2 2)) &&
    explained "comp2" [coordsValue "b"] .integerPair ==
      "comp2 reads component 2 of an array with frame b, but b is a frame of a 2-dimensional object, so the " ++
        "component must be below 2" &&
    explain "entry20" [mapValue "b" "c"] .integerPair ==
      some (.role (.bound "map" "target frame" "row" (id "c") 2 2)))
#eval check "frame_at names the object of the array's frame"
  (explain "at" [coordsValue "b", .indexed ⟨id "Smooth", [obj "Pt", obj "Plane2"]⟩] .boolean ==
    some (.role (.object "point" "target" (.global (id "Plane")) (.global (id "Plane2"))
      "the object of the array's frame")))

/-! ## Source rejections -/

#eval check "a frame binding naming a declaration that is not a frame is E_FRAME"
  (rejectsWith (with' [encode "bad" "Tangent" "Coords" "Tangent"]) "E_FRAME"
      "the frame of `frame_encode` must be a frame, but `frames::Tangent` is not a frame declaration" &&
    rejectsWith (with' [matrix "bad" "b" "Plane"]) "E_FRAME"
      "the target frame of `frame_matrix` must be a frame, but `frames::Plane` is not a frame declaration" &&
    rejectsWith (with' [vector "bad" "Coords" "F"]) "E_FRAME" "`frames::F` is not a frame declaration")
#eval check "an encoding between families of two variances is E_FRAME"
  (rejectsWith (with' [encode "bad" "Tangent" "CoCoords" "b"]) "E_FRAME"
      ("`frame_encode` relates the vector family `frames::Tangent` to `frames::CoCoords`, which holds the " ++
        "arrays of covectors") &&
    rejectsWith (with' [decode "bad" "Coords" "Cotangent" "b"]) "E_FRAME" "`frame_decode` relates the covector")
#eval check "a transition between frames of two objects is E_ENDPOINT, naming both"
  (rejectsWith (with' [transition "bad" "b" "d"]) "E_ENDPOINT"
    ("`frame_transition` changes between two frames of one object, but the source frame `frames::b` is on " ++
      "`frames::Plane` and the target frame `frames::d` is on `frames::Plane2`"))
#eval check "a frame binding with a family of the wrong representation fails the audit"
  (rejectsWith (with' [primitive "bad" ⟨"frame_apply", [ref "frame_map" "Coords", ref "coords" "Coords"]⟩])
      "E_TYPE" "the family `frames::Coords` of the `frame_apply` primitive `frames::bad` must have the representation `frame_map`" &&
    rejectsWith (with' [primitive "bad" ⟨"frame_pairing", [ref "cocoords" "Coords", ref "coords" "Coords"]⟩])
      "E_TYPE" "must have the representation `frame_covector`" &&
    rejectsWith (with' [vector "bad" "Tangent" "b"]) "E_TYPE"
      "must have the representation `frame_vector` or `frame_covector`" &&
    rejectsWith (with' [matrix "bad" "b" "c" (maps := "Coords")]) "E_TYPE" "must have the representation `frame_map`" &&
    rejectsWith (with' [primitive "bad" ⟨"frame_equal", [ref "family" "Tangent"]⟩]) "E_TYPE"
      "must have the representation `frame_vector`, `frame_covector` or `frame_map`")

private def index : Namespace.Indexed := program.indexed
private def scope : Namespace.Scope := ⟨pkg, []⟩
private def reported (form : Source.Primitive) : Option (String × String) :=
  match (Source.resolvePrimitive index scope form).run [] with
  | .ok _ => none
  | .error diagnostic => some (diagnostic.code, diagnostic.message)
private def undefinedName (name : String) : Option (String × String) :=
  some ("E_NAME", s!"undefined name '{name}' in this module")

#eval check "the frame families resolve their frames first"
  ((primitiveFamily? "frame_encode").map (·.resolutionOrder) == some ["frame", "fiber", "coords"] &&
    (primitiveFamily? "frame_matrix").map (·.resolutionOrder) == some ["source", "target", "map_family", "frame_map"])
#eval check "a frame binding with two unresolvable names reports its frame first"
  (reported ⟨"frame_encode", [ref "fiber" "MissingFiber", ref "coords" "Coords", ref "frame" "MissingFrame"]⟩ ==
      undefinedName "MissingFrame" &&
    reported ⟨"frame_matrix", [ref "map_family" "MissingSmooth", ref "frame_map" "FrameMap", ref "source" "b",
      ref "target" "MissingTarget"]⟩ == undefinedName "MissingTarget")

/-! ## Tampered Core: the independent audit rechecks every embedded frame -/

private def tamper (extra : PrimitiveBinding) : Bool :=
  !Core.validDeclarations { env with primitives := env.primitives ++ [⟨id "bad", extra⟩] }

private def identityPolys : PolyMatrix := FrameDeclarations.polyIdentity 2

#eval check "accepted Core is valid" (Core.validDeclarations env)
#eval check "a fresh copy of a correct binding is accepted, so the forgeries below fail on their data"
  (!tamper (.frameEncode .tangent (id "Tangent") (id "Coords") (frameRef "b")) &&
    !tamper (.frameTransition (id "Smooth") (id "FrameMap") (frameRef "b") (frameRef "c")))
#eval check "a forged embedded matrix or inverse is rejected"
  (tamper (.frameEncode .tangent (id "Tangent") (id "Coords") { frameRef "b" with inverse := identityPolys }) &&
    tamper (.frameDecode .tangent (id "Coords") (id "Tangent") { frameRef "b" with matrix := identityPolys }) &&
    tamper (.frameMatrix (id "Smooth") (id "FrameMap") (frameRef "b") { frameRef "c" with inverse := identityPolys }) &&
    tamper (.frameTransition (id "Smooth") (id "FrameMap") { frameRef "b" with matrix := identityPolys } (frameRef "c")))
#eval check "a forged embedded object is rejected"
  (tamper (.frameEncode .tangent (id "Tangent") (id "Coords") { frameRef "b" with object := id "Plane2" }) &&
    tamper (.frameVector (id "Coords") (id "Smooth") (id "Plane2") (id "b")))
#eval check "an embedded frame that is not a frame declaration is rejected"
  (tamper (.frameEncode .tangent (id "Tangent") (id "Coords") ⟨id "Plane", id "Plane", identityPolys, identityPolys⟩))
#eval check "a forged transition between frames of two objects is rejected"
  (tamper (.frameTransition (id "Smooth") (id "FrameMap") (frameRef "b") (frameRef "d")))
#eval check "a forged variance or swapped families are rejected"
  (tamper (.frameEncode .cotangent (id "Tangent") (id "Coords") (frameRef "b")) &&
    tamper (.frameEncode .tangent (id "Tangent") (id "CoCoords") (frameRef "b")) &&
    tamper (.frameApply (id "FrameMap") (id "CoCoords")) && tamper (.frameCoapply (id "FrameMap") (id "Coords")) &&
    tamper (.framePairing (id "Coords") (id "CoCoords")) && tamper (.frameCompose (id "Coords")) &&
    tamper (.frameComponent (id "FrameMap") 0) && tamper (.frameEntry (id "Coords") 0 0) &&
    tamper (.frameAt (id "FrameMap") (id "Smooth")) && tamper (.frameEqual (id "Tangent")))

/-! ## Generated code declares each frame matrix once -/

private def generatedCode (function : Core.Function) : Option String := do
  let .ok checked := Core.Typing.checkModule ⟨env, [function], some 0⟩ true | none
  (Core.Codegen.generate checked).toOption
private def generatedChecks (checks : List Core.Term) : Option String :=
  generatedCode { frameMain with body := checks.foldr (fun condition rest => guarded condition 1 rest) (.integer 42) }
private def occurrences (part : String) (source : Option String) : Option Nat :=
  source.map fun text => (text.splitOn part).length - 1

private def frameType : String := "def frame_0 : List (List VastitasKernel.AlgebraRuntime.Poly) :=\n"
private def oneEncoding : Option String := generatedChecks [sameCoords (enc "b" v) (vec "vec_b" "b" p 8 (-3))]
private def sixEncodings : Option String :=
  generatedChecks (List.replicate 6 (sameCoords (enc "b" v) (vec "vec_b" "b" p 8 (-3))))

#eval check "one call and six calls of an encoding declare its frame matrix once"
  ([oneEncoding, sixEncodings].map (occurrences frameType) == [some 1, some 1] &&
    [oneEncoding, sixEncodings].map (occurrences "(VastitasKernel.FrameRuntime.encodeTangent frame_0 ") ==
      [some 1, some 6] &&
    occurrences "frame_1" oneEncoding == some 0)
#eval check "a module with frame calls imports the frame runtime"
  (occurrences "import VastitasKernel.FrameRuntime\n" (generatedCode frameMain) == some 1 &&
    occurrences "import VastitasKernel.FrameRuntime\n" (generatedChecks []) == some 0)
#eval check "the frame primitives lower to the frame and smooth runtimes"
  (let source := generatedCode frameMain
  ["VastitasKernel.FrameRuntime.encodeCotangent frame_", "VastitasKernel.FrameRuntime.decodeTangent frame_",
    "VastitasKernel.FrameRuntime.decodeCotangent frame_", "VastitasKernel.FrameRuntime.frameMatrix ",
    "VastitasKernel.FrameRuntime.transition ", "VastitasKernel.FrameRuntime.apply ",
    "VastitasKernel.FrameRuntime.coapply ", "VastitasKernel.FrameRuntime.compose ",
    "VastitasKernel.FrameRuntime.entry ", "VastitasKernel.FrameRuntime.matrixEqual ",
    "VastitasKernel.SmoothRuntime.fiberEqual ", "VastitasKernel.SmoothRuntime.pairing ",
    "VastitasKernel.SmoothRuntime.component ", "VastitasKernel.SmoothRuntime.fiberAt ",
    "VastitasKernel.SmoothRuntime.vector "].all fun call => (occurrences call source).any (· > 0))
#eval check "frame_equal compares maps with matrixEqual and arrays with fiberEqual"
  (occurrences "(VastitasKernel.FrameRuntime.matrixEqual " (generatedChecks [sameMap (frameTransition "b" "b" p)
      (frameTransition "b" "b" p)]) == some 1 &&
    occurrences "(VastitasKernel.SmoothRuntime.fiberEqual " (generatedChecks [sameCoords (enc "b" v) (enc "b" v)]) ==
      some 1 &&
    occurrences "matrixEqual" (generatedChecks [sameCoords (enc "b" v) (enc "b" v)]) == some 0)
#eval check "a lowering with the wrong operand count is the arity error"
  ((binding "mat_bc").all fun b => !(b.contract.render (.share []) ["f"]).toBool)

/-! ## Protocols 7 and 8 do not admit the frame primitives; protocol 9 does -/

open Lean in
private def decodes (j : Json) (algebraic : Bool) : Bool :=
  (Wire.declarationBody j (numerical := true) (algebraic := algebraic)).isOk
open Lean in
private def spanJson : Json :=
  Json.mkObj [("start", (0 : Nat)), ("end", (0 : Nat)), ("line", (1 : Nat)), ("column", (1 : Nat))]
open Lean in
private def pathJson (name : String) : Json := Json.mkObj [("path", Json.arr #[Json.str name]), ("span", spanJson)]
open Lean in
private def primitiveJson (fields : List (String × Json)) : Json := Json.mkObj
  [("kind", Json.str "primitive"), ("name", Json.str "X"), ("public", Json.bool true), ("span", spanJson),
    ("binding", Json.mkObj fields)]
open Lean in
private def form (op : String) (paths : List (String × String)) (naturals : List (String × Json) := []) : Json :=
  primitiveJson ((("op", Json.str op) :: paths.map fun (field, name) => (field, pathJson name)) ++ naturals)

open Lean in
private def forms : List Json := [
  form "frame_encode" [("fiber", "Tangent"), ("coords", "Coords"), ("frame", "b")],
  form "frame_decode" [("coords", "Coords"), ("fiber", "Tangent"), ("frame", "b")],
  form "frame_vector" [("coords", "Coords"), ("map_family", "Smooth"), ("frame", "b")],
  form "frame_matrix" [("map_family", "Smooth"), ("frame_map", "FrameMap"), ("source", "b"), ("target", "c")],
  form "frame_transition" [("map_family", "Smooth"), ("frame_map", "FrameMap"), ("source", "b"), ("target", "c")],
  form "frame_apply" [("frame_map", "FrameMap"), ("coords", "Coords")],
  form "frame_coapply" [("frame_map", "FrameMap"), ("cocoords", "CoCoords")],
  form "frame_compose" [("frame_map", "FrameMap")],
  form "frame_pairing" [("cocoords", "CoCoords"), ("coords", "Coords")],
  form "frame_component" [("family", "Coords")] [("index", Json.str "1")],
  form "frame_entry" [("frame_map", "FrameMap")] [("row", Json.str "0"), ("column", Json.str "1")],
  form "frame_equal" [("family", "Coords")],
  form "frame_at" [("family", "Coords"), ("map_family", "Smooth")]]

#eval check "protocol 9 decodes each frame primitive" (forms.all (decodes · true))
#eval check "protocols 7 and 8 reject each frame primitive" (forms.all (!decodes · false))
#eval check "the forms are exactly the frame families of the table"
  (forms.length == 13 && (families.filter (·.op.startsWith "frame_")).length == 13)
open Lean in
#eval check "a natural field is an unsigned decimal string of at most 64 digits"
  (decodes (form "frame_component" [("family", "Coords")] [("index", Json.str (String.ofList (List.replicate 64 '9')))])
      true &&
    ["", "-1", "+1", "1.5", "0x1", "1_0", " 1", String.ofList (List.replicate 65 '1')].all (fun text =>
      !decodes (form "frame_component" [("family", "Coords")] [("index", Json.str text)]) true) &&
    !decodes (form "frame_component" [("family", "Coords")] [("index", (1 : Nat))]) true &&
    !decodes (form "frame_component" [("family", "Coords")]) true &&
    !decodes (form "frame_entry" [("frame_map", "FrameMap")] [("row", Json.str "0")]) true)
open Lean in
#eval check "the wire carries no frame data: a matrix, an inverse or an object is an unknown field"
  (!decodes (form "frame_encode" [("fiber", "Tangent"), ("coords", "Coords"), ("frame", "b"), ("object", "Plane")])
      true &&
    !decodes (primitiveJson [("op", Json.str "frame_transition"), ("map_family", pathJson "Smooth"),
      ("frame_map", pathJson "FrameMap"), ("source", pathJson "b"), ("target", pathJson "c"),
      ("inverse", Json.arr #[])]) true &&
    !decodes (form "frame_matrix" [("map_family", "Smooth"), ("frame_map", "FrameMap"), ("source", "b")]) true)

end VastitasKernel.Indexed.FrameRegression
