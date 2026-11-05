import VastitasKernel.IndexedCodegen

set_option autoImplicit false

/-! Frozen copies of the lowering of a primitive call (`renderPrimitive`) and
of the shared bases (`bases`) of `IndexedCodegen` as they were before the
registry entries rendered them (#622, step 4a), with the proof that the
derived ones agree with them: on every module, the literals the entries share
are the frozen bases, and on every binding and every list of rendered
operands, the entry's lowering with those literals is the frozen text or the
frozen error. The text helpers the frozen rows use are frozen with them, so
the theorems also check that `Lowering` writes the same names and literals.
The lowering is the table moved into `PrimitiveBinding.contract` whose frozen
copy lives here rather than in `IndexedPrimitiveLegacyRegression`, which keeps
the frozen copies of the other moved tables. The module is deleted at the end of the migration; the emit goldens
(`tests/fixtures/emit`) stay. -/
namespace VastitasKernel.Indexed.PrimitiveRenderLegacyRegression
open VastitasKernel.Indexed.Core (Declarations)

/-! ## The lowering before the registry, verbatim -/

private def runtime (name : String) : String := "VastitasKernel.IndexedRuntime." ++ name
private def algebra (name : String) : String := "VastitasKernel.AlgebraRuntime." ++ name
private def smooth (name : String) : String := "VastitasKernel.SmoothRuntime." ++ name

/-- Exact rational literals of the checked map data; no source spelling is used. -/
private def renderRat (value : Rat) : String := s!"(mkRat ({value.num} : Int) {value.den})"
private def renderTerm' (term : AlgebraRuntime.Term) : String :=
  s!"({algebra "Term.mk"} {term.monomial} {renderRat term.coefficient})"
private def renderPoly (p : AlgebraRuntime.Poly) : String :=
  s!"([{String.intercalate ", " (p.map renderTerm')}] : {algebra "Poly"})"
private def renderPolys (ps : List AlgebraRuntime.Poly) : String :=
  s!"([{String.intercalate ", " (ps.map renderPoly)}] : List {algebra "Poly"})"
/-- A checked metric matrix, row by row, with exact rational entries. -/
private def renderMatrix (matrix : SmoothRuntime.Matrix) : String :=
  let rows := matrix.map fun row => s!"[{String.intercalate ", " (row.map renderRat)}]"
  s!"([{String.intercalate ", " rows}] : {smooth "Matrix"})"
/-- The distinct bases of the checked relative constants, in declaration order.
Each is emitted once as `basis_k` and shared by every map over that object. -/
private def bases (env : Declarations) : List (List AlgebraRuntime.Poly) :=
  env.primitives.foldl (fun found entry => match entry.binding with
    | .relativeConstant _ map => if found.contains map.basis then found else found ++ [map.basis]
    | _ => found) []
private def basisName (index : Nat) : String := s!"basis_{index}"
private def renderMap (env : Declarations) (map : AlgebraRuntime.Map) : String :=
  let basis := match (bases env).idxOf? map.basis with
    | some index => basisName index
    | none => renderPolys map.basis
  s!"({algebra "Map.mk"} {map.arity} {basis} {renderPolys map.images})"

private def application (name : String) (args : List String) : String :=
  "(" ++ String.intercalate " " (name :: args) ++ ")"

private def renderPrimitive (env : Declarations) (binding : PrimitiveBinding) (args : List String) :
    Except String String :=
  match binding, args with
  | .descriptor _, [dimension] => .ok (application (runtime "descriptor") [dimension])
  | .global _, [] => .ok (runtime "baseObject")
  | .origin .., [object] => .ok (application (runtime "origin") [object, runtime "baseObject"])
  | .identity .., [object] => .ok (application (runtime "identity") [object])
  | .compose .., [after, before] => .ok (application (runtime "compose") [after, before])
  | .apply .., [map, point] => .ok (application (runtime "apply") [map, point])
  | .dimension .., [object] => .ok s!"({object}).dimension"
  | .relativeConstant _ map, [] => .ok (renderMap env map)
  | .relativeCompose _, [after, before] => .ok (application (algebra "Map.compose") [after, before])
  | .relativeView .., [map] => .ok map
  | .relativeEqual _, [left, right] => .ok (application (algebra "Map.same") [left, right])
  | .relativeCoefficient _ _ _ coordinate monomial, [map] =>
      .ok (application (algebra "Map.coefficient") [map, toString coordinate, toString monomial])
  | .relativePair .., [left, right] => .ok (application (algebra "Map.pair") [left, right])
  | .relativeIntPoint .., coordinates =>
      .ok (application (algebra "Map.intPoint") [s!"[{String.intercalate ", " coordinates}]"])
  | .smoothConstant _ map, [] => .ok (application (smooth "Program.primitive") [renderMap env map])
  | .smoothCompose _, [after, before] => .ok (application (smooth "Program.compose") [after, before])
  | .smoothEqual _, [left, right] => .ok (application (smooth "same") [left, right])
  | .smoothIntPoint .., coordinates =>
      .ok (application (smooth "intPoint") [s!"[{String.intercalate ", " coordinates}]"])
  | .smoothComposite _, [program] => .ok (application (smooth "composite") [program])
  | .fiberVector .., point :: components =>
      .ok (application (smooth "vector") [point, s!"[{String.intercalate ", " components}]"])
  | .fiberAt .., [value, point] => .ok (application (smooth "fiberAt") [value, point])
  | .fiberEqual _, [left, right] => .ok (application (smooth "fiberEqual") [left, right])
  | .fiberComponent _ _ coordinate, [value] => .ok (application (smooth "component") [value, toString coordinate])
  | .fiberPairing .., [covector, vector] => .ok (application (smooth "pairing") [covector, vector])
  | .cotangentPullback _ _ mode, [map, point, seed] =>
      let mode := match mode with
        | .saved => smooth "PullbackMode.saved"
        | .recomputed => smooth "PullbackMode.recomputed"
      .ok (application (smooth "pullback") [mode, map, point, seed])
  | .differential .., [function, point] => .ok (application (smooth "differential") [function, point])
  | .linearize .., [map, point] => .ok (application (smooth "linearize") [map, point])
  | .cotangentBackward .., [tape, seed] => .ok (application (smooth "backward") [tape, seed])
  | .metricFlat _ _ gram _ _, [vector] => .ok (application (smooth "flat") [renderMatrix gram, vector])
  | .metricSharp _ _ _ _ inverse _ _, [covector] =>
      .ok (application (smooth "sharp") [renderMatrix inverse, covector])
  | _, _ => .error "closed primitive arity mismatch"

/-! ## Agreement -/

/-- The literals one entry contributes are the basis of a relative constant and
nothing else, folded as the frozen `bases` folds them. -/
private theorem literals_agrees (found : List (List AlgebraRuntime.Poly)) (binding : PrimitiveBinding) :
    binding.contract.literals.foldl
      (fun found literal => if found.contains literal then found else found ++ [literal]) found =
      match binding with
      | .relativeConstant _ map => if found.contains map.basis then found else found ++ [map.basis]
      | _ => found := by
  cases binding <;> rfl

/-- The literals the entries of every module share are the frozen bases. -/
theorem bases_agrees (env : Declarations) :
    PrimitiveDescriptor.sharedLiterals (env.primitives.map fun entry => entry.binding.contract) = bases env := by
  unfold PrimitiveDescriptor.sharedLiterals bases
  rw [List.foldl_map]
  exact congrArg (fun step => List.foldl step [] env.primitives)
    (funext fun found => funext fun entry => literals_agrees found entry.binding)

/-- With the frozen bases as the module's shared literals, the lowering of
every binding is the frozen one on every list of rendered operands: by the
binding and the list shapes the rows distinguish (no, one, two, three, or four
or more operands), both sides are the same text or the same error. -/
theorem render_agrees (env : Declarations) (binding : PrimitiveBinding) (args : List String) :
    binding.contract.render ⟨bases env⟩ args = renderPrimitive env binding args := by
  cases binding <;> rcases args with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl

/-- What `IndexedCodegen` renders for a call (`Codegen.renderPrimitive` with the
module's `Codegen.renderContext`) is the frozen text on every module, binding and
list of rendered operands. -/
theorem renderPrimitive_agrees (env : Declarations) (binding : PrimitiveBinding) (args : List String) :
    Core.Codegen.renderPrimitive (Core.Codegen.renderContext env) binding args =
      renderPrimitive env binding args := by
  unfold Core.Codegen.renderPrimitive Core.Codegen.renderContext
  rw [bases_agrees]
  exact render_agrees env binding args

end VastitasKernel.Indexed.PrimitiveRenderLegacyRegression
