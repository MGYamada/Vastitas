import VastitasKernel.ResourceStatementSource

set_option autoImplicit false

/-! Physical numerical declarations and view operations in resource bodies. -/
namespace VastitasKernel.ResourceViewSource
open AssemblyText ResourceSource ResourceStatementSource

inductive View where
  | fields (tokens : List ExactLexeme)
  | metric (name basis involution : String) (gram : Storage.Numerical.Gram)

private def call (name : String) (arguments : List (List ExactLexeme)) : List ExactLexeme :=
  [.ident name, .punctuation '('] ++ (arguments.intersperse [.punctuation ',']).flatten ++ [.punctuation ')']

private def declaration (kind name constructor : String) (arguments : List (List ExactLexeme)) : View :=
  .fields ([.ident kind, .ident name, .punctuation '='] ++ call constructor arguments)

private def names (ns : List String) : List (List ExactLexeme) :=
  ns.map fun name => [.ident name]

private def layout (l : Storage.Layout) : List ExactLexeme :=
  layoutFields (some l.offset) (.dimension l.rows) (.dimension l.columns) (.dimension l.leading) l.transposed

private def numerical : NumericalOperation → Option View
  | .space n p dim => some (declaration "space" n "linear" [[.reference p.path p.span], [.dimension dim]])
  | .basis n s => some (declaration "basis" n "basis" (names [s]))
  | .involution n s => some (declaration "involution" n "canonical" (names [s]))
  | .dualSpace n s => some (declaration "space" n "dual" (names [s]))
  | .conjugateSpace n s inv => some (declaration "space" n "conjugate" (names [s,inv]))
  | .derivedBasis n b s => some (declaration "basis" n "derived" (names [b,s]))
  | .metric n b inv gram => some (.metric n b inv gram)
  | .transform n p (.dual s t) => some (declaration "map" n "dual" (names [p,s,t]))
  | .transform n p (.conjugate s t inv) => some (declaration "map" n "conjugate" (names [p,s,t,inv]))
  | .transform n p (.adjoint s t) => some (declaration "map" n "adjoint" (names [p,s,t]))
  | .vector n loan b => some (declaration "vector" n "view" (names [loan,b]))
  | .conjugateVector n v b inv => some (declaration "vector" n "conjugate" (names [v,b,inv]))
  | .map n loan s t => some (declaration "map" n "view" (names [loan,s,t]))
  | .ownedMap n owner l s t => some (declaration "map" n "owned" ([[.ident owner], layout l] ++ names [s,t]))
  | .packMap n owner => some (declaration "map" n "pack" (names [owner]))
  | .unpackMap p s b owner => some (.fields ([.ident "unpack", .ident p] ++ call "as" (names [s,b,owner])))
  | .ownedView n loan owner => some (declaration "map" n "view" (names [loan,owner]))
  | .adjointInto i o s t .nativeFast => some (.fields (call "adjoint_into" (names [i,o,s,t,"NativeFast"])))
  | .hermitianDiagonal a b o m scratch l .nativeFast =>
    let temp := call "scratch" [[.ident scratch], layout l]
    some (.fields (call "hermitian_diagonal" (names [a,b,o,m] ++ [temp] ++ names ["overwrite","NativeFast"])))
  | .borrowOwned .. | .evaluate .. | .gemm .. => none

private def runtime : RuntimeNumerical → Option View
  | .space n p dim => some (declaration "runtime_space" n "linear" [[.reference p.path p.span], [extent dim]])
  | .basis n s => some (declaration "runtime_basis" n "basis" (names [s]))
  | .map n loan s t => some (declaration "runtime_map" n "view" (names [loan,s,t]))
  | .gemm .. => none

def select : Statement → Option (View × Span)
  | .numerical op span => (numerical op).map (·, span)
  | .runtimeNumerical op span => (runtime op).map (·, span)
  | _ => none

private def gramEntry (i : Int) : Parser Unit := do
  consume fun f before => do
    let t ← f.next before
    let negative := t.kind matches .symbol '-'
    unless i == 0 || negative == (i < 0) do throw "Gram entry sign differs from the source"
    ResourceLiteralText.expectNat f (if negative then t.after else before) i.natAbs

def spelling : View → Parser Unit
  | .fields fields => tokens fields
  | .metric name basis inv gram => do
    let kind := match gram with | .identity => "orthonormal" | .scaledIdentity _ => "scaled_identity" | .diagonal _ => "diagonal"
    tokens [.ident "metric", .ident name, .punctuation '=', .ident kind, .punctuation '(',
      .ident basis, .punctuation ',', .ident inv]
    match gram with
    | .identity => pure ()
    | .scaledIdentity i => token (.punctuation ','); gramEntry i
    | .diagonal entries =>
      tokens [.punctuation ',', .punctuation '[']
      for (entry, index) in entries.zipIdx do
        if index != 0 then token (.punctuation ',')
        gramEntry entry
      token (.closeList ']' (!entries.isEmpty))
    token (.punctuation ')')

end VastitasKernel.ResourceViewSource
