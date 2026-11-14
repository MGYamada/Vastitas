import VastitasKernel.CotangentRegression
import VastitasKernel.IndexedReverse
import VastitasKernel.IndexedCodegen
import VastitasKernel.RegressionSupport

set_option autoImplicit false

/-! Compiled reverse Core (#623) on the Core module of `CotangentRegression`
and on a second module with a function parameter, `let`s, a tape bound by a
`let`, a branch and a recomputing pullback. The checks run the actual
compilation, its validation and the Core audit, the Core semantics before and
after, and the lowering. Every forged module below must be rejected. These are
executable regressions, not proofs. -/
namespace VastitasKernel.Indexed.Core.ReverseCoreRegression


private def pkg : Namespace.PackageId := ⟨"/cotangent/Vastitas.toml", "cotangent", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩

private def check := RegressionSupport.check "reverse Core regression failed"

private def int : Result := ⟨.pure .int, none⟩
private def run (module : Module) (term : Term) : Option Semantics.Value :=
  Semantics.eval module 512 (fun _ => none) term
private def mainCall : Term := .call 0 [] [] int

/-! ## The Core module of the cotangent regression -/

private def source : Module := CotangentRegression.cotangentFixture
private def generated : Module := (Reverse.generate source).1
private def entries : List Reverse.Entry := (Reverse.generate source).2

mutual
/-- The reverse sites of a term in the order the compilation finds them:
operands first. -/
private def sitesOf (env : Declarations) : Term → List Term
  | .primitive declaration arguments result =>
    let inner := sitesOfAll env arguments
    match Reverse.ruleOf env declaration with
    | .pass _ => inner ++ [.primitive declaration arguments result]
    | _ => inner
  | .unary _ value _ | .project _ _ value | .natToInt value | .ascribe _ value | .scope value => sitesOf env value
  | .binary _ left right _ | .pair _ left right => sitesOf env left ++ sitesOf env right
  | .branch condition yes no _ => sitesOf env condition ++ sitesOf env yes ++ sitesOf env no
  | .call _ arguments _ _ => sitesOfAll env arguments
  | .letE _ value body => sitesOf env value ++ sitesOf env body
  | _ => []

/-- The reverse sites of a list of terms, in order. -/
private def sitesOfAll (env : Declarations) : List Term → List Term
  | [] => []
  | term :: rest => sitesOf env term ++ sitesOfAll env rest
end

private def mainBody (module : Module) : Term :=
  ((module.functions.find? (·.id == 0)).map Function.body).getD .unit

/-- One site compiled on its own: the module with its generated functions and
the rewritten site. -/
private def compileOne (module : Module) (site : Term) : Module × Term × List Reverse.Entry :=
  let state : Reverse.State :=
    ⟨Reverse.maxSymbol site + 1, (id "main").scope, 0, 1000, [], module.declarations.ids.length⟩
  let (term, state) := Reverse.rewrite module.declarations [] state site
  ({ module with
      declarations := { module.declarations with
        primitives := module.declarations.primitives ++ state.entries.flatMap Reverse.Entry.declarations }
      functions := state.entries.map Reverse.Entry.generated ++ module.functions }, term, state.entries)

private def sourceSites : List Term := sitesOf source.declarations (mainBody source)

#eval check "the source module is accepted and evaluates to 42"
  ((Typing.checkModule source true).isOk && run source mainCall == some (.integer 42))
#eval check "the fixture has one entry per reverse site"
  (entries.length == sourceSites.length)
#eval check "every site of the fixture is compiled"
  (entries.length == 45 && sourceSites.all fun site => !(compileOne source site).2.2.isEmpty)
#eval check "the generated module passes the Core audit and validates"
  ((Typing.checkModule generated true).isOk && Reverse.validate source entries generated)
#eval check "the compilation stage accepts the module"
  (match Typing.checkModule source true with
   | .ok checked => match Reverse.compile checked with
     | .ok compiled => Reverse.moduleEq compiled.core.module generated && compiled.entries == entries
     | .error _ => false
   | .error _ => false)
#eval check "the compiled module evaluates to 42" (run generated mainCall == some (.integer 42))
#eval check "each compiled site evaluates to the value of the source site, failures included"
  (sourceSites.all fun site =>
    let (module, term, _) := compileOne source site
    (run source site).isSome && run module term == run source site)
#eval check "a declared map is pulled back by its Jacobian table; composite(..) is the one opaque step"
  (let kinds := entries.flatMap fun entry => entry.site.steps.map (·.kind)
   (kinds.filter (· == .opaque)).length == 1 && kinds.length - 1 == (kinds.filter fun
     | .declared _ _ _ => true
     | .opaque => false).length)
#eval check "the recomputing pullback keeps its mode; every other site saves"
  ((entries.filter fun entry => entry.site.mode == .recomputed).length == 1)
#eval check "the differential builds its seed at the primal value"
  ((entries.filter fun entry => entry.seed == .unit).length == 4)
#eval check "a module without a reverse site compiles to itself"
  (let plain : Module := { source with functions := [{ (source.functions.headD default) with body := .integer 42 }] }
   (Reverse.generate plain).2.isEmpty && Reverse.moduleEq (Reverse.generate plain).1 plain &&
     Reverse.validate plain [] plain)

/-! ## The lowering -/

private def lowered : String :=
  match Typing.checkModule generated true with
  | .ok checked => match Codegen.generate checked with
    | .ok text => text
    | .error message => s!"error: {message}"
  | .error diagnostic => s!"error: {diagnostic.message}"

private def count (text needle : String) : Nat := (text.splitOn needle).length - 1

/-- The end of a Jacobian table written as a literal. -/
private def tableType : String := ": List (List VastitasKernel.AlgebraRuntime.Poly))"
/-- The declaration of the table `[[coefficient · t]]` of a map of the line. -/
private def tableDefinition (index coefficient : Nat) : String :=
  s!"def jacobian_{index} : List (List VastitasKernel.AlgebraRuntime.Poly) :=\n  " ++
    s!"([([([(VastitasKernel.AlgebraRuntime.Term.mk [1] (mkRat ({coefficient} : Int) 1))] : " ++
    "VastitasKernel.AlgebraRuntime.Poly)] : List VastitasKernel.AlgebraRuntime.Poly)] " ++ tableType ++ "\n"
/-- A step of one output that names the declared table `index`. -/
private def stepCall (index : Nat) : String := s!"(VastitasKernel.SmoothRuntime.jacobianStep 1 jacobian_{index} "

#eval check "the lowering calls the compiled steps and no runtime reverse pass at a compiled site"
  (count lowered "VastitasKernel.SmoothRuntime.jacobianStep " > 0 &&
    count lowered "VastitasKernel.SmoothRuntime.applyPoint " > 0 &&
    count lowered "VastitasKernel.SmoothRuntime.differential " == 0 &&
    count lowered "VastitasKernel.SmoothRuntime.backward " == 0 &&
    count lowered "VastitasKernel.SmoothRuntime.linearize " == 0 &&
    count lowered "PullbackMode.recomputed" == 0 &&
    count lowered "VastitasKernel.SmoothRuntime.pullback " == 1)
#eval check "one generated function per site, before the source functions"
  (count lowered "def f_" == entries.length + 1 &&
    (lowered.splitOn "def f_0 ").length == 2 &&
    ((lowered.splitOn "def f_0 ").headD "").length > ((lowered.splitOn "def f_1 ").headD "").length)

/-- The site `pullback(gf(), 3, dt at 18)`: one step along `gf(t) = 2t²` by
its Jacobian table `[[4t]]`. -/
private def gfSite : Term :=
  .primitive (id "pullback") [.primitive (id "gf") [] ⟨.indexed ⟨id "Smooth", [.object (.global (id "Line")),
    .object (.global (id "Line"))]⟩, none⟩,
    .primitive (id "line_at") [.integer 3] ⟨.indexed ⟨id "Smooth", [.object (.global (id "Pt")),
      .object (.global (id "Line"))]⟩, none⟩,
    .primitive (id "dline") [.primitive (id "line_at") [.integer 18] ⟨.indexed ⟨id "Smooth",
      [.object (.global (id "Pt")), .object (.global (id "Line"))]⟩, none⟩, .integer 1]
      ⟨.indexed ⟨id "Cotangent", [.object (.global (id "Line"))]⟩, none⟩]
    ⟨.indexed ⟨id "Cotangent", [.object (.global (id "Line"))]⟩, none⟩

/-- The library whose root is the generated function of that site, with the
function's id. -/
private def gfLibrary : Option (Nat × String) :=
  let (module, _, compiledEntries) := compileOne source gfSite
  match compiledEntries, Typing.checkModule module false with
  | [entry], .ok checked =>
    (Codegen.generateLibrary checked [entry.function]).toOption.map fun text => (entry.function, text)
  | _, _ => none

/-- The parameters and the body of the generated function. -/
private def gfFunction : String :=
  match gfLibrary with
  | some (function, text) =>
    let lines := ((text.splitOn s!"def f_{function} ").getD 1 "").splitOn "\n"
    lines.getD 0 "" ++ "\n" ++ lines.getD 1 ""
  | none => "error: not compiled"

#eval check "the generated function of one declared step, byte for byte"
  (gfFunction == "(v_0 : VastitasKernel.SmoothRuntime.Program) (v_1 : VastitasKernel.SmoothRuntime.Program) " ++
    "(v_2 : (Option VastitasKernel.SmoothRuntime.Fiber)) : (Option VastitasKernel.SmoothRuntime.Fiber) :=\n" ++
    "  (VastitasKernel.SmoothRuntime.jacobianStep 1 jacobian_0 v_0 v_1 v_2)")
#eval check "the library of that function declares the table of the step, byte for byte, and no map"
  (gfLibrary.map (fun (_, text) => (count text (tableDefinition 0 4), count text tableType, count text "def map_")) ==
    some (1, 1, 0))

/-! ## Forged reverse Core

Each module below changes the compiled module or its ledger in one place. The
validation rejects every one; the Core audit alone accepts some of them. -/

mutual
/-- Replace the first subterm that `change` rewrites; the flag says whether
one was found. -/
private def replaceFirst (change : Term → Option Term) (term : Term) : Term × Bool :=
  match change term with
  | some replaced => (replaced, true)
  | none =>
    match term with
    | .primitive declaration arguments result =>
      let (arguments, found) := replaceFirstAll change arguments
      (.primitive declaration arguments result, found)
    | .call function arguments substitution result =>
      let (arguments, found) := replaceFirstAll change arguments
      (.call function arguments substitution result, found)
    | .branch condition yes no result =>
      let (condition, found) := replaceFirst change condition
      if found then (.branch condition yes no result, true) else
      let (yes, found) := replaceFirst change yes
      if found then (.branch condition yes no result, true) else
      let (no, found) := replaceFirst change no
      (.branch condition yes no result, found)
    | .letE symbol value body =>
      let (value, found) := replaceFirst change value
      if found then (.letE symbol value body, true) else
      let (body, found) := replaceFirst change body
      (.letE symbol value body, found)
    | .unary operator value result =>
      let (value, found) := replaceFirst change value
      (.unary operator value result, found)
    | .binary operator left right result =>
      let (left, found) := replaceFirst change left
      if found then (.binary operator left right result, true) else
      let (right, found) := replaceFirst change right
      (.binary operator left right result, found)
    | .project element first value =>
      let (value, found) := replaceFirst change value
      (.project element first value, found)
    | .scope value =>
      let (value, found) := replaceFirst change value
      (.scope value, found)
    | .ascribe annotation value =>
      let (value, found) := replaceFirst change value
      (.ascribe annotation value, found)
    | _ => (term, false)

/-- Replace the first subterm of a list that `change` rewrites. -/
private def replaceFirstAll (change : Term → Option Term) : List Term → List Term × Bool
  | [] => ([], false)
  | term :: rest =>
    let (term, found) := replaceFirst change term
    if found then (term :: rest, true) else
    let (rest, found) := replaceFirstAll change rest
    (term :: rest, found)
end

private def generatedIds : List Nat := entries.map (·.function)
private def isGenerated (fx : Function) : Bool := generatedIds.contains fx.id

/-- Change the first generated function with at least two steps. -/
private def onTwoSteps (change : Function → Function) : Module :=
  let target := (entries.find? fun entry => entry.site.steps.length ≥ 2 && entry.site.mode == .saved).map (·.function)
  { generated with functions := generated.functions.map (fun fx =>
      if target == some fx.id then change fx else fx) }

private def rejected (module : Module) (ledger := entries) : Bool := !Reverse.validate source ledger module
private def audited (module : Module) : Bool := (Typing.checkModule module true).isOk

/-- Swap the input and the output point of the first step in a body. -/
private def swapPoints (fx : Function) : Function :=
  { fx with body := (replaceFirst (fun
      | .primitive declaration [input, output, seed] result =>
        some (.primitive declaration [output, input, seed] result)
      | _ => none) fx.body).1 }

/-- A body that returns its seed. -/
private def seedOnly (fx : Function) : Function :=
  match fx.parameters.getLast? with
  | some seed => { fx with body := .variable seed.symbol seed.result }
  | none => fx

#eval check "a backward function that returns its seed is well typed but rejected"
  (let forged := onTwoSteps seedOnly
   audited forged && rejected forged)
/-- The two steps of a body in the opposite order: the step along the first
map reads the seed, and the step along the second map gives the result. -/
private def swapSteps (fx : Function) : Function :=
  match fx.body with
  | .letE symbol (.primitive later laterArguments laterResult) (.primitive earlier earlierArguments earlierResult) =>
    { fx with body := (Term.letE symbol (.primitive earlier laterArguments laterResult)
        (.primitive later earlierArguments earlierResult)) }
  | _ => fx

/-- The generated function of the first site whose two steps share their
objects, so that the steps may run in either order: the shears of the plane. -/
private def shearSite : Option Nat :=
  (entries.find? fun entry => match entry.site.steps with
    | [first, second] => first.source == first.target && second.source == second.target &&
        first.kind != .opaque && second.kind != .opaque
    | _ => false).map (·.function)

#eval check "the steps of a backward function in the opposite order are well typed, change the result and are rejected"
  (let forged := { generated with functions := generated.functions.map (fun fx =>
      if shearSite == some fx.id then swapSteps fx else fx) }
   shearSite.isSome && audited forged && rejected forged && run forged mainCall != some (.integer 42))
#eval check "a step with its input and output points exchanged is rejected"
  (let forged := onTwoSteps swapPoints
   rejected forged)
#eval check "a residual from another point: a site passing the input point as the image is rejected"
  (let forged := { generated with functions := generated.functions.map fun fx =>
      if fx.id == 0 then { fx with body := (replaceFirst (fun
        | .call callee (first :: second :: rest) substitution result =>
          if generatedIds.contains callee && first.result == second.result then
            some (.call callee (first :: first :: rest) substitution result) else none
        | _ => none) fx.body).1 } else fx }
   audited forged && rejected forged)
#eval check "a step along another declared map is rejected"
  (let forged := { generated with declarations := { generated.declarations with
      primitives := generated.declarations.primitives.map fun entry => match entry.binding with
        | .cotangentJacobian cotangent application _ =>
          ⟨entry.id, .cotangentJacobian cotangent application ⟨1, [], [AlgebraRuntime.Poly.var 1 0]⟩⟩
        | _ => entry } }
   rejected forged)
#eval check "a generated function under another owner is rejected"
  (let forged := { generated with functions := generated.functions.map (fun fx =>
      if isGenerated fx then { fx with definition := id "forged" } else fx) }
   audited forged && rejected forged)
#eval check "a missing generated function fails the Core audit"
  (let forged := { generated with functions := generated.functions.filter (fun fx =>
      !(isGenerated fx && generatedIds.head? == some fx.id)) }
   !audited forged && rejected forged)
#eval check "an extra function is rejected"
  (let forged := { generated with functions := generated.functions ++ [{ (generated.functions.headD default) with
      id := 9999 }] }
   rejected forged)
#eval check "a site left uncompiled is rejected"
  (let forged := { generated with functions := generated.functions.map (fun fx =>
      if fx.id == 0 then (source.functions.find? (·.id == 0)).getD fx else fx) }
   audited forged && rejected forged)
#eval check "a generated function returning a covector over another object fails the Core audit"
  (let forged := onTwoSteps fun fx =>
      { fx with returnType := .indexed ⟨id "Cotangent", [.object (.global (id "Plane"))]⟩ }
   !audited forged && rejected forged)
#eval check "a forged ledger is rejected"
  (rejected generated (entries.map fun entry => { entry with site := { entry.site with mode := .recomputed } }) &&
    rejected generated (entries.drop 1))

/-! ## A function parameter, `let`s, a tape bound by a `let` and a branch -/

private def obj (name : String) : Index := .object (.global (id name))
private def smoothType (x y : String) : Result := ⟨.indexed ⟨id "Smooth", [obj x, obj y]⟩, none⟩
private def cotangentType (x : String) : Result := ⟨.indexed ⟨id "Cotangent", [obj x]⟩, none⟩
private def tapeType (x y : String) : Result := ⟨.indexed ⟨id "Tape", [obj x, obj y]⟩, none⟩
private def bool : Result := ⟨.pure .bool, none⟩
private def prim (name : String) (arguments : List Term) (result : Result) : Term :=
  .primitive (id name) arguments result
private def constant (name x y : String) : Term := prim name [] (smoothType x y)
private def compose (after before : Term) (x y : String) : Term := prim "compose" [after, before] (smoothType x y)
private def lineAt (value : Int) : Term := prim "line_at" [.integer value] (smoothType "Pt" "Line")
private def planeAt (x y : Int) : Term := prim "plane_at" [.integer x, .integer y] (smoothType "Pt" "Plane")
private def dline (point : Term) (component : Int) : Term :=
  prim "dline" [point, .integer component] (cotangentType "Line")
private def dplane (point : Term) (x y : Int) : Term :=
  prim "dplane" [point, .integer x, .integer y] (cotangentType "Plane")
private def same (left right : Term) : Term := prim "same_covector" [left, right] bool
private def guarded (condition : Term) (code : Int) (rest : Term) : Term := .branch condition rest (.integer code) int
private def var (symbol : Nat) (result : Result) : Term := .variable symbol result

/-- `differential(h, p)` for a parameter `h`: one opaque step. -/
private def gradient : Function := {
  id := 1, definition := id "gradient",
  parameters := [⟨0, smoothType "Plane" "Line"⟩, ⟨1, smoothType "Pt" "Plane"⟩],
  returnType := (cotangentType "Plane").type,
  body := prim "differential" [var 0 (smoothType "Plane" "Line"), var 1 (smoothType "Pt" "Plane")]
    (cotangentType "Plane") }

private def three : Term := lineAt 3
private def seed : Term := dline (lineAt 18) 1
private def m : Term := var 0 (smoothType "Line" "Line")
private def tape : Term := var 1 (tapeType "Line" "Line")
private def chosen : Term := var 2 (smoothType "Line" "Line")
private def twelve : Term := dline three 12

private def extendedMain : Function := {
  id := 0, definition := id "main", parameters := [], returnType := .pure .int
  body :=
    .letE 0 (.ascribe (.indexed ⟨id "Smooth", [obj "Line", obj "Line"]⟩)
      (compose (constant "g" "Plane" "Line") (constant "f" "Line" "Plane") "Line" "Line")) <|
    .letE 1 (prim "linearize" [m, three] (tapeType "Line" "Line")) <|
    .letE 2 (.branch (.boolean true) m (constant "gf" "Line" "Line") (smoothType "Line" "Line")) <|
    guarded (same (prim "pullback" [m, three, seed] (cotangentType "Line")) twelve) 1 <|
    guarded (same (prim "backward" [tape, seed] (cotangentType "Line")) twelve) 2 <|
    guarded (same (prim "backward" [tape, dline (lineAt 18) 2] (cotangentType "Line")) (dline three 24)) 3 <|
    guarded (same (prim "pullback" [chosen, three, seed] (cotangentType "Line")) twelve) 4 <|
    guarded (same (.call 1 [constant "g" "Plane" "Line", planeAt 1 2] [] (cotangentType "Plane"))
      (dplane (planeAt 1 2) 2 1)) 5 <|
    -- sq'(18) = 36 times 12 is 432.
    guarded (same (prim "pullback_recomputed" [compose (constant "sq" "Line" "Line") m "Line" "Line", three,
      dline (lineAt 324) 1] (cotangentType "Line")) (dline three 432)) 6 <|
    .integer 42 }

/-- The second module, also compiled by the native fixture script. -/
def extendedFixture : Module := { source with functions := [gradient, extendedMain] }
private def extended : Module := extendedFixture
private def extendedGenerated : Module := (Reverse.generate extended).1
private def extendedEntries : List Reverse.Entry := (Reverse.generate extended).2

#eval check "the extended module is accepted and evaluates to 42"
  ((Typing.checkModule extended true).isOk && run extended mainCall == some (.integer 42))
#eval check "its compiled module passes the Core audit, validates and evaluates to 42"
  ((Typing.checkModule extendedGenerated true).isOk && Reverse.validate extended extendedEntries extendedGenerated &&
    run extendedGenerated mainCall == some (.integer 42))
#eval check "the parameter h is one opaque step"
  (extendedEntries.any fun entry => entry.caller == 1 && entry.site.steps.map (·.kind) == [.opaque] &&
    entry.seed == .unit)
#eval check "the let-bound map is read through: two declared steps"
  (extendedEntries.any fun entry => entry.caller == 0 && entry.site.steps.length == 2 &&
    entry.site.steps.all fun step => step.kind != .opaque)
#eval check "both backward calls on the let-bound tape are compiled"
  ((extendedEntries.filter fun entry => entry.caller == 0 && entry.site.mode == .saved &&
    entry.site.steps.length == 2).length == 3)
#eval check "the map chosen by a branch is one opaque step"
  (extendedEntries.any fun entry => entry.site.steps.map (·.kind) == [.opaque] && entry.caller == 0)
#eval check "the recomputing pullback reads through the let: three declared steps"
  (extendedEntries.any fun entry => entry.site.mode == .recomputed && entry.site.steps.length == 3)

/-! ## Budgets

Doubling `let`s give a map of `2ⁿ` steps. The leaf budget `reverseLeaves`
stops the reading as soon as it is spent, so the compilation stays fast; a map
beyond it keeps opaque steps, which the runtime reverse pass pulls back. -/

/-- `a₀ := base`, `aᵢ₊₁ := compose(aᵢ, aᵢ)`, then a pullback along `aₙ` at 3. -/
private def doubling (base : String) (levels : Nat) (seedPoint : Int) : Function :=
  let line := smoothType "Line" "Line"
  let rec chain : Nat → Term → Term
    | 0, body => body
    | k + 1, body => .letE (levels - k) (compose (var (levels - k - 1) line) (var (levels - k - 1) line) "Line" "Line")
        (chain k body)
  { id := 0, definition := id "main", parameters := [], returnType := .pure .int
    body := .letE 0 (constant base "Line" "Line") <| chain levels <|
      guarded (same (prim "pullback" [var levels line, three, dline (lineAt seedPoint) 1] (cotangentType "Line"))
        (dline three 1)) 1 (.integer 42) }

private def doubled (base : String) (levels : Nat) (seedPoint : Int) : Module :=
  { source with functions := [doubling base levels seedPoint] }

#eval check "40 doubling lets compile within the leaf budget"
  (let (module, ledger) := Reverse.generate (doubled "sq" 40 3)
   ledger.length == 1 && (ledger.headD default).site.steps.length ≤ Limits.reverseLeaves &&
     (ledger.headD default).site.steps.any (·.kind == .opaque) && (Typing.checkModule module true).isOk)
#eval check "512 identities exceed the leaf budget, keep opaque steps and evaluate as the source does"
  (let module := doubled "idL" 9 3
   let (compiled, ledger) := Reverse.generate module
   ledger.length == 1 && (ledger.headD default).site.steps.any (·.kind == .opaque) &&
     (Typing.checkModule compiled true).isOk && run module mainCall == some (.integer 42) &&
     run compiled mainCall == some (.integer 42))
#eval check "a site whose declarations would exceed 4096 ids stays a call of the runtime reverse pass"
  (let site := gfSite
   let full : Reverse.State := ⟨Reverse.maxSymbol site + 1, (id "main").scope, 0, 1000, [], 4096 - 1⟩
   let room : Reverse.State := ⟨Reverse.maxSymbol site + 1, (id "main").scope, 0, 1000, [], 4096 - 2⟩
   (Reverse.rewrite source.declarations [] full site).2.entries.isEmpty &&
     (Reverse.rewrite source.declarations [] room site).2.entries.length == 1)

/-- `a₀ := g ∘ f`, then `aᵢ₊₁ := aᵢ` for `aliases` aliases, then the pullback
along the last alias at 3. -/
private def aliased (aliases : Nat) : Function :=
  let line := smoothType "Line" "Line"
  let rec chain : Nat → Term → Term
    | 0, body => body
    | k + 1, body => .letE (aliases - k) (var (aliases - k - 1) line) (chain k body)
  { id := 0, definition := id "main", parameters := [], returnType := .pure .int
    body := .letE 0 (compose (constant "g" "Plane" "Line") (constant "f" "Line" "Plane") "Line" "Line") <|
      chain aliases <|
        guarded (same (prim "pullback" [var aliases line, three, seed] (cotangentType "Line")) twelve) 1
          (.integer 42) }

#eval check "a chain of 200 aliases is read in one step: two declared steps, evaluated as the source"
  (let module : Module := { source with functions := [aliased 200] }
   let (compiled, ledger) := Reverse.generate module
   ledger.length == 1 && (ledger.headD default).site.steps.length == 2 &&
     (ledger.headD default).site.steps.all (·.kind != .opaque) && (Typing.checkModule compiled true).isOk &&
     run compiled mainCall == some (.integer 42) && run module mainCall == some (.integer 42))
#eval check "steps over the wrong objects fail the Core audit"
  (!audited (onTwoSteps swapSteps))

/-! ## Jacobian tables are declared once

A generated module declares each distinct Jacobian table of the backward
steps that its functions call, and every step names the declaration (#629).
The number of tables in the generated text does not depend on the number of
steps. Two declared maps with one table give one declaration, and a step that
no emitted function calls gives none. -/

/-- The fixture's declarations with `sqShifted(t) = t² + 1`, a second declared
map with the Jacobian table `[[2t]]` of `sq`. -/
private def withShifted : Declarations := { source.declarations with
  primitives := source.declarations.primitives ++ [⟨id "sqShifted",
    .smoothConstant ⟨id "Smooth", [obj "Line", obj "Line"]⟩ ⟨1, [], [[⟨[2], 1⟩, ⟨[0], 1⟩]]⟩⟩] }
/-- The pullback of `dt` at `image` along the declared `map` at 3 is
`expected · dt`: one site with one declared step. -/
private def pulled (map : String) (image expected : Int) : Term :=
  same (prim "pullback" [constant map "Line" "Line", three, dline (lineAt image) 1] (cotangentType "Line"))
    (dline three expected)
/-- A function that returns 42 when every check holds. -/
private def checking (checks : List Term) (function := 0) (name := "main") : Function := {
  id := function, definition := id name, parameters := [], returnType := .pure .int
  body := checks.foldr (fun condition rest => guarded condition 1 rest) (.integer 42) }
/-- The generated code of the compiled module of these functions, when the
compiled module evaluates to 42. -/
private def compiledCode (functions : List Function) : Option String := do
  let .ok checked := Typing.checkModule ⟨withShifted, functions, some 0⟩ true | none
  let .ok compiled := Reverse.compile checked | none
  if run compiled.core.module mainCall == some (.integer 42) then (Codegen.generate compiled.core).toOption else none
private def occurrences (part : String) (code : Option String) : Option Nat := code.map (count · part)
/-- `steps` sites, each with one step along `sq`. -/
private def alongSq (steps : Nat) : Option String := compiledCode [checking (List.replicate steps (pulled "sq" 9 6))]

#eval check "the generated modules hold 1, 2 and 6 steps along sq"
  ([1, 2, 6].map (fun steps => occurrences (stepCall 0) (alongSq steps)) == [some 1, some 2, some 6])
#eval check "1, 2 and 6 steps along one declared map give one Jacobian table"
  ([1, 2, 6].all fun steps => occurrences tableType (alongSq steps) == some 1 &&
    occurrences (tableDefinition 0 2) (alongSq steps) == some 1 &&
    occurrences "def jacobian_" (alongSq steps) == some 1)
#eval check "two declared maps with one Jacobian table give one declaration"
  (let code := compiledCode [checking [pulled "sq" 9 6, pulled "sqShifted" 10 6]]
   occurrences (tableDefinition 0 2) code == some 1 && occurrences tableType code == some 1 &&
     occurrences (stepCall 0) code == some 2 && occurrences "def map_" code == some 2)
#eval check "two different tables give two declarations, in the order of their steps"
  (let code := compiledCode [checking [pulled "gf" 18 12, pulled "sq" 9 6, pulled "gf" 18 12]]
   occurrences (tableDefinition 0 4) code == some 1 && occurrences (tableDefinition 1 2) code == some 1 &&
     occurrences tableType code == some 2 && occurrences (stepCall 0) code == some 2 &&
     occurrences (stepCall 1) code == some 1)
#eval check "a module without a step declares no table"
  (occurrences "jacobian_" (compiledCode [checking []]) == some 0)
#eval check "a step that no emitted function calls gives no declaration"
  (let functions := [checking [pulled "gf" 18 12] 1 "unused", checking [pulled "sq" 9 6]]
   let code := compiledCode functions
   -- Both sites are compiled, and only the step that `main` reaches is emitted.
   (Reverse.generate ⟨withShifted, functions, some 0⟩).2.length == 2 &&
     occurrences (tableDefinition 0 2) code == some 1 && occurrences tableType code == some 1 &&
     occurrences "def jacobian_" code == some 1 && occurrences "(mkRat (4 : Int) 1)" code == some 0)

/-! ## Definitions that `measure` does not read in full

`measure` reads a `let` with the fuel of the `let`s before it plus 64; a site
reads with the fuel of every `let` in scope plus 64. Source nests expressions
less than 64 deep, so only a hand-built wire reaches the difference. A
definition nested deeper than its record reads counts as `reverseLeaves + 1`
steps, so no site reads it through. Before, the record counted the unread part
as one step; a site with more fuel then read deeper, overflowed the budget and
undid the reading, and nested undone readings multiplied the work by about 8
per level. -/

/-- A balanced `compose` tree of `2^depth` copies of `leaf`. -/
private def tree : Nat → Term → Term
  | 0, leaf => leaf
  | depth + 1, leaf => compose (tree depth leaf) (tree depth leaf) "Line" "Line"

/-- `inner` nested `depth` levels deep along the first operand of `compose`,
the operand `resolve` reads first: `compose(… compose(inner, m) …, m)`. -/
private def comb (name : String) (depth : Nat) (inner : Term) : Term :=
  Nat.repeat (fun term => compose term (constant name "Line" "Line") "Line" "Line") depth inner

/-- `L₀ := comb(68, base)` and `Lᵢ := comb(i + 68, compose(tree(3, Lᵢ₋₁), tree(8, m)))`
for `i ≤ levels`, each nested four levels deeper than its record reads; then
`pad` integer `let`s, which give the site more fuel than any record had, and a
pullback along `L_levels` at 3. -/
private def deep (name : String) (base : Term) (levels pad : Nat) : Function :=
  let line := smoothType "Line" "Line"
  let value (i : Nat) : Term := match i with
    | 0 => comb name 68 base
    | i + 1 => comb name (i + 69)
      (compose (tree 3 (var i line)) (tree 8 (constant name "Line" "Line")) "Line" "Line")
  let maps (body : Term) : Term := (List.range (levels + 1)).foldr (fun i rest => .letE i (value i) rest) body
  let padding (body : Term) : Term :=
    (List.range pad).foldr (fun j rest => .letE (levels + 1 + j) (.integer 0) rest) body
  { id := 0, definition := id "main", parameters := [], returnType := .pure .int
    body := maps <| padding <|
      guarded (same (prim "pullback" [var levels line, three, dline (lineAt 3) 1] (cotangentType "Line"))
        (dline three 1)) 1 (.integer 42) }

#eval check "a definition nested deeper than its record reads stays one opaque step at a site with more fuel"
  (let module : Module := { source with functions := [deep "idL" (constant "idL" "Line" "Line") 0 20] }
   let (compiled, ledger) := Reverse.generate module
   ledger.length == 1 && (ledger.headD default).site.steps.map (·.kind) == [.opaque] &&
     (Typing.checkModule compiled true).isOk && run module mainCall == some (.integer 42) &&
     run compiled mainCall == some (.integer 42))
#eval check "six nested definitions that measure does not read in full compile without undone readings"
  (let module : Module := { source with functions := [deep "sq" (tree 8 (constant "sq" "Line" "Line")) 6 500] }
   let (compiled, ledger) := Reverse.generate module
   ledger.length == 1 && (ledger.headD default).site.steps.map (·.kind) == [.opaque] &&
     (Typing.checkModule compiled true).isOk)

end VastitasKernel.Indexed.Core.ReverseCoreRegression
