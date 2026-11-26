import VastitasKernel.ExactOperatorMethods
import VastitasKernel.ResourceSource
import VastitasKernel.Protocol
import Lean.Data.Json

/-! Revision evidence for protocol 10. Source owners are nominal and stable;
the dense method, definition and Core indices are local to the exact checked
input. The witness stores the input once for the whole compilation. It is
never a source of method selection or a cache key accepted by hash alone. -/
namespace VastitasKernel.ResourceSource.FunctionRevision
open Lean Indexed FunctionSource

def ownerJson (owner : Namespace.Owner) : Json :=
  Json.mkObj [("package", Json.mkObj [("source", owner.scope.package.source),
    ("name", owner.scope.package.name), ("version", owner.scope.package.version)]),
    ("module", toJson owner.scope.path), ("name", owner.name)]

def functionIdJson (id : Namespace.FunctionId) : Json := ownerJson id.owner

private def binderJson : IndexParam → Json
  | .category schema => Json.mkObj [("schema", ownerJson schema)]
  | .monad schema => Json.mkObj [("monad_schema", ownerJson schema)]
  | .object slot => Json.mkObj [("category_slot", slot)]
  | .monadObject slot => Json.mkObj [("monad_slot", slot)]

private def indexJson : StaticIndex → Json
  | .category owner => Json.mkObj [("category", ownerJson owner)]
  | .monad owner => Json.mkObj [("monad", ownerJson owner)]
  | .object owner tag => Json.mkObj [("category", ownerJson owner), ("object", tag)]

private def methodOrigin : AuthoritySource.MethodOrigin → Json
  | .ordinary i => Json.mkObj [("ordinary", i)]
  | .contribution owner i => Json.mkObj [("contribution", ownerJson owner), ("index", i)]

private def families {p : DispatchSource.Program} {main} (checked : AuthoritySource.CheckedProgram p main) : Json :=
  .arr <| (p.source.headers.indexed.declarations.filterMap fun target =>
    let id := functionIdJson ⟨target.owner⟩
    match target.kind with
    | .function => some <| match checked.compiler.input.templates[target.owner]? with
      | some (_,template) => Json.mkObj [("id", id), ("finite_binders", toJson (template.binders.map binderJson))]
      | none => Json.mkObj [("id", id), ("definition", toJson (checked.compiler.input.named[target.owner]?))]
    | .generic => some <| Json.mkObj [("id", id), ("dispatch", toJson <|
        checked.dispatcher.families[target.owner]?.map fun family => Id.run do
          let domain := Std.HashSet.ofList family.domain
          return family.checked.rows.filterMap fun row => do
            guard (domain.contains row.key)
            let selected := row.winner.bind fun winner => do
              let entry ← checked.authority.headers.methods[winner]?
              let definition ← checked.dispatcher.definitions[(winner, row.key)]?
              return Json.mkObj [("ordinal", winner), ("origin", methodOrigin entry.origin),
                ("definition", definition)]
            return Json.mkObj [("key", toJson row.key), ("selected", toJson selected)])]
    | _ => none).toArray

private def targetJson : Compiler.TargetName → Json
  | .concrete i => Json.mkObj [("definition", i)]
  | .probe i => Json.mkObj [("probe", i)]

private def keyJson (k : Compiler.Key) : Json :=
  Json.mkObj [("definition", toJson k.definition), ("targets", toJson (k.targets.map targetJson))]

mutual
  private def signatureJson : Signature → Json
    | .data (.finite (.hom owner x y)) =>
      Json.mkObj [("category", ownerJson owner), ("source", x), ("target", y)]
    | .data (.pure .nat) => "Nat" | .data (.pure .int) => "Int"
    | .data (.pure .bool) => "Bool" | .data (.pure .unit) => "Unit"
    | .data _ => .null -- excluded by validTargetName
    | .function params result => Json.mkObj [("params", toJson (signatureList params)),
        ("result", signatureJson result)]
  private def signatureList : Surface.TypeList Core.DataType → List Json
    | .nil => []
    | .cons x xs => signatureJson x :: signatureList xs
end

private def staticUseJson (u : Compiler.StaticUse) : Json :=
  let fields := [("caller", toJson (u.caller.map keyJson)), ("target", targetJson u.target.name),
    ("selection", toJson <| u.target.selected.map fun sel =>
      Json.mkObj [("id", functionIdJson ⟨sel.target.owner⟩), ("key", toJson sel.key),
        ("method", sel.method), ("definition", sel.definition)])]
  let scalarOnly := u.expected.allData fun ty => match ty with | .pure _ => true | _ => false
  Json.mkObj (if scalarOnly then fields else ("signature", signatureJson u.expected) :: fields)

/-- The immutable family-local method ordinal and its Core result type. -/
def operatorMethod (selection : Nat × Core.DataType) : Json :=
  Json.mkObj [("ordinal", toJson selection.1), ("result", signatureJson (.data selection.2))]

/-- Complete method selected at this exact operator site of the accepted Core. -/
def operatorSite {m : Core.Module} (typed : Core.Typing.ModuleTyped m)
    (site : Nat × ExactOperators.Selection) (member : site ∈ ExactOperators.selections m) : Json :=
  Json.mkObj [("core", site.1), ("id", functionIdJson site.2.family), ("key", toJson site.2.scalarKey),
    ("method", operatorMethod (ExactOperators.methodAt typed site member))]

def operatorSites {m : Core.Module} (typed : Core.Typing.ModuleTyped m) : List Json :=
  (ExactOperators.selections m).attach.map fun ⟨site, member⟩ => operatorSite typed site member

private def pass {prepared : Compiler.PreparedProgram} {main} (checked : Compiler.CheckedPass prepared false main) : Json :=
  let lowered := checked.lowered
  let forwarded := lowered.forwardUses.map fun f => Json.mkObj [
    ("caller", keyJson f.caller), ("family", functionIdJson ⟨f.family⟩),
    ("finite_indices", toJson (f.indices.map indexJson)), ("definition", toJson f.definition),
    ("method", spanJson f.method), ("site", spanJson f.site),
    ("targets", toJson <| f.targets.map fun arg => arg.map fun t =>
      Json.mkObj [("target", targetJson t.name), ("signature", signatureJson t.signature)])]
  let refs := lowered.familyRefs.map fun ref => Json.mkObj [
    ("caller", keyJson ref.caller), ("id", functionIdJson ⟨ref.target.owner⟩),
    ("path", toJson ref.path.path), ("span", spanJson ref.path.span)]
  Json.mkObj <| (if forwarded.isEmpty then [] else [("finite_forwards", toJson forwarded)]) ++
    (if refs.isEmpty then [] else [("family_refs", toJson refs)]) ++
    [("symbols", toJson <| lowered.module.functions.map fun f =>
    Json.mkObj [("core", f.id), ("id", functionIdJson ⟨f.definition⟩),
      ("specialization", toJson <| lowered.origins[f.id]?.map fun k =>
        let indices := (prepared.input.prepared[k.definition]?.map (·.finiteKey)).getD []
        let fields := [("definition", toJson k.definition), ("targets", toJson (k.targets.map targetJson))]
        Json.mkObj (if indices.isEmpty then fields else ("finite_indices", toJson (indices.map indexJson)) :: fields))]),
    ("operator_sites", toJson (operatorSites checked.core.typed)),
    ("calls", toJson <| lowered.emittedCalls.map fun c =>
      Json.mkObj [("caller", c.caller.definition), ("caller_targets", toJson (c.caller.targets.map targetJson)),
        ("definition", c.key.definition), ("targets", toJson (c.key.targets.map targetJson)), ("core", c.id)]),
    ("static_uses", toJson (lowered.staticUses.map staticUseJson)),
    ("dispatch_calls", toJson <| lowered.dispatchCalls.map fun c =>
      Json.mkObj [("caller", c.caller.definition), ("caller_targets", toJson (c.caller.targets.map targetJson)),
        ("id", functionIdJson ⟨c.target.owner⟩), ("key", toJson c.key),
        ("method", c.method), ("definition", c.definition), ("core", c.emittedId)])]

private def representationName : Storage.Realization.Representation → String
  | .real32 => "F32<RR>" | .real64 => "F64<RR>"
  | .complex32 => "F32<CC>" | .complex64 => "F64<CC>"

private def planFields (plan : Storage.Realization.Plan) : List (String × Json) :=
  [("graph", ownerJson plan.graph), ("policy", match plan.policy with | .nativeFast => "NativeFast"),
   ("flags", match plan.flags with | .unavailable => "Unavailable")]

private def realizationSite (site : RealizationSite) : Json :=
  let op := site.operation
  let d := op.descriptor
  let fields := [("owner", ownerJson site.owner), ("path", toJson site.position),
    ("span", spanJson site.span), ("id", functionIdJson site.functionId),
    ("subject", ownerJson d.subject), ("chart", ownerJson d.chart),
    ("representation", toJson (representationName d.representation))] ++
    (site.affine.toList.map fun _ => ("constructor", functionIdJson ⟨Namespace.affineConstructor⟩))
  Json.mkObj <| fields ++ match op with
    | .realize _ => []
    | .interpret plan => planFields plan
    | .point _ loan => [("loan", toJson loan)]
    | .run plan input output => [("input", toJson input), ("output", toJson output)] ++ planFields plan

private def locationSite (site : Storage.Functions.NumericalSourceSite) : Json :=
  Json.mkObj [("function", toJson site.function), ("path", toJson site.path)]

private def loanState (s : Storage.State) (name : Storage.Symbol) : Option Json := do
  let loan ← s.loan? name
  let a ← s.allocation? loan.allocation
  let l := loan.layout
  return Json.mkObj [("allocation", toJson a.identity), ("version", toJson a.version),
    ("offset", toJson l.offset), ("rows", toJson l.rows), ("columns", toJson l.columns),
    ("leading", toJson l.leading), ("transposed", toJson l.transposed)]

private def runReceipt (r : Storage.Functions.RealizationRunReceipt) : Json :=
  Json.mkObj <| [("source", locationSite r.location.source),
    ("callers", toJson (r.location.callers.map locationSite)),
    ("block", toJson r.location.block), ("start", toJson r.location.start),
    ("source_loan", toJson r.input), ("destination_loan", toJson r.output),
    ("input", toJson (loanState r.before r.input)), ("before", toJson (loanState r.before r.output)),
    ("after", toJson (loanState r.after r.output))] ++ planFields r.plan

private def realizationRevision {p : Program} {main} (checked : Checked p main) : Json := Id.run do
  let sites := checked.lowered.realizationSites
  -- Descriptors with one subject share the coordinate list stored here. Source
  -- sites retain the nominal subject and chart even when their dimensions agree.
  let mut seen : Std.HashSet DeclId := {}
  let mut charts : Array Json := #[]
  for site in sites do
    let d := site.operation.descriptor
    unless seen.contains d.subject do
      if let some profile := d.profile (numericalEnvironment checked.pureProgram) then
        let subject := [("subject", ownerJson d.subject), ("chart", Json.str "standard_chart"),
          ("coordinates", toJson profile.coordinates)]
        let base := match profile.base with
          | .smooth implementation marker => [("implementation", ownerJson implementation), ("marker", ownerJson marker)]
          | .exactComplex model carrier realModel realCarrier =>
            [("model", ownerJson model), ("carrier", ownerJson carrier),
             ("real_model", ownerJson realModel), ("real_carrier", ownerJson realCarrier)]
        charts := charts.push (Json.mkObj (subject ++ base))
      seen := seen.insert d.subject
  let runs := match h : p.entry with
    | none => #[]
    | some i => (checked.execution i h).checked.context.realizationRuns.map runReceipt
  return Json.mkObj [("charts", .arr charts), ("sites", toJson (sites.map realizationSite)), ("runs", .arr runs)]

/-- The receipt has one exact revision context for singletons, overloaded
families, contributions and higher-order specializations. Keep the two Core
namespaces distinct when resource fragments require a second executable pass. -/
def artifact (input : Json) {p : Program} {main} (checked : Checked p main) : Json :=
  let fields := [("schema", toJson 1), ("input", input), ("families", families checked.pureProgram),
    ("pure", pass checked.pureProgram.executable),
    ("resource_values", if p.pureFragments.isEmpty then Json.null else pass checked.values.executable)]
  Json.mkObj <| if checked.lowered.realizationSites.isEmpty then fields else
    ("resource_realizations", realizationRevision checked) :: fields

private theorem pass_operators {prepared main} (checked : Compiler.CheckedPass prepared false main) :
    (pass checked).getObjVal? "operator_sites" = .ok (toJson (operatorSites checked.core.typed)) := by
  simp only [pass]
  split <;> split <;> rfl

theorem artifact_operators (input : Json) {p : Program} {main} (checked : Checked p main) :
    ((artifact input checked).getObjVal? "pure").bind (·.getObjVal? "operator_sites") =
      .ok (toJson (operatorSites checked.pureProgram.executable.core.typed)) := by
  simp only [artifact]
  split <;> exact pass_operators checked.pureProgram.executable

/-- Keep revision printing/replay below the driver response limit, even when
many Core symbols refer to the same long package name. Count before rendering
the complete string. This operational bound does not admit a program. -/
def maxBytes : Nat := 64 * 1024 * 1024

private def spend (n cost : Nat) : Option Nat :=
  if cost ≤ n then some (n - cost) else none

private def stringCost (budget : Nat) (s : String) : Option Nat := do
  -- The UTF-8 spelling alone is a lower bound, so a huge repeated string need
  -- not even be escaped once if it cannot fit the remaining budget.
  guard (s.utf8ByteSize + 2 ≤ budget)
  let extra := s.foldl (fun n c =>
    n + if c == '"' || c == '\\' || c == '\n' || c == '\r' then 1
        else if c.toNat < 32 then 5 else 0) 0
  spend budget (s.utf8ByteSize + extra + 2)

/-- Each queued JSON value costs at least one compact byte, independently of
its children. Thus a receipt within the byte budget cannot need more than
`maxBytes` worklist steps. Explicit fuel makes this traversal total even for
malformed input, without recursive descent on the depth of the witness. -/
private def remaining : Nat → Nat → List Json → Option Nat
  | _, budget, [] => some budget
  | 0, _, _ :: _ => none
  | fuel + 1, budget, j :: rest => do
    match j with
    | .null => remaining fuel (← spend budget 4) rest
    | .bool b => remaining fuel (← spend budget (if b then 4 else 5)) rest
    | .num n => remaining fuel (← spend budget n.toString.utf8ByteSize) rest
    | .str s => remaining fuel (← stringCost budget s) rest
    | .arr xs =>
      remaining fuel (← spend budget (2 + (xs.size - 1))) (xs.foldr List.cons rest)
    | .obj xs =>
      let initial ← spend budget (2 + (xs.size - 1) + xs.size)
      let left ← xs.foldlM (fun n k _ => stringCost n k) initial
      remaining fuel left (xs.foldr (fun _ v stack => v :: stack) rest)

def bounded (j : Json) : Bool := (remaining maxBytes maxBytes [j]).isSome

/-- The original wire has its own byte limit. Bound the fields derived by the
checker separately when the full revision stays in the live compilation. -/
def derivedFields? : Json → Option Json
  | .obj fields => if fields.contains "input" then some (.obj (fields.erase "input")) else none
  | _ => none

def boundedDerived (revision : Json) : Bool := (derivedFields? revision).any bounded

end VastitasKernel.ResourceSource.FunctionRevision
