import VastitasKernel.NamespaceChecker

/-! A per-pass resolver for a fixed reconstructed namespace. A repeated
successful (scope, path) can reuse its target. Logical member visits are
charged on hits as well so independent reference audits remain bounded. -/
namespace VastitasKernel.Namespace

attribute [local instance] lexOrd

private theorem memberAt_span (fuel budget : Nat) (p : Indexed) (requester scope : Scope)
    (name : String) (active : Std.TreeSet ImportKey) (a b : Span) :
    ((memberAt fuel p requester scope name active a).run budget).toOption =
      ((memberAt fuel p requester scope name active b).run budget).toOption := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases budget with
    | zero => rfl
    | succ budget =>
      cases decl : p.byOwner[Owner.mk scope name]? with
      | some target =>
        cases access : visible requester target <;>
          simp [memberAt, charge, decl, access, StateT.run, StateT.bind, StateT.pure, bind, pure, Except.bind, Except.pure, problem] <;> rfl
      | none =>
        cases modl : moduleLookupAt p scope with
        | none => simp [memberAt, charge, decl, modl, StateT.run, StateT.bind, bind, Except.bind, problem] <;> rfl
        | some m =>
          cases alias : m.imports[name]? with
          | none => simp [memberAt, charge, decl, modl, alias, StateT.run, StateT.bind, bind, Except.bind, problem] <;> rfl
          | some entry =>
            cases access : visible requester ⟨⟨scope, name⟩, .module, entry.isPublic⟩ <;>
              cases cycle : active.contains (importKey (scope, name)) <;>
              simp [memberAt, charge, decl, modl, alias, access, cycle, StateT.run, StateT.bind, bind, Except.bind, problem] <;> rfl

private theorem singleton_member (fuel budget : Nat) (p : Indexed) (scope : Scope) (name : String)
    (span : Span) (pkg : PackageLookup) (found : p.byPackage[scope.package.source]? = some pkg)
    (ordinary : name ≠ "self" ∧ name ≠ "super" ∧ name ≠ "package")
    (notDependency : pkg.dependencies[name]? = none) :
    (resolveAt (fuel + 2) p scope [name] {} span).run budget =
      (memberAt (fuel + 1) p scope scope name {} span).run budget := by
  obtain ⟨selfName, superName, packageName⟩ := ordinary
  cases visited : (memberAt (fuel + 1) p scope scope name {} span).run budget with
  | error diagnostic =>
    simp [resolveAt, found, notDependency, StateT.run, StateT.bind, bind, Except.bind] at visited ⊢
    rw [visited]
  | ok result =>
    rcases result with ⟨target, remaining⟩
    simp [resolveAt, found, notDependency, StateT.run, StateT.bind, bind, Except.bind] at visited ⊢
    rw [visited]
    rfl

private def localAlias (p : Indexed) (scope : Scope) (name : String) : Bool :=
  match p.byPackage[scope.package.source]? with
  | none => false
  | some pkg => decide (name ≠ "self" ∧ name ≠ "super" ∧ name ≠ "package") &&
      pkg.dependencies[name]?.isNone && (moduleLookupAt p scope).any (fun m => m.imports.contains name)

/-- A local import is resolved at its declaration's fixed namespace. Its
successful target and remaining member budget are independent of diagnostic spans. -/
structure AliasHit (p : Indexed) where
  scope : Scope
  name : String
  span : Span
  target : Target
  remaining : Nat
  eligible : localAlias p scope name = true
  checked : (memberAt (Limits.namespaceResolution - 1) p scope scope name {} span).run
    Limits.namespaceResolution = .ok (target, remaining)

theorem AliasHit.atSpan {p : Indexed} (hit : AliasHit p) (span : Span) :
    ((memberAt (Limits.namespaceResolution - 1) p hit.scope hit.scope hit.name {} span).run
      Limits.namespaceResolution).toOption = some (hit.target, hit.remaining) := by
  rw [memberAt_span _ _ _ _ _ _ _ span hit.span, hit.checked]
  rfl

/-- A reusable hit denotes the same target as the public resolver at the
caller's actual diagnostic span. Both its fixed namespace and scope are retained. -/
theorem AliasHit.resolves {p : Indexed} (hit : AliasHit p) (span : Span) :
    resolve p hit.scope [hit.name] span = .ok hit.target := by
  have eligible := hit.eligible
  cases found : p.byPackage[hit.scope.package.source]? with
  | none => simp [localAlias, found] at eligible
  | some pkg =>
    simp only [localAlias, found, Bool.and_eq_true, decide_eq_true_eq,
      Option.isNone_iff_eq_none] at eligible
    have original := hit.atSpan span
    unfold resolve
    rw [show Limits.namespaceResolution = (Limits.namespaceResolution - 2) + 2 from rfl,
      singleton_member (Limits.namespaceResolution - 2) _ _ _ _ _ _ found eligible.1.1 eligible.1.2]
    cases actual : (memberAt (Limits.namespaceResolution - 1) p hit.scope hit.scope hit.name {} span).run
        Limits.namespaceResolution with
    | error diagnostic =>
      rw [actual] at original
      contradiction
    | ok pair =>
      rw [actual] at original
      change some pair = some (hit.target, hit.remaining) at original
      cases Option.some.inj original
      change ((memberAt (Limits.namespaceResolution - 1) p hit.scope hit.scope hit.name {} span).run
        Limits.namespaceResolution).map (·.1) = .ok hit.target
      rw [actual]
      rfl

structure QuerySession where
  index : Indexed
  aliases : Std.HashMap (Scope × String) (AliasHit index) := {}
  units : Fin (Limits.namespaceProgramWork + 1) := 0
  hits : Nat := 0

def QuerySession.debit (s : QuerySession) (amount : Nat) (span : Span) : Result QuerySession :=
  if bound : s.units.val + amount ≤ Limits.namespaceProgramWork then
    .ok {s with units := ⟨s.units.val + amount, Nat.lt_succ_of_le bound⟩}
  else problem span "E_LIMIT" s!"program-wide namespace resolution exceeds {Limits.namespaceProgramWork} logical visits"

/-- Only successful unqualified aliases are memoized. Relative/qualified
paths retain the complete resolver, including visibility, fuel and cycle checks. -/
def QuerySession.query (s : QuerySession) (scope : Scope) (path : List String) (span : Span) :
    Result (Target × QuerySession) := do
  let limit := Limits.namespaceResolution
  if let [name] := path then
    if permitted : localAlias s.index scope name then
      if let some hit := s.aliases[(scope, name)]? then
        if hit.scope == scope && hit.name == name then
          let paid ← s.debit (2 + (limit - hit.remaining)) span
          return (hit.target, {paid with hits := paid.hits + 1})
      match checked : (memberAt (limit - 1) s.index scope scope name {} span).run limit with
      | .error diagnostic => .error diagnostic
      | .ok (target, remaining) =>
        let hit : AliasHit s.index := ⟨scope, name, span, target, remaining, permitted, checked⟩
        let table := s.aliases.insert (scope, name) hit
        let saved := {s with aliases := table}
        return (target, ← saved.debit (2 + (limit - remaining)) span)
  let (target, remaining) ← (resolveAt limit s.index scope path {} span).run limit
  return (target, ← s.debit (1 + path.length + (limit - remaining)) span)

/-- Look through same-module `self::name` aliases once per module. This table
prices spellings only. The actual namespace validation independently resolves
every import, including visibility, cycles, fuel and target identity. -/
private def spellingPrice (p : Indexed) (scope : Scope) (m : ModuleLookup) :
    Nat → String → Std.HashSet String → StateT (Std.HashMap String Nat) Result Nat
  | 0, _, _ => pure Limits.namespaceResolution
  | fuel + 1, name, active => do
    if let some prior := (← get)[name]? then return prior
    if p.byOwner.contains ⟨scope, name⟩ then return 1
    let some entry := m.imports[name]? | return Limits.namespaceResolution
    let price ← match entry.path with
      | ["self", next] =>
        if !active.contains name then
          let rest ← spellingPrice p scope m fuel next (active.insert name)
          pure (min Limits.namespaceResolution (1 + rest))
        else
          match (memberAt Limits.namespaceResolution p scope scope name {} entry.span).run Limits.namespaceResolution with
          | .error diagnostic => throw diagnostic
          | .ok (_, remaining) => pure (Limits.namespaceResolution - remaining)
      | _ =>
        match (memberAt Limits.namespaceResolution p scope scope name {} entry.span).run Limits.namespaceResolution with
        | .error diagnostic => throw diagnostic
        | .ok (_, remaining) => pure (Limits.namespaceResolution - remaining)
    modify (·.insert name price)
    return price

def inputPrices (p : Indexed) : Result (ImportWork × Std.HashMap String Nat) := do
  let mut work : ImportWork := ⟨0, Nat.zero_le _⟩
  let mut prices : Std.HashMap String Nat := {}
  for pkg in p.packages do
    for m in pkg.modules do
      if m.imports.isEmpty then continue
      let scope : Scope := ⟨pkg.id, m.path⟩
      let some table := moduleLookupAt p scope | problem m.span "E_NAME" "unknown module"
      let mut memo : Std.HashMap String Nat := {}
      for entry in m.imports do
        let (consumed, fresh) ← (spellingPrice p scope table Limits.namespaceResolution entry.alias {}).run memo
        memo := fresh
        work ← work.add consumed entry.span
        prices := prices.insert entry.alias (max (prices.getD entry.alias 0) consumed)
  return (work, prices)

def queryLimit {α : Type} (span : Span := {}) : Result α :=
  problem span "E_LIMIT" s!"program-wide namespace resolution exceeds {Limits.namespaceProgramWork} logical visits"

private def wordPrice (prices : Std.HashMap String Nat) (text : String) : Nat :=
  if text.contains ':' then (text.splitOn "::").foldl (fun n part => n + 1 + prices.getD part 0) 0
  else 1 + prices.getD text 0

/-- The explicit worklist visits the source once. Import declarations are charged separately
by the spelling table and independently audited by the resolver. Diagnostic location objects do not represent references. -/
private def priceNodes (prices : Std.HashMap String Nat) :
    Nat → List Lean.Json → Nat → Result (Fin (Limits.namespaceProgramWork + 1))
  | _, [], used =>
    if bound : used ≤ Limits.namespaceProgramWork then .ok ⟨used, Nat.lt_succ_of_le bound⟩ else queryLimit
  | 0, _ :: _, _ => queryLimit
  | fuel + 1, item :: rest, used => do
    let amount := match item with | .str text => wordPrice prices text | _ => 1
    let next := used + amount
    if next > Limits.namespaceProgramWork then queryLimit
    else
      let work := match item with
        | .arr xs => xs.foldr List.cons rest
        | .obj fields => fields.toList.foldr (fun (key, value) stack =>
            if key == "span" || key == "imports" then stack else value :: stack) rest
        | _ => rest
      priceNodes prices fuel work next

def priceInput (p : Indexed) (json : Lean.Json) : Result (Fin (Limits.namespaceProgramWork + 1)) := do
  let (imports, prices) ← inputPrices p
  priceNodes prices Limits.namespaceProgramWork [json] imports.units

structure RequestReceipt (p : Indexed) (json : Lean.Json) (passUnits : Nat) where
  inputUnits : Fin (Limits.namespaceProgramWork + 1)
  priced : priceInput p json = .ok inputUnits
  bounded : inputUnits.val + passUnits ≤ Limits.namespaceProgramWork

structure Admitted (p : Indexed) (json : Lean.Json) (evaluate : Unit → Result α) (cost : α → Nat) where
  value : α
  accepted : evaluate () = .ok value
  receipt : RequestReceipt p json (cost value)

def checkRequest (p : Indexed) (json : Lean.Json) (evaluate : Unit → Result α) (cost : α → Nat) :
    Result (Admitted p json evaluate cost) := do
  match priced : priceInput p json with
  | .error problem => .error problem
  | .ok inputUnits =>
    match accepted : evaluate () with
    | .error problem => .error problem
    | .ok value =>
      if bound : inputUnits.val + cost value ≤ Limits.namespaceProgramWork then
        return ⟨value, accepted, ⟨inputUnits, priced, bound⟩⟩
      else queryLimit

end VastitasKernel.Namespace
