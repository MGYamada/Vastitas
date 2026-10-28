import Std
import VastitasKernel.Limits

/-! Closed-world nominal/static-capability method selection. The public universe
is fixed; `checkWith` uses the same algorithm for finite synthetic hierarchies.
No runtime value, erased object identity, or declaration-order priority enters
selection. The oracle proves the executable checker's selection contract. -/
namespace VastitasKernel.Dispatch

abbrev Key := List Nat

inductive Capability where
  | hasEq | hasOrder
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

def parseCapability : String → Option Capability
  | "HasEq" => some .hasEq
  | "HasOrder" => some .hasOrder
  | _ => none

/-- Canonical conjunction closure: order entails equality. -/
def normalizeCapabilities (caps : List Capability) : List Capability :=
  if caps.contains .hasOrder then [.hasEq, .hasOrder]
  else if caps.contains .hasEq then [.hasEq] else []

structure Hierarchy where
  nominalCount : Nat
  concrete : List Nat
  subtype : Nat → Nat → Bool
  facts : Nat → List Capability

def parseScalar : String → Option Nat
  | "Nat" => some 0 | "Int" => some 1
  | "Bool" => some 2 | "Unit" => some 3
  | _ => none

def parseSelector (name : String) : Option Nat :=
  match name with
  | "Number" => some 4 | "Any" => some 5
  | _ => parseScalar name

def nominalName : Nat → String
  | 0 => "Nat" | 1 => "Int" | 2 => "Bool" | 3 => "Unit"
  | 4 => "Number" | 5 => "Any" | n => s!"nominal#{n}"

def publicHierarchy : Hierarchy where
  nominalCount := 6
  concrete := [0, 1, 2, 3]
  subtype a b := a == b || b == 5 || (a < 2 && b == 4)
  facts a := if a < 2 then [.hasEq, .hasOrder] else [.hasEq]

structure Method where
  id : Nat
  selectors : List Nat
  requirements : List String := []
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

structure NormalizedMethod where
  id : Nat
  selectors : List Nat
  requirements : List Capability
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

structure Error where
  code : String
  message : String
  key : Option Key := none
  methods : List Nat := []
  deriving Repr, Inhabited

structure Row where
  key : Key
  winner : Option Nat
  deriving Repr, DecidableEq, BEq, ReflBEq, LawfulBEq, Inhabited

structure Checked where
  keys : List Key
  methods : List NormalizedMethod
  rows : List Row
  applicablePairs : List (Nat × Key)
  deriving Repr, Inhabited

def Checked.winner (checked : Checked) (key : Key) : Option Nat :=
  (checked.rows.find? (fun row => row.key == key)).bind (·.winner)

def keys (concrete : List Nat) : Nat → List Key
  | 0 => [[]]
  | arity + 1 => concrete.flatMap fun ty => (keys concrete arity).map (ty :: ·)

/-- Capability evidence for a tuple is the intersection of argument facts.
The empty tuple has no facts, rather than every fact vacuously. -/
def tupleFacts (hierarchy : Hierarchy) : Key → List Capability
  | [] => []
  | head :: tail => [Capability.hasEq, .hasOrder].filter fun cap =>
      (hierarchy.facts head).contains cap &&
      tail.all (fun ty => (hierarchy.facts ty).contains cap)

def nominalBelow (hierarchy : Hierarchy) : List Nat → List Nat → Bool
  | [], [] => true
  | a :: rest, b :: more => hierarchy.subtype a b && nominalBelow hierarchy rest more
  | _, _ => false

def applicable (hierarchy : Hierarchy) (key : Key) (method : NormalizedMethod) : Bool :=
  nominalBelow hierarchy key method.selectors &&
    method.requirements.all (tupleFacts hierarchy key).contains

/-- Product order: nominal subtyping and implication of normalized requirements.
This deliberately does not compare sets of currently applicable keys. -/
def atLeastSpecific (hierarchy : Hierarchy) (a b : NormalizedMethod) : Bool :=
  nominalBelow hierarchy a.selectors b.selectors &&
    b.requirements.all a.requirements.contains

def moreSpecific (hierarchy : Hierarchy) (a b : NormalizedMethod) : Bool :=
  atLeastSpecific hierarchy a b && !atLeastSpecific hierarchy b a

def optimalCandidates (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) : List NormalizedMethod :=
  methods.filter fun method => applicable hierarchy key method &&
    !methods.any (fun other => applicable hierarchy key other &&
      moreSpecific hierarchy other method)

/-- Declarative candidate condition; it does not mention the executable checker. -/
def Optimal (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) (method : NormalizedMethod) : Prop :=
  method ∈ methods ∧ applicable hierarchy key method = true ∧
    ∀ other ∈ methods, applicable hierarchy key other = true →
      moreSpecific hierarchy other method = false

def Selection (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (key : Key) : Option Nat → Prop
  | none => ∀ method, ¬Optimal hierarchy methods key method
  | some id => ∃ method, method.id = id ∧ Optimal hierarchy methods key method ∧
      ∀ other, Optimal hierarchy methods key other → other = method

def RowsCorrect (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (rows : List Row) : Prop :=
  ∀ row ∈ rows, Selection hierarchy methods row.key row.winner

def hierarchyValid (hierarchy : Hierarchy) : Bool := Id.run do
  if hierarchy.nominalCount == 0 || hierarchy.nominalCount > Limits.nominalTypes then return false
  if hierarchy.concrete.isEmpty || !hierarchy.concrete.Nodup then return false
  if !hierarchy.concrete.all (· < hierarchy.nominalCount) then return false
  let names := List.range hierarchy.nominalCount
  return names.all fun a => hierarchy.subtype a a &&
    names.all (fun b =>
      (!(hierarchy.subtype a b && hierarchy.subtype b a) || a == b) &&
      names.all (fun c => !(hierarchy.subtype a b && hierarchy.subtype b c) ||
        hierarchy.subtype a c)) &&
    (!(hierarchy.facts a).contains .hasOrder || (hierarchy.facts a).contains .hasEq)

def normalizeMethod (hierarchy : Hierarchy) (arity : Nat) (method : Method) :
    Except Error NormalizedMethod := do
  if method.selectors.length != arity then
    throw { code := "E_DISPATCH_ARITY", message := "method selector arity differs from its generic", methods := [method.id] }
  if !method.selectors.all (· < hierarchy.nominalCount) then
    throw { code := "E_DISPATCH_SELECTOR", message := "unsupported nominal selector", methods := [method.id] }
  let requirements ← method.requirements.mapM fun name =>
    match parseCapability name with
    | some cap => pure cap
    | none => throw { code := "E_DISPATCH_CAPABILITY", message := s!"unsupported static capability '{name}'", methods := [method.id] }
  return { id := method.id, selectors := method.selectors, requirements := normalizeCapabilities requirements }

def sameSignature (a b : NormalizedMethod) : Bool :=
  a.selectors == b.selectors && a.requirements == b.requirements

def validateMethods (hierarchy : Hierarchy) (allKeys : List Key) :
    List NormalizedMethod → Except Error Unit
  | [] => pure ()
  | method :: rest => do
    if rest.any (fun other => other.id == method.id) then
      throw { code := "E_DISPATCH_DUPLICATE_ID", message := "duplicate method identity", methods := [method.id] }
    if let some other := rest.find? (sameSignature method) then
      throw { code := "E_DISPATCH_DUPLICATE", message := "duplicate normalized method signature", methods := [method.id, other.id] }
    if !allKeys.any (fun key => applicable hierarchy key method) then
      throw { code := "E_DISPATCH_UNREALIZABLE", message := "method conditions have no admitted concrete key", methods := [method.id] }
    validateMethods hierarchy allKeys rest

def selectRows (hierarchy : Hierarchy) (domain : List Key)
    (methods : List NormalizedMethod) : List Key → Except Error (List Row)
  | [] => pure []
  | key :: rest => do
    let winner ← match optimalCandidates hierarchy methods key with
      | [] =>
        if domain.contains key then
          throw { code := "E_DISPATCH_COVERAGE", message := "declared domain key has no applicable method", key := some key }
        else pure none
      | [method] => pure (some method.id)
      | methods => throw { code := "E_DISPATCH_AMBIGUOUS", message := "multiple incomparable optimal methods", key := some key, methods := methods.map (·.id) }
    let rows ← selectRows hierarchy domain methods rest
    return { key, winner } :: rows

def allApplicablePairs (hierarchy : Hierarchy) (methods : List NormalizedMethod)
    (allKeys : List Key) : List (Nat × Key) :=
  allKeys.flatMap fun key =>
    (methods.filter (applicable hierarchy key)).map (fun method => (method.id, key))

def checkWith (hierarchy : Hierarchy) (arity : Nat) (domain : List Key)
    (methods : List Method) : Except Error Checked := do
  if !hierarchyValid hierarchy then
    throw { code := "E_DISPATCH_HIERARCHY", message := "nominal hierarchy or static facts are invalid" }
  if arity > Limits.dispatchKeys || hierarchy.concrete.length ^ arity > Limits.dispatchKeys then
    throw { code := "E_DISPATCH_LIMIT", message := s!"dispatch key space exceeds {Limits.dispatchKeys}" }
  let allKeys := keys hierarchy.concrete arity
  if !domain.all allKeys.contains then
    throw { code := "E_DISPATCH_DOMAIN", message := "domain contains a nonconcrete key or wrong arity" }
  let normalized ← methods.mapM (normalizeMethod hierarchy arity)
  validateMethods hierarchy allKeys normalized
  let rows ← selectRows hierarchy domain normalized allKeys
  return { keys := allKeys, methods := normalized, rows, applicablePairs := allApplicablePairs hierarchy normalized allKeys }

def check (arity : Nat) (domain : List Key) (methods : List Method) : Except Error Checked :=
  if arity > Limits.dispatchArity then
    .error { code := "E_DISPATCH_LIMIT", message := s!"dispatch key space exceeds {Limits.dispatchKeys}" }
  else checkWith publicHierarchy arity domain methods

end VastitasKernel.Dispatch
