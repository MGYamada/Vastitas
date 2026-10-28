import VastitasKernel.Abstract

/-! Bodyless contracts expand to concrete keys. They never enter the executable
method list or participate in specificity/return-type-directed selection. -/
namespace VastitasKernel.Contracts
open Checker.Internal

structure Contract (hierarchy : Dispatch.Hierarchy) where
  raw : RawAbstractMethod
  selector : Dispatch.NormalizedMethod
  domain : List Dispatch.Key
  valid : domain.all (Dispatch.applicable hierarchy · selector) = true

def expand (hierarchy : Dispatch.Hierarchy) (arity : Nat) (clauses : List (List Nat)) : List Dispatch.Key :=
  (Dispatch.keys hierarchy.concrete arity).filter fun key =>
    clauses.any (Dispatch.nominalBelow hierarchy key)

def prepare (nominals : Abstract.Checked) (arity : Nat) (raw : RawAbstractMethod) : CheckM (Contract nominals.hierarchy) := do
  if arity > Limits.dispatchArity then fail raw.span "E_LIMIT" s!"dispatch key space exceeds {Limits.dispatchKeys}"
  if raw.params.length != arity then fail raw.span "E_ARITY" "abstract method parameter count differs from its generic"
  let selectors ← raw.params.mapM fun param => Abstract.selector nominals param.ty param.span
  let requirements ← raw.requirements.mapM fun name =>
    match Dispatch.parseCapability name with
    | some capability => pure capability
    | none => fail raw.span "E_CAPABILITY" s!"unknown capability '{name}'"
  let selector : Dispatch.NormalizedMethod := {
    id := 0, selectors
    requirements := Dispatch.normalizeCapabilities requirements }
  let clauses ← raw.domain.mapM fun clause => do
    if clause.length != arity then fail raw.span "E_ARITY" "abstract domain tuple has the wrong arity"
    let ids ← clause.mapM (Abstract.lookup nominals.names)
    if (expand nominals.hierarchy arity [ids]).isEmpty then
      fail (clause.head?.map (·.span) |>.getD raw.span) "E_CONTRACT_EMPTY" "abstract domain clause expands to no concrete keys; use domain; for an explicit empty contract"
    pure ids
  let domain := expand nominals.hierarchy arity clauses
  if valid : domain.all (Dispatch.applicable nominals.hierarchy · selector) = true then
    return { raw, selector, domain, valid }
  else fail raw.span "E_CONTRACT_DOMAIN" "contract domain does not satisfy its parameter selectors and requirements"

/-- Canonical union, independent of declaration order and repeated clauses. -/
def effectiveDomain (hierarchy : Dispatch.Hierarchy) (arity : Nat) (base : List Dispatch.Key)
    (contracts : List (Contract hierarchy)) : List Dispatch.Key :=
  (Dispatch.keys hierarchy.concrete arity).filter fun key =>
    base.contains key || contracts.any (fun contract => contract.domain.contains key)

def selectedResult (methods : List RawMethod) (checked : Dispatch.Checked) (key : Dispatch.Key) : Option RawType :=
  (checked.winner key).bind fun id => (methods[id]?).map (·.returnType)

def satisfied (methods : List RawMethod) (checked : Dispatch.Checked) (contract : Contract hierarchy) : Bool :=
  contract.domain.all fun key => selectedResult methods checked key == some contract.raw.returnType

end VastitasKernel.Contracts
