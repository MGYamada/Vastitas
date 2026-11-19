import VastitasKernel.IndexedCallCoverage

/-! Validate the exact let/call structure of finite callable forwarding in
the returned Core. Only callers with a forwarding site need a subterm index. -/
namespace VastitasKernel.Indexed.FunctionSource.Compiler.Forwarding
open Core

def bindings (wanted : Std.HashSet Nat) : Core.Term → List (Nat × Core.Term)
  | t@(.letE s v b) =>
    (if wanted.contains s then [(s,t)] else []) ++ bindings wanted v ++ bindings wanted b
  | .unpack _ _ v b | .binary _ v b _ | .pair _ v b => bindings wanted v ++ bindings wanted b
  | .branch c y n _ => bindings wanted c ++ bindings wanted y ++ bindings wanted n
  | .pack _ w fs => bindings wanted w ++ fs.flatMap (bindings wanted)
  | .call _ args _ _ | .primitive _ args _ => args.flatMap (bindings wanted)
  | .scope a | .unary _ a _ | .ascribe _ a | .natToInt a | .project _ _ a => bindings wanted a
  | .variable .. | .finiteLookup .. | .finiteTag .. | .natural .. | .integer .. | .boolean .. | .unit => []

def fragments (pass : Pass) : Std.HashMap (Key × Nat) Core.Term := Id.run do
  let mut wanted : Std.HashMap Key (Std.HashSet Nat) := {}
  for site in pass.forwardUses do
    wanted := wanted.alter site.caller fun prev => some ((prev.getD {}).insert site.firstBinding)
  let mut found := {}
  for f in pass.module.functions do
    if let some key := pass.origins[f.id]? then
      if let some slots := wanted[key]? then
        for (s,term) in bindings slots f.body do
          found := found.insert (key,s) term
  return found

/-- Read exactly n consecutive outer bindings without looking through a branch,
a scope or another operation. -/
def peel : Nat → Core.Term → Option (List (Nat × Core.Term) × Core.Term)
  | 0, term => some ([],term)
  | n+1, .letE s value rest => do
    let (bindings,tail) ← peel n rest
    return ((s,value) :: bindings,tail)
  | _+1, _ => none

def argumentMatches (origins : Array Key) (audit : Bool) (source : Nat)
    (target : Option Target) (value : Core.Term) : Bool :=
  match target, value with
  | none, .variable s _ => source == s
  | some ⟨.probe _,_,_⟩, .variable .. => audit
  | some ⟨.concrete id,_,_⟩, .call callee [] [] _ => origins[callee]? == some ⟨id,[]⟩
  | _, _ => false

def variableSymbol : Core.Term → Option Nat
  | .variable s _ => some s
  | _ => none

def matchesBody (origins : Array Key) (audit : Bool) (site : ForwardUse) (body : Core.Term) : Bool := Id.run do
  let some (inputs,inner) := peel site.targets.length body | return false
  let some (args,.call callee passed [] _) := peel site.targets.length inner | return false
  return origins[callee]? == some ⟨site.definition,[]⟩ &&
    passed.mapM variableSymbol == some (args.map Prod.fst) &&
    ((inputs.zip site.targets).zip args).all fun ((p,t),a) => argumentMatches origins audit p.1 t a.2

end VastitasKernel.Indexed.FunctionSource.Compiler.Forwarding
