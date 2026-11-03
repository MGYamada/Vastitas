import VastitasKernel.IndexedFunctionCompiler
import VastitasKernel.FiniteIndex

namespace VastitasKernel.Indexed.FunctionSource.Compiler

/-- The caller's exact specialization key and the target's emitted Core ID.
An absent caller origin remains an unmatched edge, never a default identity. -/
abbrev CallEdge := Option Key × Nat

def coreCallEdges (pass : Pass) : List CallEdge :=
  pass.module.functions.flatMap fun function =>
    function.body.callIds.map fun target => (pass.origins[function.id]?, target)

def emittedCallEdges (pass : Pass) : List CallEdge :=
  pass.emittedCalls.map fun call => (some call.caller, call.id)

def dispatchDefinitions (input : Input) : Std.HashSet Nat :=
  Std.HashSet.ofList (input.dispatch.definitions.toList.map Prod.snd)

def dispatchTarget (definitions : Std.HashSet Nat) (pass : Pass) (target : Nat) : Bool :=
  (pass.origins[target]?).any fun origin => definitions.contains origin.definition

def coreDispatchEdges (input : Input) (pass : Pass) : List CallEdge :=
  let definitions := dispatchDefinitions input
  (coreCallEdges pass).filter fun edge => dispatchTarget definitions pass edge.2

def dispatchCallEdges (pass : Pass) : List CallEdge :=
  pass.dispatchCalls.map fun call => (some call.caller, call.emittedId)

def emittedCallCoverage (pass : Pass) : Bool :=
  Finite.distinct pass.origins.toList &&
    Finite.sameCounts (coreCallEdges pass) (emittedCallEdges pass)

def dispatchCallCoverage (input : Input) (pass : Pass) : Bool :=
  Finite.sameCounts (coreDispatchEdges input pass) (dispatchCallEdges pass)

end VastitasKernel.Indexed.FunctionSource.Compiler
