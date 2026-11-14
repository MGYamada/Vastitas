import VastitasKernel.StorageFunctionNumerical
import VastitasKernel.StorageFunctionCalls

/-! Expansion of a resource-function body, including each actual call, which
is rechecked against the resources of its caller. -/
namespace VastitasKernel.Storage.Functions

open Internal

mutual
  def expandAt : Nat → List Function → List Nat → List Nat → Nat → Frame → List Statement → M Frame
    | _, _, _, _, _, frame, [] => pure frame
    | 0, _, stack, path, position, frame, first :: _ =>
      atStatement stack path position frame first
        (throw {code := "E_RESOURCE_LIMIT", message := "resource expansion exceeds the depth bound"})
    | fuel + 1, functions, stack, path, position, frame, first :: rest => do
      let after ← atStatement stack path position frame first do
        spend
        match first with
        | .value name fragment arguments type => do
          let arguments ← (arguments.mapM (resolve frame) : Except Error (List Symbol))
          let (frame, global) ← bindName frame name
          scalarCall global fragment arguments type
          pure frame
        | .action action => operation frame action
        | .runtime operation => runtimeOperation frame operation
        | .runtimeNumerical operation => runtimeNumericalOperation frame operation
        | .numerical op => do
          priceFrame
          numericalOperation ⟨stack.head?, path ++ [position]⟩ frame op
        | .network graph output policy => do
          priceFrame
          networkOperation ⟨stack.head?, path ++ [position]⟩ frame graph output policy
        | .tree graph output policy plan => do
          priceFrame
          treeOperation ⟨stack.head?, path ++ [position]⟩ frame graph output policy plan
        | .tensor op => do
          priceFrame
          tensorOperation ⟨stack.head?, path ++ [position]⟩ frame op
        | .call callee actuals outputs | .callValue callee actuals outputs .. => do
          let actuals ← (actuals.mapM (resolve frame) : Except Error (List Symbol))
          let demand := match first with | .callValue .. => true | _ => false
          let callers := (← get).sourceCallers
          modify fun c => {c with sourceCallers := ⟨stack.head?, path ++ [position]⟩ :: callers}
          let returned ← invoke fuel functions stack callee actuals demand
          modify fun c => {c with sourceCallers := callers}
          if returned.length != outputs.length then throw {code := "E_RESOURCE_ARITY", message := "resource result count differs"}
          let mut frame := frame
          for (localName, value) in outputs.zip returned do
            let (next, target) ← bindName frame localName
            match value.payload with
            | .raw => step (.move value.owner target)
            | .map view => transferMap view target
            | .package view => transferPackage view target
            frame := next
          if let .callValue _ _ _ localName expected := first then
            let some (slot, actual) := (← get).returnedValue
              | throw {code := "E_RESOURCE_VALUE", message := "resource callee has no scalar result"}
            unless actual == expected do throw {code := "E_RESOURCE_VALUE", message := "resource scalar result type differs"}
            if frame.any (·.1 == localName) then throw {code := "E_RESOURCE_NAME", message := "scalar result shadows a binding"}
            frame := (localName, slot) :: frame
          pure frame
        | .branch condition yes no => do
          let condition ← match condition with
            | .literal value => pure (ValueFlow.Condition.literal value)
            | .slot localName => do
              let slot ← resolve frame localName
              unless ValueFlow.type? (← get).scalarSlots slot == some .bool do
                throw {code := "E_RESOURCE_VALUE", message := "resource branch requires a live Bool value"}
              pure (.slot slot)
          let before ← get
          set {before.clearArmReceipts with
            branchDepth := before.branchDepth + 1
            codeBlock := (before.code.size, true) :: before.codeBlock
            code := #[]
            flow := #[]
            returnedValue := none}
          let _ ← expandAt fuel functions stack (path ++ [position, 0]) 0 frame yes
          cleanupDependencies before.resources
          let left ← get
          set {before.clearArmReceipts with
            branchDepth := before.branchDepth + 1
            codeBlock := (before.code.size, false) :: before.codeBlock
            nextSymbol := left.nextSymbol
            unused := left.unused
            work := left.work
            code := #[]
            flow := #[]
            returnedValue := none
            resources := {before.resources with nextAllocation := left.resources.nextAllocation}}
          let _ ← expandAt fuel functions stack (path ++ [position, 1]) 0 frame no
          cleanupDependencies before.resources
          let right ← get
          let work ← debitWork right.work (left.resources.work + right.resources.work)
          let resources ← join left.resources right.resources
          set {Context.mergeArmReceipts before left right with
            work
            branchDepth := before.branchDepth
            codeBlock := before.codeBlock
            resources
            code := before.code.push (.branch condition.projection left.code.toList right.code.toList)
            flow := before.flow.push (.branch condition left.flow.toList right.flow.toList)
            scalarSlots := before.scalarSlots
            returnedValue := none
            numerical := before.numerical
            tensors := before.tensors
            packCaches := before.packCaches}
          pure frame
      expandAt fuel functions stack path (position + 1) after rest
  def invoke : Nat → List Function → List Nat → Nat → List Symbol → Bool → M (List Returned)
    | 0, _, _, _, _, _ => throw {code := "E_RESOURCE_LIMIT", message := "resource call exceeds the depth bound"}
    | fuel + 1, functions, stack, callee, actuals, demand => atFunction callee .header do
      spend
      if stack.contains callee then throw {code := "E_RESOURCE_RECURSION", message := "resource functions cannot recurse"}
      let some function := functions.find? (·.id == callee)
        | throw {code := "E_RESOURCE_FUNCTION", message := "resource callee does not exist"}
      let before ← get
      let (frame, borrowed, runtimeBorrowed) ← arguments callee function.parameters actuals
      let frame ← expandAt fuel functions (callee :: stack) [] 0 frame function.body
      atResult callee frame do
        cleanupDependencies before.resources
        let returned ← finish before.resources frame borrowed function.results
        let runtimeContext ← get
        let runtimeAfter ← Shapes.Functions.finish before.shapes runtimeContext.shapes runtimeBorrowed
        if runtimeAfter.events.size != runtimeContext.shapes.events.size then setShapes runtimeAfter
        else modify fun context => {context with shapes := runtimeAfter}
        let nestedShape := if before.shapeCalls.size < runtimeContext.shapeCalls.size then
          runtimeContext.shapeCalls.back? else none
        let (runtimeReceipt, work) ← Shapes.Functions.checkCallMetered before.shapes runtimeAfter nestedShape
          (← get).work
        modify fun context => {context with work}
        if runtimeAfter.events.size != before.shapes.events.size then
          modify fun context => {context with shapeCalls := context.shapeCalls.push runtimeReceipt}
        -- Discarding a result avoids native evaluation, not its signature audit.
        -- Pair terminals remain compatible without becoming scalar flow slots.
        if let some (fragment, locals, expected) := function.valueResult then
          let arguments ← (locals.mapM (resolve frame) : Except Error (List Symbol))
          let context ← get
          let some signature := context.signatures[fragment]?
            | throw {code := "E_RESOURCE_VALUE", message := "callee return fragment is absent"}
          unless signature.result == expected && signature.parameters.all ValueFlow.scalar &&
              arguments.map (ValueFlow.type? context.scalarSlots) == signature.parameters.map some do
            throw {code := "E_RESOURCE_VALUE", message := "callee return arguments or signature differ"}
        let after ← get
        let results := returned.map fun value => (value.owner, value.type)
        let prefixWork ← debitWork after.work (1 + before.code.size + after.code.size +
          before.resources.work + after.resources.work)
        let statements := after.code.toList.drop before.code.size
        if slice : before.code.toList ++ statements = after.code.toList then
          let nested := if before.calls.size < after.calls.size then after.calls.back? else none
          let (checked, work) ← replayMeteredWithEvidence (run 4096) (runMetered 4096) before.resources
            statements (nested.map fun receipt =>
              ⟨receipt.before, receipt.statements, .ok receipt.after, receipt.replayed⟩) prefixWork
          match result : checked.val with
          | .error diagnostic => throw diagnostic
          | .ok state =>
            if exactState : state = after.resources then
              if valid : ExitValid before.resources after.resources results then
                let receipt : CallReceipt := ⟨callee, before.resources, after.resources, results,
                  before.code.toList, statements, after.code.toList, slice, exactState ▸ checked.property.trans result, valid⟩
                set {after with
                  work
                  calls := after.calls.push receipt
                  numerical := before.numerical
                  tensors := before.tensors
                  packCaches := before.packCaches
                  returnedValue := none}
                if demand then
                  match contract : function.valueResult with
                  | none => pure ()
                  | some (fragment, locals, type) =>
                    match resolved : locals.mapM (resolve frame) with
                    | .error diagnostic => throw diagnostic
                    | .ok arguments =>
                      let valueBefore ← get
                      match typed : ValueFlow.checkCall valueBefore.signatures valueBefore.scalarSlots fragment arguments with
                      | .error diagnostic => throw diagnostic
                      | .ok actual =>
                        unless actual == type do throw {code := "E_RESOURCE_VALUE", message := "callee result signature differs"}
                        let slot ← fresh
                        scalarCall slot fragment arguments type
                        let valueAfter ← get
                        if sameCallee : function.id = receipt.callee then
                          if exactType : actual = type then
                            if completed : ValueFlow.project valueBefore.flow.toList = receipt.code then
                              if emitted : valueBefore.flow.toList ++ [.value slot fragment arguments] = valueAfter.flow.toList then
                                let runtimeReturn ← checkRuntimeReturn before.flow.toList valueBefore.flow.toList runtimeReceipt
                                let resultReceipt : ValueReturnReceipt := ⟨receipt, function, sameCallee, frame,
                                  fragment, locals, type, contract, arguments, resolved, valueBefore.signatures,
                                  valueBefore.scalarSlots, exactType ▸ typed, slot, valueBefore.flow.toList,
                                  valueAfter.flow.toList, completed, emitted, runtimeReturn⟩
                                set {valueAfter with
                                  returnedValue := some (slot, type)
                                  valueReturns := valueAfter.valueReturns.push resultReceipt}
                              else throw {code := "E_RESOURCE_VALUE", message := "scalar result changed earlier mixed operations"}
                            else throw {code := "E_RESOURCE_VALUE", message := "scalar result precedes resource call completion"}
                          else throw {code := "E_RESOURCE_VALUE", message := "scalar result signature differs"}
                        else throw {code := "E_RESOURCE_VALUE", message := "scalar result belongs to another callee"}
                return returned
              else throw {code := "E_RESOURCE_ESCAPE", message := "call exit failed the independent resource audit"}
            else throw {code := "E_RESOURCE_STATE", message := "call expansion differs from replayed resource transitions"}
        else throw {code := "E_RESOURCE_STATE", message := "call expansion changed earlier resource operations"}
end

def expand (fuel : Nat) (functions : List Function) (stack : List Nat)
    (frame : Frame) (statements : List Statement) : M Frame :=
  expandAt fuel functions stack [] 0 frame statements

end VastitasKernel.Storage.Functions
