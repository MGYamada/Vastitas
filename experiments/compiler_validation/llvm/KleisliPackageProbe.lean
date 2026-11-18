import VastitasKernel.LLVM.FiniteProgram

open Lean VastitasKernel VastitasKernel.LLVM

/-- Machine-local manifest paths participate in the full revision check.
The portable report displays the package, module and name of each symbol. -/
private def owner (id : Namespace.Owner) : Json :=
  Json.mkObj [("package", id.scope.package.name), ("version", id.scope.package.version),
    ("module", toJson id.scope.path), ("name", id.name)]

private def index : Indexed.FunctionSource.StaticIndex → Json
  | .category id => Json.mkObj [("category", owner id)]
  | .monad id => Json.mkObj [("monad", owner id)]
  | .object id tag => Json.mkObj [("category", owner id), ("object", tag)]

def main (args : List String) : IO Unit := do
  let receiptPath :: sourcePath :: modulePath :: focus := args
    | throw (IO.userError "expected revision, source and LLVM files")
  unless focus.length ≤ 1 do throw (IO.userError "expected at most one function name")
  let receipt ← IO.ofExcept (Json.parse (← IO.FS.readFile receiptPath))
  let wire ← IO.ofExcept (receipt.getObjVal? "input")
  let source ← IO.ofExcept (wire.getObjVal? "root_source" >>= (·.getObjValAs? String "text"))
  unless source.toUTF8 == (← IO.FS.readBinFile sourcePath) do throw (IO.userError "root source mismatch")
  let .ok req := ResourceSource.Wire.check wire true | throw (IO.userError "wire rejected")
  let bytes := (← IO.FS.readBinFile modulePath).data.toList
  let some parsed := FiniteModule.parse bytes | throw (IO.userError "complete LLVM bytes rejected")
  let some a := FiniteProgram.compile req parsed.code.header | throw (IO.userError "finite package rejected")
  unless a.linked.exe.revision == receipt && a.model == parsed && FiniteModule.print a.model == bytes do
    throw (IO.userError "revision or LLVM module mismatch")
  let kept := a.linked.dispositions.filterMap fun d => d.localId.map fun localId =>
    Json.mkObj [("source_symbol", d.original), ("local_symbol", localId), ("owner", owner d.owner),
      ("body_package", d.bodyScope.package.name), ("body_module", toJson d.bodyScope.path),
      ("definition", d.specialization.definition), ("indices", toJson (d.indices.map index))]
  let calls := a.linked.exe.functions.map fun f =>
    Json.mkObj [("caller", f.coreId), ("callees", toJson (f.blocks.toList.flatMap fun b =>
      b.ops.toList.filterMap fun op => match op.code with
        | .call t => some t.symbol | _ => none))]
  let focusFields ← match focus with
    | [] => pure []
    | [name] => do
      let [f] := a.linked.exe.functions.toList.filter (·.id.owner.name == name)
        | throw (IO.userError "focused function must have a unique linked specialization")
      let ops := f.blocks.toList.flatMap fun b => b.ops.toList.map fun op =>
        let fields := [("opcode", toJson op.code.tag),
          ("operands", toJson (op.args.map fun r => [r.block,r.slot]))]
        Json.mkObj <| match op.code with
          | .lookupOrdinal site => fields ++ [("table", owner site.table),
              ("authority", toJson (site.category.map owner))]
          | _ => fields
      pure [("focused_function", Json.mkObj [("local_symbol", f.coreId), ("owner", owner f.id.owner),
        ("operations", toJson ops)])]
    | _ => throw (IO.userError "unexpected focus arguments")
  let fields : List (String × Json) := [("original_symbols", a.linked.dispositions.size),
    ("source_entry", a.linked.sourceEntry), ("local_entry", a.linked.entry),
    ("retained", toJson kept), ("calls", toJson calls), ("observation_fuel", a.observed.fuel),
    ("core_and_midir_integer", toJson a.observed.value),
    ("modeled_exit", toJson (a.model.code.entryStatus.map UInt32.toNat))]
  IO.println (Json.mkObj (fields ++ focusFields)).compress
