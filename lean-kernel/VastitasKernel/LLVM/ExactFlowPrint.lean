import VastitasKernel.LLVM.ExactFlow

set_option autoImplicit false

namespace VastitasKernel.LLVM.ExactFlow
open ExactLibrary

def reg (b s : Nat) := s!"%b{b}v{s}"
def edgeLabel (src dst : Nat) := s!"e{src}_{dst}"
def constantScope (fn block : Nat) := s!"{fn}_{block}_"
def fnName (id : Nat) := s!"@vq_f{id}"

private def typedArg (kinds : Array Kind) (b r : Nat) :=
  (kinds[r]?.getD .int).abi ++ " " ++ reg b r

private def opLine (fs : Array Func) (kinds : Array Kind) (f b dst : Nat) (op : Op) : String :=
  let assign := "  " ++ reg b dst ++ " = "
  match op with
  | .exact step => callWith step dst (constantScope f b) (reg b)
  | .invoke callee args =>
    assign ++ "call " ++ ((fs[callee]?).map Func.result |>.getD .int).abi ++ " " ++ fnName callee ++
      "(" ++ String.intercalate ", " (args.map (typedArg kinds b)) ++ ")"
  | .boolean bit => assign ++ "or i32 0, " ++ (if bit then "1" else "0")
  | .boolNot a => assign ++ "xor i32 " ++ reg b a ++ ", 1"
  | .boolAnd a c => assign ++ "and i32 " ++ reg b a ++ ", " ++ reg b c
  | .boolOr a c => assign ++ "or i32 " ++ reg b a ++ ", " ++ reg b c

/-- A called function borrows its entry parameters. Later block parameters each
own the reference passed on the taken edge. Every boxed instruction result owns one. -/
def ownedSlots (block arity : Nat) (kinds : Array Kind) : List Nat :=
  (List.range kinds.size).reverse.filter fun i =>
    (block != 0 || arity ≤ i) && kinds[i]?.any (· != .bool)

def retainedSlots (args : List Nat) (kinds : Array Kind) :=
  args.filter fun i => kinds[i]?.any (· != .bool)

private def rc (name : String) (b i : Nat) := "  call void " ++ symbol name ++ "(ptr " ++ reg b i ++ ")"

private abbrev Incoming := Array (List (Nat × Array Nat))

private def predecessors (f : Func) : Incoming := Id.run do
  let mut result := Array.replicate f.blocks.size []
  for (b,i) in f.blocks.toList.zipIdx do
    for e in b.exit.edges do
      result := result.modify e.dest fun xs => (i,e.args.toArray) :: xs
  return result.map List.reverse

private def blockLines (fs : Array Func) (fn i : Nat) (b : Block)
    (incoming : List (Nat × Array Nat)) : List String := Id.run do
  let kinds := (b.slotKinds fs).getD #[]
  let phis := if i == 0 then [] else b.params.zipIdx.map fun (k,s) =>
    let legs := incoming.map fun (pred,args) =>
      "[ " ++ reg pred (args[s]?.getD 0) ++ ", %" ++ edgeLabel pred i ++ " ]"
    "  " ++ reg i s ++ " = phi " ++ k.abi ++ " " ++ String.intercalate ", " legs
  let ops := (b.ops.zipIdx b.params.length).map fun (op,dst) => opLine fs kinds fn i dst op
  let drops := (ownedSlots i b.params.length kinds).map (rc "release" i)
  let transfer (args : List Nat) := (retainedSlots args kinds).map (rc "retain" i) ++ drops
  let gotoEdge (e : Edge) := "label %" ++ edgeLabel i e.dest
  let control := match b.exit with
    | .ret r => transfer [r] ++ ["  ret " ++ typedArg kinds i r]
    | .jump e => ["  br " ++ gotoEdge e]
    | .branch cond yes no =>
      [s!"  %cond{i} = icmp ne i32 {reg i cond}, 0",
       s!"  br i1 %cond{i}, {gotoEdge yes}, {gotoEdge no}"]
  let edges := b.exit.edges.flatMap fun e =>
    [edgeLabel i e.dest ++ ":"] ++ transfer e.args ++ [s!"  br label %b{e.dest}"]
  return ["; block (" ++ String.intercalate ", " (b.params.map Kind.name) ++ ")", s!"b{i}:"] ++
    phis ++ ops ++ control ++ edges

private def functionLines (fs : Array Func) (fn : Nat) (f : Func) : List String := Id.run do
  let globals := f.blocks.toList.zipIdx.flatMap fun (b,i) =>
    (b.ops.zipIdx b.params.length).filterMap fun (op,dst) => do
      let .exact step := op | none
      return global (← step.literal) dst (constantScope fn i)
  let incoming := predecessors f
  let body := f.blocks.toList.zipIdx.flatMap fun (b,i) => blockLines fs fn i b (incoming[i]?.getD [])
  let params := (f.params.getD []).zipIdx.map fun (k,j) => k.abi ++ " " ++ reg 0 j
  return ["; flow -> " ++ f.result.name] ++ globals ++
    ["define internal " ++ f.result.abi ++ " " ++ fnName fn ++ "(" ++ String.intercalate ", " params ++ ") {"] ++
    body ++ ["}"]

/-- A runtime declaration depends on its operation and scalar sort. Literal
payloads and SSA operands only occur at the call site. -/
private def sameDeclaration : Step → Step → Bool
  | .nat _, .nat _ | .int _, .int _ => true
  | .apply op _, .apply op' _ => decide (op = op')
  | .compare k op .., .compare k' op' .. => decide (k = k' ∧ op = op')
  | _, _ => false

def Code.bodyLines (c : Code) : List String :=
  let ops := c.functions.toList.flatMap fun f => f.blocks.toList.flatMap fun b =>
    b.ops.filterMap fun op => match op with | .exact s => some s | _ => none
  ["declare void @vastitas_initialize_v1()", "declare i32 @vastitas_exit_status_v1(ptr)",
   "declare void @vastitas_retain_v1(ptr)", "declare void @vastitas_release_v1(ptr)"] ++
  (ops.eraseDupsBy sameDeclaration).map Step.declaration ++
  (c.functions.toList.zipIdx.flatMap fun (f,i) => functionLines c.functions i f) ++
  ["define i32 @main() {", "entry:", "  call void @vastitas_initialize_v1()",
   "  %result = call ptr " ++ fnName c.entry ++ "()", "  %status = call i32 @vastitas_exit_status_v1(ptr %result)",
   "  ret i32 %status", "}"]

def Code.print (c : Code) : List UInt8 :=
  c.header.print ++ ("\n" ++ String.intercalate "\n" c.bodyLines ++ "\n").toUTF8.data.toList

end VastitasKernel.LLVM.ExactFlow
