import VastitasKernel.ResourceOwnershipSource

set_option autoImplicit false

/-! Replay tensor views, finite network declarations and contraction plans in
their physical resource function. Occurrences and named edges are identified
by name. Boundary ports and the complete plan retain their written order. -/
namespace VastitasKernel.ResourceTensorSource
open AssemblyText ResourceSource ResourceStatementSource SourceText Storage

private def failHere {α : Type} (message : String) : Parser α := do
  throw (diagnostic (← peek).span message)

private def callNames (name : String) (args : List String) : Parser Unit :=
  tokens (callFields name (nameFields args))

private def view (name loan : String) (axes : List String) (g : Tensor.Grouping) : Parser Unit := do
  let rank := axes.length
  unless 1 ≤ rank && rank ≤ 3 do failHere "expected a tensor of rank one, two or three"
  tokens [.ident "tensor", .ident name, .punctuation '=', .ident ("view" ++ toString rank), .punctuation '(', .ident loan]
  for axis in axes do tokens [.punctuation ',', .ident axis]
  if rank == 1 || (rank == 2 && ((← peek).kind matches .symbol ')')) then
    unless g.order == List.range rank && g.split == 1 do failHere "implicit tensor grouping differs from the source"
  else
    tokens [.punctuation ',', .ident "axes"]
    delimited '(' ')' g.order fun n => tokens [.dimension n]
    tokens [.punctuation ',', .dimension g.split]
  token (.punctuation ')')

def operation : Tensor.Operation String → Parser Unit
  | .view n loan axes g => view n loan axes g
  | .pack src dst => callNames "pack3" [src,dst]
  | .cachedPack n src dst => do
    tokens [.ident "cache", .ident n, .punctuation '=']
    callNames "pack3" [src,dst]
  | .contract3 a b out .nativeFast => callNames "contract3" [a,b,out,"NativeFast"]
  | .cachedContract3 cache a b out .nativeFast => callNames "contract3_cached" [cache,a,b,out,"NativeFast"]

private abbrev Fields := List ExactLexeme

private def occurrence (name value : String) : String × Fields :=
  (name, [.ident name, .punctuation '=', .ident value])

private def networkPort (p : TensorNetwork.Port) : Fields :=
  [.ident p.occurrence, .punctuation '.', .ident (match p.role with | .input => "input" | .output => "output")]

private def treePort (p : TensorTree.Port) : Fields :=
  [.ident p.occurrence, .punctuation '[', .dimension p.axis, .punctuation ']']

private structure Rows where
  occurrences : List (String × Fields)
  namedEdges : List (String × Fields) := []
  edges : List Fields := []
  inputs : List Fields := []
  outputs : List Fields := []
  boundary : List Fields := []

private abbrev NamedRows := Std.HashMap String Fields

private def namedRow (keyword : String) (remaining : NamedRows) : Parser NamedRows := do
  token (.ident keyword)
  let .word name := (← peek).kind | failHere "expected a contraction declaration name"
  let some fields := remaining[name]? | failHere "unknown or repeated contraction declaration"
  tokens fields
  token (.punctuation ';')
  return remaining.erase name

private def row : List Fields → Parser (List Fields)
  | [] => failHere "unexpected or repeated contraction declaration"
  | fields :: rest => do tokens fields; token (.punctuation ';'); return rest

/-- Each boundary clause appends its ports, including when clauses are split
or the final comma is present. -/
private def boundary (remaining : List Fields) : Parser (List Fields) := do
  tokens [.ident "boundary", .punctuation '(']
  let mut left := remaining
  for fields in remaining do
    if (← peek).kind matches .symbol ')' then break
    tokens fields
    left := left.drop 1
    unless (← peek).kind matches .symbol ',' do break
    token (.punctuation ',')
  tokens [.punctuation ')', .punctuation ';']
  return left

private def declarations (initial : Rows) (tree : Bool) : Parser Unit := do
  let mut rows := initial
  let mut occurrences := Std.HashMap.ofList initial.occurrences
  let mut namedEdges := Std.HashMap.ofList initial.namedEdges
  unless occurrences.size == initial.occurrences.length && namedEdges.size == initial.namedEdges.length do
    failHere "duplicate named contraction declaration in request"
  for _ in [:(if tree then 128 else 5)] do
    match (← peek).kind with
    | .word "occurrence" => occurrences ← namedRow "occurrence" occurrences
    | .word "edge" =>
      if tree then namedEdges ← namedRow "edge" namedEdges
      else rows := {rows with edges := ← row rows.edges}
    | .word "input" => rows := {rows with inputs := ← row rows.inputs}
    | .word "output" => rows := {rows with outputs := ← row rows.outputs}
    | .word "boundary" =>
      unless tree do failHere "unexpected boundary in two-map network"
      rows := {rows with boundary := ← boundary rows.boundary}
    | _ => break
  unless occurrences.isEmpty && namedEdges.isEmpty && rows.edges.isEmpty && rows.inputs.isEmpty &&
      rows.outputs.isEmpty && rows.boundary.isEmpty do
    failHere "contraction declarations differ from the source"

private def opening (word output : String) : Parser Unit := do
  callNames word [output,"NativeFast"]
  token (.punctuation '{')

def network (g : TensorNetwork.Graph String) (output : String) : Parser Unit := do
  opening "contract" output
  declarations {
    occurrences := g.occurrences.map fun o => occurrence o.name o.value
    edges := g.edges.map fun e => callFields "edge" [networkPort e.dual, networkPort e.primal]
    inputs := g.inputs.map fun p => callFields "input" [networkPort p]
    outputs := g.outputs.map fun p => callFields "output" [networkPort p] } false

private def step : TensorTree.PlanStep String ResourceSource.Action → Parser Unit
  | .action a => do
    unless (a matches .borrow .. | .release ..) do failHere "expected a borrow or release in the contraction plan"
    let some (fields, _) := ResourceOwnershipSource.spelling? (.action a {}) | failHere "unknown contraction loan action"
    tokens fields
  | .view n loan axes g => view n loan axes g
  | .regroup component target => callNames "regroup" [component,target]
  | .rebind component target => callNames "rebind" [component,target]
  | .join n edge left right out => do
    tokens [.ident "join", .ident n, .punctuation '=', .punctuation '(']
    tokens (([edge,left,right,out].map ExactLexeme.ident).intersperse (.punctuation ','))
    token (.punctuation ')')

def tree (g : TensorTree.Graph String) (output : String) (plan : List (TensorTree.PlanStep String ResourceSource.Action)) :
    Parser Unit := do
  opening "contract_tree" output
  declarations {
    occurrences := g.occurrences.map fun o => occurrence o.name o.value
    namedEdges := g.edges.map fun e => (e.name, [.ident e.name, .punctuation '=', .punctuation '('] ++
      treePort e.dual ++ [.punctuation ','] ++ treePort e.primal ++ [.punctuation ')'])
    boundary := g.boundary.map treePort } true
  tokens [.ident "plan", .punctuation '{']
  for action in plan do
    step action
    token (.punctuation ';')
  token (.punctuation '}')

end VastitasKernel.ResourceTensorSource
