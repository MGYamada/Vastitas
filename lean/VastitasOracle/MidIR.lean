import Std.Data.HashMap.Lemmas
import VastitasKernel.MidIR.Evaluation
import VastitasKernel.IndexedSemantics
import VastitasOracle.ExactFold

set_option autoImplicit false

/-! Pure finite MidIR observations. The meaning is evaluated over values and
control flow, independent of the structural validator. The Opt-to-Exec pass
preserves function observations. Core-to-MidIR refinement is a separate obligation. -/
namespace VastitasOracle.MidIR
open VastitasKernel VastitasKernel.Indexed VastitasKernel.MidIR
open VastitasKernel.Indexed.Core.Semantics

private def fits : VastitasKernel.MidIR.Ty → Value → Bool
  | .unit, .unit => true
  | .bool, .boolean _ => true
  | .finite c, .finiteTag d _ => c == d
  | _, _ => false

/-- Read the ordered nominal arguments of a table, including the owner and
endpoints of each Hom fiber. Arity mismatches have no value. -/
def lookupKey : List FiniteSort → List Value → Option (List String)
  | [], [] => some []
  | sort :: sorts, .finiteTag actual tag :: args => do
    guard (actual == sort)
    return tag :: (← lookupKey sorts args)
  | _, _ => none

def lookupValue (env : Environment) (site : FiniteLookup) (args : List Value) : Option Value := do
  let plan ← site.plan? env
  let key ← lookupKey site.inputs args
  return .finiteTag site.output (← plan.atKey key)

/-- For any SSA operand list read from the Core environment, the two
representations of the arguments yield exactly the same lookup key. -/
private theorem lookupKey_eq (values : Values) (symbols : List Nat) (sorts : List FiniteSort) :
    (symbols.mapM values >>= lookupKey sorts) = readFiniteTags values symbols sorts := by
  induction symbols generalizing sorts with
  | nil => cases sorts <;> rfl
  | cons sym rest ih =>
    cases sorts with
    | nil =>
      cases h : values sym <;> cases r : rest.mapM values <;>
        simp [List.mapM_cons, h, r, lookupKey, readFiniteTags]
    | cons s ss =>
      cases h : values sym with
      | none => simp [List.mapM_cons, h, readFiniteTags]
      | some v =>
        cases args : rest.mapM values <;> have tail := ih ss <;>
          simp [args] at tail <;> cases v <;>
          simp [List.mapM_cons, h, args, lookupKey, readFiniteTags, ← tail, guard] <;>
          split <;> rfl

/-- Applies equally to nullary tables, multiple columns and a dependent
composition table. The source and MidIR read the same checked plan. -/
theorem lookup_from_core (env : Environment) (site : FiniteLookup) (values : Values)
    (symbols : List Nat) (args : List Value) (read : symbols.mapM values = some args) :
    lookupValue env site args = evalFiniteLookup env values site symbols := by
  have key := lookupKey_eq values symbols site.inputs
  simp [read] at key
  simp [lookupValue, evalFiniteLookup, key]

abbrev Resolver := CallTarget → List Value → Option Value

def denote {p : Phase} (env : Environment) (op : Opcode p) (args : List Value)
    (resolve : Resolver := fun _ _ => none) : Option Value :=
  match op with
  | .unit => if args.isEmpty then some .unit else none
  | .boolean b => if args.isEmpty then some (.boolean b) else none
  | .natural n => if args.isEmpty then some (.natural n) else none
  | .exactOp op => Evaluation.exactValue op args
  | .integer n => if args.isEmpty then some (.integer n) else none
  | .finiteTag c t => if args.isEmpty then some (.finiteTag c t) else none
  | .finiteOrdinal c n => do
    guard args.isEmpty
    let tags ← FiniteSort.tags env c
    return .finiteTag c (← tags[n]?)
  | .lookupTag s | .lookupOrdinal s => lookupValue env s args
  | .boolAnd => match args with
    | [.boolean a, .boolean b] => some (.boolean (a && b))
    | _ => none
  | .boolOr => match args with
    | [.boolean a, .boolean b] => some (.boolean (a || b))
    | _ => none
  | .boolNot => match args with
    | [.boolean a] => some (.boolean (!a))
    | _ => none
  | .call target => resolve target args
  | .compare k t => do
    let [a, b] := args | none
    guard (fits t a && fits t b)
    let equal := decide (a = b)
    return .boolean (match k with | .eq => equal | .ne => !equal)

/-- Resolving a tag to an ordinal in its checked nominal sort preserves its
logical value, including the endpoints of a Hom sort. Covers every operand
list, including malformed lists. -/
theorem execute_denote_with (resolve : Resolver) (env : Environment) (op : Opcode .optimization)
    (out : Opcode .execution) (args : List Value) (h : op.execute env = some out) :
    denote env out args resolve = denote env op args resolve := by
  cases op with
  | unit => cases h; rfl
  | boolean b => cases h; rfl
  | integer n | natural n => cases h; rfl
  | exactOp op => cases h; rfl
  | boolAnd | boolOr | boolNot => cases h; rfl
  | compare k t => cases h; rfl
  | lookupTag s => cases h; rfl
  | call target => cases h; rfl
  | finiteTag c t =>
    cases hc : FiniteSort.tags env c with
    | none => simp [Opcode.execute, hc] at h
    | some tags =>
      by_cases ht : tags[tags.idxOf t]? = some t
      · simp [Opcode.execute, hc, ht] at h
        subst out
        cases args <;> simp [denote, hc, ht, guard]
      · simp [Opcode.execute, hc, ht] at h

theorem execute_denote (env : Environment) (op : Opcode .optimization)
    (out : Opcode .execution) (args : List Value) (h : op.execute env = some out) :
    denote env out args = denote env op args := execute_denote_with _ env op out args h

/-- The actual Core selector and the runtime opcode agree on arbitrary scalar
values for every accepted source operator and ordered argument signature. -/
theorem exact_binary_from_core (op : BinaryOp) (a b : VastitasKernel.MidIR.ExactFold.Scalar)
    (selected : ExactOp) (choice : ExactOp.binary op a.type b.type = some selected) :
    Evaluation.exactValue selected [ExactFold.scalarValue a, ExactFold.scalarValue b] =
      evalBinary op (ExactFold.scalarValue a) (ExactFold.scalarValue b) := by
  cases a <;> cases b <;> cases op <;>
    simp [ExactOp.binary, Arithmetic.ofCore, VastitasKernel.MidIR.ExactFold.Scalar.type, guard,
      failure, pure, bind] at choice <;> subst selected <;> rfl

theorem exact_unary_from_core (n : Nat) (i : Int) :
    Evaluation.exactValue .neg [.integer i] = evalUnary .neg (.integer i) ∧
    Evaluation.exactValue .natToInt [.natural n] = some (.integer (Int.ofNat n)) := ⟨rfl, rfl⟩

/-- At the declared arity, both element sorts use the Core construction and projection rules. -/
theorem pair_from_core (e : PairElem) (a b p : Value) (first : Bool) :
    Evaluation.exactValue (.pair e) [a,b] = evalPair e a b ∧
    Evaluation.exactValue (.project e first) [p] = evalProject e first p := ⟨rfl,rfl⟩

theorem pair_projections (e : PairElem) (x y : Value)
    (p : Value) (made : Evaluation.exactValue (.pair e) [x,y] = some p) :
    Evaluation.exactValue (.project e true) [p] = some x ∧
    Evaluation.exactValue (.project e false) [p] = some y := by
  cases e <;> cases x <;> cases y <;> cases made <;> exact ⟨rfl,rfl⟩

theorem boolAnd_from_core {p : Phase} (env : Environment) (a b : Bool) :
    denote env (.boolAnd : Opcode p) [.boolean a, .boolean b] =
      evalBinary .and (.boolean a) (.boolean b) := rfl

theorem boolOr_from_core {p : Phase} (env : Environment) (a b : Bool) :
    denote env (.boolOr : Opcode p) [.boolean a, .boolean b] =
      evalBinary .or (.boolean a) (.boolean b) := rfl

theorem boolNot_from_core {p : Phase} (env : Environment) (a : Bool) :
    denote env (.boolNot : Opcode p) [.boolean a] = evalUnary .not (.boolean a) := rfl

theorem unit_from_core {p : Phase} (m : Core.Module) (fuel : Nat) (values : Values) :
    denote m.declarations.indexed (.unit : Opcode p) [] =
      eval m (fuel + 1) values .unit := rfl

private abbrev SemanticOp := Evaluation.SemanticOp
private abbrev SemanticBlock := Evaluation.SemanticBlock
open Evaluation (runGraph)

private def observeOp {p : Phase} (resolve : Resolver) (env : Environment) (op : Op p) : SemanticOp :=
  ⟨op.args, fun vs => denote env op.code vs resolve⟩

private def observeBlock {p : Phase} (resolve : Resolver) (env : Environment) (b : Block p) : SemanticBlock :=
  ⟨b.params, b.ops.map (observeOp resolve env), b.term⟩

def run {p : Phase} (env : Environment) (f : MidIR.Function p) (args : List Value) : Option Value :=
  runGraph (f.blocks.map (observeBlock (fun _ _ => none) env)) args

/-- Interpret a direct call with the selected symbol in this exact module.
The decreasing call depth also bounds interpretation of malformed modules. -/
def runWith {p : Phase} (env : Environment) (f : MidIR.Function p) (resolve : Resolver)
    (args : List Value) : Option Value :=
  runGraph (f.blocks.map (observeBlock resolve env)) args

def invoke {p : Phase} (m : Module p) : Nat → Resolver
  | 0, _, _ => none
  | depth + 1, target, args => do
    let f ← m.functions[target.symbol]?
    guard (decide (f.target = target))
    runWith m.env f (invoke m depth) args

private theorem checked_lookupKey (sorts : List FiniteSort) (values : List Value) :
    Evaluation.lookupKey sorts values = lookupKey sorts values := by
  induction sorts generalizing values with
  | nil => cases values <;> rfl
  | cons sort sorts ih =>
    cases values with
    | nil => rfl
    | cons v vs => cases v <;> simp only [Evaluation.lookupKey, lookupKey, ih]

private theorem checked_denote {p : Phase} (env : Environment) (op : Opcode p)
    (args : List Value) (resolve : Resolver) : Evaluation.denote env op args resolve = denote env op args resolve := by
  cases op <;> first | rfl | simp [Evaluation.denote, denote, Evaluation.lookupValue, lookupValue, checked_lookupKey]

private theorem checked_observeOp {p : Phase} (resolve : Resolver) (env : Environment) (op : Op p) :
    Evaluation.observeOp resolve env op = observeOp resolve env op := by
  simp [Evaluation.observeOp, observeOp, checked_denote]

theorem checked_runWith {p : Phase} (env : Environment) (f : MidIR.Function p)
    (resolve : Resolver) (args : List Value) :
    Evaluation.runWith env f resolve args = runWith env f resolve args := by
  have ops : Evaluation.observeOp (p := p) resolve env = observeOp resolve env :=
    funext (checked_observeOp resolve env)
  have blocks : Evaluation.observeBlock (p := p) resolve env = observeBlock resolve env := by
    funext b
    simp only [Evaluation.observeBlock, observeBlock, ops]
  simp only [Evaluation.runWith, runWith, blocks]

/-- The executable entry observer uses the same SSA denotation, including
malformed arguments and resolver failures, as the Oracle. -/
theorem checked_invoke {p : Phase} (m : Module p) (depth : Nat) :
    Evaluation.invoke m depth = invoke m depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    funext target args
    simp only [Evaluation.invoke, invoke, ih, checked_runWith]

/-- The single unary lookup block reads its argument and returns the result
of the lookup. The statement also covers a missing logical result. -/
theorem runWith_unary (resolve : Resolver) {p : Phase} (env : Environment) (s : UnaryLookup) (f : MidIR.Function p)
    (shape : f.blocks = #[s.block p]) (arg : Value) :
    runWith env f resolve [arg] = lookupValue env s.site [arg] := by
  unfold runWith
  rw [shape]
  cases found : lookupValue env s.site [arg] <;> cases p <;>
    simp [runGraph, Evaluation.runGraph.go, observeBlock, observeOp, UnaryLookup.block,
      UnaryLookup.code, denote, guard, found]

theorem run_unary {p : Phase} (env : Environment) (s : UnaryLookup) (f : MidIR.Function p)
    (shape : f.blocks = #[s.block p]) (arg : Value) :
    run env f [arg] = lookupValue env s.site [arg] := runWith_unary _ _ _ _ shape _

/-- A two-argument SSA block passes its incoming values to its operation in
parameter order and returns precisely the value of that operation. -/
theorem run_binary {p : Phase} (env : Environment) (f : MidIR.Function p) (op : Opcode p)
    (a b : VastitasKernel.MidIR.Ty) (row col : Value)
    (shape : f.blocks = #[⟨#[a,b], #[⟨op,[⟨0,0⟩,⟨0,1⟩]⟩], .ret ⟨0⟩ ⟨0,2⟩⟩]) :
    run env f [row,col] = denote env op [row,col] := by
  unfold run
  rw [shape]
  cases h : denote env op [row,col] <;>
    simp [runGraph, Evaluation.runGraph.go, observeBlock, observeOp, Std.HashMap.getElem?_insert, guard, h]

/-- The second argument can also occur first in the opcode's actual SSA operands. -/
theorem run_binary_swapped {p : Phase} (env : Environment) (f : MidIR.Function p) (op : Opcode p)
    (a b : VastitasKernel.MidIR.Ty) (row col : Value)
    (shape : f.blocks = #[⟨#[b,a], #[⟨op,[⟨0,1⟩,⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,2⟩⟩]) :
    run env f [col,row] = denote env op [row,col] := by
  unfold run
  rw [shape]
  cases h : denote env op [row,col] <;>
    simp [runGraph, Evaluation.runGraph.go, observeBlock, observeOp, Std.HashMap.getElem?_insert, guard, h]

/-- A single unary call block invokes its exact target with the entry argument
and returns that result, including a failed resolution. -/
theorem runWith_call {p : Phase} (env : Environment) (resolve : Resolver) (f : MidIR.Function p)
    (target : CallTarget) (ty : VastitasKernel.MidIR.Ty) (arg : Value)
    (shape : f.blocks = #[⟨#[ty], #[⟨.call target,[⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]) :
    runWith env f resolve [arg] = resolve target [arg] := by
  unfold runWith
  rw [shape]
  cases found : resolve target [arg] <;>
    simp [runGraph, Evaluation.runGraph.go, observeBlock, observeOp, denote, guard, found]

theorem runWith_intLiteral {p : Phase} (env : Environment) (resolve : Resolver)
    (f : MidIR.Function p) (lit : IntLiteral) (shape : f.blocks = #[lit.block p]) :
    runWith env f resolve [] = some (.integer lit.value) := by
  simp [runWith, shape, runGraph, Evaluation.runGraph.go, IntLiteral.block, observeBlock, observeOp, denote, guard]

theorem runWith_boolParam {p : Phase} (env : Environment) (resolve : Resolver) (f : MidIR.Function p)
    (arg : Bool) (shape : f.blocks = #[⟨#[.bool],#[],.ret ⟨0⟩ ⟨0,0⟩⟩]) :
    runWith env f resolve [.boolean arg] = some (.boolean arg) := by
  simp [runWith, shape, runGraph, Evaluation.runGraph.go, observeBlock, guard]

theorem runWith_boolConst {p : Phase} (env : Environment) (resolve : Resolver) (f : MidIR.Function p)
    (arg b : Bool) (shape : f.blocks = #[⟨#[.bool],#[⟨.boolean b,[]⟩],.ret ⟨0⟩ ⟨0,1⟩⟩]) :
    runWith env f resolve [.boolean arg] = some (.boolean b) := by
  simp [runWith, shape, runGraph, Evaluation.runGraph.go, observeBlock, observeOp, denote, guard]

/-- Both actual predecessors feed the join argument. The condition must be
the result returned by the linked resolver for this exact target and operand. -/
theorem runWith_callBranch {p : Phase} (env : Environment) (resolve : Resolver) (f : MidIR.Function p)
    (target : CallTarget) (arg choice : Bool) (yes no : Int)
    (selected : resolve target [.boolean arg] = some (.boolean choice))
    (shape : f.blocks = #[
      ⟨#[], #[⟨.boolean arg,[]⟩,⟨.call target,[⟨0,0⟩]⟩], .branch ⟨0,1⟩ ⟨1,⟨0⟩,[]⟩ ⟨2,⟨0⟩,[]⟩⟩,
      ⟨#[], #[⟨.integer yes,[]⟩], .jump ⟨3,⟨1⟩,[⟨1,0⟩]⟩⟩,
      ⟨#[], #[⟨.integer no,[]⟩], .jump ⟨3,⟨2⟩,[⟨2,0⟩]⟩⟩,
      ⟨#[.int], #[], .ret ⟨3⟩ ⟨3,0⟩⟩]) :
    runWith env f resolve [] = some (.integer (if choice then yes else no)) := by
  cases choice <;> simp [runWith, shape, runGraph, Evaluation.runGraph.go, observeBlock, observeOp,
    denote, guard, selected]

/-- A successful, pointwise translation preserves the observations of the
whole array. The same lemma applies to instruction sequences and to blocks. -/
private theorem mapM_observes {α β γ : Type} (f : α → Option β) (a : α → γ) (b : β → γ)
    (sound : ∀ x y, f x = some y → b y = a x)
    (xs : Array α) (ys : Array β) (h : xs.mapM f = some ys) :
    ys.map b = xs.map a := by
  have listResult (vs : List α) (ws : List β) (ok : vs.mapM f = some ws) :
      ws.map b = vs.map a := by
    induction vs generalizing ws with
    | nil => simp at ok; subst ws; rfl
    | cons x tail ih =>
      cases hx : f x with
      | none => simp [List.mapM_cons, hx] at ok
      | some y =>
        cases ht : tail.mapM f with
        | none => simp [List.mapM_cons, hx, ht] at ok
        | some rest =>
          simp [List.mapM_cons, hx, ht] at ok
          subst ws
          simp [sound x y hx, ih rest ht]
  apply Array.toList_inj.mp
  have lists := congrArg (Option.map Array.toList) h
  have mapped : xs.toList.mapM f = some ys.toList := by
    simpa only [← Array.toList_mapM, Functor.map, Option.map_some] using lists
  simpa using listResult _ _ mapped

private theorem execute_op (resolve : Resolver) (env : Environment) (x : Op .optimization) (y : Op .execution)
    (h : x.execute env = some y) : observeOp resolve env y = observeOp resolve env x := by
  cases hc : x.code.execute env with
  | none => simp [Op.execute, hc] at h
  | some code =>
    simp [Op.execute, hc] at h
    subst y
    simp only [observeOp]
    rw [show (fun vs => denote env code vs resolve) = (fun vs => denote env x.code vs resolve) from
      funext fun args => execute_denote_with resolve env _ _ args hc]

private theorem execute_block (resolve : Resolver) (env : Environment) (x : Block .optimization) (y : Block .execution)
    (h : x.execute env = some y) : observeBlock resolve env y = observeBlock resolve env x := by
  cases ho : x.ops.mapM (Op.execute env) with
  | none => simp [Block.execute, ho] at h
  | some ops =>
    simp [Block.execute, ho] at h
    subst y
    simp [observeBlock, mapM_observes _ _ _ (execute_op resolve env) _ _ ho]

/-- For every successfully converted finite function and all arguments, Opt
and Exec return the same value or the same failure. This includes joins and
non-taken branches, without assuming that a particular sample was run. -/
theorem execute_run_with (resolve : Resolver) (env : Environment) (f : MidIR.Function .optimization)
    (out : MidIR.Function .execution) (h : f.execute env = some out) (args : List Value) :
    runWith env out resolve args = runWith env f resolve args := by
  simp only [MidIR.Function.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, blocks, hb, _, _, ho⟩ := h
  cases Option.some.inj ho
  simp [runWith, mapM_observes _ _ _ (execute_block resolve env) _ _ hb]

theorem execute_run (env : Environment) (f : MidIR.Function .optimization)
    (out : MidIR.Function .execution) (h : f.execute env = some out) (args : List Value) :
    run env out args = run env f args := execute_run_with _ env f out h args

/-- The observable identity and signature stay attached to the computation
when the array of functions is transformed. This projection observes functions in isolation. -/
structure FunctionObservation where
  family : Namespace.FunctionId
  specialization : FunctionSource.Compiler.Key
  coreId : Nat
  params : Array VastitasKernel.MidIR.Ty
  result : VastitasKernel.MidIR.Ty
  apply : List Value → Option Value

def observeFunction {p : Phase} (env : Environment) (f : MidIR.Function p) : FunctionObservation :=
  ⟨f.id, f.specialization, f.coreId, f.params, f.result, run env f⟩

private theorem execute_function (env : Environment) (x : MidIR.Function .optimization)
    (y : MidIR.Function .execution) (h : x.execute env = some y) :
    observeFunction env y = observeFunction env x := by
  have hr := funext (execute_run env x y h)
  simp only [MidIR.Function.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, ho⟩ := h
  cases Option.some.inj ho
  simp [observeFunction, hr]

/-- Every admitted array of singleton functions retains the complete revision,
nominal declarations, entry, function order, identities and results. -/
theorem execute_module (x : Module .optimization) (y : Module .execution)
    (h : x.execute = some y) :
    y.revision = x.revision ∧ y.env = x.env ∧ y.entry = x.entry ∧
    y.functions.map (observeFunction y.env) = x.functions.map (observeFunction x.env) := by
  simp only [Module.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, functions, hfs, ho⟩ := h
  cases Option.some.inj ho
  exact ⟨rfl, rfl, rfl, mapM_observes _ _ _ (execute_function x.env) _ _ hfs⟩

private def linked {p : Phase} (env : Environment) (resolve : Resolver) (f : MidIR.Function p) :=
  (f.target, runWith env f resolve)

private theorem execute_link (resolve : Resolver) (env : Environment) (x : MidIR.Function .optimization)
    (y : MidIR.Function .execution) (h : x.execute env = some y) :
    linked env resolve y = linked env resolve x := by
  have result := funext (execute_run_with resolve env x y h)
  simp only [MidIR.Function.execute, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, _, _, _, _, ho⟩ := h
  cases Option.some.inj ho
  simp [linked, result, MidIR.Function.target]

private def applyLinked (symbols : Array (CallTarget × (List Value → Option Value))) : Resolver :=
  fun target args => do
    let (selected, apply) ← symbols[target.symbol]?
    guard (decide (selected = target))
    apply args

private theorem invoke_succ {p : Phase} (m : Module p) (depth : Nat) :
    invoke m (depth + 1) = applyLinked (m.functions.map (linked m.env (invoke m depth))) := by
  funext target args
  cases hs : m.functions[target.symbol]? <;> simp [invoke, applyLinked, Array.getElem?_map, hs, linked]

/-- For any fuel, target and argument list, Opt and Exec agree on resolved
calls throughout the module, including missing symbols and ABI mismatches. -/
theorem execute_invoke (x : Module .optimization) (y : Module .execution)
    (h : x.execute = some y) (depth : Nat) : invoke y depth = invoke x depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
    rw [invoke_succ y, invoke_succ x, ih]
    apply congrArg applyLinked
    simp only [Module.execute, bind, Option.bind_eq_some_iff] at h
    obtain ⟨_, _, fs, mapped, ho⟩ := h
    cases Option.some.inj ho
    exact mapM_observes _ _ _ (execute_link _ x.env) _ _ mapped

end VastitasOracle.MidIR
