import VastitasKernel.MidIR.Check
import VastitasKernel.MidIR.ExactFold
import VastitasKernel.MidIR.Literal

set_option autoImplicit false

namespace VastitasKernel.MidIR
open Indexed

private structure Draft where
  params : Array Ty
  ops : Array (Op .optimization) := #[]
  terminator : Option Terminator := none

private abbrev Builder := StateT (Array Draft) Option

private def newBlock (params : Array Ty) : Builder Nat := do
  let blocks ← get
  set (blocks.push { params })
  return blocks.size

private def active : Builder Nat := do
  let blocks ← get
  guard (!blocks.isEmpty)
  return blocks.size - 1

private def finishBlock (i : Nat) (term : Terminator) : Builder Unit := do
  let blocks ← get
  let b ← liftM (blocks[i]?)
  guard b.terminator.isNone
  set (blocks.set! i { b with terminator := some term })

private def emit (code : Opcode .optimization) (args : List Ref) : Builder Ref := do
  let blocks ← get
  let i ← active
  let b ← liftM (blocks[i]?)
  guard b.terminator.isNone
  set (blocks.set! i { b with ops := b.ops.push ⟨code, args⟩ })
  return ⟨i, b.params.size + b.ops.size⟩

/-- The static operand types choose an instruction only after literal folding. -/
def binaryCode {phase : Phase} (op : BinaryOp) (left right : Core.DataType) : Option (Opcode phase) :=
  match op with
  | .and => some Opcode.boolAnd
  | .or => some Opcode.boolOr
  | .eq => (Ty.ofCore left).map (.compare .eq ·)
  | .ne => (Ty.ofCore left).map (.compare .ne ·)
  | .lt => (Ty.ofCore left).map (.compare .lt ·)
  | .le => (Ty.ofCore left).map (.compare .le ·)
  | .gt => (Ty.ofCore left).map (.compare .gt ·)
  | .ge => (Ty.ofCore left).map (.compare .ge ·)
  | _ => (ExactOp.binary op left right).map .exactOp

mutual
private def lowerTerm (resolve : Nat → Option CallTarget) (ctx : List (Nat × Ref)) : Core.Term → Builder Ref
  | .finiteLookup site symbols => do
    let refs ← liftM (symbols.mapM (fun symbol => ctx.lookup symbol))
    emit (.lookupTag site) refs
  | .call id arguments [] annotation => do
    let target ← liftM (resolve id)
    guard (annotation.reference.isNone && Ty.ofCore annotation.type == some target.result)
    let refs ← lowerArguments resolve ctx arguments
    emit (.call target) refs
  | .finiteTag c tag => emit (.finiteTag c tag) []
  | .unit => emit .unit []
  | .boolean b => emit (.boolean b) []
  | .unary .not arg _ => do emit .boolNot [← lowerTerm resolve ctx arg]
  | .natural n => emit (.natural n) []
  | .integer n => emit (.integer n) []
  | .unary .neg arg ann => do
    if let some ⟨literal, _⟩ := IntLiteral.inspect (.unary .neg arg ann) then
      emit (.integer literal.value) []
    else emit (.exactOp .neg) [← lowerTerm resolve ctx arg]
  | .pair element first second => do
    let left ← lowerTerm resolve ctx first
    let right ← lowerTerm resolve ctx second
    emit (.exactOp (.pair element)) [left, right]
  | .project element first arg => do
    emit (.exactOp (.project element first)) [← lowerTerm resolve ctx arg]
  | .natToInt arg => do emit (.exactOp .natToInt) [← lowerTerm resolve ctx arg]
  | .variable symbol _ => liftM (ctx.lookup symbol)
  | .scope body => lowerTerm resolve ctx body
  | .ascribe t body => do
    guard (t == body.result.type)
    lowerTerm resolve ctx body
  | .letE symbol rhs body => do
    let x ← lowerTerm resolve ctx rhs
    lowerTerm resolve ((symbol, x) :: ctx) body
  | .binary op left right _ => do
    if let some value := ExactFold.literalComparison op left right then
      return ← emit (.boolean value) []
    let code ← liftM (binaryCode op left.result.type right.result.type)
    let l ← lowerTerm resolve ctx left
    let r ← lowerTerm resolve ctx right
    emit code [l, r]
  | .branch cond yes no result => do
    let t ← liftM (Ty.ofCore result.type)
    let choice ← lowerTerm resolve ctx cond
    let origin ← active
    let yesStart ← newBlock #[]
    let y ← lowerTerm resolve ctx yes
    let yesEnd ← active
    let noStart ← newBlock #[]
    let n ← lowerTerm resolve ctx no
    let noEnd ← active
    let joinId ← newBlock #[t]
    finishBlock origin (.branch choice ⟨yesStart, ⟨origin⟩, []⟩ ⟨noStart, ⟨origin⟩, []⟩)
    finishBlock yesEnd (.jump ⟨joinId, ⟨yesEnd⟩, [y]⟩)
    finishBlock noEnd (.jump ⟨joinId, ⟨noEnd⟩, [n]⟩)
    return ⟨joinId, 0⟩
  | _ => failure

private def lowerArguments (resolve : Nat → Option CallTarget) (ctx : List (Nat × Ref)) :
    List Core.Term → Builder (List Ref)
  | [] => pure []
  | arg :: rest => do
    let ref ← lowerTerm resolve ctx arg
    return ref :: (← lowerArguments resolve ctx rest)
end

private theorem lower_literal_action (lit : Literal) (resolve : Nat → Option CallTarget) (ctx : List (Nat × Ref)) :
    lowerTerm resolve ctx lit.term = emit (lit.opcode .optimization) [] := by
  cases lit <;> rfl

/-- The production builder appends one nullary instruction to the live block
and returns its SSA slot. All preceding blocks and instructions are preserved. -/
def AppendsNullary (term : Core.Term) (code : Opcode .optimization) : Prop :=
  ∀ resolve ctx (prior : Array Draft) (params : Array Ty) (prefixOps : Array (Op .optimization)),
    (lowerTerm resolve ctx term).run (prior.push {params, ops := prefixOps}) =
      some (⟨prior.size, params.size + prefixOps.size⟩,
        prior.push {params, ops := prefixOps.push ⟨code, []⟩})

private theorem emit_live (code : Opcode .optimization) (args : List Ref) (prior : Array Draft)
    (params : Array Ty) (prefixOps : Array (Op .optimization)) :
    (emit code args).run (prior.push {params, ops := prefixOps}) =
      some (⟨prior.size, params.size + prefixOps.size⟩,
        prior.push {params, ops := prefixOps.push ⟨code, args⟩}) := by
  simp [emit, active, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, guard, StateT.pure, liftM, monadLift, MonadLift.monadLift, StateT.lift,
    set, StateT.set, Array.set!, Array.setIfInBounds, Array.set_push]

private theorem appends_nullary {term code}
    (lower : ∀ resolve ctx, lowerTerm resolve ctx term = emit code []) : AppendsNullary term code := by
  intro resolve ctx prior params prefixOps
  rw [lower resolve ctx]
  exact emit_live _ _ _ _ _

def AppendsLiteral (lit : Literal) : Prop := AppendsNullary lit.term (lit.opcode .optimization)

theorem appends_literal (lit : Literal) : AppendsLiteral lit :=
  appends_nullary (lower_literal_action lit)

theorem appends_finite_tag (carrier : FiniteSort) (tag : String) :
    AppendsNullary (.finiteTag carrier tag) (.finiteTag carrier tag) :=
  appends_nullary (fun _ _ => rfl)

/-- The name of this opcode is shared by every nominal carrier and Hom fiber.
The opcode itself carries the actual sort and tag. -/
def finiteTagRegistryRow : Lean.Name × String := (``Core.Term.finiteTag, "finite.tag.v1")

/-- Read every Core symbol in order. Missing symbols fail before emission.
The successful instruction contains exactly the resolved SSA references. -/
def AppendsLookup (site : FiniteLookup) (symbols : List Nat) : Prop :=
  ∀ resolve (ctx : List (Nat × Ref)) (prior : Array Draft) (params : Array Ty) (prefixOps : Array (Op .optimization)),
    (lowerTerm resolve ctx (.finiteLookup site symbols)).run (prior.push {params, ops := prefixOps}) =
      (symbols.mapM (fun sym => ctx.lookup sym)).map fun args =>
        (⟨prior.size, params.size + prefixOps.size⟩,
          prior.push {params, ops := prefixOps.push ⟨.lookupTag site, args⟩})

theorem appends_lookup (site : FiniteLookup) (symbols : List Nat) : AppendsLookup site symbols := by
  intro resolve ctx prior params prefixOps
  change ((do let refs ← liftM (symbols.mapM (fun sym => ctx.lookup sym)); emit (.lookupTag site) refs) : Builder Ref).run _ = _
  cases found : symbols.mapM (fun sym => ctx.lookup sym) with
  | none => rfl
  | some args => exact emit_live _ _ _ _ _

def lookupRegistryRow : Lean.Name × String := (``Core.Term.finiteLookup, "finite.lookup.tag.v1")

private theorem lowerArguments_in_order (resolve : Nat → Option CallTarget) (ctx : List (Nat × Ref))
    (terms : List Core.Term) :
    lowerArguments resolve ctx terms = terms.mapM (lowerTerm resolve ctx) := by
  induction terms with
  | nil => rfl
  | cons arg rest ih => simp [lowerArguments, List.mapM_cons, ih]

/-- Lower two operands left to right. Both operand actions may create
blocks. Only the live exit of the second operand receives the instruction. -/
def AppendsOperands (term left right : Core.Term) (code : Opcode .optimization) : Prop :=
  ∀ resolve ctx blocks,
    (lowerTerm resolve ctx term).run blocks =
      (do let (a, intermediate) ← (lowerTerm resolve ctx left).run blocks
          let (b, after) ← (lowerTerm resolve ctx right).run intermediate
          (emit code [a,b]).run after) ∧
    ∀ a intermediate b (prior : Array Draft) (params : Array Ty) (ops : Array (Op .optimization)),
      (lowerTerm resolve ctx left).run blocks = some (a, intermediate) →
      (lowerTerm resolve ctx right).run intermediate = some (b, prior.push {params, ops}) →
      (lowerTerm resolve ctx term).run blocks =
        some (⟨prior.size, params.size + ops.size⟩,
          prior.push {params, ops := ops.push ⟨code, [a,b]⟩})

private theorem appends_operands {term left right : Core.Term} {code : Opcode .optimization}
    (equation : ∀ resolve ctx, lowerTerm resolve ctx term =
      (do let a ← lowerTerm resolve ctx left
          let b ← lowerTerm resolve ctx right
          emit code [a,b])) : AppendsOperands term left right code := by
  intro resolve ctx blocks
  rw [equation]
  constructor
  · rfl
  · intro a intermediate b prior params ops first second
    change ((lowerTerm resolve ctx left).run blocks >>= fun (x, state) =>
      (lowerTerm resolve ctx right).run state >>= fun (y, after) =>
        (emit code [x,y]).run after) = _
    rw [first]
    change ((lowerTerm resolve ctx right).run intermediate >>= fun (y, after) =>
      (emit code [a,y]).run after) = _
    rw [second]
    exact emit_live _ _ _ _ _

abbrev AppendsPair (element : PairElem) (left right : Core.Term) :=
  AppendsOperands (.pair element left right) left right (.exactOp (.pair element))

theorem appends_pair (element : PairElem) (left right : Core.Term) : AppendsPair element left right :=
  appends_operands (fun _ _ => rfl)

/-- Lower an operand once and append one operation at its live exit, including
when the operand introduces control flow. -/
def AppendsOperand (term arg : Core.Term) (code : Opcode .optimization) : Prop :=
  ∀ resolve ctx blocks,
    (lowerTerm resolve ctx term).run blocks =
      (do let (ref, after) ← (lowerTerm resolve ctx arg).run blocks
          (emit code [ref]).run after) ∧
    ∀ ref (prior : Array Draft) (params : Array Ty) (ops : Array (Op .optimization)),
      (lowerTerm resolve ctx arg).run blocks = some (ref, prior.push {params, ops}) →
      (lowerTerm resolve ctx term).run blocks =
        some (⟨prior.size, params.size + ops.size⟩,
          prior.push {params, ops := ops.push ⟨code, [ref]⟩})

private theorem appends_operand {term arg : Core.Term} {code : Opcode .optimization}
    (action : ∀ resolve ctx, lowerTerm resolve ctx term = (do emit code [← lowerTerm resolve ctx arg])) :
    AppendsOperand term arg code := by
  intro resolve ctx blocks
  rw [action]
  refine ⟨rfl, ?_⟩
  intro ref prior params ops lowered
  change ((lowerTerm resolve ctx arg).run blocks >>= fun (r, after) => (emit code [r]).run after) = _
  rw [lowered]
  exact emit_live _ _ _ _ _

/-- The binary constructor has three routes. Fold an exact comparison of literals,
emit the statically selected opcode after evaluating both operands, or reject. -/
def LowersBinary (op : BinaryOp) (left right : Core.Term) (result : Core.Result) : Prop :=
  let term := Core.Term.binary op left right result
  match ExactFold.literalComparison op left right with
  | some answer => AppendsNullary term (.boolean answer)
  | none =>
    match binaryCode (phase := .optimization) op left.result.type right.result.type with
    | some code => AppendsOperands term left right code
    | none => ∀ resolve ctx blocks, (lowerTerm resolve ctx term).run blocks = none

theorem lowers_binary (op : BinaryOp) (left right : Core.Term) (result : Core.Result) :
    LowersBinary op left right result := by
  unfold LowersBinary
  dsimp only
  cases folded : ExactFold.literalComparison op left right with
  | some answer =>
    intro resolve ctx prior params ops
    rw [lowerTerm, folded]
    exact emit_live _ _ _ _ _
  | none =>
    cases selected : binaryCode (phase := .optimization) op left.result.type right.result.type with
    | some code =>
      apply appends_operands
      intro resolve ctx
      rw [lowerTerm, folded, selected]
      rfl
    | none =>
      intro resolve ctx blocks
      rw [lowerTerm, folded, selected]
      rfl

def unaryCode (phase : Phase) : UnaryOp → Opcode phase
  | .not => .boolNot
  | .neg => .exactOp .neg

def unaryType : UnaryOp → VastitasKernel.MidIR.Ty
  | .not => .bool
  | .neg => .int

def unaryParameter (op : UnaryOp) : Core.Result :=
  ⟨match op with | .not => .pure .bool | .neg => .pure .int, none⟩

/-- Boolean negation always lowers its operand. Integer negation has an
additional path for an exact signed literal with the required Core result. -/
def LowersUnary (op : UnaryOp) (arg : Core.Term) (result : Core.Result) : Prop :=
  match op with
  | .not => AppendsOperand (.unary .not arg result) arg .boolNot
  | .neg =>
    match IntLiteral.inspect (.unary .neg arg result) with
    | some ⟨lit, _⟩ => AppendsNullary (.unary .neg arg result) (.integer lit.value)
    | none => AppendsOperand (.unary .neg arg result) arg (.exactOp .neg)

theorem lowers_unary (op : UnaryOp) (arg : Core.Term) (result : Core.Result) : LowersUnary op arg result := by
  cases op with
  | not => exact appends_operand (fun _ _ => rfl)
  | neg =>
    unfold LowersUnary
    cases literal : IntLiteral.inspect (.unary .neg arg result) with
    | none =>
      apply appends_operand
      intro resolve ctx
      rw [lowerTerm]
      simp only [literal]
    | some witness =>
      obtain ⟨lit, _⟩ := witness
      apply appends_nullary
      intro resolve ctx
      rw [lowerTerm]
      simp only [literal]

/-- Project a field from the actual operand reference, preserving the element
type and the field selector when that operand introduces a join. -/
def AppendsProjection (element : PairElem) (first : Bool) (arg : Core.Term) : Prop :=
  AppendsOperand (.project element first arg) arg (.exactOp (.project element first))

theorem appends_projection (element : PairElem) (first : Bool) (arg : Core.Term) :
    AppendsProjection element first arg :=
  appends_operand (fun _ _ => rfl)

/-- The conversion evaluates its operand once, threading any blocks it
introduces. On a live exit it appends one instruction using the returned
reference. If lowering the operand fails, the entire action fails. -/
def AppendsNatToInt (arg : Core.Term) : Prop := AppendsOperand (.natToInt arg) arg (.exactOp .natToInt)

theorem appends_nat_to_int (arg : Core.Term) : AppendsNatToInt arg := appends_operand (fun _ _ => rfl)

def natToIntRegistryRow : Lean.Name × String := (``Core.Term.natToInt, "nat_to_int.v1")

/-- The call checks its resolved result and then threads the builder through
each actual argument in source order, including any blocks they introduce. -/
def LowersStaticCall (id : Nat) (terms : List Core.Term) (annotation : Core.Result) : Prop :=
  ∀ resolve ctx, lowerTerm resolve ctx (.call id terms [] annotation) = (do
    let target ← liftM (resolve id)
    guard (annotation.reference.isNone && Ty.ofCore annotation.type == some target.result)
    let refs ← terms.mapM (lowerTerm resolve ctx)
    emit (.call target) refs)

theorem lowers_static_call (id : Nat) (terms : List Core.Term) (annotation : Core.Result) :
    LowersStaticCall id terms annotation := by
  intro resolve ctx
  simp only [lowerTerm, lowerArguments_in_order]

/-- After argument evaluation, the call appends the exact target and ordered
references to the current live block and returns their instruction's slot. -/
def AppendsStaticCall (id : Nat) (terms : List Core.Term) (annotation : Core.Result) : Prop :=
  ∀ resolve ctx target blocks refs (prior : Array Draft) (params : Array Ty)
    (prefixOps : Array (Op .optimization)), resolve id = some target →
    (annotation.reference.isNone && Ty.ofCore annotation.type == some target.result) = true →
    (terms.mapM (lowerTerm resolve ctx)).run blocks = some (refs, prior.push {params, ops := prefixOps}) →
    (lowerTerm resolve ctx (.call id terms [] annotation)).run blocks =
      some (⟨prior.size, params.size + prefixOps.size⟩,
        prior.push {params, ops := prefixOps.push ⟨.call target, refs⟩})

theorem appends_static_call (id : Nat) (terms : List Core.Term) (annotation : Core.Result) :
    AppendsStaticCall id terms annotation := by
  intro resolve ctx target blocks refs prior params prefixOps found fits args
  rw [lowers_static_call id terms annotation resolve ctx]
  simp only [found, fits, StateT.run, bind, StateT.bind, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, Option.bind_some, guard, pure, StateT.pure,
    ↓reduceIte] at *
  rw [args]
  exact emit_live _ _ _ _ _

/-- Unsupported substitutions, missing targets and conflicting result
annotations reject at the call site before lowering any argument. -/
def RejectsStaticCall (id : Nat) (terms : List Core.Term) (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef))
    (annotation : Core.Result) : Prop :=
  ∀ resolve ctx blocks, (substitution ≠ [] ∨
    (resolve id).all (fun target => !(annotation.reference.isNone && Ty.ofCore annotation.type == some target.result))) →
    (lowerTerm resolve ctx (.call id terms substitution annotation)).run blocks = none

theorem rejects_static_call (id : Nat) (terms : List Core.Term) (substitution : List (Indexed.ObjectRef × Indexed.ObjectRef))
    (annotation : Core.Result) : RejectsStaticCall id terms substitution annotation := by
  intro resolve ctx blocks invalid
  cases substitution with
  | cons => rfl
  | nil =>
    cases found : resolve id with
    | none => simp [lowerTerm, found, StateT.run, bind, StateT.bind, liftM, monadLift,
        MonadLift.monadLift, StateT.lift]
    | some target =>
      rcases invalid with impossible | rejected
      · exact (impossible rfl).elim
      rw [found] at rejected
      change (!(annotation.reference.isNone && Ty.ofCore annotation.type == some target.result)) = true at rejected
      rw [Bool.not_eq_true'] at rejected
      rw [lowers_static_call id terms annotation resolve ctx]
      simp only [found]
      change ((do guard (annotation.reference.isNone && Ty.ofCore annotation.type == some target.result)
                  let refs ← terms.mapM (lowerTerm resolve ctx)
                  emit (.call target) refs) : Builder Ref).run blocks = none
      rw [rejected]
      rfl

def staticCallRegistryRow : Lean.Name × String := (``Core.Term.call, "static.call.v1")

/-- Variables reuse the defining SSA reference in every builder state. An
unbound symbol fails before changing any block. -/
def ReadsVariable (symbol : Nat) (result : Core.Result) : Prop :=
  ∀ resolve (ctx : List (Nat × Ref)) blocks,
    (lowerTerm resolve ctx (.variable symbol result)).run blocks =
      (ctx.lookup symbol).map fun ref => (ref, blocks)

theorem reads_variable (symbol : Nat) (result : Core.Result) : ReadsVariable symbol result := by
  intro resolve ctx blocks
  cases found : ctx.lookup symbol <;> simp [lowerTerm, found, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, StateT.run]

/-- A lexical scope forwards the entire child action, including failure and
changes to the active block inside the child. -/
def ForwardsScope (body : Core.Term) : Prop :=
  ∀ resolve ctx, lowerTerm resolve ctx (.scope body) = lowerTerm resolve ctx body

theorem forwards_scope (body : Core.Term) : ForwardsScope body := fun _ _ => rfl

/-- Ascription checks the exact Core type before forwarding the child. -/
def ChecksAscription (annotation : Core.DataType) (body : Core.Term) : Prop :=
  ∀ resolve ctx blocks, (lowerTerm resolve ctx (.ascribe annotation body)).run blocks =
    if annotation = body.result.type then (lowerTerm resolve ctx body).run blocks else none

theorem checks_ascription (annotation : Core.DataType) (body : Core.Term) :
    ChecksAscription annotation body := by
  intro resolve ctx blocks
  by_cases h : annotation = body.result.type <;>
    simp [lowerTerm, h, guard, bind, StateT.run, StateT.bind, pure, StateT.pure,
      failure, Alternative.failure, StateT.failure]

/-- Lower the initializer once and pass its returned SSA reference and updated
blocks to the body. Failure of either action propagates. -/
def BindsLet (symbol : Nat) (rhs body : Core.Term) : Prop :=
  ∀ resolve ctx blocks, (lowerTerm resolve ctx (.letE symbol rhs body)).run blocks =
    (do let (ref, after) ← (lowerTerm resolve ctx rhs).run blocks
        (lowerTerm resolve ((symbol, ref) :: ctx) body).run after)

theorem binds_let (symbol : Nat) (rhs body : Core.Term) : BindsLet symbol rhs body :=
  fun _ _ _ => rfl

/-- Each child may end in a different block from the one where it started.
The branch uses those actual exits as predecessors and forwards their result
references to the single typed join parameter. -/
def JoinsBranches (condition yes no : Core.Term) (result : Core.Result) : Prop :=
  ∀ resolve ctx blocks type choice y n
      (cPrefix yPrefix nPrefix : Array Draft) (cLast yLast nLast : Draft),
    Ty.ofCore result.type = some type →
    (lowerTerm resolve ctx condition).run blocks = some (choice, cPrefix.push cLast) →
    (lowerTerm resolve ctx yes).run ((cPrefix.push cLast).push {params := #[]}) = some (y, yPrefix.push yLast) →
    (lowerTerm resolve ctx no).run ((yPrefix.push yLast).push {params := #[]}) = some (n, nPrefix.push nLast) →
    let joinId := nPrefix.size + 1
    (lowerTerm resolve ctx (.branch condition yes no result)).run blocks =
      (do finishBlock cPrefix.size (.branch choice
            ⟨cPrefix.size + 1, ⟨cPrefix.size⟩, []⟩ ⟨yPrefix.size + 1, ⟨cPrefix.size⟩, []⟩)
          finishBlock yPrefix.size (.jump ⟨joinId, ⟨yPrefix.size⟩, [y]⟩)
          finishBlock nPrefix.size (.jump ⟨joinId, ⟨nPrefix.size⟩, [n]⟩)
          pure (⟨joinId, 0⟩ : Ref)).run ((nPrefix.push nLast).push {params := #[type]})

private theorem active_push (pre : Array Draft) (last : Draft) :
    active.run (pre.push last) = some (pre.size, pre.push last) := by
  simp [active, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, guard, StateT.pure]

private theorem runBind {α β : Type} (a : Builder α) (b : α → Builder β) (blocks : Array Draft) :
    (a >>= b).run blocks = ((a.run blocks).bind fun (v, state) => (b v).run state) := rfl

private theorem runNew (params : Array Ty) (blocks : Array Draft) :
    (newBlock params).run blocks = some (blocks.size, blocks.push {params}) := rfl

private theorem runLift {α : Type} (x : Option α) (blocks : Array Draft) :
    (liftM x : Builder α).run blocks = x.map (fun v => (v, blocks)) := by cases x <;> rfl

theorem joins_branches (condition yes no : Core.Term) (result : Core.Result) :
    JoinsBranches condition yes no result := by
  intro resolve ctx blocks type choice y n cp yp np cl yl nl htype hc hy hn
  dsimp only
  rw [lowerTerm]
  simp only [runBind, runLift, htype, Option.map_some, Option.bind_some, hc, hy, hn,
    active_push, runNew, Array.size_push]

/-- Both arm actions must compile even for a statically known condition. A
failure before the join is propagated without a partial function. -/
def ChecksBothArms (condition yes no : Core.Term) (result : Core.Result) : Prop :=
  ∀ resolve ctx blocks type choice (cp : Array Draft) (cl : Draft),
    Ty.ofCore result.type = some type →
    (lowerTerm resolve ctx condition).run blocks = some (choice, cp.push cl) →
    let yesBlocks := (cp.push cl).push {params := #[]}
    let whole := (lowerTerm resolve ctx (.branch condition yes no result)).run blocks
    ((lowerTerm resolve ctx yes).run yesBlocks = none → whole = none) ∧
    ∀ y (yp : Array Draft) (yl : Draft),
      (lowerTerm resolve ctx yes).run yesBlocks = some (y, yp.push yl) →
      (lowerTerm resolve ctx no).run ((yp.push yl).push {params := #[]}) = none → whole = none

theorem checks_both_arms (condition yes no : Core.Term) (result : Core.Result) :
    ChecksBothArms condition yes no result := by
  intro resolve ctx blocks type choice cp cl htype hc
  dsimp only
  constructor
  · intro hy
    rw [lowerTerm]
    simp only [runBind, runLift, htype, Option.map_some, Option.bind_some, hc, active_push, runNew, hy, Option.bind_none]
  · intro y yp yl hy hn
    rw [lowerTerm]
    simp only [runBind, runLift, htype, Option.map_some, Option.bind_some, hc, active_push, runNew, hy, hn, Option.bind_none]

/-- Structural lowering of one exact body. Acceptance of a source module and
its family identities belongs to the checked request adapter in MidIR.Checked. -/
def lowerLinkedFunction (env : Environment) (origin : FunctionSource.Compiler.Key)
    (f : Core.Function) (resolve : Nat → Option CallTarget) : Option (Function .optimization) := do
  let params ← f.parameters.mapM fun param => Ty.ofCore param.result.type
  let result ← Ty.ofCore f.returnType
  let folded := if params.isEmpty && result == .int then ExactFold.integer f.body else none
  let blocks : Array (Block .optimization) ← match folded with
    | some ⟨n, _⟩ => pure #[(IntLiteral.integer n).block .optimization]
    | none => do
      let ctx := f.parameters.zipIdx.map fun (param, i) => (param.symbol, ⟨0, i⟩)
      let (value, drafts) ← (lowerTerm resolve ctx f.body).run #[{ params := params.toArray }]
      let last := drafts.size - 1
      let (_, drafts) ← (finishBlock last (.ret ⟨last⟩ value)).run drafts
      drafts.mapM fun d => do return ⟨d.params, d.ops, ← d.terminator⟩
  let out : Function .optimization := {
    id := ⟨f.definition⟩, coreId := f.id, specialization := origin
    params := params.toArray, result, blocks }
  guard (validFunction env out)
  return out

/-- Complete lowering of the explicit conversion in a one-parameter method.
The selected definition, local symbol and specialization carry through the
ordinary function compiler and its SSA validator. -/
theorem lower_nat_to_int_parameter (env : Environment) (key : FunctionSource.Compiler.Key)
    (id : Nat) (owner : Namespace.Owner) (symbol : Nat) (span : Span) (resolve : Nat → Option CallTarget) :
    let ann : Core.Result := ⟨.pure .nat, none⟩
    let body := Core.Term.scope (.natToInt (.variable symbol ann))
    lowerLinkedFunction env key ⟨id, owner, [⟨symbol, ann⟩], .pure .int, body, span⟩ resolve =
      some ⟨⟨owner⟩, id, key, #[.nat], .int,
        #[⟨#[.nat], #[⟨.exactOp .natToInt, [⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩ := by
  dsimp only
  let ann : Core.Result := ⟨.pure .nat, none⟩
  let ctx : List (Nat × Ref) := [(symbol, ⟨0,0⟩)]
  let start : Array Draft := #[{params := #[.nat]}]
  have arg : (lowerTerm resolve ctx (.variable symbol ann)).run start = some (⟨0,0⟩, start) := by
    rw [reads_variable symbol ann resolve ctx start]
    simp [ctx]
  have step := (appends_nat_to_int (.variable symbol ann) resolve ctx start).2
    ⟨0,0⟩ #[] #[.nat] #[] arg
  simp [lowerLinkedFunction, Ty.ofCore]
  rw [forwards_scope (.natToInt (.variable symbol ann)) resolve ctx, step]
  set_option maxRecDepth 8192 in
    with_unfolding_all rfl

/-- A method projecting a field of its pair parameter lowers to one
instruction even when reached through an assembled specialization. -/
theorem lower_project_parameter (env : Environment) (key : FunctionSource.Compiler.Key)
    (id : Nat) (owner : Namespace.Owner) (symbol : Nat) (span : Span) (resolve : Nat → Option CallTarget)
    (e : PairElem) (first : Bool) :
    let ann : Core.Result := ⟨.pure (.pair e), none⟩
    let projection := Core.Term.project e first (.variable symbol ann)
    lowerLinkedFunction env key ⟨id, owner, [⟨symbol, ann⟩], projection.result.type, .scope projection, span⟩ resolve =
      some ⟨⟨owner⟩, id, key, #[.pair e], pairScalar e,
        #[⟨#[.pair e], #[⟨.exactOp (.project e first), [⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩ := by
  dsimp only
  let ann : Core.Result := ⟨.pure (.pair e), none⟩
  let ctx : List (Nat × Ref) := [(symbol, ⟨0,0⟩)]
  let start : Array Draft := #[{params := #[.pair e]}]
  have arg : (lowerTerm resolve ctx (.variable symbol ann)).run start = some (⟨0,0⟩, start) := by
    rw [reads_variable symbol ann resolve ctx start]
    simp [ctx]
  have step := (appends_projection e first (.variable symbol ann) resolve ctx start).2
    ⟨0,0⟩ #[] #[.pair e] #[] arg
  simp [lowerLinkedFunction, Ty.ofCore]
  rw [forwards_scope (.project e first (.variable symbol ann)) resolve ctx, step]
  set_option maxRecDepth 8192 in
    cases e <;> cases first <;> with_unfolding_all rfl

/-- A checked one-parameter Boolean or integer negation keeps its dense target
and specialization. The operand is a parameter, so it always remains a runtime operation. -/
theorem lower_unary_parameter (env : Environment) (key : FunctionSource.Compiler.Key)
    (id : Nat) (owner : Namespace.Owner) (symbol : Nat) (span : Span) (resolve : Nat → Option CallTarget)
    (op : UnaryOp) :
    let ann := unaryParameter op
    let body := Core.Term.unary op (.variable symbol ann) ann
    lowerLinkedFunction env key ⟨id, owner, [⟨symbol, ann⟩], ann.type, .scope body, span⟩ resolve =
      some ⟨⟨owner⟩, id, key, #[unaryType op], unaryType op,
        #[⟨#[unaryType op], #[⟨unaryCode .optimization op, [⟨0,0⟩]⟩], .ret ⟨0⟩ ⟨0,1⟩⟩]⟩ := by
  dsimp only
  let ann := unaryParameter op
  let ctx : List (Nat × Ref) := [(symbol, ⟨0,0⟩)]
  let start : Array Draft := #[{params := #[unaryType op]}]
  have arg : (lowerTerm resolve ctx (.variable symbol ann)).run start = some (⟨0,0⟩, start) := by
    rw [reads_variable symbol ann resolve ctx start]
    simp [ctx]
  have append : AppendsOperand (.unary op (.variable symbol ann) ann) (.variable symbol ann)
      (unaryCode .optimization op) := by
    cases op with
    | neg => exact lowers_unary .neg (.variable symbol ann) ann
    | not => exact lowers_unary .not (.variable symbol ann) ann
  have step := (append resolve ctx start).2 ⟨0,0⟩ #[] #[unaryType op] #[] arg
  have type : Ty.ofCore (unaryParameter op).type = some (unaryType op) := by cases op <;> rfl
  simp [lowerLinkedFunction, type]
  rw [forwards_scope, step]
  set_option maxRecDepth 8192 in
    cases op <;> with_unfolding_all rfl

/-- The incoming integer on each edge is a different entry slot, even though
the two parameters have identical types. Both jump to one typed join. -/
def parameterBranch (p : Phase) : Array (Block p) := #[
  ⟨#[.bool, .int, .int], #[], .branch ⟨0,0⟩ ⟨1,⟨0⟩,[]⟩ ⟨2,⟨0⟩,[]⟩⟩,
  ⟨#[], #[], .jump ⟨3,⟨1⟩,[⟨0,1⟩]⟩⟩,
  ⟨#[], #[], .jump ⟨3,⟨2⟩,[⟨0,2⟩]⟩⟩,
  ⟨#[.int], #[], .ret ⟨3⟩ ⟨3,0⟩⟩]

/-- Elaboration gives each arm of a written integer conditional a scope and a
checked result ascription, including an arm that just returns a parameter. -/
def scopedIntParameter (symbol : Nat) : Core.Term :=
  let ann : Core.Result := ⟨.pure .int, none⟩
  .ascribe ann.type (.scope (.variable symbol ann))

private theorem read_scoped_int_parameter (symbol : Nat) (resolve : Nat → Option CallTarget)
    (ctx : List (Nat × Ref)) (blocks : Array Draft) :
    (lowerTerm resolve ctx (scopedIntParameter symbol)).run blocks =
      (ctx.lookup symbol).map fun ref => (ref, blocks) := by
  unfold scopedIntParameter
  rw [checks_ascription]
  change (lowerTerm resolve ctx (.scope (.variable symbol ⟨.pure .int, none⟩))).run blocks = _
  rw [forwards_scope, reads_variable]

set_option maxHeartbeats 400000 in
theorem lower_parameter_branch (env : Environment) (key : FunctionSource.Compiler.Key)
    (id : Nat) (owner : Namespace.Owner) (c y n : Nat) (span : Span) (resolve : Nat → Option CallTarget)
    (cy : c ≠ y) (cn : c ≠ n) (yn : y ≠ n) :
    let bool : Core.Result := ⟨.pure .bool, none⟩
    let int : Core.Result := ⟨.pure .int, none⟩
    let body := Core.Term.branch (.variable c bool) (scopedIntParameter y) (scopedIntParameter n) int
    lowerLinkedFunction env key ⟨id, owner, [⟨c,bool⟩,⟨y,int⟩,⟨n,int⟩], int.type, .scope body, span⟩ resolve =
      some ⟨⟨owner⟩, id, key, #[.bool,.int,.int], .int, parameterBranch .optimization⟩ := by
  dsimp only
  let bool : Core.Result := ⟨.pure .bool, none⟩
  let int : Core.Result := ⟨.pure .int, none⟩
  let ctx : List (Nat × Ref) := [(c,⟨0,0⟩),(y,⟨0,1⟩),(n,⟨0,2⟩)]
  let entry : Draft := {params := #[.bool,.int,.int]}
  let arm : Draft := {params := #[]}
  have choice : (lowerTerm resolve ctx (.variable c bool)).run #[entry] = some (⟨0,0⟩, #[entry]) := by
    rw [reads_variable c bool resolve ctx #[entry]]
    simp [ctx]
  have onYes : (lowerTerm resolve ctx (scopedIntParameter y)).run #[entry,arm] = some (⟨0,1⟩, #[entry,arm]) := by
    rw [read_scoped_int_parameter y resolve ctx #[entry,arm]]
    simp [ctx, List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm cy)]
  have onNo : (lowerTerm resolve ctx (scopedIntParameter n)).run #[entry,arm,arm] = some (⟨0,2⟩, #[entry,arm,arm]) := by
    rw [read_scoped_int_parameter n resolve ctx #[entry,arm,arm]]
    simp [ctx, List.lookup, beq_eq_false_iff_ne.mpr (Ne.symm cn), beq_eq_false_iff_ne.mpr (Ne.symm yn)]
  have step := joins_branches (.variable c bool) (scopedIntParameter y) (scopedIntParameter n) int
    resolve ctx #[entry] .int ⟨0,0⟩ ⟨0,1⟩ ⟨0,2⟩ #[] #[entry] #[entry,arm] entry arm arm rfl choice onYes onNo
  simp [lowerLinkedFunction, Ty.ofCore]
  rw [forwards_scope _ resolve ctx]
  let branch := Terminator.branch ⟨0,0⟩ ⟨1,⟨0⟩,[]⟩ ⟨2,⟨0⟩,[]⟩
  let left := Terminator.jump ⟨3,⟨1⟩,[⟨0,1⟩]⟩
  let right := Terminator.jump ⟨3,⟨2⟩,[⟨0,2⟩]⟩
  let join : Draft := {params := #[.int]}
  let partialBlocks := #[{entry with terminator := branch}, {arm with terminator := left},
    {arm with terminator := right}, join]
  have ends : (lowerTerm resolve ctx (.branch (.variable c bool) (scopedIntParameter y) (scopedIntParameter n) int)).run #[entry] =
      some (⟨3,0⟩, partialBlocks) := by
    rw [step]
    rfl
  rw [ends]
  simp only [Option.bind_some]
  let ret := Terminator.ret ⟨3⟩ ⟨3,0⟩
  let closed := #[{entry with terminator := branch}, {arm with terminator := left},
    {arm with terminator := right}, {join with terminator := ret}]
  have last : (finishBlock (partialBlocks.size - 1) (.ret ⟨partialBlocks.size - 1⟩ ⟨3,0⟩)).run partialBlocks =
      some ((), closed) := rfl
  rw [last]
  simp only [Option.bind_some]
  have finalize : (closed.mapM fun d => d.terminator.bind fun t => some (⟨d.params, d.ops, t⟩ : Block .optimization)) =
      some (parameterBranch .optimization) := by
    with_unfolding_all rfl
  rw [finalize]
  simp only [Option.bind_some]
  let out : Function .optimization := ⟨⟨owner⟩, id, key, #[.bool,.int,.int], .int, parameterBranch .optimization⟩
  change (do guard (validFunction env out); pure out) = some out
  have valid : validFunction env out = true := by
    set_option maxRecDepth 8192 in
      with_unfolding_all rfl
  rw [valid]
  rfl

/-- Full modules keep the original dense Core symbol numbers. -/
def lowerFunction (env : Environment) (origin : FunctionSource.Compiler.Key)
    (f : Core.Function) (targets : Array CallTarget := #[]) : Option (Function .optimization) :=
  lowerLinkedFunction env origin f fun id => do
    let t ← targets[id]?
    guard (t.symbol == id)
    return t

end VastitasKernel.MidIR
