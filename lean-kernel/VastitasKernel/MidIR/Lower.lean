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
    let code ← liftM (match op with
      | .and => some Opcode.boolAnd
      | .or => some Opcode.boolOr
      | .eq => (Ty.ofCore left.result.type).map (.compare .eq ·)
      | .ne => (Ty.ofCore left.result.type).map (.compare .ne ·)
      | _ => (ExactOp.binary op left.result.type right.result.type).map .exactOp)
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

/-- Full modules keep the original dense Core symbol numbers. -/
def lowerFunction (env : Environment) (origin : FunctionSource.Compiler.Key)
    (f : Core.Function) (targets : Array CallTarget := #[]) : Option (Function .optimization) :=
  lowerLinkedFunction env origin f fun id => do
    let t ← targets[id]?
    guard (t.symbol == id)
    return t

end VastitasKernel.MidIR
