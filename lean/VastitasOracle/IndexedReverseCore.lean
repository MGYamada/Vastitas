import VastitasOracle.IndexedWire
import VastitasOracle.LegacySource
import VastitasOracle.ResourceCodegen

/-! The structure of compiled reverse Core (#623).

`Core.Reverse.validate` compares Core with the structural tests `termEq`,
`functionEq` and `moduleEq`. These are sound and reflexive, so validation holds
exactly when the generated module and the ledger are the result of
`Core.Reverse.generate` on the source module. The generated module keeps the
source declarations, adds the declarations of every entry, keeps `main` and
every source function header, and lists the generated function of every entry.
With the unique function and declaration ids of a checked module, the generated
function and every declaration of an entry are found by their ids.

`Core.Reverse.Compiled` carries this validation. Every public path that
generates code from a compiled module (protocols 2-7, and the pure program and
pure values of protocols 8/9) therefore uses the compilation of its executable
Core, and every function of it has typed, finite evaluation
(`IndexedProgramSafety`). These theorems concern checked Core. That a
generated function computes the reverse pass of its site is stated in
`SmoothReverseCore` and, for every entry of a compiled module, in
`SmoothReverseCompiled`; the generated text and native code are not covered. -/
namespace VastitasOracle.IndexedReverseCore
open VastitasKernel.Indexed.Core
open VastitasKernel.Indexed.Core.Reverse

/-! ## Structural equality -/

theorem termEq_sound {a b : Term} (equal : termEq a b = true) : a = b := by
  induction a using Term.rec (motive_2 := fun as => ∀ bs, termsEq as bs = true → as = bs)
    generalizing b with
  | natural x => cases b <;> simp_all [termEq]
  | integer x => cases b <;> simp_all [termEq]
  | boolean x => cases b <;> simp_all [termEq]
  | unit => cases b <;> simp_all [termEq]
  | «variable» s r => cases b <;> simp_all [termEq]
  | unary o x r ih =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, x'⟩, rfl⟩ := equal
    rw [ih x']
  | binary o x y r ihx ihy =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨⟨rfl, x'⟩, y'⟩, rfl⟩ := equal
    rw [ihx x', ihy y']
  | pair e x y ihx ihy =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, x'⟩, y'⟩ := equal
    rw [ihx x', ihy y']
  | project e f x ih =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, rfl⟩, x'⟩ := equal
    rw [ih x']
  | natToInt x ih =>
    cases b <;> simp only [termEq] at equal <;> try contradiction
    rw [ih equal]
  | ascribe a x ih =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨rfl, x'⟩ := equal
    rw [ih x']
  | primitive i xs r ih =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, xs'⟩, rfl⟩ := equal
    rw [ih _ xs']
  | call i xs s r ih =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨⟨rfl, xs'⟩, rfl⟩, rfl⟩ := equal
    rw [ih _ xs']
  | branch c y n r ihc ihy ihn =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨⟨c', y'⟩, n'⟩, rfl⟩ := equal
    rw [ihc c', ihy y', ihn n']
  | pack a w fs ihw ihfs =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, w'⟩, fs'⟩ := equal
    rw [ihw w', ihfs _ fs']
  | unpack w fs p body ihp ihb =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨⟨rfl, rfl⟩, p'⟩, b'⟩ := equal
    rw [ihp p', ihb b']
  | scope body ih =>
    cases b <;> simp only [termEq] at equal <;> try contradiction
    rw [ih equal]
  | letE s v body ihv ihb =>
    cases b <;> simp only [termEq, Bool.and_eq_true, decide_eq_true_eq] at equal <;> try contradiction
    obtain ⟨⟨rfl, v'⟩, b'⟩ := equal
    rw [ihv v', ihb b']
  | nil =>
    rename_i bs equal
    cases bs <;> simp_all [termsEq]
  | cons head rest ihHead ihRest =>
    rename_i bs equal
    cases bs with
    | nil => simp [termsEq] at equal
    | cons head' rest' =>
      simp only [termsEq, Bool.and_eq_true] at equal
      rw [ihHead equal.1, ihRest _ equal.2]

theorem termsEq_sound {as bs : List Term} (equal : termsEq as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [termsEq]
  | cons head rest ih =>
    cases bs with
    | nil => simp [termsEq] at equal
    | cons head' rest' =>
      simp only [termsEq, Bool.and_eq_true] at equal
      rw [termEq_sound equal.1, ih equal.2]

theorem termEq_refl (a : Term) : termEq a a = true := by
  induction a using Term.rec (motive_2 := fun as => termsEq as as = true) with
  | nil => rfl
  | cons head rest ihHead ihRest => simp [termsEq, ihHead, ihRest]
  | _ => simp_all [termEq]

theorem termsEq_refl (as : List Term) : termsEq as as = true := by
  induction as with
  | nil => rfl
  | cons head rest ih => simp [termsEq, termEq_refl, ih]

theorem functionEq_sound {a b : Function} (equal : functionEq a b = true) : a = b := by
  cases a
  cases b
  simp only [functionEq, Bool.and_eq_true, decide_eq_true_eq] at equal
  obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, body⟩, rfl⟩ := equal
  rw [termEq_sound body]

theorem functionEq_refl (a : Function) : functionEq a a = true := by
  simp [functionEq, termEq_refl]

theorem functionsEq_sound {as bs : List Function} (equal : functionsEq as bs = true) : as = bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp_all [functionsEq]
  | cons head rest ih =>
    cases bs with
    | nil => simp [functionsEq] at equal
    | cons head' rest' =>
      simp only [functionsEq, Bool.and_eq_true] at equal
      rw [functionEq_sound equal.1, ih equal.2]

theorem functionsEq_refl (as : List Function) : functionsEq as as = true := by
  induction as with
  | nil => rfl
  | cons head rest ih => simp [functionsEq, functionEq_refl, ih]

theorem moduleEq_sound {a b : Module} (equal : moduleEq a b = true) : a = b := by
  cases a
  cases b
  simp only [moduleEq, Bool.and_eq_true, decide_eq_true_eq] at equal
  obtain ⟨⟨rfl, functions⟩, rfl⟩ := equal
  rw [functionsEq_sound functions]

theorem moduleEq_refl (a : Module) : moduleEq a a = true := by
  simp [moduleEq, functionsEq_refl]

/-! ## Validation -/

/-- Validation holds exactly when the generated module and the ledger are the
compilation of the source module. -/
theorem validate_iff {source generated : Module} {entries : List Entry} :
    validate source entries generated = true ↔ generate source = (generated, entries) := by
  constructor
  · intro valid
    simp only [validate, Bool.and_eq_true, decide_eq_true_eq] at valid
    obtain ⟨sites, same⟩ := valid
    rw [← sites, ← moduleEq_sound same]
  · intro compiled
    simp [validate, compiled, moduleEq_refl]

theorem validate_sound {source generated : Module} {entries : List Entry}
    (valid : validate source entries generated = true) : generate source = (generated, entries) :=
  validate_iff.mp valid

/-! ## The structure of `generate` -/

/-- The step of the function fold of `generate`. -/
def foldStep (env : Declarations) (base baseIds : Nat) (state : List Function × List Entry) (function : Function) :
    List Function × List Entry :=
  (state.1 ++ [(rewriteFunction env base baseIds state.2 function).1],
    (rewriteFunction env base baseIds state.2 function).2)

/-- The rewritten source functions and the ledger, before `generate` decides
whether the module changes. -/
def folded (module : Module) : List Function × List Entry :=
  module.functions.foldl
    (foldStep module.declarations ((module.functions.map Function.id).foldl max 0 + 1) module.declarations.ids.length)
    ([], [])

theorem generate_eq (module : Module) :
    generate module =
      if (folded module).2.isEmpty then (module, [])
      else ({ module with
        declarations := { module.declarations with
          primitives := module.declarations.primitives ++ (folded module).2.flatMap Entry.declarations }
        functions := (folded module).2.map Entry.generated ++ (folded module).1 }, (folded module).2) := by
  rfl

theorem rewriteFunction_fst (env : Declarations) (base baseIds : Nat) (entries : List Entry) (function : Function) :
    ∃ body, (rewriteFunction env base baseIds entries function).1 = { function with body } := by
  unfold rewriteFunction
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · exact ⟨function.body, rfl⟩

/-- The header of a function: everything except its body. -/
def header (function : Function) : Nat × VastitasKernel.Namespace.Owner × List Parameter × DataType × VastitasKernel.Span :=
  (function.id, function.definition, function.parameters, function.returnType, function.span)

theorem fold_headers (env : Declarations) (base baseIds : Nat) :
    ∀ (functions : List Function) (state : List Function × List Entry),
      ∃ rewritten : List Function,
        (functions.foldl (foldStep env base baseIds) state).1 = state.1 ++ rewritten ∧
        rewritten.map header = functions.map header
  | [], state => ⟨[], by simp⟩
  | function :: rest, state => by
    obtain ⟨body, same⟩ := rewriteFunction_fst env base baseIds state.2 function
    obtain ⟨rewritten, folded, headers⟩ :=
      fold_headers env base baseIds rest (foldStep env base baseIds state function)
    refine ⟨(rewriteFunction env base baseIds state.2 function).1 :: rewritten, ?_, ?_⟩
    · rw [List.foldl_cons, folded]
      simp [foldStep]
    · simp [same, headers, header]

theorem generate_headers (module : Module) :
    ∃ rewritten : List Function,
      (generate module).1.functions = (generate module).2.map Entry.generated ++ rewritten ∧
      rewritten.map header = module.functions.map header := by
  rw [generate_eq]
  by_cases empty : (folded module).2.isEmpty
  · rw [ite_eq_left empty]
    exact ⟨module.functions, rfl, rfl⟩
  · rw [ite_eq_right empty]
    obtain ⟨rewritten, same, headers⟩ := fold_headers module.declarations
      ((module.functions.map Function.id).foldl max 0 + 1) module.declarations.ids.length module.functions ([], [])
    have functions : (folded module).1 = rewritten := same.trans (List.nil_append rewritten)
    refine ⟨rewritten, ?_, headers⟩
    show (folded module).2.map Entry.generated ++ (folded module).1 =
      (folded module).2.map Entry.generated ++ rewritten
    rw [functions]

theorem generate_declarations (module : Module) :
    (generate module).1.declarations = { module.declarations with
      primitives := module.declarations.primitives ++ (generate module).2.flatMap Entry.declarations } ∧
    (generate module).1.main = module.main := by
  rw [generate_eq]
  by_cases empty : (folded module).2.isEmpty
  · rw [ite_eq_left empty]
    refine ⟨?_, rfl⟩
    show module.declarations = { module.declarations with
      primitives := module.declarations.primitives ++ ([] : List Entry).flatMap Entry.declarations }
    rw [List.flatMap_nil, List.append_nil]
  · rw [ite_eq_right empty]
    exact ⟨rfl, rfl⟩

/-- The shape of the generated module: the source declarations with the
declarations of every entry, the source `main`, and the generated functions of
the entries before the rewritten source functions, which keep their ids,
owners, parameters, return types and spans. -/
theorem generate_shape (module : Module) :
    (generate module).1.declarations = { module.declarations with
      primitives := module.declarations.primitives ++ (generate module).2.flatMap Entry.declarations } ∧
    (generate module).1.main = module.main ∧
    ∃ rewritten : List Function,
      (generate module).1.functions = (generate module).2.map Entry.generated ++ rewritten ∧
      rewritten.map Function.id = module.functions.map Function.id ∧
      rewritten.map Function.definition = module.functions.map Function.definition ∧
      rewritten.map Function.parameters = module.functions.map Function.parameters ∧
      rewritten.map Function.returnType = module.functions.map Function.returnType ∧
      rewritten.map Function.span = module.functions.map Function.span := by
  obtain ⟨declarations, main⟩ := generate_declarations module
  obtain ⟨rewritten, functions, headers⟩ := generate_headers module
  have field {β : Type} (project : Nat × VastitasKernel.Namespace.Owner × List Parameter × DataType ×
      VastitasKernel.Span → β) : rewritten.map (project ∘ header) = module.functions.map (project ∘ header) := by
    rw [← List.map_map, headers, List.map_map]
  exact ⟨declarations, main, rewritten, functions, field (·.1), field (·.2.1), field (·.2.2.1),
    field (·.2.2.2.1), field (·.2.2.2.2)⟩

/-- Every source function stays in the generated module with its id, owner,
parameters, return type and span; only its body may change. -/
theorem generate_keeps_function (module : Module) {function : Function} (member : function ∈ module.functions) :
    ∃ rewritten ∈ (generate module).1.functions,
      rewritten.id = function.id ∧ rewritten.definition = function.definition ∧
      rewritten.parameters = function.parameters ∧ rewritten.returnType = function.returnType ∧
      rewritten.span = function.span := by
  obtain ⟨rewritten, functions, headers⟩ := generate_headers module
  have mapped : header function ∈ rewritten.map header := headers ▸ List.mem_map_of_mem member
  obtain ⟨kept, keptMember, same⟩ := List.mem_map.mp mapped
  simp only [header, Prod.mk.injEq] at same
  obtain ⟨id, definition, parameters, returnType, span⟩ := same
  refine ⟨kept, ?_, id, definition, parameters, returnType, span⟩
  rw [functions]
  exact List.mem_append_right _ keptMember

/-- A module without a site compiles to itself. -/
theorem generate_no_entries {module : Module} (empty : (generate module).2 = []) :
    (generate module).1 = module := by
  rw [generate_eq] at empty ⊢
  by_cases none : (folded module).2.isEmpty
  · rw [ite_eq_left none]
  · rw [ite_eq_right none] at empty
    exact absurd (List.isEmpty_iff.mpr empty) none

/-- A module compiles to itself exactly when its ledger is empty. -/
theorem generate_entries_nil_iff (module : Module) :
    (generate module).2 = [] ↔ (generate module).1 = module := by
  constructor
  · exact generate_no_entries
  · intro same
    obtain ⟨rewritten, functions, headers⟩ := generate_headers module
    have lengths := congrArg List.length headers
    simp only [List.length_map] at lengths
    have total := congrArg List.length functions
    rw [same] at total
    simp only [List.length_append, List.length_map, lengths] at total
    exact List.eq_nil_of_length_eq_zero (by omega)

/-- A validated ledger without entries leaves the source module unchanged. -/
theorem validate_no_entries {source generated : Module} (valid : validate source [] generated = true) :
    generated = source := by
  have compiled := validate_sound valid
  have unchanged := generate_no_entries (module := source) (by rw [compiled])
  rw [compiled] at unchanged
  exact unchanged

theorem generate_entry_mem {module : Module} {entry : Entry} (member : entry ∈ (generate module).2) :
    entry.generated ∈ (generate module).1.functions := by
  obtain ⟨rewritten, functions, _⟩ := generate_headers module
  rw [functions]
  exact List.mem_append_left _ (List.mem_map_of_mem member)

theorem generate_declaration_mem {module : Module} {entry : Entry} (member : entry ∈ (generate module).2)
    {declaration : NamedPrimitive} (declared : declaration ∈ entry.declarations) :
    declaration ∈ (generate module).1.declarations.primitives := by
  obtain ⟨declarations, _⟩ := generate_declarations module
  rw [declarations]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, member, declared⟩)

theorem primitive_lookup {env : Declarations} (unique : env.ids.Nodup) {declaration : NamedPrimitive}
    (member : declaration ∈ env.primitives) : env.primitive? declaration.id = some declaration.binding := by
  have primitives : (env.primitives.map NamedPrimitive.id).Nodup :=
    (List.nodup_append.mp unique).2.1
  unfold Declarations.primitive?
  generalize env.primitives = list at primitives member
  induction list with
  | nil => contradiction
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at primitives
    rcases List.mem_cons.mp member with equal | member
    · subst declaration; simp
    · have different : head.id ≠ declaration.id := fun equal =>
        primitives.1 (equal ▸ List.mem_map.mpr ⟨declaration, member, rfl⟩)
      simpa [List.find?_cons, different] using ih primitives.2 member

/-- With unique function ids, the generated function of an entry is found by
the entry's function id. -/
theorem generate_entry_function {module : Module}
    (unique : ((generate module).1.functions.map Function.id).Nodup) {entry : Entry}
    (member : entry ∈ (generate module).2) :
    (generate module).1.functions.find? (fun function => function.id == entry.function) =
      some entry.generated :=
  IndexedProgramSafety.function_lookup unique (generate_entry_mem member)

/-- With unique declaration ids, every declaration of an entry is found by its
id with its binding. -/
theorem generate_entry_declaration {module : Module}
    (unique : (generate module).1.declarations.ids.Nodup) {entry : Entry}
    (member : entry ∈ (generate module).2) {declaration : NamedPrimitive}
    (declared : declaration ∈ entry.declarations) :
    (generate module).1.declarations.primitive? declaration.id = some declaration.binding :=
  primitive_lookup unique (generate_declaration_mem member declared)

/-! ## The compilation stage -/

section Compiled
variable {requireMain : Bool} {source : Typing.CheckedModule requireMain}

theorem compiled_generate (compiled : Compiled source) :
    generate source.module = (compiled.core.module, compiled.entries) :=
  validate_sound compiled.validated

/-- Every entry of a compiled module resolves: its generated function by the
entry's function id, and each of its declarations by its id with its binding. -/
theorem compiled_entry_resolves (compiled : Compiled source) {entry : Entry} (member : entry ∈ compiled.entries) :
    compiled.core.module.functions.find? (fun function => function.id == entry.function) =
      some entry.generated ∧
    ∀ declaration ∈ entry.declarations,
      compiled.core.module.declarations.primitive? declaration.id = some declaration.binding := by
  have same := compiled_generate compiled
  have functions : ((generate source.module).1.functions.map Function.id).Nodup := by
    rw [same]; exact compiled.core.typed.uniqueFunctions
  have declarations : (generate source.module).1.declarations.ids.Nodup := by
    rw [same]; exact compiled.core.typed.declarations.unique
  have entries : entry ∈ (generate source.module).2 := by rw [same]; exact member
  constructor
  · simpa only [same] using generate_entry_function functions entries
  · intro declaration declared
    simpa only [same] using generate_entry_declaration declarations entries declared

/-- The compiled module keeps the source declarations and `main`, and every
source function header. -/
theorem compiled_shape (compiled : Compiled source) :
    compiled.core.module.declarations = { source.module.declarations with
      primitives := source.module.declarations.primitives ++ compiled.entries.flatMap Entry.declarations } ∧
    compiled.core.module.main = source.module.main ∧
    ∃ rewritten : List Function,
      compiled.core.module.functions = compiled.entries.map Entry.generated ++ rewritten ∧
      rewritten.map Function.id = source.module.functions.map Function.id ∧
      rewritten.map Function.definition = source.module.functions.map Function.definition ∧
      rewritten.map Function.parameters = source.module.functions.map Function.parameters ∧
      rewritten.map Function.returnType = source.module.functions.map Function.returnType ∧
      rewritten.map Function.span = source.module.functions.map Function.span := by
  simpa only [compiled_generate compiled] using generate_shape source.module

theorem compiled_no_entries (compiled : Compiled source) (empty : compiled.entries = []) :
    compiled.core.module = source.module := by
  have same := compiled_generate compiled
  have unchanged := generate_no_entries (module := source.module) (by rw [same, empty])
  rw [same] at unchanged
  exact unchanged

/-- Every function of the compiled module, generated or rewritten, has typed,
finite evaluation. -/
theorem compiled_functions_total (compiled : Compiled source) :
    ∀ function ∈ compiled.core.module.functions,
      IndexedFunctionSafety.FunctionReturns compiled.core.module function :=
  IndexedProgramSafety.checked_functions_total_and_typed compiled.core

end Compiled

/-! ## The validation holds by construction

`compile` builds the generated module with `generate` and the certificate
`validated` from the same call, so the validation cannot fail: `compile`
fails only when the Core audit rejects the generated module. The validation
therefore detects no error of the generator; the theorems about the templates
and the compiled sites are what rule such errors out. -/

/-- The Core audit returns the module it checks. -/
theorem checkModule_module {module : Module} {requireMain : Bool} {checked : Typing.CheckedModule requireMain}
    (audited : Typing.checkModule module requireMain = .ok checked) : checked.module = module := by
  unfold Typing.checkModule at audited
  split at audited
  · split at audited
    · split at audited
      · cases audited; rfl
      · cases audited
    · cases audited
  · cases audited

/-- The generator's own output validates, for every module. -/
theorem validate_generate (module : Module) : validate module (generate module).2 (generate module).1 = true :=
  validate_iff.mpr rfl

/-- **`compile` fails only by the Core audit.** When `compile` fails, the
Core audit rejects the generated module; the branch that reports a failed
validation is not reached. -/
theorem compile_fails_only_by_audit {requireMain : Bool} (source : Typing.CheckedModule requireMain)
    (diagnostic : VastitasKernel.Diagnostic) (failed : compile source = .error diagnostic) :
    ∃ error, Typing.checkModule (generate source.module).1 requireMain = .error error := by
  have valid := validate_generate source.module
  unfold compile at failed
  revert failed valid
  rcases generated : generate source.module with ⟨module, entries⟩
  intro failed valid
  dsimp only at valid failed
  split at failed
  · rename_i empty
    exfalso
    have none : entries = [] := List.isEmpty_iff.mp empty
    have same : module = source.module := by
      have unchanged := generate_no_entries (module := source.module) (by rw [generated, none])
      rw [generated] at unchanged
      exact unchanged
    rw [same] at valid
    rw [pure_bind] at failed
    try dsimp only at failed
    rw [dite_eq_left valid] at failed
    first | cases failed | (simp [pure, Except.pure] at failed) | nomatch failed | contradiction
  · cases audit : Typing.checkModule module requireMain with
    | error error => exact ⟨error, rfl⟩
    | ok checked =>
      exfalso
      have same := checkModule_module audit
      rw [← same] at valid
      rw [audit] at failed
      simp only [Except.mapError] at failed
      rw [show (Except.ok checked : Except VastitasKernel.Diagnostic (Typing.CheckedModule requireMain)) =
        pure checked from rfl, pure_bind] at failed
      try dsimp only at failed
      rw [dite_eq_left valid] at failed
      first | cases failed | (simp [pure, Except.pure] at failed) | nomatch failed | contradiction

theorem compiled_main_total {source : Typing.CheckedModule true} (compiled : Compiled source) :
    ∃ id function result,
      compiled.core.module.main = some id ∧
      compiled.core.module.functions.find? (fun function => function.id == id) = some function ∧
      IndexedEvaluation.Evaluates compiled.core.module (fun _ => none) function.body (.integer result) :=
  IndexedProgramSafety.checked_main_total compiled.core

/-! ## Public paths -/

open VastitasKernel VastitasKernel.Indexed in
/-- Protocol 7: `accepted.checked.compiled.core` is the compilation of the
executable Core of the accepted program. `Main.process` generates code from
this module; that is read from `Main`, which the oracle does not import. -/
theorem compiled_codegen_input {json : Lean.Json} (accepted : Wire.CheckedInput json true) :
    Core.Reverse.generate accepted.checked.executable.lowered.module =
      (accepted.checked.compiled.core.module, accepted.checked.compiled.entries) ∧
    Core.Reverse.validate accepted.checked.executable.core.module accepted.checked.compiled.entries
      accepted.checked.compiled.core.module = true := by
  refine ⟨?_, accepted.checked.compiled.validated⟩
  rw [← accepted.checked.executable.coreInput]
  exact compiled_generate accepted.checked.compiled

open VastitasKernel VastitasKernel.Indexed in
/-- Protocol 7: every entry of the accepted compiled module resolves, and every
function of it has typed, finite evaluation. -/
theorem public_compiled_entries {json : Lean.Json} {requireMain : Bool}
    (accepted : Wire.CheckedInput json requireMain) :
    (∀ entry ∈ accepted.checked.compiled.entries,
      accepted.checked.compiled.core.module.functions.find? (fun function => function.id == entry.function) =
        some entry.generated ∧
      ∀ declaration ∈ entry.declarations,
        accepted.checked.compiled.core.module.declarations.primitive? declaration.id = some declaration.binding) ∧
    ∀ function ∈ accepted.checked.compiled.core.module.functions,
      IndexedFunctionSafety.FunctionReturns accepted.checked.compiled.core.module function :=
  ⟨fun _ member => compiled_entry_resolves accepted.checked.compiled member,
    compiled_functions_total accepted.checked.compiled⟩

open VastitasKernel VastitasKernel.Indexed in
/-- Protocol 7: the `main` of the emitted compiled module evaluates to an `Int`. -/
theorem public_compiled_main_total {json : Lean.Json} (accepted : Wire.CheckedInput json true) :
    ∃ id function result,
      accepted.checked.compiled.core.module.main = some id ∧
      accepted.checked.compiled.core.module.functions.find? (fun function => function.id == id) = some function ∧
      IndexedEvaluation.Evaluates accepted.checked.compiled.core.module (fun _ => none) function.body
        (.integer result) :=
  compiled_main_total accepted.checked.compiled

open VastitasKernel VastitasKernel.Indexed in
/-- Protocols 2-6: `accepted.checked.compiled.core` is the compilation of the
executable Core. `Main.process` generates code from this module, as for
protocol 7. -/
theorem legacy_compiled_codegen_input {json : Lean.Json} (accepted : Indexed.LegacySource.CheckedInput json true) :
    Core.Reverse.generate accepted.checked.executable.lowered.module =
      (accepted.checked.compiled.core.module, accepted.checked.compiled.entries) ∧
    Core.Reverse.validate accepted.checked.executable.core.module accepted.checked.compiled.entries
      accepted.checked.compiled.core.module = true := by
  refine ⟨?_, accepted.checked.compiled.validated⟩
  rw [← accepted.checked.executable.coreInput]
  exact compiled_generate accepted.checked.compiled

open VastitasKernel VastitasKernel.Indexed in
/-- Protocols 8/9 without a resource entry: the emitted module is the accepted
certificate's `pureProgram.compiled` module, the compilation of the executable
Core, and every entry of its ledger resolves there. -/
theorem generated_pure_entry_compiled {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Codegen.generate program = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Core.Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Core.Codegen.generate core = .ok generated.source ∧
      Core.Reverse.generate checked.pureProgram.executable.lowered.module =
        (core.module, checked.pureProgram.compiled.entries) ∧
      ∀ entry ∈ checked.pureProgram.compiled.entries,
        core.module.functions.find? (fun function => function.id == entry.function) = some entry.generated ∧
        ∀ declaration ∈ entry.declarations,
          core.module.declarations.primitive? declaration.id = some declaration.binding := by
  obtain ⟨checked, accepted, core, same, compiled, _, _⟩ := ResourceCodegen.generated_pure_entry found emitted
  refine ⟨checked, accepted, core, same, compiled, ?_, ?_⟩
  · rw [same, ← checked.pureProgram.executable.coreInput]
    exact compiled_generate checked.pureProgram.compiled
  · intro entry member
    rw [same]
    exact compiled_entry_resolves checked.pureProgram.compiled member

open VastitasKernel VastitasKernel.Indexed in
/-- Protocol 9 (and 8) emit without a resource entry: the public request's
decoded program is checked, and its emitted module is the compiled module of
`generated_pure_entry_compiled`. -/
theorem public_pure_entry_compiled {json : Lean.Json} {program : VastitasKernel.ResourceSource.Program}
    {generated : VastitasKernel.ResourceSource.Codegen.Generated}
    (decoded : VastitasKernel.ResourceSource.Wire.program json = .ok program) (found : program.entry = none)
    (emitted : VastitasKernel.ResourceSource.Wire.emit json = .ok generated) :
    ∃ checked : VastitasKernel.ResourceSource.Checked program true,
      VastitasKernel.ResourceSource.check program true = .ok checked ∧
    ∃ core : Core.Typing.CheckedModule true,
      core.module = checked.pureProgram.compiled.core.module ∧
      Core.Codegen.generate core = .ok generated.source ∧
      Core.Reverse.generate checked.pureProgram.executable.lowered.module =
        (core.module, checked.pureProgram.compiled.entries) ∧
      ∀ entry ∈ checked.pureProgram.compiled.entries,
        core.module.functions.find? (fun function => function.id == entry.function) = some entry.generated ∧
        ∀ declaration ∈ entry.declarations,
          core.module.declarations.primitive? declaration.id = some declaration.binding := by
  obtain ⟨input, _, decodedInput, _, rendered⟩ := ResourceCodegen.public_generated_checked emitted
  have same : input.input = program := Except.ok.inj (decodedInput.symm.trans decoded)
  have generatedFrom : VastitasKernel.ResourceSource.Codegen.generate input.input = .ok generated :=
    (VastitasKernel.ResourceSource.Codegen.generate_eq_checked input.accepted).trans rendered
  rw [same] at generatedFrom
  exact generated_pure_entry_compiled found generatedFrom

open VastitasKernel VastitasKernel.Indexed in
/-- Protocols 8/9 acceptance: both compiled passes of a checked resource
program (the pure program and the pure values of a resource entry) validate
against their executable Core, every entry resolves, and every function of the
compiled modules has typed, finite evaluation. -/
theorem public_resource_compiled {json : Lean.Json} {requireMain : Bool}
    (input : VastitasKernel.ResourceSource.Wire.CheckedInput json requireMain) :
    Core.Reverse.generate input.checked.pureProgram.executable.lowered.module =
      (input.checked.pureProgram.compiled.core.module, input.checked.pureProgram.compiled.entries) ∧
    Core.Reverse.generate input.checked.values.executable.lowered.module =
      (input.checked.values.compiled.core.module, input.checked.values.compiled.entries) ∧
    (∀ entry ∈ input.checked.pureProgram.compiled.entries,
      input.checked.pureProgram.compiled.core.module.functions.find?
          (fun function => function.id == entry.function) = some entry.generated ∧
      ∀ declaration ∈ entry.declarations,
        input.checked.pureProgram.compiled.core.module.declarations.primitive? declaration.id =
          some declaration.binding) ∧
    (∀ entry ∈ input.checked.values.compiled.entries,
      input.checked.values.compiled.core.module.functions.find?
          (fun function => function.id == entry.function) = some entry.generated ∧
      ∀ declaration ∈ entry.declarations,
        input.checked.values.compiled.core.module.declarations.primitive? declaration.id =
          some declaration.binding) ∧
    (∀ function ∈ input.checked.pureProgram.compiled.core.module.functions,
      IndexedFunctionSafety.FunctionReturns input.checked.pureProgram.compiled.core.module function) ∧
    ∀ function ∈ input.checked.values.compiled.core.module.functions,
      IndexedFunctionSafety.FunctionReturns input.checked.values.compiled.core.module function := by
  refine ⟨?_, ?_, fun _ member => compiled_entry_resolves input.checked.pureProgram.compiled member,
    fun _ member => compiled_entry_resolves input.checked.values.compiled member,
    compiled_functions_total input.checked.pureProgram.compiled,
    compiled_functions_total input.checked.values.compiled⟩
  · rw [← input.checked.pureProgram.executable.coreInput]
    exact compiled_generate input.checked.pureProgram.compiled
  · rw [← input.checked.values.executable.coreInput]
    exact compiled_generate input.checked.values.compiled

end VastitasOracle.IndexedReverseCore
