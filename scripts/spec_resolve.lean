import Lean

open Lean Elab Command

/-! # Specification claim resolver

This file is a check, not a theorem. It reads the statement pins of one
specification environment and checks every pinned declaration in exactly the
modules that the pins list. `scripts/check_spec.py` checks the rest of the
specification files, and `docs/specifications.md` describes both checks.

Run it from the Lake package of the environment:

```sh
cd lean && VASTITAS_SPEC_INPUT=../docs/spec/pins/oracle.json \
  lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean
cd lean-bridge && VASTITAS_SPEC_INPUT=../docs/spec/pins/bridge.json \
  lake env lean -DwarningAsError=true ../scripts/spec_resolve.lean
```

Each pinned name must exist, be declared by exactly one module, its pinned
module, under the root of the environment, and have its pinned kind. The
oracle environment resolves theorems under `VastitasOracle` and kernel
definitions under `VastitasKernel`; the bridge environment resolves theorems
under `VastitasBridge` only. A pinned declaration may reach only the axioms
`propext` of `Init.Core` and `Classical.choice` and `Quot.sound` of
`Init.Prelude`. The search walks types, values and constructors itself, as
`scripts/audit_axioms.lean` does; it does not use axiom sets recorded in
imported object files. It fails on a constant that the imported modules do not
define. Lean merges declarations of one name with one type on import, as it
does for equation lemmas that several modules generate, and keeps one copy; the
search therefore walks every copy that a project module declares. A theorem's
statement must have its pinned hash.

The hash is the SHA-256 of a canonical text of the statement: the universe
parameters and the type, with constants, universe levels, de Bruijn indices and
literals, and without binder names, binder annotations or metadata. Every form
in the text is self-delimiting, so two different types have different texts.
The pin covers the statement's expression; it does not cover the bodies of the
definitions that the statement names.

An entry without a pinned module or statement is compared with nothing, and
outside report mode its absence is a problem. With `VASTITAS_SPEC_REPORT=<file>`
the resolver also writes what it finds to that file; `check_spec.py
--update-statements` uses this mode, importing the package root, to pin new
names. Every problem fails the run, in both modes. `VASTITAS_SPEC_CANONICAL=1`
adds the canonical text of each statement to the report, so that
`scripts/check_spec_lean.py` can compare this SHA-256 with Python's, and
`VASTITAS_SPEC_STATEMENT_LIMIT` lowers the statement size limit for its test. -/
namespace VastitasSpecResolve

/-! ## SHA-256 (FIPS 180-4) -/

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message, one 1 bit, zero bits up to 56 bytes modulo 64, and the message
length in bits as a 64-bit big-endian number. -/
def padded (message : ByteArray) : ByteArray := Id.run do
  let bits : UInt64 := message.size.toUInt64 * 8
  let mut data := message.push 0x80
  while data.size % 64 != 56 do
    data := data.push 0
  for i in [0:8] do
    data := data.push (bits >>> ((7 - i) * 8).toUInt64).toUInt8
  return data

/-- One application of the compression function to the 64-byte block at `offset`. -/
def compress (state : Array UInt32) (data : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let byte (k : Nat) : UInt32 := (data.get! (offset + 4 * i + k)).toUInt32
    w := w.push ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for i in [0:64] do
    let t1 := h + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) +
      roundConstants[i]! + w[i]!
    let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b) ^^^ (a &&& c) ^^^ (b &&& c))
    h := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d,
    state[4]! + e, state[5]! + f, state[6]! + g, state[7]! + h]

def hexWord (word : UInt32) : String :=
  let digits := Nat.toDigits 16 word.toNat
  String.ofList (List.replicate (8 - digits.length) '0' ++ digits)

/-- The SHA-256 digest of `message`, as 64 lower-case hexadecimal digits. -/
def sha256 (message : ByteArray) : String := Id.run do
  let data := padded message
  let mut state := initialState
  for block in [0:data.size / 64] do
    state := compress state data (64 * block)
  return String.join (state.toList.map hexWord)

/-- Test vectors: three from FIPS 180-4 and two longer messages, one of them not ASCII. -/
def selfTests : Array (String × String) := #[
  ("", "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
  ("abc", "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
  ("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
  (String.ofList (List.replicate 1000 'a'),
    "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3"),
  ("η ∘ Df(x) = «x»", "111b67da6187fe7582c1fa22ed29e4e1f7bc2236703e53db296f619de776264d")]

/-! ## Canonical statement text -/

/-- Components of a name, each length-prefixed. -/
def appendName (out : String) : Name → String
  | .anonymous => out.push '_'
  | .str pre part => appendName out pre ++ ".s" ++ toString part.utf8ByteSize ++ ":" ++ part
  | .num pre index => appendName out pre ++ ".n" ++ toString index ++ ";"

/-- Statements longer than this many bytes are not pinned. The canonical text is
built as a tree, so the limit also bounds the work on a statement with shared
subterms. -/
def statementLimit : Nat := 4 * 1024 * 1024

partial def appendLevel (out : String) : Level → Except String String
  | .zero => pure (out.push 'z')
  | .succ level => appendLevel (out.push 's') level
  | .max left right => do
    let out ← appendLevel (out ++ "m(") left
    return (← appendLevel (out.push ',') right).push ')'
  | .imax left right => do
    let out ← appendLevel (out ++ "i(") left
    return (← appendLevel (out.push ',') right).push ')'
  | .param name => pure ((appendName (out.push 'p') name).push ';')
  | .mvar _ => throw "a universe metavariable"

partial def appendExpr (limit : Nat) (out : String) (e : Expr) : Except String String := do
  if out.utf8ByteSize > limit then
    throw s!"more than {limit} bytes of canonical text"
  appendExprStep limit out e
where
  appendExprStep (limit : Nat) (out : String) : Expr → Except String String
  | .bvar index => pure (out ++ "#" ++ toString index ++ ";")
  | .sort level => return (← appendLevel (out.push 'S') level).push ';'
  | .const name levels => do
    let mut out := (appendName (out.push 'C') name).push '{'
    for level in levels do
      out := (← appendLevel out level).push ','
    return out.push '}'
  | .app function argument => do
    let out ← appendExpr limit (out ++ "A(") function
    return (← appendExpr limit (out.push ' ') argument).push ')'
  | .lam _ type body _ => do
    let out ← appendExpr limit (out ++ "L(") type
    return (← appendExpr limit (out.push ' ') body).push ')'
  | .forallE _ type body _ => do
    let out ← appendExpr limit (out ++ "P(") type
    return (← appendExpr limit (out.push ' ') body).push ')'
  | .letE _ type value body _ => do
    let out ← appendExpr limit (out ++ "E(") type
    let out ← appendExpr limit (out.push ' ') value
    return (← appendExpr limit (out.push ' ') body).push ')'
  | .lit (.natVal value) => pure (out ++ "N" ++ toString value ++ ";")
  | .lit (.strVal value) => pure (out ++ "T" ++ toString value.utf8ByteSize ++ ":" ++ value)
  | .mdata _ inner => appendExpr limit out inner
  | .proj typeName index inner => do
    let out := appendName (out.push 'J') typeName
    return (← appendExpr limit (out ++ "." ++ toString index ++ "(") inner).push ')'
  | .fvar _ => throw "a free variable"
  | .mvar _ => throw "a metavariable"

/-- The canonical text of a declaration's statement: its universe parameters and its type. -/
def statementText (limit : Nat) (info : ConstantInfo) : Except String String := do
  let mut out := "vastitas-statement-v1 U{"
  for level in info.levelParams do
    out := (appendName out level).push ','
  let text ← appendExpr limit (out ++ "} ") info.type
  if text.utf8ByteSize > limit then
    throw s!"more than {limit} bytes of canonical text"
  return text

/-! ## Axioms -/

/-- The approved axioms and the Lean modules that declare them. -/
def approvedAxioms : Array (Name × Name) :=
  #[(`propext, `Init.Core), (`Classical.choice, `Init.Prelude), (`Quot.sound, `Init.Prelude)]

/-- The roots of the project's modules, whose constants must each have one declaring module. -/
def projectRoots : Array Name := #[`VastitasOracle, `VastitasKernel, `VastitasPromotion, `VastitasBridge,
  `VastitasAlgebraTest, `VastitasPublicTest, `VastitasStorageTest]

/-- The module that declares `name` in `env`, if any. -/
def ownerOf (env : Environment) (name : Name) : Option Name :=
  (env.getModuleIdxFor? name).bind fun index => env.allImportedModuleNames[index.toNat]?

/-- Every copy of each project constant that more than one imported project
module declares. Lean merges such copies on import and keeps one of them. -/
def copies (env : Environment) : NameMap (Array ConstantInfo) := Id.run do
  let project := (List.range env.header.moduleNames.size).filter fun index =>
    (env.header.moduleNames[index]?.map fun module => projectRoots.any (·.isPrefixOf module)).getD false
  let mut counts : NameMap Nat := {}
  for index in project do
    for name in (env.header.moduleData[index]?.map (·.constNames)).getD #[] do
      counts := counts.insert name ((counts.find? name).getD 0 + 1)
  let mut result : NameMap (Array ConstantInfo) := {}
  for index in project do
    for info in (env.header.moduleData[index]?.map (·.constants)).getD #[] do
      if (counts.find? info.name).getD 0 > 1 then
        result := result.insert info.name (((result.find? info.name).getD #[]).push info)
  return result

/-- Constants that a declaration refers to: its type, its value (also for
theorems and opaque constants) and the constructors of an inductive type. -/
def dependencies (info : ConstantInfo) : Array Name :=
  let used (expressions : List Expr) := expressions.foldl (fun found e => found ++ e.getUsedConstants) #[]
  match info with
  | .defnInfo v => used [v.type, v.value]
  | .thmInfo v => used [v.type, v.value]
  | .opaqueInfo v => used [v.type, v.value]
  | .inductInfo v => used [v.type] ++ v.ctors.toArray
  | info => used [info.type]

structure Reached where
  axioms : Array Name := #[]
  /-- Reached constants that the imported modules do not define. -/
  missing : Array Name := #[]

/-- Every axiom reachable from `root`, by an exact search with one visited set,
through every copy of a merged constant. `cache` keeps the dependencies of
each constant already read. -/
def axiomsOf (env : Environment) (merged : NameMap (Array ConstantInfo)) (cache : NameMap (Array Name))
    (root : Name) : Reached × NameMap (Array Name) := Id.run do
  let mut cache := cache
  let mut visited : NameSet := ({} : NameSet).insert root
  let mut stack := #[root]
  let mut found : Reached := {}
  while !stack.isEmpty do
    let name := stack.back!
    stack := stack.pop
    let infos := (merged.find? name).getD (env.find? name).toArray
    if infos.isEmpty then
      found := { found with missing := found.missing.push name }
      continue
    if infos.any (fun info => info matches .axiomInfo _) then
      found := { found with axioms := found.axioms.push name }
    let mut next := #[]
    match cache.find? name with
    | some known => next := known
    | none =>
      next := infos.foldl (fun all info => all ++ dependencies info) #[]
      cache := cache.insert name next
    for dependency in next do
      unless visited.contains dependency do
        visited := visited.insert dependency
        stack := stack.push dependency
  let sorted : Reached := {
    axioms := found.axioms.qsort Name.lt
    missing := found.missing.qsort Name.lt }
  return (sorted, cache)

/-! ## Pins -/

structure Rules where
  theorems : Name
  definitions : Option Name

def rules? : String → Option Rules
  | "oracle" => some { theorems := `VastitasOracle, definitions := some `VastitasKernel }
  | "bridge" => some { theorems := `VastitasBridge, definitions := none }
  | _ => none

structure Entry where
  text : String
  kind : String
  module? : Option String := none
  statement? : Option String := none

/-- A dotted Lean name without escapes, numeric components or empty components. -/
def parseName? (text : String) : Option Name :=
  let parts := text.splitOn "."
  if parts.any fun part => part.isEmpty || part.any fun c => c.isWhitespace || c == '«' || c == '»' then
    none
  else
    some (parts.foldl Name.str .anonymous)

def optionalString (json : Json) (key : String) : Except String (Option String) :=
  match json.getObjVal? key with
  | .ok value => some <$> value.getStr?
  | .error _ => pure none

/-- The environment, the modules to import and the entries of an input file. -/
def parseInput (source : String) : Except String (String × Array Name × Array Entry) := do
  let json ← Json.parse source
  match (← json.getObjVal? "format").getNat? with
  | .ok 1 => pure ()
  | _ => throw "the input must have format 1"
  let environment ← (← json.getObjVal? "environment").getStr?
  let mut imports := #[]
  for item in ← (← json.getObjVal? "imports").getArr? do
    let text ← item.getStr?
    let some module := parseName? text | throw s!"the import `{text}` is not a module name"
    imports := imports.push module
  let mut entries := #[]
  for item in ← (← json.getObjVal? "entries").getArr? do
    entries := entries.push {
      text := ← (← item.getObjVal? "name").getStr?
      kind := ← (← item.getObjVal? "kind").getStr?
      module? := ← optionalString item "module"
      statement? := ← optionalString item "statement" }
  return (environment, imports, entries)

def kindOf : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .axiomInfo _ => "axiom"
  | .opaqueInfo _ => "opaque constant"
  | .quotInfo _ => "quotient primitive"
  | .inductInfo _ => "inductive type"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

structure Outcome where
  facts : Array Json := #[]
  problems : Array String := #[]
  theorems : Nat := 0
  definitions : Nat := 0

/-- Check one entry in `env`: the facts found, the problems, and the extended cache.
A pinned module or statement must match what `env` contains; outside `report`
mode an entry must pin both. -/
def resolveEntry (env : Environment) (merged : NameMap (Array ConstantInfo)) (environment : String) (rules : Rules)
    (entry : Entry) (report canonical : Bool) (limit : Nat) (cache : NameMap (Array Name)) :
    Option Json × Array String × NameMap (Array Name) := Id.run do
  let text := entry.text
  let mut problems : Array String := #[]
  let root? := if entry.kind == "theorem" then some rules.theorems
    else if entry.kind == "definition" then rules.definitions else none
  let some root := root?
    | return (none, #[s!"{text}: the {environment} environment resolves no {entry.kind}"], cache)
  let some name := parseName? text
    | return (none, #[s!"{text}: is not a Lean name"], cache)
  if name == root || !root.isPrefixOf name then
    problems := problems.push s!"{text}: is not a fully qualified name under {root}"
  let some info := env.find? name
    | return (none, problems.push s!"{text}: is not found in the imported modules", cache)
  let owner := (ownerOf env name).getD .anonymous
  let kind := kindOf info
  if kind != entry.kind then
    problems := problems.push s!"{text}: is a {kind}, not a {entry.kind}"
  unless root.isPrefixOf owner do
    problems := problems.push s!"{text}: is defined in {owner}, outside {root}"
  if merged.contains name then
    problems := problems.push s!"{text}: is declared by more than one imported module"
  match entry.module? with
  | some module =>
    if parseName? module != some owner then
      problems := problems.push s!"{text}: is defined in {owner}, not in the pinned module {module}"
  | none =>
    unless report do problems := problems.push s!"{text}: has no pinned module"
  let mut fact : List (String × Json) :=
    [("name", toJson text), ("kind", toJson kind), ("module", toJson owner.toString)]
  let (reached, cache) := axiomsOf env merged cache name
  for axiomName in reached.axioms do
    let module := (ownerOf env axiomName).getD .anonymous
    unless approvedAxioms.contains (axiomName, module) do
      problems := problems.push s!"{text}: depends on the unapproved axiom {axiomName} of {module}"
  for missing in reached.missing do
    problems := problems.push s!"{text}: reaches {missing}, which the imported modules do not define"
  fact := fact ++ [("axioms", toJson (reached.axioms.map toString))]
  if kind == "theorem" then
    match statementText limit info with
    | .error what =>
      problems := problems.push s!"{text}: has a statement that cannot be pinned: it contains {what}"
    | .ok statement =>
      let hash := "sha256:" ++ sha256 statement.toUTF8
      fact := fact ++ [("statement", toJson hash)]
      if canonical then
        fact := fact ++ [("canonical", toJson statement)]
      match entry.statement? with
      | some pinned =>
        if pinned != hash then
          problems := problems.push s!"{text}: has a changed statement: pinned {pinned}, found {hash}"
      | none =>
        unless report do problems := problems.push s!"{text}: has no pinned statement"
  return (some (Json.mkObj fact), problems, cache)

/-- Check every entry in `env`. -/
def resolve (env : Environment) (environment : String) (rules : Rules) (entries : Array Entry)
    (report canonical : Bool) (limit : Nat) : Outcome := Id.run do
  let mut outcome : Outcome := {}
  let mut cache : NameMap (Array Name) := {}
  let merged := copies env
  for (axiomName, module) in approvedAxioms do
    if let some owner := ownerOf env axiomName then
      unless owner == module do
        let problem := s!"the imported modules declare the axiom {axiomName} in {owner}, not in {module}"
        outcome := { outcome with problems := outcome.problems.push problem }
  for entry in entries do
    let (fact?, problems, extended) :=
      resolveEntry env merged environment rules entry report canonical limit cache
    cache := extended
    outcome := { outcome with problems := outcome.problems ++ problems }
    if let some fact := fact? then
      outcome := { outcome with facts := outcome.facts.push fact }
      if entry.kind == "theorem" then
        outcome := { outcome with theorems := outcome.theorems + 1 }
      else
        outcome := { outcome with definitions := outcome.definitions + 1 }
  return outcome

end VastitasSpecResolve

open VastitasSpecResolve in
run_cmd do
  for (message, expected) in selfTests do
    let actual := sha256 message.toUTF8
    unless actual == expected do
      throwError "SHA-256 self-test failed for a {message.utf8ByteSize}-byte message: expected {expected}, found {actual}"
  let some path ← IO.getEnv "VASTITAS_SPEC_INPUT"
    | throwError "set VASTITAS_SPEC_INPUT to a statement pins file, such as ../docs/spec/pins/oracle.json"
  let report? ← IO.getEnv "VASTITAS_SPEC_REPORT"
  let canonical := (← IO.getEnv "VASTITAS_SPEC_CANONICAL") == some "1"
  let limit := ((← IO.getEnv "VASTITAS_SPEC_STATEMENT_LIMIT").bind String.toNat?).getD statementLimit
  let (environment, imports, entries) ← match parseInput (← IO.FS.readFile path) with
    | .ok input => pure input
    | .error message => throwError "{path}: {message}"
  let some rules := rules? environment
    | throwError "{path}: unknown specification environment {environment}"
  if entries.isEmpty then
    throwError "{path}: no pinned declarations; a resolver run must check at least one"
  if imports.isEmpty then
    throwError "{path}: no modules to import"
  let env ← importModules (imports.map ({ module := · })) {}
  let outcome := resolve env environment rules entries report?.isSome canonical limit
  if let some out := report? then
    IO.FS.writeFile out (Json.mkObj [("format", toJson (1 : Nat)), ("environment", toJson environment),
      ("entries", Json.arr outcome.facts), ("problems", toJson outcome.problems)]).pretty
    logInfo m!"specification resolver ({environment}): reported {entries.size} declarations to {out}"
  unless outcome.problems.isEmpty do
    throwError "specification resolver ({environment}) rejected {path}:\n{"\n".intercalate outcome.problems.toList}\nIf the change is intended, review it, then run: python3 scripts/check_spec.py --update-statements {environment}"
  if report?.isNone then
    let count (n : Nat) (noun : String) := s!"{n} {noun}{if n == 1 then "" else "s"}"
    logInfo m!"specification resolver ({environment}): {count outcome.theorems "theorem"} and {count outcome.definitions "kernel definition"} resolved in {count imports.size "module"}"
