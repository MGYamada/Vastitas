import VastitasKernel.TypeAudit
import VastitasKernel.Dependency
import VastitasKernel.Checker
import VastitasKernel.Codegen

/-!
Adversarial checked-IR regressions for the independent audit. These are executable
regression checks, separate from the logical soundness theorems.
They bypass raw elaboration so the audit itself must reject forged annotations.
-/
namespace VastitasKernel.TypeAuditRegression
open Typing

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"checked-IR audit regression failed: {name}")

private def objectRef (id : Nat) : ObjectRef := .local .qq id
private def objectType (id : Nat) : ResultType := ⟨.object .qq, some (objectRef id)⟩
private def pointType (id : Nat) : ResultType := ⟨.point (objectRef id) (.base .qq), none⟩
private def affine (id : Nat) : Term :=
  .builtin (.affine .qq) [.literal .nat 2] (objectType id)
private def origin (id symbol : Nat) : Term :=
  .builtin .origin [.var symbol (objectType id)] (pointType id)
private def function (id : Nat) (body : Term) (returnType : Ty := .int)
    (params : List CheckedParam := []) : CheckedFunction :=
  { id, name := s!"test{id}", params, returnType, body, span := {} }
private def module (functions : List CheckedFunction) : CheckedModule :=
  { functions, mainId := none }

#eval check "scalar acceptance" (auditModule (module [function 0 (.literal .int 7)]) == true)

-- An in-scope point and its declared object remain associated.
private def pointIdentity : CheckedFunction :=
  function 0 (.var 2 (pointType 1)) (.point (objectRef 1) (.base .qq))
    [⟨1, objectType 1⟩, ⟨2, pointType 1⟩]
#eval check "dependent identity acceptance" (auditModule (module [pointIdentity]) == true)

-- Primitive result annotations cannot override their operation's contract.
#eval check "forged arithmetic result" (auditModule (module [function 0 (.binary .add
    (.literal .nat 1) (.literal .nat 2) .int)]) == false)
#eval check "wrong unary operand" (auditModule (module [function 0 (.unary .neg
    (.literal .nat 1) .int)]) == false)
#eval check "non-numeric literal" (auditModule (module [function 0
    (.literal (.pointed .qq) 1) (.pointed .qq)]) == false)
#eval check "forged branch result" (auditModule (module [function 0
    (.branch (.boolean true) (.literal .nat 1) (.literal .nat 2) ⟨.int, none⟩)]) == false)

-- A variable must exist with exactly the recorded type and nominal endpoint.
#eval check "unbound variable" (auditModule (module [function 0 (.var 99 ⟨.int, none⟩)]) == false)
#eval check "forged nominal variable endpoint" (auditModule (module [function 0 (.var 2 (pointType 3))
    (.point (objectRef 3) (.base .qq))
    [⟨1, objectType 1⟩, ⟨2, pointType 1⟩, ⟨3, objectType 3⟩]]) == false)

-- Equal descriptors do not allow two allocations to share one brand.
#eval check "duplicate allocation brand" (auditModule (module [function 0 (.letE 1 (affine 10)
    (.letE 2 (affine 10) (.literal .int 0)))]) == false)
#eval check "canonical base cannot be an allocation" (auditModule (module [function 0
    (.builtin (.affine .qq) [.literal .nat 2] ⟨.object .qq, some (.base .qq)⟩)
    (.object .qq)]) == false)

-- Local endpoint escape and mismatched package endpoints are rejected.
#eval check "escaping local point" (auditModule (module [function 0 (.letE 1 (affine 10) (origin 10 1))
    (.point (objectRef 10) (.base .qq))]) == false)
#eval check "mismatched package object" (auditModule (module [function 0 (.letE 1 (affine 10)
    (.letE 2 (affine 20) (.pack .qq (.var 1 (objectType 10)) (origin 20 2))))
    (.pointed .qq)]) == false)

-- Rebinding a live symbol and opening a non-package cannot fabricate bindings.
#eval check "shadowed symbol" (auditModule (module [function 0 (.letE 1 (.literal .int 1)
    (.letE 1 (.literal .int 2) (.var 1 ⟨.int, none⟩)))]) == false)
#eval check "non-package unpack" (auditModule (module [function 0 (.unpack 1 2 (.literal .int 0)
    (.literal .int 1))]) == false)

-- Object arguments require the precise formal-to-actual substitution.
private def applyPoint (substitution : List (ObjectRef × ObjectRef)) : CheckedFunction :=
  function 3 (.letE 4 (affine 4) (.letE 5 (origin 4 4)
    (.letE 6 (.call 0 [.var 4 (objectType 4), .var 5 (pointType 4)] substitution
      (pointType 4)) (.literal .int 1))))
#eval check "dependent call acceptance" (auditModule (module [pointIdentity,
    applyPoint [(objectRef 1, objectRef 4)]]) == true)
#eval check "missing call substitution" (auditModule (module [pointIdentity, applyPoint []]) == false)
#eval check "cross-base call substitution" (auditModule (module [pointIdentity,
    applyPoint [(objectRef 1, .local .cinfReal 4)]]) == false)

-- Signature IDs and generative parameter brands are unique across the module.
#eval check "duplicate function ID" (auditModule (module [function 0 (.literal .int 0),
    function 0 (.literal .int 1)]) == false)
#eval check "duplicate parameter brand" (auditModule (module [pointIdentity,
    function 3 (.literal .int 1) .int [⟨1, objectType 1⟩]]) == false)

-- Graph acceptance is independent of typing: these calls have valid signatures.
private def scalarCall (target : Nat) : Term := .call target [] [] ⟨.int, none⟩
#eval check "ordered scalar call" (Dependency.auditModule (module
    [function 0 (.literal .int 1), function 1 (scalarCall 0)]) == true)
#eval check "self recursion" (Dependency.auditModule (module
    [function 0 (scalarCall 0)]) == false)
#eval check "mutual recursion" (Dependency.auditModule (module
    [function 0 (scalarCall 1), function 1 (scalarCall 0)]) == false)
#eval check "unknown callee" (Dependency.auditModule (module
    [function 0 (scalarCall 42)]) == false)

-- The same boundary also accepts actual elaborator output, not only hand-built terms.
private def rawScalar : RawModule :=
  { version := 1, file := "audit-regression.vast", functions := [
      { name := "main", params := [], returnType := .named "Int",
        body := .mk [] (.binary "+" (.integer "40" {}) (.integer "2" {}) {}) {}, span := {} }] }
#eval check "actual raw checker output" (match checkModule rawScalar true with
  | .ok checked => Typing.auditModule checked.val && Dependency.auditModule checked.val
  | .error _ => false)

-- Even a manually obtained legacy annotation certificate cannot bypass the
-- independent checks at the public code-generation boundary.
private def codegenRejects (functions : List CheckedFunction) (message : String) : Bool :=
  match certifyModule { functions, mainId := some 0 } with
  | .error _ => false -- The fixture must pass the weaker, legacy certificate.
  | .ok certified => match Codegen.generate certified with
    | .ok _ => false
    | .error actual => actual == message

#eval check "codegen rejects unbound legacy certificate" (codegenRejects
  [function 0 (.var 99 ⟨.int, none⟩)]
  "checked IR failed declarative typing audit before code generation")
#eval check "codegen rejects retagged legacy certificate" (codegenRejects
  [function 0 (.var 2 (pointType 3)) (.point (objectRef 3) (.base .qq))
    [⟨1, objectType 1⟩, ⟨2, pointType 1⟩, ⟨3, objectType 3⟩]]
  "checked IR failed declarative typing audit before code generation")
#eval check "codegen rejects recursive legacy certificate" (codegenRejects
  [function 0 (scalarCall 0)]
  "checked IR failed dependency-order audit before code generation")
#eval check "codegen accepts valid scalar certificate" (match certifyModule
    { functions := [function 0 (.literal .int 42)], mainId := some 0 } with
  | .error _ => false
  | .ok certified => match Codegen.generate certified with
    | .ok _ => true
    | .error _ => false)

#eval check "codegen rejects missing main ID" (match certifyModule
    { functions := [function 0 (.literal .int 42)], mainId := some 99 } with
  | .ok certified => match Codegen.generate certified with
    | .error message => message == "native entrypoint refers to a missing function"
    | .ok _ => false
  | .error _ => false)
#eval check "codegen rejects parameterized entrypoint" (codegenRejects
  [function 0 (.literal .int 42) .int [⟨1, ⟨.int, none⟩⟩]]
  "native entrypoint must have no parameters and return Int")
#eval check "codegen rejects Bool entrypoint" (codegenRejects
  [function 0 (.boolean true) .bool]
  "native entrypoint must have no parameters and return Int")

end VastitasKernel.TypeAuditRegression
