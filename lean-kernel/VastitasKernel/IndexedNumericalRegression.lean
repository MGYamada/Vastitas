import VastitasKernel.IndexedSourceChecker
import VastitasKernel.IndexedCodegen

namespace VastitasKernel.Indexed.NumericalRegression

private def pkg : Namespace.PackageId := ⟨"/numeric/Vastitas.toml", "numeric", "0.1.0"⟩
private def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
private def path (name : String) : Source.Path := ⟨[name], {}⟩
private def decl (name : String) (body : Source.Body) : Source.Declaration := ⟨name, body, true, {}⟩
private def declarations : List Source.Declaration := [
  decl "R" .marker, decl "C" .marker,
  decl "BaseImpl" (.implementation (path "R") (.scalarBase .smooth .real) []),
  decl "BaseA" (.global (path "BaseImpl")), decl "BaseB" (.global (path "BaseImpl")),
  decl "RealA" (.implementation (path "R") (.linearDescriptor (path "BaseA") .real) []),
  decl "ComplexA" (.implementation (path "C") (.linearDescriptor (path "BaseA") .complex) []),
  decl "RealB" (.implementation (path "R") (.linearDescriptor (path "BaseB") .real) []) ]
private def program (ds := declarations) : Source.Program := {
  file := "numerical declarations", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := ds }], none⟩] }
private def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError s!"numerical declaration regression failed: {label}")
private def change (name : String) (body : Source.Body) : Source.Program :=
  program (declarations.map fun d => if d.name == name then {d with body} else d)
private def rejects (p : Source.Program) : Bool := !(Source.checkDeclarations p).isOk

#eval check "actual common source checker" (Source.checkDeclarations (program)).isOk
#eval check "declaration order independent" (Source.checkDeclarations (program declarations.reverse)).isOk
#eval check "coefficient marker is not a geometric base" (rejects (change "RealA"
  (.implementation (path "R") (.linearDescriptor (path "R") .real) [])))
#eval check "affine descriptor does not gain linear structure" (rejects (change "BaseImpl"
  (.implementation (path "R") .affineDescriptor [])))
#eval check "smooth base cannot be a complex scalar base" (rejects (change "BaseImpl"
  (.implementation (path "R") (.scalarBase .smooth .complex) [])))
#eval check "coefficient kind conflict across unused implementations" (rejects (program
  (declarations ++ [decl "Unused" (.implementation (path "R") (.scalarBase .scheme .complex) [])])))
#eval check "cyclic base cannot satisfy the closed base contract" (rejects (change "BaseImpl"
  (.implementation (path "R") (.linearDescriptor (path "BaseA") .real) [])))
#eval check "old capabilities cannot be claimed by numerical metadata" (rejects (change "ComplexA"
  (.implementation (path "C") (.linearDescriptor (path "BaseA") .complex) [.origin])))

#eval check "same coefficient and base implementation retain distinct nominal base IDs" (
  match Source.checkDeclarations (program) with
  | .error _ => false
  | .ok checked =>
    let env := checked.resolved.declarations.indexed
    lookup env (id "RealA") == some (.implementation (id "R") (.linearDescriptor (id "BaseA") .real) []) &&
    lookup env (id "RealB") == some (.implementation (id "R") (.linearDescriptor (id "BaseB") .real) []) &&
    id "BaseA" != id "BaseB" &&
    checked.resolved.references.any (fun reference => reference.path.path == ["BaseA"] && reference.target.owner == id "BaseA"))

#eval check "forged checked Core is audited again" (match Source.checkDeclarations (program) with
  | .error _ => false
  | .ok checked =>
    let env := checked.resolved.declarations
    let original : Core.Module := ⟨env, [], none⟩
    let forged := {env with indexed := env.indexed.map (fun entry =>
      if entry.id == id "RealA" then
        {entry with declaration := .implementation (id "R") (.linearDescriptor (id "R") .real) []}
      else entry)}
    (Core.Typing.checkModule original false).isOk &&
    !(Core.Typing.checkModule {original with declarations := forged} false).isOk &&
    !(Core.Typing.checkModule {original with declarations := {env with primitives :=
      [⟨id "forged", .descriptor (id "RealA")⟩]}} false).isOk)

end VastitasKernel.Indexed.NumericalRegression
