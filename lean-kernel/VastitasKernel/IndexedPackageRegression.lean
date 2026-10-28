import VastitasKernel.IndexedPackages

namespace VastitasKernel.Indexed.PackageRegression
private def id (name : String) : DeclId := ⟨⟨⟨"/package", "package", "1"⟩, []⟩, name⟩
private def env : Environment := [
  ⟨id "K", .marker⟩, ⟨id "L", .marker⟩,
  ⟨id "Grid", .implementation (id "K") .affineDescriptor [.origin, .dimension]⟩,
  ⟨id "Sparse", .implementation (id "K") .affineDescriptor []⟩,
  ⟨id "Other", .implementation (id "L") .affineDescriptor []⟩,
  ⟨id "Container", .classification [] [id "Grid", id "Sparse"]⟩,
  ⟨id "Base", .global (id "Grid")⟩,
  ⟨id "Position", .family ⟨[.object (id "Container"), .object (id "Container")], [.sameBase 0 1], .point⟩⟩,
  ⟨id "Self", .family ⟨[.object (id "Container"), .object (id "Container")], [.sameObject 0 1], .token⟩⟩,
  ⟨id "GridOnly", .family ⟨[.object (id "Grid")], [], .token⟩⟩ ]
private def shape : PackageShape := ⟨⟨id "Container", id "K"⟩,
  [⟨id "Position", [.witness, .global (id "Base")]⟩, ⟨id "Self", [.witness, .witness]⟩]⟩
private def x : ObjectRef := .local ⟨id "Grid", id "K"⟩ 2
private def y : ObjectRef := .local ⟨id "Grid", id "K"⟩ 3
private def z : ObjectRef := .local ⟨id "Other", id "L"⟩ 4
private def payload (witness : ObjectRef) : PackagePayload := ⟨witness, shape.instantiate witness⟩
private def check (name : String) (accepted : Bool) : IO Unit :=
  unless accepted do throw (IO.userError s!"indexed package regression failed: {name}")

#eval check "valid finite package declaration" (validEnvironment env && validPackageShape env shape)
#eval check "non-geometric association" (validPackageShape env ⟨shape.witnessType,
  [⟨id "Self", [.witness, .witness]⟩]⟩)
#eval check "payload may hide its concrete implementation" (validPackagePayload env shape (payload x))
#eval check "field must belong to its actual witness" (!validPackagePayload env shape
  ⟨x, shape.instantiate y⟩)
#eval check "wrong base cannot be hidden" (!validPackagePayload env shape (payload z))
#eval check "missing and extra fields" (!validPackagePayload env shape ⟨x, []⟩ &&
  !validPackagePayload env shape ⟨x, shape.instantiate x ++ shape.instantiate x⟩)
#eval check "same-object descriptor is not the canonical object" (!validPackagePayload env shape
  ⟨x, [⟨id "Position", [.object x, .object y]⟩, ⟨id "Self", [.object x, .object x]⟩]⟩)
#eval check "template retains the entire abstract domain" (!validPackageShape env
  ⟨shape.witnessType, [⟨id "GridOnly", [.witness]⟩]⟩)
#eval check "template cannot identify witness with a global" (!validPackageShape env
  ⟨shape.witnessType, [⟨id "Self", [.witness, .global (id "Base")]⟩]⟩)
#eval check "unknown global in a template" (!validPackageShape env
  ⟨shape.witnessType, [⟨id "Position", [.witness, .global (id "missing")]⟩]⟩)
#eval check "marker is not a canonical object" (!validPackageShape env
  ⟨shape.witnessType, [⟨id "Position", [.witness, .marker (id "K")]⟩]⟩)
#eval check "empty witness domain rejected" (!validPackageShape env
  { shape with witnessType := ⟨id "Grid", id "L"⟩ })
#eval check "checked opening, repeated opening and repacking" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => match checkPackageShape checked shape with
    | .error _ => false
    | .ok checkedShape => match checkPackagePayload checkedShape (payload x) with
      | .error _ => false
      | .ok _ => match openPackage checkedShape [x] 10 with
        | .error _ => false
        | .ok first => match openPackage checkedShape [x, first.opening.witness] 11 with
          | .error _ => false
          | .ok second => first.opening.witness != second.opening.witness &&
            (checkPackagePayload checkedShape ⟨first.opening.witness, first.opening.fields⟩).isOk &&
            !(checkPackagePayload checkedShape ⟨first.opening.witness, second.opening.fields⟩).isOk &&
            !(openPackage checkedShape [first.opening.witness] 10).isOk)
#eval check "freshness ignores forged type metadata" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => match checkPackageShape checked shape with
    | .error _ => false
    | .ok checkedShape => !(openPackage checkedShape [z] 4).isOk)
#eval check "forged opening rejected by independent audit" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => match checkPackageShape checked shape with
    | .error _ => false
    | .ok checkedShape =>
      !(checkPackageOpening checkedShape [] 10 ⟨x, shape.instantiate x⟩).isOk &&
      !(checkPackageOpening checkedShape [] 10
        ⟨.local shape.witnessType 10, shape.instantiate y⟩).isOk)
#eval check "opened field cannot escape to an outer scope" (
  let opened := shape.instantiate (.local shape.witnessType 10)
  opened.all (fun app => decide (app.Scoped [.local shape.witnessType 10])) &&
    !(opened.head!.Scoped [] |> decide))
end VastitasKernel.Indexed.PackageRegression
