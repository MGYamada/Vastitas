import VastitasKernel.Indexed

namespace VastitasKernel.Indexed.Regression
private def id (name : String) : DeclId :=
  ⟨⟨⟨"/indexed/Vastitas.toml", "indexed", "0.1.0"⟩, []⟩, name⟩
private def entry (name : String) (declaration : Declaration) : Entry := ⟨id name, declaration⟩
private def env : Environment := [
  entry "Coefficient" .marker, entry "OtherCoefficient" .marker,
  entry "Grid" (.implementation (id "Coefficient") .affineDescriptor [.origin, .dimension]),
  entry "SparseGrid" (.implementation (id "Coefficient") .affineDescriptor []),
  entry "OtherGrid" (.implementation (id "OtherCoefficient") .affineDescriptor [.dimension]),
  entry "Container" (.classification [] [id "Grid", id "SparseGrid", id "OtherGrid"]),
  entry "DenseContainer" (.classification [id "Container"] [id "Grid"]),
  entry "Canonical" (.global (id "Grid")),
  entry "Position" (.family ⟨[.object (id "Container"), .object (id "Container")],
    [.sameBase 0 1], .point⟩),
  entry "Self" (.family ⟨[.object (id "Container"), .object (id "Container")],
    [.sameObject 0 1], .token⟩),
  entry "VectorShape" (.family ⟨[.object (id "Container"), .marker, .natural], [.over 0 1], .token⟩),
  entry "DenseOnly" (.family ⟨[.object (id "DenseContainer")], [], .token⟩) ]
private def x : ObjectRef := .local ⟨id "Container", id "Coefficient"⟩ 0
private def y : ObjectRef := .local ⟨id "Container", id "Coefficient"⟩ 1
private def z : ObjectRef := .local ⟨id "Container", id "OtherCoefficient"⟩ 2
private def app (family : String) (indices : List Index) : Application := ⟨id family, indices⟩
private def replace (name : String) (declaration : Declaration) : Environment :=
  env.map fun e => if e.id == id name then { e with declaration } else e
private def check (name : String) (accepted : Bool) : IO Unit :=
  unless accepted do throw (IO.userError s!"indexed regression failed: {name}")

#eval check "declarations and non-geometric families" (validEnvironment env)
#eval check "order independence" (validEnvironment env.reverse)
#eval check "duplicate identity" (!validEnvironment (env ++ [entry "Container" .marker]))
#eval check "same spelling in a different module stays distinct" (
  let foreignId := { id "Coefficient" with scope := { (id "Coefficient").scope with path := ["other"] } }
  validEnvironment (env ++ [⟨foreignId, .marker⟩]) &&
    !validEnvironment (replace "Grid" (.implementation foreignId .affineDescriptor [])))
#eval check "unknown marker" (!validEnvironment (replace "Grid"
  (.implementation (id "missing") .affineDescriptor [])))
#eval check "wrong marker kind" (!validEnvironment (replace "Grid"
  (.implementation (id "Container") .affineDescriptor [])))
#eval check "unknown class member" (!validEnvironment (replace "Container" (.classification [] [id "absent"])))
#eval check "empty class" (!validEnvironment (replace "Container" (.classification [] [])))
#eval check "invalid parent kind" (!validEnvironment (replace "DenseContainer"
  (.classification [id "Grid"] [id "Grid"])))
#eval check "self cycle" (!validEnvironment (replace "Container"
  (.classification [id "Container"] [id "Grid", id "SparseGrid", id "OtherGrid"])))
#eval check "cycle" (!validEnvironment (replace "Container" (.classification [id "DenseContainer"] [id "Grid"])))
#eval check "subclass domain cannot expand parent" (!validEnvironment
  (env.map fun e => if e.id == id "Container" then
    { e with declaration := .classification [] [id "SparseGrid"] } else e))
#eval check "global must bind an implementation" (!validEnvironment (replace "Canonical" (.global (id "Container"))))
#eval check "sealed point representation requires base constraint" (!validEnvironment
  (replace "Position" (.family ⟨[.object (id "Container"), .object (id "Container")], [], .point⟩)))
#eval check "constraint positions are kind checked" (!validEnvironment
  (replace "Self" (.family ⟨[.marker], [.sameObject 0 0], .token⟩)))
#eval check "constraint positions are bounded" (!validEnvironment
  (replace "Self" (.family ⟨[.object (id "Container")], [.sameObject 0 1], .token⟩)))
#eval check "capabilities cannot be duplicated" (!validEnvironment
  (replace "Grid" (.implementation (id "Coefficient") .affineDescriptor [.origin, .origin])))

#eval check "general test object" (validApplication env (app "Position" [.object x, .object y]))
#eval check "canonical object" (validApplication env (app "Position" [.object x, .object (.global (id "Canonical"))]))
#eval check "a marker is not an object" (!validApplication env (app "Position" [.object x, .marker (id "Coefficient")]))
#eval check "base mismatch" (!validApplication env (app "Position" [.object x, .object z]))
#eval check "exact object equality" (validApplication env (app "Self" [.object x, .object x]) &&
  !validApplication env (app "Self" [.object x, .object y]))
#eval check "non-geometric natural index" (validApplication env (app "VectorShape"
  [.object x, .marker (id "Coefficient"), .natural 12]))
#eval check "forged base metadata" (!validApplication env (app "VectorShape"
  [.object x, .marker (id "OtherCoefficient"), .natural 12]))
#eval check "wrong index arity" (!validApplication env (app "Position" [.object x]) &&
  !validApplication env (app "Position" [.object x, .object y, .object x]))
#eval check "unknown family" (!validApplication env (app "Scheme" []))
#eval check "empty object implementation set" (!validApplication env (app "Self"
  [.object (.local ⟨id "Grid", id "OtherCoefficient"⟩ 0), .object x]))
#eval check "entire finite domain required" (!validApplication env (app "DenseOnly" [.object x]) &&
  validApplication env (app "DenseOnly" [.object (.local ⟨id "Grid", id "Coefficient"⟩ 0)]))
#eval check "token indices cannot hide an escape" (
  let shaped := app "VectorShape" [.object x, .marker (id "Coefficient"), .natural 12]
  decide (shaped.Scoped [x]) && !decide (shaped.Scoped [y]))
#eval check "canonical references cannot be substituted" (
  renameRef [(.global (id "Canonical"), x)] (.global (id "Canonical")) == .global (id "Canonical"))
#eval check "substitution preserves the marker and domain" (
  decide (SubstitutionValid env [(x, y)]) && !decide (SubstitutionValid env [(x, z)]))
#eval check "substitution cannot rewrite a global" (!decide
  (SubstitutionValid env [(.global (id "Canonical"), x)]))
#eval check "substitution cannot duplicate a source" (!decide
  (SubstitutionValid env [(x, y), (x, x)]))
#eval check "actual checked API keeps exact environment" (match checkEnvironment env with
  | .error _ => false
  | .ok checked => (checkApplication checked (app "Self" [.object x, .object x])).isOk &&
    !(checkApplication checked (app "Self" [.object x, .object y])).isOk)
private def renameId (old : DeclId) : DeclId := { old with name := "Renamed_" ++ old.name }
private def renameParameter : Parameter → Parameter
  | .object id => .object (renameId id)
  | other => other
private def renameDeclaration : Declaration → Declaration
  | .marker => .marker
  | .implementation marker repr capabilities => .implementation (renameId marker) repr capabilities
  | .classification parents domain => .classification (parents.map renameId) (domain.map renameId)
  | .global implementation => .global (renameId implementation)
  | .family family => .family { family with parameters := family.parameters.map renameParameter }
private def renamed : Environment := env.map fun e => ⟨renameId e.id, renameDeclaration e.declaration⟩
#eval check "coherent library renaming preserves acceptance" (validEnvironment renamed &&
  validApplication renamed ⟨renameId (id "Position"), [
    .object (.local ⟨renameId (id "Container"), renameId (id "Coefficient")⟩ 0),
    .object (.global (renameId (id "Canonical"))) ]⟩)
#eval check "no acceptance from the old spelling after renaming" (
  !validApplication renamed (app "Position" [.object x, .object y]))
#eval check "equal global descriptors do not identify declarations" (
  let extended := env ++ [entry "SecondCanonical" (.global (id "Grid"))]
  validEnvironment extended && !validApplication extended (app "Self" [
    .object (.global (id "Canonical")), .object (.global (id "SecondCanonical"))]))
end VastitasKernel.Indexed.Regression
