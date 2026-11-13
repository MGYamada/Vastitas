import VastitasKernel.IndexedMetricSource

set_option autoImplicit false

/-! Presentation only: the rule that an invalid indexed declaration breaks, in
the words of the source.

`Core.validDeclarations` alone decides acceptance. The functions here run only
after it has rejected, to name the first rule of the rejected declaration that
does not hold. Each follows the conjuncts of the check of its declaration
(`Entry.Valid`, `NamedPackage.Valid`, the registry entry of a binding) and
reports a rule only where its conjunct fails. A declaration that its check
rejects for a reason that these functions do not find keeps the general
message. A rule is a code and a message: the size limits of a classification,
a family and a package declaration are `E_LIMIT`, every other rule `E_TYPE`.
Messages name declarations by their full path, `package::module::name`. -/
namespace VastitasKernel.Indexed.Source

/-- The code and the message of a broken rule. -/
abbrev Rule := String × String

/-- The first element of a list that a later element repeats. -/
def repeated {α : Type} [BEq α] : List α → Option α
  | [] => none
  | x :: rest => if rest.contains x then some x else repeated rest

/-- An object type as a diagnostic writes it, `D<K>`. -/
def objectTypeText (type : Indexed.ObjectType) : String := s!"{qualified type.domain}<{qualified type.marker}>"

/-- An indexed type as a diagnostic writes it: the family and its arguments. -/
def applicationLabel (application : Application) : String :=
  let index : Index → String
    | .domain id | .marker id | .object (.global id) | .frame id => id.name
    | .object (.local type _) => s!"{type.domain.name}<{type.marker.name}>"
    | .natural value => toString value
  s!"{application.family.name}<{String.intercalate ", " (application.indices.map index)}>"

def parameterText : Indexed.Parameter → String
  | .domain => "domain"
  | .marker => "marker"
  | .natural => "natural"
  | .object id => s!"object({qualified id})"
  | .frame family => s!"frame({qualified family})"

def constraintText : Constraint → String
  | .sameObject left right => s!"same_object({left}, {right})"
  | .sameBase left right => s!"same_base({left}, {right})"
  | .over object marker => s!"over({object}, {marker})"
  | .structural object base => s!"structural({object}, {base})"
  | .canonical object => s!"canonical({object})"

def representationText : FamilyRepresentation → String
  | .token => "token"
  | .point => "point"
  | .morphism => "morphism"
  | .relative => "relative"
  | .smooth => "smooth"
  | .fiber .tangent => "tangent"
  | .fiber .cotangent => "cotangent"
  | .tape => "tape"
  | .metricForm => "metric_form"
  | .frame => "frame"
  | .frameFiber .tangent => "frame_vector"
  | .frameFiber .cotangent => "frame_covector"
  | .frameMap => "frame_map"
  | .reading => "reading"
  | .physicalMetric => "physical_metric"

def boundIndexText : Indexed.BoundIndex → String
  | .witness => "witness"
  | .global id => s!"global({id.name})"
  | .domain id => s!"domain({id.name})"
  | .marker id => s!"marker({id.name})"
  | .natural value => toString value

def fieldText (field : Indexed.BoundApplication) : String :=
  s!"{qualified field.family}({String.intercalate ", " (field.indices.map boundIndexText)})"

/-- Why `ObjectType.Valid` rejects an object type. -/
def objectTypeProblem (env : Environment) (type : Indexed.ObjectType) : Option String :=
  if !isDomain env type.domain then
    some s!"`{qualified type.domain}` is neither a classification nor an implementation"
  else if !isMarker env type.marker then some s!"`{qualified type.marker}` is not a marker"
  else if (type.implementations env).isEmpty then
    some s!"no implementation of `{qualified type.domain}` has the marker `{qualified type.marker}`"
  else none

/-- Why `validApplication` rejects an application. `argument i` names the
argument at position `i`. -/
def applicationProblem (env : Environment) (application : Application) (argument : Nat → String) :
    Option String :=
  let family := qualified application.family
  match lookup env application.family with
  | some (.family contract) =>
    if contract.parameters.length != application.indices.length then
      some s!"`{family}` has {contract.parameters.length} parameters, but {application.indices.length} arguments are given"
    else
      match (contract.parameters.zip application.indices).zipIdx.find?
          (fun ((parameter, index), _) => !decide (parameter.Accepts env index)) with
      | some ((parameter, _), position) =>
        some s!"{argument position} does not fit the parameter `{parameterText parameter}` of `{family}`"
      | none =>
        (contract.constraints.find? (fun constraint => !constraintHolds env application.indices constraint)).map
          fun constraint => s!"the constraint `{constraintText constraint}` of `{family}` does not hold"
  | _ => some s!"`{family}` is not a family"

/-- The rule of `Entry.Valid` that an invalid classification breaks. -/
def classificationRule (env : Environment) (ranks : List (DeclId × Nat)) (entry : Entry) : Option Rule := do
  let .classification parents implementations := entry.declaration | none
  let name := qualified entry.id
  if let some parent := repeated parents then
    return ("E_TYPE", s!"the parents of the classification `{name}` name `{qualified parent}` twice")
  if let some implementation := repeated implementations then
    return ("E_TYPE", s!"the domain of the classification `{name}` names `{qualified implementation}` twice")
  if implementations.isEmpty then
    return ("E_TYPE", s!"the domain of the classification `{name}` must not be empty")
  if implementations.length > 64 then
    return ("E_LIMIT", s!"the domain of the classification `{name}` has {implementations.length} " ++
      "implementations, more than the limit of 64")
  if let some other := implementations.find? (fun id => (implementationMarker env id).isNone) then
    return ("E_TYPE", s!"each path of the domain of the classification `{name}` must name an implementation, " ++
      s!"but `{qualified other}` is not one")
  for parent in parents do
    match lookup env parent with
    | some (.classification _ parentDomain) =>
      if let some missing := implementations.find? (fun id => !parentDomain.contains id) then
        return ("E_TYPE", s!"the domain of the parent `{qualified parent}` of the classification `{name}` must " ++
          s!"contain every implementation of the domain of `{name}`, but it does not contain `{qualified missing}`")
      if !decide (classRank ranks parent < classRank ranks entry.id) then
        return ("E_TYPE", s!"the parents of the classification `{name}` must not form a cycle, but they reach " ++
          s!"one through `{qualified parent}`")
    | _ =>
      return ("E_TYPE", s!"each parent of the classification `{name}` must be a classification, " ++
        s!"but `{qualified parent}` is not one")
  none

/-- The rule of `Entry.Valid` that an invalid global object breaks. -/
def globalRule (env : Environment) (entry : Entry) : Option Rule := do
  let .global implementation := entry.declaration | none
  let name := qualified entry.id
  let declared (form : String) :=
    s!"the global object `{name}` must not name the `{form}` implementation `{qualified implementation}`: " ++
      "an `indexed affine` declaration declares the objects of that implementation"
  if (implementationMarker env implementation).isNone then
    return ("E_TYPE", s!"the global object `{name}` must name an implementation, " ++
      s!"but `{qualified implementation}` is not one")
  if presentedImplementation env implementation then return ("E_TYPE", declared "presented_affine")
  if smoothImplementation env implementation then return ("E_TYPE", declared "smooth_affine")
  none

/-- What a well-formed constraint names. -/
private def wellFormedRule : Constraint → String
  | .sameObject .. | .sameBase .. | .structural .. => "must name two positions of `object(…)` parameters"
  | .over .. => "must name the position of an `object(…)` parameter and then the position of a `marker` parameter"
  | .canonical _ => "must name the position of an `object(…)` parameter"

/-- The rule of `Family.Valid` that an invalid family breaks. -/
def familyRule (env : Environment) (entry : Entry) : Option Rule := do
  let .family contract := entry.declaration | none
  let name := qualified entry.id
  let form := representationText contract.representation
  let count := contract.parameters.length
  if count > 16 then
    return ("E_LIMIT", s!"the family `{name}` has {count} parameters, more than the limit of 16")
  match contract.parameters.zipIdx.find? (fun (parameter, _) => !decide (parameter.Valid env)) with
  | some (.object id, position) =>
    return ("E_TYPE", s!"the parameter `object({qualified id})` at position {position} of the family `{name}` " ++
      "must name a classification or an implementation")
  | some (.frame family, position) =>
    return ("E_TYPE", s!"the parameter `frame({qualified family})` at position {position} of the family `{name}` " ++
      "must name a family with the representation `frame`")
  | _ => pure ()
  if let some constraint := contract.constraints.find? (fun constraint =>
      !decide (constraint.WellFormed contract.parameters)) then
    return ("E_TYPE", s!"the constraint `{constraintText constraint}` of the family `{name}` " ++
      wellFormedRule constraint)
  let objects (expected : Nat) : Bool :=
    count == expected && contract.parameters.all fun | .object _ => true | _ => false
  let frames (expected : Nat) : Bool :=
    count == expected && contract.parameters.all fun | .frame _ => true | _ => false
  let shape (parameters : String) : Option Rule :=
    some ("E_TYPE", s!"the `{form}` family `{name}` must have {parameters}")
  let implementationsOf (representation : String) (holds : DeclId → Bool) : Option Rule :=
    let ids := contract.parameters.flatMap fun | .object id => domain env id | _ => []
    (ids.find? (fun id => !holds id)).map fun id =>
      ("E_TYPE", s!"every implementation in the domains of the parameters of the `{form}` family `{name}` " ++
        s!"must have the representation `{representation}`, but `{qualified id}` does not")
  match contract.representation with
  | .token => none
  | .point | .morphism =>
    if !objects 2 then shape "exactly two parameters, both `object(…)`"
    else if !contract.constraints.contains (.sameBase 0 1) then shape "the constraint `same_base(0, 1)`"
    else implementationsOf "affine_descriptor" (affineImplementation env)
  | .relative =>
    if !objects 3 then shape "exactly three parameters, all `object(…)`"
    else if contract.constraints != [.structural 0 2, .structural 1 2] then
      shape "exactly the constraints `structural(0, 2), structural(1, 2)`"
    else implementationsOf "presented_affine" (presentedImplementation env)
  | .smooth | .tape =>
    if !objects 2 then shape "exactly two parameters, both `object(…)`"
    else if contract.constraints != [.canonical 0, .canonical 1] then
      shape "exactly the constraints `canonical(0), canonical(1)`"
    else implementationsOf "smooth_affine" (smoothImplementation env)
  | .fiber _ | .metricForm | .frame | .reading | .physicalMetric =>
    if !objects 1 then shape "exactly one parameter, of the form `object(…)`"
    else if contract.constraints != [.canonical 0] then shape "exactly the constraint `canonical(0)`"
    else implementationsOf "smooth_affine" (smoothImplementation env)
  | .frameFiber _ =>
    if !frames 1 then shape "exactly one parameter, of the form `frame(…)`"
    else if !contract.constraints.isEmpty then shape "no constraints"
    else none
  | .frameMap =>
    if !frames 2 then shape "exactly two parameters, both `frame(…)`"
    else if !contract.constraints.isEmpty then shape "no constraints"
    else none

/-- The rule of `NamedPackage.Valid` that an invalid package declaration breaks. -/
def packageRule (env : Environment) (declaration : Core.NamedPackage) : Option Rule := do
  let name := qualified declaration.id
  let cases := declaration.cases
  if cases.isEmpty then
    return ("E_TYPE", s!"the package declaration `{name}` must have at least one case")
  if cases.length > 64 then
    return ("E_LIMIT", s!"the package declaration `{name}` has {cases.length} cases, more than the limit of 64")
  if let some type := repeated (cases.map (·.witnessType)) then
    return ("E_TYPE", s!"two cases of the package declaration `{name}` have the witness type `{objectTypeText type}`")
  for shape in cases do
    let caseText := s!"the case `{objectTypeText shape.witnessType}` of the package declaration `{name}`"
    if let some reason := objectTypeProblem env shape.witnessType then
      return ("E_TYPE", s!"the witness type of {caseText} must be an object type, but {reason}")
    if shape.fields.length > 64 then
      return ("E_LIMIT", s!"{caseText} has {shape.fields.length} fields, more than the limit of 64")
    for field in shape.fields do
      let index (position : Nat) : String :=
        s!"the bound index `{(field.indices[position]?.map boundIndexText).getD ""}` at position {position}"
      if let some reason := applicationProblem env (field.instantiate shape.representative) index then
        return ("E_TYPE", s!"the field `{fieldText field}` of {caseText} must be a valid type for every witness, " ++
          s!"but {reason}")
  none

/-- The rule of a primitive binding that `validPrimitiveBinding` rejects. `name`
is the declaration and `op` its binding as the source spells it: an op such as
`relative_view`, or `morphism` for a declared map. -/
def primitiveRule (env : Environment) (name : DeclId) (op : String) (binding : PrimitiveBinding) :
    Option String :=
  let subject := if op == "morphism" then s!"the morphism `{qualified name}`"
    else s!"the `{op}` primitive `{qualified name}`"
  let rule (holds : Bool) (message : String) : Option String := if holds then none else some message
  let family (id : DeclId) (holds : Bool) (what : String) : Option String :=
    rule holds s!"the family `{qualified id}` of {subject} must {what}"
  let relative (id : DeclId) := family id (isRelativeFamily env id) "be a relative family"
  let smooth (id : DeclId) := family id (isSmoothFamily env id) "have the representation `smooth`"
  let tape (id : DeclId) := family id (isTapeFamily env id) "have the representation `tape`"
  let fiber (id : DeclId) :=
    family id (fiberVariance? env id).isSome "have the representation `tangent` or `cotangent`"
  let variance (id : DeclId) (expected : Variance) :=
    family id (fiberVariance? env id == some expected)
      s!"have the representation `{representationText (.fiber expected)}`"
  let typeOf (domain : Indexed.ObjectType) : Option String :=
    (objectTypeProblem env domain).map fun reason =>
      s!"the object type `{objectTypeText domain}` of {subject} is not an object type: {reason}"
  let supports (domain : Indexed.ObjectType) (capability : Capability) (spelling : String) : Option String :=
    (typeOf domain).orElse fun _ =>
      ((domain.implementations env).find? (fun id => !implementationSupports env id capability)).map fun id =>
        s!"every implementation of `{objectTypeText domain}` must have the capability `{spelling}` for " ++
          s!"{subject}, but `{qualified id}` lacks it"
  -- An application that the binding fixes, with its arguments named as `names` says.
  let result (application : Application) (what : String) (names : List String) : Option String :=
    (applicationProblem env application fun position => (names[position]?).getD s!"the argument {position}").map
      fun reason => s!"{what} `{applicationLabel application}` of {subject} is not a valid type: {reason}"
  let first (rules : List (Option String)) : Option String := rules.findSome? id
  match binding with
  | .descriptor implementation =>
    first [rule (implementationMarker env implementation).isSome
        s!"the path of {subject} must name an implementation, but `{qualified implementation}` is not one",
      rule (affineImplementation env implementation)
        s!"the implementation `{qualified implementation}` of {subject} must have the representation `affine_descriptor`"]
  | .global id =>
    rule (affineGlobal env id) <| s!"the path of {subject} must name a global object of an `affine_descriptor` " ++
      s!"implementation, but `{qualified id}` is not one"
  | .origin domain points base =>
    first [supports domain .origin "origin",
      family points (familyRepresentation env points == some .point) "have the representation `point`",
      result ⟨points, [.object (.local domain 0), .object (.global base)]⟩ "the type"
        [s!"an object of type `{objectTypeText domain}`", s!"the base object `{qualified base}`"]]
  | .identity domain maps =>
    first [typeOf domain,
      family maps (familyRepresentation env maps == some .morphism) "have the representation `morphism`",
      result ⟨maps, [.object (.local domain 0), .object (.local domain 0)]⟩ "the type"
        [s!"an object of type `{objectTypeText domain}`", s!"an object of type `{objectTypeText domain}`"]]
  | .dimension domain => supports domain .dimension "dimension"
  | .compose maps => family maps (familyRepresentation env maps == some .morphism) "have the representation `morphism`"
  | .apply maps points =>
    first [family maps (familyRepresentation env maps == some .morphism) "have the representation `morphism`",
      family points (familyRepresentation env points == some .point) "have the representation `point`"]
  | .relativeConstant application _ =>
    first [rule (isRelativeFamily env application.family || isSmoothFamily env application.family)
        s!"the family `{qualified application.family}` of {subject} must be a relative or a smooth family",
      result application "the type" ["the source", "the target", "the base"]]
  | .smoothConstant application _ => result application "the type" ["the source", "the target"]
  | .relativeCompose family | .relativeEqual family => relative family
  | .relativeView family source target =>
    first [relative family,
      rule (onChain env source target) s!"`{qualified target}` must lie on the base chain of `{qualified source}` in {subject}"]
  | .relativeCoefficient family .. => relative family
  | .relativeIntPoint family object base =>
    let point : Application := ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩
    first [relative family,
      rule (freeAffine env object)
        s!"the relations of the object `{qualified object}` of {subject} must generate the zero ideal",
      rule (pointBase env base) <| s!"the object `{qualified base}` of {subject} must have no coordinates and " ++
        "relations that generate the zero ideal",
      if !validApplication env point && !onChain env object base then
        some <| s!"the result type `{applicationLabel point}` of {subject} is not a valid type: " ++
          s!"`{qualified base}` is not on the base chain of `{qualified object}`"
      else result point "the result type" ["the base", "the object", "the base"]]
  | .relativePair family product =>
    first [relative family,
      match ((affineData? env product).map (·.construction) : Option AlgebraDeclarations.Construction) with
      | some (.fiber _ _ none _) => none
      | some (.fiber _ _ (some _) _) =>
        some s!"the fiber product `{qualified product}` of {subject} must be declared without `via`"
      | _ => some s!"`{qualified product}` of {subject} must be a fiber product declared without `via`"]
  | .smoothCompose family | .smoothEqual family | .smoothComposite family | .smoothApply family => smooth family
  | .smoothIntPoint family object point =>
    first [smooth family,
      result ⟨family, [.object (.global point), .object (.global object)]⟩ "the result type"
        ["the point object", "the object"]]
  | .fiberVector family maps object =>
    first [fiber family, smooth maps, result ⟨family, [.object (.global object)]⟩ "the result type" ["the object"]]
  | .fiberAt family maps => first [fiber family, smooth maps]
  | .fiberEqual family => fiber family
  | .fiberComponent family object _ =>
    first [fiber family, result ⟨family, [.object (.global object)]⟩ "the type" ["the object"]]
  | .fiberPairing cotangent tangent => first [variance cotangent .cotangent, variance tangent .tangent]
  | .cotangentPullback maps cotangent _ => first [smooth maps, variance cotangent .cotangent]
  | .differential maps cotangent _ => first [smooth maps, variance cotangent .cotangent]
  | .linearize maps tapes => first [smooth maps, tape tapes]
  | .cotangentBackward tapes cotangent => first [tape tapes, variance cotangent .cotangent]
  | _ => none

end VastitasKernel.Indexed.Source
