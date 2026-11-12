import VastitasKernel.IndexedMetricSource

set_option autoImplicit false

/-! Presentation only: the rule that an invalid indexed declaration breaks, in
the words of the source.

`Core.validDeclarations` alone decides acceptance. The functions here run only
after it has rejected, to name the first rule of the rejected declaration that
does not hold. Each follows the conjuncts of the check of its declaration and
reports a rule only where its conjunct fails. A declaration that its check
rejects for a reason that these functions do not find keeps the general
message. Messages name declarations by their full path,
`package::module::name`. -/
namespace VastitasKernel.Indexed.Source

/-- An indexed type as a diagnostic writes it: the family and its arguments. -/
def applicationLabel (application : Application) : String :=
  let index : Index → String
    | .domain id | .marker id | .object (.global id) => id.name
    | .object (.local type _) => s!"{type.domain.name}<{type.marker.name}>"
    | .natural value => toString value
  s!"{application.family.name}<{String.intercalate ", " (application.indices.map index)}>"

/-- The rule of a primitive binding that `validPrimitiveBinding` rejects. `name`
is the declaration and `op` its binding as the source spells it. -/
def primitiveRule (env : Environment) (name : DeclId) (op : String) : PrimitiveBinding → Option String
  | .relativeIntPoint family object base =>
    let subject := s!"the `{op}` primitive `{qualified name}`"
    let point : Application :=
      ⟨family, [.object (.global base), .object (.global object), .object (.global base)]⟩
    if !isRelativeFamily env family then
      some s!"the family `{qualified family}` of {subject} must be a relative family"
    else if !freeAffine env object then
      some s!"the relations of the object `{qualified object}` of {subject} must generate the zero ideal"
    else if !pointBase env base then
      some <| s!"the object `{qualified base}` of {subject} must have no coordinates and relations that " ++
        "generate the zero ideal"
    else if !validApplication env point then
      let reason := if !onChain env object base then
          s!": `{qualified base}` is not on the base chain of `{qualified object}`"
        else ""
      some s!"the result type `{applicationLabel point}` of {subject} is not a valid type{reason}"
    else none
  | _ => none

end VastitasKernel.Indexed.Source
