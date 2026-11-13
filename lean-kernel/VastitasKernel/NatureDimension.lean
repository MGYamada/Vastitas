import VastitasKernel.Indexed

set_option autoImplicit false

/-! Checks for the declarations of the minimal `nature::dimension` profile
(Stage 4, #759): base dimensions, quantity kinds, physical readings of a
chart, scales, and physical interpretations of a metric. "Dimension" here is
a physical dimension, an element of the free abelian group on the base
dimensions, not the dimension of a vector space. `Entry.Valid`
(`IndexedValidity`) calls one check per declaration.

Not implemented yet: every check rejects, so no environment with a nature
declaration is valid. -/
namespace VastitasKernel.NatureDimension

open VastitasKernel.Indexed

/-- The base dimension declaration. It rejects every declaration until the
nature checks are implemented. -/
def checkBaseDimension (_env : Environment) : Bool := false

/-- The quantity declaration `quantity dimension`. It rejects every
declaration until the nature checks are implemented. -/
def checkQuantity (_env : Environment) (_dimension : DimensionVector) : Bool := false

/-- The reading declaration `reading family object quantities`. It rejects
every declaration until the nature checks are implemented. -/
def checkReading (_env : Environment) (_family _object : DeclId) (_quantities : List DeclId) : Bool := false

/-- The scale declaration `scale quantity magnitude`. It rejects every
declaration until the nature checks are implemented. -/
def checkScale (_env : Environment) (_quantity : DeclId) (_magnitude : Rat) : Bool := false

/-- The physical metric declaration `physicalMetric family object metric
reading value entries`. It rejects every declaration until the nature checks
are implemented. -/
def checkPhysicalMetric (_env : Environment) (_family _object _metric _reading : DeclId)
    (_value : Option DimensionVector) (_entries : PhysicalGram) : Bool := false

end VastitasKernel.NatureDimension
