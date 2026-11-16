set_option autoImplicit false

/-! The strict keywords of the source grammar
(`docs/language/lexical-structure.md`, `STRICT_KEYWORD`): a strict keyword
has a fixed meaning and is never an identifier. The frontend's `KEYWORDS`
(`src/frontend.rs`) is the same list, and a unit test of the frontend reads
this definition and compares the two. The spectral audit of a fiber
coordinate reads it (`SpectralDeclarations.isIdentifier`, #831). -/
namespace VastitasKernel

/-- The strict keywords of the source grammar. -/
def strictKeywords : List String :=
  ["abstract", "as", "domain", "else", "false", "fn", "for", "generic", "if", "let", "loop", "method", "mut",
   "pack", "requires", "return", "subtype", "true", "type", "unpack", "while"]

end VastitasKernel
