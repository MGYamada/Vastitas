import VastitasKernel.Surface
import VastitasKernel.DispatchChecker

/-! The names that a source module cannot bind (`builtinNames`) and the
body-less headers of a surface program, which declaration and finite-family
validation read (`headers`). -/
namespace VastitasKernel.Surface

def builtinNames : List String :=
  ["Affine", "Base", "origin", "id", "compose", "apply", "dim", "int", "pair", "pair_first", "pair_second", "QQ", "CInfReal"]

-- Body-less headers are used only to reuse declaration and finite-family
-- validation. The actual bodies are checked separately, never these placeholders.
def headers (p : Program) : RawProgram := {
  version := p.version, file := p.file, generics := p.generics
  abstractTypes := p.abstractTypes, subtypes := p.subtypes, abstractMethods := p.abstractMethods
  functions := p.functions.map fun f => {
    name := f.name, params := f.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := f.result.core, body := .mk [] (.unit f.span) f.span, span := f.span }
  methods := p.methods.map fun m => {
    name := m.name, params := m.params.map fun param => { name := param.name, ty := param.ty.core, span := param.span }
    returnType := m.result.core, body := .mk [] (.unit m.span) m.span, span := m.span, requirements := m.requirements } }

end VastitasKernel.Surface
