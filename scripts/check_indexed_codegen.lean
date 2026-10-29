import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedCoreRegression
import VastitasKernel.IndexedPackageSemanticRegression
import VastitasKernel.IndexedSourceRegression
import VastitasKernel.IndexedSourceTypeRegression
import VastitasKernel.IndexedSourceBodyRegression

open VastitasKernel.Indexed.Core

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  let .ok sourceFixture := VastitasKernel.Indexed.Source.Regression.sourceFixture
    | throw (IO.userError "source declaration fixture rejected")
  let .ok typeFixture := VastitasKernel.Indexed.Source.TypeRegression.typeFixture
    | throw (IO.userError "source type fixture rejected")
  let mut bodies := []
  for (name, program) in [
      ("source_bodies", VastitasKernel.Indexed.Source.BodyRegression.packageFixture),
      ("source_scalars", VastitasKernel.Indexed.Source.BodyRegression.scalarFixture),
      ("source_fields", VastitasKernel.Indexed.Source.BodyRegression.multipleFixture)] do
    let .ok checked := VastitasKernel.Indexed.Source.Bodies.checkProgram program true
      | throw (IO.userError s!"fixture {name} failed source body checking")
    bodies := bodies ++ [(name, checked.core.module)]
  for (name, module) in [("package", Regression.packageFixture),
      ("primitives", Regression.primitiveFixture), ("scalar", Regression.scalarFixture),
      ("global_witness", PackageSemanticRegression.globalWitnessFixture),
      ("multiple_fields", PackageSemanticRegression.multipleFieldsFixture),
      ("source_declarations", sourceFixture), ("source_types", typeFixture)] ++ bodies do
    let .ok checked := Typing.checkModule module true
      | throw (IO.userError s!"fixture {name} rejected")
    let .ok source := Codegen.generate checked
      | throw (IO.userError s!"fixture {name} failed code generation")
    IO.FS.writeFile (System.FilePath.mk directory / s!"{name}.lean") source
