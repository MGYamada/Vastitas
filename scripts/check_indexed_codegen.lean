import VastitasKernel.IndexedCodegen
import VastitasKernel.IndexedCoreRegression
import VastitasKernel.IndexedPackageSemanticRegression

open VastitasKernel.Indexed.Core

def main (arguments : List String) : IO Unit := do
  let [directory] := arguments | throw (IO.userError "expected output directory")
  for (name, module) in [("package", Regression.packageFixture),
      ("primitives", Regression.primitiveFixture), ("scalar", Regression.scalarFixture),
      ("global_witness", PackageSemanticRegression.globalWitnessFixture),
      ("multiple_fields", PackageSemanticRegression.multipleFieldsFixture)] do
    let .ok checked := Typing.checkModule module true
      | throw (IO.userError s!"fixture {name} rejected")
    let .ok source := Codegen.generate checked
      | throw (IO.userError s!"fixture {name} failed code generation")
    IO.FS.writeFile (System.FilePath.mk directory / s!"{name}.lean") source
