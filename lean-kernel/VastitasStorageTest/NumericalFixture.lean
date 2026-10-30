import VastitasKernel.StorageFunctions
import VastitasKernel.IndexedSourceChecker

namespace VastitasKernel.Storage.NumericalFixture
open Indexed

def pkg : Namespace.PackageId := ⟨"/numeric-values/Vastitas.toml", "numeric-values", "0.1.0"⟩
def id (name : String) : DeclId := ⟨⟨pkg, []⟩, name⟩
def path (name : String) : Indexed.Source.Path := ⟨[name], {}⟩
def decl (name : String) (body : Indexed.Source.Body) : Indexed.Source.Declaration := ⟨name, body, true, {}⟩
def source : Indexed.Source.Program := {
  file := "numeric values", root := pkg.source,
  packages := [⟨pkg, [], [{
    module := {path := [], isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {}}
    declarations := [decl "R" .marker, decl "C" .marker,
      decl "Scalar" (.implementation (path "R") (.scalarBase .smooth .real) []),
      decl "Base" (.global (path "Scalar")), decl "OtherBase" (.global (path "Scalar")),
      decl "Real" (.implementation (path "R") (.linearDescriptor (path "Base") .real) []),
      decl "Complex" (.implementation (path "C") (.linearDescriptor (path "Base") .complex) []),
      decl "Other" (.implementation (path "R") (.linearDescriptor (path "OtherBase") .real) []),
      decl "Affine" (.implementation (path "R") .affineDescriptor [])] }], none⟩] }

def layout (rows columns : Nat) : Layout := ⟨0, rows, columns, max 1 rows, false⟩
def payload : Scalar → Literal | .f64 => .f64 0x3ff0000000000000 | .complexF64 => .complexF64 0 0x3ff0000000000000

/-- A: V(3) → W(2), B: U(2) → V(3), C: U → W, with distinct U/W. -/
def setup (scalar : Scalar) (implementation : String) (middle := 3) : List Functions.Statement := [
  .numerical (.space 0 (id implementation) 2),
  .numerical (.space 1 (id implementation) middle),
  .numerical (.space 2 (id implementation) 2),
  .numerical (.basis 3 0), .numerical (.basis 4 1), .numerical (.basis 5 2),
  .action (.allocate 10 scalar (2 * middle)), .action (.allocate 11 scalar (middle * 2)),
  .action (.allocate 12 scalar 4),
  .action (.borrow 20 (.owner 10) (layout 2 middle) .write),
  .action (.fill 20 (payload scalar)), .action (.release 20),
  .action (.borrow 21 (.owner 11) (layout middle 2) .write),
  .action (.fill 21 (payload scalar)), .action (.release 21),
  .action (.borrow 22 (.owner 10) (layout 2 middle) .read),
  .action (.borrow 23 (.owner 11) (layout middle 2) .read),
  .action (.borrow 24 (.owner 12) (layout 2 2) .write),
  .numerical (.map 30 22 4 5), .numerical (.map 31 23 3 4), .numerical (.map 32 24 3 5)]

def multiply : Functions.Statement := .numerical (.gemm 30 31 32 .overwrite .nativeFast)
def cleanup : List Functions.Statement := [
  .action (.release 22), .action (.release 23), .action (.release 24),
  .action (.borrow 25 (.owner 12) (layout 2 2) .read), .action (.release 25),
  .action (.drop 10), .action (.drop 11), .action (.drop 12)]
def program (body : List Functions.Statement) : Functions.Program := ⟨[⟨0, [], [], body⟩], 0⟩

end VastitasKernel.Storage.NumericalFixture
