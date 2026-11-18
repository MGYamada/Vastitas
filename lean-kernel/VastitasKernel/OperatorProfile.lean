import VastitasKernel.IndexedDispatchSource
import VastitasKernel.OperatorNames

namespace VastitasKernel.Indexed.OperatorProfile
open FunctionSource

private def keys : String → List (List Core.PureType)
  | "neg" => [[.int]]
  | "add" | "sub" | "mul" => [[.nat,.nat],[.int,.int]]
  | "div" => [[.nat,.nat],[.nat,.int],[.int,.nat],[.int,.int]]
  | _ => []

private def header (name : String) : Namespace.Generic :=
  let names := if name == "neg" then ["a"] else ["a","b"]
  { name, isPublic := true, span := {}, params := names.map (⟨·, {}⟩),
    domain := (keys name).map (·.map DispatchSource.pureType) }

private def method (name : String) (key : List Core.PureType) : DispatchSource.Method :=
  let op := match name with | "add" => "+" | "sub" | "neg" => "-" | "mul" => "*" | _ => "/"
  let val (n : String) := Expr.variable n {}
  let expr := if name == "neg" then Expr.unary op (val "a") {}
              else Expr.binary op (val "a") (val "b") {}
  { target := ⟨[name], {}⟩, requirements := [], span := {},
    params := (["a","b"].zip key).map (fun (n, t) => ⟨n, .data (DispatchSource.pureType t), {}⟩),
    result := if key.all (· == .nat) then .nat else .int,
    body := .mk [] expr {} }

private def emptyModule (path : List String) : Namespace.Module :=
  { path, isPublic := true, imports := [], functions := [], generics := [], methods := [], span := {} }

/-- Only the kernel constructs these bodies. The finite methods go through
the same authority, Fn, dispatch and returned-Core audits as source methods. -/
def package (names : List String) : DispatchSource.Package :=
  { id := Namespace.operatorScope.package, dependencies := [], modules := [
    { module := emptyModule [], declarations := [] },
    { module := { emptyModule Namespace.operatorScope.path with generics := names.map header },
      declarations := [], methods := names.flatMap (fun n => (keys n).map (method n)) }] }

abbrev Mention := Source.Path
abbrev Bound := Std.HashSet String
mutual
  def values (candidate : String → Bool) (bound : Bound) : Expr → List Mention
    | .variable n s => if candidate n && !bound.contains n then [⟨[n], s⟩] else []
    | .functionValue p _ => [p]
    | .lambda params _ b _ => blockValues candidate (params.foldl (fun seen p => seen.insert p.name) bound) b
    | .block b _ => blockValues candidate bound b
    | .unary _ v _ => values candidate bound v
    | .binary _ a b _ => values candidate bound a ++ values candidate bound b
    | .call _ args _ | .finiteCall _ _ args _ | .finiteLookup _ args _ => args.flatMap (values candidate bound)
    | .invoke f args _ => values candidate bound f ++ args.flatMap (values candidate bound)
    | .pack _ v fs _ => values candidate bound v ++ fs.flatMap (values candidate bound)
    | .branch c a b _ => values candidate bound c ++ blockValues candidate bound a ++ blockValues candidate bound b
    | .unit _ | .integer .. | .boolean .. | .lifted .. => []
    termination_by expr => (sizeOf expr, 0)
  def blockValues (candidate : String → Bool) (bound : Bound) : Block → List Mention
    | .mk stmts r _ => stmtValues candidate bound stmts r
    termination_by block => (sizeOf block, 0)
  def stmtValues (candidate : String → Bool) (bound : Bound) : List Stmt → Expr → List Mention
    | [], r => values candidate bound r
    | .letE n _ v _ :: rest, r =>
        values candidate bound v ++ stmtValues candidate (bound.insert n) rest r
    | .unpack v w fs _ :: rest, r =>
        values candidate bound v ++ stmtValues candidate (fs.foldl (fun seen n => seen.insert n) (bound.insert w)) rest r
    termination_by stmts r => (sizeOf stmts + sizeOf r, 1)
end

end VastitasKernel.Indexed.OperatorProfile
