import Inputs

namespace VastitasQualification.ExitFixture
open Lean

/-- A complete JSON value delimited by object/array arities. Object keys are
traversed in the map's order. Numbers retain both representation fields. -/
inductive RevisionToken where
  | null | boolean (b : Bool) | number (mantissa : Int) (exponent : Nat)
  | string (text : String) | key (text : String) | array (size : Nat) | object (size : Nat)
  deriving DecidableEq

def revisionTokens : Nat → Json → Option (List RevisionToken)
  | 0, _ => none
  | _ + 1, .null => some [.null]
  | _ + 1, .bool b => some [.boolean b]
  | _ + 1, .num n => some [.number n.mantissa n.exponent]
  | _ + 1, .str s => some [.string s]
  | depth + 1, .arr xs => do
    let items ← xs.toList.mapM (revisionTokens depth)
    return .array xs.size :: items.flatten
  | depth + 1, .obj fields => do
    let parts := fields.toList
    let items ← parts.mapM fun (k,v) => do return .key k :: (← revisionTokens depth v)
    return .object parts.length :: items.flatten
end VastitasQualification.ExitFixture
