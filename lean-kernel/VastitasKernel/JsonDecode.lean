import Lean.Data.Json
import VastitasKernel.Program

namespace VastitasKernel.JsonDecode
open Lean

def str (j : Json) (key : String) : Except String String :=
  j.getObjValAs? String key

def field (j : Json) (key : String) : Except String Json :=
  j.getObjVal? key

def array (j : Json) (key : String) : Except String (List Json) := do
  pure (← (← field j key).getArr?).toList

def optionalArray (j : Json) (key : String) : Except String (List Json) := do
  match j.getObjVal? key with
  | .error _ => return []
  | .ok value => return (← value.getArr?).toList

def fields (j : Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← j.getObj?).toArray do
    if !allowed.contains key then throw s!"unknown protocol field '{key}'"

def decodeSpan (j : Json) : Except String Span := do
  let s ← field j "span"
  fields s ["start", "end", "line", "column"]
  let start ← s.getObjValAs? Nat "start"
  let finish ← s.getObjValAs? Nat "end"
  let line ← s.getObjValAs? Nat "line"
  let column ← s.getObjValAs? Nat "column"
  if start > finish || line == 0 || column == 0 then
    throw "invalid source span"
  pure { start, «end» := finish, line, column }

end VastitasKernel.JsonDecode
