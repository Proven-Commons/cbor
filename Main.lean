/-
  Command line front end for the CBOR codec. It reads one request per
  line on stdin and writes one answer per line, so the differential
  tests can drive millions of cases through one process.

    d <hex>    Decode the bytes. Prints the item in canonical form, or
               `error` for anything the decoder turns away.
    r <hex>    Decode, then encode again. Prints the lowercase hex of
               the encoding, or `error`.

  Hex is two lowercase or uppercase digits per byte, with nothing
  between them. A line that is not a well-formed request prints
  `error`.
-/

import Cbor

open Cbor

/-- Parse hex text into bytes. Accepts either case; anything else,
    including an odd number of digits, is `none`. -/
def parseHex : List Char → Option (List UInt8)
  | [] => some []
  | c1 :: c2 :: rest => do
    let digit (c : Char) : Option Nat :=
      if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
      else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
      else none
    let hi ← digit c1
    let lo ← digit c2
    let tl ← parseHex rest
    some ((hi * 16 + lo).toUInt8 :: tl)
  | [_] => none

/-- Drop a trailing LF, then a trailing CR. -/
def stripEol (s : String) : String :=
  let cs := s.toList
  let cs := if cs.getLast? = some '\n' then cs.dropLast else cs
  let cs := if cs.getLast? = some '\r' then cs.dropLast else cs
  String.ofList cs

def answer (line : String) : String :=
  match line.toList with
  | 'd' :: ' ' :: hex =>
    (match parseHex hex with
    | none => "error"
    | some bs =>
      match decode bs with
      | none => "error"
      | some v => v.canonical)
  | 'r' :: ' ' :: hex =>
    (match parseHex hex with
    | none => "error"
    | some bs =>
      match decode bs with
      | none => "error"
      | some v => hexOf (encode v))
  | _ => "error"

partial def loop : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  while true do
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (answer (stripEol line))
    stdout.flush

def main : IO Unit := loop
