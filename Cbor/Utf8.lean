/-
  A UTF-8 validator, written from the well-formed byte condition table
  of RFC 3629, page 4 (the same table Unicode's UAX #31-independent
  definition uses). It turns away overlong forms, surrogate halves,
  values past U+10FFFF, leading bytes with no valid continuation, and
  sequences cut short by the end of the input.
-/

namespace Cbor.Utf8

/-- One continuation byte: 0x80 to 0xBF. -/
def cont (b : UInt8) : Bool := 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF

/-- Is this byte string well-formed UTF-8, per the RFC 3629 table? -/
def valid : List UInt8 → Bool
  | [] => true
  | b :: rest =>
    let n := b.toNat
    if n ≤ 0x7F then valid rest
    else if 0xC2 ≤ n ∧ n ≤ 0xDF then
      match rest with
      | c1 :: r => cont c1 && valid r
      | [] => false
    else if n = 0xE0 then
      match rest with
      | c1 :: c2 :: r => (0xA0 ≤ c1.toNat ∧ c1.toNat ≤ 0xBF) && cont c2 && valid r
      | _ => false
    else if (0xE1 ≤ n ∧ n ≤ 0xEC) ∨ n = 0xEE ∨ n = 0xEF then
      match rest with
      | c1 :: c2 :: r => cont c1 && cont c2 && valid r
      | _ => false
    else if n = 0xED then
      match rest with
      | c1 :: c2 :: r => (0x80 ≤ c1.toNat ∧ c1.toNat ≤ 0x9F) && cont c2 && valid r
      | _ => false
    else if n = 0xF0 then
      match rest with
      | c1 :: c2 :: c3 :: r => (0x90 ≤ c1.toNat ∧ c1.toNat ≤ 0xBF) && cont c2 && cont c3 && valid r
      | _ => false
    else if 0xF1 ≤ n ∧ n ≤ 0xF3 then
      match rest with
      | c1 :: c2 :: c3 :: r => cont c1 && cont c2 && cont c3 && valid r
      | _ => false
    else if n = 0xF4 then
      match rest with
      | c1 :: c2 :: c3 :: r => (0x80 ≤ c1.toNat ∧ c1.toNat ≤ 0x8F) && cont c2 && cont c3 && valid r
      | _ => false
    else false
