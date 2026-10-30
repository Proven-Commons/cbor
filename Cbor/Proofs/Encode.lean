/-
  The encoder writes the encoding of the specification: `Cbor.encode v`
  is `Cbor.Spec.enc v` for every item.
-/

import Cbor
import Cbor.Spec.Defs

namespace Cbor

theorem toNat_toUInt8 (x : Nat) : x.toUInt8.toNat = x % 256 := by simp [Nat.toUInt8]

/-- Two numbers give the same byte when they agree modulo 256. -/
theorem toUInt8_eq (x y : Nat) (h : x % 256 = y % 256) : x.toUInt8 = y.toUInt8 :=
  UInt8.toNat_inj.mp (by rw [toNat_toUInt8, toNat_toUInt8, h])

/-- Peeling the last byte off `netBytes`. -/
theorem netBytes_succ (n x : Nat) :
    Cbor.Spec.netBytes (n + 1) x = Cbor.Spec.netBytes n (x / 256) ++ [(x % 256).toUInt8] := by
  induction n generalizing x with
  | zero => simp [Cbor.Spec.netBytes]
  | succ n ih =>
    rw [Cbor.Spec.netBytes, ih x, Cbor.Spec.netBytes, Nat.div_div_eq_div_mul, Nat.pow_succ,
      Nat.mul_comm 256 (256 ^ n)]
    rfl

/-- The code's big-endian bytes are the specification's network byte
    order. -/
theorem beBytes_eq_netBytes (n x : Nat) : beBytes n x = Cbor.Spec.netBytes n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [beBytes, ih, netBytes_succ]

/-- The code's head is the specification's head. -/
theorem head_eq_itemHead (mt arg : Nat) : head mt arg = Cbor.Spec.itemHead mt arg := by
  have hadd : ∀ k : Nat, (mt * 32).toUInt8 + k.toUInt8 = (mt * 32 + k).toUInt8 := by
    intro k
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_add, toNat_toUInt8, toNat_toUInt8, toNat_toUInt8, ← Nat.add_mod]
  have hlit : ∀ k : Nat, k < 256 → (OfNat.ofNat k : UInt8) = k.toUInt8 := by
    intro k hk
    apply UInt8.toNat_inj.mp
    rw [toNat_toUInt8, UInt8.toNat_ofNat]
  unfold head Cbor.Spec.itemHead
  simp only [Cbor.Spec.netBytes, beBytes_eq_netBytes]
  by_cases h1 : arg < 24
  · rw [ite_eq_left h1, ite_eq_left h1, hadd]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : arg < 2 ^ 8
    · rw [ite_eq_left (by omega : arg ≤ 0xFF), ite_eq_left h2,
        show (24 : UInt8) = (24 : Nat).toUInt8 from hlit 24 (by decide), hadd,
        toUInt8_eq arg (arg / 256 ^ 0 % 256) (by simp)]
    · rw [ite_eq_right (by omega : ¬ arg ≤ 0xFF), ite_eq_right h2]
      by_cases h3 : arg < 2 ^ 16
      · rw [ite_eq_left (by omega : arg ≤ 0xFFFF), ite_eq_left h3,
          show (25 : UInt8) = (25 : Nat).toUInt8 from hlit 25 (by decide), hadd]
        rfl
      · rw [ite_eq_right (by omega : ¬ arg ≤ 0xFFFF), ite_eq_right h3]
        by_cases h4 : arg < 2 ^ 32
        · rw [ite_eq_left (by omega : arg ≤ 0xFFFFFFFF), ite_eq_left h4,
            show (26 : UInt8) = (26 : Nat).toUInt8 from hlit 26 (by decide), hadd]
          rfl
        · rw [ite_eq_right (by omega : ¬ arg ≤ 0xFFFFFFFF), ite_eq_right h4,
            show (27 : UInt8) = (27 : Nat).toUInt8 from hlit 27 (by decide), hadd]
          rfl

mutual
theorem encode_eq_enc : ∀ v : Value, encode v = Cbor.Spec.enc v
  | .uint n => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead]
  | .nint n => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead]
  | .bytes bs => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead]
  | .text bs => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead]
  | .array xs => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead, encodeList_eq_encList xs]
  | .map kvs => by simp only [encode, Cbor.Spec.enc, head_eq_itemHead, encodePairs_eq_encPairs kvs]
  | .vfalse => rfl
  | .vtrue => rfl
  | .vnull => rfl

theorem encodeList_eq_encList : ∀ xs : List Value, encodeList xs = Cbor.Spec.encList xs
  | [] => rfl
  | x :: xs => by simp only [encodeList, Cbor.Spec.encList, encode_eq_enc x, encodeList_eq_encList xs]

theorem encodePairs_eq_encPairs : ∀ kvs : List (Value × Value), encodePairs kvs = Cbor.Spec.encPairs kvs
  | [] => rfl
  | (k, v) :: kvs => by
    simp only [encodePairs, Cbor.Spec.encPairs, encode_eq_enc k, encode_eq_enc v,
      encodePairs_eq_encPairs kvs]
end

end Cbor

/-- `Cbor.Spec.cbor_encode_spec`. -/
theorem Cbor.Spec.cbor_encode_spec (v : Cbor.Value) : Cbor.encode v = Cbor.Spec.enc v :=
  Cbor.encode_eq_enc v
