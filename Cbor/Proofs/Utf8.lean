/-
  The decoder's UTF-8 check, `Cbor.Utf8.valid`, is the grammar of
  RFC 3629, section 4, as `Cbor.Spec.Utf8.wellFormed` writes it.

  `valid_step` shows that one step of the validator, which looks at the
  first byte to pick a row, gives the same answer as trying every row
  of the grammar: the rows' first bytes do not overlap. Induction on
  the length then gives the equality for every byte list.
-/

import Cbor
import Cbor.Spec.Defs

namespace Cbor.Utf8

/-- One step of the validator: the first character matches one row of
    the grammar, and the rest is valid. -/
theorem valid_step (a : UInt8) (rest : List UInt8) :
    valid (a :: rest) =
      Cbor.Spec.Utf8.rows.any (fun row => Cbor.Spec.Utf8.fits row ((a :: rest).take row.length) &&
        valid ((a :: rest).drop row.length)) := by
  have ha : a.toNat < 256 := a.toBitVec.isLt
  have hcls : a.toNat ≤ 0x7F ∨ (0x80 ≤ a.toNat ∧ a.toNat ≤ 0xC1) ∨
      (0xC2 ≤ a.toNat ∧ a.toNat ≤ 0xDF) ∨ a.toNat = 0xE0 ∨ (0xE1 ≤ a.toNat ∧ a.toNat ≤ 0xEC) ∨
      a.toNat = 0xED ∨ (0xEE ≤ a.toNat ∧ a.toNat ≤ 0xEF) ∨ a.toNat = 0xF0 ∨
      (0xF1 ≤ a.toNat ∧ a.toNat ≤ 0xF3) ∨ a.toNat = 0xF4 ∨ 0xF5 ≤ a.toNat := by omega
  rw [valid.eq_def (a :: rest)]
  rcases rest with _ | ⟨b, _ | ⟨c, _ | ⟨d, r⟩⟩⟩ <;>
    simp only [Cbor.Spec.Utf8.rows, List.any_cons, List.any_nil, List.length_cons, List.length_nil,
      List.take, List.drop, Cbor.Spec.Utf8.fits, cont] <;>
    rcases hcls with h | h | h | h | h | h | h | h | h | h | h <;>
    simp (disch := omega) only [decide_eq_true, decide_eq_false, ite_eq_left, ite_eq_right,
      Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.or_false,
      Bool.false_or, Bool.and_assoc]

theorem any_congr_mem {α : Type} {l : List α} {p q : α → Bool} (h : ∀ x ∈ l, p x = q x) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

/-- Every row of the grammar is at least one byte long. -/
theorem rows_nonempty : ∀ row ∈ Cbor.Spec.Utf8.rows, 1 ≤ row.length := by
  have h : Cbor.Spec.Utf8.rows.all (fun row => decide (1 ≤ row.length)) = true := by decide
  intro row hrow
  exact of_decide_eq_true (List.all_eq_true.1 h row hrow)

/-- With enough room for one character per byte, splitting into
    characters is the validator. -/
theorem octets_eq_valid : ∀ n bs, bs.length ≤ n → Cbor.Spec.Utf8.octets n bs = valid bs := by
  intro n
  induction n with
  | zero =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons a rest => simp at h
  | succ n ih =>
    intro bs h
    cases bs with
    | nil => rfl
    | cons a rest =>
      rw [valid_step]
      show (Cbor.Spec.Utf8.rows.any fun row => Cbor.Spec.Utf8.fits row ((a :: rest).take row.length) &&
        Cbor.Spec.Utf8.octets n ((a :: rest).drop row.length)) = _
      apply any_congr_mem
      intro row hrow
      have h1 := rows_nonempty row hrow
      rw [ih _ (by rw [List.length_drop, List.length_cons] at *; omega)]

/-- The validator is the RFC 3629 grammar. -/
theorem valid_eq_wellFormed (bs : List UInt8) : valid bs = Cbor.Spec.Utf8.wellFormed bs :=
  (octets_eq_valid bs.length bs (Nat.le_refl _)).symm

end Cbor.Utf8

/-- `Cbor.Spec.cbor_utf8_valid_eq`. -/
theorem Cbor.Spec.cbor_utf8_valid_eq (bs : List UInt8) :
    Cbor.Utf8.valid bs = Cbor.Spec.Utf8.wellFormed bs :=
  Cbor.Utf8.valid_eq_wellFormed bs
