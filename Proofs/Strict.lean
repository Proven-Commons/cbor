/-
  The decoder is strict, for every input of each shape: non-preferred
  arguments, out-of-slice items at the top or inside a container, and
  input cut short inside an item are all turned away.
-/

import Proofs.Cbor
import Proofs.Encode
import Proofs.RoundTrip

open Cbor

namespace Cbor

/-! ## Reading an argument written by `Spec.netBytes` -/

theorem netBytes_length (k x : Nat) : (Spec.netBytes k x).length = k := by
  rw [← beBytes_eq_netBytes, beBytes_length]

theorem readBe_netBytes (k x : Nat) (h : x < 256 ^ k) : readBe (Spec.netBytes k x) = x := by
  rw [← beBytes_eq_netBytes]
  exact readBe_beBytes k x h

theorem readArg_24 (c : UInt8) (r : List UInt8) :
    readArg 24 (c :: r) = if c.toNat ≥ 24 then some (c.toNat, r) else none := by
  rw [readArg.eq_def, ite_eq_right (by decide), ite_eq_left rfl]

theorem readArg_25 (l : List UInt8) :
    readArg 25 l = if (l.take 2).length = 2 ∧ readBe (l.take 2) ≥ 2 ^ 8
      then some (readBe (l.take 2), l.drop 2) else none := by
  rw [readArg.eq_def, ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl,
    List.splitAt_eq]

theorem readArg_26 (l : List UInt8) :
    readArg 26 l = if (l.take 4).length = 4 ∧ readBe (l.take 4) ≥ 2 ^ 16
      then some (readBe (l.take 4), l.drop 4) else none := by
  rw [readArg.eq_def, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_left rfl, List.splitAt_eq]

theorem readArg_27 (l : List UInt8) :
    readArg 27 l = if (l.take 8).length = 8 ∧ readBe (l.take 8) ≥ 2 ^ 32
      then some (readBe (l.take 8), l.drop 8) else none := by
  rw [readArg.eq_def, ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, List.splitAt_eq]

/-- The decoder turns away an item whose initial byte is not in major
    type 6 or 7 and whose argument `readArg` turns away. -/
theorem decode_none_of_readArg (b : UInt8) (rest : List UInt8) (h7 : ¬ b.toNat / 32 = 7)
    (h6 : ¬ b.toNat / 32 = 6) (hr : readArg (b.toNat % 32) rest = none) :
    decode (b :: rest) = none := by
  unfold decode
  rw [List.length_cons, decodeFuel_cons, ite_eq_right h7, ite_eq_right h6, hr]

/-- The initial byte for major type `mt` and additional information
    `ai`. -/
theorem headByte (mt ai : Nat) (hmt : mt ≤ 5) (hai : ai < 32) :
    ((mt * 32 + ai).toUInt8).toNat / 32 = mt ∧ ((mt * 32 + ai).toUInt8).toNat % 32 = ai := by
  rw [toNat_toUInt8, Nat.mod_eq_of_lt (by omega)]
  omega

end Cbor

/-- `Spec.cbor_rejects_nonpreferred`. -/
theorem Spec.cbor_rejects_nonpreferred (mt x : Nat) (rest : List UInt8) (hmt : mt ≤ 5) :
    (x < 24 → decode ((mt * 32 + 24).toUInt8 :: Spec.netBytes 1 x ++ rest) = none) ∧
    (x < 2 ^ 8 → decode ((mt * 32 + 25).toUInt8 :: Spec.netBytes 2 x ++ rest) = none) ∧
    (x < 2 ^ 16 → decode ((mt * 32 + 26).toUInt8 :: Spec.netBytes 4 x ++ rest) = none) ∧
    (x < 2 ^ 32 → decode ((mt * 32 + 27).toUInt8 :: Spec.netBytes 8 x ++ rest) = none) := by
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨h1, h2⟩ := headByte mt 24 hmt (by decide)
    rw [List.cons_append]
    apply decode_none_of_readArg _ _ (by omega) (by omega)
    rw [h2]
    simp only [Spec.netBytes, List.cons_append, List.nil_append]
    rw [readArg_24, ite_eq_right]
    rw [toNat_toUInt8]
    omega
  · obtain ⟨h1, h2⟩ := headByte mt 25 hmt (by decide)
    rw [List.cons_append]
    apply decode_none_of_readArg _ _ (by omega) (by omega)
    rw [h2, readArg_25, List.take_left' (netBytes_length 2 x),
      readBe_netBytes 2 x (by omega), ite_eq_right]
    omega
  · obtain ⟨h1, h2⟩ := headByte mt 26 hmt (by decide)
    rw [List.cons_append]
    apply decode_none_of_readArg _ _ (by omega) (by omega)
    rw [h2, readArg_26, List.take_left' (netBytes_length 4 x),
      readBe_netBytes 4 x (by omega), ite_eq_right]
    omega
  · obtain ⟨h1, h2⟩ := headByte mt 27 hmt (by decide)
    rw [List.cons_append]
    apply decode_none_of_readArg _ _ (by omega) (by omega)
    rw [h2, readArg_27, List.take_left' (netBytes_length 8 x),
      readBe_netBytes 8 x (by omega), ite_eq_right]
    omega

namespace Cbor

/-! ## Out-of-slice items, at the top and inside containers -/

/-- The reader of one item turns away an out-of-slice initial byte,
    whatever its fuel. -/
theorem decodeFuel_outOfSlice (F : Nat) (b : UInt8) (rest : List UInt8)
    (hb : Spec.outOfSlice b = true) : decodeFuel F (b :: rest) = none := by
  simp [Spec.outOfSlice] at hb
  have hlt : b.toNat < 256 := b.toBitVec.isLt
  cases F with
  | zero => rfl
  | succ F =>
    rw [decodeFuel_cons]
    by_cases h7 : b.toNat / 32 = 7
    · rw [ite_eq_left h7, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
    · rw [ite_eq_right h7]
      by_cases h6 : b.toNat / 32 = 6
      · rw [ite_eq_left h6]
      · rw [ite_eq_right h6, readArg_none_of_ge_28 (by omega)]

theorem wfAll_mem {xs : List Value} (h : Value.wfAll xs = true) {x : Value} (hx : x ∈ xs) :
    x.wf = true := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [Value.wfAll, Bool.and_eq_true] at h
    cases hx with
    | head => exact h.1
    | tail _ hm => exact ih h.2 hm

theorem wfPairs_mem {kvs : List (Value × Value)} (h : Value.wfPairs kvs = true)
    {kv : Value × Value} (hkv : kv ∈ kvs) : kv.1.wf = true ∧ kv.2.wf = true := by
  induction kvs with
  | nil => cases hkv
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [Value.wfPairs, Bool.and_eq_true] at h
    cases hkv with
    | head => exact h.1
    | tail _ hm => exact ih h.2 hm

theorem depth_le_depthList {xs : List Value} {x : Value} (hx : x ∈ xs) :
    x.depth ≤ Value.depthList xs := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    simp only [Value.depthList]
    cases hx with
    | head => omega
    | tail _ hm => have := ih hm; omega

theorem depth_le_depthPairs {kvs : List (Value × Value)} {kv : Value × Value}
    (hkv : kv ∈ kvs) : kv.1.depth ≤ Value.depthPairs kvs ∧ kv.2.depth ≤ Value.depthPairs kvs := by
  induction kvs with
  | nil => cases hkv
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp only [Value.depthPairs]
    cases hkv with
    | head => dsimp only; omega
    | tail _ hm => have := ih hm; omega

/-- After items it reads back, the reader of `n` items fails where the
    reader of the rest fails. -/
theorem decodeItems_skip (dec : List UInt8 → Option (Value × List UInt8)) (xs : List Value)
    (s : List UInt8) (j : Nat) (hdec : ∀ x ∈ xs, ∀ r, dec (encode x ++ r) = some (x, r))
    (hj : decodeItems dec j s = none) :
    decodeItems dec (xs.length + j) (encodeList xs ++ s) = none := by
  induction xs with
  | nil => simpa [encodeList] using hj
  | cons x xs ih =>
    rw [List.length_cons, show xs.length + 1 + j = (xs.length + j) + 1 by omega, decodeItems_succ,
      encodeList, List.append_assoc, hdec x List.mem_cons_self]
    show (match decodeItems dec (xs.length + j) (encodeList xs ++ s) with
      | none => none
      | some (ys, r') => some (x :: ys, r')) = none
    rw [ih (fun y hy => hdec y (List.mem_cons_of_mem x hy))]

/-- After pairs it reads back, the reader of `n` pairs fails where the
    reader of the rest fails. -/
theorem decodePairs_skip (dec : List UInt8 → Option (Value × List UInt8))
    (kvs : List (Value × Value)) (s : List UInt8) (j : Nat)
    (hdec : ∀ kv ∈ kvs, ∀ r, dec (encode kv.1 ++ r) = some (kv.1, r) ∧
      dec (encode kv.2 ++ r) = some (kv.2, r))
    (hj : decodePairs dec j s = none) :
    decodePairs dec (kvs.length + j) (encodePairs kvs ++ s) = none := by
  induction kvs with
  | nil => simpa [encodePairs] using hj
  | cons kv kvs ih =>
    obtain ⟨k, v⟩ := kv
    have hk := (hdec (k, v) List.mem_cons_self (encode v ++ (encodePairs kvs ++ s))).1
    have hv := (hdec (k, v) List.mem_cons_self (encodePairs kvs ++ s)).2
    rw [List.length_cons, show kvs.length + 1 + j = (kvs.length + j) + 1 by omega,
      decodePairs_succ, encodePairs, List.append_assoc, List.append_assoc, hk]
    show (match dec (encode v ++ (encodePairs kvs ++ s)) with
      | none => none
      | some (v', r') =>
        match decodePairs dec (kvs.length + j) r' with
        | none => none
        | some (kvs', r'') => some ((k, v') :: kvs', r'')) = none
    rw [hv]
    show (match decodePairs dec (kvs.length + j) (encodePairs kvs ++ s) with
      | none => none
      | some (kvs', r'') => some ((k, v) :: kvs', r'')) = none
    rw [ih (fun kv hkv => hdec kv (List.mem_cons_of_mem _ hkv))]

/-- The decoder, on a container head of `n` items or pairs followed by
    `body`: it fails when the container's reader fails. -/
theorem decode_container_none (mt n : Nat) (body : List UInt8) (hmt : mt = 4 ∨ mt = 5)
    (hn : n < 2 ^ 64)
    (hitems : (mt = 4 → decodeItems (decodeFuel (head mt n ++ body).length) n body = none) ∧
      (mt = 5 → decodePairs (decodeFuel (head mt n ++ body).length) n body = none)) :
    decode (head mt n ++ body) = none := by
  obtain ⟨hi, hp⟩ := hitems
  unfold decode
  rw [decodeFuel_head mt n body (by omega) hn]
  rcases hmt with rfl | rfl
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left rfl, hi rfl]
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl, hp rfl]

end Cbor

/-- `Spec.cbor_rejects_nested_out_of_slice`. -/
theorem Spec.cbor_rejects_nested_out_of_slice (b : UInt8) (rest : List UInt8) (n : Nat)
    (xs : List Value) (kvs : List (Value × Value)) (k : Value)
    (hb : Spec.outOfSlice b = true) (hn : n < 2 ^ 64) (hxs : Value.wfAll xs = true)
    (hkvs : Value.wfPairs kvs = true) (hk : k.wf = true) :
    decode (b :: rest) = none ∧
    (xs.length < n → decode (Spec.itemHead 4 n ++ Spec.encList xs ++ b :: rest) = none) ∧
    (kvs.length < n → decode (Spec.itemHead 5 n ++ Spec.encPairs kvs ++ b :: rest) = none) ∧
    (kvs.length < n →
      decode (Spec.itemHead 5 n ++ Spec.encPairs kvs ++ Spec.enc k ++ b :: rest) = none) := by
  have hbad : ∀ F, decodeFuel F (b :: rest) = none := fun F => decodeFuel_outOfSlice F b rest hb
  refine ⟨?_, fun hlt => ?_, fun hlt => ?_, fun hlt => ?_⟩
  · unfold decode
    rw [hbad]
  · obtain ⟨j, rfl⟩ : ∃ j, n = xs.length + (j + 1) := ⟨n - xs.length - 1, by omega⟩
    rw [← head_eq_itemHead, ← encodeList_eq_encList, List.append_assoc]
    apply decode_container_none 4 _ _ (Or.inl rfl) hn
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    have hpos := head_length_pos 4 (xs.length + (j + 1))
    have hdl := (depthLen (Value.depthList xs)).2.1 xs (Nat.le_refl _)
    generalize hF : (head 4 (xs.length + (j + 1)) ++ (encodeList xs ++ b :: rest)).length = F
    simp only [List.length_append, List.length_cons] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    apply decodeItems_skip _ xs _ (j + 1)
    · intro x hx r
      exact (rtAll F').1 x r (wfAll_mem hxs hx) (by have := depth_le_depthList hx; omega)
    · rw [decodeItems_succ, hbad]
  · obtain ⟨j, rfl⟩ : ∃ j, n = kvs.length + (j + 1) := ⟨n - kvs.length - 1, by omega⟩
    rw [← head_eq_itemHead, ← encodePairs_eq_encPairs, List.append_assoc]
    apply decode_container_none 5 _ _ (Or.inr rfl) hn
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    have hpos := head_length_pos 5 (kvs.length + (j + 1))
    have hdp := (depthLen (Value.depthPairs kvs)).2.2 kvs (Nat.le_refl _)
    generalize hF : (head 5 (kvs.length + (j + 1)) ++ (encodePairs kvs ++ b :: rest)).length = F
    simp only [List.length_append, List.length_cons] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    apply decodePairs_skip _ kvs _ (j + 1)
    · intro kv hkv r
      obtain ⟨hwk, hwv⟩ := wfPairs_mem hkvs hkv
      obtain ⟨hdk, hdv⟩ := depth_le_depthPairs hkv
      exact ⟨(rtAll F').1 kv.1 r hwk (by omega), (rtAll F').1 kv.2 r hwv (by omega)⟩
    · rw [decodePairs_succ, hbad]
  · obtain ⟨j, rfl⟩ : ∃ j, n = kvs.length + (j + 1) := ⟨n - kvs.length - 1, by omega⟩
    rw [← head_eq_itemHead, ← encodePairs_eq_encPairs, ← encode_eq_enc, List.append_assoc,
      List.append_assoc]
    apply decode_container_none 5 _ _ (Or.inr rfl) hn
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    have hpos := head_length_pos 5 (kvs.length + (j + 1))
    have hdp := (depthLen (Value.depthPairs kvs)).2.2 kvs (Nat.le_refl _)
    have hdk := depth_le_length k
    generalize hF : (head 5 (kvs.length + (j + 1)) ++
      (encodePairs kvs ++ (encode k ++ b :: rest))).length = F
    simp only [List.length_append, List.length_cons] at hF
    obtain ⟨F', rfl⟩ : ∃ F', F = F' + 1 := ⟨F - 1, by omega⟩
    apply decodePairs_skip _ kvs _ (j + 1)
    · intro kv hkv r
      obtain ⟨hwk, hwv⟩ := wfPairs_mem hkvs hkv
      obtain ⟨hdk', hdv'⟩ := depth_le_depthPairs hkv
      exact ⟨(rtAll F').1 kv.1 r hwk (by omega), (rtAll F').1 kv.2 r hwv (by omega)⟩
    · rw [decodePairs_succ, (rtAll F').1 k (b :: rest) hk (by omega)]
      show (match decodeFuel (F' + 1) (b :: rest) with
        | none => none
        | some (v', r') =>
          match decodePairs (decodeFuel (F' + 1)) j r' with
          | none => none
          | some (kvs', r'') => some ((k, v') :: kvs', r'')) = none
      rw [hbad]

/-! ## Input cut short inside an item -/

/-- `Spec.cbor_rejects_truncated`. -/
theorem Spec.cbor_rejects_truncated (v : Value) (pre post : List UInt8) (hv : v.wf = true)
    (h : pre ++ post = Spec.enc v) (hpost : post ≠ []) : decode pre = none := by
  rw [← encode_eq_enc] at h
  cases hd : decode pre with
  | none => rfl
  | some w =>
    exfalso
    obtain ⟨hw, hpre⟩ := encode_decode pre w hd
    subst hpre
    have hlen : (encode w).length ≤ (encode v).length := by
      rw [← h, List.length_append]; omega
    have h1 := (rtAll (encode v).length).1 v [] hv (depth_le_length v)
    have h2 := (rtAll (encode v).length).1 w post hw
      (by have := depth_le_length w; omega)
    rw [List.append_nil] at h1
    rw [h, h1] at h2
    injection h2 with h3
    injection h3 with _ h4
    exact hpost h4.symm
