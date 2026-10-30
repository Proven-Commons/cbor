/-
  The round trip: decoding an encoding returns the same item.
-/

import Cbor
import Cbor.Spec.Defs
import Cbor.Proofs.Utf8

open Cbor

namespace Cbor

/-! ## List utilities -/

/-- Induction peeling from the right. -/
theorem rightInduction {α : Type _} {P : List α → Prop} (h0 : P [])
    (h1 : ∀ a l, P l → P (l ++ [a])) (w : List α) : P w := by
  have key : ∀ w : List α, P w.reverse := by
    intro w
    induction w with
    | nil => exact h0
    | cons a l ih => rw [List.reverse_cons]; exact h1 _ _ ih
  have h := key w.reverse
  rwa [List.reverse_reverse] at h

/-! ## `readBe` and `beBytes` are inverse -/

theorem readBeFoldl (init : Nat) (w : List UInt8) :
    w.foldl (fun a b => a * 256 + b.toNat) init = init * 256 ^ w.length + readBe w := by
  induction w generalizing init with
  | nil => simp [readBe]
  | cons b rest ih =>
    rw [List.foldl_cons, ih (init * 256 + b.toNat), List.length_cons, Nat.pow_succ]
    have e2 : readBe (b :: rest) = b.toNat * 256 ^ rest.length + readBe rest := by
      rw [readBe, List.foldl_cons, ih (0 * 256 + b.toNat)]
      simp
    rw [e2, Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (256 ^ rest.length) 256,
      ← Nat.mul_assoc, Nat.add_assoc]

theorem readBe_cons (b : UInt8) (rest : List UInt8) :
    readBe (b :: rest) = b.toNat * 256 ^ rest.length + readBe rest := by
  rw [readBe, List.foldl_cons, readBeFoldl]; simp

theorem readBe_append_single (w : List UInt8) (b : UInt8) :
    readBe (w ++ [b]) = readBe w * 256 + b.toNat := by
  simp [readBe, List.foldl_append]

theorem readBe_lt_pow (w : List UInt8) : readBe w < 256 ^ w.length := by
  induction w using rightInduction with
  | h0 => simp [readBe]
  | h1 a l ih =>
    rw [List.length_append, List.length_singleton, readBe_append_single, Nat.pow_succ]
    have hb : a.toNat < 256 := a.toBitVec.isLt
    have hle : readBe l * 256 + 256 ≤ 256 ^ l.length * 256 := by
      have h2 : readBe l + 1 ≤ 256 ^ l.length := ih
      calc readBe l * 256 + 256 = (readBe l + 1) * 256 := by omega
        _ ≤ 256 ^ l.length * 256 := Nat.mul_le_mul h2 (Nat.le_refl 256)
    omega

theorem beBytes_length (n x : Nat) : (beBytes n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem toUInt8_toNat (b : UInt8) : (b.toNat).toUInt8 = b := by
  apply (UInt8.toNat_inj).1
  have hb : b.toNat < 256 := b.toBitVec.isLt
  have : ((b.toNat).toUInt8).toNat = b.toNat % 256 := by simp [Nat.toUInt8]
  rw [this, Nat.mod_eq_of_lt hb]

theorem readBe_beBytes (n x : Nat) (h : x < 256 ^ n) : readBe (beBytes n x) = x := by
  induction n generalizing x with
  | zero => simp at h; simp [beBytes, readBe, show x = 0 by omega]
  | succ n ih =>
    rw [beBytes, readBe_append_single]
    rw [Nat.pow_succ] at h
    rw [ih (x / 256) ((Nat.div_lt_iff_lt_mul (k := 256) (x := x) (y := 256 ^ n)
      (by decide : (0:Nat) < 256)).mpr h)]
    have hmod : ((x % 256).toUInt8).toNat = x % 256 := by
      have hlt : x % 256 < 256 := Nat.mod_lt _ (by decide)
      have : ((x % 256).toUInt8).toNat = (x % 256) % 256 := by simp [Nat.toUInt8]
      rw [this, Nat.mod_eq_of_lt hlt]
    rw [hmod, Nat.mul_comm (x / 256) 256]
    exact Nat.div_add_mod x 256

theorem beBytes_readBe (w : List UInt8) : beBytes w.length (readBe w) = w := by
  induction w using rightInduction with
  | h0 => rfl
  | h1 a l ih =>
    rw [List.length_append, List.length_singleton, readBe_append_single, beBytes]
    have hb : a.toNat < 256 := a.toBitVec.isLt
    have hdiv : (readBe l * 256 + a.toNat) / 256 = readBe l := by
      rw [Nat.mul_comm (readBe l) 256, Nat.mul_add_div (by decide : (0:Nat) < 256),
        Nat.div_eq_of_lt hb, Nat.add_zero]
    have hmod : (readBe l * 256 + a.toNat) % 256 = a.toNat := by
      rw [Nat.mul_comm (readBe l) 256, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
    rw [hdiv, ih, hmod, toUInt8_toNat]

/-! ## Parsing a head written by `head` -/

theorem head_parse (mt arg : Nat) (rest : List UInt8) (hmt : mt ≤ 5) (harg : arg < 2 ^ 64) :
    ∃ b tail, head mt arg = b :: tail ∧ b.toNat / 32 = mt ∧ b.toNat % 32 ≤ 27 ∧
      readArg (b.toNat % 32) (tail ++ rest) = some (arg, rest) := by
  have hmod256 : ∀ k : UInt8, k.toNat ≤ 27 →
      ((mt * 32).toUInt8 + k).toNat = mt * 32 + k.toNat := by
    intro k hk
    have hb : mt * 32 < 256 := by
      have := Nat.mul_le_mul hmt (Nat.le_refl 32); omega
    have hm : ((mt * 32).toUInt8).toNat = mt * 32 % 256 := by simp [Nat.toUInt8]
    rw [UInt8.toNat_add, hm, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (by omega)]
  have hdiv : ∀ k : UInt8, k.toNat ≤ 27 → ((mt * 32).toUInt8 + k).toNat / 32 = mt := by
    intro k hk
    rw [hmod256 k hk, Nat.mul_comm mt 32, Nat.mul_add_div (by decide : (32:Nat) > 0),
      Nat.div_eq_of_lt (by omega), Nat.add_zero]
  have hmod : ∀ k : UInt8, k.toNat ≤ 27 → ((mt * 32).toUInt8 + k).toNat % 32 = k.toNat := by
    intro k hk
    rw [hmod256 k hk, Nat.mul_comm mt 32, Nat.mul_add_mod,
      Nat.mod_eq_of_lt (by omega)]
  have htk : ∀ n : Nat, List.take n (beBytes n arg) = beBytes n arg := by
    intro n
    have h := List.take_length (l := beBytes n arg)
    rw [beBytes_length] at h
    exact h
  have hdr : ∀ n : Nat, List.drop n (beBytes n arg) = [] := by
    intro n
    have h := List.drop_length (l := beBytes n arg)
    rw [beBytes_length] at h
    exact h
  unfold head
  by_cases h1 : arg < 24
  · rw [ite_eq_left h1]
    have e1 : (arg.toUInt8).toNat = arg := by
      have : (arg.toUInt8).toNat = arg % 256 := by simp [Nat.toUInt8]
      rw [this, Nat.mod_eq_of_lt (by omega)]
    refine ⟨(mt * 32).toUInt8 + arg.toUInt8, [], rfl, hdiv _ (by rw [e1]; omega),
      ?_, ?_⟩
    · rw [hmod _ (by rw [e1]; omega), e1]; omega
    · rw [hmod _ (by rw [e1]; omega), e1]
      simp only [readArg, List.nil_append]
      rw [ite_eq_left (by omega : arg ≤ 23)]
  · rw [ite_eq_right h1]
    by_cases h2 : arg ≤ 0xFF
    · rw [ite_eq_left h2]
      have e2 : (arg.toUInt8).toNat = arg := by
        have : (arg.toUInt8).toNat = arg % 256 := by simp [Nat.toUInt8]
        rw [this, Nat.mod_eq_of_lt (by omega)]
      refine ⟨(mt * 32).toUInt8 + 24, [arg.toUInt8], rfl,
        hdiv _ (by decide), ?_, ?_⟩
      · rw [hmod _ (by decide : (24:UInt8).toNat ≤ 27)]; decide
      · rw [hmod _ (by decide : (24:UInt8).toNat ≤ 27)]
        change readArg 24 (arg.toUInt8 :: rest) = some (arg, rest)
        rw [Cbor.readArg.eq_def, ite_eq_right (by decide : ¬(24:Nat) ≤ 23), ite_eq_left rfl]
        show (if (arg.toUInt8).toNat ≥ 24 then some ((arg.toUInt8).toNat, rest)
          else none) = some (arg, rest)
        rw [e2, ite_eq_left (by omega : arg ≥ 24)]
    · rw [ite_eq_right h2]
      by_cases h3 : arg ≤ 0xFFFF
      · rw [ite_eq_left h3]
        refine ⟨(mt * 32).toUInt8 + 25, beBytes 2 arg, rfl,
          hdiv _ (by decide), ?_, ?_⟩
        · rw [hmod _ (by decide : (25:UInt8).toNat ≤ 27)]; decide
        · rw [hmod _ (by decide : (25:UInt8).toNat ≤ 27)]
          have hb2 : arg < 65536 := by omega
          change readArg 25 (beBytes 2 arg ++ rest) = some (arg, rest)
          rw [Cbor.readArg.eq_def, ite_eq_right (by decide : ¬(25:Nat) ≤ 23),
            ite_eq_right (by decide : ¬(25:Nat) = 24), ite_eq_left rfl, List.splitAt_eq]
          show (if (List.take 2 (beBytes 2 arg ++ rest)).length = 2 ∧
                readBe (List.take 2 (beBytes 2 arg ++ rest)) ≥ 2 ^ 8
              then some (readBe (List.take 2 (beBytes 2 arg ++ rest)),
                List.drop 2 (beBytes 2 arg ++ rest)) else none) = some (arg, rest)
          rw [List.take_append_of_le_length (by simp [beBytes_length]), htk 2,
            readBe_beBytes 2 arg hb2,
            List.drop_append_of_le_length (by simp [beBytes_length]), hdr 2,
            List.nil_append, ite_eq_left ⟨by rw [beBytes_length], by omega⟩]
      · rw [ite_eq_right h3]
        by_cases h4 : arg ≤ 0xFFFFFFFF
        · rw [ite_eq_left h4]
          refine ⟨(mt * 32).toUInt8 + 26, beBytes 4 arg, rfl,
            hdiv _ (by decide), ?_, ?_⟩
          · rw [hmod _ (by decide : (26:UInt8).toNat ≤ 27)]; decide
          · rw [hmod _ (by decide : (26:UInt8).toNat ≤ 27)]
            have hb4 : arg < 4294967296 := by omega
            change readArg 26 (beBytes 4 arg ++ rest) = some (arg, rest)
            rw [Cbor.readArg.eq_def, ite_eq_right (by decide : ¬(26:Nat) ≤ 23),
              ite_eq_right (by decide : ¬(26:Nat) = 24), ite_eq_right (by decide : ¬(26:Nat) = 25),
              ite_eq_left rfl, List.splitAt_eq]
            show (if (List.take 4 (beBytes 4 arg ++ rest)).length = 4 ∧
                  readBe (List.take 4 (beBytes 4 arg ++ rest)) ≥ 2 ^ 16
                then some (readBe (List.take 4 (beBytes 4 arg ++ rest)),
                  List.drop 4 (beBytes 4 arg ++ rest)) else none) = some (arg, rest)
            rw [List.take_append_of_le_length (by simp [beBytes_length]), htk 4,
              readBe_beBytes 4 arg hb4,
              List.drop_append_of_le_length (by simp [beBytes_length]), hdr 4,
              List.nil_append, ite_eq_left ⟨by rw [beBytes_length], by omega⟩]
        · rw [ite_eq_right h4]
          have hb : arg < 256 ^ 8 := by
            rw [show (256:Nat)^8 = 18446744073709551616 from rfl]
            have harg' : arg < 18446744073709551616 := harg
            omega
          refine ⟨(mt * 32).toUInt8 + 27, beBytes 8 arg, rfl,
            hdiv _ (by decide), ?_, ?_⟩
          · rw [hmod _ (by decide : (27:UInt8).toNat ≤ 27)]; decide
          · rw [hmod _ (by decide : (27:UInt8).toNat ≤ 27)]
            change readArg 27 (beBytes 8 arg ++ rest) = some (arg, rest)
            rw [Cbor.readArg.eq_def, ite_eq_right (by decide : ¬(27:Nat) ≤ 23),
              ite_eq_right (by decide : ¬(27:Nat) = 24), ite_eq_right (by decide : ¬(27:Nat) = 25),
              ite_eq_right (by decide : ¬(27:Nat) = 26), List.splitAt_eq]
            show (if (List.take 8 (beBytes 8 arg ++ rest)).length = 8 ∧
                  readBe (List.take 8 (beBytes 8 arg ++ rest)) ≥ 2 ^ 32
                then some (readBe (List.take 8 (beBytes 8 arg ++ rest)),
                  List.drop 8 (beBytes 8 arg ++ rest)) else none) = some (arg, rest)
            rw [List.take_append_of_le_length (by simp [beBytes_length]), htk 8,
              readBe_beBytes 8 arg hb,
              List.drop_append_of_le_length (by simp [beBytes_length]), hdr 8,
              List.nil_append, ite_eq_left ⟨by rw [beBytes_length], by omega⟩]


theorem head_length_pos (mt arg : Nat) : 1 ≤ (head mt arg).length := by
  unfold head
  dsimp only
  by_cases h1 : arg < 24
  · rw [ite_eq_left h1]; simp
  · by_cases h2 : arg ≤ 255
    · rw [ite_eq_right h1, ite_eq_left h2]; simp
    · by_cases h3 : arg ≤ 65535
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]; simp [beBytes_length]
      · by_cases h4 : arg ≤ 4294967295
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]; simp [beBytes_length]
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]; simp [beBytes_length]

end Cbor

/-! ## Round trip: decoding an encoding gives the item back -/

/-- The cons equation of the decoder, with the head lets inlined. -/
theorem decodeFuel_cons (F : Nat) (b : UInt8) (rest : List UInt8) :
    decodeFuel (F + 1) (b :: rest) =
      (if b.toNat / 32 = 7 then
        if b.toNat = 0xf4 then some (.vfalse, rest)
        else if b.toNat = 0xf5 then some (.vtrue, rest)
        else if b.toNat = 0xf6 then some (.vnull, rest)
        else none
      else if b.toNat / 32 = 6 then none
      else match readArg (b.toNat % 32) rest with
        | none => none
        | some (arg, r) =>
          if b.toNat / 32 = 0 then some (.uint (UInt64.ofNat arg), r)
          else if b.toNat / 32 = 1 then some (.nint (UInt64.ofNat arg), r)
          else if b.toNat / 32 = 2 then
            if r.length < arg then none
            else some (.bytes (r.take arg), r.drop arg)
          else if b.toNat / 32 = 3 then
            if r.length < arg then none
            else if Utf8.valid (r.take arg) then some (.text (r.take arg), r.drop arg)
            else none
          else if b.toNat / 32 = 4 then
            match decodeItems (decodeFuel F) arg r with
            | some (xs, r') => some (.array xs, r')
            | none => none
          else if b.toNat / 32 = 5 then
            match decodePairs (decodeFuel F) arg r with
            | some (kvs, r') => some (.map kvs, r')
            | none => none
          else none) := rfl

theorem decodeItems_zero (dec : List UInt8 → Option (Value × List UInt8)) (bs : List UInt8) :
    decodeItems dec 0 bs = some ([], bs) := rfl

theorem decodeItems_succ (dec : List UInt8 → Option (Value × List UInt8)) (n : Nat)
    (bs : List UInt8) :
    decodeItems dec (n + 1) bs =
      match dec bs with
      | none => none
      | some (x, r) =>
        match decodeItems dec n r with
        | none => none
        | some (xs, r') => some (x :: xs, r') := rfl

theorem decodePairs_succ (dec : List UInt8 → Option (Value × List UInt8)) (n : Nat)
    (bs : List UInt8) :
    decodePairs dec (n + 1) bs =
      match dec bs with
      | none => none
      | some (k, r) =>
        match dec r with
        | none => none
        | some (v, r') =>
          match decodePairs dec n r' with
          | none => none
          | some (kvs, r'') => some ((k, v) :: kvs, r'') := rfl

/-- The decoder on an item head written by `head`, with major type at
    most 5: the head parses back to its major type and argument. -/
theorem decodeFuel_head (mt arg : Nat) (rest : List UInt8) (hmt : mt ≤ 5)
    (harg : arg < 2 ^ 64) (F : Nat) :
    decodeFuel (F + 1) (head mt arg ++ rest) =
      (if mt = 0 then some (.uint (UInt64.ofNat arg), rest)
      else if mt = 1 then some (.nint (UInt64.ofNat arg), rest)
      else if mt = 2 then
        if rest.length < arg then none
        else some (.bytes (rest.take arg), rest.drop arg)
      else if mt = 3 then
        if rest.length < arg then none
        else if Utf8.valid (rest.take arg) then some (.text (rest.take arg), rest.drop arg)
        else none
      else if mt = 4 then
        match decodeItems (decodeFuel F) arg rest with
        | some (xs, r) => some (.array xs, r)
        | none => none
      else if mt = 5 then
        match decodePairs (decodeFuel F) arg rest with
        | some (kvs, r) => some (.map kvs, r)
        | none => none
      else none) := by
  obtain ⟨b, tail, e, hb, _hmod, hrd⟩ := head_parse mt arg rest hmt harg
  rw [e, show (b :: tail) ++ rest = b :: (tail ++ rest) from rfl, decodeFuel_cons,
    hb, ite_eq_right (by omega : ¬(mt = 7)), ite_eq_right (by omega : ¬(mt = 6)), hrd]
/-- Every item has depth at least one. -/
theorem depth_pos (v : Value) : 1 ≤ v.depth := by
  cases v <;> simp only [Value.depth] <;> omega

/-- The depth of an item never exceeds the length of its encoding:
    each level of nesting takes at least one byte on the wire. -/
theorem depthLen : ∀ n : Nat,
    (∀ v, v.depth ≤ n → v.depth ≤ (encode v).length) ∧
    (∀ xs, Value.depthList xs ≤ n → Value.depthList xs ≤ (encodeList xs).length) ∧
    (∀ kvs, Value.depthPairs kvs ≤ n → Value.depthPairs kvs ≤ (encodePairs kvs).length) := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro v h
      have := depth_pos v
      omega
    · intro xs h
      cases xs with
      | nil => exact Nat.zero_le _
      | cons x xs =>
        simp only [Value.depthList] at h
        have := depth_pos x
        omega
    · intro kvs h
      cases kvs with
      | nil => exact Nat.zero_le _
      | cons kv kvs =>
        simp only [Value.depthPairs] at h
        have := depth_pos kv.1
        omega
  | succ n ih =>
    obtain ⟨ihv, ihl, ihp⟩ := ih
    have hv : ∀ v, v.depth ≤ n + 1 → v.depth ≤ (encode v).length := by
      intro v h
      cases v with
      | uint m =>
        simp only [Value.depth, encode]
        exact head_length_pos 0 m.toNat
      | nint m =>
        simp only [Value.depth, encode]
        exact head_length_pos 1 m.toNat
      | bytes bs =>
        simp only [Value.depth, encode, List.length_append]
        have := head_length_pos 2 bs.length
        omega
      | text bs =>
        simp only [Value.depth, encode, List.length_append]
        have := head_length_pos 3 bs.length
        omega
      | array xs =>
        simp only [Value.depth] at h ⊢
        have hdl : Value.depthList xs ≤ n := by omega
        have hrec := ihl xs hdl
        simp only [encode, List.length_append]
        have hh := head_length_pos 4 xs.length
        omega
      | map kvs =>
        simp only [Value.depth] at h ⊢
        have hdp : Value.depthPairs kvs ≤ n := by omega
        have hrec := ihp kvs hdp
        simp only [encode, List.length_append]
        have hh := head_length_pos 5 kvs.length
        omega
      | vfalse =>
        simp only [Value.depth, encode]
        decide
      | vtrue =>
        simp only [Value.depth, encode]
        decide
      | vnull =>
        simp only [Value.depth, encode]
        decide
      all_goals (intro ys hcon; exact Value.noConfusion hcon)
    have hl : ∀ xs, Value.depthList xs ≤ n + 1 →
        Value.depthList xs ≤ (encodeList xs).length := by
      intro xs
      induction xs with
      | nil => intro _; exact Nat.zero_le _
      | cons x xs ihx =>
        intro h
        simp only [Value.depthList] at h ⊢
        have hx : x.depth ≤ (encode x).length := hv x (by omega)
        have hxs : Value.depthList xs ≤ (encodeList xs).length := ihx (by omega)
        simp only [encodeList, List.length_append]
        omega
    have hp : ∀ kvs, Value.depthPairs kvs ≤ n + 1 →
        Value.depthPairs kvs ≤ (encodePairs kvs).length := by
      intro kvs
      induction kvs with
      | nil => intro _; exact Nat.zero_le _
      | cons kv kvs ihk =>
        intro h
        simp only [Value.depthPairs] at h ⊢
        have hk : kv.1.depth ≤ (encode kv.1).length := hv kv.1 (by omega)
        have hvv : kv.2.depth ≤ (encode kv.2).length := hv kv.2 (by omega)
        have hrest : Value.depthPairs kvs ≤ (encodePairs kvs).length := ihk (by omega)
        simp only [encodePairs, List.length_append]
        omega
    exact ⟨hv, hl, hp⟩

/-- The depth of an item never exceeds the length of its encoding. -/
theorem depth_le_length (v : Value) : v.depth ≤ (encode v).length :=
  (depthLen v.depth).1 v (Nat.le_refl _)

/-- The round trip, by induction on the fuel: decoding the encoding of
    a well-formed item gives the item and the rest back. -/
theorem rtAll : ∀ F : Nat,
    (∀ v rest, v.wf = true → v.depth ≤ F →
      decodeFuel (F + 1) (encode v ++ rest) = some (v, rest)) ∧
    (∀ xs rest, Value.wfAll xs = true → Value.depthList xs ≤ F →
      decodeItems (decodeFuel (F + 1)) xs.length (encodeList xs ++ rest) = some (xs, rest)) ∧
    (∀ kvs rest, Value.wfPairs kvs = true → Value.depthPairs kvs ≤ F →
      decodePairs (decodeFuel (F + 1)) kvs.length (encodePairs kvs ++ rest) = some (kvs, rest)) := by
  intro F
  induction F with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro v rest _ hdepth
      have := depth_pos v
      omega
    · intro xs rest _ hdepth
      cases xs with
      | nil => simp only [encodeList]; rfl
      | cons x xs =>
        simp only [Value.depthList] at hdepth
        have := depth_pos x
        omega
    · intro kvs rest _ hdepth
      cases kvs with
      | nil => simp only [encodePairs]; rfl
      | cons kv kvs =>
        simp only [Value.depthPairs] at hdepth
        have := depth_pos kv.1
        omega
  | succ F ih =>
    obtain ⟨ihv, ihl, ihp⟩ := ih
    have hv : ∀ v rest, v.wf = true → v.depth ≤ F + 1 →
        decodeFuel (F + 1 + 1) (encode v ++ rest) = some (v, rest) := by
      intro v rest hwf hdepth
      cases v with
      | uint n =>
        simp only [encode]
        rw [decodeFuel_head 0 n.toNat rest (by decide) (UInt64.toNat_lt n) (F + 1),
          ite_eq_left rfl, UInt64.ofNat_toNat]
      | nint n =>
        simp only [encode]
        rw [decodeFuel_head 1 n.toNat rest (by decide) (UInt64.toNat_lt n) (F + 1),
          ite_eq_right (by decide : ¬(1:Nat) = 0), ite_eq_left rfl, UInt64.ofNat_toNat]
      | bytes bs =>
        simp only [Value.wf] at hwf
        have hlen : bs.length < 2 ^ 64 := of_decide_eq_true hwf
        simp only [encode]
        rw [List.append_assoc,
          decodeFuel_head 2 bs.length (bs ++ rest) (by decide) hlen (F + 1),
          ite_eq_right (by decide : ¬(2:Nat) = 0), ite_eq_right (by decide : ¬(2:Nat) = 1), ite_eq_left rfl,
          ite_eq_right (by rw [List.length_append]; omega : ¬(bs ++ rest).length < bs.length),
          List.take_append_of_le_length (Nat.le_refl bs.length), List.take_length,
          List.drop_append_of_le_length (Nat.le_refl bs.length), List.drop_length,
          List.nil_append]
      | text bs =>
        simp only [Value.wf, Bool.and_eq_true] at hwf
        obtain ⟨hwfu, hlen⟩ := hwf
        have hval : Utf8.valid bs = true := by rw [Utf8.valid_eq_wellFormed]; exact hwfu
        have hlen' : bs.length < 2 ^ 64 := of_decide_eq_true hlen
        simp only [encode]
        rw [List.append_assoc,
          decodeFuel_head 3 bs.length (bs ++ rest) (by decide) hlen' (F + 1),
          ite_eq_right (by decide : ¬(3:Nat) = 0), ite_eq_right (by decide : ¬(3:Nat) = 1),
          ite_eq_right (by decide : ¬(3:Nat) = 2), ite_eq_left rfl,
          ite_eq_right (by rw [List.length_append]; omega : ¬(bs ++ rest).length < bs.length),
          List.take_append_of_le_length (Nat.le_refl bs.length), List.take_length,
          ite_eq_left hval,
          List.drop_append_of_le_length (Nat.le_refl bs.length), List.drop_length,
          List.nil_append]
      | array xs =>
        simp only [Value.wf, Bool.and_eq_true] at hwf
        obtain ⟨hlen, hwfA⟩ := hwf
        have hlen' : xs.length < 2 ^ 64 := of_decide_eq_true hlen
        simp only [Value.depth] at hdepth
        have hdep : Value.depthList xs ≤ F := by omega
        simp only [encode]
        rw [List.append_assoc,
          decodeFuel_head 4 xs.length (encodeList xs ++ rest) (by decide) hlen' (F + 1),
          ite_eq_right (by decide : ¬(4:Nat) = 0), ite_eq_right (by decide : ¬(4:Nat) = 1),
          ite_eq_right (by decide : ¬(4:Nat) = 2), ite_eq_right (by decide : ¬(4:Nat) = 3), ite_eq_left rfl,
          ihl xs rest hwfA hdep]
      | map kvs =>
        simp only [Value.wf, Bool.and_eq_true] at hwf
        obtain ⟨hlen, hwfP⟩ := hwf
        have hlen' : kvs.length < 2 ^ 64 := of_decide_eq_true hlen
        simp only [Value.depth] at hdepth
        have hdep : Value.depthPairs kvs ≤ F := by omega
        simp only [encode]
        rw [List.append_assoc,
          decodeFuel_head 5 kvs.length (encodePairs kvs ++ rest) (by decide) hlen' (F + 1),
          ite_eq_right (by decide : ¬(5:Nat) = 0), ite_eq_right (by decide : ¬(5:Nat) = 1),
          ite_eq_right (by decide : ¬(5:Nat) = 2), ite_eq_right (by decide : ¬(5:Nat) = 3),
          ite_eq_right (by decide : ¬(5:Nat) = 4), ite_eq_left rfl,
          ihp kvs rest hwfP hdep]
      | vfalse =>
        simp only [encode]
        show decodeFuel (F + 1 + 1) (0xf4 :: rest) = some (.vfalse, rest)
        rw [decodeFuel_cons, ite_eq_left (by decide : (0xf4 : UInt8).toNat / 32 = 7),
          ite_eq_left (by decide : (0xf4 : UInt8).toNat = 0xf4)]
      | vtrue =>
        simp only [encode]
        show decodeFuel (F + 1 + 1) (0xf5 :: rest) = some (.vtrue, rest)
        rw [decodeFuel_cons, ite_eq_left (by decide : (0xf5 : UInt8).toNat / 32 = 7),
          ite_eq_right (by decide : ¬(0xf5 : UInt8).toNat = 0xf4),
          ite_eq_left (by decide : (0xf5 : UInt8).toNat = 0xf5)]
      | vnull =>
        simp only [encode]
        show decodeFuel (F + 1 + 1) (0xf6 :: rest) = some (.vnull, rest)
        rw [decodeFuel_cons, ite_eq_left (by decide : (0xf6 : UInt8).toNat / 32 = 7),
          ite_eq_right (by decide : ¬(0xf6 : UInt8).toNat = 0xf4),
          ite_eq_right (by decide : ¬(0xf6 : UInt8).toNat = 0xf5),
          ite_eq_left (by decide : (0xf6 : UInt8).toNat = 0xf6)]
    have hl : ∀ xs rest, Value.wfAll xs = true → Value.depthList xs ≤ F + 1 →
        decodeItems (decodeFuel (F + 1 + 1)) xs.length (encodeList xs ++ rest) =
          some (xs, rest) := by
      intro xs
      induction xs with
      | nil => intro rest _ _; simp only [encodeList]; rfl
      | cons x xs ihx =>
        intro rest hwf hdepth
        simp only [Value.wfAll, Bool.and_eq_true] at hwf
        obtain ⟨hx, hxs⟩ := hwf
        simp only [Value.depthList] at hdepth
        have hxd : x.depth ≤ F + 1 := by omega
        have hxsd : Value.depthList xs ≤ F + 1 := by omega
        simp only [encodeList]
        rw [List.length_cons, List.append_assoc, decodeItems_succ,
          hv x (encodeList xs ++ rest) hx hxd]
        show (match decodeItems (decodeFuel (F + 1 + 1)) xs.length (encodeList xs ++ rest)
              with
              | none => none
              | some (ys, r') => some (x :: ys, r')) = some (x :: xs, rest)
        rw [ihx rest hxs hxsd]
    have hp : ∀ kvs rest, Value.wfPairs kvs = true → Value.depthPairs kvs ≤ F + 1 →
        decodePairs (decodeFuel (F + 1 + 1)) kvs.length (encodePairs kvs ++ rest) =
          some (kvs, rest) := by
      intro kvs
      induction kvs with
      | nil => intro rest _ _; simp only [encodePairs]; rfl
      | cons kv kvs ihk =>
        intro rest hwf hdepth
        simp only [Value.wfPairs, Bool.and_eq_true] at hwf
        obtain ⟨⟨hk, hvv⟩, hrest⟩ := hwf
        simp only [Value.depthPairs] at hdepth
        have hkd : kv.1.depth ≤ F + 1 := by omega
        have hvd : kv.2.depth ≤ F + 1 := by omega
        have hresd : Value.depthPairs kvs ≤ F + 1 := by omega
        simp only [encodePairs]
        rw [List.length_cons, List.append_assoc, List.append_assoc, decodePairs_succ,
          hv kv.1 (encode kv.2 ++ (encodePairs kvs ++ rest)) hk hkd]
        show (match decodeFuel (F + 1 + 1) (encode kv.2 ++ (encodePairs kvs ++ rest)) with
              | none => none
              | some (v', r') =>
                match decodePairs (decodeFuel (F + 1 + 1)) kvs.length r' with
                | none => none
                | some (kvs', r'') => some ((kv.1, v') :: kvs', r'')) =
              some ((kv.1, kv.2) :: kvs, rest)
        rw [hv kv.2 (encodePairs kvs ++ rest) hvv hvd]
        show (match decodePairs (decodeFuel (F + 1 + 1)) kvs.length (encodePairs kvs ++ rest)
              with
              | none => none
              | some (kvs', r'') => some ((kv.1, kv.2) :: kvs', r'')) =
              some ((kv.1, kv.2) :: kvs, rest)
        rw [ihk rest hrest hresd]
    exact ⟨hv, hl, hp⟩

/-- Completeness: decoding the encoding of a well-formed item gives
    the item back. -/
theorem decode_encode (v : Value) (h : v.wf = true) : decode (encode v) = some v := by
  obtain ⟨hv, -, -⟩ := rtAll (encode v).length
  have hmain := hv v [] h (depth_le_length v)
  rw [List.append_nil] at hmain
  unfold decode
  rw [hmain]

/-- Decoding an encoding returns the same item: `Cbor.Spec.cbor_decode_encode`. -/
theorem Cbor.Spec.cbor_decode_encode (v : Value) (h : v.wf = true) :
    decode (encode v) = some v := decode_encode v h

/-! ## Soundness: the decoder accepts nothing but encodings -/

/-- An initial byte whose argument `readArg` accepts is exactly the
    head that `head` writes for that major type and argument. -/
theorem head_sound (b : UInt8) (rest : List UInt8) (mt : Nat) (hmt : b.toNat / 32 = mt)
    (hmt5 : mt ≤ 5) (arg : Nat) (r : List UInt8)
    (h : readArg (b.toNat % 32) rest = some (arg, r)) :
    b :: rest = head mt arg ++ r ∧ arg < 2 ^ 64 := by
  have hbnd : b.toNat < 256 := b.toBitVec.isLt
  have hb_eq : mt * 32 + b.toNat % 32 = b.toNat := by
    rw [← hmt, Nat.mul_comm (b.toNat / 32) 32]; exact Nat.div_add_mod b.toNat 32
  have hb256 : mt * 32 < 256 := by
    have := Nat.mul_le_mul hmt5 (Nat.le_refl 32); omega
  have hm : ((mt * 32).toUInt8).toNat = mt * 32 % 256 := by simp [Nat.toUInt8]
  have hbyte : ∀ k : Nat, k ≤ 27 → b.toNat % 32 = k →
      b = (mt * 32).toUInt8 + k.toUInt8 := by
    intro k hk1 hk2
    apply UInt8.toNat_inj.mp
    have hk3 : (k.toUInt8).toNat = k % 256 := by simp [Nat.toUInt8]
    rw [UInt8.toNat_add, hm, hk3, Nat.mod_eq_of_lt (by omega : k < 256),
      Nat.mod_eq_of_lt hb256, Nat.mod_eq_of_lt (by omega : mt * 32 + k < 256),
      ← hk2, hb_eq]
  unfold readArg at h
  by_cases h1 : b.toNat % 32 ≤ 23
  · rw [ite_eq_left h1] at h
    injection h with hpair; injection hpair with hga hgr
    subst hgr
    refine ⟨?_, by omega⟩
    rw [← hga]
    unfold head
    rw [ite_eq_left (by omega : b.toNat % 32 < 24), ← hbyte (b.toNat % 32) (by omega) rfl]
    rfl
  · rw [ite_eq_right h1] at h
    by_cases h2 : b.toNat % 32 = 24
    · rw [ite_eq_left h2] at h
      cases rest with
      | nil => simp at h
      | cons b0 r' =>
        change (if b0.toNat ≥ 24 then some (b0.toNat, r') else none) = some (arg, r) at h
        by_cases hb0 : b0.toNat ≥ 24
        · rw [ite_eq_left hb0] at h
          injection h with hpair; injection hpair with hga hgr
          subst hgr
          have hb0nd : b0.toNat < 256 := b0.toBitVec.isLt
          refine ⟨?_, by omega⟩
          rw [← hga]
          unfold head
          rw [ite_eq_right (by omega : ¬b0.toNat < 24), ite_eq_left (by omega : b0.toNat ≤ 255),
            show (24 : UInt8) = (24 : Nat).toUInt8 from UInt8.toNat_inj.mp (by decide),
            ← hbyte 24 (by decide) h2,
            show (b0.toNat.toUInt8) = b0 from UInt8.toNat_inj.mp (by
              have e : (b0.toNat.toUInt8).toNat = b0.toNat % 256 := by simp [Nat.toUInt8]
              rw [e, Nat.mod_eq_of_lt hb0nd])]
          rfl
        · rw [ite_eq_right hb0] at h
          simp at h
    · rw [ite_eq_right h2] at h
      by_cases h3 : b.toNat % 32 = 25
      · rw [ite_eq_left h3] at h
        change (if (rest.splitAt 2).1.length = 2 ∧ readBe (rest.splitAt 2).1 ≥ 2 ^ 8
            then some (readBe (rest.splitAt 2).1, (rest.splitAt 2).2) else none) =
          some (arg, r) at h
        by_cases hc : (rest.splitAt 2).1.length = 2 ∧ readBe (rest.splitAt 2).1 ≥ 2 ^ 8
        · rw [ite_eq_left hc] at h
          injection h with hpair; injection hpair with hga hgr
          rw [List.splitAt_eq] at hc
          have hga' : readBe (rest.take 2) = arg := by
            rw [List.splitAt_eq] at hga; exact hga
          have hw : (rest.take 2).length = 2 := hc.1
          have hge : readBe (rest.take 2) ≥ 256 := hc.2
          have hlt : readBe (rest.take 2) ≤ 65535 := by
            have := readBe_lt_pow (rest.take 2)
            rw [hw, show (256:Nat) ^ 2 = 65536 from rfl] at this
            omega
          subst hga'
          have hr2 : r = rest.drop 2 := by
            rw [List.splitAt_eq] at hgr; exact hgr.symm
          subst hr2
          have hbw2 : beBytes 2 (readBe (rest.take 2)) = rest.take 2 := by
            have h := beBytes_readBe (rest.take 2)
            rw [hw] at h
            exact h
          refine ⟨?_, by omega⟩
          unfold head
          rw [ite_eq_right (by omega : ¬readBe (rest.take 2) < 24),
            ite_eq_right (by omega : ¬readBe (rest.take 2) ≤ 255),
            ite_eq_left (by omega : readBe (rest.take 2) ≤ 65535), show (25 : UInt8) = (25 : Nat).toUInt8 from UInt8.toNat_inj.mp (by decide),
            ← hbyte 25 (by decide) h3,
            hbw2]
          show b :: rest = b :: (rest.take 2 ++ rest.drop 2)
          rw [List.take_append_drop]
        · rw [ite_eq_right hc] at h
          simp at h
      · rw [ite_eq_right h3] at h
        by_cases h4 : b.toNat % 32 = 26
        · rw [ite_eq_left h4] at h
          change (if (rest.splitAt 4).1.length = 4 ∧ readBe (rest.splitAt 4).1 ≥ 2 ^ 16
              then some (readBe (rest.splitAt 4).1, (rest.splitAt 4).2) else none) =
            some (arg, r) at h
          by_cases hc : (rest.splitAt 4).1.length = 4 ∧ readBe (rest.splitAt 4).1 ≥ 2 ^ 16
          · rw [ite_eq_left hc] at h
            injection h with hpair; injection hpair with hga hgr
            rw [List.splitAt_eq] at hc
            have hw : (rest.take 4).length = 4 := hc.1
            have hge : readBe (rest.take 4) ≥ 65536 := hc.2
            have hlt : readBe (rest.take 4) ≤ 4294967295 := by
              have := readBe_lt_pow (rest.take 4)
              rw [hw, show (256:Nat) ^ 4 = 4294967296 from rfl] at this
              omega
            have hga' : readBe (rest.take 4) = arg := by
              rw [List.splitAt_eq] at hga; exact hga
            subst hga'
            have hr4 : r = rest.drop 4 := by rw [List.splitAt_eq] at hgr; exact hgr.symm
            subst hr4
            have hbw4 : beBytes 4 (readBe (rest.take 4)) = rest.take 4 := by
              have h := beBytes_readBe (rest.take 4)
              rw [hw] at h
              exact h
            refine ⟨?_, by omega⟩
            unfold head
            rw [ite_eq_right (by omega : ¬readBe (rest.take 4) < 24),
              ite_eq_right (by omega : ¬readBe (rest.take 4) ≤ 255),
              ite_eq_right (by omega : ¬readBe (rest.take 4) ≤ 65535),
              ite_eq_left (by omega : readBe (rest.take 4) ≤ 4294967295),
              show (26 : UInt8) = (26 : Nat).toUInt8 from UInt8.toNat_inj.mp (by decide),
            ← hbyte 26 (by decide) h4,
              hbw4]
            show b :: rest = b :: (rest.take 4 ++ rest.drop 4)
            rw [List.take_append_drop]
          · rw [ite_eq_right hc] at h
            simp at h
        · rw [ite_eq_right h4] at h
          by_cases h5 : b.toNat % 32 = 27
          · rw [ite_eq_left h5] at h
            change (if (rest.splitAt 8).1.length = 8 ∧ readBe (rest.splitAt 8).1 ≥ 2 ^ 32
                then some (readBe (rest.splitAt 8).1, (rest.splitAt 8).2) else none) =
              some (arg, r) at h
            by_cases hc : (rest.splitAt 8).1.length = 8 ∧ readBe (rest.splitAt 8).1 ≥ 2 ^ 32
            · rw [ite_eq_left hc] at h
              injection h with hpair; injection hpair with hga hgr
              rw [List.splitAt_eq] at hc
              have hw : (rest.take 8).length = 8 := hc.1
              have hge : readBe (rest.take 8) ≥ 4294967296 := hc.2
              have hlt : readBe (rest.take 8) < 2 ^ 64 := by
                have := readBe_lt_pow (rest.take 8)
                rw [hw, show (256:Nat) ^ 8 = 18446744073709551616 from rfl] at this
                exact this
              have hga' : readBe (rest.take 8) = arg := by
                rw [List.splitAt_eq] at hga; exact hga
              subst hga'
              have hr8 : r = rest.drop 8 := by rw [List.splitAt_eq] at hgr; exact hgr.symm
              subst hr8
              have hbw8 : beBytes 8 (readBe (rest.take 8)) = rest.take 8 := by
                have h := beBytes_readBe (rest.take 8)
                rw [hw] at h
                exact h
              refine ⟨?_, by omega⟩
              unfold head
              rw [ite_eq_right (by omega : ¬readBe (rest.take 8) < 24),
                ite_eq_right (by omega : ¬readBe (rest.take 8) ≤ 255),
                ite_eq_right (by omega : ¬readBe (rest.take 8) ≤ 65535),
                ite_eq_right (by omega : ¬readBe (rest.take 8) ≤ 4294967295),
                show (27 : UInt8) = (27 : Nat).toUInt8 from UInt8.toNat_inj.mp (by decide),
            ← hbyte 27 (by decide) h5,
                hbw8]
              show b :: rest = b :: (rest.take 8 ++ rest.drop 8)
              rw [List.take_append_drop]
            · rw [ite_eq_right hc] at h
              simp at h
          · rw [ite_eq_right h5] at h
            simp at h

/-- `decodeItems` reads exactly as many items as asked. -/
theorem decodeItems_length (dec : List UInt8 → Option (Value × List UInt8)) :
    ∀ n bs xs r, decodeItems dec n bs = some (xs, r) → xs.length = n := by
  intro n
  induction n with
  | zero =>
    intro bs xs r h
    rw [decodeItems_zero] at h
    injection h with hpair; injection hpair with h1 h2
    rw [← h1]
    rfl
  | succ n ih =>
    intro bs xs r h
    rw [decodeItems_succ] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · have hrec := ih _ _ _ (by assumption)
        injection h with hpair; injection hpair with h1 h2
        rw [← h1, List.length_cons, hrec]

/-- `decodePairs` reads exactly as many pairs as asked. -/
theorem decodePairs_length (dec : List UInt8 → Option (Value × List UInt8)) :
    ∀ n bs kvs r, decodePairs dec n bs = some (kvs, r) → kvs.length = n := by
  intro n
  induction n with
  | zero =>
    intro bs kvs r h
    have hz : decodePairs dec 0 bs = some ([], bs) := rfl
    rw [hz] at h
    injection h with hpair; injection hpair with h1 h2
    rw [← h1]
    rfl
  | succ n ih =>
    intro bs kvs r h
    rw [decodePairs_succ] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · have hrec := ih _ _ _ (by assumption)
          injection h with hpair; injection hpair with h1 h2
          rw [← h1, List.length_cons, hrec]

/-- Soundness, by induction on the fuel: whatever the decoder accepts
    is the encoding of what it returns, followed by the rest. -/
theorem soundAll : ∀ F : Nat,
    (∀ bs v r, decodeFuel (F + 1) bs = some (v, r) →
      v.wf = true ∧ bs = encode v ++ r) ∧
    (∀ n bs xs r, decodeItems (decodeFuel (F + 1)) n bs = some (xs, r) →
      Value.wfAll xs = true ∧ bs = encodeList xs ++ r) ∧
    (∀ n bs kvs r, decodePairs (decodeFuel (F + 1)) n bs = some (kvs, r) →
      Value.wfPairs kvs = true ∧ bs = encodePairs kvs ++ r) := by
  intro F
  induction F with
  | zero =>
    have hl00 : ∀ n bs xs r, decodeItems (decodeFuel 0) n bs = some (xs, r) →
        Value.wfAll xs = true ∧ bs = encodeList xs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs xs r h
        rw [decodeItems_zero] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfAll], by simp only [encodeList]; rfl⟩
      | succ n ih =>
        intro bs xs r h
        rw [decodeItems_succ] at h
        split at h
        · simp at h
        · rename_i hdec
          have hnone : decodeFuel 0 bs = none := rfl
          rw [hnone] at hdec
          simp at hdec
    have hp00 : ∀ n bs kvs r, decodePairs (decodeFuel 0) n bs = some (kvs, r) →
        Value.wfPairs kvs = true ∧ bs = encodePairs kvs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs kvs r h
        have hz : decodePairs (decodeFuel 0) 0 bs = some ([], bs) := rfl
        rw [hz] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfPairs], by simp only [encodePairs]; rfl⟩
      | succ n ih =>
        intro bs kvs r h
        rw [decodePairs_succ] at h
        split at h
        · simp at h
        · rename_i hdec
          have hnone : decodeFuel 0 bs = none := rfl
          rw [hnone] at hdec
          simp at hdec
    have hv0 : ∀ bs v r, decodeFuel (0 + 1) bs = some (v, r) →
        v.wf = true ∧ bs = encode v ++ r := by
      intro bs v r h
      cases bs with
      | nil =>
        simp only [decodeFuel] at h
        simp at h
      | cons b rest =>
        rw [decodeFuel_cons] at h
        by_cases h7 : b.toNat / 32 = 7
        · rw [ite_eq_left h7] at h
          by_cases h4 : b.toNat = 0xf4
          · rw [ite_eq_left h4] at h
            injection h with hpair; injection hpair with hve hre
            subst hre; subst hve
            have hb : b = 0xf4 := UInt8.toNat_inj.mp h4
            exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
          · rw [ite_eq_right h4] at h
            by_cases h5 : b.toNat = 0xf5
            · rw [ite_eq_left h5] at h
              injection h with hpair; injection hpair with hve hre
              subst hre; subst hve
              have hb : b = 0xf5 := UInt8.toNat_inj.mp h5
              exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
            · rw [ite_eq_right h5] at h
              by_cases h6 : b.toNat = 0xf6
              · rw [ite_eq_left h6] at h
                injection h with hpair; injection hpair with hve hre
                subst hre; subst hve
                have hb : b = 0xf6 := UInt8.toNat_inj.mp h6
                exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
              · rw [ite_eq_right h6] at h
                simp at h
        · rw [ite_eq_right h7] at h
          by_cases h6 : b.toNat / 32 = 6
          · rw [ite_eq_left h6] at h
            simp at h
          · rw [ite_eq_right h6] at h
            split at h
            · simp at h
            · rename_i arg r' hrd
              by_cases h0 : b.toNat / 32 = 0
              · rw [ite_eq_left h0] at h
                injection h with hpair; injection hpair with hve hre
                obtain ⟨hbs, harg64⟩ := head_sound b rest 0 h0 (by omega) arg r' hrd
                subst hre; subst hve
                refine ⟨by simp only [Value.wf], ?_⟩
                rw [hbs]
                simp only [encode]
                rw [UInt64.toNat_ofNat_of_lt' harg64]
              · rw [ite_eq_right h0] at h
                by_cases h1 : b.toNat / 32 = 1
                · rw [ite_eq_left h1] at h
                  injection h with hpair; injection hpair with hve hre
                  obtain ⟨hbs, harg64⟩ := head_sound b rest 1 h1 (by omega) arg r' hrd
                  subst hre; subst hve
                  refine ⟨by simp only [Value.wf], ?_⟩
                  rw [hbs]
                  simp only [encode]
                  rw [UInt64.toNat_ofNat_of_lt' harg64]
                · rw [ite_eq_right h1] at h
                  by_cases h2 : b.toNat / 32 = 2
                  · rw [ite_eq_left h2] at h
                    by_cases hlt : r'.length < arg
                    · rw [ite_eq_left hlt] at h
                      simp at h
                    · rw [ite_eq_right hlt] at h
                      injection h with hpair; injection hpair with hve hre
                      obtain ⟨hbs, harg64⟩ := head_sound b rest 2 h2 (by omega) arg r' hrd
                      subst hve
                      have htk : (r'.take arg).length = arg := by
                        rw [List.length_take]; omega
                      refine ⟨?_, ?_⟩
                      · simp only [Value.wf]
                        rw [htk]
                        exact decide_eq_true harg64
                      · rw [hbs, ← hre]
                        simp only [encode]
                        rw [htk, List.append_assoc, List.take_append_drop]
                  · rw [ite_eq_right h2] at h
                    by_cases h3 : b.toNat / 32 = 3
                    · rw [ite_eq_left h3] at h
                      by_cases hlt : r'.length < arg
                      · rw [ite_eq_left hlt] at h
                        simp at h
                      · rw [ite_eq_right hlt] at h
                        by_cases hval : Utf8.valid (r'.take arg) = true
                        · rw [ite_eq_left hval] at h
                          injection h with hpair; injection hpair with hve hre
                          obtain ⟨hbs, harg64⟩ := head_sound b rest 3 h3 (by omega) arg r' hrd
                          subst hve
                          have htk : (r'.take arg).length = arg := by
                            rw [List.length_take]; omega
                          refine ⟨?_, ?_⟩
                          · simp only [Value.wf, Bool.and_eq_true]
                            refine ⟨by rw [← Utf8.valid_eq_wellFormed]; exact hval,
                              by rw [htk]; exact decide_eq_true harg64⟩
                          · rw [hbs, ← hre]
                            simp only [encode]
                            rw [htk, List.append_assoc, List.take_append_drop]
                        · rw [ite_eq_right hval] at h
                          simp at h
                    · rw [ite_eq_right h3] at h
                      by_cases h4 : b.toNat / 32 = 4
                      · rw [ite_eq_left h4] at h
                        split at h
                        · rename_i _ _ xs r'' hdi
                          injection h with hpair; injection hpair with hve hre
                          obtain ⟨hwfA, hbsA⟩ := hl00 arg r' xs r'' hdi
                          have hlen : xs.length = arg := decodeItems_length _ _ _ _ _ hdi
                          obtain ⟨hbs, harg64⟩ := head_sound b rest 4 h4 (by omega) arg r' hrd
                          subst hre; subst hve
                          refine ⟨?_, ?_⟩
                          · simp only [Value.wf, Bool.and_eq_true]
                            exact ⟨by rw [hlen]; exact decide_eq_true harg64, hwfA⟩
                          · rw [hbs, hbsA]
                            simp only [encode]
                            rw [hlen, List.append_assoc]
                        · simp at h
                      · rw [ite_eq_right h4] at h
                        by_cases h5 : b.toNat / 32 = 5
                        · rw [ite_eq_left h5] at h
                          split at h
                          · rename_i _ _ kvs r'' hdp
                            injection h with hpair; injection hpair with hve hre
                            obtain ⟨hwfP, hbsP⟩ := hp00 arg r' kvs r'' hdp
                            have hlen : kvs.length = arg := decodePairs_length _ _ _ _ _ hdp
                            obtain ⟨hbs, harg64⟩ := head_sound b rest 5 h5 (by omega) arg r' hrd
                            subst hre; subst hve
                            refine ⟨?_, ?_⟩
                            · simp only [Value.wf, Bool.and_eq_true]
                              exact ⟨by rw [hlen]; exact decide_eq_true harg64, hwfP⟩
                            · rw [hbs, hbsP]
                              simp only [encode]
                              rw [hlen, List.append_assoc]
                          · simp at h
                        · rw [ite_eq_right h5] at h
                          simp at h
    have hl0 : ∀ n bs xs r, decodeItems (decodeFuel (0 + 1)) n bs = some (xs, r) →
        Value.wfAll xs = true ∧ bs = encodeList xs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs xs r h
        rw [decodeItems_zero] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfAll], by simp only [encodeList]; rfl⟩
      | succ n ih2 =>
        intro bs xs r h
        rw [decodeItems_succ] at h
        split at h
        · simp at h
        · rename_i x r1 hd
          split at h
          · simp at h
          · rename_i xs' r'' hrec
            injection h with hpair; injection hpair with h1 h2
            obtain ⟨hwfx, hbsx⟩ := hv0 bs x r1 hd
            obtain ⟨hwfxs, hbsxs⟩ := ih2 r1 xs' r'' hrec
            subst h2; subst h1
            refine ⟨?_, ?_⟩
            · simp only [Value.wfAll, Bool.and_eq_true]
              exact ⟨hwfx, hwfxs⟩
            · simp only [encodeList]
              rw [List.append_assoc, ← hbsxs, ← hbsx]
    have hp0 : ∀ n bs kvs r, decodePairs (decodeFuel (0 + 1)) n bs = some (kvs, r) →
        Value.wfPairs kvs = true ∧ bs = encodePairs kvs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs kvs r h
        have hz : decodePairs (decodeFuel (0 + 1)) 0 bs = some ([], bs) := rfl
        rw [hz] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfPairs], by simp only [encodePairs]; rfl⟩
      | succ n ih2 =>
        intro bs kvs r h
        rw [decodePairs_succ] at h
        split at h
        · simp at h
        · rename_i k r1 hd
          split at h
          · simp at h
          · rename_i v' r' hdv
            split at h
            · simp at h
            · rename_i kvs' r'' hrec
              injection h with hpair; injection hpair with h1 h2
              obtain ⟨hwfk, hbsk⟩ := hv0 bs k r1 hd
              obtain ⟨hwfv, hbsv⟩ := hv0 r1 v' r' hdv
              obtain ⟨hwfrest, hbsrest⟩ := ih2 r' kvs' r'' hrec
              subst h2; subst h1
              refine ⟨?_, ?_⟩
              · simp only [Value.wfPairs, Bool.and_eq_true]
                exact ⟨⟨hwfk, hwfv⟩, hwfrest⟩
              · simp only [encodePairs]
                rw [List.append_assoc, List.append_assoc, ← hbsrest, ← hbsv, ← hbsk]
    exact ⟨hv0, hl0, hp0⟩
  | succ F ih =>
    obtain ⟨ihv, ihl, ihp⟩ := ih
    have hv : ∀ bs v r, decodeFuel (F + 1 + 1) bs = some (v, r) →
        v.wf = true ∧ bs = encode v ++ r := by
      intro bs v r h
      cases bs with
      | nil =>
        simp only [decodeFuel] at h
        simp at h
      | cons b rest =>
        rw [decodeFuel_cons] at h
        by_cases h7 : b.toNat / 32 = 7
        · rw [ite_eq_left h7] at h
          by_cases h4 : b.toNat = 0xf4
          · rw [ite_eq_left h4] at h
            injection h with hpair; injection hpair with hve hre
            subst hre; subst hve
            have hb : b = 0xf4 := UInt8.toNat_inj.mp h4
            exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
          · rw [ite_eq_right h4] at h
            by_cases h5 : b.toNat = 0xf5
            · rw [ite_eq_left h5] at h
              injection h with hpair; injection hpair with hve hre
              subst hre; subst hve
              have hb : b = 0xf5 := UInt8.toNat_inj.mp h5
              exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
            · rw [ite_eq_right h5] at h
              by_cases h6 : b.toNat = 0xf6
              · rw [ite_eq_left h6] at h
                injection h with hpair; injection hpair with hve hre
                subst hre; subst hve
                have hb : b = 0xf6 := UInt8.toNat_inj.mp h6
                exact ⟨by simp only [Value.wf], by simp only [encode]; rw [hb]; rfl⟩
              · rw [ite_eq_right h6] at h
                simp at h
        · rw [ite_eq_right h7] at h
          by_cases h6 : b.toNat / 32 = 6
          · rw [ite_eq_left h6] at h
            simp at h
          · rw [ite_eq_right h6] at h
            split at h
            · simp at h
            · rename_i arg r' hrd
              by_cases h0 : b.toNat / 32 = 0
              · rw [ite_eq_left h0] at h
                injection h with hpair; injection hpair with hve hre
                obtain ⟨hbs, harg64⟩ := head_sound b rest 0 h0 (by omega) arg r' hrd
                subst hre; subst hve
                refine ⟨by simp only [Value.wf], ?_⟩
                rw [hbs]
                simp only [encode]
                rw [UInt64.toNat_ofNat_of_lt' harg64]
              · rw [ite_eq_right h0] at h
                by_cases h1 : b.toNat / 32 = 1
                · rw [ite_eq_left h1] at h
                  injection h with hpair; injection hpair with hve hre
                  obtain ⟨hbs, harg64⟩ := head_sound b rest 1 h1 (by omega) arg r' hrd
                  subst hre; subst hve
                  refine ⟨by simp only [Value.wf], ?_⟩
                  rw [hbs]
                  simp only [encode]
                  rw [UInt64.toNat_ofNat_of_lt' harg64]
                · rw [ite_eq_right h1] at h
                  by_cases h2 : b.toNat / 32 = 2
                  · rw [ite_eq_left h2] at h
                    by_cases hlt : r'.length < arg
                    · rw [ite_eq_left hlt] at h
                      simp at h
                    · rw [ite_eq_right hlt] at h
                      injection h with hpair; injection hpair with hve hre
                      obtain ⟨hbs, harg64⟩ := head_sound b rest 2 h2 (by omega) arg r' hrd
                      subst hve
                      have htk : (r'.take arg).length = arg := by
                        rw [List.length_take]; omega
                      refine ⟨?_, ?_⟩
                      · simp only [Value.wf]
                        rw [htk]
                        exact decide_eq_true harg64
                      · rw [hbs, ← hre]
                        simp only [encode]
                        rw [htk, List.append_assoc, List.take_append_drop]
                  · rw [ite_eq_right h2] at h
                    by_cases h3 : b.toNat / 32 = 3
                    · rw [ite_eq_left h3] at h
                      by_cases hlt : r'.length < arg
                      · rw [ite_eq_left hlt] at h
                        simp at h
                      · rw [ite_eq_right hlt] at h
                        by_cases hval : Utf8.valid (r'.take arg) = true
                        · rw [ite_eq_left hval] at h
                          injection h with hpair; injection hpair with hve hre
                          obtain ⟨hbs, harg64⟩ := head_sound b rest 3 h3 (by omega) arg r' hrd
                          subst hve
                          have htk : (r'.take arg).length = arg := by
                            rw [List.length_take]; omega
                          refine ⟨?_, ?_⟩
                          · simp only [Value.wf, Bool.and_eq_true]
                            refine ⟨by rw [← Utf8.valid_eq_wellFormed]; exact hval,
                              by rw [htk]; exact decide_eq_true harg64⟩
                          · rw [hbs, ← hre]
                            simp only [encode]
                            rw [htk, List.append_assoc, List.take_append_drop]
                        · rw [ite_eq_right hval] at h
                          simp at h
                    · rw [ite_eq_right h3] at h
                      by_cases h4 : b.toNat / 32 = 4
                      · rw [ite_eq_left h4] at h
                        split at h
                        · rename_i _ _ xs r'' hdi
                          injection h with hpair; injection hpair with hve hre
                          obtain ⟨hwfA, hbsA⟩ := ihl arg r' xs r'' hdi
                          have hlen : xs.length = arg := decodeItems_length _ _ _ _ _ hdi
                          obtain ⟨hbs, harg64⟩ := head_sound b rest 4 h4 (by omega) arg r' hrd
                          subst hre; subst hve
                          refine ⟨?_, ?_⟩
                          · simp only [Value.wf, Bool.and_eq_true]
                            exact ⟨by rw [hlen]; exact decide_eq_true harg64, hwfA⟩
                          · rw [hbs, hbsA]
                            simp only [encode]
                            rw [hlen, List.append_assoc]
                        · simp at h
                      · rw [ite_eq_right h4] at h
                        by_cases h5 : b.toNat / 32 = 5
                        · rw [ite_eq_left h5] at h
                          split at h
                          · rename_i _ _ kvs r'' hdp
                            injection h with hpair; injection hpair with hve hre
                            obtain ⟨hwfP, hbsP⟩ := ihp arg r' kvs r'' hdp
                            have hlen : kvs.length = arg := decodePairs_length _ _ _ _ _ hdp
                            obtain ⟨hbs, harg64⟩ := head_sound b rest 5 h5 (by omega) arg r' hrd
                            subst hre; subst hve
                            refine ⟨?_, ?_⟩
                            · simp only [Value.wf, Bool.and_eq_true]
                              exact ⟨by rw [hlen]; exact decide_eq_true harg64, hwfP⟩
                            · rw [hbs, hbsP]
                              simp only [encode]
                              rw [hlen, List.append_assoc]
                          · simp at h
                        · rw [ite_eq_right h5] at h
                          simp at h
    have hl : ∀ n bs xs r, decodeItems (decodeFuel (F + 1 + 1)) n bs = some (xs, r) →
        Value.wfAll xs = true ∧ bs = encodeList xs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs xs r h
        rw [decodeItems_zero] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfAll], by simp only [encodeList]; rfl⟩
      | succ n ih2 =>
        intro bs xs r h
        rw [decodeItems_succ] at h
        split at h
        · simp at h
        · rename_i x r1 hd
          split at h
          · simp at h
          · rename_i xs' r'' hrec
            injection h with hpair; injection hpair with h1 h2
            obtain ⟨hwfx, hbsx⟩ := hv bs x r1 hd
            obtain ⟨hwfxs, hbsxs⟩ := ih2 r1 xs' r'' hrec
            subst h2; subst h1
            refine ⟨?_, ?_⟩
            · simp only [Value.wfAll, Bool.and_eq_true]
              exact ⟨hwfx, hwfxs⟩
            · simp only [encodeList]
              rw [List.append_assoc, ← hbsxs, ← hbsx]
    have hp : ∀ n bs kvs r, decodePairs (decodeFuel (F + 1 + 1)) n bs = some (kvs, r) →
        Value.wfPairs kvs = true ∧ bs = encodePairs kvs ++ r := by
      intro n
      induction n with
      | zero =>
        intro bs kvs r h
        have hz : decodePairs (decodeFuel (F + 1 + 1)) 0 bs = some ([], bs) := rfl
        rw [hz] at h
        injection h with hpair; injection hpair with h1 h2
        subst h1; subst h2
        exact ⟨by simp only [Value.wfPairs], by simp only [encodePairs]; rfl⟩
      | succ n ih2 =>
        intro bs kvs r h
        rw [decodePairs_succ] at h
        split at h
        · simp at h
        · rename_i k r1 hd
          split at h
          · simp at h
          · rename_i v' r' hdv
            split at h
            · simp at h
            · rename_i kvs' r'' hrec
              injection h with hpair; injection hpair with h1 h2
              obtain ⟨hwfk, hbsk⟩ := hv bs k r1 hd
              obtain ⟨hwfv, hbsv⟩ := hv r1 v' r' hdv
              obtain ⟨hwfrest, hbsrest⟩ := ih2 r' kvs' r'' hrec
              subst h2; subst h1
              refine ⟨?_, ?_⟩
              · simp only [Value.wfPairs, Bool.and_eq_true]
                exact ⟨⟨hwfk, hwfv⟩, hwfrest⟩
              · simp only [encodePairs]
                rw [List.append_assoc, List.append_assoc, ← hbsrest, ← hbsv, ← hbsk]
    exact ⟨hv, hl, hp⟩

/-- Soundness: whatever the decoder accepts is the encoding of a
    well-formed item, the one it returns. -/
theorem encode_decode (bs : List UInt8) (v : Value) (h : decode bs = some v) :
    v.wf = true ∧ encode v = bs := by
  obtain ⟨hv, -, -⟩ := soundAll bs.length
  unfold decode at h
  split at h
  · rename_i v' hmain
    obtain ⟨hwf, hbs⟩ := hv bs v' [] hmain
    rw [List.append_nil] at hbs
    cases h
    exact ⟨hwf, hbs.symm⟩
  · simp at h

/-- The decoder accepts exactly the encodings of well-formed items:
    `Cbor.Spec.cbor_encode_decode`. -/
theorem Cbor.Spec.cbor_encode_decode (bs : List UInt8) (v : Value) :
    decode bs = some v ↔ v.wf = true ∧ encode v = bs := by
  constructor
  · exact encode_decode bs v
  · rintro ⟨hwf, rfl⟩
    exact decode_encode v hwf
