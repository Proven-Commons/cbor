/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names. The `sorry` below is expected in this file only.

  The definitions the statements use besides the code are in
  `Spec/Defs.lean`, `Spec/Value.lean` (the item type and `Value.wf`)
  and `Spec/Utf8.lean` (well-formed UTF-8, from RFC 3629). They are
  part of the specification too.
-/

import Cbor
import Spec.Defs

open Cbor

/-! ## The two main claims -/

/-- Decoding an encoding returns the same item. (RFC 8949: the slice's
    well-formed items, as `Value.wf` defines.) -/
theorem Spec.cbor_decode_encode (v : Value) (h : v.wf = true) :
    decode (encode v) = some v := sorry

/-- The decoder accepts exactly the encodings of well-formed items, and
    nothing else: it accepts `bs` and returns `v` if and only if `v` is
    well-formed (`Value.wf`) and `bs` is the encoding of `v`. -/
theorem Spec.cbor_encode_decode (bs : List UInt8) (v : Value) :
    decode bs = some v ↔ v.wf = true ∧ encode v = bs := sorry

/-! ## The encoding is RFC 8949's preferred serialization -/

/-- The encoder writes `Spec.enc`, the encoding `Spec/Defs.lean` writes
    from RFC 8949 (sections 3, 3.1 and 3.3, with the preferred
    serialization of sections 4.1 and 4.2.1), for every item. So the
    two claims above are about that encoding. -/
theorem Spec.cbor_encode_spec (v : Value) : encode v = Spec.enc v := sorry

/-! ## Text strings: the UTF-8 check is RFC 3629

`Value.wf` asks every text payload to be `Spec.Utf8.wellFormed`, the
grammar of RFC 3629, section 4. The decoder checks text payloads with
`Utf8.valid`; this says the two agree on every byte list. -/

theorem Spec.cbor_utf8_valid_eq (bs : List UInt8) :
    Cbor.Utf8.valid bs = Spec.Utf8.wellFormed bs := sorry

/-! ## Added information the RFC holds back, and the indefinite form -/

/-- An initial byte with added information 28 to 30 (reserved by
    RFC 8949, section 3.1) is turned away, as is 31, the indefinite
    form, which this slice does not carry. -/
theorem Spec.cbor_rejects_reserved_ai (b : UInt8) (rest : List UInt8) :
    b.toNat % 32 ≥ 28 → decode (b :: rest) = none := sorry

/-- Tags (major type 6) are outside the slice and turned away. -/
theorem Spec.cbor_rejects_tags (b : UInt8) (rest : List UInt8) :
    b.toNat / 32 = 6 → decode (b :: rest) = none := sorry

/-- Major type 7 carries only false, true, and null in this slice:
    undefined, other simple values, every float, and break are turned
    away. -/
theorem Spec.cbor_rejects_simple (b : UInt8) (rest : List UInt8) :
    b.toNat / 32 = 7 → b.toNat ≠ 0xf4 → b.toNat ≠ 0xf5 → b.toNat ≠ 0xf6 →
    decode (b :: rest) = none := sorry

/-! ## Test vectors: RFC 8949, Appendix A

Appendix A has 81 rows. Each of the 37 rows in the slice holds in both
directions. The other 44 (bignums, floats, undefined and other simple
values, tags, and indefinite lengths) are turned away, in the theorem
after this one. The differential tests run all 81. -/

theorem Spec.cbor_rfc8949_vectors :
    -- Unsigned integers
    encode (.uint 0) = [0x00] ∧ decode [0x00] = some (.uint 0) ∧
    encode (.uint 1) = [0x01] ∧ decode [0x01] = some (.uint 1) ∧
    encode (.uint 10) = [0x0a] ∧ decode [0x0a] = some (.uint 10) ∧
    encode (.uint 23) = [0x17] ∧ decode [0x17] = some (.uint 23) ∧
    encode (.uint 24) = [0x18, 0x18] ∧ decode [0x18, 0x18] = some (.uint 24) ∧
    encode (.uint 25) = [0x18, 0x19] ∧ decode [0x18, 0x19] = some (.uint 25) ∧
    encode (.uint 100) = [0x18, 0x64] ∧ decode [0x18, 0x64] = some (.uint 100) ∧
    encode (.uint 1000) = [0x19, 0x03, 0xe8] ∧ decode [0x19, 0x03, 0xe8] = some (.uint 1000) ∧
    encode (.uint 1000000) = [0x1a, 0x00, 0x0f, 0x42, 0x40] ∧
      decode [0x1a, 0x00, 0x0f, 0x42, 0x40] = some (.uint 1000000) ∧
    encode (.uint 1000000000000) = [0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00] ∧
      decode [0x1b, 0x00, 0x00, 0x00, 0xe8, 0xd4, 0xa5, 0x10, 0x00] = some (.uint 1000000000000) ∧
    encode (.uint 18446744073709551615) = [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ∧
      decode [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] =
        some (.uint 18446744073709551615) ∧
    -- Negative integers: nint n is -1 - n
    encode (.nint 0) = [0x20] ∧ decode [0x20] = some (.nint 0) ∧
    encode (.nint 9) = [0x29] ∧ decode [0x29] = some (.nint 9) ∧
    encode (.nint 99) = [0x38, 0x63] ∧ decode [0x38, 0x63] = some (.nint 99) ∧
    encode (.nint 999) = [0x39, 0x03, 0xe7] ∧ decode [0x39, 0x03, 0xe7] = some (.nint 999) ∧
    encode (.nint 18446744073709551615) = [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] ∧
      decode [0x3b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] =
        some (.nint 18446744073709551615) ∧
    -- Byte strings
    encode (.bytes []) = [0x40] ∧ decode [0x40] = some (.bytes []) ∧
    encode (.bytes [0x01, 0x02, 0x03, 0x04]) = [0x44, 0x01, 0x02, 0x03, 0x04] ∧
      decode [0x44, 0x01, 0x02, 0x03, 0x04] = some (.bytes [0x01, 0x02, 0x03, 0x04]) ∧
    -- Text strings, as their UTF-8 payload bytes
    encode (.text []) = [0x60] ∧ decode [0x60] = some (.text []) ∧
    encode (.text [0x61]) = [0x61, 0x61] ∧ decode [0x61, 0x61] = some (.text [0x61]) ∧
    encode (.text [0x49, 0x45, 0x54, 0x46]) = [0x64, 0x49, 0x45, 0x54, 0x46] ∧
      decode [0x64, 0x49, 0x45, 0x54, 0x46] = some (.text [0x49, 0x45, 0x54, 0x46]) ∧
    encode (.text [0x22, 0x5c]) = [0x62, 0x22, 0x5c] ∧
      decode [0x62, 0x22, 0x5c] = some (.text [0x22, 0x5c]) ∧
    encode (.text [0xc3, 0xbc]) = [0x62, 0xc3, 0xbc] ∧
      decode [0x62, 0xc3, 0xbc] = some (.text [0xc3, 0xbc]) ∧
    encode (.text [0xe6, 0xb0, 0xb4]) = [0x63, 0xe6, 0xb0, 0xb4] ∧
      decode [0x63, 0xe6, 0xb0, 0xb4] = some (.text [0xe6, 0xb0, 0xb4]) ∧
    encode (.text [0xf0, 0x90, 0x85, 0x91]) = [0x64, 0xf0, 0x90, 0x85, 0x91] ∧
      decode [0x64, 0xf0, 0x90, 0x85, 0x91] = some (.text [0xf0, 0x90, 0x85, 0x91]) ∧
    -- Arrays
    encode (.array []) = [0x80] ∧ decode [0x80] = some (.array []) ∧
    encode (.array [.uint 1, .uint 2, .uint 3]) = [0x83, 0x01, 0x02, 0x03] ∧
      decode [0x83, 0x01, 0x02, 0x03] = some (.array [.uint 1, .uint 2, .uint 3]) ∧
    encode (.array [.uint 1, .array [.uint 2, .uint 3], .array [.uint 4, .uint 5]]) =
      [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05] ∧
      decode [0x83, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05] =
        some (.array [.uint 1, .array [.uint 2, .uint 3], .array [.uint 4, .uint 5]]) ∧
    encode (.array ((List.range 25).map fun n => .uint (n + 1).toUInt64)) =
      (0x98 :: 0x19 :: ((List.range 23).map fun n => (n + 1).toUInt8) ++
        [0x18, 0x18, 0x18, 0x19]) ∧
      decode (0x98 :: 0x19 :: ((List.range 23).map fun n => (n + 1).toUInt8) ++
        [0x18, 0x18, 0x18, 0x19]) =
        some (.array ((List.range 25).map fun n => .uint (n + 1).toUInt64)) ∧
    -- Maps
    encode (.map []) = [0xa0] ∧ decode [0xa0] = some (.map []) ∧
    encode (.map [(.uint 1, .uint 2), (.uint 3, .uint 4)]) = [0xa2, 0x01, 0x02, 0x03, 0x04] ∧
      decode [0xa2, 0x01, 0x02, 0x03, 0x04] = some (.map [(.uint 1, .uint 2), (.uint 3, .uint 4)]) ∧
    encode (.map [(.text [0x61], .uint 1), (.text [0x62], .array [.uint 2, .uint 3])]) =
      [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03] ∧
      decode [0xa2, 0x61, 0x61, 0x01, 0x61, 0x62, 0x82, 0x02, 0x03] =
        some (.map [(.text [0x61], .uint 1), (.text [0x62], .array [.uint 2, .uint 3])]) ∧
    encode (.array [.text [0x61], .map [(.text [0x62], .text [0x63])]]) =
      [0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63] ∧
      decode [0x82, 0x61, 0x61, 0xa1, 0x61, 0x62, 0x61, 0x63] =
        some (.array [.text [0x61], .map [(.text [0x62], .text [0x63])]]) ∧
    encode (.map [(.text [0x61], .text [0x41]), (.text [0x62], .text [0x42]),
                  (.text [0x63], .text [0x43]), (.text [0x64], .text [0x44]),
                  (.text [0x65], .text [0x45])]) =
      [0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43,
       0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45] ∧
      decode [0xa5, 0x61, 0x61, 0x61, 0x41, 0x61, 0x62, 0x61, 0x42, 0x61, 0x63, 0x61, 0x43,
              0x61, 0x64, 0x61, 0x44, 0x61, 0x65, 0x61, 0x45] =
        some (.map [(.text [0x61], .text [0x41]), (.text [0x62], .text [0x42]),
                    (.text [0x63], .text [0x43]), (.text [0x64], .text [0x44]),
                    (.text [0x65], .text [0x45])]) ∧
    -- Simple values
    encode .vfalse = [0xf4] ∧ decode [0xf4] = some .vfalse ∧
    encode .vtrue = [0xf5] ∧ decode [0xf5] = some .vtrue ∧
    encode .vnull = [0xf6] ∧ decode [0xf6] = some .vnull := sorry

/-- Every row of Appendix A outside the slice, all 44, is turned away:
    bignums (tags 2 and 3), floats, undefined, simple(16), simple(255),
    tags, and indefinite-length items, at the top or nested. Break on its
    own is turned away too. -/
theorem Spec.cbor_rejects_out_of_slice :
    -- Bignums (tags 2 and 3)
    decode [0xc2, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    decode [0xc3, 0x49, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    -- Floats: half, single and double, including infinities and NaN
    decode [0xf9, 0x00, 0x00] = none ∧
    decode [0xf9, 0x80, 0x00] = none ∧
    decode [0xf9, 0x3c, 0x00] = none ∧
    decode [0xfb, 0x3f, 0xf1, 0x99, 0x99, 0x99, 0x99, 0x99, 0x9a] = none ∧
    decode [0xf9, 0x3e, 0x00] = none ∧
    decode [0xf9, 0x7b, 0xff] = none ∧
    decode [0xfa, 0x47, 0xc3, 0x50, 0x00] = none ∧
    decode [0xfa, 0x7f, 0x7f, 0xff, 0xff] = none ∧
    decode [0xfb, 0x7e, 0x37, 0xe4, 0x3c, 0x88, 0x00, 0x75, 0x9c] = none ∧
    decode [0xf9, 0x00, 0x01] = none ∧
    decode [0xf9, 0x04, 0x00] = none ∧
    decode [0xf9, 0xc4, 0x00] = none ∧
    decode [0xfb, 0xc0, 0x10, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66] = none ∧
    decode [0xf9, 0x7c, 0x00] = none ∧
    decode [0xf9, 0x7e, 0x00] = none ∧
    decode [0xf9, 0xfc, 0x00] = none ∧
    decode [0xfa, 0x7f, 0x80, 0x00, 0x00] = none ∧
    decode [0xfa, 0x7f, 0xc0, 0x00, 0x00] = none ∧
    decode [0xfa, 0xff, 0x80, 0x00, 0x00] = none ∧
    decode [0xfb, 0x7f, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    decode [0xfb, 0x7f, 0xf8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    decode [0xfb, 0xff, 0xf0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] = none ∧
    -- undefined, simple(16), simple(255)
    decode [0xf7] = none ∧
    decode [0xf0] = none ∧
    decode [0xf8, 0xff] = none ∧
    -- Tags 0, 1, 23, 24, 32
    decode [0xc0, 0x74, 0x32, 0x30, 0x31, 0x33, 0x2d, 0x30, 0x33, 0x2d, 0x32, 0x31, 0x54, 0x32,
            0x30, 0x3a, 0x30, 0x34, 0x3a, 0x30, 0x30, 0x5a] = none ∧
    decode [0xc1, 0x1a, 0x51, 0x4b, 0x67, 0xb0] = none ∧
    decode [0xc1, 0xfb, 0x41, 0xd4, 0x52, 0xd9, 0xec, 0x20, 0x00, 0x00] = none ∧
    decode [0xd7, 0x44, 0x01, 0x02, 0x03, 0x04] = none ∧
    decode [0xd8, 0x18, 0x45, 0x64, 0x49, 0x45, 0x54, 0x46] = none ∧
    decode [0xd8, 0x20, 0x76, 0x68, 0x74, 0x74, 0x70, 0x3a, 0x2f, 0x2f, 0x77, 0x77, 0x77, 0x2e,
            0x65, 0x78, 0x61, 0x6d, 0x70, 0x6c, 0x65, 0x2e, 0x63, 0x6f, 0x6d] = none ∧
    -- Indefinite-length strings, arrays and maps, alone or nested
    decode [0x5f, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xff] = none ∧
    decode [0x7f, 0x65, 0x73, 0x74, 0x72, 0x65, 0x61, 0x64, 0x6d, 0x69, 0x6e, 0x67, 0xff] = none ∧
    decode [0x9f, 0xff] = none ∧
    decode [0x9f, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff, 0xff] = none ∧
    decode [0x9f, 0x01, 0x82, 0x02, 0x03, 0x82, 0x04, 0x05, 0xff] = none ∧
    decode [0x83, 0x01, 0x82, 0x02, 0x03, 0x9f, 0x04, 0x05, 0xff] = none ∧
    decode [0x83, 0x01, 0x9f, 0x02, 0x03, 0xff, 0x82, 0x04, 0x05] = none ∧
    decode [0x9f, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x18, 0x18, 0x19,
            0xff] = none ∧
    decode [0xbf, 0x61, 0x61, 0x01, 0x61, 0x62, 0x9f, 0x02, 0x03, 0xff, 0xff] = none ∧
    decode [0x82, 0x61, 0x61, 0xbf, 0x61, 0x62, 0x61, 0x63, 0xff] = none ∧
    decode [0xbf, 0x63, 0x46, 0x75, 0x6e, 0xf5, 0x63, 0x41, 0x6d, 0x74, 0x21, 0xff] = none ∧
    -- Break, on its own
    decode [0xff] = none := sorry

/-- Non-preferred arguments are turned away (RFC 8949, section 4.2.1),
    for every major type from 0 to 5, every value, and whatever bytes
    follow: additional information 24, 25, 26 or 27, followed by an
    argument in 1, 2, 4 or 8 bytes whose value fits a shorter form.
    Every such argument is `Spec.netBytes` of its value. -/
theorem Spec.cbor_rejects_nonpreferred (mt x : Nat) (rest : List UInt8) (hmt : mt ≤ 5) :
    (x < 24 → decode ((mt * 32 + 24).toUInt8 :: Spec.netBytes 1 x ++ rest) = none) ∧
    (x < 2 ^ 8 → decode ((mt * 32 + 25).toUInt8 :: Spec.netBytes 2 x ++ rest) = none) ∧
    (x < 2 ^ 16 → decode ((mt * 32 + 26).toUInt8 :: Spec.netBytes 4 x ++ rest) = none) ∧
    (x < 2 ^ 32 → decode ((mt * 32 + 27).toUInt8 :: Spec.netBytes 8 x ++ rest) = none) := sorry

/-- An item outside the slice is turned away at the top, and one level
    down: as the next item of an array, or as the next key or the next
    value of a map, after any well-formed items before it in that
    container, and whatever bytes follow. `Spec.outOfSlice` says which
    initial bytes the slice does not carry. -/
theorem Spec.cbor_rejects_nested_out_of_slice (b : UInt8) (rest : List UInt8) (n : Nat)
    (xs : List Value) (kvs : List (Value × Value)) (k : Value)
    (hb : Spec.outOfSlice b = true) (hn : n < 2 ^ 64) (hxs : Value.wfAll xs = true)
    (hkvs : Value.wfPairs kvs = true) (hk : k.wf = true) :
    decode (b :: rest) = none ∧
    (xs.length < n → decode (Spec.itemHead 4 n ++ Spec.encList xs ++ b :: rest) = none) ∧
    (kvs.length < n → decode (Spec.itemHead 5 n ++ Spec.encPairs kvs ++ b :: rest) = none) ∧
    (kvs.length < n →
      decode (Spec.itemHead 5 n ++ Spec.encPairs kvs ++ Spec.enc k ++ b :: rest) = none) :=
  sorry

/-- Text payloads that are not well-formed UTF-8 are turned away. -/
theorem Spec.cbor_rejects_bad_utf8 :
    decode [0x61, 0x80] = none ∧
    decode [0x62, 0xc0, 0x80] = none ∧
    decode [0x62, 0xc3, 0x28] = none ∧
    decode [0x63, 0xed, 0xa0, 0x80] = none ∧
    decode [0x64, 0xf4, 0x90, 0x80, 0x80] = none := sorry

/-- Input that ends inside an item is turned away: no proper prefix of
    the encoding of a well-formed item decodes. -/
theorem Spec.cbor_rejects_truncated (v : Value) (pre post : List UInt8) (hv : v.wf = true)
    (h : pre ++ post = Spec.enc v) (hpost : post ≠ []) : decode pre = none := sorry

/-- Examples: input that ends inside an item, or goes on after it. -/
theorem Spec.cbor_rejects_truncation :
    decode [] = none ∧
    decode [0x18] = none ∧
    decode [0x1b, 0xff, 0xff, 0xff] = none ∧
    decode [0x44, 0x01, 0x02] = none ∧
    decode [0x62, 0xc3] = none ∧
    decode [0x82, 0x01] = none ∧
    decode [0xa2, 0x01, 0x02, 0x03] = none ∧
    decode [0x01, 0x02] = none := sorry
