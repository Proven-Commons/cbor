/-
  The CBOR data item of this slice and its well-formedness. Part of the
  specification: `bar.toml` lists this file, so the approval covers the
  type the statements quantify over and the condition the round trips
  assume. The code in `Cbor/Basic.lean` imports it.

  The slice is RFC 8949, definite-length items only: unsigned and
  negative integers (major types 0 and 1), byte strings (2), text
  strings (3), arrays (4), maps (5), and the simple values false, true,
  and null (major type 7, additional information 20, 21, 22).
-/

import Cbor.Spec.Utf8

namespace Cbor

/-- One CBOR data item, in the slice. -/
inductive Value where
  /-- Unsigned integer, major type 0. -/
  | uint (n : UInt64)
  /-- Negative integer, major type 1: the integer -1 - n. -/
  | nint (n : UInt64)
  /-- Byte string, major type 2. -/
  | bytes (bs : List UInt8)
  /-- Text string, major type 3, held as its UTF-8 payload bytes. -/
  | text (bs : List UInt8)
  /-- Array, major type 4. -/
  | array (xs : List Value)
  /-- Map, major type 5: a list of key and value pairs, in order. -/
  | map (kvs : List (Value × Value))
  /-- Major type 7, additional information 20. -/
  | vfalse
  /-- Major type 7, additional information 21. -/
  | vtrue
  /-- Major type 7, additional information 22. -/
  | vnull

mutual
/-- Does an item fit on the wire in this slice: every text payload is
    well-formed UTF-8 (RFC 8949, section 3.1, asks for RFC 3629, and
    `Cbor.Spec.Utf8.wellFormed` is its section 4 grammar), and every string
    and container length fits in the 64-bit argument. Any item small
    enough to exist in memory passes the length checks. -/
def Value.wf : Value → Bool
  | .uint _ => Bool.true
  | .nint _ => Bool.true
  | .bytes bs => bs.length < 2 ^ 64
  | .text bs => Cbor.Spec.Utf8.wellFormed bs && (bs.length < 2 ^ 64)
  | .array xs => xs.length < 2 ^ 64 && Value.wfAll xs
  | .map kvs => kvs.length < 2 ^ 64 && Value.wfPairs kvs
  | .vfalse => Bool.true
  | .vtrue => Bool.true
  | .vnull => Bool.true

/-- Every item of the list is well-formed. -/
def Value.wfAll : List Value → Bool
  | [] => true
  | x :: xs => x.wf && Value.wfAll xs

/-- Every key and every value of the list is well-formed. -/
def Value.wfPairs : List (Value × Value) → Bool
  | [] => true
  | (k, v) :: kvs => k.wf && v.wf && Value.wfPairs kvs
end

example : (Value.text [0x61, 0xC3, 0xBC]).wf = true := rfl
example : (Value.text [0xFF]).wf = false := rfl
example : (Value.array [.text [0x61], .map [(.uint 1, .text [0xED, 0xA0, 0x80])]]).wf = false := rfl

end Cbor
