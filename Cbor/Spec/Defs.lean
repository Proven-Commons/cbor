/-
  The definitions the statements in `Cbor/Spec.lean` use besides the code
  under proof: the encoding of an item, written from RFC 8949, and the
  initial bytes the slice does not carry. Part of the specification for
  this slice, with `Cbor/Spec.lean` and `SPEC.md`; the specification is
  unreviewed (see `SPEC.md`).

  - `Cbor/Spec/Utf8.lean`: well-formed UTF-8, written from the grammar of
    RFC 3629, section 4, with one example for each row.
  - `Cbor/Spec/Value.lean`: the item type and its well-formedness.
  - This file: `Cbor.Spec.enc`, the preferred serialization of an item
    (RFC 8949, sections 3, 3.1, 3.3, 4.1 and 4.2.1), with examples at
    every boundary of the argument table, and `Cbor.Spec.outOfSlice`.
-/

import Cbor.Spec.Value

namespace Cbor.Spec

open Cbor

/-- The `n` bytes of `x` in network byte order, most significant byte
    first (RFC 8949, section 3): the first byte is the base-256 digit
    of `x` for 256^(n-1), the last is the digit for 256^0. -/
def netBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => (x / 256 ^ n % 256).toUInt8 :: netBytes n x

/-- The head of an item of major type `mt` with argument `arg`
    (RFC 8949, section 3). The initial byte holds the major type in its
    high 3 bits and the additional information in its low 5 bits. The
    argument takes its preferred serialization (section 4.1; the
    table in section 4.2.1): below 24 it is the additional information
    itself; otherwise it follows the initial byte in 1, 2, 4 or 8
    bytes, the fewest that hold it, with additional information 24,
    25, 26 or 27. -/
def itemHead (mt arg : Nat) : List UInt8 :=
  if arg < 24 then [(mt * 32 + arg).toUInt8]
  else if arg < 2 ^ 8 then (mt * 32 + 24).toUInt8 :: netBytes 1 arg
  else if arg < 2 ^ 16 then (mt * 32 + 25).toUInt8 :: netBytes 2 arg
  else if arg < 2 ^ 32 then (mt * 32 + 26).toUInt8 :: netBytes 4 arg
  else (mt * 32 + 27).toUInt8 :: netBytes 8 arg

mutual
/-- The encoding of an item (RFC 8949, sections 3.1 and 3.3):
    - an unsigned integer `n`: major type 0, argument `n`;
    - the negative integer -1 - n: major type 1, argument `n`;
    - a byte or text string: major type 2 or 3, argument the number of
      bytes, then the bytes;
    - an array: major type 4, argument the number of items, then the
      items in order;
    - a map: major type 5, argument the number of pairs, then each key
      followed by its value, in order;
    - false, true and null: major type 7, simple values 20, 21 and 22,
      held in the additional information. -/
def enc : Value → List UInt8
  | .uint n => itemHead 0 n.toNat
  | .nint n => itemHead 1 n.toNat
  | .bytes bs => itemHead 2 bs.length ++ bs
  | .text bs => itemHead 3 bs.length ++ bs
  | .array xs => itemHead 4 xs.length ++ encList xs
  | .map kvs => itemHead 5 kvs.length ++ encPairs kvs
  | .vfalse => itemHead 7 20
  | .vtrue => itemHead 7 21
  | .vnull => itemHead 7 22

/-- The items of an array, one after another. -/
def encList : List Value → List UInt8
  | [] => []
  | x :: xs => enc x ++ encList xs

/-- The pairs of a map, each key followed by its value. -/
def encPairs : List (Value × Value) → List UInt8
  | [] => []
  | (k, v) :: kvs => enc k ++ enc v ++ encPairs kvs
end

/-- An initial byte the slice does not carry: major type 6 (a tag); in
    major type 7, anything but simple values 20, 21 and 22 (other
    simple values, floats, and break); or additional information 28
    to 31 (held back by RFC 8949, section 3, and the indefinite form).
    No encoding `enc` writes starts an item with such a byte. -/
def outOfSlice (b : UInt8) : Bool :=
  b.toNat / 32 = 6 ||
  (b.toNat / 32 = 7 && !(b.toNat % 32 = 20 || b.toNat % 32 = 21 || b.toNat % 32 = 22)) ||
  28 ≤ b.toNat % 32

/-! ## Examples at each boundary of the argument table (RFC 8949, 4.2.1)

Each argument form at its smallest and largest value. A mistake in
`itemHead` fails the build. -/

example : enc (.uint 23) = [0x17] := rfl
example : enc (.uint 24) = [0x18, 0x18] := rfl
example : enc (.uint 255) = [0x18, 0xff] := rfl
example : enc (.uint 256) = [0x19, 0x01, 0x00] := rfl
example : enc (.uint 65535) = [0x19, 0xff, 0xff] := rfl
example : enc (.uint 65536) = [0x1a, 0x00, 0x01, 0x00, 0x00] := rfl
example : enc (.uint 4294967295) = [0x1a, 0xff, 0xff, 0xff, 0xff] := rfl
example : enc (.uint 4294967296) = [0x1b, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00] := rfl
example : enc (.uint 18446744073709551615) =
    [0x1b, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] := rfl
example : enc (.nint 23) = [0x37] := rfl                -- -24
example : enc (.nint 24) = [0x38, 0x18] := rfl          -- -25
example : enc (.nint 255) = [0x38, 0xff] := rfl         -- -256
example : enc (.nint 256) = [0x39, 0x01, 0x00] := rfl   -- -257
example : enc (.bytes [0xaa]) = [0x41, 0xaa] := rfl
example : enc (.text [0x61, 0x62]) = [0x62, 0x61, 0x62] := rfl
example : enc (.array [.vfalse, .vtrue, .vnull]) = [0x83, 0xf4, 0xf5, 0xf6] := rfl
example : enc (.map [(.uint 1, .array [])]) = [0xa1, 0x01, 0x80] := rfl

example : outOfSlice 0xc0 = true := rfl                 -- tag 0
example : outOfSlice 0xf7 = true := rfl                 -- undefined
example : outOfSlice 0xf9 = true := rfl                 -- half float
example : outOfSlice 0xff = true := rfl                 -- break
example : outOfSlice 0x9f = true := rfl                 -- indefinite array
example : outOfSlice 0x1c = true := rfl                 -- reserved
example : outOfSlice 0xf6 = false := rfl                -- null
example : outOfSlice 0x1b = false := rfl                -- 8-byte unsigned
example : outOfSlice 0xbb = false := rfl                -- map, 8-byte count

end Cbor.Spec
