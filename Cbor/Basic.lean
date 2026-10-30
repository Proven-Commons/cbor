/-
  The encoder and the decoder, for the first slice of RFC 8949:
  definite length unsigned and negative integers, byte strings, text
  strings, arrays, and maps, with the simple values false, true, and
  null.

  The decoder is strict. It accepts only the preferred form of each
  argument (RFC 8949, section 4.2.1): an argument that fits in fewer
  bytes must not be sent in a longer form. It turns away every out of
  slice shape: indefinite length items, tags, floating point values,
  undefined, other simple values, and break. A text payload that is
  not well-formed UTF-8 (RFC 3629) is turned away, as RFC 8949 asks.

  A text item holds its UTF-8 payload bytes. Converting those bytes to
  and from a string happens at the edges, outside this slice.

  The item type `Value` and its well-formedness `Value.wf` are part of
  the specification, in `Cbor/Spec/Value.lean`, so the approval covers them.
-/

import Cbor.Utf8
import Cbor.Spec.Value

namespace Cbor

/-! ## Depth -/

mutual
/-- The nesting depth of an item: a leaf is 1, and a container is one
    more than the deepest item it holds. Each level of nesting takes
    at least one byte on the wire, so the depth never exceeds the
    encoding length. -/
def Value.depth : Value → Nat
  | .array xs => 1 + Value.depthList xs
  | .map kvs => 1 + Value.depthPairs kvs
  | _ => 1

def Value.depthList : List Value → Nat
  | [] => 0
  | x :: xs => max x.depth (Value.depthList xs)

def Value.depthPairs : List (Value × Value) → Nat
  | [] => 0
  | (k, v) :: kvs => max (max k.depth v.depth) (Value.depthPairs kvs)
end

/-! ## The encoder -/

/-- Big-endian bytes of a number, in exactly `n` bytes. -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => beBytes n (x / 256) ++ [(x % 256).toUInt8]

/-- The head of an item: the initial byte for a major type and its
    argument, in the preferred form of RFC 8949, section 4.2.1. -/
def head (mt : Nat) (arg : Nat) : List UInt8 :=
  let m : UInt8 := (mt * 32).toUInt8
  if arg < 24 then [m + arg.toUInt8]
  else if arg ≤ 0xFF then [m + 24, arg.toUInt8]
  else if arg ≤ 0xFFFF then [m + 25] ++ beBytes 2 arg
  else if arg ≤ 0xFFFFFFFF then [m + 26] ++ beBytes 4 arg
  else [m + 27] ++ beBytes 8 arg

mutual
/-- Encode one item. -/
def encode : Value → List UInt8
  | .uint n => head 0 n.toNat
  | .nint n => head 1 n.toNat
  | .bytes bs => head 2 bs.length ++ bs
  | .text bs => head 3 bs.length ++ bs
  | .array xs => head 4 xs.length ++ encodeList xs
  | .map kvs => head 5 kvs.length ++ encodePairs kvs
  | .vfalse => [0xf4]
  | .vtrue => [0xf5]
  | .vnull => [0xf6]

def encodeList : List Value → List UInt8
  | [] => []
  | x :: xs => encode x ++ encodeList xs

def encodePairs : List (Value × Value) → List UInt8
  | [] => []
  | (k, v) :: kvs => encode k ++ encode v ++ encodePairs kvs
end

/-! ## The decoder -/

/-- Read big-endian bytes as a number. -/
def readBe (bs : List UInt8) : Nat := bs.foldl (fun a b => a * 256 + b.toNat) 0

/-- Read the argument after an initial byte, given the added
    information `ai`. Returns the argument and the rest of the input.
    Only the preferred form is accepted: an argument written in more
    bytes than it needs is turned away, as is added information the
    RFC holds back (28 to 30) and the indefinite form (31). -/
def readArg (ai : Nat) (rest : List UInt8) : Option (Nat × List UInt8) :=
  if ai ≤ 23 then some (ai, rest)
  else if ai = 24 then
    match rest with
    | b :: r => if b.toNat ≥ 24 then some (b.toNat, r) else none
    | [] => none
  else if ai = 25 then
    let (w, r) := rest.splitAt 2
    if w.length = 2 ∧ readBe w ≥ 2 ^ 8 then some (readBe w, r) else none
  else if ai = 26 then
    let (w, r) := rest.splitAt 4
    if w.length = 4 ∧ readBe w ≥ 2 ^ 16 then some (readBe w, r) else none
  else if ai = 27 then
    let (w, r) := rest.splitAt 8
    if w.length = 8 ∧ readBe w ≥ 2 ^ 32 then some (readBe w, r) else none
  else none

/-- Decode `n` items in a row, using `dec` to decode each one. -/
def decodeItems (dec : List UInt8 → Option (Value × List UInt8)) :
    Nat → List UInt8 → Option (List Value × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match dec bs with
    | none => none
    | some (x, r) =>
      match decodeItems dec n r with
      | none => none
      | some (xs, r') => some (x :: xs, r')

/-- Decode `n` key and value pairs in a row, using `dec` to decode
    each item. -/
def decodePairs (dec : List UInt8 → Option (Value × List UInt8)) :
    Nat → List UInt8 → Option (List (Value × Value) × List UInt8)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
    match dec bs with
    | none => none
    | some (k, r) =>
      match dec r with
      | none => none
      | some (v, r') =>
        match decodePairs dec n r' with
        | none => none
        | some (kvs, r'') => some ((k, v) :: kvs, r'')

/-- Decode one item from the front of the input, returning the item
    and the unread rest. `fuel` bounds the nesting depth the decoder
    will follow; the caller passes one more than the input length,
    which is always enough, since each level of nesting takes at least
    one byte. -/
def decodeFuel : Nat → List UInt8 → Option (Value × List UInt8)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: rest =>
    let mt := b.toNat / 32
    let ai := b.toNat % 32
    if mt = 7 then
      if b.toNat = 0xf4 then some (.vfalse, rest)
      else if b.toNat = 0xf5 then some (.vtrue, rest)
      else if b.toNat = 0xf6 then some (.vnull, rest)
      else none
    else if mt = 6 then none
    else match readArg ai rest with
      | none => none
      | some (arg, r) =>
        if mt = 0 then some (.uint (UInt64.ofNat arg), r)
        else if mt = 1 then some (.nint (UInt64.ofNat arg), r)
        else if mt = 2 then
          if r.length < arg then none
          else some (.bytes (r.take arg), r.drop arg)
        else if mt = 3 then
          if r.length < arg then none
          else
            let p := r.take arg
            if Utf8.valid p then some (.text p, r.drop arg) else none
        else if mt = 4 then
          match decodeItems (decodeFuel fuel) arg r with
          | some (xs, r') => some (.array xs, r')
          | none => none
        else if mt = 5 then
          match decodePairs (decodeFuel fuel) arg r with
          | some (kvs, r') => some (.map kvs, r')
          | none => none
        else none

/-- Decode exactly one item spanning the whole input. Anything the
    decoder does not accept is `none`: out of slice shapes, a text
    payload that is not well-formed UTF-8, a non-preferred argument,
    bytes left over, or input that ends inside an item. -/
def decode (bs : List UInt8) : Option Value :=
  match decodeFuel (bs.length + 1) bs with
  | some (v, []) => some v
  | _ => none

/-! ## Printing, for the command line tool -/

/-- Lowercase hex of a byte list, as Python's `bytes.hex()` writes it. -/
def hexOf (bs : List UInt8) : String :=
  let digits := "0123456789abcdef".toList
  let pair (b : UInt8) := [digits.getD (b.toNat / 16) '?', digits.getD (b.toNat % 16) '?']
  String.ofList (bs.flatMap pair)

mutual
/-- The canonical text form of an item, for the differential tests.
    Text payloads print as hex, so byte comparisons stay exact. -/
def Value.canonical : Value → String
  | .uint n => toString n.toNat
  | .nint n => "-" ++ toString (n.toNat + 1)
  | .bytes bs => "h'" ++ hexOf bs ++ "'"
  | .text bs => "t'" ++ hexOf bs ++ "'"
  | .array xs => "[" ++ String.intercalate "," (Value.canonList xs) ++ "]"
  | .map kvs => "{" ++ String.intercalate "," (Value.canonPairs kvs) ++ "}"
  | .vfalse => "false"
  | .vtrue => "true"
  | .vnull => "null"

def Value.canonList : List Value → List String
  | [] => []
  | x :: xs => x.canonical :: Value.canonList xs

def Value.canonPairs : List (Value × Value) → List String
  | [] => []
  | (k, v) :: kvs => (k.canonical ++ ":" ++ v.canonical) :: Value.canonPairs kvs
end

end Cbor
