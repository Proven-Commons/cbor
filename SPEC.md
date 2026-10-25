# Specification: cbor

A CBOR codec: a decoder and encoder for a slice of RFC 8949. This
specification is unreviewed: `bar.toml` lists it together with
`Spec.lean` and `Spec/Defs.lean`, and its approval section is empty
until a reviewer who did not write this specification approves it in a
pull request.

Bytes are `List UInt8`. The command-line tool converts at the edges.

## The slice

RFC 8949, definite-length items only, in preferred (shortest) form
(section 4.2.1):

- Major type 0: unsigned integers, argument range 0 to 2^64 - 1.
- Major type 1: negative integers, `-1 - n` for argument `n`.
- Major type 2: byte strings, definite length.
- Major type 3: text strings, definite length, payload required to be
  well-formed UTF-8 (RFC 3629, as section 3.1 of RFC 8949 asks).
- Major type 4: arrays, definite length.
- Major type 5: maps, definite length.
- Major type 7, added information 20, 21, 22: `false`, `true`, `null`.

Out of slice, always turned away: tags (major type 6), indefinite-length
items and break (added information 31), reserved added information 28 to
30, `undefined`, other simple values, half, single, and double floats,
and any argument not in preferred form.

## Encoding

Each well-formed item has exactly one encoding, given by `encode` in
`Cbor/Basic.lean`: the head is the major type and the shortest argument
form; byte and text strings follow with their payload; arrays and maps
follow with their items in order; pairs encode key then value.

## Decoding

`decode` reads one item and requires it to end at the last input byte.
It returns `none` for everything it does not accept: out-of-slice
initial bytes, non-preferred arguments, truncated input, text that is
not well-formed UTF-8, and bytes left over after the item.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The
statements there carry `sorry` on purpose: the proofs live under the
same names in `Proofs/`, and the build fails if any proof breaks.

| Property | Theorem |
|----------|---------|
| Decoding an encoding returns the same item | `Spec.cbor_decode_encode` |
| The decoder accepts nothing but encodings | `Spec.cbor_encode_decode` |
| Reserved and indefinite added information is turned away | `Spec.cbor_rejects_reserved_ai` |
| Tags are turned away | `Spec.cbor_rejects_tags` |
| Other major type 7 values are turned away | `Spec.cbor_rejects_simple` |
| The in-slice RFC 8949 Appendix A vectors hold, both directions | `Spec.cbor_rfc8949_vectors` |
| Out-of-slice Appendix A rows are turned away | `Spec.cbor_rejects_out_of_slice` |
| Non-preferred arguments are turned away | `Spec.cbor_rejects_nonpreferred` |
| Text that is not well-formed UTF-8 is turned away | `Spec.cbor_rejects_bad_utf8` |
| Input that ends inside an item is turned away | `Spec.cbor_rejects_truncation` |

With both round-trip theorems, the decoder accepts exactly the
preferred-form, definite-length encodings of the slice, and nothing else.

## The command-line tool

`Main.lean` reads one request per line and prints one answer per line:

- `d <hex>` decodes the bytes and prints the item in a canonical text
  form, or `error`. The canonical form prints integers in decimal,
  negative integers as `-n`, byte strings as `h'<hex>'`, text strings as
  `t'<hex of the UTF-8 bytes>'`, arrays as `[a,b]`, maps as `{k:v}`,
  and `false`, `true`, `null`.
- `r <hex>` decodes, then encodes again, and prints the lowercase hex
  of the encoding, or `error`. For every input the decoder accepts,
  soundness says the answer is the input itself.

Hex is two lowercase or uppercase digits per byte. Any other line,
including odd-length hex, prints `error`.
