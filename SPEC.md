# Specification: cbor

A CBOR codec: a decoder and encoder for a slice of RFC 8949. This
specification is unreviewed: `bar.toml` lists it together with
`Cbor/Spec.lean`, `Cbor/Spec/Defs.lean`, `Cbor/Spec/Value.lean` and `Cbor/Spec/Utf8.lean`,
and its approval section is empty until a reviewer who did not write
this specification approves it in a pull request.

Bytes are `List UInt8`. The command-line tool converts at the edges.

## The slice

RFC 8949, definite-length items only, with every argument in its
preferred (shortest) form (sections 4.1 and 4.2.1):

- Major type 0: unsigned integers, argument range 0 to 2^64 - 1.
- Major type 1: negative integers, `-1 - n` for argument `n`.
- Major type 2: byte strings, definite length.
- Major type 3: text strings, definite length, payload required to be
  well-formed UTF-8 (RFC 3629, as section 3.1 of RFC 8949 asks).
  `Cbor.Spec.Utf8.wellFormed` in `Cbor/Spec/Utf8.lean` writes the grammar of
  RFC 3629, section 4: its nine rows of byte ranges, and a split of the
  payload into characters that each match a row. Each row has examples
  there, checked by the build.
- Major type 4: arrays, definite length.
- Major type 5: maps, definite length.
- Major type 7, additional information 20, 21, 22: `false`, `true`,
  `null`.

Out of slice, always turned away: tags (major type 6), indefinite-length
items and break (additional information 31), reserved additional
information 28 to 30, `undefined`, other simple values, half, single,
and double floats, and any argument not in preferred form.
`Cbor.Spec.outOfSlice` in `Cbor/Spec/Defs.lean` names the initial bytes the slice
does not carry: major type 6, major type 7 except simple values 20 to
22, and additional information 28 to 31.

## Well-formed items

`Value` in `Cbor/Spec/Value.lean` is the item type: one constructor for each
kind of item in the slice. `Value.wf` says when an item can be sent:
every text payload is well-formed UTF-8 (`Cbor.Spec.Utf8.wellFormed`), and
every string and container length is below 2^64, so it fits the 64-bit
argument. Both are spec files, so the approval covers them.

## Encoding

`Cbor.Spec.enc` in `Cbor/Spec/Defs.lean` is the encoding, written from RFC 8949:

- `Cbor.Spec.itemHead mt arg` is the head (section 3): one initial byte with
  the major type in its high 3 bits and the additional information in
  its low 5 bits. An argument below 24 is the additional information
  itself. A larger one follows in 1, 2, 4 or 8 bytes, the fewest that
  hold it (below 2^8, 2^16, 2^32, or 2^64), with additional information
  24, 25, 26 or 27 (the preferred serialization of section 4.1, and the
  table of section 4.2.1).
- `Cbor.Spec.netBytes n x` is the `n` bytes of `x` in network byte order.
- Unsigned `n` has major type 0 and argument `n`; the negative integer
  `-1 - n` has major type 1 and argument `n`; byte and text strings
  have major type 2 or 3, their length as argument, then their bytes;
  arrays and maps have major type 4 or 5, their count of items or pairs
  as argument, then the items, or each key followed by its value, in
  order (section 3.1). `false`, `true` and `null` are major type 7 with
  simple values 20, 21 and 22 (section 3.3).

Examples in the same file check each boundary of the argument table:
23 and 24, 255 and 256, 65535 and 65536, 2^32 - 1 and 2^32, and
2^64 - 1. `Cbor.Spec.cbor_encode_spec` proves that `encode` in
`Cbor/Basic.lean` writes `Cbor.Spec.enc` for every item.

## Decoding

`decode` reads one item and requires it to end at the last input byte.
It returns `none` for everything it does not accept: out-of-slice
initial bytes, non-preferred arguments, truncated input, text that is
not well-formed UTF-8, and bytes left over after the item.
`Cbor.Spec.cbor_encode_decode` says exactly what it accepts: the encodings
of the well-formed items. The rejection theorems state each kind of
input it turns away for every input of that shape.

## What must always hold

Each property is a theorem in `Cbor/Spec.lean`, under the name given. The
statements there carry `sorry` on purpose: the proofs live under the
same names in `Cbor/Proofs/`, and the build fails if any proof breaks.

| Property | Theorem |
|----------|---------|
| Decoding the encoding of a well-formed item returns the item | `Cbor.Spec.cbor_decode_encode` |
| The decoder accepts a byte list exactly when it is the encoding of a well-formed item, and returns that item | `Cbor.Spec.cbor_encode_decode` |
| The encoder writes `Cbor.Spec.enc`, for every item | `Cbor.Spec.cbor_encode_spec` |
| The decoder's UTF-8 check is the RFC 3629 grammar, on every byte list | `Cbor.Spec.cbor_utf8_valid_eq` |
| Additional information 28 to 31 is turned away, whatever follows | `Cbor.Spec.cbor_rejects_reserved_ai` |
| Tags are turned away, whatever follows | `Cbor.Spec.cbor_rejects_tags` |
| Major type 7 other than false, true, null is turned away, whatever follows | `Cbor.Spec.cbor_rejects_simple` |
| Every non-preferred argument in major types 0 to 5 is turned away, whatever follows | `Cbor.Spec.cbor_rejects_nonpreferred` |
| An out-of-slice item at the top, or one level inside an array or map after well-formed items, is turned away | `Cbor.Spec.cbor_rejects_nested_out_of_slice` |
| No proper prefix of the encoding of a well-formed item decodes | `Cbor.Spec.cbor_rejects_truncated` |
| The 37 in-slice rows of RFC 8949 Appendix A hold, both directions | `Cbor.Spec.cbor_rfc8949_vectors` |
| The 44 out-of-slice rows of Appendix A, and break alone, are turned away | `Cbor.Spec.cbor_rejects_out_of_slice` |
| Five example text items with bad UTF-8 are turned away | `Cbor.Spec.cbor_rejects_bad_utf8` |
| Eight example inputs are turned away: empty, cut short inside an item, or going on after one | `Cbor.Spec.cbor_rejects_truncation` |

`Cbor.Spec.cbor_encode_decode` is an if and only if: `decode bs = some v`
holds exactly when `v.wf = true` and `encode v = bs`. With
`Cbor.Spec.cbor_encode_spec`, `encode v` is `Cbor.Spec.enc v`. So the decoder
accepts the encodings of the well-formed items that RFC 8949 and this
slice define, and nothing else, and never returns an item that is not
well-formed.

`Cbor.Spec.cbor_rejects_nested_out_of_slice` states one level of nesting. At
any depth, the decoder accepts only `Cbor.Spec.enc v` for a well-formed `v`,
and `Cbor.Spec.enc` starts no item with a byte `Cbor.Spec.outOfSlice` names; that
second point is read from the definition of `Cbor.Spec.enc`, not stated as a
theorem.

## The command-line tool

`Main.lean` reads one request per line and prints one answer per line:

- `d <hex>` decodes the bytes and prints the item in a canonical text
  form, or `error`. The canonical form prints integers in decimal,
  negative integers as `-n`, byte strings as `h'<hex>'`, text strings as
  `t'<hex of the UTF-8 bytes>'`, arrays as `[a,b]`, maps as `{k:v}`,
  and `false`, `true`, `null`.
- `r <hex>` decodes, then encodes again, and prints the lowercase hex
  of the encoding, or `error`. For every input the decoder accepts,
  `Cbor.Spec.cbor_encode_decode` says the encoding is the input's bytes, so
  the answer is the input in lowercase hex.

Hex is two lowercase or uppercase digits per byte. Any other line,
including odd-length hex, prints `error`.
