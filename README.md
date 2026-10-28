# cbor: a CBOR codec whose decoder accepts nothing but encodings

This repo decodes and encodes a slice of RFC 8949 CBOR: definite-length
items in preferred (shortest) form. A machine-checked proof shows the
decoder accepts exactly the encodings of the slice's well-formed items,
and nothing else.

It is a Proven Commons project, built to the verified bar published in
the org's home repo, [mission](https://github.com/Proven-Commons/mission).
Status: first slice, October 2026.

## Run it

Needs Lean 4.35.0 (install with elan, toolchain pinned in
`lean-toolchain`).

```
lake build
printf 'd 83010203\n' | .lake/build/bin/cbor
printf 'r 83010203\n' | .lake/build/bin/cbor
```

The tool reads one request per line. `d <hex>` prints the item in a
canonical text form (`[1,2,3]` for the example), or `error`. `r <hex>`
decodes and encodes again, printing the lowercase hex of the encoding;
for any input the decoder accepts, the answer is the input itself.

## What is proved

Each claim below is a theorem of `Spec.lean`, the challenge file, proved
under the same name in `Proofs/`. The definitions the statements use
besides the code are spec files too: the item type `Value` and
well-formedness `Value.wf` in `Spec/Value.lean`, well-formed UTF-8 in
`Spec/Utf8.lean`, and the encoding `Spec.enc` in `Spec/Defs.lean`.

The round trip, and what the encoding is:

| Claim | Theorem |
|-------|---------|
| Decoding the encoding of a well-formed item gives the item back. | `Spec.cbor_decode_encode` |
| The decoder accepts bytes `bs` and returns the item `v` if and only if `v` is well-formed (`Value.wf`) and `bs` is the encoding of `v`. So it accepts the encodings of the well-formed items and nothing else, and never returns an item that is not well-formed. | `Spec.cbor_encode_decode` |
| For every item, the encoder writes `Spec.enc`: the encoding `Spec/Defs.lean` writes from RFC 8949, sections 3, 3.1 and 3.3, with each argument in its preferred (shortest) form, as sections 4.1 and 4.2.1 ask. | `Spec.cbor_encode_spec` |
| The decoder's UTF-8 check gives the same answer, on every byte list, as the grammar of RFC 3629, section 4, written in `Spec/Utf8.lean`. `Value.wf` asks every text payload to meet that grammar. | `Spec.cbor_utf8_valid_eq` |

What the decoder turns away, for every input of the shape named:

| Claim | Theorem |
|-------|---------|
| An initial byte with additional information 28 to 31 (reserved, or the indefinite form), whatever follows. | `Spec.cbor_rejects_reserved_ai` |
| A tag (major type 6), whatever follows. | `Spec.cbor_rejects_tags` |
| In major type 7, any initial byte but false, true and null: undefined, other simple values, every float, and break, whatever follows. | `Spec.cbor_rejects_simple` |
| In major types 0 to 5, additional information 24, 25, 26 or 27 followed by an argument whose value fits a shorter form, whatever follows. | `Spec.cbor_rejects_nonpreferred` |
| An item whose initial byte is outside the slice (`Spec.outOfSlice`), at the top, or as the next item of an array or the next key or value of a map, after any well-formed items before it in that container, whatever follows. This theorem covers one level of nesting; see What is not proved for deeper ones. | `Spec.cbor_rejects_nested_out_of_slice` |
| Input that ends inside an item: no proper prefix of the encoding of a well-formed item decodes. | `Spec.cbor_rejects_truncated` |

Examples, checked by the proofs:

| Claim | Theorem |
|-------|---------|
| All 37 rows of RFC 8949 Appendix A that are in the slice hold in both directions: encoding the item gives the bytes, and decoding the bytes gives the item. | `Spec.cbor_rfc8949_vectors` |
| All 44 rows of Appendix A outside the slice are turned away (bignums, floats, undefined and other simple values, tags, indefinite-length items alone and nested), and so is break on its own. | `Spec.cbor_rejects_out_of_slice` |
| Five text items whose payloads are not well-formed UTF-8 are turned away. | `Spec.cbor_rejects_bad_utf8` |
| Eight inputs that end inside an item, or go on after one, are turned away. | `Spec.cbor_rejects_truncation` |

`lake comparator --paranoid` checks that each proof proves exactly the
statement in `Spec.lean`, uses no axiom but `propext`,
`Classical.choice` and `Quot.sound`, and is accepted by every kernel
that ships with Lean.

## The slice

In: major types 0 (unsigned) and 1 (negative) integers up to 64 bits,
definite-length byte strings, definite-length text strings with
well-formed UTF-8 payloads, definite-length arrays and maps, and
`false`, `true`, `null`. Arguments must use the preferred (shortest)
form, as RFC 8949 sections 4.1 and 4.2.1 define.

Out, always turned away: tags, indefinite-length items and break,
reserved additional information 28 to 30, `undefined`, other simple
values, and every float.

## What is not proved

Read this before trusting the codec with real data:

- Nothing outside the slice is handled: no tags (so no dates or
  bignums), no floats, no indefinite lengths, no `undefined`.
- Maps are read and written as ordered lists of pairs. No duplicate-key
  rule is applied, and no key order is checked or produced. RFC 8949's
  core deterministic encoding (section 4.2.1) also sorts map keys; this
  slice takes only its rule for arguments.
- That `Spec.enc`, `Value.wf` and `Spec.Utf8.wellFormed` say what
  RFC 8949 and RFC 3629 say is the judgment of the spec reviewer, not a
  theorem. Examples in the spec files pin each boundary of the argument
  table and each row of the UTF-8 grammar.
- `Spec.cbor_rejects_nested_out_of_slice` covers an out-of-slice item
  one level inside an array or map. For deeper ones there is no
  theorem of their own: `Spec.cbor_encode_decode` and
  `Spec.cbor_encode_spec` say the decoder accepts only `Spec.enc v`,
  and that `Spec.enc` never starts an item with such a byte is read
  from its definition. The three Appendix A rows with an indefinite
  item two levels down are proved examples, and the tests nest such
  items up to three levels down.
- The command-line tool in `Main.lean` calls the proved `decode` and
  `encode`, but its hex parsing and the canonical text form it prints
  are not proved; the tests exercise them. It is a thin wrapper for the
  differential tests, not a file tool, and reads requests on stdin.
- Speed and memory use are not proved.
- The Lean compiler, runtime, and kernel are trusted, as in every Lean
  project. A bug in them is outside the proof.

## Re-check it

```
lake build
python3 tests/run_tests.py
```

The build fails if a proof breaks. The test script rebuilds if needed,
reruns every comparison against an independent Python implementation of
the slice, and rewrites `tests/TEST-RESULTS.md`.
