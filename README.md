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

The round-trip theorems, in `Proofs/RoundTrip.lean`:

- `Spec.cbor_decode_encode`: decoding the encoding of a well-formed
  item returns the same item (completeness).
- `Spec.cbor_encode_decode`: the decoder accepts bytes `bs` and returns
  the item `v` if and only if `v` is well-formed (`Value.wf`) and `bs`
  is the encoding of `v`. So it accepts exactly the encodings of the
  well-formed items, and nothing else.

The rejection theorems, in `Proofs/Cbor.lean`:

- `Spec.cbor_rejects_reserved_ai`: added information 28 to 31 is turned
  away (reserved forms and indefinite lengths).
- `Spec.cbor_rejects_tags`: tags (major type 6) are turned away.
- `Spec.cbor_rejects_simple`: `undefined`, other simple values, every
  float, and break are turned away.
- `Spec.cbor_rfc8949_vectors`: the in-slice rows of RFC 8949 Appendix A
  hold in both directions.
- `Spec.cbor_rejects_out_of_slice`: the out-of-slice rows of Appendix A
  are turned away.
- `Spec.cbor_rejects_nonpreferred`: a value that fits in fewer bytes
  must not use a longer form.
- `Spec.cbor_rejects_bad_utf8`: text payloads that are not well-formed
  UTF-8 are turned away.
- `Spec.cbor_rejects_truncation`: input that ends inside an item is
  turned away.

Axiom check: each proof depends only on the standard Lean axioms
(`propext`, `Classical.choice`, `Quot.sound`, or a subset). Full output
is recorded in `tests/TEST-RESULTS.md`.

## The slice

In: major types 0 (unsigned) and 1 (negative) integers up to 64 bits,
definite-length byte strings, definite-length text strings with
well-formed UTF-8 payloads, definite-length arrays and maps, and
`false`, `true`, `null`. Arguments must use the preferred (shortest)
form, as RFC 8949 section 4.2.1 defines.

Out, always turned away: tags, indefinite-length items and break,
reserved added information 28 to 30, `undefined`, other simple values,
and every float.

## What is not proved

Read this before trusting the codec with real data:

- Nothing outside the slice is handled: no tags (so no dates or
  bignums), no floats, no indefinite lengths, no `undefined`.
- Maps are read and written as ordered lists of pairs. No duplicate-key
  rule is applied, and no canonical key ordering is checked or produced;
  RFC 8949's core deterministic encoding (section 4.2) sorts map keys,
  and this slice does not.
- The CLI is a thin wrapper for the differential tests, not a file
  tool. It reads requests on stdin.
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
