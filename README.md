# cbor: a CBOR codec whose decoder accepts nothing but encodings

This repo decodes and encodes a slice of RFC 8949 CBOR: definite-length
items in preferred (shortest) form. A machine-checked proof shows the
decoder accepts exactly the encodings of the slice's well-formed items,
and nothing else.

It is a Proven Commons project, working toward the verified bar
published in the org's home repo,
[mission](https://github.com/Proven-Commons/mission). It does not meet
the bar yet.

Status: in progress. The specification has no approval from a reviewer
who did not write it, and the bar check has not yet passed in CI with
the branch rule in place, so this project is not verified.

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
decodes and encodes again, printing the lowercase hex of the encoding.
For any input the decoder accepts, `Cbor.Spec.cbor_encode_decode` says the
encoding is the input's bytes, so the answer is the input in lowercase
hex. The tool's hex parsing and printing are not proved; see What is
not proved.

## What is proved

Each claim below is a theorem of `Cbor/Spec.lean`, the challenge file, proved
under the same name in `Cbor/Proofs/`. The definitions the statements use
besides the code are spec files too: the item type `Value` and
well-formedness `Value.wf` in `Cbor/Spec/Value.lean`, well-formed UTF-8 in
`Cbor/Spec/Utf8.lean`, and the encoding `Cbor.Spec.enc` in `Cbor/Spec/Defs.lean`.

The round trip, and what the encoding is:

| Claim | Theorem |
|-------|---------|
| Decoding the encoding of a well-formed item gives the item back. | `Cbor.Spec.cbor_decode_encode` |
| The decoder accepts bytes `bs` and returns the item `v` if and only if `v` is well-formed (`Value.wf`) and `bs` is the encoding of `v`. So it accepts the encodings of the well-formed items and nothing else, and never returns an item that is not well-formed. | `Cbor.Spec.cbor_encode_decode` |
| For every item, the encoder writes `Cbor.Spec.enc`: the encoding `Cbor/Spec/Defs.lean` writes from RFC 8949, sections 3, 3.1 and 3.3, with each argument in its preferred (shortest) form, as sections 4.1 and 4.2.1 ask. | `Cbor.Spec.cbor_encode_spec` |
| The decoder's UTF-8 check gives the same answer, on every byte list, as the grammar of RFC 3629, section 4, written in `Cbor/Spec/Utf8.lean`. `Value.wf` asks every text payload to meet that grammar. | `Cbor.Spec.cbor_utf8_valid_eq` |

What the decoder turns away, for every input of the shape named:

| Claim | Theorem |
|-------|---------|
| An initial byte with additional information 28 to 31 (reserved, or the indefinite form), whatever follows. | `Cbor.Spec.cbor_rejects_reserved_ai` |
| A tag (major type 6), whatever follows. | `Cbor.Spec.cbor_rejects_tags` |
| In major type 7, any initial byte but false, true and null: undefined, other simple values, every float, and break, whatever follows. | `Cbor.Spec.cbor_rejects_simple` |
| In major types 0 to 5, additional information 24, 25, 26 or 27 followed by an argument whose value fits a shorter form, whatever follows. | `Cbor.Spec.cbor_rejects_nonpreferred` |
| An item whose initial byte is outside the slice (`Cbor.Spec.outOfSlice`), at the top, or as the next item of an array or the next key or value of a map, after any well-formed items before it in that container, whatever follows. This theorem covers one level of nesting; see What is not proved for deeper ones. | `Cbor.Spec.cbor_rejects_nested_out_of_slice` |
| Input that ends inside an item: no proper prefix of the encoding of a well-formed item decodes. | `Cbor.Spec.cbor_rejects_truncated` |

Examples, checked by the proofs:

| Claim | Theorem |
|-------|---------|
| All 37 rows of RFC 8949 Appendix A that are in the slice hold in both directions: encoding the item gives the bytes, and decoding the bytes gives the item. | `Cbor.Spec.cbor_rfc8949_vectors` |
| All 44 rows of Appendix A outside the slice are turned away (bignums, floats, undefined and other simple values, tags, indefinite-length items alone and nested), and so is break on its own. | `Cbor.Spec.cbor_rejects_out_of_slice` |
| Five text items whose payloads are not well-formed UTF-8 are turned away. | `Cbor.Spec.cbor_rejects_bad_utf8` |
| Eight inputs are turned away: the empty input, six that end inside an item, and one that goes on after an item. | `Cbor.Spec.cbor_rejects_truncation` |

`lake comparator --paranoid` checks that each proof proves exactly the
statement in `Cbor/Spec.lean`, uses no axiom but `propext`,
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
- That `Cbor.Spec.enc`, `Value.wf` and `Cbor.Spec.Utf8.wellFormed` say what
  RFC 8949 and RFC 3629 say is the judgment of the spec reviewer, not a
  theorem. Examples in the spec files pin each boundary of the argument
  table and each row of the UTF-8 grammar.
- `Cbor.Spec.cbor_rejects_nested_out_of_slice` covers an out-of-slice item
  one level inside an array or map. For deeper ones there is no
  theorem of their own: `Cbor.Spec.cbor_encode_decode` and
  `Cbor.Spec.cbor_encode_spec` say the decoder accepts only `Cbor.Spec.enc v`,
  and that `Cbor.Spec.enc` never starts an item with such a byte is read
  from its definition. No row of Appendix A nests an out-of-slice item
  more than one level down. The three rows with an indefinite item
  inside a definite array (`83018202039f0405ff`, `83019f0203ff820405`
  and `826161bf61626163ff`) are instances of this theorem, and
  `Cbor.Spec.cbor_rejects_out_of_slice` also lists them. The tests nest
  such items up to three levels down.
- The command-line tool in `Main.lean` calls the proved `decode` and
  `encode`, but its hex parsing and the canonical text form it prints
  are not proved; the tests exercise them. It is a thin wrapper for the
  differential tests, not a file tool, and reads requests on stdin.
- Speed and memory use are not proved.

## What you must trust

- The Lean 4.35.0 kernel, and the five other kernels that
  `lake comparator --paranoid` runs (`leanchecker-paranoid`,
  `lean4lean`, `nanoda`, `con-leche`, `con-ron`): a bug that every one
  of them shares would be outside the proof.
- The Lean compiler and runtime, which turn the proved definitions into
  the program that runs: a bug in them could make it differ.
- The hardware and operating system the program runs on.
- The specification itself: `SPEC.md`, `Cbor/Spec.lean`, and the
  definitions in `Cbor/Spec/Defs.lean`, `Cbor/Spec/Value.lean` and
  `Cbor/Spec/Utf8.lean`, which say what the theorems mean.

There are no dependencies: `lake-manifest.json` lists no packages. The
code uses none of the features bar item 4 forbids, so `bar.toml` lists
no exceptions.

## Re-check it

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake build` builds the code, the challenge file and the proofs.
`lake comparator --paranoid` checks, in a sandbox, that each theorem
named in `comparator.json` proves exactly the statement in `Cbor/Spec.lean`,
uses only the three standard axioms, and passes every kernel. The test
script builds the tool if needed, runs every input against the oracle,
and rewrites `tests/TEST-RESULTS.md`. Where Python's cbor2 can be
imported, the script also has cbor2, a CBOR library written apart from
this project, judge the tool's answers, counted apart from the
record's inputs. The record says whether that ran, with which version,
and how to install it.
