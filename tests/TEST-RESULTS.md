# Test results

Written by `python3 tests/run_tests.py`, which feeds each input to the
command-line tool built from the proved code (`.lake/build/bin/cbor`)
and compares its answer with the oracle's.

- Oracle: reference codec in `tests/run_tests.py`, on Python 3.13.17; cross-checked against cbor2 6.1.5, counted apart
- Seed: 20261025
- Inputs: 4298
- Failures: 0

The oracle is a decoder and encoder of the slice written from RFC 8949
apart from the Lean code, in the test script itself. It checks text
payloads with Python's strict UTF-8 decoder, which follows RFC 3629.

Inputs by section:

  - RFC 8949 Appendix A rows and other out-of-slice shapes: 196
  - Generated well-formed items and their truncations: 1310
  - Random bytes: 611
  - Non-preferred arguments and preferred controls: 228
  - Out-of-slice initial bytes, at the top and nested: 595
  - Malformed UTF-8 examples: 6
  - UTF-8 grammar rows: 1350
  - Trailing bytes and empty input: 2

The RFC 8949 Appendix A section runs all 81 rows: the 37 in the slice
are decoded and encoded again, and the 44 outside it (bignums, floats,
`undefined` and other simple values, tags, indefinite-length items) are
turned away, in both directions. None is skipped. It also runs 17 other
shapes outside the slice: simple(24), more tags and indefinite items,
break on its own, and reserved additional information.

Each input is one request to the tool: `d` (decode) or `r` (decode and
encode again). This script does not check proofs or axioms; `lake
comparator --paranoid` does.

## Cross-check against cbor2

The plan in issue #1 named Python cbor2 as the oracle. The record's
oracle is the reference codec above instead, so that CI, which installs
nothing beyond Python's standard library, reruns the same inputs and
gets the same numbers. The reference codec is written apart from the
Lean code, but by the same project. So where cbor2, a CBOR library
written apart from this project, can be imported, the script also has
cbor2 judge the tool's answers. Those requests are counted apart, not
in Inputs, so a run with or without cbor2 records the same Inputs. A
disagreement is a failure, listed under Failures above.

cbor2 accepts an input when `cbor2.loads` reads it, every value in it
is of a kind the slice carries (false, true, null, an integer from
-2^64 to 2^64 - 1, a byte or text string, an array, a map), and
`cbor2.dumps` writes the same bytes back. That last step turns away
what cbor2 reads but the slice does not: arguments not in preferred
form, indefinite lengths, tags that come back as plain values, and
bytes after the item. The tool's `d` answer must be the canonical text
of cbor2's value, or `error` when cbor2 does not accept; for an input
cbor2 accepts, the `r` answer must be the input. An input is left out
when cbor2 reads it, writes other bytes back, and a map in it holds
two keys that are equal as Python values (the same key twice, or 1 and
true, or 0 and false): cbor2 keeps one pair of those, and the slice
keeps every pair, since it applies no duplicate-key rule.

In this run cbor2 6.1.5 could be imported, and the cross-check ran. The
requests by part, where each input cbor2 accepts is asked twice, `d` and
`r`:

  - All inputs of 0, 1 or 2 bytes: 66751 requests; cbor2 accepted 958 inputs, refused 64835
  - RFC 8949 Appendix A, all 81 rows: 118 requests; cbor2 accepted 37 inputs, refused 44
  - Random bytes, 3 to 9 long: 30206 requests; cbor2 accepted 206 inputs, refused 29794
  - Text items with 1 to 4 payload bytes, each random or from 80 to bf: 11012 requests; cbor2 accepted 1012 inputs, refused 8988
  - Random values written by cbor2.dumps, and 3 mutations of each: 28505 requests; cbor2 accepted 8516 inputs, refused 11473, left out 11

In all: 136592 requests, from 10729 inputs cbor2 accepted and 115134 it
refused, with 0 disagreements. 11 inputs were left out because a map in
them holds two keys that are equal as Python values.
