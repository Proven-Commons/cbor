# Test results

Written by `python3 tests/run_tests.py`, which feeds each input to the
command-line tool built from the proved code (`.lake/build/bin/cbor`)
and compares its answer with the oracle's.

- Oracle: reference codec in `tests/run_tests.py`, on Python 3.13.17
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

The plan in issue #1 named Python cbor2 as the oracle. This script uses
its own reference implementation instead, so that it needs nothing
outside Python's standard library.

Each input is one request to the tool: `d` (decode) or `r` (decode and
encode again). This script does not check proofs or axioms; `lake
comparator --paranoid` does.
