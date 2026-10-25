# Test results

Run by `tests/run_tests.py` against an independent Python implementation of
the slice written from RFC 8949, in the same file, and against the RFC 8949
Appendix A vectors.
Lean: Lean 4.35.0. Python: 3.10.12.

- Seed: 20261025
- Byte inputs fed to the Lean codec: 2060
- Checks run: 2060
- Checks passed: 2060
- Failures: 0
- Accepted inputs: generated well-formed items, their random-garbage
  counterparts that parse, and the in-slice RFC 8949 Appendix A rows.
- Turned away: the out-of-slice Appendix A rows (floats, simple values,
  `undefined`, tags including bignums, indefinite lengths, break, reserved
  added information), truncations of every generated item, non-preferred
  argument forms for all six major types, malformed UTF-8 text payloads,
  trailing bytes after an item, and empty input.

Axiom check (`Proofs.lean`):

```
'Spec.cbor_decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'Spec.cbor_encode_decode' depends on axioms: [propext, Quot.sound]
'Spec.cbor_rejects_reserved_ai' depends on axioms: [propext, Quot.sound]
'Spec.cbor_rejects_tags' depends on axioms: [propext, Quot.sound]
'Spec.cbor_rejects_simple' depends on axioms: [propext, Quot.sound]
'Spec.cbor_rfc8949_vectors' depends on axioms: [propext]
'Spec.cbor_rejects_out_of_slice' depends on axioms: [propext]
'Spec.cbor_rejects_nonpreferred' depends on axioms: [propext]
'Spec.cbor_rejects_bad_utf8' depends on axioms: [propext]
'Spec.cbor_rejects_truncation' depends on axioms: [propext]
```
