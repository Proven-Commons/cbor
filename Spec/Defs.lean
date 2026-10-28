/-
  The definitions the statements in `Spec.lean` use besides the code
  under proof. Part of the specification for this slice, with
  `Spec.lean` and `SPEC.md`; the specification is unreviewed (see
  `SPEC.md`).

  - `Spec/Utf8.lean`: well-formed UTF-8, written from the grammar of
    RFC 3629, section 4, with one example for each row.
  - `Spec/Value.lean`: the item type and its well-formedness.
-/

import Spec.Value
