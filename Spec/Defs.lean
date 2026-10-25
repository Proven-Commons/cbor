/-
  The definitions and checks the specification uses, written from
  RFC 8949 and RFC 3629, independently of the proofs. Part of the
  specification for this slice, with `Spec.lean` and `SPEC.md`; the
  specification is unreviewed (see `SPEC.md`).

  The `example`s pin the UTF-8 validator against the boundary cases of
  RFC 3629: one example per row of its well-formed byte condition
  table, plus the known attack shapes (overlong forms, surrogate
  halves, values past U+10FFFF, lone continuations, truncations). A
  mistake in the table fails the build. A standalone codec with the
  validator proved against an independent definition is the job of the
  `utf` project; this slice pins the table by examples instead.
-/

import Cbor

namespace Cbor

open Cbor

/-! ## UTF-8 validator pins (RFC 3629) -/

-- One-byte and multi-byte minima and maxima.
example : Utf8.valid [0x00] = true := rfl
example : Utf8.valid [0x7F] = true := rfl
example : Utf8.valid [0xC2, 0x80] = true := rfl           -- U+0080, smallest 2-byte
example : Utf8.valid [0xDF, 0xBF] = true := rfl           -- U+07FF, largest 2-byte
example : Utf8.valid [0xE0, 0xA0, 0x80] = true := rfl     -- U+0800, smallest 3-byte
example : Utf8.valid [0xED, 0x9F, 0xBF] = true := rfl     -- U+D7FF, below surrogates
example : Utf8.valid [0xEE, 0x80, 0x80] = true := rfl     -- U+E000, above surrogates
example : Utf8.valid [0xEF, 0xBF, 0xBF] = true := rfl     -- U+FFFF
example : Utf8.valid [0xF0, 0x90, 0x80, 0x80] = true := rfl -- U+10000, smallest 4-byte
example : Utf8.valid [0xF4, 0x8F, 0xBF, 0xBF] = true := rfl -- U+10FFFF, the largest

-- The attack shapes, turned away.
example : Utf8.valid [0x80] = false := rfl                -- lone continuation
example : Utf8.valid [0xC0, 0xAF] = false := rfl          -- overlong "/"
example : Utf8.valid [0xC1, 0xBF] = false := rfl          -- overlong
example : Utf8.valid [0xC2] = false := rfl                -- cut short
example : Utf8.valid [0xC2, 0x20] = false := rfl          -- bad continuation
example : Utf8.valid [0xE0, 0x80, 0xAF] = false := rfl    -- overlong
example : Utf8.valid [0xE0, 0xA0] = false := rfl          -- cut short
example : Utf8.valid [0xED, 0xA0, 0x80] = false := rfl    -- surrogate U+D800
example : Utf8.valid [0xED, 0xBF, 0xBF] = false := rfl    -- surrogate U+DFFF
example : Utf8.valid [0xF0, 0x80, 0x80, 0xAF] = false := rfl -- overlong
example : Utf8.valid [0xF0, 0x90, 0x80] = false := rfl    -- cut short
example : Utf8.valid [0xF4, 0x90, 0x80, 0x80] = false := rfl -- past U+10FFFF
example : Utf8.valid [0xF5, 0x80, 0x80, 0x80] = false := rfl -- F5 is not a lead byte
example : Utf8.valid [0xFF] = false := rfl

-- Mixed content: valid text, then one bad string.
example : Utf8.valid [0x61, 0xC3, 0xBC, 0x62] = true := rfl -- "aüb"
example : Utf8.valid [0x61, 0x80, 0x62] = false := rfl

end Cbor
