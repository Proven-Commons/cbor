/-
  Well-formed UTF-8, written from the grammar in RFC 3629, section 4.
  Unicode's Table 3-7 (Well-Formed UTF-8 Byte Sequences) has the same
  rows. Part of the specification: `bar.toml` lists this file, so the
  approval covers it.

  The grammar of RFC 3629, section 4:

    UTF8-octets = *( UTF8-char )
    UTF8-char   = UTF8-1 / UTF8-2 / UTF8-3 / UTF8-4
    UTF8-1      = %x00-7F
    UTF8-2      = %xC2-DF UTF8-tail
    UTF8-3      = %xE0 %xA0-BF UTF8-tail / %xE1-EC 2( UTF8-tail ) /
                  %xED %x80-9F UTF8-tail / %xEE-EF 2( UTF8-tail )
    UTF8-4      = %xF0 %x90-BF 2( UTF8-tail ) / %xF1-F3 3( UTF8-tail ) /
                  %xF4 %x80-8F 2( UTF8-tail )
    UTF8-tail   = %x80-BF

  `rows` below holds the nine alternatives of `UTF8-char`, with each
  `UTF8-tail` written out as its range. `wellFormed` is
  `UTF8-octets`: the bytes split into a run of characters, each one
  matching a row.
-/

namespace Cbor.Spec.Utf8

/-- The alternatives of `UTF8-char`, one per line of the grammar. Each
    is a list of byte ranges, low and high inclusive, one range for
    each byte of the character. -/
def rows : List (List (Nat × Nat)) :=
  [ [(0x00, 0x7F)],                                           -- UTF8-1
    [(0xC2, 0xDF), (0x80, 0xBF)],                             -- UTF8-2
    [(0xE0, 0xE0), (0xA0, 0xBF), (0x80, 0xBF)],               -- UTF8-3
    [(0xE1, 0xEC), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xED, 0xED), (0x80, 0x9F), (0x80, 0xBF)],
    [(0xEE, 0xEF), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xF0, 0xF0), (0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)], -- UTF8-4
    [(0xF1, 0xF3), (0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xF4, 0xF4), (0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)] ]

/-- Do the bytes match the row: as many bytes as ranges, and each byte
    inside its range. -/
def fits : List (Nat × Nat) → List UInt8 → Bool
  | [], [] => true
  | (lo, hi) :: row, b :: bs => decide (lo ≤ b.toNat ∧ b.toNat ≤ hi) && fits row bs
  | _, _ => false

/-- `UTF8-octets = *( UTF8-char )`, with at most `n` characters: the
    bytes are empty, or some row matches their first bytes and the
    rest splits the same way. -/
def octets : Nat → List UInt8 → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, bs => rows.any fun row => fits row (bs.take row.length) && octets n (bs.drop row.length)

/-- Well-formed UTF-8 (RFC 3629, section 4): the bytes split into
    characters. Every character takes at least one byte, so a split
    never needs more characters than there are bytes. -/
def wellFormed (bs : List UInt8) : Bool := octets bs.length bs

/-! ## One example for each row of the grammar

The smallest and the largest character of each row are well-formed. A
byte just outside a row's range is turned away: overlong forms, the
surrogate halves, values past U+10FFFF, lone and missing tails. A
mistake in `rows` fails the build. -/

example : wellFormed [] = true := rfl
-- UTF8-1: U+0000 and U+007F
example : wellFormed [0x00] = true := rfl
example : wellFormed [0x7F] = true := rfl
example : wellFormed [0x80] = false := rfl                    -- a lone tail
-- UTF8-2: U+0080 and U+07FF
example : wellFormed [0xC2, 0x80] = true := rfl
example : wellFormed [0xDF, 0xBF] = true := rfl
example : wellFormed [0xC1, 0xBF] = false := rfl              -- overlong
example : wellFormed [0xC2, 0x7F] = false := rfl              -- tail below 80
example : wellFormed [0xC2, 0xC0] = false := rfl              -- tail above BF
example : wellFormed [0xC2] = false := rfl                    -- cut short
-- UTF8-3, E0 row: U+0800 and U+0FFF
example : wellFormed [0xE0, 0xA0, 0x80] = true := rfl
example : wellFormed [0xE0, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xE0, 0x9F, 0xBF] = false := rfl        -- overlong
-- UTF8-3, E1-EC row: U+1000 and U+CFFF
example : wellFormed [0xE1, 0x80, 0x80] = true := rfl
example : wellFormed [0xEC, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xE6, 0xB0, 0xB4] = true := rfl         -- U+6C34
example : wellFormed [0xE1, 0x80] = false := rfl              -- cut short
-- UTF8-3, ED row: U+D000 and U+D7FF
example : wellFormed [0xED, 0x80, 0x80] = true := rfl
example : wellFormed [0xED, 0x9F, 0xBF] = true := rfl
example : wellFormed [0xED, 0xA0, 0x80] = false := rfl        -- surrogate U+D800
example : wellFormed [0xED, 0xBF, 0xBF] = false := rfl        -- surrogate U+DFFF
-- UTF8-3, EE-EF row: U+E000 and U+FFFF
example : wellFormed [0xEE, 0x80, 0x80] = true := rfl
example : wellFormed [0xEF, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xEF, 0xBF, 0xC0] = false := rfl        -- tail above BF
-- UTF8-4, F0 row: U+10000 and U+3FFFF
example : wellFormed [0xF0, 0x90, 0x80, 0x80] = true := rfl
example : wellFormed [0xF0, 0xBF, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xF0, 0x8F, 0xBF, 0xBF] = false := rfl  -- overlong
-- UTF8-4, F1-F3 row: U+40000 and U+FFFFF
example : wellFormed [0xF1, 0x80, 0x80, 0x80] = true := rfl
example : wellFormed [0xF3, 0xBF, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xF1, 0x80, 0x80] = false := rfl        -- cut short
-- UTF8-4, F4 row: U+100000 and U+10FFFF
example : wellFormed [0xF4, 0x80, 0x80, 0x80] = true := rfl
example : wellFormed [0xF4, 0x8F, 0xBF, 0xBF] = true := rfl
example : wellFormed [0xF4, 0x90, 0x80, 0x80] = false := rfl  -- past U+10FFFF
-- No row starts with C0, C1, or F5 to FF.
example : wellFormed [0xC0, 0x80] = false := rfl
example : wellFormed [0xF5, 0x80, 0x80, 0x80] = false := rfl
example : wellFormed [0xFF] = false := rfl
-- A run of characters, then one bad byte in the middle.
example : wellFormed [0x61, 0xC3, 0xBC, 0x62] = true := rfl   -- "aüb"
example : wellFormed [0x61, 0x80, 0x62] = false := rfl

end Cbor.Spec.Utf8
