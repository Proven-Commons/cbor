#!/usr/bin/env python3
"""Differential tests for the Proven Commons CBOR codec.

Compares the Lean implementation against an independent Python
implementation of the slice (below), and against the RFC 8949
Appendix A vectors. Run from anywhere:

    python3 tests/run_tests.py

It builds the Lean project if the executable is missing, runs all
cases, writes `tests/TEST-RESULTS.md`, and exits non-zero on failure.
"""

import random
import subprocess
import sys
from pathlib import Path

PILOT_DIR = Path(__file__).resolve().parent.parent
EXE = PILOT_DIR / ".lake" / "build" / "bin" / "cbor"
RESULTS = PILOT_DIR / "tests" / "TEST-RESULTS.md"
SEED = 20261025

checks = 0
failures = []
inputs = 0
accepted = 0
rejected = 0


def check(name, ok, detail=""):
    global checks
    checks += 1
    if not ok:
        failures.append(f"{name}: {detail}")
        print(f"FAIL {name}: {detail}")


# ---------- Independent reference implementation of the slice ----------
# Written from RFC 8949, not from the Lean code. Decode returns
# (canonical_text, rest) or None. Encode takes a Python value tree:
# ("uint", n) ("nint", n) ("bytes", b) ("text", b) ("array", [...])
# ("map", [(k, v)]) ("false",) ("true",) ("null",).

def read_arg(ai, rest):
    if ai < 24:
        return (ai, rest)
    if ai == 24:
        if len(rest) < 1 or rest[0] < 24:
            return None
        return (rest[0], rest[1:])
    if ai == 25:
        if len(rest) < 2:
            return None
        v = int.from_bytes(rest[:2], "big")
        return None if v < 2**8 else (v, rest[2:])
    if ai == 26:
        if len(rest) < 4:
            return None
        v = int.from_bytes(rest[:4], "big")
        return None if v < 2**16 else (v, rest[4:])
    if ai == 27:
        if len(rest) < 8:
            return None
        v = int.from_bytes(rest[:8], "big")
        return None if v < 2**32 else (v, rest[8:])
    return None  # 28..31: reserved or indefinite


def ref_decode(bs):
    if not bs:
        return None
    b, rest = bs[0], bs[1:]
    mt, ai = b >> 5, b & 31
    if mt == 7:
        if b == 0xF4:
            return ("false", rest)
        if b == 0xF5:
            return ("true", rest)
        if b == 0xF6:
            return ("null", rest)
        return None
    if mt == 6:
        return None
    ar = read_arg(ai, rest)
    if ar is None:
        return None
    arg, rest = ar
    if mt == 0:
        return (str(arg), rest)
    if mt == 1:
        return ("-" + str(arg + 1), rest)
    if mt == 2:
        if len(rest) < arg:
            return None
        return ("h'" + bytes(rest[:arg]).hex() + "'", rest[arg:])
    if mt == 3:
        if len(rest) < arg:
            return None
        p = bytes(rest[:arg])
        try:
            p.decode("utf-8")  # strict: rejects overlongs and surrogates
        except UnicodeDecodeError:
            return None
        return ("t'" + p.hex() + "'", rest[arg:])
    if mt == 4:
        items = []
        for _ in range(arg):
            r = ref_decode(rest)
            if r is None:
                return None
            c, rest = r
            items.append(c)
        return ("[" + ",".join(items) + "]", rest)
    if mt == 5:
        pairs = []
        for _ in range(arg):
            k = ref_decode(rest)
            if k is None:
                return None
            kc, rest = k
            v = ref_decode(rest)
            if v is None:
                return None
            vc, rest = v
            pairs.append(kc + ":" + vc)
        return ("{" + ",".join(pairs) + "}", rest)
    return None


def ref_full(bs):
    """Full-input decode: returns canonical text, or None."""
    r = ref_decode(bs)
    if r is None:
        return None
    c, rest = r
    if rest:
        return None
    return c


def ref_head(mt, arg):
    if arg < 24:
        return bytes([(mt << 5) | arg])
    if arg < 2**8:
        return bytes([(mt << 5) | 24, arg])
    if arg < 2**16:
        return bytes([(mt << 5) | 25]) + arg.to_bytes(2, "big")
    if arg < 2**32:
        return bytes([(mt << 5) | 26]) + arg.to_bytes(4, "big")
    return bytes([(mt << 5) | 27]) + arg.to_bytes(8, "big")


def ref_encode(v):
    t = v[0]
    if t == "uint":
        return ref_head(0, v[1])
    if t == "nint":
        return ref_head(1, v[1])
    if t == "bytes":
        return ref_head(2, len(v[1])) + bytes(v[1])
    if t == "text":
        return ref_head(3, len(v[1])) + bytes(v[1])
    if t == "array":
        return ref_head(4, len(v[1])) + b"".join(ref_encode(x) for x in v[1])
    if t == "map":
        out = ref_head(5, len(v[1]))
        for k, w in v[1]:
            out += ref_encode(k) + ref_encode(w)
        return out
    if t == "false":
        return b"\xf4"
    if t == "true":
        return b"\xf5"
    return b"\xf6"


def ref_canonical(v):
    t = v[0]
    if t == "uint":
        return str(v[1])
    if t == "nint":
        return "-" + str(v[1] + 1)
    if t == "bytes":
        return "h'" + bytes(v[1]).hex() + "'"
    if t == "text":
        return "t'" + bytes(v[1]).hex() + "'"
    if t == "array":
        return "[" + ",".join(ref_canonical(x) for x in v[1]) + "]"
    if t == "map":
        return "{" + ",".join(ref_canonical(k) + ":" + ref_canonical(w) for k, w in v[1]) + "}"
    return {"false": "false", "true": "true", "null": "null"}[t]


# The rows of RFC 3629, section 4 (Unicode Table 3-7): the code points
# each row encodes, and its byte ranges, one per byte.
UTF8_ROW_SCALARS = [
    (0x0000, 0x007F), (0x0080, 0x07FF), (0x0800, 0x0FFF), (0x1000, 0xCFFF),
    (0xD000, 0xD7FF), (0xE000, 0xFFFF), (0x10000, 0x3FFFF),
    (0x40000, 0xFFFFF), (0x100000, 0x10FFFF),
]
UTF8_ROW_BYTES = [
    [(0x00, 0x7F)],
    [(0xC2, 0xDF), (0x80, 0xBF)],
    [(0xE0, 0xE0), (0xA0, 0xBF), (0x80, 0xBF)],
    [(0xE1, 0xEC), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xED, 0xED), (0x80, 0x9F), (0x80, 0xBF)],
    [(0xEE, 0xEF), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xF0, 0xF0), (0x90, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xF1, 0xF3), (0x80, 0xBF), (0x80, 0xBF), (0x80, 0xBF)],
    [(0xF4, 0xF4), (0x80, 0x8F), (0x80, 0xBF), (0x80, 0xBF)],
]


# ---------- Lean process driver ----------

class LeanDriver:
    def __init__(self):
        if not EXE.exists():
            subprocess.run(["lake", "build"], cwd=PILOT_DIR, check=True)
        self.proc = subprocess.Popen([str(EXE)], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True)

    def ask(self, op, hexs):
        global inputs
        inputs += 1
        self.proc.stdin.write(f"{op} {hexs}\n")
        self.proc.stdin.flush()
        return self.proc.stdout.readline().rstrip("\n")


# ---------- RFC 8949 Appendix A vectors ----------

# (hex, canonical) for in-slice rows.
RFC_OK = [
    ("00", "0"), ("01", "1"), ("0a", "10"), ("17", "23"),
    ("1818", "24"), ("1819", "25"), ("1864", "100"), ("1903e8", "1000"),
    ("1a000f4240", "1000000"), ("1b000000e8d4a51000", "1000000000000"),
    ("1bffffffffffffffff", "18446744073709551615"),
    ("20", "-1"), ("29", "-10"), ("3863", "-100"), ("3903e7", "-1000"),
    ("3bffffffffffffffff", "-18446744073709551616"),
    ("40", "h''"), ("4401020304", "h'01020304'"),
    ("60", "t''"), ("6161", "t'61'"), ("6449455446", "t'49455446'"),
    ("62225c", "t'225c'"), ("62c3bc", "t'c3bc'"), ("63e6b0b4", "t'e6b0b4'"),
    ("64f0908591", "t'f0908591'"),
    ("80", "[]"), ("83010203", "[1,2,3]"),
    ("8301820203820405", "[1,[2,3],[4,5]]"),
    ("98190102030405060708090a0b0c0d0e0f101112131415161718181819",
     "[" + ",".join(str(i) for i in range(1, 26)) + "]"),
    ("a0", "{}"), ("a201020304", "{1:2,3:4}"),
    ("a26161016162820203", "{t'61':1,t'62':[2,3]}"),
    ("826161a161626163", "[t'61',{t'62':t'63'}]"),
    ("a56161614161626142616361436164614461656145",
     "{t'61':t'41',t'62':t'42',t'63':t'43',t'64':t'44',t'65':t'45'}"),
    ("f4", "false"), ("f5", "true"), ("f6", "null"),
]

# The other 44 rows of RFC 8949 Appendix A, all outside the slice:
# bignums, floats, undefined and other simple values, tags, and
# indefinite-length items, alone or nested. With RFC_OK, this is every
# row of Appendix A (81).
RFC_A_OUT = [
    "c249010000000000000000", "c349010000000000000000",
    "f90000", "f98000", "f93c00", "fb3ff199999999999a", "f93e00", "f97bff",
    "fa47c35000", "fa7f7fffff", "fb7e37e43c8800759c", "f90001", "f90400",
    "f9c400", "fbc010666666666666", "f97c00", "f97e00", "f9fc00",
    "fa7f800000", "fa7fc00000", "faff800000", "fb7ff0000000000000",
    "fb7ff8000000000000", "fbfff0000000000000",
    "f7", "f0", "f8ff",
    "c074323031332d30332d32315432303a30343a30305a", "c11a514b67b0",
    "c1fb41d452d9ec200000", "d74401020304", "d818456449455446",
    "d82076687474703a2f2f7777772e6578616d706c652e636f6d",
    "5f42010243030405ff", "7f657374726561646d696e67ff", "9fff",
    "9f018202039f0405ffff", "9f01820203820405ff", "83018202039f0405ff",
    "83019f0203ff820405",
    "9f0102030405060708090a0b0c0d0e0f101112131415161718181819ff",
    "bf61610161629f0203ffff", "826161bf61626163ff",
    "bf6346756ef563416d7421ff",
]

# Other shapes outside the slice, not rows of Appendix A: simple(24),
# which section 3.3 calls not well-formed, more tags and indefinite
# items, break on its own, and reserved additional information.
OTHER_REJECT = [
    "f818", "d8204567696751554d", "d8234567696751554d",
    "5f4100ff", "7f6141ff", "bf616101ff", "ff",
    "1c", "1d", "1e", "1f", "3c", "5c", "7c", "9c", "bc", "dc",
]


def out_of_slice(b):
    """An initial byte the slice does not carry: a tag, major type 7
    other than false, true and null, or additional information 28 to
    31. Written from RFC 8949 section 3, apart from the Lean code."""
    mt, ai = b >> 5, b & 31
    return mt == 6 or (mt == 7 and ai not in (20, 21, 22)) or ai >= 28


def completion(b):
    """Bytes that would finish an item that starts with b, if the slice
    carried it: a tag's content, a float's or simple value's following
    bytes, the end of an empty indefinite item."""
    mt, ai = b >> 5, b & 31
    if mt == 6:
        return bytes([0x00])
    if mt == 7:
        return bytes({24: 1, 25: 2, 26: 4, 27: 8}.get(ai, 0))
    if ai == 31:
        return bytes([0xff])
    return b""


def main():
    global accepted, rejected
    drv = LeanDriver()

    # RFC vectors, both directions.
    for hexs, canon in RFC_OK:
        check(f"rfc d {hexs}", drv.ask("d", hexs) == canon,
              f"want {canon}")
        check(f"rfc r {hexs}", drv.ask("r", hexs) == hexs,
              "re-encode must return the input")
    for hexs in RFC_A_OUT + OTHER_REJECT:
        check(f"rfc reject {hexs}", drv.ask("d", hexs) == "error")
        check(f"rfc reject r {hexs}", drv.ask("r", hexs) == "error")

    rng = random.Random(SEED)

    def rand_scalar():
        """A Unicode scalar value from a random row of RFC 3629's
        grammar (Unicode Table 3-7), often at a row's first or last
        code point."""
        lo, hi = rng.choice(UTF8_ROW_SCALARS)
        return rng.choice([lo, hi, rng.randrange(lo, hi + 1)])

    # Random generated in-slice items: encode with the reference, then
    # compare decode + re-encode.
    def gen(depth):
        choices = ["uint", "nint", "bytes", "text", "false", "true", "null"]
        if depth < 3:
            choices += ["array", "map"]
        t = rng.choice(choices)
        if t == "uint":
            return ("uint", rng.choice([0, 1, 23, 24, 255, 256, 65535, 65536,
                                        2**32 - 1, 2**32, 2**64 - 1,
                                        rng.randrange(0, 2**64)]))
        if t == "nint":
            return ("nint", rng.choice([0, 23, 24, 255, 256, 2**32,
                                        2**64 - 1, rng.randrange(0, 2**64)]))
        if t == "bytes":
            return ("bytes", bytes(rng.randrange(256)
                                   for _ in range(rng.randrange(0, 10))))
        if t == "text":
            n = rng.randrange(0, 6)
            cps = [rand_scalar() for _ in range(n)]
            return ("text", "".join(chr(c) for c in cps).encode("utf-8"))
        if t == "array":
            return ("array", [gen(depth + 1) for _ in range(rng.randrange(0, 5))])
        if t == "map":
            return ("map", [(gen(depth + 1), gen(depth + 1))
                            for _ in range(rng.randrange(0, 4))])
        return (t,)

    for i in range(400):
        v = gen(0)
        enc = ref_encode(v)
        canon = ref_canonical(v)
        check(f"gen d {i}", drv.ask("d", enc.hex()) == canon, f"want {canon}")
        check(f"gen r {i}", drv.ask("r", enc.hex()) == enc.hex(),
              "soundness: re-encode returns the input")
        # Every truncation must be turned away.
        for cut in range(1, min(len(enc), 4)):
            check(f"gen trunc {i}.{cut}", drv.ask("d", enc[:cut].hex()) == "error")
        accepted += 1

    # Random garbage: compare acceptance and canonical form.
    for i in range(600):
        bs = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 14)))
        want = ref_full(list(bs))
        got = drv.ask("d", bs.hex())
        if want is None:
            check(f"rand d {i}", got == "error", f"accepted {bs.hex()}")
            rejected += 1
        else:
            check(f"rand d {i}", got == want, f"{bs.hex()}: want {want}")
            check(f"rand r {i}", drv.ask("r", bs.hex()) == bs.hex(),
                  "re-encode returns the input")
            accepted += 1

    # Non-preferred arguments, at every boundary of the argument table
    # (RFC 8949 section 4.2.1) and at random values below it, for each
    # major type 0 to 5: turned away. Strings, arrays and maps carry a
    # full body, so only the argument's form is wrong. The same value in
    # its preferred form is accepted, as a control.
    def body(mt, n):
        if mt < 2:
            return b""
        return {2: b"\x00", 3: b"a", 4: b"\x00", 5: b"\x00\x00"}[mt] * n
    limits = {24: 24, 25: 2**8, 26: 2**16, 27: 2**32}
    widths = {24: 1, 25: 2, 26: 4, 27: 8}
    for mt in [0, 1, 2, 3, 4, 5]:
        for ai in [24, 25, 26, 27]:
            lim = limits[ai]
            values = sorted(v for v in {0, 1, 23, lim // 256 - 1, lim // 256,
                                        lim - 1, rng.randrange(lim)}
                            if 0 <= v < lim)
            for x in values:
                if mt >= 2 and x > 300:
                    continue
                np = bytes([(mt << 5) | ai]) + x.to_bytes(widths[ai], "big")
                item = np + body(mt, x)
                check(f"nonpref mt{mt} ai{ai} {x}",
                      drv.ask("d", item.hex()) == "error", item.hex())
                rejected += 1
                pref = ref_head(mt, x) + body(mt, x)
                want = ref_full(list(pref))
                check(f"pref mt{mt} {x}", want is not None
                      and drv.ask("d", pref.hex()) == want, pref.hex())
                accepted += 1

    # Every initial byte outside the slice, with the bytes that would
    # finish its item, at the top and nested: as an array's first or
    # later item, as a map's key or value, and two and three levels
    # down. Turned away, by the Lean code and by the oracle.
    def nestings(it):
        return [it, b"\x81" + it, b"\x82\x01" + it, b"\xa1" + it + b"\x00",
                b"\xa1\x01" + it, b"\x81\x81" + it, b"\xa1\x01\x81\xa1\x00" + it]
    for b in range(256):
        if not out_of_slice(b):
            continue
        for k, enc in enumerate(nestings(bytes([b]) + completion(b))):
            want = ref_full(list(enc))
            check(f"nested out {b:02x} {k}", want is None
                  and drv.ask("d", enc.hex()) == "error", enc.hex())
            rejected += 1

    # Bad UTF-8 text payloads: overlong, surrogate, stray continuation.
    bad = [bytes([0x61, 0xc0]), bytes([0x62, 0xc0, 0x80]),
           bytes([0x63, 0xed, 0xa0, 0x80]), bytes([0x62, 0xf4, 0x90]),
           bytes([0x61, 0x80]), bytes([0x62, 0xc2])]
    for p in bad:
        hdr = ref_head(3, len(p))
        check(f"utf8 reject {p.hex()}", drv.ask("d", (hdr + p).hex()) == "error")
        rejected += 1

    # Each row of the UTF-8 grammar: byte sequences built from the row's
    # ranges, with some bytes moved just outside their range, alone or
    # between other characters. The oracle is Python's strict UTF-8
    # decoder, which follows RFC 3629.
    for row_i, row in enumerate(UTF8_ROW_BYTES):
        for i in range(150):
            seq = []
            for lo, hi in row:
                seq.append(rng.choice([lo, hi, rng.randrange(lo, hi + 1),
                                       rng.randrange(lo, hi + 1),
                                       max(lo - 1, 0), min(hi + 1, 255),
                                       rng.randrange(256)]))
            if i % 3 == 1:
                seq = seq[:rng.randrange(len(seq) + 1)]
            if i % 3 == 2:
                seq = (list(chr(rand_scalar()).encode("utf-8")) + seq
                       + list(chr(rand_scalar()).encode("utf-8")))
            p = bytes(seq)
            enc = ref_head(3, len(p)) + p
            want = ref_full(list(enc))
            got = drv.ask("d", enc.hex())
            check(f"utf8 row {row_i} {i}", got == (want or "error"),
                  f"{enc.hex()}: want {want or 'error'}, got {got}")
            if want is None:
                rejected += 1
            else:
                accepted += 1

    # Leftover bytes after a complete item: turned away.
    check("trailing", drv.ask("d", "0102") == "error")
    check("empty", drv.ask("d", "") == "error")

    # The build is part of the check: lake build already ran if needed.
    total = checks
    ok = total - len(failures)
    RESULTS.write_text(f"""# Test results

Run by `tests/run_tests.py` against an independent Python implementation of
the slice written from RFC 8949, in the same file, and against the RFC 8949
Appendix A vectors.
Lean: Lean 4.35.0. Python: {sys.version.split()[0]}.

- Seed: {SEED}
- Byte inputs fed to the Lean codec: {inputs}
- Checks run: {total}
- Checks passed: {ok}
- Failures: {len(failures)}
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
""")
    print(f"{ok}/{total} checks passed; results written to {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
