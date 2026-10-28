#!/usr/bin/env python3
"""Differential tests for the Proven Commons CBOR codec.

Compares the Lean implementation against an independent Python
implementation of the slice (below), and against the RFC 8949
Appendix A vectors. Where the cbor2 library can be imported, it also
has cbor2 judge the tool's answers, counted apart (see
`cbor2_cross_check`). Run from anywhere:

    python3 tests/run_tests.py

It builds the Lean project if the executable is missing, runs all
cases, writes `tests/TEST-RESULTS.md`, and exits non-zero on failure.
"""

import itertools
import random
import subprocess
import sys
import textwrap
import threading
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
# Inputs fed to the Lean tool, by section of this script.
section = "start"
per_section = {}


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
        per_section[section] = per_section.get(section, 0) + 1
        self.proc.stdin.write(f"{op} {hexs}\n")
        self.proc.stdin.flush()
        return self.proc.stdout.readline().rstrip("\n")

    def ask_many(self, reqs):
        """Send many (op, hex) requests and read the answers in order.
        Used by the cbor2 cross-check, whose inputs are not counted in
        Inputs."""
        answers = []
        for i in range(0, len(reqs), 2000):
            chunk = reqs[i:i + 2000]

            def write():
                self.proc.stdin.write("".join(f"{op} {h}\n" for op, h in chunk))
                self.proc.stdin.flush()
            w = threading.Thread(target=write)
            w.start()
            answers += [self.proc.stdout.readline().rstrip("\n") for _ in chunk]
            w.join()
        return answers


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


# ---------- Cross-check against cbor2, when it can be imported ----------
# cbor2 (https://github.com/agronholm/cbor2) is a CBOR library for
# Python written apart from this project, and the oracle the plan in
# issue #1 named. CI installs nothing beyond Python's standard library,
# so the record's oracle is the reference codec above, and this
# cross-check runs only where cbor2 can be imported. Its inputs are
# counted apart, not in Inputs, so a run with or without cbor2 records
# the same Inputs. A disagreement is a failure.

CBOR2_PIN = "6.1.5"


class OutsideSlice(Exception):
    pass


def cbor2_text(o):
    """The tool's canonical text for a value cbor2 returned, or
    OutsideSlice when the value is of a kind the slice does not carry
    (a float, a tag cbor2 kept or turned into another type, undefined,
    another simple value, or an integer outside -2^64 to 2^64 - 1)."""
    from collections.abc import Mapping
    if o is False:
        return "false"
    if o is True:
        return "true"
    if o is None:
        return "null"
    if type(o) is int:
        if -2**64 <= o < 2**64:
            return str(o)
        raise OutsideSlice
    if type(o) is bytes:
        return "h'" + o.hex() + "'"
    if type(o) is str:
        return "t'" + o.encode("utf-8").hex() + "'"
    if type(o) in (list, tuple):
        return "[" + ",".join(cbor2_text(x) for x in o) + "]"
    if isinstance(o, Mapping):
        return "{" + ",".join(cbor2_text(k) + ":" + cbor2_text(v)
                              for k, v in o.items()) + "}"
    raise OutsideSlice


def cbor2_cross_check(drv):
    """Has cbor2 judge the tool's answers. Returns (None, reason) when
    cbor2 cannot be imported or lacks the option the judge needs, else
    (cbor2's version and the counts, None).

    cbor2 accepts an input when `cbor2.loads` reads it, every value in
    it is of a kind the slice carries, and `cbor2.dumps` writes the
    same bytes back. That last step turns away what cbor2 reads but the
    slice does not: arguments not in preferred form, indefinite
    lengths, tags that come back as plain values, and bytes after the
    item. The tool's `d` answer must be the canonical text of cbor2's
    value, or `error`; for each input cbor2 accepts, the `r` answer must
    be the input. An input is left out when cbor2 reads it, writes other
    bytes back, and a map in it holds two keys that are equal as Python
    values (the same key twice, or 1 and true, or 0 and false): cbor2
    keeps one pair of those, and the slice keeps every pair."""
    try:
        import cbor2
        from importlib.metadata import version
        ver = version("cbor2")
    except Exception:
        return None, "cbor2 could not be imported"
    try:
        cbor2.loads(b"\xa0", allow_duplicate_keys=False)
    except TypeError:
        return None, f"cbor2 {ver} has no allow_duplicate_keys option"

    def judge(bs):
        try:
            o = cbor2.loads(bs)
        except Exception:
            return "error"
        try:
            text = cbor2_text(o)
        except OutsideSlice:
            return "error"
        if cbor2.dumps(o) == bs:
            return text
        try:
            cbor2.loads(bs, allow_duplicate_keys=False)
        except Exception:
            return None  # keys equal as Python values: left out
        return "error"

    rng = random.Random(SEED)

    def rand_value(depth):
        kind = rng.randrange(9 if depth < 3 else 6)
        if kind == 0:
            return rng.choice([0, 1, 23, 24, 255, 256, 65535, 65536, 2**32 - 1,
                               2**32, 2**64 - 1, rng.randrange(2**64)])
        if kind == 1:
            return -1 - rng.choice([0, 23, 24, 255, 256, 65535, 2**32,
                                    2**64 - 1, rng.randrange(2**64)])
        if kind == 2:
            return bytes(rng.randrange(256)
                         for _ in range(rng.choice([0, 1, 5, 23, 24, 30, 256])))
        if kind == 3:
            chars = []
            for _ in range(rng.randrange(0, 12)):
                lo, hi = rng.choice(UTF8_ROW_SCALARS)
                chars.append(chr(rng.randrange(lo, hi + 1)))
            return "".join(chars)
        if kind == 4:
            return rng.choice([False, True, None])
        if kind == 5:
            return rng.randrange(-1000, 1000)
        if kind in (6, 7):
            return [rand_value(depth + 1)
                    for _ in range(rng.choice([0, 1, 2, 3, 24, 25]))]
        keys = [rng.choice([rng.randrange(2**32), rng.randrange(-30, 30),
                            str(rng.randrange(100)), bytes([rng.randrange(256)]),
                            False, True, None,
                            tuple(rng.randrange(5) for _ in range(rng.randrange(3)))])
                for _ in range(rng.randrange(0, 5))]
        return {k: rand_value(depth + 1) for k in keys}

    def mutate(e):
        m = bytearray(e)
        op = rng.randrange(5)
        if op == 0 and m:
            m[rng.randrange(len(m))] = rng.randrange(256)
        elif op == 1:
            m.insert(rng.randrange(len(m) + 1), rng.randrange(256))
        elif op == 2 and m:
            del m[rng.randrange(len(m))]
        elif op == 3 and m:
            m[rng.randrange(len(m))] ^= 1 << rng.randrange(8)
        elif m:
            del m[rng.randrange(len(m)):]
        return bytes(m)

    parts = []
    parts.append(("All inputs of 0, 1 or 2 bytes",
                  [bytes(t) for n in range(3)
                   for t in itertools.product(range(256), repeat=n)]))
    parts.append(("RFC 8949 Appendix A, all 81 rows",
                  [bytes.fromhex(h) for h, _ in RFC_OK]
                  + [bytes.fromhex(h) for h in RFC_A_OUT]))
    parts.append(("Random bytes, 3 to 9 long",
                  [bytes(rng.randrange(256) for _ in range(rng.randrange(3, 10)))
                   for _ in range(30000)]))
    parts.append(("Text items with 1 to 4 payload bytes, each random or "
                  "from 80 to bf",
                  [bytes([0x60 + k]) + bytes(rng.choice([rng.randrange(256),
                                                         rng.randrange(0x80, 0xC0)])
                                             for _ in range(k))
                   for k in (rng.randrange(1, 5) for _ in range(10000))]))
    written = []
    for _ in range(5000):
        e = cbor2.dumps(rand_value(0))
        written.append(e)
        written += [mutate(e) for _ in range(3)]
    parts.append(("Random values written by cbor2.dumps, and 3 mutations "
                  "of each", written))

    rows = []
    totals = {"requests": 0, "accepted": 0, "refused": 0, "left out": 0}
    failures_before = len(failures)
    for name, items in parts:
        reqs, wants, labels = [], [], []
        acc = ref = left = 0
        for bs in items:
            want = judge(bs)
            if want is None:
                left += 1
                continue
            reqs.append(("d", bs.hex()))
            wants.append(want)
            labels.append(f"cbor2 d {bs.hex()}")
            if want == "error":
                ref += 1
            else:
                acc += 1
                reqs.append(("r", bs.hex()))
                wants.append(bs.hex())
                labels.append(f"cbor2 r {bs.hex()}")
        got = drv.ask_many(reqs)
        for label, want, answer in zip(labels, wants, got):
            check(label, answer == want, f"cbor2 says {want}, the tool {answer}")
        rows.append((name, len(reqs), acc, ref, left))
        totals["requests"] += len(reqs)
        totals["accepted"] += acc
        totals["refused"] += ref
        totals["left out"] += left
    totals["disagreements"] = len(failures) - failures_before
    return {"version": ver, "rows": rows, "totals": totals}, None


def main():
    global accepted, rejected, section
    drv = LeanDriver()

    section = "RFC 8949 Appendix A rows and other out-of-slice shapes"
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

    section = "Generated well-formed items and their truncations"
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

    section = "Random bytes"
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

    section = "Non-preferred arguments and preferred controls"
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

    section = "Out-of-slice initial bytes, at the top and nested"
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

    section = "Malformed UTF-8 examples"
    # Bad UTF-8 text payloads: overlong, surrogate, stray continuation.
    bad = [bytes([0x61, 0xc0]), bytes([0x62, 0xc0, 0x80]),
           bytes([0x63, 0xed, 0xa0, 0x80]), bytes([0x62, 0xf4, 0x90]),
           bytes([0x61, 0x80]), bytes([0x62, 0xc2])]
    for p in bad:
        hdr = ref_head(3, len(p))
        check(f"utf8 reject {p.hex()}", drv.ask("d", (hdr + p).hex()) == "error")
        rejected += 1

    section = "UTF-8 grammar rows"
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

    section = "Trailing bytes and empty input"
    # Leftover bytes after a complete item: turned away.
    check("trailing", drv.ask("d", "0102") == "error")
    check("empty", drv.ask("d", "") == "error")

    cross, why_not = cbor2_cross_check(drv)
    if cross is None:
        oracle_note = f"; the cbor2 cross-check did not run ({why_not})"
        cross_text = textwrap.fill(
            f"In this run {why_not}, so the cross-check did not run. To run "
            f"it, install cbor2 {CBOR2_PIN}, the version the committed "
            "record used, where the script can import it. For example:", 72)
        cross_text += f"""

    python3 -m venv /tmp/cbor2-venv
    /tmp/cbor2-venv/bin/pip install cbor2=={CBOR2_PIN}
    /tmp/cbor2-venv/bin/python tests/run_tests.py
"""
    else:
        oracle_note = f"; cross-checked against cbor2 {cross['version']}, counted apart"
        t = cross["totals"]
        part_lines = "\n".join(
            f"  - {name}: {n} requests; cbor2 accepted {acc} inputs, "
            f"refused {ref}" + (f", left out {left}" if left else "")
            for name, n, acc, ref, left in cross["rows"])
        version_note = ("" if cross["version"] == CBOR2_PIN else
                        f" This is not cbor2 {CBOR2_PIN}, the version the "
                        "committed record used.")
        cross_text = textwrap.fill(
            f"In this run cbor2 {cross['version']} could be imported, and the "
            f"cross-check ran.{version_note} The requests by part, where "
            "each input cbor2 accepts is asked twice, `d` and `r`:", 72)
        cross_text += "\n\n" + part_lines + "\n\n" + textwrap.fill(
            f"In all: {t['requests']} requests, from {t['accepted']} inputs "
            f"cbor2 accepted and {t['refused']} it refused, with "
            f"{t['disagreements']} disagreements. {t['left out']} inputs were "
            "left out because a map in them holds two keys that are equal "
            "as Python values.", 72) + "\n"

    # The build is part of the check: lake build already ran if needed.
    total = checks
    ok = total - len(failures)
    breakdown = "\n".join(f"  - {name}: {n}" for name, n in per_section.items())
    failed = "".join(f"\n  - {f}" for f in failures)
    RESULTS.write_text(f"""# Test results

Written by `python3 tests/run_tests.py`, which feeds each input to the
command-line tool built from the proved code (`.lake/build/bin/cbor`)
and compares its answer with the oracle's.

- Oracle: reference codec in `tests/run_tests.py`, on Python {sys.version.split()[0]}{oracle_note}
- Seed: {SEED}
- Inputs: {inputs}
- Failures: {len(failures)}{failed}

The oracle is a decoder and encoder of the slice written from RFC 8949
apart from the Lean code, in the test script itself. It checks text
payloads with Python's strict UTF-8 decoder, which follows RFC 3629.

Inputs by section:

{breakdown}

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

{cross_text}""")
    print(f"{ok}/{total} checks passed; results written to {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
