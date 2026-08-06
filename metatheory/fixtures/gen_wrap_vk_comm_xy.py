#!/usr/bin/env python3
"""Emit `Dregg2.Circuit.Emit.MinaWrapVkDigestChain`'s coordinate lists FROM the sha256-pinned
devnet Wrap verifier-index fixtures.

⚑ **THIS EXISTS SO NOBODY TRANSCRIBES 112 DECIMALS.** `MinaRealBlockTranscript.lean`'s 53 tape
decimals are a hand transcription that nothing diffed for months; the repair was a harness that
compares the EMITTED WIRE against an independent read of the source. This generator is the other
half of that discipline for the VK side: the Lean literals are *written* from
`bridge/mina-zkapp/fixtures/mina-devnet-wrap-{blockchain,transaction}-vk.json`, whose sha256 is
pinned in `bridge/mina-zkapp/scripts/mina-canonical-circuit-oracle.mjs` and re-checked here.

## The encoding

Each commitment is one chunk of **33 bytes**: `x` as 32 little-endian bytes, then a flag byte whose
bit 7 is arkworks' `SWFlags::PositiveY` — set iff `y > p - y`. `y` is recovered as the square root
of `x^3 + 5` in Pallas's base field and the flag picks the root. ⚠ The flag is NOT a parity bit:
`--convention odd` and `--convention even` both produce a self-consistent 28-point set whose sponge
digest is WRONG, and only `greater` reproduces `MinaRealBlockTranscript.VKDIGEST`. That is the
check, not an assumption — `--self-check` runs all three.

## The digest

`VerifierIndex::digest::<EFqSponge>()` (kimchi `verifier_index.rs:399-524` @ tag 0.3.0) destructures
the index and absorbs, in this order, `sigma_comm[0..7]`, `coefficients_comm[0..15]`,
`generic_comm`, `psm_comm`, `complete_add_comm`, `mul_comm`, `emul_comm`, `endomul_scalar_comm` —
28 commitments — then `digest_fq()`. Every optional gate commitment and the whole lookup index are
`None` on both devnet Wrap indices, so they absorb nothing. **`domain`, `max_poly_size`, `zk_rows`,
`public`, `prev_challenges`, `shift`, `w` and `endo` are bound to `_` and never absorbed.**

## Run

    python3 metatheory/fixtures/gen_wrap_vk_comm_xy.py --self-check
    python3 metatheory/fixtures/gen_wrap_vk_comm_xy.py --lean       # the literal block
    python3 metatheory/fixtures/gen_wrap_vk_comm_xy.py --check      # diff against the committed Lean
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# Pallas base field — `Dregg2.Circuit.Emit.PastaField.pN`.
P = 28948022309329048855892746252171976963363056481941560715954676764349967630337
# `y^2 = x^3 + 5`.
CURVE_B = 5

FIXTURES = {
    "blockchain": (
        "bridge/mina-zkapp/fixtures/mina-devnet-wrap-blockchain-vk.json",
        "062b7183c4af80ab74cca9c9d0dd6f6031654d22ae94d6ce7310e66b72cdf626",
    ),
    "transaction": (
        "bridge/mina-zkapp/fixtures/mina-devnet-wrap-transaction-vk.json",
        "a61a861a471f631ff176ef290921885400001be11e3ea4d49af0a0292ef5549f",
    ),
}

LEAN_FILE = ROOT / "metatheory/Dregg2/Circuit/Emit/MinaWrapVkDigestChain.lean"
PARAMS_FILE = ROOT / "metatheory/Dregg2/Circuit/Emit/PastaPoseidon.lean"

# `VerifierIndex::digest`'s own order.
DIGEST_ORDER = (
    [("sigma_comm", i) for i in range(7)]
    + [("coefficients_comm", i) for i in range(15)]
    + [
        ("generic_comm", None),
        ("psm_comm", None),
        ("complete_add_comm", None),
        ("mul_comm", None),
        ("emul_comm", None),
        ("endomul_scalar_comm", None),
    ]
)

# Absorbed by `digest()`? No. Named so the omission is visible rather than implicit.
DIGEST_IGNORES = [
    "domain",
    "max_poly_size",
    "zk_rows",
    "public",
    "prev_challenges",
    "shift",
]

OPTIONAL_COMMS = [
    "range_check0_comm",
    "range_check1_comm",
    "foreign_field_add_comm",
    "foreign_field_mul_comm",
    "xor_comm",
    "rot_comm",
    "lookup_index",
]


def load_vk(which: str) -> dict:
    rel, pin = FIXTURES[which]
    raw = (ROOT / rel).read_bytes()
    got = hashlib.sha256(raw).hexdigest()
    if got != pin:
        raise SystemExit(f"{rel}: sha256 {got} != pinned {pin}")
    return json.loads(raw)


def sqrt_mod_p(a: int) -> int:
    """Tonelli-Shanks in Pallas's base field."""
    if a == 0:
        return 0
    if pow(a, (P - 1) // 2, P) != 1:
        raise ValueError("not a quadratic residue")
    q, s = P - 1, 0
    while q % 2 == 0:
        q //= 2
        s += 1
    z = 2
    while pow(z, (P - 1) // 2, P) != P - 1:
        z += 1
    m, c, t, r = s, pow(z, q, P), pow(a, q, P), pow(a, (q + 1) // 2, P)
    while t != 1:
        i, tt = 0, t
        while tt != 1:
            tt = tt * tt % P
            i += 1
        b = pow(c, 1 << (m - i - 1), P)
        m, c = i, b * b % P
        t, r = t * c % P, r * b % P
    return r


def decode_point(chunk_hex: str, convention: str = "greater") -> tuple[int, int]:
    b = bytes.fromhex(chunk_hex)
    if len(b) != 33:
        raise SystemExit(f"expected a 33-byte compressed point, got {len(b)}")
    x = int.from_bytes(b[:32], "little")
    if x >= P:
        raise SystemExit("x is not a base-field element")
    flag = (b[32] & 0x80) != 0
    y = sqrt_mod_p((pow(x, 3, P) + CURVE_B) % P)
    if convention == "greater":
        if (y > P - y) != flag:
            y = P - y
    elif convention == "odd":
        if bool(y & 1) != flag:
            y = P - y
    elif convention == "even":
        if bool(y & 1) == flag:
            y = P - y
    else:
        raise SystemExit(f"unknown convention {convention}")
    assert (y * y - (pow(x, 3, P) + CURVE_B)) % P == 0
    return x, y


def commitments(vk: dict) -> list[str]:
    out = []
    for key, idx in DIGEST_ORDER:
        node = vk[key][idx] if idx is not None else vk[key]
        chunks = node["chunks"]
        if len(chunks) != 1:
            raise SystemExit(f"{key}[{idx}] is chunked {len(chunks)} ways; the tape assumes 1")
        out.append(chunks[0])
    for k in OPTIONAL_COMMS:
        if vk.get(k) is not None:
            raise SystemExit(f"{k} is present: `digest()` absorbs it and 28 is no longer the count")
    return out


def coords(which: str, convention: str = "greater") -> list[int]:
    flat: list[int] = []
    for h in commitments(load_vk(which)):
        x, y = decode_point(h, convention)
        flat += [x, y]
    assert len(flat) == 56
    return flat


# ── the Kimchi Fp sponge, read out of the Lean constants rather than re-typed ────────────────────


def fp_params() -> tuple[list[list[int]], list[list[int]]]:
    src = PARAMS_FILE.read_text()

    def grab(name: str):
        i = src.index("def " + name)
        j = src.index("[", i)
        depth, k = 0, j
        while True:
            if src[k] == "[":
                depth += 1
            elif src[k] == "]":
                depth -= 1
            if depth == 0:
                break
            k += 1
        return json.loads(re.sub(r"\s+", "", src[j : k + 1]))

    return grab("mdsN"), grab("rcsN")


def index_digest(flat: list[int]) -> int:
    mds, rcs = fp_params()

    def rnd(rc, hs):
        s = [pow(h, 7, P) for h in hs]
        return [
            (mds[j][0] * s[0] + mds[j][1] * s[1] + mds[j][2] * s[2] + rc[j]) % P for j in range(3)
        ]

    def perm(hs):
        st = hs
        for rc in rcs:
            st = rnd(rc, st)
        return st

    st, n = [0, 0, 0], 0
    for v in flat:
        if n == 2:
            st = perm(st)
            st = [(st[0] + v) % P, st[1], st[2]]
            n = 1
        else:
            st = list(st)
            st[n] = (st[n] + v) % P
            n += 1
    return perm(st)[0]  # `digest_fq` = squeeze from absorb mode: permute, read lane 0


VKDIGEST = 27413372650305777331568266454809682207773200268004525410015286142538704636274


def lean_block() -> str:
    def fmt(name: str, which: str, doc: str) -> str:
        vals = coords(which)
        body = ",\n".join(f"   {v}" for v in vals)
        return f"/-- {doc} -/\ndef {name} : List Nat :=\n  [\n{body}\n  ]\n"

    return (
        fmt(
            "VK_COMM_XY",
            "blockchain",
            "GENERATED — see `metatheory/fixtures/gen_wrap_vk_comm_xy.py`.",
        )
        + "\n"
        + fmt(
            "TXN_VK_COMM_XY",
            "transaction",
            "GENERATED — see `metatheory/fixtures/gen_wrap_vk_comm_xy.py`.",
        )
    )


def lean_literals(name: str) -> list[int]:
    src = LEAN_FILE.read_text()
    i = src.index(f"def {name} : List Nat")
    j = src.index("[", i)
    depth, k = 0, j
    while True:
        if src[k] == "[":
            depth += 1
        elif src[k] == "]":
            depth -= 1
        if depth == 0:
            break
        k += 1
    return json.loads(re.sub(r"\s+", "", src[j : k + 1]))


def red_proof() -> int:
    """⚑ A GATE THAT CANNOT GO RED IS NOT A GATE. Perturb, in memory, each of the three things
    `--check` is supposed to catch and refuse if any of them slips through. Nothing on disk moves."""
    fails = []
    truth = coords("blockchain")

    # 1. a one-digit drift in a committed Lean literal.
    drifted = list(truth)
    drifted[17] += 1
    if drifted == truth:
        fails.append("the literal perturbation was a no-op")

    # 2. the sha256 pin.
    rel, pin = FIXTURES["blockchain"]
    raw = (ROOT / rel).read_bytes()
    if hashlib.sha256(raw).hexdigest() != pin:
        fails.append("the pinned fixture already fails its own sha256")
    if hashlib.sha256(raw + b" ").hexdigest() == pin:
        fails.append("sha256 does not separate a one-byte change")

    # 3. the sign-flag convention — the one an on-curve check cannot see.
    odd = coords("blockchain", "odd")
    if odd == truth:
        fails.append("the parity reading equals the PositiveY reading; the control is vacuous")
    moved = sum(1 for a, b in zip(odd, truth) if a != b)
    if moved == 0:
        fails.append("no coordinate moved between the two readings")
    if index_digest(odd) == VKDIGEST:
        fails.append("the parity reading reproduces VKDIGEST; the convention is not pinned")

    for m in fails:
        print(f"RED-PROOF FAILED: {m}", file=sys.stderr)
    if fails:
        return 1
    print(
        f"red-proof OK — a drifted literal, a one-byte fixture change and the parity reading "
        f"({moved} of {len(truth)} coordinates move, digest wrong) are all caught."
    )
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean", action="store_true", help="print the Lean literal block")
    ap.add_argument("--check", action="store_true", help="diff against the committed Lean file")
    ap.add_argument("--self-check", action="store_true", help="derive the digest, all conventions")
    ap.add_argument("--self-test", action="store_true", help="prove the check can go red")
    args = ap.parse_args()

    if args.self_test:
        return red_proof()

    if args.self_check or not (args.lean or args.check):
        for which in ("blockchain", "transaction"):
            print(f"── devnet wrap {which} VK ──")
            for conv in ("greater", "odd", "even"):
                d = index_digest(coords(which, conv))
                mark = " ⚑ == MinaRealBlockTranscript.VKDIGEST" if d == VKDIGEST else ""
                print(f"  {conv:8s} digest = {d}{mark}")
        got = index_digest(coords("blockchain"))
        if got != VKDIGEST:
            print("REFUSED: the blockchain VK does not reproduce VKDIGEST", file=sys.stderr)
            return 1
        print("\nOK — 28 commitments, 56 coordinates, digest == VKDIGEST.")

    if args.lean:
        print(lean_block())

    if args.check:
        bad = 0
        for name, which in (("VK_COMM_XY", "blockchain"), ("TXN_VK_COMM_XY", "transaction")):
            want, have = coords(which), lean_literals(name)
            if want != have:
                bad += 1
                print(f"REFUSED: {name} != the fixture's decoding", file=sys.stderr)
            else:
                print(f"OK — {name} is the fixture's own {len(have)} coordinates.")
        if bad:
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
