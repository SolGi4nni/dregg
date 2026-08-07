#!/usr/bin/env python3
"""check-signing-message-fidelity.py — the Lean signing-message preimages vs the RUST ones.

═══ WHY THIS EXISTS — a pin against its own definition is decoration ═══════════════
`metatheory/Dregg2/Exec/SigningMessage.lean` models, byte-for-byte, the six preimages
dregg1 actually signs. Its own docstring states the stakes: "If the preimage is
reconstructed even one byte differently from what dregg1 actually signs, the portal
verifies the wrong message."

Its fidelity check was:

    #guard (decide (sepFull = ascii "dregg-action-sig-v2:"))

— a Lean constant compared against a Lean restatement of that same constant. ONE SOURCE.
It cannot go red when Rust moves, and Rust moved: `TurnExecutor::compute_signing_message`
(`turn/src/executor/authorize.rs:2293`) bumped to `b"dregg-action-sig-v3:"` and inserted
`turn_nonce.to_le_bytes()` after `federation_id` — the Full-commitment replay closure. The
Lean model sat on v2, WITHOUT the nonce, and every guard in the file stayed green.

⚑ The missing field was not cosmetic. It is the field that makes a Full-commitment
signature single-use. Measured 2026-08-02; five of six builders were faithful, the sixth
was stale by exactly the security fix, for as long as nobody read both files in one pass.

═══ WHAT THIS GATE CHECKS ═════════════════════════════════════════════════════════
TWO INDEPENDENT SOURCES, compared:

  (1) DOMAIN SEPARATORS. The `b"..."` literal each Rust builder feeds first, against the
      `List UInt8` literal the matching Lean `sep*` def holds. Decoded on both sides, so a
      one-byte drift ('2' vs '3') reds.

  (2) FIELD ORDER of the Full-commitment preimage — the one that drifted, and the class
      the separator check alone would still have missed. The ordered `hasher.update(...)`
      arguments of `compute_signing_message` are normalized to field tokens and compared
      against the `++`-chain of Lean's `sigMsgFull`. An added, dropped, or reordered field
      reds. An UNRECOGNIZED token on either side ALSO reds (fail-closed: a new field that
      this gate does not know how to name is exactly the thing it must not wave through).

Run `--self-test` to see it go red: it re-runs the comparison against in-memory MUTATED
copies of the Lean source (v3→v2 separator; `turn_nonce` deleted) and REFUSES if either
mutation still passes. Nothing on disk is touched — the mutation lives in a string.

Exit 0 = the two sources agree. Exit 1 = they do not, or a source could not be parsed.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

LEAN_SRC = REPO / "metatheory/Dregg2/Exec/SigningMessage.lean"

# ── (1) domain separators: Lean `sep*` def  ↔  the first `b"..."` in a Rust builder ──────
# (lean_def, rust_relpath, rust_fn) — the Rust separator is the FIRST byte-string literal
# appearing in that function's body.
SEPARATORS = [
    ("sepFull", "turn/src/executor/authorize.rs", "compute_signing_message"),
    ("sepPartial", "turn/src/executor/authorize.rs", "compute_partial_signing_message"),
    ("sepCustom", "turn/src/executor/authorize.rs", "compute_custom_signing_message"),
    ("sepBearer", "turn/src/executor/authorize.rs", "compute_bearer_delegation_message"),
    ("sepStealth", "turn/src/action.rs", "stealth_signing_message"),
    ("sepHandoff", "captp/src/handoff.rs", "signing_message"),
]

# `sepFullV2` is deliberately NOT in the table: it is the SUPERSEDED literal, retained in
# Lean only so the replay theorem has an object. It must match NOTHING live — asserted
# below by `check_superseded`.
SUPERSEDED = {"sepFullV2": b"dregg-action-sig-v2:"}

# ── (2) Full-commitment field order ──────────────────────────────────────────────────────
# Rust `hasher.update(<arg>)` argument  →  canonical field token.
RUST_FIELD_TOKENS = [
    (r'^b"dregg-action-sig-v3:"$', "SEPARATOR"),
    (r"^federation_id$", "FEDERATION_ID"),
    (r"^&turn_nonce\.to_le_bytes\(\)$", "TURN_NONCE"),
    (r"^action\.target\.as_bytes\(\)$", "TARGET"),
    (r"^&action\.method$", "METHOD"),
    (r"^arg$", "ARGS"),
    (r"^&effect\.hash\(\)$", "EFFECT_HASHES"),
    (r"^&\[action\.may_delegate as u8\]$", "MAY_DELEGATE"),
    (r"^&\[action\.commitment_mode as u8\]$", "COMMITMENT_MODE"),
    # the `balance_change` match arms — a `Some` discriminant, its delta, and a `None` byte.
    (r"^&\[1u8\]$", "BALANCE_CHANGE"),
    (r"^&delta\.to_le_bytes\(\)$", "BALANCE_CHANGE"),
    (r"^&\[0u8\]$", "BALANCE_CHANGE"),
    (r"^&preconds_bytes$", "PRECONDITIONS"),
]

# Lean `++` chain summand  →  the same canonical field token.
LEAN_FIELD_TOKENS = [
    (r"^sepFull$", "SEPARATOR"),
    (r"^federationId$", "FEDERATION_ID"),
    (r"^u64le turnNonce$", "TURN_NONCE"),
    (r"^a\.target$", "TARGET"),
    (r"^a\.method$", "METHOD"),
    (r"^a\.args\.flatten$", "ARGS"),
    (r"^a\.effectHashes\.flatten$", "EFFECT_HASHES"),
    (r"^\[a\.mayDelegate\]$", "MAY_DELEGATE"),
    (r"^\[a\.commitmentMode\]$", "COMMITMENT_MODE"),
    (r"^balByte a\.balanceChange$", "BALANCE_CHANGE"),
    (r"^a\.precondBytes$", "PRECONDITIONS"),
]


class Refusal(Exception):
    """A source could not be parsed. Neither a red nor a green may be read from a Refusal."""


def fail(msg: str) -> None:
    print(f"  RED  {msg}")


# ═══════════════════════════════════════════════════════════════════════════════════════
# source extraction
# ═══════════════════════════════════════════════════════════════════════════════════════


def rust_fn_body(text: str, fn: str, path: str) -> str:
    """The brace-balanced body of `fn <fn>(...)` — the first definition of that name."""
    m = re.search(rf"\bfn\s+{re.escape(fn)}\s*\(", text)
    if m is None:
        raise Refusal(f"{path}: no `fn {fn}(` found")
    brace = text.find("{", m.end())
    if brace < 0:
        raise Refusal(f"{path}: `fn {fn}` has no body")
    depth, i = 0, brace
    while i < len(text):
        if text[i] == "{":
            depth += 1
        elif text[i] == "}":
            depth -= 1
            if depth == 0:
                return text[brace + 1 : i]
        i += 1
    raise Refusal(f"{path}: `fn {fn}` body is not brace-balanced")


def rust_first_byte_string(body: str, fn: str) -> bytes:
    """The first `b"..."` literal in a function body — the domain separator."""
    m = re.search(r'b"((?:[^"\\]|\\.)*)"', body)
    if m is None:
        raise Refusal(f"`fn {fn}`: no `b\"...\"` domain-separator literal in the body")
    return m.group(1).encode("utf-8").decode("unicode_escape").encode("latin-1")


def rust_update_args(body: str) -> list[str]:
    """The ordered arguments of every `hasher.update(...)` / `msg.extend_from_slice(...)`."""
    out: list[str] = []
    for m in re.finditer(r"(?:hasher\.update|msg\.extend_from_slice)\s*\(", body):
        depth, i, start = 1, m.end(), m.end()
        while i < len(body) and depth:
            if body[i] == "(":
                depth += 1
            elif body[i] == ")":
                depth -= 1
            i += 1
        out.append(" ".join(body[start : i - 1].split()))
    return out


def lean_sep_bytes(text: str, name: str) -> bytes:
    """The `List UInt8` literal of a Lean `def <name> : ByteString := [..]`."""
    m = re.search(rf"^def\s+{re.escape(name)}\s*:\s*ByteString\s*:=\s*\n?\s*\[([^\]]*)\]", text, re.M)
    if m is None:
        raise Refusal(f"{LEAN_SRC.name}: no `def {name} : ByteString := [..]`")
    try:
        return bytes(int(t) for t in m.group(1).replace("\n", "").split(",") if t.strip())
    except ValueError as e:
        raise Refusal(f"{LEAN_SRC.name}: `{name}` is not a plain byte list ({e})") from e


def lean_sig_msg_full_summands(text: str) -> list[str]:
    """The `++`-chain summands of Lean's `sigMsgFull` body, in order."""
    m = re.search(r"^def\s+sigMsgFull\s*\(.*?\)\s*:\s*ByteString\s*:=\s*\n(.*?)(?=\n/-|\n@\[|\ndef\s|\ntheorem\s)", text, re.M | re.S)
    if m is None:
        raise Refusal(f"{LEAN_SRC.name}: no parseable `def sigMsgFull` body")
    body = m.group(1)
    parts = [p.strip() for p in re.split(r"\+\+", body)]
    return [" ".join(p.split()) for p in parts if p.strip()]


def normalize(items: list[str], table: list[tuple[str, str]], side: str) -> list[str]:
    """Map raw summands/arguments to canonical field tokens; collapse runs; fail-closed."""
    toks: list[str] = []
    for raw in items:
        for pat, tok in table:
            if re.match(pat, raw):
                if not toks or toks[-1] != tok:
                    toks.append(tok)
                break
        else:
            raise Refusal(f"{side}: unrecognized preimage field {raw!r} — this gate refuses "
                          f"to wave through a field it cannot name")
    return toks


# ═══════════════════════════════════════════════════════════════════════════════════════
# the checks
# ═══════════════════════════════════════════════════════════════════════════════════════


def check_separators(lean_text: str) -> int:
    bad = 0
    print("── domain separators (Lean literal vs the Rust builder's own) ──")
    for lean_def, relpath, fn in SEPARATORS:
        rust_path = REPO / relpath
        if not rust_path.is_file():
            raise Refusal(f"missing Rust source {relpath}")
        body = rust_fn_body(rust_path.read_text(encoding="utf-8"), fn, relpath)
        rust_sep = rust_first_byte_string(body, fn)
        lean_sep = lean_sep_bytes(lean_text, lean_def)
        if rust_sep == lean_sep:
            print(f"  ok   {lean_def:<12} = {rust_sep.decode('latin-1')!r}  ({relpath}::{fn})")
        else:
            bad += 1
            fail(f"{lean_def}: Lean has {lean_sep.decode('latin-1')!r} but "
                 f"{relpath}::{fn} signs {rust_sep.decode('latin-1')!r}")
    return bad


def check_superseded(lean_text: str) -> int:
    bad = 0
    print("── superseded literals (must match nothing live) ──")
    live = set()
    for _, relpath, fn in SEPARATORS:
        body = rust_fn_body((REPO / relpath).read_text(encoding="utf-8"), fn, relpath)
        live.add(rust_first_byte_string(body, fn))
    for name, expected in SUPERSEDED.items():
        try:
            got = lean_sep_bytes(lean_text, name)
        except Refusal:
            # Absence is fine — a retired literal nobody kept a witness for. It is only its
            # PRESENCE that carries an obligation (retired, and not live in Rust).
            print(f"  ok   {name:<12} absent (no retired-literal witness retained)")
            continue
        if got != expected:
            bad += 1
            fail(f"{name}: expected the retired {expected.decode('latin-1')!r}, found "
                 f"{got.decode('latin-1')!r} — a superseded literal was edited, not retired")
        elif got in live:
            bad += 1
            fail(f"{name}: the retired {got.decode('latin-1')!r} is LIVE in Rust again")
        else:
            print(f"  ok   {name:<12} = {got.decode('latin-1')!r} (retired, not live)")
    return bad


def check_full_field_order(lean_text: str) -> int:
    print("── Full-commitment field order (the class that actually drifted) ──")
    relpath = "turn/src/executor/authorize.rs"
    body = rust_fn_body((REPO / relpath).read_text(encoding="utf-8"), "compute_signing_message", relpath)
    rust_toks = normalize(rust_update_args(body), RUST_FIELD_TOKENS, f"{relpath}::compute_signing_message")
    lean_toks = normalize(lean_sig_msg_full_summands(lean_text), LEAN_FIELD_TOKENS, f"{LEAN_SRC.name}::sigMsgFull")
    if rust_toks == lean_toks:
        print(f"  ok   {len(rust_toks)} fields, same order: {' · '.join(rust_toks)}")
        return 0
    fail("`sigMsgFull` does not reproduce `compute_signing_message`'s field order")
    print(f"       rust: {' · '.join(rust_toks)}")
    print(f"       lean: {' · '.join(lean_toks)}")
    for miss in [t for t in rust_toks if t not in lean_toks]:
        print(f"       ⚑ Lean OMITS {miss} — a field the signer's message binds and the model does not")
    for extra in [t for t in lean_toks if t not in rust_toks]:
        print(f"       ⚑ Lean ADDS {extra} — a field Rust does not sign")
    return 1


def run(lean_text: str, quiet: bool = False) -> int:
    """Total red count over the three checks. Raises `Refusal` if a source is unparseable."""
    import contextlib, io

    sink = io.StringIO()
    with contextlib.redirect_stdout(sink) if quiet else contextlib.nullcontext():
        bad = check_separators(lean_text) + check_superseded(lean_text) + check_full_field_order(lean_text)
    return bad


# ═══════════════════════════════════════════════════════════════════════════════════════
# self-test — prove the gate can go red, on a COPY (nothing on disk is mutated)
# ═══════════════════════════════════════════════════════════════════════════════════════

MUTATIONS = [
    (
        "separator rolled back to v2 (the drift this gate was written for)",
        lambda t: t.replace(
            "[100,114,101,103,103,45,97,99,116,105,111,110,45,115,105,103,45,118,51,58]",
            "[100,114,101,103,103,45,97,99,116,105,111,110,45,115,105,103,45,118,50,58]",
            1,
        ),
    ),
    (
        "`turn_nonce` dropped from sigMsgFull (the replay closure deleted)",
        lambda t: t.replace("    ++ u64le turnNonce\n", "", 1),
    ),
    (
        "target and method transposed in sigMsgFull (a reorder, same fields)",
        lambda t: t.replace("    ++ a.target\n    ++ a.method\n", "    ++ a.method\n    ++ a.target\n", 1),
    ),
]


def self_test(lean_text: str) -> int:
    print("== self-test: each mutation must make this gate RED ==")
    bad = 0
    for label, mutate in MUTATIONS:
        mutated = mutate(lean_text)
        if mutated == lean_text:
            bad += 1
            fail(f"mutation did not apply ({label}) — the self-test is not exercising anything")
            continue
        try:
            reds = run(mutated, quiet=True)
        except Refusal as e:
            print(f"  ok   RED (refused to parse) on: {label}\n         {e}")
            continue
        if reds:
            print(f"  ok   RED ({reds}) on: {label}")
        else:
            bad += 1
            fail(f"gate stayed GREEN on: {label} — it cannot see this drift class")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--self-test", action="store_true", help="prove the gate reds (mutates a COPY in memory)")
    args = ap.parse_args()

    if not LEAN_SRC.is_file():
        print(f"REFUSED: missing {LEAN_SRC}")
        return 1
    lean_text = LEAN_SRC.read_text(encoding="utf-8")

    try:
        if args.self_test:
            bad = self_test(lean_text)
            print("\nself-test PASS: the gate reds on every drift class it claims to cover"
                  if not bad else f"\nself-test FAIL: {bad} mutation(s) left it green")
            return 1 if bad else 0

        bad = run(lean_text)
    except Refusal as e:
        print(f"REFUSED: {e}")
        print("Neither a red nor a green may be read from a REFUSED run.")
        return 1

    if bad:
        print(f"\nFAIL: {bad} disagreement(s) between the Lean signing-message model and Rust.")
        print("The Lean model is the one that moves: Rust is what is actually signed.")
        return 1
    print("\nPASS: every Lean preimage literal and the Full field order match the Rust source.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
