#!/usr/bin/env python3
"""check-mina-multiblock-conformance — the standing instrument that keeps the Mina welds
answerable to the PROTOCOL rather than to one block. Green or bust.

## The wound this closes

Every real-data conformance claim in `metatheory/Dregg2/Bridge/MinaWrap*Weld.lean`,
`StepMainFtEval0RealBlock.lean` and `MinaStepPrevCommitments.lean` was stated over exactly ONE
devnet block, 539508. Anything accidentally fitted to that block's particulars could never show.
`Dregg2/Bridge/MinaMultiBlockConformance.lean` re-runs the same weld functions on other blocks —
but a GENERATED file is only as good as the guarantee that it still corresponds to the fixtures it
claims to be about. That guarantee is this script.

## What it checks, all of it green-or-bust, none of it needing cargo or lean

  1. **COVERAGE RATCHET.** Every fixture on disk is DECLARED here with the axis it exists to cover;
     every declared fixture is on disk and is git-TRACKED. Floors on the number of fixtures, the
     number of networks, and the presence of the degenerate cases. A fixture set that quietly
     narrows back toward one block is RED — which is the whole failure mode.
  2. **THE INPUTS ARE THE FIXTURES' OWN BYTES.** Every Step-side input in the generated Lean is
     re-derived here by `walk.py` — the independent binprot re-walk — from that block's committed
     base64 proof, and must match exactly. A hand-edited Lean fixture is RED. So is a fixture file
     swapped underneath it.
  3. **THE BINPROT LAYOUT STILL FITS.** Every fixture decodes with ZERO trailing bytes, and none
     trips the walk's refusals (a joint combiner, a feature flag, a lookup evaluation) — a block
     that does is a block exercising a shape this tree does not implement, and must be loud.
  4. **THE TARGETS AGREE WITH THEMSELVES ACROSS TWO OPENMINA PATHS.** For every block the full
     verifying gate accepted, the six `expand_deferred` targets must equal public-input slots
     0-4 and 9 of the SAME record — `expand_deferred` and `PreparedStatement::to_public_input`
     are different functions, and the Lean file carries both answers.

⚠ WHAT IT DOES NOT CHECK: that the Lean weld functions reproduce the targets. That is the
`#guard`s in the generated module itself, run by `lake build` (the module is rooted in
`Dregg2.MinaBridgeGuards`, a `defaultTargets` library). This script keeps the module HONEST; the
build keeps it TRUE.

## Usage

    scripts/check-mina-multiblock-conformance.py             # the gate
    scripts/check-mina-multiblock-conformance.py --self-test # prove the gate can go RED
"""
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = "metatheory/Dregg2/Bridge/MinaMultiBlockConformance.lean"
FIXDIR = "metatheory/fixtures/mina-blocks"
# ⚑ Block 539508 is the CONTROL and lives at its historical path — every single-block weld in the
# tree names that path, so it is not moved by this lane.
CONTROL = "metatheory/fixtures/pickles-extractors/mina_devnet_block.json"

# ── THE COVERAGE RATCHET ──────────────────────────────────────────────────────────────────
# height | network | the AXIS this fixture exists to cover.
# Raise the floors when the set grows. A fixture that disappears is RED; a fixture that appears
# undeclared is RED. Both directions, because the failure mode is the set narrowing back to one.
DECLARED = {
    539508: ("devnet", "the CONTROL — the block every single-block weld in the tree is pinned to"),
    540890: ("devnet", "an EMPTY block: 0 user commands, 0 zkApp commands, 0 snark jobs"),
    540906: ("devnet", "zkApp-only: 3 zkApp commands, 0 user commands, 0 snark jobs"),
    540922: ("devnet", "the BUSIEST in the window: 4 user + 3 zkApp commands, 35 snark jobs"),
    540929: ("devnet", "the chain tip at fetch time"),
    296372: ("devnet", "the HARDFORK GENESIS — a dummy proof, 32 binprot bytes shorter, "
                       "REJECTED by kimchi::verifier::verify (Step side only)"),
    541858: ("mainnet", "a DIFFERENT NETWORK with a different verification key and genesis "
                        "(Step side only — openmina cannot load its own mainnet VK)"),
}
MIN_FIXTURES = 7
MIN_NETWORKS = 2
MIN_WRAP_BLOCKS = 5

CHAIN_IDS = {
    "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6": "devnet",
    "5f704cc0c82e0ed70e873f0893d7e06f148524e3f0bdae2afb02e7819a0c24d1": "mainnet",
}

fails = []


def red(msg):
    fails.append(msg)
    print(f"  RED  {msg}")


def ok(msg):
    print(f"  ok   {msg}")


# ── a strict reader for the GENERATED Lean ────────────────────────────────────────────────
# The file is generated, so its shape is known. A shape change makes this parser fail LOUDLY,
# which is the correct behaviour: the checker must never silently check nothing.

def split_records(text, listname):
    m = re.search(r"def " + listname + r"[^\n]*\n \[\n(.*?)\n \]\n", text, re.S)
    if m is None:
        return None
    body = m.group(1)
    parts = re.split(r"\n?  \{ height := ", body)
    return ["height := " + p for p in parts if p.strip()]


def scalar(rec, name):
    m = re.search(name + r" := (\d+)", rec)
    return int(m.group(1)) if m else None


def natlist(rec, name):
    m = re.search(name + r" := \[([\d, ]*)\]", rec)
    if m is None:
        return None
    s = m.group(1).strip()
    return [int(x) for x in s.split(",")] if s else []


def listoflists(rec, name):
    m = re.search(name + r" := (\[\[.*?\]\])\n", rec, re.S)
    if m is None:
        return None
    return [[int(x) for x in inner.split(",")]
            for inner in re.findall(r"\[([\d, ]+)\]", m.group(1))]


def pairlist(rec, name):
    m = re.search(name + r" := \[(\(.*?\))\]\n", rec, re.S)
    if m is None:
        return None
    return [(int(a), int(b)) for a, b in re.findall(r"\((\d+), (\d+)\)", m.group(1))]


def pair(rec, name):
    m = re.search(name + r" := \((\d+), (\d+)\)", rec)
    return (int(m.group(1)), int(m.group(2))) if m else None


ABSORPTION_ORDER = [("z", 1), ("selectors", 6), ("w", 15), ("coefficients", 15), ("s", 6)]


def cols_in_absorption_order(cols, chunked):
    out = []
    for name, n in ABSORPTION_ORDER:
        v = cols[name]
        assert len(v) == n
        for e in v:
            if chunked:
                a, b = e
                assert len(a) == 1 and len(b) == 1
                out.append((a[0], b[0]))
            else:
                out.append((e[0], e[1]))
    return out


def run(root):
    global fails
    fails = []
    sys.path.insert(0, os.path.join(root, "metatheory/fixtures/pickles-extractors"))
    for m in [k for k in sys.modules if k == "walk"]:
        del sys.modules[m]
    import walk  # noqa: E402

    lean_path = os.path.join(root, LEAN)
    if not os.path.exists(lean_path):
        red(f"{LEAN} does not exist — the multi-block conformance module is GONE")
        return 1
    text = open(lean_path).read()

    # ---- 1. the fixture set on disk ------------------------------------------------------
    fixdir = os.path.join(root, FIXDIR)
    paths = []
    if os.path.isdir(fixdir):
        paths += [os.path.join(fixdir, f) for f in sorted(os.listdir(fixdir)) if f.endswith(".json")]
    ctl = os.path.join(root, CONTROL)
    if os.path.exists(ctl):
        paths.append(ctl)
    else:
        red(f"{CONTROL} — the CONTROL block's fixture is gone")

    print("── fixture set ──")
    on_disk = {}
    for p in paths:
        fx = json.load(open(p))
        net = CHAIN_IDS.get(fx["chain_id"])
        if net is None:
            red(f"{os.path.relpath(p, root)} — unknown chain_id {fx['chain_id']}")
            continue
        on_disk[int(fx["blockchain_length"])] = (net, p, fx)

    for h, (net, why) in sorted(DECLARED.items()):
        if h not in on_disk:
            red(f"declared fixture {net} {h} is NOT ON DISK — {why}")
        elif on_disk[h][0] != net:
            red(f"fixture {h} is on {on_disk[h][0]}, declared {net}")
        else:
            ok(f"{net} {h} — {why}")
    for h in sorted(on_disk):
        if h not in DECLARED:
            red(f"fixture {on_disk[h][0]} {h} is on disk but UNDECLARED — declare it with its axis")

    if len(on_disk) < MIN_FIXTURES:
        red(f"only {len(on_disk)} fixtures, floor is {MIN_FIXTURES} — the set is narrowing back "
            f"toward one block, which is the failure this gate exists to catch")
    nets = {v[0] for v in on_disk.values()}
    if len(nets) < MIN_NETWORKS:
        red(f"only {len(nets)} network(s) {sorted(nets)}, floor is {MIN_NETWORKS}")

    # every fixture must be TRACKED, or a green here says nothing about HEAD
    if subprocess.run(["git", "-C", root, "rev-parse", "--is-inside-work-tree"],
                      capture_output=True).returncode == 0:
        untracked = subprocess.run(
            ["git", "-C", root, "ls-files", "--others", "--exclude-standard", "--", FIXDIR],
            capture_output=True, text=True).stdout.split()
        for u in untracked:
            if u.endswith(".json"):
                red(f"{u} is UNTRACKED — a green on a working tree proves nothing about the commit")

    # ---- 2/3. the Lean's inputs ARE the fixtures' bytes -----------------------------------
    print("── the generated module's inputs vs an independent binprot re-walk ──")
    steps = split_records(text, "STEP_BLOCKS")
    wraps = split_records(text, "WRAP_BLOCKS")
    if steps is None or wraps is None:
        red(f"{LEAN} — cannot parse STEP_BLOCKS / WRAP_BLOCKS; the generator's shape changed and "
            f"this checker must be updated rather than left checking nothing")
        return 1
    if len(steps) != len(on_disk):
        red(f"{LEAN} carries {len(steps)} Step fixtures, {len(on_disk)} are on disk")
    if len(wraps) < MIN_WRAP_BLOCKS:
        red(f"{LEAN} carries {len(wraps)} Wrap fixtures, floor is {MIN_WRAP_BLOCKS}")

    for rec in steps:
        h = scalar(rec, "height")
        if h not in on_disk:
            red(f"Lean Step fixture {h} has NO fixture file")
            continue
        _net, p, fx = on_disk[h]
        try:
            w = walk.walk_b64(fx["protocol_state_proof_base64_urlsafe"])
        except Exception as e:  # a refusal is a finding, never a skip
            red(f"{h}: binprot walk REFUSED the committed proof — {type(e).__name__}: {e}")
            continue
        if w["_tail"] != 0:
            red(f"{h}: binprot walk left {w['_tail']} trailing bytes")
        want = {
            "spongeDigest": w["sponge_digest"],
            "ftEval1": w["ft_eval1"],
            "betaChal": w["beta"],
            "gammaChal": w["gamma"],
            "alphaChal": w["alpha"],
            "zetaChal": w["zeta"],
            "domainLog2": w["branch_domain_log2"],
        }
        bad = [k for k, v in want.items() if scalar(rec, k) != v]
        if pair(rec, "pubEval") != tuple(w["pub_eval"]):
            bad.append("pubEval")
        if natlist(rec, "bpChals") != w["bp_challenges"]:
            bad.append("bpChals")
        if listoflists(rec, "oldChals") != w["acc_challenges"]:
            bad.append("oldChals")
        if pairlist(rec, "evals") != cols_in_absorption_order(w["cols"], chunked=True):
            bad.append("evals")
        if bad:
            red(f"{h}: the generated Lean does NOT match the fixture's own bytes at {bad} — "
                f"regenerate with gen_multiblock_conformance.py")
        else:
            ok(f"{h}: 43 evaluation columns + 2x16 accumulator challenges + 16 bulletproof "
               f"challenges + digest + 4 plonk challenges + domain, all from the committed proof")

    # ---- 4. the targets agree across two openmina paths -----------------------------------
    print("── expand_deferred targets vs to_public_input slots, inside each Wrap record ──")
    step_by_h = {scalar(r, "height"): r for r in steps}
    for rec in wraps:
        h = scalar(rec, "height")
        pi = natlist(rec, "publicInput")
        s = step_by_h.get(h)
        if s is None or pi is None or len(pi) != 40:
            red(f"{h}: Wrap record has no matching Step record or no 40-word public input")
            continue
        bad = [(nm, slot) for nm, slot in
               [("tCip", 0), ("tB", 1), ("tZsrs", 2), ("tZdom", 3), ("tPerm", 4), ("tXi", 9)]
               if scalar(s, nm) != pi[slot]]
        if bad:
            red(f"{h}: expand_deferred targets disagree with to_public_input at {bad}")
        else:
            ok(f"{h}: all six deferred targets ARE public-input slots 0-4 and 9")
    # ⚠ NAMED GAP, not a silent one. A Step-ONLY fixture (the hardfork genesis, mainnet) has no
    # `to_public_input` answer, because that call needs a verifier index this tree cannot load for
    # it. Its six targets therefore come from ONE openmina function, `expand_deferred`, and nothing
    # here corroborates them. They are still a genuine differential against the LEAN derivation —
    # which is what the module's `#guard`s measure — but they are not corroborated twice.
    lone = sorted(set(step_by_h) - {scalar(r, "height") for r in wraps})
    if lone:
        print(f"  note {lone}: Step-ONLY fixtures — their six targets have a SINGLE openmina "
              f"source (`expand_deferred`); no `to_public_input` corroboration exists for them")
    return 1 if fails else 0


def self_test():
    """⚑ Prove the gate can go RED. Three corruptions, in a scratch copy; each must be caught."""
    print("== --self-test: the gate's own red path ==")
    bad = 0
    with tempfile.TemporaryDirectory() as td:
        scratch = os.path.join(td, "tree")
        for rel in [LEAN, FIXDIR, CONTROL, "metatheory/fixtures/pickles-extractors/walk.py"]:
            src, dst = os.path.join(ROOT, rel), os.path.join(scratch, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            (shutil.copytree if os.path.isdir(src) else shutil.copy2)(src, dst)

        cases = []

        def case(name, mutate):
            cases.append((name, mutate))

        def bend_field(field, height, terminator):
            """Bend ONE field of ONE fixture record. ⚑ The record is located by its height, not
            by the first textual match: the first `spongeDigest := ` in the file is `evalsOf`'s
            projection, and bending THAT is caught by nothing — which is exactly the miss this
            self-test found on its first run."""
            def go(root):
                p = os.path.join(root, LEAN)
                s = open(p).read()
                anchor = s.index(f"{{ height := {height},")
                i = s.index(f"{field} := ", anchor)
                j = s.index(terminator, i)
                open(p, "w").write(s[:i] + f"{field} := 12345" + s[j:])
            return go

        def drop_fixture(root):
            os.remove(os.path.join(root, FIXDIR, "devnet-540890.json"))

        # 540890 is chosen because it carries BOTH a Step and a Wrap record, so both the
        # walk-vs-Lean check and the two-openmina-paths check are in scope for it.
        case("a bent Lean INPUT (sponge digest) vs the fixture's own bytes",
             bend_field("spongeDigest", 540890, "\n"))
        case("a bent Lean INPUT (a bulletproof challenge) vs the fixture's own bytes",
             bend_field("bpChals", 540890, "\n"))
        case("a bent Lean TARGET vs the public-input slot beside it",
             bend_field("tCip", 540890, ","))
        case("a DROPPED fixture (the set narrowing back toward one block)", drop_fixture)

        for name, mutate in cases:
            work = os.path.join(td, "work")
            shutil.rmtree(work, ignore_errors=True)
            shutil.copytree(scratch, work)
            mutate(work)
            rc = run(work)
            if rc == 0:
                print(f"  RED-PATH FAILURE: {name} was NOT caught")
                bad += 1
            else:
                print(f"  ok   red path bites: {name}")
    return bad


def main():
    if "--self-test" in sys.argv:
        n = self_test()
        print()
        if n:
            print(f"== {n} RED PATH(S) DID NOT BITE — this gate cannot be trusted ==")
            return 1
        print("== red path proven: every corruption is caught ==")
        return 0
    print("== Mina multi-block conformance: the welds vs the PROTOCOL, not vs block 539508 ==")
    rc = run(ROOT)
    print()
    if rc:
        print(f"== {len(fails)} FINDING(S) ==")
    else:
        print("== ALL GREEN — every fixture declared, tracked, decoding, and byte-identical to "
              "the generated module's inputs; every deferred target agrees across two openmina "
              "paths ==")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
