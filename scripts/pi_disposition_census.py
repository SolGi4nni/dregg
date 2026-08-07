#!/usr/bin/env python3
r"""Per-slot PI census over the EMITTED descriptor registries.

WHAT IT COUNTS, and why that is the whole question: a `pi_binding` constraint is
the ONLY kind that reads a public input.  `circuit/src/descriptor_ir2.rs` has
exactly one `pv[*pi_index]` site (the `PiBinding` arm); neither `WindowExpr` nor
`ChalExpr` carries a public-input leaf.  The Lean twin is the same shape and is
now a theorem: `env.pub` is projected at EXACTLY the two `.piBinding` arms of
`VmConstraint.holdsVm` and nowhere else, which is what makes
`Emit.PiDeclaration.unpinned_pi_admits_any_value` provable -- overwrite an
unpinned slot with an arbitrary value and the SAME descriptor is still
satisfied.

So "unpinned" here means: THE CONSTRAINT SYSTEM NEVER LOOKS.  A verifier reading
that slot is reading the producer's word.

## /!\ SCOPE, AND THE WOUND THAT TAUGHT IT (2026-08-07)

"Unpinned in these two registries" is NOT "nothing reads it", and reading the
table as if it were cost a lane a whole VK rotation on a false premise.
`docs/PI-DISPOSITION.md` Sec.6 declared `EFFECTS_HASH_GLOBAL` (v1 offsets 37..40)
dead -- "is there a reader? none" -- off exactly this table's zero.  It is not
dead.  Those four felts are the declared storage of `sched::EFFECTS_HASH_GLOBAL`
inside the 49-felt bilateral-schedule contract window `inner_pi[33, 82)`, which
`bilateral_aggregation_air::schedule_block_from_inner_pi` projects (host-side)
into the DEPLOYED `dregg-bilateral-aggregation-v3` main trace at cols 4..7 --
where they are FORCED by four `window_gate` transitions (equal on every row) and
PINNED first+last to that descriptor's own `PI[4..7]`.  A slot can be unpinned
in its OWN descriptor and load-bearing in ANOTHER one that consumes the window.

So this file now carries `PROJECTIONS`: every KNOWN v1-window consumer outside
these two registries, CHECKED against the emitted bytes rather than asserted.
The per-slot table gains a `proj-read` column, and the run REFUSES (exit 1) if a
declared projection's target columns stop being forced+pinned -- so the
annotation cannot rot into a lie, and deleting the consumer goes RED here
instead of quietly restoring a "nothing reads it" verdict.

`PROJECTIONS` is a list of the projections we have MEASURED, not a proof that no
other exists.  A zero in `felts-bound` with a blank `proj-read` means "no reader
is known to this script", never "no reader exists" -- go read the consumers
before you delete a slot.

Run:  python3 scripts/pi_disposition_census.py
      python3 scripts/pi_disposition_census.py --json      (machine-readable)

The slot names below are the ROTATED PI WINDOW: indices 0..41 are the v1 prefix
(`trace_rotated::V1_PI_COUNT = 42`, itself `pi::ACTOR_NONCE + 1`), 42..45 the
four appended rotated pins, and everything past that is the per-effect / dsl-rc /
wide tail, which varies per member and is reported as one bucket.
"""
import json, sys, collections

# ---- the v1/v2 PI layout, computed exactly as circuit/src/effect_vm/pi.rs does ----
L = []          # (name, base, len)
def slot(name, ln=1):
    base = L[-1][1] + L[-1][2] if L else 0
    L.append((name, base, ln)); return base

slot("OLD_COMMIT", 8); slot("NEW_COMMIT", 8); slot("EFFECTS_HASH", 4)
slot("INIT_BAL_LO"); slot("INIT_BAL_HI"); slot("FINAL_BAL_LO"); slot("FINAL_BAL_HI")
slot("NET_DELTA_MAG"); slot("NET_DELTA_SIGN")
slot("CURRENT_BLOCK_HEIGHT"); slot("MAX_CUSTOM_EFFECTS"); slot("CUSTOM_EFFECT_COUNT")
slot("APPROVED_HANDOFFS", 4)
slot("TURN_HASH", 4)
slot("EFFECTS_HASH_GLOBAL", 4)
slot("ACTOR_NONCE")
slot("PREVIOUS_RECEIPT_HASH", 4)
for n in ("OUTBOUND_TRANSFER_COUNT","INBOUND_TRANSFER_COUNT","OUTBOUND_GRANT_COUNT",
          "INBOUND_GRANT_COUNT","INTRO_AS_INTRODUCER_COUNT","INTRO_AS_RECIPIENT_COUNT",
          "INTRO_AS_TARGET_COUNT"): slot(n)
for n in ("OUTGOING_TRANSFER_ROOT","INCOMING_TRANSFER_ROOT","OUTGOING_GRANT_ROOT",
          "INCOMING_GRANT_ROOT","INTRO_AS_INTRODUCER_ROOT","INTRO_AS_RECIPIENT_ROOT",
          "INTRO_AS_TARGET_ROOT"): slot(n, 4)
slot("IS_AGENT_CELL")
slot("SOVEREIGN_WITNESS_KEY_COMMIT", 4); slot("SOVEREIGN_WITNESS_SEQUENCE"); slot("IS_SOVEREIGN_CELL")
slot("SOVEREIGN_TRANSITION_PROOF_VK_HASH", 4); slot("SOVEREIGN_TRANSITION_PROOF_COMMITMENT", 4)
slot("HAS_TRANSITION_PROOF")
slot("BRIDGE_MINT_VALUE_LIMBS", 4); slot("BRIDGE_LOCK_VALUE_LIMBS", 4); slot("CREATE_ESCROW_AMOUNT_LIMBS", 4)
slot("SLOT_CAVEAT_COUNT"); slot("SLOT_CAVEAT_MANIFEST", 24)
slot("CROSS_EFFECT_DEPS_COUNT"); slot("CROSS_EFFECT_DEPS", 24)
slot("WITNESS_INDEX_MAP_COUNT"); slot("WITNESS_INDEX_MAP", 16)
slot("UNILATERAL_ATTESTATIONS_COUNT"); slot("UNILATERAL_ATTESTATIONS_ROOT", 4)
slot("EMIT_EVENT_COUNT"); slot("EMIT_EVENT_TOPIC_HASH", 8); slot("EMIT_EVENT_PAYLOAD_HASH", 8)
slot("FEDERATION_ID", 4); slot("OWNER_CELL_ID", 4)
slot("NOTESPEND_NULLIFIER"); slot("NOTECREATE_COMMITMENT"); slot("BURN_TARGET_PI")
BASE_COUNT = L[-1][1] + L[-1][2]
assert BASE_COUNT == 209, BASE_COUNT
slot("v3::COMMITTED_HEIGHT"); slot("v3::RATE_BOUND_TAG"); slot("v3::CHALLENGE_WINDOW_TAG"); slot("v3::ASSET_CLASS")
assert L[-1][1] == 212

V1_PI_COUNT = 42
ROT_TAIL = ["rot::OLD_COMMIT", "rot::NEW_COMMIT", "rot::COMMITTED_HEIGHT", "rot::CAVEAT_COMMIT"]

def slot_of(i):
    """Name the rotated-window PI index i."""
    if i < V1_PI_COUNT:
        for name, base, ln in L:
            if base <= i < base + ln:
                return name if ln == 1 else f"{name}[{i-base}]", name
        return f"v1::{i}", f"v1::{i}"
    if i < V1_PI_COUNT + 4:
        n = ROT_TAIL[i - V1_PI_COUNT]; return n, n
    return f"tail::{i}", "tail::(per-effect/rc/wide)"

# ---------------------------------------------------------------------------
# PROJECTIONS -- v1-PI-window consumers that live OUTSIDE the two registries.
#
# Each entry is CHECKED against the emitted descriptor bytes on every run (see
# `check_projections`), never merely asserted.  If the consumer stops forcing or
# pinning the columns it claims, the run goes RED rather than silently handing
# the slot back to the "nothing reads it" column.
# ---------------------------------------------------------------------------
PROJECTIONS = [
    {
        # `bilateral_aggregation_air.rs`: `SCHEDULE_PI_BASE == inner_pi::TURN_HASH_BASE
        # == 33`, `sched::WIDTH == 49`, and `schedule_block_from_inner_pi` copies
        # `inner_pi[33, 82)` into the aggregation main trace at cols [0, 49).
        # Pinned by `schedule_block_offsets_match_v1_pi_window` on the Rust side and
        # emitted from `EffectVmEmitBilateralAgg.lean` (`turnIdBindings`) on the Lean side.
        "name": "bilateral-schedule window -> dregg-bilateral-aggregation-v3",
        "descriptor": "circuit/descriptors/dregg-bilateral-aggregation-v3.json",
        "src_base": 33,
        "width": 49,
        # Cols the aggregation PINS to its own outer PI (turn hash 0..3,
        # effects-hash-global 4..7, actor nonce 8, previous-receipt hash 9..12).
        "bound_cols": list(range(0, 13)),
        # Cols something OTHER than the pin reads -- the 13 window_gate transitions
        # that hold the turn-identity block equal on every row, plus IS_AGENT_CELL
        # (col 48), which the booleanity/cumulative gates read.  The counts/roots
        # (cols 13..47) are CARRIED, not bound: their `expected_*` self-check block
        # was deleted in the v3 compaction, so they are deliberately absent here.
        "forced_cols": list(range(0, 13)) + [48],
        "reader": "schedule_block_from_inner_pi (turn-prover::aggregate_bilateral_prover"
                  " -- the path taken whenever a WR carries no native bilateral_schedule)",
        # The projection reads the FULL v1 PI vector (it requires
        # `len >= inner_pi::ACTIVE_BASE_COUNT`), not the 42-felt rotated window a
        # rotated leg publishes -- a rotated WR must carry the block natively.  The
        # annotation still belongs on this table because both vectors are the SAME
        # `pi.rs` LAYOUT: deleting a slot there removes it from both.

    },
]


def _cols_read(node, acc):
    """Every trace column a DescriptorIR2 expression node reads."""
    if isinstance(node, dict):
        t = node.get("t")
        if t == "var" and isinstance(node.get("v"), int):
            acc.add(node["v"])
        elif t in ("loc", "nxt") and isinstance(node.get("c"), int):
            acc.add(node["c"])
        for v in node.values():
            _cols_read(v, acc)
    elif isinstance(node, list):
        for v in node:
            _cols_read(v, acc)


def check_projections(root):
    """Verify every declared projection against the EMITTED descriptor bytes.

    Returns `(ok, findings, proj_read)` where `proj_read` maps a v1 PI index to
    the projection entry that consumes it.  A declared projection whose target
    columns are no longer forced+pinned is a FINDING, not a silent downgrade.
    """
    import os
    findings, proj_read = [], {}
    for p in PROJECTIONS:
        path = os.path.join(root, p["descriptor"])
        if not os.path.exists(path):
            findings.append(f"{p['name']}: descriptor MISSING at {p['descriptor']}")
            continue
        d = json.load(open(path))
        cs = d.get("constraints", [])
        pinned = {c["col"] for c in cs if c.get("t") == "pi_binding"}
        forced = set()
        for c in cs:
            if c.get("t") != "pi_binding":
                _cols_read(c, forced)
        missing_pin = sorted(set(p["bound_cols"]) - pinned)
        missing_force = sorted(set(p["forced_cols"]) - forced)
        if missing_pin:
            findings.append(
                f"{p['name']}: cols {missing_pin} are declared PINNED and carry no "
                f"pi_binding in {p['descriptor']}")
        if missing_force:
            findings.append(
                f"{p['name']}: cols {missing_force} are declared FORCED and are read by "
                f"no non-pin constraint in {p['descriptor']}")
        for col in sorted(set(p["bound_cols"]) | set(p["forced_cols"])):
            if col < p["width"]:
                proj_read[p["src_base"] + col] = p
    return (not findings), findings, proj_read


def census(path):
    members, rows = [], []
    for line in open(path):
        line = line.rstrip("\n")
        if not line.strip(): continue
        parts = line.split("\t")
        ident, name, js = parts[0], parts[1], parts[2]
        d = json.loads(js)
        n = d["public_input_count"]
        bound = set()
        for c in d.get("constraints", []):
            if isinstance(c, dict) and c.get("t") == "pi_binding":
                bound.add(c["pi_index"])
        members.append((ident, name, n, bound))
    return members

def report(path, label, proj_read=None):
    proj_read = proj_read or {}
    ms = census(path)
    tot_pi = sum(m[2] for m in ms)
    tot_b  = sum(len(m[3]) for m in ms)
    print(f"### {label}  ({path})")
    print(f"members={len(ms)}  Sigma PI={tot_pi}  Sigma bound={tot_b}  UNBOUND={tot_pi-tot_b} ({100*(tot_pi-tot_b)/tot_pi:.1f}%)")
    # per-slot: how many members bind ANY index of that slot / how many members HAVE it
    have = collections.Counter(); bind = collections.Counter()
    for ident, name, n, bound in ms:
        seen = set()
        for i in range(n):
            _, grp = slot_of(i)
            seen.add(grp)
            if i in bound: bind[grp] += 1
        for g in seen: have[g] += 1
    print(f"{'slot':42s} {'members-with':>12s} {'felts-bound':>12s}  {'proj-read'}")
    for name, base, ln in L:
        if base >= V1_PI_COUNT: break
        pr = sum(1 for i in range(base, base + ln) if i in proj_read)
        tag = "" if not pr else f"{pr}/{ln} via {proj_read[base if base in proj_read else next(i for i in range(base, base+ln) if i in proj_read)]['descriptor'].split('/')[-1]}"
        print(f"{name:42s} {have[name]:>12d} {bind[name]:>12d}  {tag}")
    for n in ROT_TAIL + ["tail::(per-effect/rc/wide)"]:
        print(f"{n:42s} {have[n]:>12d} {bind[n]:>12d}")
    return ms

def self_test_projections(root):
    """Drive the projection check RED and GREEN on a throwaway copy.

    A gate that cannot go red is not a gate.  This builds the mutation
    CONSTRUCTIVELY and asserts it happened before reading any verdict -- a
    mutation that silently became a no-op is how a falsifier stops falsifying.
    Touches nothing shared: everything happens under a `tempfile.mkdtemp`.
    """
    import os, shutil, tempfile
    tmp = tempfile.mkdtemp(prefix="pi-census-selftest-")
    try:
        for p in PROJECTIONS:
            src = os.path.join(root, p["descriptor"])
            dst = os.path.join(tmp, p["descriptor"])
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(src, dst)
        ok, findings, _ = check_projections(tmp)
        if not ok:
            print("self-test: GREEN CONTROL FAILED on an unmutated copy: "
                  + "; ".join(findings), file=sys.stderr)
            return 1
        print("self-test: green control OK (unmutated copy passes)")

        for p in PROJECTIONS:
            dst = os.path.join(tmp, p["descriptor"])
            d = json.load(open(dst))
            before = len(d["constraints"])
            target = set(p["forced_cols"])
            kept = []
            for c in d["constraints"]:
                if c.get("t") == "pi_binding":
                    kept.append(c); continue
                acc = set(); _cols_read(c, acc)
                if acc & target:
                    continue                      # drop: this is the mutation
                kept.append(c)
            d["constraints"] = kept
            if len(kept) >= before:
                print(f"self-test: MUTATION WAS A NO-OP on {p['descriptor']} "
                      f"({before} -> {len(kept)} constraints) -- the adversary is dead, "
                      "the verdict below would be meaningless", file=sys.stderr)
                return 1
            print(f"self-test: mutated {p['descriptor']}: constraints "
                  f"{before} -> {len(kept)} (dropped {before - len(kept)})")
            json.dump(d, open(dst, "w"))

        ok, findings, _ = check_projections(tmp)
        if ok:
            print("self-test: RED PROOF FAILED -- the projection check still passes with every "
                  "forcing constraint deleted.  It is not detecting anything.", file=sys.stderr)
            return 1
        print("self-test: red proof OK -- check refuses with the forcing constraints gone:")
        for f in findings:
            print(f"  {f}")
        return 0
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


REGISTRIES = [
    ("circuit/descriptors/rotation-wide-registry-staged.tsv", "WIDE (deployed)"),
    ("circuit/descriptors/rotation-v3-staged-registry.tsv", "V3 staged"),
]

if __name__ == "__main__":
    import os, sys
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if "--self-test-projections" in sys.argv:
        sys.exit(self_test_projections(root))
    ok, findings, proj_read = check_projections(root)
    if "--json" in sys.argv:
        out = {"projections_ok": ok, "projection_findings": findings,
               "projection_read_v1_indices": sorted(proj_read)}
        for path, lab in REGISTRIES:
            ms = census(os.path.join(root, path))
            out[lab] = {
                "members": len(ms),
                "pi_total": sum(m[2] for m in ms),
                "pi_bound": sum(len(m[3]) for m in ms),
                "pi_unbound": sum(m[2] - len(m[3]) for m in ms),
            }
        print(json.dumps(out, indent=2))
    else:
        for path, lab in REGISTRIES:
            report(os.path.join(root, path), lab, proj_read)
            print()
        print("### PROJECTIONS (v1-window consumers outside these registries)")
        for p in PROJECTIONS:
            lo, hi = p["src_base"], p["src_base"] + p["width"]
            print(f"  {p['name']}")
            print(f"    v1 PI [{lo}, {hi}) -> cols [0, {p['width']}); "
                  f"{len(p['bound_cols'])} pinned, {len(p['forced_cols'])} forced")
            print(f"    reader: {p['reader']}")
        print(f"  verdict: {'OK' if ok else 'FINDINGS'}")
        for f in findings:
            print(f"    /!\\ {f}")
    if not ok:
        print("pi_disposition_census: REFUSED -- a declared projection no longer holds. "
              "Do NOT read a zero in `felts-bound` as `nothing reads it`.", file=sys.stderr)
        sys.exit(1)
