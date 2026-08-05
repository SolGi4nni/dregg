#!/usr/bin/env python3
"""Per-slot PI census over the EMITTED descriptor registries.

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

def report(path, label):
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
    print(f"{'slot':42s} {'members-with':>12s} {'felts-bound':>12s}")
    for name, base, ln in L:
        if base >= V1_PI_COUNT: break
        print(f"{name:42s} {have[name]:>12d} {bind[name]:>12d}")
    for n in ROT_TAIL + ["tail::(per-effect/rc/wide)"]:
        print(f"{n:42s} {have[n]:>12d} {bind[n]:>12d}")
    return ms

REGISTRIES = [
    ("circuit/descriptors/rotation-wide-registry-staged.tsv", "WIDE (deployed)"),
    ("circuit/descriptors/rotation-v3-staged-registry.tsv", "V3 staged"),
]

if __name__ == "__main__":
    import os, sys
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    if "--json" in sys.argv:
        out = {}
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
            report(os.path.join(root, path), lab)
            print()
