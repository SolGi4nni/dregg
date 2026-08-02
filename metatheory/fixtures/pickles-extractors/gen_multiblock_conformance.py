#!/usr/bin/env python3
"""gen_multiblock_conformance — emit `Dregg2/Bridge/MinaMultiBlockConformance.lean`.

⚑ WHY. Every real-data conformance claim in the Bridge welds was pinned to ONE devnet block,
539508. Anything accidentally fitted to that block's particulars could never show. This generator
runs the SAME extraction over every fixture in `metatheory/fixtures/mina-blocks/` and emits one
Lean module in which the SAME weld functions run over all of them.

## The two code paths, and why this is a differential rather than a restatement

  * **INPUTS** come from `walk.py` — the independent Python re-walk of `bridge/src/mina_pickles.rs`
    `decode_proof_at`. It consumes the binprot object with zero trailing bytes, which is the
    structural check that the layout is the right one.
  * **TARGETS** come from openmina: `ledger::proofs::step::expand_deferred`,
    `ProverProof::oracles`, `PolishToken::evaluate(constant_term)`, `PreparedStatement::
    to_public_input`, and (group side) the IPA transcript `SRS::verify` itself accepts.

Values that appear in BOTH are cross-checked HERE, at generation time, and a disagreement is a
hard failure — a walk that had desynchronised by one field would not reproduce a 255-bit digest
and sixteen 128-bit challenges.

## Run

    cd metatheory/fixtures/pickles-extractors
    python3 gen_multiblock_conformance.py \
        --fixtures ../mina-blocks --out-dir <extractor json dir> \
        --lean ../../Dregg2/Bridge/MinaMultiBlockConformance.lean
"""
import argparse
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import walk  # noqa: E402

PN = 28948022309329048855892746252171976963363056481941560715954676764349967630337
QN = 28948022309329048855892746252171976963363056481941647379679742748393362948097

# `Plonk_types.Evals.to_absorption_sequence` order (`plonk_types.ml:487-499`):
# z, the 6 selectors, w x15, coefficients x15, s x6 = 43 columns.
ABSORPTION_ORDER = [("z", 1), ("selectors", 6), ("w", 15), ("coefficients", 15), ("s", 6)]


def cols_in_absorption_order(cols, chunked):
    """Flatten walk.py's column dict into the 43-column absorption sequence."""
    out = []
    for name, n in ABSORPTION_ORDER:
        v = cols[name]
        assert len(v) == n, f"column {name}: {len(v)} != {n}"
        for e in v:
            if chunked:
                a, b = e
                assert len(a) == 1 and len(b) == 1, f"{name}: chunk count != 1 ({len(a)},{len(b)})"
                out.append((a[0], b[0]))
            else:
                out.append((e[0], e[1]))
    assert len(out) == 43
    return out


def fail(msg):
    raise SystemExit(f"gen_multiblock_conformance: {msg}")


def cross_check(tag, a, b, what):
    if a != b:
        fail(f"{tag}: WALK vs OPENMINA disagree on {what}\n  walk    = {a}\n  openmina= {b}")


def collect(fixture_path, out_dir):
    """One block: walk it, read whatever extractor outputs exist, cross-check, return a record."""
    fx = json.load(open(fixture_path))
    base = os.path.basename(fixture_path)[: -len(".json")]
    # Network and height come from the fixture's own content, not from its filename — block
    # 539508's fixture predates the naming convention and lives at its historical path.
    CHAIN_IDS = {
        "29936104443aaf264a7f0192ac64b1c7173198c1ed404c1bcff5e562e05eb7f6": "devnet",
        "5f704cc0c82e0ed70e873f0893d7e06f148524e3f0bdae2afb02e7819a0c24d1": "mainnet",
    }
    network = CHAIN_IDS.get(fx["chain_id"])
    if network is None:
        fail(f"{base}: unknown chain_id {fx['chain_id']}")
    height = int(fx["blockchain_length"])
    w = walk.walk_b64(fx["protocol_state_proof_base64_urlsafe"])
    if w["_tail"] != 0:
        fail(f"{base}: binprot walk left {w['_tail']} trailing bytes")

    rec = {
        "base": base,
        "network": network,
        "height": height,
        "state_hash": fx["state_hash"],
        "n_user_commands": fx.get("n_user_commands"),
        "n_zkapp_commands": fx.get("n_zkapp_commands"),
        "n_snark_jobs": fx.get("n_snark_jobs"),
        "walk": w,
    }

    def load(suffix):
        # ⚠ An EMPTY output file means the extractor REFUSED that block on that path (the
        # devnet gate `assert!`s `kimchi::verifier::verify == Ok`, and the hardfork genesis
        # block's dummy proof does not verify). Absent evidence, not evidence of absence —
        # the block then appears in the Step-side fixtures only.
        p = os.path.join(out_dir, base + suffix)
        if not os.path.exists(p) or os.path.getsize(p) == 0:
            return None
        return json.load(open(p))

    rec["deferred"] = load(".deferred.json")
    rec["full"] = load(".out.json")
    rec["group"] = load(".group.json")

    # ---- STEP side: inputs (walk) vs targets (openmina expand_deferred) -----------------
    d = rec["deferred"] or rec["full"]
    if d is None:
        fail(f"{base}: no extractor output in {out_dir}")
    sd = d["step_deferred_values"]
    cross_check(base, w["alpha"], int(sd["alpha"]), "deferred_values.plonk.alpha")
    cross_check(base, w["beta"], int(sd["beta"]), "deferred_values.plonk.beta")
    cross_check(base, w["gamma"], int(sd["gamma"]), "deferred_values.plonk.gamma")
    cross_check(base, w["zeta"], int(sd["zeta"]), "deferred_values.plonk.zeta")
    cross_check(
        base,
        w["branch_domain_log2"],
        int(d["wrap_shape"]["branch_data_domain_log2"]),
        "branch_data.domain_log2",
    )
    cross_check(base, len(w["lr"]), int(d["wrap_shape"]["ipa_rounds_k"]), "ipa rounds k")

    rec["step_evals"] = cols_in_absorption_order(w["cols"], chunked=True)
    # ⚑ THE TARGETS ARE THE **SHIFTED** VALUES. `PreparedStatement::to_public_input` puts the
    # Type-1 shifted encoding in public-input slots 0-4, which is exactly what Lean's
    # `expandDeferred` returns; `xi` is a raw 128-bit challenge and is not shifted.
    rec["step_targets"] = {
        "cip": int(sd["combined_inner_product_shifted"]),
        "b": int(sd["b_shifted"]),
        "zsrs": int(sd["zeta_to_srs_length_shifted"]),
        "zdom": int(sd["zeta_to_domain_size_shifted"]),
        "perm": int(sd["perm_shifted"]),
        "xi": int(sd["xi"]),
    }
    # …and when the FULL gate ran, the five shifted words must BE public-input slots 0-4 and 9,
    # which is a third code path (`to_public_input`) agreeing with `expand_deferred`.
    if rec["full"]:
        pi = [int(x) for x in rec["full"]["wrap_public_input"]]
        for slot, key in [(0, "cip"), (1, "b"), (2, "zsrs"), (3, "zdom"), (4, "perm"), (9, "xi")]:
            cross_check(base, rec["step_targets"][key], pi[slot],
                        f"expand_deferred {key} vs to_public_input slot {slot}")

    # ---- WRAP side: only for blocks the FULL (verifying) gate accepted ------------------
    if rec["full"] and rec["group"]:
        f, g = rec["full"], rec["group"]
        t = f["wrap_transcript"]
        cross_check(base, [w["w_comm"][0][0], w["w_comm"][0][1]],
                    [int(x) for x in t["phase1_w_comm_xy"][:2]], "w_comm[0] (x,y)")
        cross_check(base, list(w["z_comm"]), [int(x) for x in t["phase1_z_comm_xy"]], "z_comm")
        cross_check(base, [x for p in w["t_comm"] for x in p],
                    [int(x) for x in t["phase1_t_comm_xy"]], "t_comm")
        cross_check(base, [x for p in w["acc_comm"] for x in p],
                    [int(x) for x in t["phase1_prev_comm_xy"]], "prev/accumulator comm")
        cross_check(base, list(w["delta"]),
                    [int(g["bulletproof_rung"]["delta"]["x"]), int(g["bulletproof_rung"]["delta"]["y"])],
                    "delta")
        wrap_cols = cols_in_absorption_order(w["wrap_evals"], chunked=False)
        es_z = [int(x) for x in f["c8_gold"]["es_zeta"]][4:]
        es_w = [int(x) for x in f["c8_gold"]["es_zeta_omega"]][4:]
        cross_check(base, [c[0] for c in wrap_cols], es_z, "wrap evals at zeta (43 cols)")
        cross_check(base, [c[1] for c in wrap_cols], es_w, "wrap evals at zeta_omega (43 cols)")
        rec["wrap_cols"] = wrap_cols
        rec["wrap"] = {
            "vk_digest": int(t["verifier_index_digest"]),
            "prev_comm": [int(x) for x in t["phase1_prev_comm_xy"]],
            "pub_comm": [int(x) for x in t["phase1_public_comm_xy"]],
            "w_comm": [int(x) for x in t["phase1_w_comm_xy"]],
            "z_comm": [int(x) for x in t["phase1_z_comm_xy"]],
            "t_comm": [int(x) for x in t["phase1_t_comm_xy"]],
            "endo_r": int(t["endo_r"]),
            "beta": int(t["beta"]),
            "gamma": int(t["gamma"]),
            "alpha_chal": int(t["alpha_chal"]),
            "zeta_chal": int(t["zeta_chal"]),
            "fq_digest": int(t["fq_digest"]),
            "cip_shifted": int(g["bulletproof_rung"]["combined_inner_product_shifted"]),
            # `lr` is a list of [L, R] point pairs; `MinaWrapChallenges.ipaChallengesOf`
            # absorbs each round as the flat 4-vector Lx Ly Rx Ry.
            "lr": [[int(p[0]["x"]), int(p[0]["y"]), int(p[1]["x"]), int(p[1]["y"])]
                   for p in g["bulletproof_rung"]["lr"]],
            "delta": [int(g["bulletproof_rung"]["delta"]["x"]),
                      int(g["bulletproof_rung"]["delta"]["y"])],
            "ipa_t": int(g["bulletproof_rung"]["u_base_preimage_t"]),
            "ipa_prechals": [int(x) for x in g["bulletproof_rung"]["ipa_prechallenges"]],
            "c_prechal": int(g["bulletproof_rung"]["c_prechallenge"]),
            "public_input": [int(x) for x in f["wrap_public_input"]],
            "shift": [int(x) for x in f["c5_gold"]["shift"]],
            "p_zeta": int(f["c5_gold"]["p_zeta"]),
            "ft_eval0": int(f["c5_gold"]["ft_eval0"]),
            "lin_const_term": int(f["c5_gold"]["lin_const_term"]),
            "domain_log2": int(f["wrap_shape"]["domain_log2"]),
            "max_poly_size": int(f["wrap_shape"]["max_poly_size"]),
            "zeta_to_srs_len": int(g["group_scalars"]["zeta_to_srs_len"]),
            "zeta_to_domain_size": int(g["group_scalars"]["zeta_to_domain_size"]),
            # ⚑ `MinaWrapGroupGate.SIGMA6` — `combine_points[41..46]`, the six sigma commitments.
            # Claimed to be VERIFIER-KEY config; whether it is is a per-block measurement.
            "sigma6": [int(v) for pt in g["combine_points"][41:47] for v in (pt["x"], pt["y"])],
            # ⚑ `MinaWrapGroupGate.FT_COMM_GOLD` — claimed to be per-BLOCK data.
            "ft_comm_gold": [int(g["ft_comm_gold"]["x"]), int(g["ft_comm_gold"]["y"])],
            # The 40 SRS Lagrange commitments `MinaStepPrevCommitments.LAGRANGE_XY` carries.
            "lagrange": [int(v) for pt in g["public_comm_rung"]["lagrange_basis"]
                         for v in (pt["x"], pt["y"])],
        }
        # ⚑ The oracles' ft_eval0 and the c5 gold must be the same number, on two paths.
        cross_check(base, int(f["wrap_oracles"]["ft_eval0"]), rec["wrap"]["ft_eval0"],
                    "oracles().ft_eval0 vs c5_gold.ft_eval0")
    return rec


# ---------------------------------------------------------------- Lean rendering


def nats(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


def pairs(ps):
    return "[" + ", ".join(f"({a}, {b})" for a, b in ps) + "]"


def lists(ls):
    return "[" + ", ".join(nats(x) for x in ls) + "]"


def step_record(r):
    w = r["walk"]
    t = r["step_targets"]
    return f"""  {{ height := {r['height']}, net := "{r['network']}"
    spongeDigest := {w['sponge_digest']}
    oldChals := {lists(w['acc_challenges'])}
    ftEval1 := {w['ft_eval1']}
    pubEval := ({w['pub_eval'][0]}, {w['pub_eval'][1]})
    evals := {pairs(r['step_evals'])}
    bpChals := {nats(w['bp_challenges'])}
    betaChal := {w['beta']}, gammaChal := {w['gamma']}
    alphaChal := {w['alpha']}, zetaChal := {w['zeta']}
    domainLog2 := {w['branch_domain_log2']}
    tCip := {t['cip']}, tB := {t['b']}, tZsrs := {t['zsrs']}, tZdom := {t['zdom']}
    tPerm := {t['perm']}, tXi := {t['xi']} }}"""


def wrap_record(r):
    v = r["wrap"]
    return f"""  {{ height := {r['height']}
    vkDigest := {v['vk_digest']}
    prevComm := {nats(v['prev_comm'])}
    pubComm := {nats(v['pub_comm'])}
    wComm := {nats(v['w_comm'])}
    zComm := {nats(v['z_comm'])}
    tComm := {nats(v['t_comm'])}
    endoR := {v['endo_r']}
    cipShifted := {v['cip_shifted']}
    lr := {lists(v['lr'])}
    delta := {nats(v['delta'])}
    ez := {nats([c[0] for c in r['wrap_cols']])}
    ew := {nats([c[1] for c in r['wrap_cols']])}
    publicInput := {nats(v['public_input'])}
    shift := {nats(v['shift'])}
    log2n := {v['domain_log2']}
    tBeta := {v['beta']}, tGamma := {v['gamma']}
    tAlphaChal := {v['alpha_chal']}, tZetaChal := {v['zeta_chal']}
    tFqDigest := {v['fq_digest']}
    tT := {v['ipa_t']}, tPrechals := {nats(v['ipa_prechals'])}, tCPre := {v['c_prechal']}
    tPZeta := {v['p_zeta']}
    tFt0 := {v['ft_eval0']}, tLct := {v['lin_const_term']}
    sigma6 := {nats(v['sigma6'])}
    ftCommGold := ({v['ft_comm_gold'][0]}, {v['ft_comm_gold'][1]})
    lagrange := {nats(v['lagrange'])} }}"""


HEADER = r'''/-
# `Dregg2.Bridge.MinaMultiBlockConformance` — ⚑⚑ **THE WELDS, RE-RUN ON BLOCKS THAT ARE NOT 539508.**

GENERATED by `metatheory/fixtures/pickles-extractors/gen_multiblock_conformance.py`. Do not edit by
hand: regenerate. The generator refuses to emit if the two extraction paths disagree anywhere they
overlap, so a green file already carries that differential.

## The gap this closes

Every real-data conformance claim in `Dregg2/Bridge/MinaWrap*Weld.lean`,
`StepMainFtEval0RealBlock.lean` and `MinaStepPrevCommitments.lean` is stated over **one** devnet
block, 539508. A constant accidentally fitted to that block's particulars — a value that happens to
equal something there, a branch never taken because that block's shape does not take it — could
never show. This file runs the SAME functions on other blocks.

## The two code paths

| | source |
|---|---|
| **INPUTS** | `walk.py`, the independent Python re-walk of `bridge/src/mina_pickles.rs::decode_proof_at`; zero trailing bytes on every fixture |
| **TARGETS** | openmina: `ledger::proofs::step::expand_deferred`, `ProverProof::oracles`, `PolishToken::evaluate(constant_term)`, `PreparedStatement::to_public_input`, and the IPA transcript `SRS::verify` itself accepts |

Values present in both are cross-checked in the generator; the block's expectations are its OWN
decoded wire, never 539508's constants carried across.

## ⚑ WHAT THE FIXTURE SET CAN AND CANNOT VARY — measured, not assumed

40 consecutive devnet blocks were decoded before choosing. **Every devnet blockchain-SNARK Wrap
proof has the same shape**: `branch_data = (proofs_verified = N2, domain_log2 = 16)`, 2 accumulator
commitments, 15 IPA rounds, one chunk per evaluation column, and an identical binprot length. That
is a property of the RULE, not of the instance — so no additional devnet block can exercise a
different `proofs_verified` or a different domain, and **a fixture set of block proofs cannot
refute a constant fitted to those**. The axes that DO vary, and on which the fixtures were chosen:

  * transaction content — from an empty block (0 user commands, 0 zkApp commands, 0 snark jobs) to
    the busiest in the window (4 / 3 / 35). This changes the Step proof being wrapped, hence every
    field value, the accumulator challenges and the accumulator commitments.
  * the **hardfork genesis block**, whose proof is 32 binprot bytes SHORTER than every other block's
    — a degenerate/dummy object whose small challenge limbs take short varints. `expand_deferred`
    runs on it; ⚠ `kimchi::verifier::verify` REJECTS it (`Err(OpenProof)`), which is correct: Mina's
    genesis carries a dummy blockchain proof. It is therefore a STEP-side fixture only.
  * **mainnet**, a different network with a different verification key and a different genesis.
    ⚠ Step-side only, and the blocker is named: openmina at `82480cd468` cannot load its own
    embedded mainnet verifier index (stale serde format, `PolyComm` as `{unshifted, shifted}` and
    the domain as an arkworks-0.3 int array where a hex string is expected), so `BlockVerifier::
    make()` panics and the Wrap-side ground truths are unobtainable. `expand_deferred` needs no
    verifier index, which is why the Step side runs anyway.

Compiled, not kernel: every pin below is `#guard`.
-/
import Dregg2.Bridge.MinaWrapFtEval0
import Dregg2.Bridge.MinaWrapDeferred
import Dregg2.Bridge.MinaWrapChallenges
import Dregg2.Bridge.TickShifts

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Dregg2.Bridge.MinaMultiBlockConformance

open Dregg2.Bridge.MinaWrapFtEval0
open Dregg2.Bridge.MinaWrapChallenges
open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap)
open Dregg2.Bridge.MinaWrapPublicInput (DeferredWords)

/-! ## §1 — the STEP side: wire bytes in, openmina's `expand_deferred` out. -/

/-- One block's Step-side wire values, and the six words openmina's own `expand_deferred`
produced from them. ⚑ Nothing here is carried from another block. -/
structure StepBlock where
  height : Nat
  net : String
  spongeDigest : Nat
  oldChals : List (List Nat)
  ftEval1 : Nat
  pubEval : Nat × Nat
  evals : List (Nat × Nat)
  bpChals : List Nat
  betaChal : Nat
  gammaChal : Nat
  alphaChal : Nat
  zetaChal : Nat
  domainLog2 : Nat
  /-- TARGET — `expand_deferred`'s `combined_inner_product` (unshifted). -/
  tCip : Nat
  /-- TARGET — `b`. -/
  tB : Nat
  /-- TARGET — `zeta_to_srs_length`. -/
  tZsrs : Nat
  /-- TARGET — `zeta_to_domain_size`. -/
  tZdom : Nat
  /-- TARGET — `perm`. -/
  tPerm : Nat
  /-- TARGET — `xi`. -/
  tXi : Nat

/-- The block as `MinaWrapDeferred` wants it. -/
def evalsOf (b : StepBlock) : Dregg2.Bridge.MinaWrapDeferred.WrapEvals :=
  { spongeDigest := b.spongeDigest, oldChals := b.oldChals, ftEval1 := b.ftEval1
    pubEval := b.pubEval, evals := b.evals, bpChals := b.bpChals
    betaChal := b.betaChal, gammaChal := b.gammaChal, alphaChal := b.alphaChal
    zetaChal := b.zetaChal, domainLog2 := b.domainLog2 }

/-- The block's Step side as `MinaWrapFtEval0` wants it.

⚑ **`sh` READS THE BLOCK'S OWN `domainLog2`.** `MinaWrapFtEval0Weld.TICK_SHIFTS` is
`tickShiftsFp 16` — a literal that happens to be right for every devnet blockchain proof. Here the
shifts are derived at the domain the block's own `branch_data` declares, so the weld cannot pass by
a coincidence between two 16s. -/
def stepWire (b : StepBlock) : SideWire pN :=
  { log2n := b.domainLog2
    alphaChal := b.alphaChal, betaChal := b.betaChal
    gammaChal := b.gammaChal, zetaChal := b.zetaChal
    ez := b.evals.map (fun p => ((p.1 : ZMod pN)))
    ew := b.evals.map (fun p => ((p.2 : ZMod pN)))
    pZeta := ((b.pubEval.1 : Nat) : ZMod pN)
    er := ((Dregg2.Bridge.MinaWrapDeferred.ENDO : Nat) : ZMod pN)
    endo := Dregg2.Bridge.TickShifts.stepEndoCoefficient
    sh := Dregg2.Bridge.TickShifts.tickShiftsFp b.domainLog2
    mds9 := (Dregg2.Circuit.Emit.PastaPoseidon.mdsN.flatten).map (fun x => (x : ZMod pN)) }

/-- `ft_eval0`, DERIVED from the block's own bytes — the gate linearization over all six bodies
plus the C5 fold. `none` is a refusal, and a refusal fails the conformance predicate below. -/
def stepFtEval0 (b : StepBlock) : Option Nat :=
  (deriveSide (stepWire b)).map (fun o => o.ftEval0.val)

/-- The six deferred words, from the derived `ft_eval0` and the block's own wire. -/
def stepWords (b : StepBlock) : Option DeferredWords :=
  (stepFtEval0 b).map (Dregg2.Bridge.MinaWrapDeferred.expandDeferred (evalsOf b))

/-- ⚑⚑ **THE STEP-SIDE CONFORMANCE PREDICATE.** Six independent targets, all from openmina, none
of them a value this tree carried in. -/
def stepAgrees (b : StepBlock) : Bool :=
  Dregg2.Bridge.MinaWrapDeferred.wrapEvalsOk (evalsOf b) &&
  match stepWords b with
  | some d => d.cip == b.tCip && d.b == b.tB && d.zetaToSrsLength == b.tZsrs
              && d.zetaToDomainSize == b.tZdom && d.perm == b.tPerm && d.xi == b.tXi
  | none => false

/-! ### §1b — the EMITTED CIRCUIT PROGRAM on every fixture lives NEXT DOOR, deliberately.

`Dregg2.Bridge.StepMainFtEval0RealBlock` §5 sweeps `STEP_BLOCKS` below through
`KimchiStepMain.ftProgOf` — the straight-line program whose slots BECOME `r6_ft_eval0`'s `Generic`
rows. That sweep is not here because it would drag `KimchiStepMain` (the largest emit module in the
tree, and one under active edit) into THIS module's import closure, and this module is the one that
must stay independently checkable in seconds. The rooted aggregate `Dregg2.MinaBridgeGuards` pulls
both, so `lake build` runs both regardless. -/

/-! ## §2 — the WRAP side: the Fq transcript, the IPA challenges, `p(ζ)`, `ft_eval0`, `LCT`. -/

/-- One block's Wrap-side wire values and openmina's own answers. Only blocks that
`kimchi::verifier::verify` ACCEPTED appear here. -/
structure WrapBlock where
  height : Nat
  vkDigest : Nat
  prevComm : List Nat
  pubComm : List Nat
  wComm : List Nat
  zComm : List Nat
  tComm : List Nat
  endoR : Nat
  cipShifted : Nat
  lr : List (List Nat)
  delta : List Nat
  ez : List Nat
  ew : List Nat
  publicInput : List Nat
  shift : List Nat
  log2n : Nat
  tBeta : Nat
  tGamma : Nat
  tAlphaChal : Nat
  tZetaChal : Nat
  tFqDigest : Nat
  tT : Nat
  tPrechals : List Nat
  tCPre : Nat
  tPZeta : Nat
  tFt0 : Nat
  tLct : Nat
  /-- `MinaWrapGroupGate.SIGMA6`, flat — claimed VK CONFIG. §4c measures whether it is. -/
  sigma6 : List Nat
  /-- `MinaWrapGroupGate.FT_COMM_GOLD` — claimed per-BLOCK. §4c measures whether it is. -/
  ftCommGold : Nat × Nat
  /-- The 40 SRS Lagrange commitments, flat — `MinaStepPrevCommitments.LAGRANGE_XY`. -/
  lagrange : List Nat

/-- Phase 1 of the block's Fq-sponge, from its own absorbed coordinates. -/
def wp1 (b : WrapBlock) : Phase1 :=
  wrapPhase1Of b.vkDigest b.prevComm b.pubComm b.wComm b.zComm b.tComm

/-- The 15 IPA prechallenges, continuing the SAME sponge state. -/
def wipa (b : WrapBlock) : IpaChallenges :=
  ipaChallengesOf (wp1 b).st b.cipShifted b.lr b.delta

/-- The Wrap side as `MinaWrapFtEval0` wants it. ⚑ The four challenges are NOT fixture fields —
they are what §2's own phase-1 sponge produced, so the two welds are chained on real data. -/
def wrapWire (b : WrapBlock) : SideWire qN :=
  { log2n := b.log2n
    alphaChal := (wp1 b).alphaChal, betaChal := (wp1 b).beta
    gammaChal := (wp1 b).gamma, zetaChal := (wp1 b).zetaChal
    ez := b.ez.map (fun x => (x : ZMod qN))
    ew := b.ew.map (fun x => (x : ZMod qN))
    pZeta := ((b.tPZeta : Nat) : ZMod qN)
    er := ((b.endoR : Nat) : ZMod qN)
    endo := powFast ((5 : Nat) : ZMod qN) ((qN - 1) / 3)
    sh := b.shift.map (fun x => (x : ZMod qN))
    mds9 := ((Dregg2.Circuit.Emit.PastaPoseidonFq.mdsQ).flatten).map (fun x => (x : ZMod qN)) }

/-- `p(ζ)` recomputed from the forty public-input words at the block's own ζ. -/
def wrapPZeta (b : WrapBlock) : Option (ZMod qN) :=
  publicEvalAt (2 ^ b.log2n) (rootOfUnity qN b.log2n)
    (endoMap ((b.endoR : Nat) : ZMod qN) (wp1 b).zetaChal)
    (b.publicInput.map (fun x => (x : ZMod qN)))

/-- ⚑⚑ **THE WRAP-SIDE CONFORMANCE PREDICATE.** Eleven independent targets: five phase-1
challenges, `t`, the fifteen IPA prechallenges, `c′`, `p(ζ)`, `ft_eval0` and the linearization
constant term. -/
def wrapAgrees (b : WrapBlock) : Bool :=
  phase1WireOk b.prevComm b.pubComm b.wComm b.zComm b.tComm &&
  openingWireOk b.lr b.delta &&
  (wp1 b).beta == b.tBeta && (wp1 b).gamma == b.tGamma &&
  (wp1 b).alphaChal == b.tAlphaChal && (wp1 b).zetaChal == b.tZetaChal &&
  (wp1 b).fqDigest == b.tFqDigest &&
  (wipa b).t == b.tT && (wipa b).prechals == b.tPrechals && (wipa b).cPre == b.tCPre &&
  wrapPZeta b == some ((b.tPZeta : Nat) : ZMod qN) &&
  (match deriveSide (wrapWire b) with
   | some o => o.ftEval0.val == b.tFt0 && o.linConstTerm.val == b.tLct
   | none => false)
'''


def render(records, lean_path):
    steps = [r for r in records]
    wraps = [r for r in records if "wrap" in r]
    out = [HEADER]
    out.append("\n/-! ## §3 — the fixtures. -/\n")
    out.append("/-- Every fixture's Step side. -/\ndef STEP_BLOCKS : List StepBlock :=\n [\n")
    out.append(",\n".join(step_record(r) for r in steps))
    out.append("\n ]\n")
    out.append(
        "\n/-- Every fixture whose Wrap proof `kimchi::verifier::verify` ACCEPTED. -/\n"
        "def WRAP_BLOCKS : List WrapBlock :=\n [\n"
    )
    out.append(",\n".join(wrap_record(r) for r in wraps))
    out.append("\n ]\n")

    prov = "\n".join(
        f"  * **{r['network']} {r['height']}** (`{r['state_hash']}`)"
        f" — {r['n_user_commands']} user cmds, {r['n_zkapp_commands']} zkApp cmds,"
        f" {r['n_snark_jobs']} snark jobs;"
        f" {'FULL gate (verify=Ok) + Wrap side' if 'wrap' in r else 'STEP side only'}"
        for r in records
    )
    out.append(
        f"""
/-! ## §4 — ⚑⚑ THE RESULT.

The fixtures, and what each one carries:

{prov}
-/

#guard STEP_BLOCKS.length == {len(steps)}
#guard WRAP_BLOCKS.length == {len(wraps)}

/- Every fixture is a DIFFERENT block: no duplicate heights, and no two share a ζ′. -/
#guard (STEP_BLOCKS.map (·.height)).dedup.length == {len(steps)}
#guard (STEP_BLOCKS.map (·.zetaChal)).dedup.length == {len(steps)}

/- ⚑⚑ **THE STEP SIDE CONFORMS ON EVERY FIXTURE.** `deriveSide` (the six-body gate linearization
plus the C5 fold, at the block's OWN domain and its own derived coset shifts) followed by
`expandDeferred` (the `Fr` sponge over 91 absorbed elements, the b-polynomial fold, the permutation
scalar, both ζ powers and the 47-leg `combined_inner_product` fold) reproduces all six of
openmina's `expand_deferred` words, on each block, from that block's own bytes. -/
#guard STEP_BLOCKS.all stepAgrees

"""
    )
    for r in steps:
        out.append(f"#guard match STEP_BLOCKS.find? (·.height == {r['height']}) with"
                   f" | some b => stepAgrees b | none => false\n")

    out.append(
        """
/- ⚑⚑ **THE WRAP SIDE CONFORMS ON EVERY FULLY-VERIFIED FIXTURE.** The Fq phase-1 sponge over the
block's own absorbed coordinates, the fifteen IPA prechallenges continuing that same sponge state,
`p(ζ)` over the forty public-input words, and `ft_eval0` + the linearization constant term. -/
#guard WRAP_BLOCKS.all wrapAgrees
"""
    )
    for r in wraps:
        out.append(f"#guard match WRAP_BLOCKS.find? (·.height == {r['height']}) with"
                   f" | some b => wrapAgrees b | none => false\n")

    out.append(
        """
/-! ### §4b — ⚑ THE RED PATH. A conformance check that cannot go red is not a check.

Each control bends ONE input of ONE fixture and requires the predicate to REFUSE. Without these,
`all stepAgrees` is compatible with a predicate that accepts everything. -/

/-- The first fixture, whichever it is. -/
def B0 : StepBlock := STEP_BLOCKS.headD
  { height := 0, net := "", spongeDigest := 0, oldChals := [], ftEval1 := 0, pubEval := (0,0)
    evals := [], bpChals := [], betaChal := 0, gammaChal := 0, alphaChal := 0, zetaChal := 0
    domainLog2 := 0, tCip := 0, tB := 0, tZsrs := 0, tZdom := 0, tPerm := 0, tXi := 0 }

/- The sponge seed is read. -/
#guard !(stepAgrees { B0 with spongeDigest := B0.spongeDigest + 1 })
/- The last of the 43 columns is read — a fold that stopped early passes every earlier control. -/
#guard !(stepAgrees { B0 with evals := B0.evals.set 42 (0, 0) })
/- β, γ and α are read in three distinct roles by `perm`. -/
#guard !(stepAgrees { B0 with betaChal := B0.betaChal + 1 })
#guard !(stepAgrees { B0 with gammaChal := B0.gammaChal + 1 })
#guard !(stepAgrees { B0 with alphaChal := B0.alphaChal + 1 })
/- ⚑ The DOMAIN is read — and by BOTH the shifts and `zeta_to_domain_size`, which is what makes
`sh := tickShiftsFp b.domainLog2` a real reading of the block rather than a constant 16. -/
#guard !(stepAgrees { B0 with domainLog2 := 15 })
/- The bulletproof challenges are read, first and last. -/
#guard !(stepAgrees { B0 with bpChals := B0.bpChals.set 0 0 })
#guard !(stepAgrees { B0 with bpChals := B0.bpChals.set 15 0 })
/- The coefficient column and the sigma column are read by the gate linearization. -/
#guard !(stepAgrees { B0 with evals := B0.evals.set 37 (0, 0) })
#guard !(stepAgrees { B0 with evals := B0.evals.set 22 (0, 0) })
/- ⚑ AND ONE FIXTURE'S TARGETS DO NOT SATISFY ANOTHER FIXTURE'S WIRE. This is the control that
says the six equalities are about THIS block: swapping in a sibling block's expected words must
refuse. Without it, a target that were somehow constant across blocks would pass unnoticed. -/
#guard match STEP_BLOCKS with
       | b0 :: b1 :: _ => !(stepAgrees { b0 with tCip := b1.tCip, tB := b1.tB, tXi := b1.tXi })
       | _ => false

/-- The first fully-verified fixture. -/
def W0 : WrapBlock := WRAP_BLOCKS.headD
  { height := 0, vkDigest := 0, prevComm := [], pubComm := [], wComm := [], zComm := []
    tComm := [], endoR := 0, cipShifted := 0, lr := [], delta := [], ez := [], ew := []
    publicInput := [], shift := [], log2n := 0, tBeta := 0, tGamma := 0, tAlphaChal := 0
    tZetaChal := 0, tFqDigest := 0, tT := 0, tPrechals := [], tCPre := 0, tPZeta := 0
    tFt0 := 0, tLct := 0, sigma6 := [], ftCommGold := (0, 0), lagrange := [] }

/- The VK digest is the FIRST absorb — the trusted-config argument, so the one whose silence would
be most expensive. -/
#guard !(wrapAgrees { W0 with vkDigest := W0.vkDigest + 1 })
/- A public-commitment coordinate. -/
#guard !(wrapAgrees { W0 with pubComm := W0.pubComm.set 0 0 })
/- The LAST witness-commitment coordinate. -/
#guard !(wrapAgrees { W0 with wComm := W0.wComm.set 29 0 })
/- An IPA round point, and `delta`, which is absorbed after the rounds. -/
#guard !(wrapAgrees { W0 with lr := W0.lr.set 14 ((W0.lr.getD 14 []).set 3 0) })
#guard !(wrapAgrees { W0 with delta := W0.delta.set 0 0 })
/- A public-input word — the leg that connects the Step side's forty words to `p(ζ)`. -/
#guard !(wrapAgrees { W0 with publicInput := W0.publicInput.set 12 0 })
/- A coset shift, and an evaluation column: both feed `ft_eval0`. -/
#guard !(wrapAgrees { W0 with shift := W0.shift.set 1 0 })
#guard !(wrapAgrees { W0 with ez := W0.ez.set 37 0 })
/- ⚑ …and a sibling block's expected challenges do not satisfy this block's tape. -/
#guard match WRAP_BLOCKS with
       | w0 :: w1 :: _ => !(wrapAgrees { w0 with tBeta := w1.tBeta, tFqDigest := w1.tFqDigest })
       | _ => false

/-! ### §4c — ⚑ WHAT THE FIXTURE SET MEASURES ABOUT THE 539508-ONLY CLAIMS.

Three claims in the single-block welds are properties of ONE block's numbers rather than of the
protocol. They are re-measured here across the whole fixture set. -/

/- `MinaWrapPublicInput.the_two_zeta_powers_coincide_and_only_they_do` observes that public-input
slots 2 and 3 hold one value. It holds on EVERY fixture — because `zeta_to_srs_length` uses the
constant `srs_length_log2 = 16` and `zeta_to_domain_size` uses `branch_data.domain_log2`, which is
16 on every devnet blockchain proof. ⚑ So the coincidence is STRUCTURAL for this proof family, not
a 539508 accident — and correspondingly NO block-proof fixture can discriminate the two legs. The
`domainLog2 := 15` control in §4b is the only thing that does. -/
#guard STEP_BLOCKS.all (fun b => b.tZsrs == b.tZdom)

/- ⚑ …and on the WRAP side they do NOT coincide, on every fixture: the Wrap domain is `2^14` and
`max_poly_size` is `2^15`. Recorded here as the measurement that the two exponents are genuinely
distinct objects, which is what makes a `log2n = srs_length_log2` assembly wrong rather than
merely lucky. -/
#guard WRAP_BLOCKS.all (fun b => b.log2n == 14)

/- `MinaWrapPublicInput.the_width_signature_partitions_the_slots` asserts every FIELD slot is
`≥ 2^128` on 539508's data. That is a probabilistic property of one block's numbers stated as an
instrument. It holds on every fixture too — so the instrument is at least not 539508-specific. -/
#guard WRAP_BLOCKS.all (fun b =>
  [0, 1, 2, 3, 4, 10, 11, 12].all (fun i => 2 ^ 128 ≤ b.publicInput.getD i 0))
#guard WRAP_BLOCKS.all (fun b =>
  ([5, 6, 7, 8, 9] ++ (List.range 16).map (fun j => 13 + j)).all
    (fun i => b.publicInput.getD i 0 < 2 ^ 128))

/- `branch_data` packs to slot 29 as `pvBits 3 + 4 · domain_log2` on every fixture — so the
reading `Index.to_bits N2 = [1,1] = 3` that `MinaWrapPublicInput` flagged as "a stated reading, not
a measurement" is now measured on every block in the set. ⚠ Every one of them is `N2`; a `N1`
branch remains unexercised and unmeasured. -/
#guard WRAP_BLOCKS.all (fun b => b.publicInput.getD 29 0 == 3 + 4 * 16)

/-- Every pair of DISTINCT slots below 30 that hold the same value. -/
def coincidingPairs (pi : List Nat) : List (Nat × Nat) :=
  (List.range 30).flatMap (fun i => (List.range 30).filterMap (fun j =>
    if i < j && pi.getD i 0 == pi.getD j 0 then some (i, j) else none))

/- ⚑ `MinaWrapPublicInput.the_two_zeta_powers_coincide_and_only_they_do` quantifies over ONE
block's numbers: a different block could carry an incidental SECOND coinciding pair and make the
"only they do" half false for an unrelated reason. Measured here on every fixture: `(2,3)` is the
only pair on all of them. So the theorem is not a 539508 accident. -/
#guard WRAP_BLOCKS.all (fun b => coincidingPairs b.publicInput == [(2, 3)])

/-! ### §4d — ⚑ WHICH GROUP-SIDE GOLDS ARE **CONFIG** AND WHICH ARE **BLOCK DATA**.

`MinaStepPrevCommitments` and `MinaWrapGroupGate` carry a pile of points extracted from ONE block,
and nothing in this tree said which of them were properties of the verifier key (so: legitimately
constant, and reusable) and which were that block's own data (so: gold that MUST move). Measured. -/

/- ⚑ **`SIGMA6` IS VERIFIER-KEY CONFIG.** Byte-identical across every fixture — so
`MinaStepPrevCommitments.INDEX_XY`'s seventh entry is a VK commitment, not one block's number. -/
#guard match WRAP_BLOCKS with
       | b0 :: rest => rest.all (fun b => b.sigma6 == b0.sigma6)
       | [] => false

/- ⚑ …and so are the forty SRS Lagrange commitments (`MinaStepPrevCommitments.LAGRANGE_XY`). -/
#guard match WRAP_BLOCKS with
       | b0 :: rest => rest.all (fun b => b.lagrange == b0.lagrange)
       | [] => false
#guard WRAP_BLOCKS.all (fun b => b.lagrange.length == 80)

/- ⚑ **`FT_COMM_GOLD` IS BLOCK DATA, and it MOVES.** All fixtures disagree — which is what makes
it a gold and not a constant that could be carried across blocks. -/
#guard (WRAP_BLOCKS.map (·.ftCommGold)).dedup.length == WRAP_BLOCKS.length

/- `MinaStepPrevCommitments` §5's distinctness and magnitude guards are properties of one block's
POINTS. Re-measured over each fixture's own 40 Lagrange + 15 `lr` pairs: the x-coordinates are
pairwise distinct and all exceed `2^200`. Still probabilistic — but no longer about one block. -/
#guard WRAP_BLOCKS.all (fun b =>
  let xs := (List.range 40).map (fun k => b.lagrange.getD (2 * k) 0)
            ++ b.lr.flatMap (fun r => [r.getD 0 0, r.getD 2 0])
  xs.dedup.length == 70 && xs.all (fun x => 2 ^ 200 < x))

end Dregg2.Bridge.MinaMultiBlockConformance
"""
    )
    with open(lean_path, "w") as f:
        f.write("".join(out))
    print(f"wrote {lean_path}: {len(steps)} step fixtures, {len(wraps)} wrap fixtures")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fixtures", required=True, help="directory of block fixtures")
    ap.add_argument("--fixture", action="append", default=[],
                    help="an EXTRA fixture path (block 539508 lives at its historical path)")
    ap.add_argument("--out-dir", required=True)
    ap.add_argument("--lean", required=True)
    a = ap.parse_args()
    files = sorted(
        os.path.join(a.fixtures, f) for f in os.listdir(a.fixtures) if f.endswith(".json")
    ) + list(a.fixture)
    if not files:
        fail(f"no fixtures in {a.fixtures}")
    records = sorted(
        (collect(p, a.out_dir) for p in files), key=lambda r: (r["network"], r["height"])
    )
    for r in records:
        print(
            f"  {r['base']:>18}  walk-ok  domain_log2={r['walk']['branch_domain_log2']} "
            f"pv={r['walk']['branch_proofs_verified']}  "
            f"{'WRAP+STEP' if 'wrap' in r else 'STEP only'}"
        )
    render(records, a.lean)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
