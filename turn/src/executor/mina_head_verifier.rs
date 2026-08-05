//! ⚑ **THE MINA→DREGG LANDING.** A dregg state transition whose acceptance DEPENDS on a verified
//! Mina anchored head — the half of the braid that previously verified into a void.
//!
//! # What was missing (measured 2026-08-02, by search)
//!
//! dregg's Mina→dregg direction is the strong one: it decodes real p2p binprot
//! (`Dregg2/Bridge/MinaBinprot.lean`), reproduces challenges / deferred values / `ft_eval0` /
//! `p(ζ)` / `ft_comm`, runs Samasika fork choice (`Dregg2/Bridge/MinaForkChoiceGate.lean`), and is
//! conformance-checked across 7 blocks on 2 networks. **None of it reached dregg state.**
//! Specifically:
//!
//! * `bridge/src/mina_head.rs`'s [`MinaVerifiedHead`] is a plain in-memory struct — three public
//!   fields, `Clone/Debug/PartialEq/Eq` only, **no `Serialize`/`Deserialize`**, and the only
//!   mutations are `self.finalized_height = …` / `self.protocol_state = …` (`:393-396`). There is
//!   no `fs`, no store, no cell, no turn. Its `offer` / `follow_candidate_set` / `follow_once`
//!   have **no non-test caller in the repo**, and there is **no production `impl
//!   MinaForkChoiceGate`** at all — only the test doubles `ScriptedGate` / `AbsentGate` /
//!   `CountingGate`.
//! * **ABSENT**: no variant of `turn::action::Effect` (36 variants) or
//!   `dregg_circuit::effect_vm::Effect` (29) carries a Mina verification result, a Mina state hash,
//!   a protocol-state blob or a finalized height. Every `Mina` string in `turn/`, `cell/`,
//!   `circuit/` is a doc-comment analogy ("analogous to Mina's AccountUpdate").
//! * The nearest prior art, `Effect::BridgeMint`, checks its `UntrustedRoot` against
//!   `trusted_federation_roots: Vec<AttestedRoot>` — and an `AttestedRoot` is entirely
//!   dregg-internal (blocklace block id, Cordial Miners round, federation quorum). It is **another
//!   dregg federation**, not an external chain, and its only setter caller in the repo is a test.
//!   So there was no existing "a dregg effect consumes an external chain's state" to mirror.
//!
//! # What this module is
//!
//! The consumer side of `metatheory/Dregg2/Circuit/Emit/LightClientMinaAir.lean`'s
//! `minaLcVerifyDesc` — the Lean-COMPILED (`EffectLower.lowerAir`) Mina anchored-head verify AIR,
//! served as [`MINA_LC_VERIFY_DESCRIPTOR`]. [`MinaAnchoredHeadStarkVerifier`] is a
//! `WitnessedPredicateVerifier` registered under the fixed vk [`mina_head_predicate_vk`], so a cell
//! program carrying
//!
//! ```text
//! StateConstraint::Witnessed { wp: WitnessedPredicate::custom(
//!     mina_head_predicate_vk(),
//!     /* commitment */ <the operator-pinned Mina WS anchor state hash>,
//!     /* input_ref  */ InputRef::Slot { index: <the slot that records the verified tip> },
//!     /* proof_idx  */ i) }
//! ```
//!
//! is **REFUSED** unless the proof verifies. The refusal is not advisory and not off-chain: it is
//! `cell/src/program/eval.rs:1906-1911` (`registry.verify(...)` →
//! `ProgramError::WitnessedPredicateRejected`) surfacing at
//! `turn/src/executor/execute_tree.rs:1206-1212` as `TurnError::ProgramViolation`, which aborts the
//! turn. A vk with no registered verifier is `KindNotRegistered` — also a rejection. Fail-closed
//! at every seam.
//!
//! ⚑ **VERB DISCIPLINE.** This verifier does NOT "record the verification". It **refuses the state
//! transition unless the Mina verification predicate holds** — and the thing the turn writes is the
//! thing the proof is about, because the descriptor's public inputs ARE the recorded triple.
//!
//! # The four refusals, and why each is load-bearing rather than decorative
//!
//! 1. **The pinned anchor is not prover-chosen.** `commitment` comes from the CELL PROGRAM (the
//!    authoritative pre-state the executor hands the evaluator), never from the action. PI slots
//!    0..8 must be exactly `Faithful9::from_key_lanes9(commitment)`. A proof about a head anchored
//!    somewhere else is REFUSED. This matters precisely because the AIR itself cannot tell two
//!    `k`-deep segments under different anchors apart — the anchor is the trust root, and here it
//!    is state, not testimony.
//! 2. **The recorded tip is the proved tip.** PI slots 9..17 must be exactly
//!    `Faithful9::from_key_lanes9(<the resolved input slot>)`. So the cell field the turn writes IS
//!    the state hash the proof verified; a turn that proves head A and records head B is REFUSED.
//! 3. **The depth policy is floored.** PI 19 (the Samasika `k` the acceptance met) must be at least
//!    [`MINA_MIN_CONFIRMATION_DEPTH`] = 290, Mina mainnet's `k`. A prover cannot discharge a
//!    290-deep policy with a proof that met `k = 1`.
//! 4. ⚑ **The declared sub-proof is the one presented.** [`check_transcript_binding`]: the head
//!    proof's PI slots 20..28 must be the nine `Faithful9` lanes of
//!    [`chainlink_pi_commitment`] of the supplied Fq-transcript public inputs. A head proof that
//!    names sub-proof A and hands over sub-proof B is REFUSED.
//! 5. ⚑⚑ **THE SUB-PROOF ITSELF IS VERIFIED.** `descriptor_by_name(MINA_CHAINLINK_DESCRIPTOR)`
//!    (fail-closed `None`) → `verify_vm_descriptor2` over its 256 public inputs. **This is the step
//!    that makes the carrier a proof rather than a bit** — see the section below.
//! 5b. ⚑⚑ **AND THE HEAD DESCRIPTOR'S PROGRAM PIN NAMES THAT SUB-PROOF.**
//!    [`check_subproof_program_pin`] recomputes the dispatched sub-proof descriptor's semantic
//!    fingerprint and requires the head descriptor's `vk_pin` cells to be its nine `Faithful9`
//!    lanes. Until 2026-08-05 that agreement was asserted only by a test, and it had already gone
//!    RED and stayed red — the head pinned `[460719650, …]` while the served sub-proof
//!    fingerprinted to `[172082222, …]`, so the bind named a program no descriptor in this tree
//!    has. A drift is now a refused head, not a red nobody read.
//! 6. **The STARK.** `descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR)` (fail-closed `None` on a miss)
//!    → `verify_vm_descriptor2` over all 30 public inputs. The descriptor's own gates then force
//!    `BLOCK_LEN = ANCHOR_H + SEG_LEN` and `WIT_DEPTH + SUBMIT_H = BLOCK_LEN` — the published
//!    `blockchain_length` is DERIVED from the pinned anchor plus the exhibited segment, so the one
//!    field a truncated peer reply leaves standing is not settable — plus the three ranged slack
//!    teeth, the carrier bits, and ⚑ the nine `proof_bind` congruences that force the row's attested
//!    program to be `MINA_CHAINLINK_DESCRIPTOR`'s fingerprint, lane by lane.
//!
//! # ⚑⚑ 2026-08-05 — `PICKLES_OK` STOPPED BEING ONE THING, AND SAY EXACTLY WHICH HALF MOVED
//!
//! Until this change the descriptor published `PICKLES_OK`: a witnessed boolean forced `= 1`, with
//! **nothing in any circuit computing it**. The honest sentence in this tree was *"dregg does not
//! verify Mina's proof; it accepts a boolean saying someone did."*
//!
//! That column is now two:
//!
//! * **`PICKLES_WITNESSED`** — the residue, and STILL A BIT. It is renamed, not repaired: an in-AIR
//!   Pickles verification is ≈10⁹ BabyBear constraints (`LightClientMinaAir` §1b), which is a
//!   recursion problem and not a bigger circuit. Anyone reading `PICKLES_OK` as "checked" was
//!   reading a name; the name no longer says that.
//! * ⚑ **`WRAP_FS_PROVED`** — NOT a bit. Its `= 1` guards nine `proof_bind` constraints that pin the
//!   row's attested program to `dregg-pasta-fq-chainlink::v1`'s semantic fingerprint lane by lane
//!   (nine `Faithful9` lanes, 256 bits — a single-felt tie would be worth `2^31`, below this repo's
//!   bar), and PI-bind the sub-proof's public-input commitment. **A prover cannot satisfy it without
//!   holding a second dregg STARK that this verifier then runs.**
//!
//! **What that sub-proof establishes, precisely — and it is narrower than "Mina's proof is valid":**
//! the final absorption of a phase-2 (`fq_kimchi`-over-Fq) Kimchi transcript — from the incoming
//! three-lane sponge state its public inputs pin, absorbing the one element they pin, permuted once
//! through the 55 `fq_kimchi` rounds whose constants are CELLS of that descriptor — lands on the
//! **three** output lanes they pin. On the fixture instance those pins are **Mina devnet block
//! 539508's own 46th and last link**, and outgoing lanes 0 and 1's low 128 bits ARE the `v′`/`u′`
//! that block's `proof.oracles(…)` returned, machine-checked in Lean against a tape read from a
//! proof o1-labs' `kimchi::verifier::verify::<Pallas, …>` accepts.
//!
//! ⚑ **THE THIRD LANE IS WHY THIS RUNG WAS RE-POINTED ON 2026-08-05.** It used to bind
//! `dregg-pasta-fq-wraplink::v1`, whose seven pin blocks publish two of a Poseidon state's three
//! outgoing lanes. Same program, fewer pins — and the consequence was in refusal 10, where the
//! 46-link fold root's 96-limb outgoing state was compared against 64 pinned limbs and the third
//! lane against nothing. `dregg-pasta-fq-chainlink::v1` publishes all three (256 PIs), and it is the
//! descriptor the fold's leaves are actually proven over, so the weld is now whole-state and about
//! the same object.
//!
//! **What it does NOT establish — three things, each with its number:**
//! 1. **Not Pickles validity.** The IPA opening is not in circuit at all, and
//!    `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free` shows a free `sg` makes the closing
//!    check accept at every value. That conjunct is `PICKLES_WITNESSED` and it is testimony.
//! 2. **Not that the transcript is THIS head's.** The 45 upstream permutations that determine the
//!    pinned incoming state are the sub-proof's PUBLIC INPUTS, not its gates (74 250 further rows
//!    ≈ 203 MB of witness), and no gate of the head descriptor relates `TIP_STATE` to the sub-proof
//!    commitment — the two are published side by side. So a prover must exhibit a real Fq-transcript
//!    proof, but nothing in-circuit forces it to be the right block's.
//!    ⚑ **NARROWED 2026-08-05, AND SAY WHICH HALF.** The 46-instance chain this note called "the
//!    next rung" is built (`circuit-prove/src/mina_phase2_chain_leaf.rs`) and refusals 7-10 make
//!    this verifier consume its root: the sub-proof's pinned incoming state is no longer a free
//!    prover choice, because the root's whole outgoing sponge state must equal the sub-proof's
//!    pinned outgoing block and the root's incoming state must be `(0,0,0)`. **What is still open is
//!    the Fp phase-1 leg that ties `fq_digest` to the protocol state** — until that lands, the chain
//!    is anchored at a fresh sponge and at a tape commitment, but not at THIS head.
//! 3. **Not the accumulator.** `bridge/examples/mina_accumulator_discharge.rs` discharges it
//!    NATIVELY over 7 real block proofs (27.4 s batched, a forged `sg` refused in each of 7 slots);
//!    it is not part of this bind.
//!
//! ⚠ **THE REBUILT-CLAIM GAP IS INHERITED, and here is the form it takes.** The native accumulator
//! oracle has a known nasty control: a claim REBUILT around tampered challenges still accepts,
//! because the relation binds the *pair*. The in-circuit analogue here is exact and worse-sounding
//! stated plainly: the sub-proof pins its incoming state, absorbed element and outputs as PUBLIC
//! INPUTS, so a prover who recomputes a CONSISTENT quadruple — any state, any element, the genuine
//! permutation of them — produces a verifying sub-proof. What the descriptor refuses is an
//! INCONSISTENT one (a tampered absorbed element against unchanged output pins is refused by the
//! boundary pin; a prover-chosen round constant by the ROM bus; a reordered permutation by the pc
//! thread). What ties the quadruple to a particular block is the CONSUMER pinning those public
//! inputs to a block it independently derived them from — which this verifier does **not** yet do,
//! and that is residual (2) above, not a hidden assumption.
//!
//! # Named residuals — do NOT read past these
//!
//! * **The lane↔bytes EQUALITY is checked HERE; the lane WIDTHS are checked in the AIR.**
//!   ⚑ NARROWED 2026-08-03. `minaLcVerifyDesc` now range-checks all eighteen lane columns — eight
//!   low lanes `< 2^29` per hash plus the ninth `< 2^22` — so a nonet that is not a canonical Pasta
//!   field element has no satisfying witness. What is still an EXECUTOR check is the equality to a
//!   specific 32-byte value: injectivity comes from [`Faithful9::from_key_lanes9`] (Lean
//!   `keyToLanes9`: nine base-`2^29` lanes, `8·29+24 = 256` exactly, machine-checked left inverse)
//!   and the comparison is made below. That is a real refusal — the turn dies — but a proof
//!   consumed by any OTHER route would get the widths and not the equality.
//! * **`LINK_OK` and `PICKLES_WITNESSED` are witnessed carriers**, not re-derived in-AIR; the
//!   Pickles residue rides the undischarged IPA/FRI floor. So this refuses a bent proof word only as
//!   strongly as the witness generator is honest about those two bits. ⚑ `CANON_OK` is no longer
//!   one of them for the anchor and the tip: `LightClientMinaAir` §1a derives their canonicality
//!   from the emitted lookups (`mina_anchor_and_tip_are_canonical`), and
//!   `shifted_anchor_old_admits_new_rejects` exhibits the `+p` anchor alias that the witnessed bit
//!   admitted and the descriptor now refuses. The per-BLOCK canonicality of the exhibited segment
//!   stays witnessed — those rows are not columns of a single-row descriptor.
//! * ⚑ **A witness generator MUST fill the eighteen lane columns**, or every honest turn is UNSAT.
//!   They are the same `Faithful9` decomposition `check_head_binding` already computes.
//! * **Not fork choice.** An accepted proof says "this head sits `k`-deep above THIS pinned anchor
//!   on a parent-linked, proof-carrying segment". It does not say "and the network selected it".
//! * **Not "machine-checked", not "Mina-valid".** The dregg-side STARK inherits the undischarged
//!   FRI floor.

use std::sync::Arc;

use dregg_cell::predicate::{
    PredicateInput, WitnessedPredicateError, WitnessedPredicateKind, WitnessedPredicateVerifier,
};
use dregg_circuit::BabyBear;
use dregg_circuit::descriptor_by_name::descriptor_by_name;
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, EffectVmDescriptor2, Ir2BatchProof, verify_vm_descriptor2,
};
use dregg_circuit::descriptor_ir2_canonical::effect_vm_descriptor2_semantic_fingerprint;
use dregg_circuit::faithful9::Faithful9;

use super::mina_accumulator_oracle::{WireAccumulatorClaim, installed_mina_accumulator_oracle};

/// The Lean-COMPILED Mina anchored-head verify descriptor's `descriptor_by_name` key.
///
/// Authored as `minaLcVerifyDesc` in
/// `metatheory/Dregg2/Circuit/Emit/LightClientMinaAir.lean` — `EffectLower.lowerAir` of the
/// `EffectAir` source `minaHeadAir`, with no hand-written `VmConstraint2` (house law #1).
pub const MINA_LC_VERIFY_DESCRIPTOR: &str = "dregg-mina-lightclient-verify::v1";

/// ⚑ **THE FQ-TRANSCRIPT SUB-PROOF'S DESCRIPTOR.** Authored as `MinaPhase2Chain.chainDesc` — the
/// 2 048-instruction Kimchi `fq_kimchi` sponge program with **eight** boundary pin blocks. This node
/// VERIFIES a STARK over it before it accepts a Mina head; a dispatch miss is
/// [`WitnessedPredicateError::Rejected`], never a skip.
///
/// ⚑⚑ **FLAG DAY 2026-08-05 — THIS WAS `dregg-pasta-fq-wraplink::v1` AND THE DIFFERENCE IS A WHOLE
/// SPONGE LANE.** Both descriptors are the SAME `programAir qLimb absorbProg`
/// (`MinaPhase2Chain.the_chain_air_extends_the_program_air`); they differ only in which boundary
/// blocks they publish:
///
/// | descriptor | pin blocks | PIs | outgoing lanes exposed |
/// |---|---|---|---|
/// | `dregg-pasta-fq-wraplink::v1` | 7 (`in(3) ‖ absorbed(2) ‖ out(2)`) | 224 | **two of three** |
/// | `dregg-pasta-fq-chainlink::v1` | 8 (`in(3) ‖ out(3) ‖ absorbed(2)`) | 256 | **three of three** |
///
/// A Poseidon state is three lanes (`MinaPhase2Chain.the_outgoing_lanes_are_registers_4_5_0`). Under
/// the wraplink, [`check_chain_root_binding`]'s weld compared 64 of the fold root's 96 outgoing state
/// limbs and the third lane was compared to **nothing**; under the chainlink it is all 96. And the
/// chainlink is the descriptor the 46-leaf fold is actually built on
/// (`circuit-prove/src/mina_phase2_chain_leaf.rs`), so `WRAP_FS_PROVED` attests a permutation OF the
/// chain the root proves instead of a sibling permutation beside it.
///
/// **What re-emits:** `circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json` (the nine
/// `vk_pin` literals move to the chainlink fingerprint), and its VK — i.e. the descriptor bytes a
/// head STARK is verified against — rotates with it. A pre-flag-day head proof no longer verifies.
/// [`mina_head_predicate_vk`] is unchanged (it is a function of the HEAD descriptor's NAME, which did
/// not move), so cell programs keep their pinned vk and simply stop having old proofs accepted.
pub const MINA_CHAINLINK_DESCRIPTOR: &str = "dregg-pasta-fq-chainlink::v1";

/// Public-input arity of [`MINA_CHAINLINK_DESCRIPTOR`] — eight 32-limb pin blocks (Lean
/// `MinaPhase2Chain.CHAIN_PI_COUNT`).
pub const MINA_CHAINLINK_PI_COUNT: usize = 256;

/// Limbs per Pasta field element in a phase-2 pin block (`PastaFieldSound.SK`).
pub const PASTA_LIMBS: usize = 32;

/// ⚑ PI offset of the sub-proof's FIRST OUTGOING sponge lane. Lean `MinaPhase2Chain.chainPins` lays
/// the eight blocks out as
/// `first r0 ‖ first r1 ‖ first r2 ‖ last r4 ‖ last r5 ‖ last r0 ‖ first r3 ‖ first r4` — three
/// incoming state lanes, then the THREE lanes the permutation lands on, then the two absorbed
/// elements. So the outgoing state is slots `96..192`, contiguous, and it is exactly the 96-limb
/// `out_state` a recursion root publishes (`mina_phase2_chain_leaf::OUT_PI_LO`).
pub const CHAINLINK_OUT_LANES_LO: usize = 3 * PASTA_LIMBS;
/// Width of the sub-proof's outgoing pinned state — a WHOLE three-lane Poseidon state.
pub const CHAINLINK_OUT_LANES_WIDTH: usize = 3 * PASTA_LIMBS;

/// Domain separation for the sub-proof public-input commitment the head descriptor publishes at PI
/// slots 20..28. ⚑ Changing this string is a wire-format flag day for [`MinaHeadProofWire`] AND for
/// `LightClientMinaAir.CHAINLINK_PI_LANES`; the two are gated against each other by
/// `circuit/tests/mina_transcript_carrier_binding.rs`.
///
/// ⚑ **IT MOVED WITH THE DESCRIPTOR ON 2026-08-05** (`wraplink-` → `chainlink-`). The arity is
/// absorbed first, so a 224-PI commitment was never a prefix of a 256-PI one; the rename is the
/// other half — a commitment minted for the seven-block program cannot be re-read as one for the
/// eight-block program. There is no accepted second form.
pub const CHAINLINK_PI_COMMITMENT_CONTEXT: &str =
    "dregg.mina-lightclient.chainlink-subproof-pi-commitment.v1";

/// Number of public inputs the descriptor declares: nine pinned-anchor lanes, nine verified-tip
/// lanes, the derived `blockchain_length`, the Samasika depth met, ⚑ the nine-lane commitment
/// to the Fq-transcript sub-proof's public inputs, ⚑ and the anchor HEIGHT. Pinned to
/// `LightClientMinaAir.MINA_PI_COUNT`.
pub const MINA_LC_PI_COUNT: usize = 30;

/// Lanes per 32-byte Mina state hash (`Faithful9`).
pub const MINA_STATE_LANES: usize = 9;

/// PI slot of anchor lane `i` (`LightClientMinaAir.PI_ANCHOR_STATE`).
pub const PI_ANCHOR_STATE_BASE: usize = 0;
/// PI slot of verified-tip lane `i` (`LightClientMinaAir.PI_TIP_STATE`).
pub const PI_TIP_STATE_BASE: usize = MINA_STATE_LANES;
/// PI slot of the DERIVED `blockchain_length` (`LightClientMinaAir.PI_BLOCK_LEN`).
pub const PI_BLOCK_LEN: usize = 2 * MINA_STATE_LANES;
/// PI slot of the Samasika confirmation depth the acceptance met
/// (`LightClientMinaAir.PI_REQ_DEPTH`).
pub const PI_REQ_DEPTH: usize = 2 * MINA_STATE_LANES + 1;
/// ⚑ PI slot of sub-proof-commitment lane `i` (`LightClientMinaAir.PI_SUB_PI`), slots 20..28.
pub const PI_SUB_COMMIT_BASE: usize = 2 * MINA_STATE_LANES + 2;
/// ⚑ PI slot 29: the weak-subjectivity anchor's blockchain length
/// (`LightClientMinaAir.PI_ANCHOR_H`, col 1). **New 2026-08-05.**
///
/// Until that day `ANCHOR_H` was published by nothing — the descriptor's G1 forces
/// `BLOCK_LEN = ANCHOR_H + SEG_LEN` and only the SUM left the proof, so a prover picked the
/// summands and `minaVerify_anchor_height_is_pinned_to_nothing` was a theorem about the emitted
/// bytes. It is now PI-bound (`minaVerify_anchor_height_is_published`), and
/// [`check_anchor_binding`] is the half that makes the pin worth something: a PI pin adds no
/// in-circuit edge (`relatedCols` returns `[]` for a `piBinding`, deliberately), so the value comes
/// from a consumer refusing the published height against a height it holds independently.
pub const PI_ANCHOR_H: usize = 3 * MINA_STATE_LANES + 2;

/// Domain separation for the WEAK-SUBJECTIVITY ANCHOR commitment — see [`mina_anchor_commitment`].
pub const MINA_ANCHOR_COMMITMENT_CONTEXT: &str = "dregg.mina-lightclient.anchor-commitment.v1";

/// ⚑⚑ **THE OPERATOR'S ANCHOR IS A PAIR, AND THE COMMITMENT NOW BINDS BOTH HALVES.**
///
/// A Mina weak-subjectivity anchor is `(protocol state hash, blockchain length)`. Until 2026-08-05
/// the `WitnessedPredicate` commitment WAS the 32-byte state hash and the height existed nowhere a
/// consumer could see, so "the published height is the pinned anchor plus the exhibited segment"
/// had no second source for the word *pinned*. This binds the pair:
///
/// ```text
///     commitment = blake3_derive_key(MINA_ANCHOR_COMMITMENT_CONTEXT, state_hash ‖ height_le32)
/// ```
///
/// ⚑ **FLAG DAY.** The cell-program-visible commitment for a `MinaAnchoredHead` predicate is a
/// DIFFERENT 32 bytes than it was: a program that pinned the bare state hash no longer matches, and
/// fails as `anchor commitment mismatch` rather than being reinterpreted. Cell programs carrying a
/// Mina anchor must be re-pinned with this function; nothing else in the tree produces the old
/// shape, and there is no accepted second form.
pub fn mina_anchor_commitment(state_hash: &[u8; 32], height: u32) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(MINA_ANCHOR_COMMITMENT_CONTEXT);
    h.update(state_hash);
    h.update(&height.to_le_bytes());
    *h.finalize().as_bytes()
}

/// ⚑⚑ **THE ANCHOR REFUSAL — the exhibited anchor pair IS the cell-program-pinned one, and the
/// proof used THAT height.**
///
/// Two refusals, and they are separate on purpose:
///
/// 1. **The declared anchor is the pinned anchor.** `commitment` is cell-program state; the wire
///    carries the preimage. A prover that names any other `(hash, height)` pair fails here, which
///    is what lets refusal 2 trust `declared_height`.
/// 2. **The proof's published `ANCHOR_H` is that height.** This is the consumer half of the
///    2026-08-05 PI pin. Without it the pin publishes a number nobody compares — decoration, and
///    the descriptor's own definition is not a second source.
///
/// ⚠ **WHAT THIS STILL DOES NOT DO.** Nothing here or in the AIR says the height is the height OF
/// that state hash — `minaVerify_anchor_height_shares_no_constraint_with_the_hash` is that residual,
/// kept as a live theorem. Both halves are now refused against the SAME cell-program-pinned pair,
/// so a prover cannot mix an operator's hash with its own height; what remains open is that the
/// operator's pair is itself asserted, not derived from Mina state in-circuit.
pub fn check_anchor_binding(
    commitment: &[u8; 32],
    declared_state: &[u8; 32],
    declared_height: u32,
    pis: &[u32],
) -> Result<(), String> {
    if pis.len() != MINA_LC_PI_COUNT {
        return Err(format!(
            "Mina anchored-head proof declared {} public inputs; {MINA_LC_VERIFY_DESCRIPTOR} binds \
             exactly {MINA_LC_PI_COUNT}",
            pis.len()
        ));
    }
    let recomputed = mina_anchor_commitment(declared_state, declared_height);
    if recomputed != *commitment {
        return Err(format!(
            "anchor commitment mismatch: the wire declares a weak-subjectivity anchor at height \
             {declared_height} whose commitment is {}, but the cell program pinned {}. This proof \
             is about an anchor the program did not pin.",
            hex::encode(recomputed),
            hex::encode(commitment)
        ));
    }
    let published = pis[PI_ANCHOR_H];
    if published != declared_height {
        return Err(format!(
            "the proof published an anchor height of {published}, but the cell-program-pinned \
             anchor is at height {declared_height}: the derived `blockchain_length` was computed \
             against a different anchor than the one this consumer pinned"
        ));
    }
    Ok(())
}

/// ⚑ **THE DEPTH FLOOR.** Mina mainnet's Samasika confirmation depth `k = 290`. The descriptor
/// PUBLISHES which depth policy an acceptance met (PI 19) precisely so a consumer can refuse a
/// weaker one; without this floor a prover discharges a 290-deep requirement with a `k = 1` proof
/// and every gate in the AIR still holds.
pub const MINA_MIN_CONFIRMATION_DEPTH: u32 = 290;

const KIND_NAME: &str = "MinaAnchoredHead";

/// The fixed `Custom { vk_hash }` this verifier registers under — the domain-separated identity of
/// the Lean-authored descriptor.
///
/// A cell program names this vk in a `WitnessedPredicate`; the registry dispatches to
/// [`MinaAnchoredHeadStarkVerifier`]. An unregistered vk is `KindNotRegistered` — a REJECTION, so a
/// node built without this verifier refuses the constraint rather than waving it through.
pub fn mina_head_predicate_vk() -> [u8; 32] {
    // Domain-separated over the descriptor NAME, so the vk moves if the descriptor identity does
    // (a VK-epoch flip must not leave a stale predicate silently dispatching to a new circuit).
    let mut h = blake3::Hasher::new();
    h.update(b"dregg.witnessed-predicate.mina-anchored-head.v1\0");
    h.update(MINA_LC_VERIFY_DESCRIPTOR.as_bytes());
    *h.finalize().as_bytes()
}

/// Wire encoding of a Mina anchored-head predicate proof.
///
/// The public inputs travel as canonical `u32` BabyBear values and are CHECKED against the pinned
/// anchor / recorded tip below before the STARK runs — a prover cannot substitute its own PI vector
/// because the descriptor binds all thirty and this verifier fixes twenty-eight of them from
/// authoritative state.
/// ⚑ **FLAG DAY 2026-08-05: THIS WIRE CARRIES TWO PROOFS.** The transcript fields are REQUIRED, so a
/// pre-2026-08-05 blob fails to decode rather than being reinterpreted as "no sub-proof supplied" —
/// the refusal is at the codec, which is the only place it cannot be forgotten.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct MinaHeadProofWire {
    /// The thirty public inputs, in descriptor order.
    pub public_inputs: Vec<u32>,
    /// The IR-v2 batch proof over `MINA_LC_VERIFY_DESCRIPTOR`.
    pub proof: Ir2BatchProof<DreggStarkConfig>,
    /// ⚑ The 256 public inputs of the Fq-transcript sub-proof, in `MINA_CHAINLINK_DESCRIPTOR` order.
    pub transcript_public_inputs: Vec<u32>,
    /// ⚑ The IR-v2 batch proof over `MINA_CHAINLINK_DESCRIPTOR`. **This node verifies it.**
    pub transcript_proof: Ir2BatchProof<DreggStarkConfig>,
    /// ⚑⚑ **THE RECURSION ROOT OF THE 46-LINK PHASE-2 CHAIN**, postcard-serialised
    /// `BatchStarkProof<DreggRecursionConfig>` bytes.
    ///
    /// REQUIRED, and REQUIRED as bytes rather than a typed field on purpose: a recursion root's
    /// type lives in `dregg-recursion-verify`, and `dregg-turn` does not take that edge (see
    /// [`MinaChainRootBackend`]). Bytes here, structure there, and the seam refuses when the
    /// backend is absent.
    pub chain_root_proof: Vec<u8>,
    /// ⚑ The weak-subjectivity anchor's 32-byte protocol state hash — the PREIMAGE half of the
    /// predicate commitment. REQUIRED. See [`mina_anchor_commitment`].
    pub pinned_anchor_state: [u8; 32],
    /// ⚑ The weak-subjectivity anchor's `blockchain_length` — the other preimage half, and the
    /// value PI 29 must equal. REQUIRED.
    pub pinned_anchor_height: u32,
    /// ⚑⚑ **THE DEFERRED IPA ACCUMULATOR CLAIM THIS HEAD CARRIES.** REQUIRED, so a pre-2026-08-05
    /// blob fails to DECODE rather than being reinterpreted as "no accumulator supplied" — the
    /// refusal is at the codec, which is the only place it cannot be forgotten.
    ///
    /// This is the claim `Ipa::Step::accumulator_check` discharges upstream and that this tree
    /// discharged only in an example binary until today. See
    /// [`super::mina_accumulator_oracle`] for what the discharge establishes and what it does not.
    pub accumulator: WireAccumulatorClaim,
}

/// ⚑⚑ **THE CLAIM A MINA PHASE-2 CHAIN-FOLD ROOT PUBLISHES**, as canonical `u32` lanes.
///
/// Read end to end: *starting from the sponge state `in_state`, absorbing exactly the tape
/// `transcript_acc` commits to, a chain of `absorbProg` executions lands on `out_state`.* The
/// widths are the Lean `MinaPhase2Chain` layout: three 32-limb sponge lanes each side.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MinaChainRootClaim {
    /// 96 limbs — the sponge state the chain's FIRST link consumed.
    pub in_state: Vec<u32>,
    /// 96 limbs — the sponge state the chain's LAST link produced.
    pub out_state: Vec<u32>,
    /// The ordered commitment to every element the chain absorbed.
    pub transcript_acc: Vec<u32>,
}

/// Width of one whole three-lane sponge state in the chain claim.
pub const CHAIN_STATE_WIDTH: usize = 3 * PASTA_LIMBS;

/// ⚑ **THE WELD IS WHOLE-STATE, ASSERTED AT COMPILE TIME.** The recursion root publishes a 96-limb
/// sponge state and the chainlink sub-proof pins a 96-limb outgoing block; refusal 10 compares them
/// limb for limb. Under the seven-block wraplink these two were 96 and 64, and the loop silently
/// covered two thirds of the claim. This is the shape of that mistake made unrepresentable — a
/// future re-point that narrows the sub-proof's exposed state fails to COMPILE rather than
/// quietly leaving a lane free.
const _: () = assert!(CHAINLINK_OUT_LANES_WIDTH == CHAIN_STATE_WIDTH);
/// And the outgoing block must FIT: `96 + 96 <= 256`.
const _: () =
    assert!(CHAINLINK_OUT_LANES_LO + CHAINLINK_OUT_LANES_WIDTH <= MINA_CHAINLINK_PI_COUNT);

/// ⚑⚑ **REFUSAL 5b — THE HEAD DESCRIPTOR'S PROGRAM PIN NAMES THE SUB-PROOF THIS NODE ACTUALLY
/// VERIFIES.** Both descriptors are in hand at verify time, so this is checkable at RUNTIME, and
/// after 2026-08-05 it is checked there.
///
/// # Why this exists, with the measurement
///
/// `WRAP_FS_PROVED = 1` guards nine `proof_bind` congruences that force the head row's `SUB_VK`
/// columns to nine LITERALS baked into the head descriptor's own bytes. Whether those literals ARE
/// the served sub-proof descriptor's semantic fingerprint was, until today, asserted **only** by
/// `circuit/tests/mina_transcript_carrier_binding.rs`. And it had already stopped being true:
/// `7a4b8ab00` wrote the wraplink fingerprint into Lean correctly, `75df624cf` re-emitted
/// `pasta-fq-wraplink.json` and moved its bytes, and the literal did not follow. Measured
/// 2026-08-05 the head descriptor pinned `[460719650, 491018495, …]` while the wraplink descriptor
/// fingerprinted to `[172082222, 381973190, …]` — **the bind named a program no descriptor in this
/// tree has**, and every head this node accepted was accepted with that pin satisfied by a prover's
/// column and tied to nothing.
///
/// A pin whose only reader is a test is a pin a running node drifts past. This is the reader that
/// runs on the node. A drift is now a REFUSED HEAD, not a red test somebody has not looked at.
///
/// ⚑ **THIS IS NOT A PIN AGAINST ITS OWN DEFINITION.** The two sides are the head descriptor's
/// emitted `vk_pin` cells (from `LightClientMinaAir.CHAINLINK_VK_LANES`, through Lean) and a blake3
/// fingerprint recomputed here over the SUB-PROOF descriptor's canonical bytes. Neither is derived
/// from the other; they agree only if both artifacts were emitted from the same Lean tree.
pub fn check_subproof_program_pin(
    head_desc: &EffectVmDescriptor2,
    sub_desc: &EffectVmDescriptor2,
) -> Result<(), String> {
    let fp = effect_vm_descriptor2_semantic_fingerprint(sub_desc).map_err(|e| {
        format!(
            "the {MINA_CHAINLINK_DESCRIPTOR} descriptor has no representable semantic fingerprint \
             ({e}): this node cannot tell which program the head proof's recursion bind names"
        )
    })?;
    let expected = key_lanes_u32(&fp);

    let binds: Vec<&dregg_circuit::descriptor_ir2::ProofBindSpec> = head_desc
        .constraints
        .iter()
        .filter_map(|c| match c {
            dregg_circuit::descriptor_ir2::VmConstraint2::ProofBind(p) => Some(p),
            _ => None,
        })
        .collect();
    if binds.len() != 1 {
        return Err(format!(
            "{MINA_LC_VERIFY_DESCRIPTOR} declares {} proof_bind constraints; this consumer requires \
             exactly one (the nine-lane recursion bind). A head descriptor with a different seam \
             shape is refused rather than partially checked",
            binds.len()
        ));
    }
    let pin = binds[0].vk_pin.as_deref().ok_or_else(|| {
        format!(
            "{MINA_LC_VERIFY_DESCRIPTOR}'s recursion bind declares NO program pin (`vk_pin: None`): \
             the row's attested program would be the prover's to choose, so this node refuses the \
             head rather than verifying a sub-proof of an unnamed program"
        )
    })?;
    if pin.len() != MINA_STATE_LANES {
        return Err(format!(
            "{MINA_LC_VERIFY_DESCRIPTOR}'s recursion bind pins {} program lanes; a `Faithful9` \
             program identity is {MINA_STATE_LANES}. A prefix pin is not a pin",
            pin.len()
        ));
    }
    for (i, want) in expected.iter().enumerate() {
        if pin[i] != i64::from(*want) {
            return Err(format!(
                "{MINA_LC_VERIFY_DESCRIPTOR} pins program lane {i} at {}, but the descriptor this \
                 node dispatches for {MINA_CHAINLINK_DESCRIPTOR} fingerprints to {want}: the head \
                 descriptor's recursion bind names a DIFFERENT program than the sub-proof this node \
                 verifies. One of the two was re-emitted and the other was not — refusing the head",
                pin[i]
            ));
        }
    }
    Ok(())
}

/// ⚑⚑ **THE INJECTED RECURSION-ROOT BACKEND — the seam, and the reason `dregg-turn` still has no
/// `dregg-circuit-prove` edge.**
///
/// Verifying a recursion root needs `p3-recursion` + `p3-circuit-prover`, which `dregg-turn`
/// deliberately does not link (`turn/Cargo.toml`). So the crypto is injected: a host that WANTS
/// the capability depends on `dregg-recursion-verify` — a crate that unconditionally verifies —
/// and installs an impl. `dregg-node` does exactly that in `executor_setup.rs`.
///
/// ⚑ **THE FINGERPRINT COMPARISON IS NOT THE BACKEND'S TO MAKE.** [`verify_chain_root`] returns
/// the fingerprint it MEASURED off the proof; [`pinned_root_vk`] returns the anchor the backend
/// was constructed with; and it is [`MinaAnchoredHeadStarkVerifier::verify`] — here, in
/// `dregg-turn` — that requires them equal. A backend that simply forgot to compare therefore
/// cannot fail open, which is the whole point of splitting the trait this way rather than having
/// one `fn verify(&self, bytes) -> Result<Claim, String>` that is trusted to have checked.
///
/// [`verify_chain_root`]: MinaChainRootBackend::verify_chain_root
/// [`pinned_root_vk`]: MinaChainRootBackend::pinned_root_vk
pub trait MinaChainRootBackend: Send + Sync + std::fmt::Debug {
    /// The `recursion_vk_fingerprint` this backend's operator pinned as the trust anchor —
    /// extracted once from an honest fold. An all-zero value is REFUSED by the consumer as an
    /// unset anchor.
    fn pinned_root_vk(&self) -> [u8; 32];

    /// Verify the root and report `(measured recursion_vk_fingerprint, claim)`.
    ///
    /// MUST verify the STARK. MUST NOT decide whether the fingerprint is acceptable — report it.
    fn verify_chain_root(
        &self,
        proof_bytes: &[u8],
    ) -> Result<([u8; 32], MinaChainRootClaim), String>;
}

/// ⚑ **THE SUB-PROOF PUBLIC-INPUT COMMITMENT** the head descriptor PI-binds at slots 20..28: blake3
/// derive-key over [`CHAINLINK_PI_COMMITMENT_CONTEXT`], absorbing the arity then every public input as
/// its canonical `u32` little-endian.
///
/// The arity goes in first so a truncated PI vector is not a prefix collision — the class the
/// `mina-tip` lane was bitten by at the peer-reply boundary, one layer down.
pub fn chainlink_pi_commitment(pis: &[u32]) -> [u8; 32] {
    let mut h = blake3::Hasher::new_derive_key(CHAINLINK_PI_COMMITMENT_CONTEXT);
    h.update(&(pis.len() as u64).to_le_bytes());
    for v in pis {
        h.update(&v.to_le_bytes());
    }
    *h.finalize().as_bytes()
}

/// ⚑ **REFUSAL 4 — THE ROW'S DECLARED SUB-PROOF COMMITMENT IS THE SUPPLIED SUB-PROOF'S.**
///
/// The head descriptor's nine `proof_bind` constraints force the row's attested program to be
/// `MINA_CHAINLINK_DESCRIPTOR`'s fingerprint, and PI-bind the commitment lanes. What no row-local
/// polynomial can do is check that a sub-proof with THAT commitment exists — that is off-row by
/// construction (`DescriptorIR2` §6c). This is that check, and it is the reason the head proof's
/// carrier is not a bit: the prover must hold a second STARK whose public inputs digest to the nine
/// lanes it published.
pub fn check_transcript_binding(pis: &[u32], transcript_pis: &[u32]) -> Result<(), String> {
    // The head arity is re-checked here rather than inherited from `check_head_binding`'s earlier
    // call: this is a `pub` fail-closed check and a caller that reached it another way must get a
    // refusal, not an index panic.
    if pis.len() != MINA_LC_PI_COUNT {
        return Err(format!(
            "Mina anchored-head proof declared {} public inputs; {MINA_LC_VERIFY_DESCRIPTOR} binds \
             exactly {MINA_LC_PI_COUNT}",
            pis.len()
        ));
    }
    if transcript_pis.len() != MINA_CHAINLINK_PI_COUNT {
        return Err(format!(
            "the Fq-transcript sub-proof declared {} public inputs; \
             {MINA_CHAINLINK_DESCRIPTOR} binds exactly {MINA_CHAINLINK_PI_COUNT}",
            transcript_pis.len()
        ));
    }
    let expected = key_lanes_u32(&chainlink_pi_commitment(transcript_pis));
    for (i, want) in expected.iter().enumerate() {
        let got = pis[PI_SUB_COMMIT_BASE + i];
        if got != *want {
            return Err(format!(
                "sub-proof commitment lane {i} is {got}, but the supplied Fq-transcript sub-proof's \
                 public inputs digest to {want}: the head proof declares a DIFFERENT sub-proof than \
                 the one presented"
            ));
        }
    }
    Ok(())
}

/// The nine `Faithful9` key lanes of a 32-byte value, as canonical `u32`s — the encoding the
/// descriptor's limb PIs are expected to carry. Lean `keyToLanes9`; machine-checked injective.
pub fn key_lanes_u32(bytes: &[u8; 32]) -> [u32; MINA_STATE_LANES] {
    let lanes = Faithful9::from_key_lanes9(bytes).lanes();
    std::array::from_fn(|i| lanes[i].as_u32())
}

/// ⚑ **THE BINDING CHECK — refusals 1, 2 and 3, as a pure function of authoritative state.**
///
/// Separated from [`MinaAnchoredHeadStarkVerifier::verify`] deliberately: these three refusals are
/// the ones that make the Mina verification LOAD-BEARING for the state write rather than adjacent
/// to it, and a refusal that cannot be exhibited without minting a STARK is a refusal nobody
/// checks. The STARK leg composes on top (refusal 4).
///
/// * `pinned_anchor` — the operator's Mina weak-subjectivity anchor, read from the CELL PROGRAM.
/// * `recorded_tip`  — the 32-byte state slot this turn writes / constrains, resolved by the
///   executor from authoritative state.
/// * `pis`           — the proof's declared public inputs, in descriptor order.
///
/// `Ok(())` iff the proof speaks about THAT anchor, records THAT head, and met at least
/// [`MINA_MIN_CONFIRMATION_DEPTH`].
pub fn check_head_binding(
    pinned_anchor: &[u8; 32],
    recorded_tip: &[u8; 32],
    pis: &[u32],
) -> Result<(), String> {
    if pis.len() != MINA_LC_PI_COUNT {
        return Err(format!(
            "Mina anchored-head proof declared {} public inputs; {MINA_LC_VERIFY_DESCRIPTOR} binds \
             exactly {MINA_LC_PI_COUNT}",
            pis.len()
        ));
    }

    // ── REFUSAL 1: the pinned weak-subjectivity anchor is CELL-PROGRAM state, not testimony.
    for (i, expected) in key_lanes_u32(pinned_anchor).iter().enumerate() {
        let got = pis[PI_ANCHOR_STATE_BASE + i];
        if got != *expected {
            return Err(format!(
                "anchor lane {i} is {got}, but the cell-program-pinned Mina weak-subjectivity \
                 anchor requires {expected}: this proof is about a head anchored somewhere else"
            ));
        }
    }

    // ── REFUSAL 2: the state this turn records IS the head the proof verified.
    for (i, expected) in key_lanes_u32(recorded_tip).iter().enumerate() {
        let got = pis[PI_TIP_STATE_BASE + i];
        if got != *expected {
            return Err(format!(
                "verified-tip lane {i} is {got}, but the recorded slot requires {expected}: the \
                 turn records a different head than the one the proof verified"
            ));
        }
    }

    // ── REFUSAL 3: the Samasika depth policy the acceptance met is floored.
    let met_depth = pis[PI_REQ_DEPTH];
    if met_depth < MINA_MIN_CONFIRMATION_DEPTH {
        return Err(format!(
            "the proof met a Samasika confirmation depth of {met_depth}; this consumer requires at \
             least {MINA_MIN_CONFIRMATION_DEPTH} (Mina mainnet k)"
        ));
    }

    Ok(())
}

/// ⚑⚑ **REFUSALS 7-10 — THE RECURSION ROOT, as a pure function of the backend's report.**
///
/// Separated from the verifier for the same reason [`check_head_binding`] is: these are the
/// refusals that make a fold root LOAD-BEARING, and a refusal that cannot be exhibited without
/// minting a 17-minute fold is a refusal nobody checks.
///
/// * **7 — the anchor is set.** An all-zero `pinned` is refused. An unset anchor that compares
///   equal to a proof nobody pinned is the fail-open shape this whole seam exists to avoid.
/// * **8 — the root is a proof of the PINNED circuit.** `measured == pinned`. Without it, "the
///   root verifies" means only "*some* circuit's proof verifies".
/// * **9 — the chain started from a FRESH Kimchi sponge.** A root whose `in_state` is anything
///   else proves a sentence about a transcript prefix nobody checked — the prover picked where
///   to start.
/// * **10 ⚑⚑ THE WELD — AND SINCE 2026-08-05 IT IS THE WHOLE SPONGE STATE.** The root's 96
///   outgoing limbs ARE the sub-proof's pinned outgoing block (`chainPins`' `last r4 ‖ last r5 ‖
///   last r0`, slots 96..192). This is what ties the recursion root to the head proof already being
///   verified: the sub-proof's incoming sponge state stops being a free prover choice and becomes
///   the output of a 46-link chain that started at (0,0,0).
///
///   ⚑ **UNDER THE SEVEN-BLOCK WRAPLINK THIS COMPARED 64 OF 96 LIMBS.** A Poseidon state is three
///   lanes and `linkPins` published two, so `claim.out_state[64..96]` — the third lane — was
///   compared against nothing at all, and a prover could hand the root any value there. The
///   comparison below is unchanged in shape; what changed is that
///   [`CHAINLINK_OUT_LANES_WIDTH`] is now the full [`CHAIN_STATE_WIDTH`], so the loop covers every
///   limb of the claim rather than two thirds of it.
///
///   It is residual (2) of this module's header narrowing — **not closing**: nothing here relates
///   either object to `TIP_STATE`, which still needs the Fp phase-1 leg.
pub fn check_chain_root_binding(
    pinned: &[u8; 32],
    measured: &[u8; 32],
    claim: &MinaChainRootClaim,
    transcript_pis: &[u32],
) -> Result<(), String> {
    // ── REFUSAL 7: the anchor is set.
    if pinned == &[0u8; 32] {
        return Err(
            "the recursion-root trust anchor is all-zero: this node has no pinned \
             `recursion_vk_fingerprint` and therefore cannot tell which circuit a root proves"
                .into(),
        );
    }

    // ── REFUSAL 8: the root is a proof of THAT circuit.
    if measured != pinned {
        return Err(format!(
            "recursion root VK fingerprint is {}, but this consumer's pinned anchor is {}: the \
             root is a proof of a DIFFERENT circuit",
            hex::encode(measured),
            hex::encode(pinned)
        ));
    }

    if claim.in_state.len() != CHAIN_STATE_WIDTH || claim.out_state.len() != CHAIN_STATE_WIDTH {
        return Err(format!(
            "the recursion root's claim carries {}/{} state limbs; a Mina phase-2 chain claim is \
             {CHAIN_STATE_WIDTH} each side",
            claim.in_state.len(),
            claim.out_state.len()
        ));
    }

    // ── REFUSAL 9: the chain started from a FRESH Kimchi sponge.
    if let Some(i) = claim.in_state.iter().position(|v| *v != 0) {
        return Err(format!(
            "the recursion root's incoming sponge limb {i} is {}, not 0: the chain did not start \
             from a FRESH Kimchi sponge, so it says nothing about the whole transcript",
            claim.in_state[i]
        ));
    }

    // ── REFUSAL 10 ⚑⚑ THE WELD: the root LANDS ON the sub-proof's own outgoing lanes.
    if transcript_pis.len() != MINA_CHAINLINK_PI_COUNT {
        return Err(format!(
            "the Fq-transcript sub-proof declared {} public inputs; \
             {MINA_CHAINLINK_DESCRIPTOR} binds exactly {MINA_CHAINLINK_PI_COUNT}",
            transcript_pis.len()
        ));
    }
    let sub_out = &transcript_pis[CHAINLINK_OUT_LANES_LO..][..CHAINLINK_OUT_LANES_WIDTH];
    for (i, want) in sub_out.iter().enumerate() {
        let got = claim.out_state[i];
        if got != *want {
            return Err(format!(
                "recursion-root outgoing limb {i} is {got}, but the Fq-transcript sub-proof pins \
                 {want}: the root does not LAND ON the sub-proof this head presents — the two are \
                 about different transcripts"
            ));
        }
    }

    Ok(())
}

/// ⚑ The Mina anchored-head verifier: a dregg turn's acceptance made to DEPEND on a verified Mina
/// head. See the module docs for the refusals and the named residuals.
///
/// ⚑ **CONSTRUCTED UNWIRED, AND UNWIRED MEANS REFUSE.** `Default` / [`Self::unwired`] carry no
/// [`MinaChainRootBackend`], and a head presented to an unwired verifier is REJECTED at refusal 7
/// — never waved through. A host that can verify a recursion root installs one with
/// [`Self::with_chain_root_backend`]; `dregg-node` does.
#[derive(Clone, Debug, Default)]
pub struct MinaAnchoredHeadStarkVerifier {
    chain_root: Option<Arc<dyn MinaChainRootBackend>>,
}

impl MinaAnchoredHeadStarkVerifier {
    /// The verifier with NO recursion-root backend: every head is refused at refusal 7.
    ///
    /// This is what `registry_with_real_verifiers()` installs, because `dregg-turn` cannot verify
    /// a recursion root and the honest behaviour of a consumer that cannot check something is to
    /// refuse it.
    pub fn unwired() -> Self {
        Self::default()
    }

    /// The verifier with a host-injected recursion-root backend.
    pub fn with_chain_root_backend(backend: Arc<dyn MinaChainRootBackend>) -> Self {
        Self {
            chain_root: Some(backend),
        }
    }

    /// Whether this verifier can check a recursion root at all. Diagnostic only — the REFUSAL is
    /// in `verify`, not in a caller's `if`.
    pub fn is_chain_root_wired(&self) -> bool {
        self.chain_root.is_some()
    }
}

impl WitnessedPredicateVerifier for MinaAnchoredHeadStarkVerifier {
    fn name(&self) -> &'static str {
        "mina-anchored-head-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: mina_head_predicate_vk(),
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The RECORDED TIP: the cell field this turn is writing / constraining. The executor
        // resolves it from authoritative state, so it is not the prover's to choose either.
        let recorded_tip: [u8; 32] = match input {
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) if b.len() == 32 => {
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::Bytes(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Mina tip state hash)",
                    actual: "non-32-byte Bytes",
                });
            }
            PredicateInput::Sender(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Mina tip state hash)",
                    actual: "Sender",
                });
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Mina tip state hash)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Mina tip state hash)",
                    actual: "SigningMessage",
                });
            }
            PredicateInput::AuthContext { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Mina tip state hash)",
                    actual: "AuthContext",
                });
            }
        };

        let reject = |reason: String| WitnessedPredicateError::Rejected {
            kind_name: KIND_NAME,
            reason,
        };

        // ── ⚑⚑⚑ REFUSAL 0 — CAPABILITY, CHECKED BEFORE ANYTHING ELSE.
        //
        // Whether this node can verify a recursion root is a property of the NODE, not of the
        // blob, so it is decided before the blob is even decoded. A node with no injected backend
        // REFUSES the head. It does not log and proceed, it does not treat "we cannot check the
        // root" as "there was no root to check", and it does not spend two STARK verifications
        // first. `dregg-turn` cannot link the recursion verifier (`turn/Cargo.toml`), so this is
        // the seam where the capability enters — and absence at a seam has exactly one honest
        // answer.
        let backend = self.chain_root.as_ref().ok_or_else(|| {
            reject(
                "no recursion-root backend is injected (fail-closed): this node cannot verify the \
                 Mina phase-2 chain root and therefore refuses the head. A host that CAN installs \
                 one via `register_mina_head_verifier_with_chain_root` (backend: \
                 `dregg-recursion-verify`)."
                    .into(),
            )
        })?;

        let wire: MinaHeadProofWire = postcard::from_bytes(proof_bytes).map_err(|e| {
            reject(format!(
                "Mina anchored-head proof wire did not decode (expected MinaHeadProofWire): {e}"
            ))
        })?;

        // ── ⚑⚑ REFUSAL 0b: THE ANCHOR PAIR. The wire's declared `(state, height)` must be the
        // pair the cell program committed to, and the proof's PI 29 must be that height. The
        // anchor-height half is new on 2026-08-05 and is the consumer side of the `ANCHOR_H` PI
        // pin — a pin whose only reader is the descriptor that declares it is decoration.
        check_anchor_binding(
            commitment,
            &wire.pinned_anchor_state,
            wire.pinned_anchor_height,
            &wire.public_inputs,
        )
        .map_err(reject)?;

        // ── REFUSALS 1-3: the proof must be ABOUT the pinned anchor, must record THAT head, and
        // must have met at least the mainnet Samasika depth. All three read authoritative state,
        // never the action.
        //
        // ⚑ The anchor argument is the wire's declared state, NOT `commitment` — since the
        // 2026-08-05 flag day the commitment is `H(state ‖ height)` and is no longer the state
        // hash itself. `check_anchor_binding` above is what makes that substitution safe: it has
        // already refused unless the declared state hashes into the pinned commitment.
        check_head_binding(
            &wire.pinned_anchor_state,
            &recorded_tip,
            &wire.public_inputs,
        )
        .map_err(reject)?;

        // ── ⚑⚑ REFUSAL 3b: **THE DEFERRED IPA ACCUMULATOR.** The leg Halo/Pickles never evaluates
        // in-circuit and upstream `&&`s into `batch_step_dlog_check` — and that this light client
        // did not evaluate AT ALL until today. Fail-closed on an ABSENT backend: a node that cannot
        // discharge the accumulator cannot know whether the terminal opening is vacuous, so it
        // refuses the head rather than accepting the carrier on the prover's word.
        wire.accumulator.check_arity().map_err(reject)?;
        let acc_oracle = installed_mina_accumulator_oracle().ok_or_else(|| {
            reject(
                "no Mina accumulator oracle is installed (fail-closed): this node cannot discharge \
                 the deferred IPA accumulator claim `C == <b_poly_coefficients(u), srs.g>` and \
                 therefore refuses the head. Install it at startup via \
                 `dregg_exec_lean::register_mina_accumulator_oracle`."
                    .to_string(),
            )
        })?;
        acc_oracle.discharged(&wire.accumulator).map_err(|e| {
            reject(format!(
                "the Mina deferred IPA accumulator did not discharge: {e}"
            ))
        })?;

        // ── ⚑⚑ REFUSAL 4: the head proof's DECLARED sub-proof is the one presented.
        check_transcript_binding(&wire.public_inputs, &wire.transcript_public_inputs)
            .map_err(reject)?;

        // ── ⚑⚑ REFUSALS 7-10: THE RECURSION ROOT OF THE 46-LINK PHASE-2 CHAIN. The backend was
        // required at refusal 0; here it is used.
        let (measured_vk, root_claim) =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                backend.verify_chain_root(&wire.chain_root_proof)
            }))
            .map_err(|_| {
                reject("Mina phase-2 chain-root verify panicked (treated as rejection)".into())
            })?
            .map_err(|reason| reject(format!("the Mina phase-2 chain root rejected: {reason}")))?;
        check_chain_root_binding(
            &backend.pinned_root_vk(),
            &measured_vk,
            &root_claim,
            &wire.transcript_public_inputs,
        )
        .map_err(reject)?;

        // ── ⚑⚑ REFUSAL 5: **THE SUB-PROOF ITSELF.** This is the step that makes the light client
        // consume a proof where it used to consume a bit. `descriptor_by_name` is fail-closed
        // `None`; a node that cannot check the Fq transcript REFUSES the head rather than accepting
        // the carrier on the prover's word.
        let transcript_pis: Vec<BabyBear> = wire
            .transcript_public_inputs
            .iter()
            .map(|v| BabyBear::new(*v))
            .collect();
        let transcript_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let desc = descriptor_by_name(MINA_CHAINLINK_DESCRIPTOR).ok_or_else(|| {
                format!(
                    "no descriptor dispatches for {MINA_CHAINLINK_DESCRIPTOR:?} (fail-closed): this \
                     node cannot check the Mina Wrap proof's Fq transcript and therefore refuses \
                     the head"
                )
            })?;
            if desc.public_input_count != MINA_CHAINLINK_PI_COUNT {
                return Err(format!(
                    "the descriptor served for {MINA_CHAINLINK_DESCRIPTOR:?} declares {} public \
                     inputs; this consumer's pin layout is {MINA_CHAINLINK_PI_COUNT}. Refusing an \
                     ambiguous layout rather than reading the outgoing block off the wrong offsets",
                    desc.public_input_count
                ));
            }
            // ── ⚑⚑ REFUSAL 5b: the head descriptor's recursion bind names THIS program.
            let head = descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR).ok_or_else(|| {
                format!(
                    "no descriptor dispatches for {MINA_LC_VERIFY_DESCRIPTOR:?} (fail-closed): \
                     this node cannot check a Mina anchored head and therefore refuses one"
                )
            })?;
            check_subproof_program_pin(&head, &desc)?;
            verify_vm_descriptor2(&desc, &wire.transcript_proof, &transcript_pis)
        }));
        match transcript_result {
            Ok(Ok(())) => {}
            Ok(Err(reason)) => {
                return Err(reject(format!(
                    "the Mina Wrap Fq-transcript sub-proof rejected: {reason}"
                )));
            }
            Err(_) => {
                return Err(reject(
                    "Mina Wrap Fq-transcript sub-proof decode/verify panicked (treated as \
                     rejection)"
                        .into(),
                ));
            }
        }

        // ── REFUSAL 6: the STARK over the Lean-compiled descriptor. Its own gates then force the
        // published `blockchain_length` to be the pinned anchor plus the EXHIBITED segment, the
        // witnessed depth to be measured to that derived tip, the three ranged slack teeth and the
        // three carrier bits. Decode + verify under `catch_unwind`: a malformed blob is a
        // fail-closed rejection, never a panic that unwinds through the executor.
        let public_inputs: Vec<BabyBear> = wire
            .public_inputs
            .iter()
            .map(|v| BabyBear::new(*v))
            .collect();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let desc = descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR).ok_or_else(|| {
                format!(
                    "no descriptor dispatches for {MINA_LC_VERIFY_DESCRIPTOR:?} (fail-closed): \
                     this node cannot check a Mina anchored head and therefore refuses one"
                )
            })?;
            verify_vm_descriptor2(&desc, &wire.proof, &public_inputs)
        }));
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(reason)) => Err(reject(format!(
                "the Mina anchored-head verify STARK rejected: {reason}"
            ))),
            Err(_) => Err(reject(
                "Mina anchored-head proof decode/verify panicked (treated as rejection)".into(),
            )),
        }
    }
}

/// The verifier as a registry-ready `Arc`, under [`mina_head_predicate_vk`] — **UNWIRED**.
///
/// It refuses every head at refusal 7 until a host installs a recursion-root backend with
/// [`register_mina_head_verifier_with_chain_root`]. That is the honest default: `dregg-turn`
/// cannot verify a recursion root, and a verifier that accepts what it cannot check is the
/// fail-open shape.
pub fn mina_head_verifier() -> Arc<dyn WitnessedPredicateVerifier> {
    Arc::new(MinaAnchoredHeadStarkVerifier::unwired())
}

/// ⚑ **THE HOST WIRING HELPER.** Replace the registry's UNWIRED Mina anchored-head verifier with
/// one that can check a recursion root, backed by `backend`.
///
/// The app-side analogue of `TeeWitnessedPredicateVerifier::with_verifier`: the vk is unchanged
/// (`mina_head_predicate_vk()`), so a cell program written against the unwired node keeps working
/// — it just stops being refused at refusal 7. `dregg-node` calls this from `executor_setup.rs`
/// with the `dregg-recursion-verify` backend.
pub fn register_mina_head_verifier_with_chain_root(
    registry: &mut dregg_cell::predicate::WitnessedPredicateRegistry,
    backend: Arc<dyn MinaChainRootBackend>,
) {
    registry.register_custom(
        mina_head_predicate_vk(),
        Arc::new(MinaAnchoredHeadStarkVerifier::with_chain_root_backend(
            backend,
        )),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑⚑ **REFUSAL 5b, POLARITY ONE — the served head descriptor's program pin IS the served
    /// sub-proof descriptor's fingerprint.** Both objects come from `descriptor_by_name`, so this is
    /// the exact pair a node holds at verify time, not a reconstruction.
    ///
    /// ⚠ This is the check that was RED as a sibling test for hours on 2026-08-05 while every head
    /// this node accepted carried a pin naming a program no descriptor in the tree had. It runs on
    /// the node now.
    #[test]
    fn the_head_descriptors_program_pin_is_the_served_sub_proofs_fingerprint() {
        let head = descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR).expect("head descriptor served");
        let sub =
            descriptor_by_name(MINA_CHAINLINK_DESCRIPTOR).expect("sub-proof descriptor served");
        assert_eq!(sub.public_input_count, MINA_CHAINLINK_PI_COUNT);
        check_subproof_program_pin(&head, &sub)
            .expect("the head's recursion bind must name the sub-proof this node dispatches");
    }

    /// ⚑⚑ **REFUSAL 5b, POLARITY TWO — a head descriptor pinned to some OTHER program is REFUSED,**
    /// and the sibling used here is a real served descriptor, so the refusal is not staged against a
    /// value nothing could produce. This is the shape a re-emission drift takes: one artifact moves,
    /// the other does not, and the pin silently names a program nobody holds.
    #[test]
    fn a_head_pinned_to_a_different_program_is_refused() {
        let head = descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR).expect("head descriptor served");
        let other = descriptor_by_name("dregg-mina-lightclient-link::v1")
            .expect("the multi-row segment descriptor is served");
        let e = check_subproof_program_pin(&head, &other)
            .expect_err("a pin naming a different program must be REFUSED");
        assert!(
            e.contains("names a DIFFERENT program"),
            "the refusal must name the substitution; got: {e}"
        );
    }

    /// ⚑ And the two descriptors it compares are genuinely different objects, so the refusal above
    /// is not an artefact of handing the same bytes twice.
    #[test]
    fn the_program_pin_refusal_is_not_vacuous() {
        let sub =
            descriptor_by_name(MINA_CHAINLINK_DESCRIPTOR).expect("sub-proof descriptor served");
        let other = descriptor_by_name("dregg-mina-lightclient-link::v1").expect("served");
        assert_ne!(
            effect_vm_descriptor2_semantic_fingerprint(&sub).expect("representable"),
            effect_vm_descriptor2_semantic_fingerprint(&other).expect("representable"),
        );
    }

    /// ⚑⚑ **THE SEVEN-BLOCK WRAPLINK IS NOT SERVED, AND THAT IS A REFUSAL, NOT AN ABSENCE.** It
    /// pinned two of a Poseidon state's three outgoing lanes, so a fold-root weld against it
    /// compared 64 of 96 limbs. A node that could still resolve it by name is a node whose next
    /// reader can pick the weaker object.
    #[test]
    fn the_superseded_wraplink_no_longer_dispatches() {
        assert!(descriptor_by_name("dregg-pasta-fq-wraplink::v1").is_none());
        assert!(descriptor_by_name(MINA_CHAINLINK_DESCRIPTOR).is_some());
    }

    /// The vk is a function of the DESCRIPTOR NAME, so a VK-epoch flip that renames the descriptor
    /// moves the predicate identity with it rather than leaving a stale predicate dispatching to a
    /// new circuit.
    #[test]
    fn vk_is_stable_and_name_derived() {
        assert_eq!(mina_head_predicate_vk(), mina_head_predicate_vk());
        let mut h = blake3::Hasher::new();
        h.update(b"dregg.witnessed-predicate.mina-anchored-head.v1\0");
        h.update(b"dregg-mina-lightclient-verify::v2");
        assert_ne!(mina_head_predicate_vk(), *h.finalize().as_bytes());
    }

    /// PI layout agrees with `LightClientMinaAir`'s Lean constants.
    #[test]
    fn pi_layout_matches_the_lean_descriptor() {
        assert_eq!(PI_ANCHOR_STATE_BASE, 0);
        assert_eq!(PI_TIP_STATE_BASE, 9);
        assert_eq!(PI_BLOCK_LEN, 18);
        assert_eq!(PI_REQ_DEPTH, 19);
        assert_eq!(PI_SUB_COMMIT_BASE, 20);
        // ⚑ 30, not 29, since `ANCHOR_H` became a published PI on 2026-08-05. The literals here
        // are deliberately literals: they are the SECOND source, and a pin written as
        // `assert_eq!(MINA_LC_PI_COUNT, MINA_LC_PI_COUNT)` would be decoration. Checked against
        // Lean `LightClientMinaAir.MINA_PI_COUNT` (`3 * STATE_LIMBS + 3`, with
        // `minaVerify_layout_facts` proving it `= 30`) and against the emitted
        // `dregg-mina-lightclient-verify-v1.json`, whose `public_input_count` is 30.
        assert_eq!(PI_ANCHOR_H, 29);
        assert_eq!(MINA_LC_PI_COUNT, 30);
    }

    /// ⚑⚑ POSITIVE POLARITY FOR THE SUB-PROOF BINDING: a head proof that publishes the digest of
    /// the sub-proof it presents BINDS. Without this the refusal below would be satisfied by a
    /// check that refuses everything.
    #[test]
    fn a_head_declaring_the_sub_proof_it_presents_is_accepted() {
        let sub: Vec<u32> = (0..MINA_CHAINLINK_PI_COUNT as u32).collect();
        let pis = pis_with_sub(&[7u8; 32], &[3u8; 32], 290, &sub);
        check_transcript_binding(&pis, &sub).expect("the declared sub-proof IS the presented one");
    }

    /// ⚑⚑ REFUSED: a head proof that names sub-proof A and hands over sub-proof B. This is the
    /// refusal that makes `WRAP_FS_PROVED` cost the prover a second STARK rather than a bit — the
    /// in-AIR binds pin the PROGRAM, and this pins WHICH instance of it.
    #[test]
    fn a_head_presenting_a_different_sub_proof_is_refused() {
        let declared: Vec<u32> = (0..MINA_CHAINLINK_PI_COUNT as u32).collect();
        let pis = pis_with_sub(&[7u8; 32], &[3u8; 32], 290, &declared);
        let mut other = declared.clone();
        other[0] += 1;
        let err = check_transcript_binding(&pis, &other).unwrap_err();
        assert!(
            err.contains("DIFFERENT sub-proof"),
            "the refusal must name the substitution: {err}"
        );
    }

    /// ⚑ REFUSED: a sub-proof of the wrong arity. A truncated PI vector is the `mina-tip` shape one
    /// layer down, and the commitment absorbs the arity first so it cannot be a prefix collision.
    #[test]
    fn a_sub_proof_of_the_wrong_arity_is_refused() {
        let declared: Vec<u32> = (0..MINA_CHAINLINK_PI_COUNT as u32).collect();
        let pis = pis_with_sub(&[7u8; 32], &[3u8; 32], 290, &declared);
        let err = check_transcript_binding(&pis, &declared[..10]).unwrap_err();
        assert!(err.contains("binds exactly"), "{err}");
    }

    /// The honest PI vector with the sub-proof commitment lanes filled from `sub`.
    fn pis_with_sub(anchor: &[u8; 32], tip: &[u8; 32], k: u32, sub: &[u32]) -> Vec<u32> {
        let mut pis = pis_for(anchor, tip, k);
        for (i, v) in key_lanes_u32(&chainlink_pi_commitment(sub))
            .iter()
            .enumerate()
        {
            pis[PI_SUB_COMMIT_BASE + i] = *v;
        }
        pis
    }

    /// The honest PI vector for a head anchored at `anchor`, recording `tip`, at depth `k`.
    fn pis_for(anchor: &[u8; 32], tip: &[u8; 32], k: u32) -> Vec<u32> {
        let mut pis = vec![0u32; MINA_LC_PI_COUNT];
        for (i, v) in key_lanes_u32(anchor).iter().enumerate() {
            pis[PI_ANCHOR_STATE_BASE + i] = *v;
        }
        for (i, v) in key_lanes_u32(tip).iter().enumerate() {
            pis[PI_TIP_STATE_BASE + i] = *v;
        }
        pis[PI_BLOCK_LEN] = 400_000;
        pis[PI_REQ_DEPTH] = k;
        pis
    }

    /// ⚑ POSITIVE POLARITY: an honest binding — the proof is about the pinned anchor, records the
    /// head the turn writes, and met mainnet `k` — PASSES the binding check. Without this the four
    /// refusals below would be satisfied by a check that refuses everything.
    #[test]
    fn an_honest_binding_is_accepted() {
        let anchor = [7u8; 32];
        let tip = [3u8; 32];
        check_head_binding(
            &anchor,
            &tip,
            &pis_for(&anchor, &tip, MINA_MIN_CONFIRMATION_DEPTH),
        )
        .expect("an honest anchored head must bind");
    }

    /// ⚑ REFUSED: a proof whose anchor lanes are not the CELL-PROGRAM-PINNED anchor. The anchor is
    /// the trust root and it is state, not testimony — and the AIR itself cannot tell two `k`-deep
    /// segments under different anchors apart, so this refusal is exactly where it has to live.
    #[test]
    fn a_head_under_a_different_anchor_is_refused() {
        let pinned = [7u8; 32];
        let other = [9u8; 32];
        let tip = [3u8; 32];
        let err = check_head_binding(&pinned, &tip, &pis_for(&other, &tip, 290)).unwrap_err();
        assert!(
            err.contains("anchored somewhere else"),
            "expected an anchor refusal, got: {err}"
        );
    }

    /// ⚑ REFUSED: a turn that proves head A and records head B. The recorded slot must BE the head
    /// the proof verified, or the state write is decoration.
    #[test]
    fn recording_a_different_head_than_the_proof_is_refused() {
        let pinned = [7u8; 32];
        let proved = [3u8; 32];
        let recorded = [4u8; 32];
        let err =
            check_head_binding(&pinned, &recorded, &pis_for(&pinned, &proved, 290)).unwrap_err();
        assert!(
            err.contains("different head"),
            "expected a recorded-tip refusal, got: {err}"
        );
    }

    /// ⚑ REFUSED: a proof that met `k = 1` cannot discharge the 290-deep policy — and note that
    /// EVERY GATE IN THE AIR HOLDS on such a proof. The descriptor publishes the depth met
    /// precisely so a consumer can refuse a weaker one.
    #[test]
    fn a_shallow_depth_policy_is_refused() {
        let anchor = [7u8; 32];
        let tip = [3u8; 32];
        let err = check_head_binding(&anchor, &tip, &pis_for(&anchor, &tip, 1)).unwrap_err();
        assert!(
            err.contains("requires at least 290"),
            "expected a depth-floor refusal, got: {err}"
        );
        // …and 289 is refused too: the floor is the mainnet constant, not a round number.
        let err289 = check_head_binding(&anchor, &tip, &pis_for(&anchor, &tip, 289)).unwrap_err();
        assert!(err289.contains("requires at least 290"), "{err289}");
    }

    /// ⚑ REFUSED: a wire whose PI count is not what the descriptor binds. A short vector must never
    /// be padded into acceptance.
    #[test]
    fn a_wrong_pi_count_is_refused() {
        let anchor = [7u8; 32];
        let tip = [3u8; 32];
        let mut short = pis_for(&anchor, &tip, 290);
        short.pop();
        let err = check_head_binding(&anchor, &tip, &short).unwrap_err();
        // ⚑ FIXED 2026-08-05. This asserted `binds exactly 20` while the message has interpolated
        // `MINA_LC_PI_COUNT` — 29 since the PI flip — for as long as the flip has been in. It
        // therefore could not go red for the right reason; it only ever passed because
        // `"…binds exactly 29"` does not contain `"binds exactly 20"`… which is to say it did NOT
        // pass, it would have failed the moment anyone ran it. Assert on the CONSTANT, so a
        // future PI flip moves the expectation with the message instead of rotting again.
        assert!(
            err.contains(&format!("binds exactly {MINA_LC_PI_COUNT}")),
            "expected a PI-count refusal naming {MINA_LC_PI_COUNT}, got: {err}"
        );
    }

    /// ⚑ The nine-lane encoding is INJECTIVE, so distinct heads have distinct PI vectors and the
    /// binding above cannot be satisfied by a near-miss. (`Faithful9::from_key_lanes9`, Lean
    /// `keyToLanes9`: image exactly `2^256`.)
    #[test]
    fn distinct_heads_have_distinct_lane_vectors() {
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        b[31] = 1;
        assert_ne!(key_lanes_u32(&a), key_lanes_u32(&b));
        // …including a difference confined to the high byte, which an eight-lane encoding lost.
        a[0] = 0x80;
        assert_ne!(key_lanes_u32(&a), key_lanes_u32(&[0u8; 32]));
        // Round-trip: the lanes recover the head.
        assert_eq!(Faithful9::from_key_lanes9(&a).to_key_bytes(), a);
    }

    /// A garbage proof blob is a fail-closed REJECTION at the wire, never a panic.
    ///
    /// ⚑ Run against a WIRED verifier deliberately: on an unwired one the refusal would be
    /// refusal 0, and this test would pass without ever exercising the codec it is about.
    #[test]
    fn a_garbage_proof_blob_is_refused() {
        let anchor = [7u8; 32];
        let tip = [3u8; 32];
        let v =
            MinaAnchoredHeadStarkVerifier::with_chain_root_backend(Arc::new(ScriptedRootBackend {
                pinned: [9u8; 32],
                measured: [9u8; 32],
                claim: honest_root_claim(),
            }));
        let err = v
            .verify(&anchor, &PredicateInput::Slot(&tip), &[0xAAu8; 64])
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => {
                assert!(reason.contains("did not decode"), "{reason}")
            }
            other => panic!("expected a wire-decode rejection, got {other:?}"),
        }
    }

    // ════════════════════════════════════════════════════════════════════════════════════════
    // ⚑⚑ REFUSALS 7-10 — THE RECURSION ROOT. Both polarities, and the ABSENT case exhibited.
    // ════════════════════════════════════════════════════════════════════════════════════════

    /// A backend that reports whatever it is told to. The refusals under test are the CONSUMER's,
    /// so the backend must be able to report an honest triple as well as each dishonest one —
    /// otherwise the positive pole below would be untestable and the negatives vacuous.
    #[derive(Debug)]
    struct ScriptedRootBackend {
        pinned: [u8; 32],
        measured: [u8; 32],
        claim: MinaChainRootClaim,
    }

    impl MinaChainRootBackend for ScriptedRootBackend {
        fn pinned_root_vk(&self) -> [u8; 32] {
            self.pinned
        }
        fn verify_chain_root(
            &self,
            _proof_bytes: &[u8],
        ) -> Result<([u8; 32], MinaChainRootClaim), String> {
            Ok((self.measured, self.claim.clone()))
        }
    }

    /// The 256 sub-proof PIs, with the WHOLE outgoing block filled from `out` (all 96 limbs of the
    /// chain claim's outgoing state — under the seven-block wraplink this was 64 and the third lane
    /// went unchecked).
    fn sub_pis_landing_on(out: &[u32]) -> Vec<u32> {
        let mut pis: Vec<u32> = (0..MINA_CHAINLINK_PI_COUNT as u32).collect();
        pis[CHAINLINK_OUT_LANES_LO..][..CHAINLINK_OUT_LANES_WIDTH]
            .copy_from_slice(&out[..CHAINLINK_OUT_LANES_WIDTH]);
        pis
    }

    /// An honest root claim: fresh sponge in, some outgoing state, some accumulator.
    fn honest_root_claim() -> MinaChainRootClaim {
        MinaChainRootClaim {
            in_state: vec![0u32; CHAIN_STATE_WIDTH],
            // Values chosen inside the 8-bit limb range the Lean layout uses, so nothing here is
            // refused for a reason other than the one under test.
            out_state: (0..CHAIN_STATE_WIDTH as u32)
                .map(|i| (i * 3) % 251)
                .collect(),
            transcript_acc: vec![7u32; 8],
        }
    }

    /// ⚑⚑ POSITIVE POLARITY: an honest root — pinned anchor set, measured fingerprint equal,
    /// fresh sponge in, landing on the sub-proof's own outgoing lanes — BINDS. Without this the
    /// four refusals below would be satisfied by a check that refuses everything.
    #[test]
    fn an_honest_chain_root_binds_to_the_sub_proof_it_closes() {
        let claim = honest_root_claim();
        let sub = sub_pis_landing_on(&claim.out_state);
        check_chain_root_binding(&[9u8; 32], &[9u8; 32], &claim, &sub)
            .expect("an honest root that lands on the presented sub-proof must bind");
    }

    /// ⚑ REFUSED (7): an all-zero anchor. An unset trust anchor that happens to compare equal is
    /// the fail-open shape — a node with no pinned fingerprint cannot tell which circuit a root
    /// proves, and must say so rather than accept.
    #[test]
    fn an_unset_root_anchor_is_refused() {
        let claim = honest_root_claim();
        let sub = sub_pis_landing_on(&claim.out_state);
        let err = check_chain_root_binding(&[0u8; 32], &[0u8; 32], &claim, &sub).unwrap_err();
        assert!(err.contains("all-zero"), "{err}");
    }

    /// ⚑⚑ REFUSED (8): a root of a DIFFERENT circuit. This is the refusal that makes
    /// `recursion_vk_fingerprint` the root's identity — without it "the root verifies" means only
    /// "*some* circuit's proof verifies".
    #[test]
    fn a_root_of_a_different_circuit_is_refused() {
        let claim = honest_root_claim();
        let sub = sub_pis_landing_on(&claim.out_state);
        let mut other = [9u8; 32];
        other[31] ^= 1;
        let err = check_chain_root_binding(&[9u8; 32], &other, &claim, &sub).unwrap_err();
        assert!(err.contains("DIFFERENT circuit"), "{err}");
    }

    /// ⚑ REFUSED (9): a chain that did not start from a fresh Kimchi sponge. Every gate of the
    /// fold still holds on such a root — it is a perfectly good proof of a SUFFIX — which is
    /// exactly why the consumer has to refuse it.
    #[test]
    fn a_root_that_starts_mid_transcript_is_refused() {
        let mut claim = honest_root_claim();
        claim.in_state[17] = 1;
        let sub = sub_pis_landing_on(&claim.out_state);
        let err = check_chain_root_binding(&[9u8; 32], &[9u8; 32], &claim, &sub).unwrap_err();
        assert!(err.contains("FRESH Kimchi sponge"), "{err}");
    }

    /// ⚑⚑ REFUSED (10 — THE WELD): a root that does not land on the sub-proof this head presents.
    /// Both objects are internally impeccable; what is false is only that they are about the same
    /// transcript.
    #[test]
    fn a_root_that_lands_elsewhere_than_the_sub_proof_is_refused() {
        let claim = honest_root_claim();
        let mut sub = sub_pis_landing_on(&claim.out_state);
        sub[CHAINLINK_OUT_LANES_LO + 5] = sub[CHAINLINK_OUT_LANES_LO + 5].wrapping_add(1);
        let err = check_chain_root_binding(&[9u8; 32], &[9u8; 32], &claim, &sub).unwrap_err();
        assert!(err.contains("does not LAND ON"), "{err}");
    }

    /// ⚑ REFUSED: a claim of the wrong shape. A root that verifies but publishes a 200-lane claim
    /// of some OTHER circuit's layout must not be sliced into acceptance.
    #[test]
    fn a_root_claim_of_the_wrong_width_is_refused() {
        let mut claim = honest_root_claim();
        claim.out_state.pop();
        let sub: Vec<u32> = (0..MINA_CHAINLINK_PI_COUNT as u32).collect();
        let err = check_chain_root_binding(&[9u8; 32], &[9u8; 32], &claim, &sub).unwrap_err();
        assert!(err.contains("state limbs"), "{err}");
    }

    /// ⚑⚑⚑ **ABSENCE IS REFUSAL, EXHIBITED AT THE REGISTRY-FACING SURFACE.** The verifier
    /// `registry_with_real_verifiers()` installs has NO backend, and a head presented to it is
    /// `Rejected` **naming the missing backend** — not accepted, not skipped, not
    /// logged-and-proceeded.
    ///
    /// ⚑ The refusal is reachable with ARBITRARY bytes precisely because it fires at refusal 0,
    /// before the wire is decoded: whether this node can check a recursion root is a fact about
    /// the node. A test that had to mint two real IR-v2 proofs to reach it would be a test nobody
    /// runs, and the refusal it guards is the one this whole seam exists for.
    #[test]
    fn an_unwired_node_refuses_a_head_rather_than_skipping_the_root() {
        let v = MinaAnchoredHeadStarkVerifier::unwired();
        assert!(!v.is_chain_root_wired());
        let err = v
            .verify(&[7u8; 32], &PredicateInput::Slot(&[3u8; 32]), &[0u8; 8])
            .unwrap_err();
        match err {
            WitnessedPredicateError::Rejected { reason, .. } => assert!(
                reason.contains("no recursion-root backend is injected"),
                "the refusal must NAME the absent capability, got: {reason}"
            ),
            other => panic!("an unwired verifier must REJECT, got {other:?}"),
        }
    }

    /// ⚑ The wired verifier reports itself wired, and the registry helper installs it under the
    /// SAME vk — a host upgrade must not mint a second predicate identity.
    #[test]
    fn the_host_helper_upgrades_in_place_under_the_same_vk() {
        use dregg_cell::predicate::{WitnessedPredicateKind, WitnessedPredicateRegistry};

        let mut reg = WitnessedPredicateRegistry::empty();
        reg.register_custom(mina_head_predicate_vk(), mina_head_verifier());
        register_mina_head_verifier_with_chain_root(
            &mut reg,
            Arc::new(ScriptedRootBackend {
                pinned: [9u8; 32],
                measured: [9u8; 32],
                claim: honest_root_claim(),
            }),
        );
        let v = reg
            .get(WitnessedPredicateKind::Custom {
                vk_hash: mina_head_predicate_vk(),
            })
            .expect("the upgraded verifier resolves under the unchanged vk");
        assert_eq!(v.name(), "mina-anchored-head-stark");
    }

    /// The input shape is checked: this predicate reads a 32-byte state slot, never a signing
    /// message.
    #[test]
    fn a_signing_message_input_is_refused() {
        let anchor = [7u8; 32];
        let err = MinaAnchoredHeadStarkVerifier::unwired()
            .verify(
                &anchor,
                &PredicateInput::SigningMessage(b"not a state slot"),
                &[0u8; 8],
            )
            .unwrap_err();
        assert!(matches!(
            err,
            WitnessedPredicateError::InputShapeMismatch { .. }
        ));
    }
}
