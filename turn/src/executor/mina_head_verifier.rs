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
//! 4. **The STARK.** `descriptor_by_name(MINA_LC_VERIFY_DESCRIPTOR)` (fail-closed `None` on a miss)
//!    → `verify_vm_descriptor2` over all 20 public inputs. The descriptor's own gates then force
//!    `BLOCK_LEN = ANCHOR_H + SEG_LEN` and `WIT_DEPTH + SUBMIT_H = BLOCK_LEN` — the published
//!    `blockchain_length` is DERIVED from the pinned anchor plus the exhibited segment, so the one
//!    field a truncated peer reply leaves standing is not settable — plus the three ranged slack
//!    teeth and the three carrier bits.
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
//! * **`LINK_OK` and `PICKLES_OK` are witnessed carriers**, not re-derived in-AIR; the Pickles
//!   carrier rides the undischarged IPA/FRI floor. So this refuses a bent proof word only as
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
use dregg_circuit::descriptor_ir2::{DreggStarkConfig, Ir2BatchProof, verify_vm_descriptor2};
use dregg_circuit::faithful9::Faithful9;

/// The Lean-COMPILED Mina anchored-head verify descriptor's `descriptor_by_name` key.
///
/// Authored as `minaLcVerifyDesc` in
/// `metatheory/Dregg2/Circuit/Emit/LightClientMinaAir.lean` — `EffectLower.lowerAir` of the
/// `EffectAir` source `minaHeadAir`, with no hand-written `VmConstraint2` (house law #1).
pub const MINA_LC_VERIFY_DESCRIPTOR: &str = "dregg-mina-lightclient-verify::v1";

/// Number of public inputs the descriptor declares: nine pinned-anchor lanes, nine verified-tip
/// lanes, the derived `blockchain_length`, the Samasika depth met. Pinned to
/// `LightClientMinaAir.MINA_PI_COUNT`.
pub const MINA_LC_PI_COUNT: usize = 20;

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
/// because the descriptor binds all twenty and this verifier fixes eighteen of them from
/// authoritative state.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct MinaHeadProofWire {
    /// The twenty public inputs, in descriptor order.
    pub public_inputs: Vec<u32>,
    /// The IR-v2 batch proof over `MINA_LC_VERIFY_DESCRIPTOR`.
    pub proof: Ir2BatchProof<DreggStarkConfig>,
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

/// ⚑ The Mina anchored-head verifier: a dregg turn's acceptance made to DEPEND on a verified Mina
/// head. See the module docs for the four refusals and the named residuals.
#[derive(Clone, Copy, Debug, Default)]
pub struct MinaAnchoredHeadStarkVerifier;

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

        let wire: MinaHeadProofWire = postcard::from_bytes(proof_bytes).map_err(|e| {
            reject(format!(
                "Mina anchored-head proof wire did not decode (expected MinaHeadProofWire): {e}"
            ))
        })?;

        // ── REFUSALS 1-3: the proof must be ABOUT the pinned anchor, must record THAT head, and
        // must have met at least the mainnet Samasika depth. All three read authoritative state,
        // never the action.
        check_head_binding(commitment, &recorded_tip, &wire.public_inputs).map_err(reject)?;

        // ── REFUSAL 4: the STARK over the Lean-compiled descriptor. Its own gates then force the
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

/// The verifier as a registry-ready `Arc`, under [`mina_head_predicate_vk`].
pub fn mina_head_verifier() -> Arc<dyn WitnessedPredicateVerifier> {
    Arc::new(MinaAnchoredHeadStarkVerifier)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(MINA_LC_PI_COUNT, 20);
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
        assert!(
            err.contains("binds exactly 20"),
            "expected a PI-count refusal, got: {err}"
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
    #[test]
    fn a_garbage_proof_blob_is_refused() {
        let anchor = [7u8; 32];
        let tip = [3u8; 32];
        let err = MinaAnchoredHeadStarkVerifier
            .verify(&anchor, &PredicateInput::Slot(&tip), &[0xAAu8; 64])
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    /// The input shape is checked: this predicate reads a 32-byte state slot, never a signing
    /// message.
    #[test]
    fn a_signing_message_input_is_refused() {
        let anchor = [7u8; 32];
        let err = MinaAnchoredHeadStarkVerifier
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
