//! ⚑⚑⚑ **THE SOLANA LIGHT CLIENT'S CONSUMER — the rung that makes the mint path spend a STARK.**
//!
//! # What this replaces, measured at source
//!
//! `dregg-solana-lightclient-verify::v1` has been proven since it was emitted and **resolved only
//! from `circuit/tests/`**. Meanwhile the value-bearing Solana path ran entirely in hand-written
//! Rust:
//!
//! - `bridge/src/solana_relayer.rs:836` — `observe_lock_at_consensus_anchored` step (5) calls
//!   [`verify_lock_proof_consensus_anchored`], and *that* is the whole consensus decision;
//! - `bridge/src/solana_trustless.rs:686` — `verify_lock_proof_consensus_anchored_inner` =
//!   `check_binding` → `derive_verified_table` → `verify_consensus_anchored`;
//! - `bridge/src/solana_provenance.rs:697` — the super-majority itself is one Rust line,
//!   `voted.saturating_mul(3) >= total.saturating_mul(2) && total > 0`.
//!
//! No AIR, no proof, no descriptor. A `LockProofTrust::ConsensusVerified` was a Rust `enum`
//! variant returned by a function that counted votes in a `for` loop.
//!
//! ⚑ **AND THE RUST QUORUM IS NON-STRICT WHERE THE AIR IS STRICT.** `tally_authorized` admits
//! `3·voted == 2·total` (`>=`); the Lean AIR refuses exactly that point —
//! `LightClientSolanaAir.solLcAir_refuses_the_exact_two_thirds_point_at_live_active_stake`.
//! (`circuit/tests/solana_lightclient_proves.rs::the_exact_two_thirds_boundary_is_refused` exhibits
//! the same refusal, but on a toy `(total 3, rooted 2)` — the live-stake instance is
//! `turn/tests/solana_anchored_lock_lands.rs`'s pair, which drives the deployed prover at
//! `LIVE_ACTIVE_STAKE`.) Routing the decision through the descriptor is
//! therefore a STRENGTHENING at the boundary, not a re-spelling: a cluster sitting exactly on two
//! thirds mints under the Rust gate and is refused under this one.
//!
//! # What this consumer decides
//!
//! It is a [`WitnessedPredicateVerifier`] under [`solana_lock_predicate_vk`]. It refuses unless a
//! STARK over the Lean-compiled `dregg-solana-lightclient-verify::v1` verifies AND every one of its
//! 22 public inputs is welded to something the prover does not choose:
//!
//! | PI slots | meaning | welded to |
//! |---|---|---|
//! | `0..8` | the fold's eight `.last` output lanes — the stake-table anchor root | the **governance-pinned** lane root injected into this node |
//! | `8..17` | the rooted bank root, nine limbs | the `Faithful9` lanes of the bank hash the executor recorded |
//! | `17` | the rooted slot | the slot named in the predicate commitment |
//! | `18..22` | the active-stake denominator | *nothing* — it is the fold's accumulator, forced in-circuit by `sol_denominator_is_derived_from_the_stake_rows` |
//!
//! The quorum arithmetic (`3·rooted > 2·total`, both operands limb-ranged) is **not checked here
//! and must not be**: it is the descriptor's own gates, and re-checking it in Rust would be the
//! twin this file exists to delete.
//!
//! # ⚠ WHAT THIS FILE DELIBERATELY DOES NOT DO — and the finding behind it
//!
//! It does **not** dispatch `dregg-solana-stake-table-fold::v1` as a sub-proof, and that is a
//! measurement, not an omission. `metatheory/Dregg2/Circuit/Emit/LightClientSolanaAir.lean:989`:
//!
//! ```text
//! def solLcVerifyAir : EffectAir :=
//!   { tables := foldTables ++ [carryTable]
//!   , legs   := foldLegs ++ quorumRangeLegs ++ ... }
//! ```
//!
//! The light client's legs **begin with the fold's legs, entire** — 33 of its 73, machine-checked
//! by `LightClientSolanaAir.sol_fold_block_is_the_shared_source` and, from the other side, by
//! `LightClientSolStakeFoldAir.solStakeFold_shares_its_legs_with_the_light_client`. The fold's 12
//! public inputs are exactly this descriptor's slots `0..8` and `18..22`, off the same columns on
//! the same rows.
//!
//! So a fold sub-proof of *this* head would attest a computation the head already performs, on the
//! same trace, and a `proof_bind` pinning it would be an identity carrier: a seam whose sub-proof
//! cannot fail unless the head does. The 2026-08-04 absorption that took this descriptor from 19
//! decorative anchors to 10 is the very change that obviated the sub-proof relationship
//! `circuit/src/descriptor_by_name.rs:276-287` still proposes. **The head is the fold plus the
//! quorum; dispatching both is dispatching the fold twice.**
//!
//! What a fold sub-proof *would* buy is a root established by a program carrying no quorum claim —
//! which is what an anchor **rotation** needs (`solana_trustless.rs:587`'s `rotate` chain, still
//! hand-written). This consumer refuses a rotated anchor instead of trusting it; see
//! [`SolanaLockProofWire::rotation_steps`].
//!
//! # House law #1
//!
//! Every constraint named here is authored in
//! `metatheory/Dregg2/Circuit/Emit/LightClientSolanaAir.lean` and reaches this file only as the
//! emitted `dregg-solana-lightclient-verify-v1.json`. This file dispatches, welds and refuses; it
//! authors no AIR.

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

/// The Lean-COMPILED Solana light-client verify descriptor's `descriptor_by_name` key.
///
/// Authored as `solLcVerifyDesc` in
/// `metatheory/Dregg2/Circuit/Emit/LightClientSolanaAir.lean` — `EffectLower.lowerAir` of the
/// `EffectAir` source `solLcVerifyAir`, with no hand-written `VmConstraint2` (house law #1).
pub const SOL_LC_VERIFY_DESCRIPTOR: &str = "dregg-solana-lightclient-verify::v1";

/// The stake-table fold descriptor. **Named, not dispatched** — see the module docblock for the
/// measurement that says why. Kept as a constant because the *pin* below is a statement about it:
/// this consumer refuses a head whose fingerprint has drifted onto the fold's.
pub const SOL_STAKE_FOLD_DESCRIPTOR: &str = "dregg-solana-stake-table-fold::v1";

/// `LightClientSolanaAir.PI_COUNT`.
pub const SOL_LC_PI_COUNT: usize = 22;

/// `LightClientSolanaAir.ANCHOR_LANES` — PI slots `0..8`, the fold's `.last` output lanes.
pub const SOL_ANCHOR_LANES: usize = 8;
/// PI slot of anchor-root lane `j`. `LightClientSolanaAir.PI_ANCHOR_ROOT`.
pub const fn pi_anchor_root(j: usize) -> usize {
    j
}
/// `LightClientSolanaAir.BANK_ROOT_LIMBS` — PI slots `8..17`, MSB-first.
pub const SOL_BANK_ROOT_LIMBS: usize = 9;
/// PI slot of bank-root limb `i`. `LightClientSolanaAir.PI_BANK_ROOT`.
pub const fn pi_bank_root(i: usize) -> usize {
    SOL_ANCHOR_LANES + i
}
/// PI slot of the rooted slot. `LightClientSolanaAir.PI_SLOT`.
pub const SOL_PI_SLOT: usize = SOL_ANCHOR_LANES + SOL_BANK_ROOT_LIMBS;
/// `LightClientSolanaAir.TALLY_LIMBS` — PI slots `18..22`, the active-stake denominator.
pub const SOL_TOTAL_STK_LIMBS: usize = 4;
/// PI slot of total-stake limb `i`. `LightClientSolanaAir.PI_TOTAL_STK`.
pub const fn pi_total_stk(i: usize) -> usize {
    SOL_ANCHOR_LANES + SOL_BANK_ROOT_LIMBS + 1 + i
}

/// A compile-time guard that the layout above cannot be narrowed into overlap or overflow. The
/// Mina rung earned this the hard way: a consumer reading a block off the wrong offsets compares
/// numbers to numbers and calls it a binding.
const _: () = assert!(SOL_PI_SLOT == 17);
const _: () = assert!(pi_total_stk(0) == 18);
const _: () = assert!(pi_total_stk(SOL_TOTAL_STK_LIMBS - 1) == SOL_LC_PI_COUNT - 1);

const KIND_NAME: &str = "SolanaAnchoredLock";

/// ⚑⚑ **THE PROGRAM PIN — the nine `Faithful9` lanes of the served light-client descriptor's
/// blake3 semantic fingerprint.**
///
/// This literal is the *second* source. The first is the descriptor JSON itself, whose bytes Lean
/// pins with `LightClientSolanaAir.solLcVerifyDesc_emits_golden_json`. At verify time this
/// consumer recomputes the fingerprint from the descriptor `descriptor_by_name` actually serves
/// and requires the nine lanes to agree — so a tree where the AIR was re-emitted and this constant
/// was not goes RED rather than verifying a STARK over a program nobody named.
///
/// ⚠ A pin against its own definition is decoration. This one is not: the value is entered here by
/// hand and derived there by the emitter, and `the_program_pin_is_the_served_descriptors_fingerprint`
/// is the gate between them. Re-emitting the descriptor re-mints this literal — say so in the
/// commit.
pub const SOL_LC_VK_LANES: [u32; 9] = [
    416547965, 512443238, 319789240, 215095374, 368157320, 16222435, 315947811, 273514716, 1745044,
];

/// The nine `Faithful9` key lanes of a 32-byte value, as canonical `u32`s. Lean `keyToLanes9`;
/// machine-checked injective. Same encoding the Mina rung uses (`mina_head_verifier::key_lanes_u32`)
/// and the same one this consumer requires of the nine bank-root limbs.
pub fn key_lanes_u32(bytes: &[u8; 32]) -> [u32; 9] {
    let lanes = Faithful9::from_key_lanes9(bytes).lanes();
    std::array::from_fn(|i| lanes[i].as_u32())
}

/// The predicate commitment a cell program must carry to demand a Solana anchored lock: a
/// domain-separated blake3 over the **governance-pinned stake-table lane root** and the **rooted
/// slot**. Both halves are preimages the wire must supply and this verifier re-derives, so neither
/// is the prover's to choose.
pub fn solana_lock_commitment(
    pinned_anchor_lanes: &[u32; SOL_ANCHOR_LANES],
    slot: u32,
) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg.solana-anchored-lock.commitment.v1\0");
    for lane in pinned_anchor_lanes {
        h.update(&lane.to_le_bytes());
    }
    h.update(&slot.to_le_bytes());
    *h.finalize().as_bytes()
}

/// The `Custom` vk this verifier registers under — domain-separated over the descriptor's NAME, so
/// a cell program written against this rung names the program it wants verified.
pub fn solana_lock_predicate_vk() -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg.witnessed-predicate.solana-anchored-lock.v1\0");
    h.update(SOL_LC_VERIFY_DESCRIPTOR.as_bytes());
    *h.finalize().as_bytes()
}

/// ⚑ **THE GOVERNANCE-PINNED STAKE TABLE, as this node holds it.**
///
/// `bridge/src/solana_provenance.rs:635` compares a *SHA-256* table root
/// (`EpochStakeTable::root`, a domain-separated SHA-256 over `(epoch, len, [(pubkey, stake)])`)
/// against `WeakSubjectivityAnchor::stake_table_root`. The descriptor publishes an **eight-lane
/// Poseidon2 fold** of the same table (`FOLD_TAG = 0x53535446`, absorbed arity-16 per row).
///
/// ⚠ **These are two different commitments to the same object and cannot be compared to each
/// other.** A consumer that "welded" them would be asserting a hash collision. So the pin this
/// node holds is the *lane* root, governance-attested alongside the SHA-256 one — and a node that
/// holds no lane root refuses every lock rather than checking the half it has.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SolanaGovernanceAnchor {
    /// The epoch the pinned table belongs to.
    pub epoch: u64,
    /// The eight `.last` Poseidon2 fold lanes of that table — the value PI `0..8` must equal.
    pub stake_table_lane_root: [u32; SOL_ANCHOR_LANES],
}

/// The wire blob a Solana anchored-lock predicate carries.
#[derive(serde::Serialize, serde::Deserialize)]
pub struct SolanaLockProofWire {
    /// The 22 public inputs, in descriptor order.
    pub public_inputs: Vec<u32>,
    /// The IR-v2 batch proof over [`SOL_LC_VERIFY_DESCRIPTOR`]. **This node verifies it.**
    pub proof: Ir2BatchProof<DreggStarkConfig>,
    /// The governance anchor epoch this proof claims to be under. REQUIRED, and compared against
    /// the node's own pin — a proof under a different epoch is refused, never reinterpreted.
    pub anchor_epoch: u64,
    /// ⚑ The number of epoch-rotation steps between the governance-pinned table and the table this
    /// proof folds. REQUIRED, and **anything but zero is REFUSED.**
    ///
    /// `solana_trustless.rs:587` rotates the trusted table forward through
    /// `provenance.rotation` in hand-written Rust, and nothing proves that chain. Rather than
    /// verify a STARK whose anchor root reached the pinned one through an unproven Rust loop, this
    /// consumer refuses the rotated case outright. That is the named residual, and it is a refusal
    /// rather than a silence.
    pub rotation_steps: u32,
    /// The 32-byte bank hash the executor recorded for this lock — the PREIMAGE of PI `8..17`.
    pub bank_hash: [u8; 32],
}

/// ⚑⚑ **THE PROGRAM-PIN CHECK — recomputed at verify time, and spent BEFORE the STARK.**
///
/// Recomputes the blake3 semantic fingerprint of the descriptor this node *actually dispatches*
/// and requires its nine `Faithful9` lanes to be [`SOL_LC_VK_LANES`]. A tree where the AIR moved
/// and the constant did not is refused here, without a verification being spent on a program the
/// consumer cannot name.
pub fn check_program_pin(desc: &EffectVmDescriptor2, expected: &[u32; 9]) -> Result<(), String> {
    let fp = effect_vm_descriptor2_semantic_fingerprint(desc).map_err(|e| {
        format!(
            "the descriptor served for {SOL_LC_VERIFY_DESCRIPTOR:?} has no representable semantic \
             fingerprint ({e}): this node cannot tell which program it is about to verify"
        )
    })?;
    let got = key_lanes_u32(&fp);
    for (i, want) in expected.iter().enumerate() {
        if got[i] != *want {
            return Err(format!(
                "this consumer pins program lane {i} at {want}, but the descriptor it dispatches \
                 for {SOL_LC_VERIFY_DESCRIPTOR:?} fingerprints to {}: the AIR was re-emitted and \
                 `SOL_LC_VK_LANES` was not (or the reverse) — refusing the lock rather than \
                 verifying a STARK over a program this node cannot name",
                got[i]
            ));
        }
    }
    Ok(())
}

/// ⚑ **THE PUBLIC-INPUT WELD — refusals 5, 6 and 7, as a pure function of authoritative state.**
///
/// Separated from [`SolanaAnchoredLockStarkVerifier::verify`] on purpose: these refusals are about
/// numbers the executor and governance own, not about the proof, so they are testable without a
/// prover and cannot drift into the STARK path.
pub fn check_public_input_weld(
    pinned: &SolanaGovernanceAnchor,
    wire: &SolanaLockProofWire,
    slot: u32,
) -> Result<(), String> {
    if wire.public_inputs.len() != SOL_LC_PI_COUNT {
        return Err(format!(
            "the wire carries {} public inputs; {SOL_LC_VERIFY_DESCRIPTOR:?} declares \
             {SOL_LC_PI_COUNT}. Refusing an ambiguous layout rather than reading the anchor block \
             off the wrong offsets",
            wire.public_inputs.len()
        ));
    }
    if wire.anchor_epoch != pinned.epoch {
        return Err(format!(
            "the proof claims governance anchor epoch {}, and this node pins epoch {}: a lock \
             anchored at an epoch this node did not attest is refused",
            wire.anchor_epoch, pinned.epoch
        ));
    }
    // ── ⚑ The rotation refusal. See `SolanaLockProofWire::rotation_steps`.
    if wire.rotation_steps != 0 {
        return Err(format!(
            "the proof declares {} epoch-rotation step(s) between the governance-pinned table and \
             the table it folds. The rotation chain is hand-written Rust \
             (`solana_trustless.rs:587`) and nothing proves it, so this consumer REFUSES the \
             rotated case instead of verifying a STARK whose anchor reached the pin through an \
             unproven loop",
            wire.rotation_steps
        ));
    }
    // ── ⚑⚑ REFUSAL 5: the published anchor root IS the governance-pinned table.
    for j in 0..SOL_ANCHOR_LANES {
        let got = wire.public_inputs[pi_anchor_root(j)];
        let want = pinned.stake_table_lane_root[j];
        if got != want {
            return Err(format!(
                "the proof publishes stake-table anchor lane {j} as {got}; this node's \
                 governance-pinned lane root has {want}. The quorum is proven over SOME table — \
                 this refusal is what makes it the FINALIZED CHAIN'S table"
            ));
        }
    }
    // ── ⚑ REFUSAL 6: the nine bank-root limbs are the recorded bank hash, not a prover's numbers.
    let want_bank = key_lanes_u32(&wire.bank_hash);
    for i in 0..SOL_BANK_ROOT_LIMBS {
        let got = wire.public_inputs[pi_bank_root(i)];
        if got != want_bank[i] {
            return Err(format!(
                "the proof publishes bank-root limb {i} as {got}; the bank hash this lock was \
                 recorded against lanes to {}. The published root must be the observed one",
                want_bank[i]
            ));
        }
    }
    // ── ⚑ REFUSAL 7: the rooted slot is the one the predicate commitment names.
    if wire.public_inputs[SOL_PI_SLOT] != slot {
        return Err(format!(
            "the proof publishes rooted slot {}; the predicate commitment names slot {slot}",
            wire.public_inputs[SOL_PI_SLOT]
        ));
    }
    Ok(())
}

/// ⚑⚑⚑ **THE VERIFIER.** Fail-closed on the governance pin, fail-closed on the descriptor,
/// fail-closed on the program identity, and only then does it spend a STARK.
#[derive(Clone, Debug, Default)]
pub struct SolanaAnchoredLockStarkVerifier {
    pinned: Option<SolanaGovernanceAnchor>,
}

impl SolanaAnchoredLockStarkVerifier {
    /// The verifier with NO governance anchor pinned: every lock is refused at refusal 0.
    ///
    /// This is what `registry_with_real_verifiers()` installs, because `dregg-turn` has no
    /// governance state and the honest behaviour of a consumer that cannot check something is to
    /// refuse it.
    pub fn unwired() -> Self {
        Self::default()
    }

    /// The verifier with a host-injected governance anchor.
    pub fn with_pinned_anchor(pinned: SolanaGovernanceAnchor) -> Self {
        Self {
            pinned: Some(pinned),
        }
    }

    /// Whether this verifier holds a governance anchor at all. Diagnostic only — the REFUSAL is in
    /// `verify`, not in a caller's `if`.
    pub fn is_anchor_pinned(&self) -> bool {
        self.pinned.is_some()
    }
}

impl WitnessedPredicateVerifier for SolanaAnchoredLockStarkVerifier {
    fn name(&self) -> &'static str {
        "solana-anchored-lock-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: solana_lock_predicate_vk(),
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The RECORDED SLOT: the executor resolves it from authoritative state, so it is not the
        // prover's to choose. Carried as the low four bytes of a 32-byte slot value.
        let recorded: [u8; 32] = match input {
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) if b.len() == 32 => {
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::Bytes(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Solana slot, LE in the low 4 bytes)",
                    actual: "non-32-byte Bytes",
                });
            }
            PredicateInput::Sender(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Solana slot, LE in the low 4 bytes)",
                    actual: "Sender",
                });
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Solana slot, LE in the low 4 bytes)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Solana slot, LE in the low 4 bytes)",
                    actual: "SigningMessage",
                });
            }
            PredicateInput::AuthContext { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot (32-byte recorded Solana slot, LE in the low 4 bytes)",
                    actual: "AuthContext",
                });
            }
        };
        let slot = u32::from_le_bytes([recorded[0], recorded[1], recorded[2], recorded[3]]);

        let reject = |reason: String| WitnessedPredicateError::Rejected {
            kind_name: KIND_NAME,
            reason,
        };

        // ── ⚑⚑⚑ REFUSAL 0 — CAPABILITY, CHECKED BEFORE THE BLOB IS DECODED.
        //
        // Whether this node holds a governance-pinned stake table is a property of the NODE, not of
        // the blob. A node with no pin REFUSES. It does not log and proceed, it does not treat "we
        // have no anchor" as "no anchor was required", and it does not spend a STARK first.
        let pinned = self.pinned.as_ref().ok_or_else(|| {
            reject(
                "no governance-pinned Solana stake-table lane root is installed (fail-closed): \
                 this node cannot tell whether a proven quorum is the FINALIZED CHAIN'S quorum, \
                 and therefore refuses the lock. A host that can installs one via \
                 `register_solana_lock_verifier_with_anchor`."
                    .into(),
            )
        })?;

        let wire: SolanaLockProofWire = postcard::from_bytes(proof_bytes).map_err(|e| {
            reject(format!(
                "Solana anchored-lock proof wire did not decode (expected SolanaLockProofWire): {e}"
            ))
        })?;

        // ── ⚑⚑ REFUSAL 1: the predicate commitment. The cell program named WHICH anchor and WHICH
        // slot it demands; the wire's declared halves must re-derive it.
        let want = solana_lock_commitment(&pinned.stake_table_lane_root, slot);
        if &want != commitment {
            return Err(reject(
                "the predicate commitment is not `H(governance lane root ‖ recorded slot)` for \
                 this node's pin and this turn's slot: the cell program is demanding a different \
                 anchor or a different slot than the one being proven"
                    .into(),
            ));
        }

        // ── ⚑ REFUSALS 2-3 and 5-7: the layout, the epoch, the rotation refusal, and the weld of
        // every public input to authoritative state. Spent BEFORE the STARK: comparing the public
        // inputs of a proof that did not verify would be comparing numbers to numbers, but
        // refusing a proof whose public inputs are already wrong costs nothing and names the
        // reason precisely.
        check_public_input_weld(pinned, &wire, slot).map_err(reject)?;

        // ── ⚑⚑ REFUSAL 4 + 8: the descriptor, its identity, and the STARK. Decode + verify under
        // `catch_unwind`: a malformed blob is a fail-closed rejection, never a panic that unwinds
        // through the executor.
        let public_inputs: Vec<BabyBear> = wire
            .public_inputs
            .iter()
            .map(|v| BabyBear::new(*v))
            .collect();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let desc = descriptor_by_name(SOL_LC_VERIFY_DESCRIPTOR).ok_or_else(|| {
                format!(
                    "no descriptor dispatches for {SOL_LC_VERIFY_DESCRIPTOR:?} (fail-closed): this \
                     node cannot check a Solana anchored lock and therefore refuses one"
                )
            })?;
            if desc.public_input_count != SOL_LC_PI_COUNT {
                return Err(format!(
                    "the descriptor served for {SOL_LC_VERIFY_DESCRIPTOR:?} declares {} public \
                     inputs; this consumer's weld layout is {SOL_LC_PI_COUNT}",
                    desc.public_input_count
                ));
            }
            // The program pin, BEFORE the verification is spent.
            check_program_pin(&desc, &SOL_LC_VK_LANES)?;
            verify_vm_descriptor2(&desc, &wire.proof, &public_inputs)
        }));
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(reason)) => Err(reject(format!(
                "the Solana anchored-lock verify STARK rejected: {reason}"
            ))),
            Err(_) => Err(reject(
                "Solana anchored-lock proof decode/verify panicked (treated as rejection)".into(),
            )),
        }
    }
}

/// The verifier as a registry-ready `Arc`, under [`solana_lock_predicate_vk`] — **UNWIRED**.
///
/// It refuses every lock at refusal 0 until a host installs a governance anchor with
/// [`register_solana_lock_verifier_with_anchor`]. That is the honest default: `dregg-turn` holds no
/// governance state, and a verifier that accepts what it cannot check is the fail-open shape.
pub fn solana_lock_verifier() -> Arc<dyn WitnessedPredicateVerifier> {
    Arc::new(SolanaAnchoredLockStarkVerifier::unwired())
}

/// ⚑ **THE HOST WIRING HELPER.** Replace the registry's UNWIRED Solana anchored-lock verifier with
/// one that holds a governance-pinned stake-table lane root.
///
/// The vk is unchanged ([`solana_lock_predicate_vk`]), so a cell program written against the
/// unwired node keeps working — it just stops being refused at refusal 0.
pub fn register_solana_lock_verifier_with_anchor(
    registry: &mut dregg_cell::predicate::WitnessedPredicateRegistry,
    pinned: SolanaGovernanceAnchor,
) {
    registry.register_custom(
        solana_lock_predicate_vk(),
        Arc::new(SolanaAnchoredLockStarkVerifier::with_pinned_anchor(pinned)),
    );
}

#[cfg(test)]
mod tests {
    use super::*;

    /// ⚑⚑ **THE TWO-SOURCE GATE.** [`SOL_LC_VK_LANES`] is entered by hand here; the right-hand side
    /// is blake3 over the descriptor `descriptor_by_name` actually serves, whose bytes Lean pins
    /// with `LightClientSolanaAir.solLcVerifyDesc_emits_golden_json`. Re-emit the AIR without
    /// re-minting this literal (or the reverse) and this test is the red.
    #[test]
    fn the_program_pin_is_the_served_descriptors_fingerprint() {
        let d = descriptor_by_name(SOL_LC_VERIFY_DESCRIPTOR)
            .unwrap_or_else(|| panic!("{SOL_LC_VERIFY_DESCRIPTOR} must dispatch"));
        let fp = effect_vm_descriptor2_semantic_fingerprint(&d).expect("representable");
        let got = key_lanes_u32(&fp);
        assert_eq!(
            got, SOL_LC_VK_LANES,
            "the served light-client descriptor fingerprints to {got:?}; re-mint SOL_LC_VK_LANES \
             and say so in the commit"
        );
    }

    /// The pin REFUSES the stake-table fold — the program the survey proposed as a sub-proof. This
    /// is also the standing record that the two are distinct objects.
    #[test]
    fn the_stake_table_fold_is_refused_by_the_light_clients_program_pin() {
        let fold = descriptor_by_name(SOL_STAKE_FOLD_DESCRIPTOR)
            .unwrap_or_else(|| panic!("{SOL_STAKE_FOLD_DESCRIPTOR} must dispatch"));
        let e = check_program_pin(&fold, &SOL_LC_VK_LANES)
            .expect_err("the fold is NOT the light client and the pin must say so");
        assert!(e.contains("fingerprints to"), "got: {e}");
        assert_eq!(fold.public_input_count, 12, "the fold's PI arity");
    }

    /// ⚑ The light client's PI arity is the layout this consumer welds against. A descriptor whose
    /// arity moved would have this consumer reading the anchor block off the wrong offsets.
    #[test]
    fn the_served_light_client_has_the_welded_pi_arity() {
        let d = descriptor_by_name(SOL_LC_VERIFY_DESCRIPTOR).expect("served");
        assert_eq!(d.public_input_count, SOL_LC_PI_COUNT);
        assert_eq!(d.trace_width, 79, "LightClientSolanaAir.SOL_LC_WIDTH");
    }
}
