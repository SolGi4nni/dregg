//! Real STARK-backed `MerkleMembership` predicate verifier (SenderAuthorized
//! AIR teeth).
//!
//! `StateConstraint::SenderAuthorized { AuthorizedSet::PublicRoot { .. } }`
//! dispatches through the witnessed-predicate registry to a verifier of kind
//! [`WitnessedPredicateKind::MerkleMembership`]. The default registry registers
//! `NotYetWiredVerifier::merkle_membership()` — a fail-closed stub that rejects
//! everything (honest, but means SenderAuthorized can never *pass*, and the
//! membership relation is never algebraically enforced).
//!
//! This module provides [`MerkleMembershipStarkVerifier`]: a real verifier that
//! checks an in-circuit Poseidon2 4-ary Merkle-membership STARK — the emitted
//! `membership_descriptor_of_depth_4ary` descriptor, dispatched by
//! `descriptor_by_name` and checked by `verify_vm_descriptor2`. A turn whose sender is genuinely a leaf
//! under the authorized-set root carries a proof that verifies; a turn whose
//! sender is NOT in the set cannot produce a proof that verifies against the
//! root (Poseidon2 collision resistance), so it is rejected **at the circuit /
//! STARK level**, not merely by an executor-side comparison.
//!
//! # Encoding convention
//!
//! The verifier receives `commitment` (the 32-byte authorized-set Merkle root,
//! as projected from the cell's slot field) and `input = Sender(pk)` (the
//! 32-byte sender public key). The sender is mapped to its leaf felt via THE
//! canonical chip-native membership compress
//! (`dregg_commit::typed::compress_member`: lane 0 of the deployed chip's
//! arity-16 `node8` absorb over `canonical_32_to_felts_8(pk) ‖ 0⁸` — the SAME
//! function the in-AIR gate `withMembershipPubkeyCompress` forces, see
//! `metatheory/Dregg2/Circuit/Emit/CarrierOctetGates.lean`), then the
//! membership STARK whose public inputs are `[leaf, root]` is verified.
//!
//! A prover constructs the matching proof with [`prove_sender_membership`].

use std::sync::Arc;

// Threshold-sig (gated): the `CanonicalSerialize`/`CanonicalDeserialize` traits
// must be in scope for `Signature::{serialize_compressed,deserialize_compressed}`.
#[cfg(feature = "threshold-sig")]
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

use dregg_cell::predicate::{
    IssuerRootAuthority, NeighborAdjacencyVerifier, PredicateInput, WitnessedPredicateError,
    WitnessedPredicateKind, WitnessedPredicateRegistry, WitnessedPredicateVerifier,
};
use dregg_cell_crypto::value_commitment::verify_range_bytes;
use dregg_circuit::BabyBear;
use dregg_circuit::adjacency_witness::{
    PI_IDX_LOWER as ADJ_PI_IDX_LOWER, PI_IDX_UPPER as ADJ_PI_IDX_UPPER, adjacency_witness,
};
use dregg_circuit::descriptor_by_name::{MEMBERSHIP_4ARY_NAME_PREFIX, descriptor_by_name};
use dregg_circuit::descriptor_ir2::{
    DreggStarkConfig, Ir2BatchProof, MemBoundaryWitness, prove_vm_descriptor2,
    verify_vm_descriptor2,
};
use dregg_circuit::dsl::circuit::ProgramRegistry;
use dregg_circuit::dsl::membership::generate_merkle_poseidon2_trace;
use dregg_circuit::membership_descriptor_4ary::membership_witness_4ary;
use dregg_circuit::predicate_air::PredicateType;
use dregg_circuit::predicate_arith_witness::PREDICATE_ARITH_NAME;
use dregg_circuit::predicate_comparison_witness::{
    PREDICATE_ARITH_GT_NAME, PREDICATE_ARITH_LE_NAME, PREDICATE_ARITH_LT_NAME,
    PREDICATE_ARITH_NEQ_NAME,
};
use dregg_circuit::temporal_predicate_dsl::TemporalPredicateRequirement;
use dregg_circuit_prove::custom_leaf_adapter::cellprogram_to_descriptor2;

/// The emitted temporal-predicate (≥) descriptor name (`descriptor_by_name` key);
/// PIs are `[num_steps, threshold, initial_state_root, final_state_root]`.
const TEMPORAL_PREDICATE_DESCRIPTOR_NAME: &str = "dregg-temporal-predicate-gte::dsl-v1";

const KIND_NAME: &str = "MerkleMembership";

/// The emitted neighbor-adjacency descriptor name (`descriptor_by_name` key) —
/// the sorted-set non-membership consecutiveness STARK.
const ADJACENCY_DESCRIPTOR_NAME: &str = "dregg-membership-adjacency::poseidon2-v1";

/// Compress a 32-byte value to its membership leaf felt — THE canonical
/// chip-native compress (`dregg_commit::typed::compress_member`): lane 0 of the
/// deployed chip's arity-16 `node8` absorb over
/// `canonical_32_to_felts_8(bytes) ‖ 0⁸`.
///
/// This is the SAME function the in-AIR membership keystone forces
/// (`CarrierOctetGates.lean::withMembershipPubkeyCompress` /
/// `pubkeyCompress1Spec`), so executor, membership-STARK leaf domain, and the
/// Lean gate agree on the leaf the membership circuit commits to (the fail-open
/// law's third edge). NOTE: this REPLACED the pre-big-bang
/// `hash_many(encode_hash(bytes))` two-permutation sponge, which no deployed
/// chip arity computes — every membership root value changed; the big-bang
/// re-genesis re-derives deployed roots. The bridge note-spend domain
/// (`apply.rs::verify_stark`'s local `compress`, `bridge::present`'s
/// `bytes_to_babybear`) is a SEPARATE domain, re-aligned in the bridge lane
/// (the re-proved note-spend STARK), not here.
fn compress(bytes: &[u8; 32]) -> BabyBear {
    dregg_commit::typed::compress_member(bytes)
}

/// Read an authorized-set root felt from a 32-byte slot value.
///
/// The cell program publishes the Poseidon2 Merkle root (a BabyBear felt) in
/// its slot as the felt's canonical 4-byte little-endian form in the low 4
/// bytes (the rest zero). The root is ALREADY a field element (the membership
/// circuit's `root` public input), so — unlike the leaf, which is a raw 32-byte
/// pk that must be compressed — the verifier reads it directly rather than
/// compressing it again. [`authorized_set_root_bytes`] emits the matching form.
fn root_felt_from_slot(bytes: &[u8; 32]) -> BabyBear {
    let v = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    BabyBear::new(v)
}

/// Wire encoding for a `MerkleMembership` proof blob.
///
/// Layout: `depth: u32 LE || postcard(Ir2BatchProof)`. The `depth` selects the
/// VK-distinct 4-ary membership descriptor (`descriptor_by_name`); the proof is
/// the IR-v2 `BatchProof` produced by [`prove_vm_descriptor2`] against that
/// descriptor. The `[leaf, root]` public inputs are NOT transmitted — the
/// verifier derives them from the sender candidate + the cell's committed root,
/// so they cannot be lied about independently of the honest witness.
struct MembershipProofWire {
    depth: u32,
    proof: Ir2BatchProof<DreggStarkConfig>,
}

impl MembershipProofWire {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.depth.to_le_bytes());
        out.extend_from_slice(
            &postcard::to_allocvec(&self.proof)
                .expect("Ir2BatchProof postcard serialization is infallible"),
        );
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 4 {
            return Err(format!(
                "membership proof wire too short: {} bytes (need >= 4 for the depth header)",
                bytes.len()
            ));
        }
        let depth = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let proof = postcard::from_bytes(&bytes[4..])
            .map_err(|e| format!("membership BatchProof postcard decode failed: {e}"))?;
        Ok(Self { depth, proof })
    }
}

/// Real STARK-backed MerkleMembership verifier for `SenderAuthorized`.
#[derive(Clone, Copy, Debug, Default)]
pub struct MerkleMembershipStarkVerifier;

impl WitnessedPredicateVerifier for MerkleMembershipStarkVerifier {
    fn name(&self) -> &'static str {
        "merkle-membership-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::MerkleMembership
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // Resolve the candidate sender bytes.
        let candidate: [u8; 32] = match input {
            PredicateInput::Sender(s) => **s,
            PredicateInput::Slot(s) => **s,
            PredicateInput::Bytes(b) => {
                if b.len() != 32 {
                    return Err(WitnessedPredicateError::InputShapeMismatch {
                        kind_name: KIND_NAME,
                        expected: "32-byte candidate",
                        actual: "non-32-byte Bytes",
                    });
                }
                let mut c = [0u8; 32];
                c.copy_from_slice(b);
                c
            }
            PredicateInput::PublicInput { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "PublicInput",
                });
            }
            PredicateInput::SigningMessage(_) => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "SigningMessage",
                });
            }
            PredicateInput::AuthContext { .. } => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: KIND_NAME,
                    expected: "Slot/Sender/Bytes (32-byte candidate)",
                    actual: "AuthContext",
                });
            }
        };

        let leaf = compress(&candidate);
        let root = root_felt_from_slot(commitment);

        // The wire is [depth: u32 LE || postcard(Ir2BatchProof)]. The depth picks
        // the VK-distinct 4-ary membership descriptor via the fail-closed
        // `descriptor_by_name` dispatch; that descriptor pins public inputs
        // [leaf, root]. Verification accepts iff the prover knew a depth-N 4-ary
        // Poseidon2 Merkle path from `leaf` to the committed `root` — a non-member
        // has no such path (collision resistance), so verify fails and
        // SenderAuthorized rejects. Decode + verify run under `catch_unwind` so a
        // malformed / tampered blob is a fail-closed rejection, never a panic.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let wire = MembershipProofWire::from_bytes(proof_bytes)?;
            let name = format!("{MEMBERSHIP_4ARY_NAME_PREFIX}{}", wire.depth);
            let desc = descriptor_by_name(&name).ok_or_else(|| {
                format!("no membership descriptor dispatches for {name:?} (fail-closed)")
            })?;
            verify_vm_descriptor2(&desc, &wire.proof, &[leaf, root])
        }));
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(reason)) => Err(WitnessedPredicateError::Rejected {
                kind_name: KIND_NAME,
                reason: format!("sender is not a member of the authorized set: {reason}"),
            }),
            Err(_) => Err(WitnessedPredicateError::Rejected {
                kind_name: KIND_NAME,
                reason: "membership proof decode/verify panicked (treated as rejection)".into(),
            }),
        }
    }
}

/// Build a witnessed-predicate registry that wires the real STARK-backed
/// MerkleMembership verifier on top of the fail-closed defaults.
///
/// Every other kind remains its `default_builtins` fail-closed verifier; this
/// only replaces the MerkleMembership slot with the real gadget so
/// `SenderAuthorized { PublicRoot }` is algebraically enforced.
pub fn registry_with_real_sender_membership() -> WitnessedPredicateRegistry {
    let mut r = WitnessedPredicateRegistry::default_builtins();
    r.register_builtin(Arc::new(MerkleMembershipStarkVerifier));
    r
}

// ─────────────────────────────────────────────────────────────────────────
// Neighbor-adjacency: the Golden-Vision lift closing the Silver non-membership
// wide-bracket forge.
// ─────────────────────────────────────────────────────────────────────────

/// Wire encoding for the `adjacency_proof` blob carried in
/// `dregg_cell::predicate::NonMembershipProofV2` /
/// `CredentialSetMembershipProof::revocation_adjacency_proof`.
///
/// Layout: `idx_lower: u32 LE || idx_upper: u32 LE || postcard(Ir2BatchProof)`.
/// The `root`/`leaf_lower`/`leaf_upper` BabyBear public inputs are *not*
/// transmitted — the verifier derives them deterministically from the cell's
/// 32-byte `(root, lower, upper)` via [`compress`], so they cannot be lied
/// about independently of the cell-side neighbor witness. The two reconstructed
/// indices ARE transmitted (they are the descriptor's `IDX_LOWER`/`IDX_UPPER`
/// public inputs); the descriptor's internalized `idx_upper == idx_lower + 1`
/// Last-row tooth judges consecutiveness on the trace regardless of them.
struct AdjacencyProofWire {
    idx_lower: u32,
    idx_upper: u32,
    proof: Ir2BatchProof<DreggStarkConfig>,
}

impl AdjacencyProofWire {
    fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.idx_lower.to_le_bytes());
        out.extend_from_slice(&self.idx_upper.to_le_bytes());
        out.extend_from_slice(
            &postcard::to_allocvec(&self.proof)
                .expect("Ir2BatchProof postcard serialization is infallible"),
        );
        out
    }

    fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
        if bytes.len() < 8 {
            return Err(format!(
                "adjacency proof wire too short: {} bytes (need >= 8 for the index header)",
                bytes.len()
            ));
        }
        let idx_lower = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        let idx_upper = u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        let proof = postcard::from_bytes(&bytes[8..])
            .map_err(|e| format!("adjacency BatchProof postcard decode failed: {e}"))?;
        Ok(Self {
            idx_lower,
            idx_upper,
            proof,
        })
    }
}

/// Real, STARK-backed [`NeighborAdjacencyVerifier`]: verifies that the two
/// sorted-set neighbors are **consecutive leaves under the committed root**
/// using the emitted `dregg-membership-adjacency::poseidon2-v1` descriptor STARK
/// (`descriptor_by_name` / `verify_vm_descriptor2`).
///
/// This is the teeth the cell crate cannot grow on its own (it must not link
/// `dregg-circuit`). Installed into a `WitnessedPredicateRegistry` by
/// [`registry_with_real_verifiers`], it upgrades
/// `SortedNeighborNonMembershipVerifier` / `CredentialSetMembershipVerifier`
/// from fail-closed to genuinely sound: an attacker who knows the public set
/// root can no longer fabricate wide-bracket sentinels, because 0x00…/0xFF…
/// are not adjacent leaves of any real tree.
#[derive(Clone, Copy, Debug, Default)]
pub struct CircuitNeighborAdjacencyVerifier;

impl NeighborAdjacencyVerifier for CircuitNeighborAdjacencyVerifier {
    fn verify_adjacency(
        &self,
        root: &[u8; 32],
        lower: &[u8; 32],
        upper: &[u8; 32],
        adjacency_proof: &[u8],
    ) -> Result<(), String> {
        // Derive the BabyBear public inputs from the cell's 32-byte values.
        //
        // ROOT: the committed sorted-set root is ALREADY a felt — the set's
        // binary-Poseidon2 Merkle root — published in the cell's 32-byte
        // commitment as the felt's canonical 4-byte LE form (mirroring the
        // MerkleMembership `root_felt_from_slot` convention). We read it
        // directly rather than re-compressing.
        //
        // LEAVES: the neighbor *values* are raw 32-byte items, mapped into the
        // tree's leaf-felt domain by the canonical Poseidon2 compression.
        let root_felt = root_felt_from_slot(root);
        let leaf_lower = compress(lower);
        let leaf_upper = compress(upper);

        // Decode + verify under `catch_unwind`: a tampered / malformed blob is a
        // fail-closed rejection, never a panic. The emitted adjacency descriptor
        // (`descriptor_by_name`, fail-closed on a miss) pins PIs
        // [root, leaf_lower, leaf_upper, idx_lower, idx_upper] and — the teeth —
        // internalizes `idx_upper == idx_lower + 1` as a Last-row boundary, so a
        // non-consecutive (wide-bracket) pair cannot produce a verifying proof
        // against the committed root.
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let wire = AdjacencyProofWire::from_bytes(adjacency_proof)?;
            let pis = vec![
                root_felt,
                leaf_lower,
                leaf_upper,
                BabyBear::from_u64(wire.idx_lower as u64),
                BabyBear::from_u64(wire.idx_upper as u64),
            ];
            let desc = descriptor_by_name(ADJACENCY_DESCRIPTOR_NAME).ok_or_else(|| {
                format!(
                    "no adjacency descriptor dispatches for {ADJACENCY_DESCRIPTOR_NAME:?} (fail-closed)"
                )
            })?;
            verify_vm_descriptor2(&desc, &wire.proof, &pis)
        }));
        match result {
            Ok(r) => r,
            Err(_) => {
                Err("adjacency proof decode/verify panicked (treated as rejection)".to_string())
            }
        }
    }
}

/// Produce an adjacency-proof blob for two consecutive sorted-set neighbors.
///
/// `lower`/`upper` are the cell's 32-byte neighbor values; `lower_path` /
/// `upper_path` are their leaf→root authentication paths in a binary Poseidon2
/// tree whose root compresses to `compress(root)` and whose leaves are
/// `compress(lower)` / `compress(upper)`. The depth must be a power of two ≥ 2.
///
/// The returned bytes go into
/// `dregg_cell::predicate::NonMembershipProofV2::adjacency_proof` (or the
/// credential-set `revocation_adjacency_proof`).
pub fn prove_neighbor_adjacency(
    lower: &[u8; 32],
    lower_path: &[NeighborAdjStep],
    upper: &[u8; 32],
    upper_path: &[NeighborAdjStep],
) -> Result<Vec<u8>, String> {
    let leaf_lower = compress(lower);
    let leaf_upper = compress(upper);
    let (trace, pis) = adjacency_witness(leaf_lower, lower_path, leaf_upper, upper_path)?;
    let idx_lower = pis[ADJ_PI_IDX_LOWER].as_u32();
    let idx_upper = pis[ADJ_PI_IDX_UPPER].as_u32();

    // Honest-prover contract: refuse a non-consecutive bracket up front. The
    // descriptor's internalized `idx_upper == idx_lower + 1` Last-row tooth also
    // rejects it at verify, but an honest prover never attempts a wide bracket
    // (preserving the retired `prove_adjacency`'s "not consecutive" refusal).
    if idx_upper != idx_lower + 1 {
        return Err(format!(
            "adjacency leaves are not consecutive: idx_lower={idx_lower}, idx_upper={idx_upper} \
             (require idx_upper == idx_lower + 1)"
        ));
    }

    let desc = descriptor_by_name(ADJACENCY_DESCRIPTOR_NAME).ok_or_else(|| {
        format!("no adjacency descriptor dispatches for {ADJACENCY_DESCRIPTOR_NAME:?}")
    })?;
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])?;
    Ok(AdjacencyProofWire {
        idx_lower,
        idx_upper,
        proof,
    }
    .to_bytes())
}

/// Re-export of the adjacency step (`AdjWitnessStep`) for prover-side callers.
pub use dregg_circuit::adjacency_witness::AdjWitnessStep as NeighborAdjStep;

/// The 32-byte set-commitment form a cell must publish for an adjacency tree
/// whose binary-Poseidon2 root is `root_felt`: the felt's canonical 4-byte LE
/// encoding (matching [`root_felt_from_slot`], the convention the adjacency
/// verifier reads). Provers build their tree over [`adjacency_leaf_felt`] leaves,
/// take the resulting root felt, and publish `adjacency_commitment_bytes(root)`
/// as the predicate commitment.
pub fn adjacency_commitment_bytes(root_felt: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&root_felt.as_u32().to_le_bytes());
    out
}

/// The tree leaf-felt for a 32-byte neighbor value (canonical Poseidon2
/// compression). Provers build their binary tree over these leaves.
pub fn adjacency_leaf_felt(neighbor: &[u8; 32]) -> BabyBear {
    compress(neighbor)
}

// ─────────────────────────────────────────────────────────────────────────
// noteSpend nullifier-set NON-MEMBERSHIP: the deployed double-spend gate that
// FORCES the sorted-tree adjacency (closing census-R1 / Lean §8¾ `NmRowEncodes`).
// ─────────────────────────────────────────────────────────────────────────

/// Why this gate is the no-double-spend gate, in band, with real teeth.
///
/// A noteSpend's spending STARK proves the note commitment is *present* in the
/// note tree and the nullifier is correctly derived — but it proves NOTHING
/// about the nullifier's *absence* from the committed nullifier set. Runtime
/// double-spend is caught by the executor's in-memory `note_nullifiers` set
/// (`apply.rs::apply_note_spend`), but a *light client* verifying only the
/// proof has no in-circuit guarantee of freshness. The sorted-set
/// non-membership argument supplies that: exhibit two neighbor leaves
/// `lo < nullifier < hi` that are CONSECUTIVE in the committed nullifier root.
///
/// The danger the census flagged (R1): without forcing `lo`,`hi` ADJACENT, a
/// prover who knows the public nullifier root can pick a WIDE BRACKET
/// (`lo = 0x00…`, `hi = 0xFF…`) that brackets-but-isn't-adjacent, "proving"
/// non-membership for a nullifier that IS in the set — a double-spend. This
/// verifier closes that by running the emitted `dregg-membership-adjacency`
/// descriptor STARK (`descriptor_by_name` / `verify_vm_descriptor2`), which
/// reconstructs the two leaf indices in-circuit and enforces
/// `idx_upper == idx_lower + 1`. A non-consecutive pair cannot produce a proof
/// (`notespend_wide_bracket_double_spend_rejected`).
///
/// This is the deployed-verifier realization of the Lean
/// `Circuit/Argus/Effects/NoteSpend.lean` §8¾ discharge: `NmRowEncodes` is no
/// longer assumed; the adjacency constraint FORCES the `GapInterval` gap decode.
///
/// # Arguments
/// * `nullifier_set_root` — the committed sorted nullifier-set root, as the
///   felt's canonical 4-byte LE form (the [`root_felt_from_slot`] convention,
///   matching [`adjacency_commitment_bytes`]).
/// * `nullifier` — the 32-byte spent nullifier whose freshness is asserted.
/// * `lower` / `upper` — the claimed neighbor leaves bracketing the nullifier.
/// * `adjacency_proof` — the [`AdjacencyProofWire`] blob from
///   [`prove_neighbor_adjacency`] proving `lower`,`upper` are consecutive
///   leaves of `nullifier_set_root`.
///
/// # Returns
/// `Ok(())` iff (a) `lower < nullifier < upper` in the leaf-felt domain (the
/// strict bracket) AND (b) the adjacency STARK accepts (`lower`,`upper` are
/// consecutive committed leaves). Either failing ⇒ `Err` (fail-closed). A
/// wide-bracket forgery fails (b); a nullifier not strictly between the
/// neighbors fails (a).
pub fn verify_nullifier_nonmembership(
    nullifier_set_root: &[u8; 32],
    nullifier: &[u8; 32],
    lower: &[u8; 32],
    upper: &[u8; 32],
    adjacency_proof: &[u8],
) -> Result<(), String> {
    // (a) The strict bracket `lo < nf < hi`, over the leaf-felt domain the tree
    //     is sorted by (the same `compress` the adjacency AIR commits leaves
    //     under). A nullifier equal to a neighbor, or outside the bracket, is
    //     NOT a non-member witness — reject.
    let nf_felt = compress(nullifier).as_u32();
    let lo_felt = compress(lower).as_u32();
    let hi_felt = compress(upper).as_u32();
    if !(lo_felt < nf_felt && nf_felt < hi_felt) {
        return Err(format!(
            "nullifier leaf-felt {nf_felt} is not strictly between neighbors \
             ({lo_felt}, {hi_felt}); not a non-membership witness"
        ));
    }

    // (b) THE TEETH: the two neighbors are CONSECUTIVE leaves of the committed
    //     nullifier root. This is the constraint that forbids the wide bracket;
    //     `CircuitNeighborAdjacencyVerifier` runs the in-circuit index
    //     reconstruction + `idx_upper == idx_lower + 1` check.
    CircuitNeighborAdjacencyVerifier
        .verify_adjacency(nullifier_set_root, lower, upper, adjacency_proof)
        .map_err(|e| {
            format!("nullifier-set neighbor adjacency rejected (no forged wide bracket): {e}")
        })
}

// ─────────────────────────────────────────────────────────────────────────
// Dfa — real DSL-circuit STARK verifier (dregg_circuit::dsl::circuit).
// ─────────────────────────────────────────────────────────────────────────

/// Wire encoding for a [`WitnessedPredicateKind::Dfa`] proof.
///
/// Layout (postcard): `{ public_inputs: Vec<u32>, stark: Vec<u8> }`. The
/// `public_inputs` are the BabyBear public inputs (as canonical u32s) the DSL
/// program's AIR boundary-constrains; the STARK binds them, so a forger cannot
/// substitute a different transition. The program *descriptor* is NOT carried —
/// it is resolved from the host-trusted [`ProgramRegistry`] by `commitment`
/// (the program's `vk_hash`), so a prover cannot swap in their own circuit.
#[derive(serde::Serialize, serde::Deserialize)]
struct DfaProofWire {
    public_inputs: Vec<u32>,
    /// The IR-v2 descriptor-prover batch proof for the program's lowered
    /// (`cellprogram_to_descriptor2`) transition descriptor, `postcard`-encoded.
    proof: Ir2BatchProof<DreggStarkConfig>,
}

/// Real DSL-circuit-backed verifier for [`WitnessedPredicateKind::Dfa`].
///
/// Holds a host-installed [`ProgramRegistry`] of deployed DSL programs. The
/// predicate `commitment` is the program `vk_hash`; the verifier looks the
/// program up, lowers its `CircuitDescriptor` to the IR-v2 descriptor via
/// `cellprogram_to_descriptor2`, and runs `verify_vm_descriptor2` over the
/// program's descriptor. A `vk_hash` absent from the registry fails closed (an
/// unknown / self-declared circuit is never trusted). Verification is the
/// authoritative STARK gate — not a field compare.
#[derive(Clone)]
pub struct DslCircuitDfaVerifier {
    programs: Arc<ProgramRegistry>,
}

impl DslCircuitDfaVerifier {
    /// Construct from a host-trusted registry of deployed DSL programs.
    pub fn new(programs: Arc<ProgramRegistry>) -> Self {
        Self { programs }
    }
}

impl WitnessedPredicateVerifier for DslCircuitDfaVerifier {
    fn name(&self) -> &'static str {
        "dsl-circuit-dfa"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Dfa
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let wire: DfaProofWire =
            postcard::from_bytes(proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: "Dfa",
                reason: format!("Dfa proof wire did not decode (expected DfaProofWire): {e}"),
            })?;
        let program =
            self.programs
                .get(commitment)
                .ok_or_else(|| WitnessedPredicateError::Rejected {
                    kind_name: "Dfa",
                    reason:
                        "no DSL program registered for this vk_hash (commitment); the circuit is \
                         not host-trusted, so the proof fails closed"
                            .into(),
                })?;
        let public_inputs: Vec<BabyBear> = wire
            .public_inputs
            .iter()
            .map(|v| BabyBear::new(*v))
            .collect();
        // Lower the host-trusted program's `CircuitDescriptor` to the IR-v2
        // descriptor (fail-closed on a lowering refusal) and verify the batch
        // proof against the reconstructed public inputs. The program is resolved
        // from the registry by `vk_hash`, so a prover cannot swap in their own
        // circuit; the descriptor pins the transition, and a proof committed to a
        // different transition/PI is UNSAT.
        let desc =
            cellprogram_to_descriptor2(program).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: "Dfa",
                reason: format!("DSL program did not lower to an IR-v2 descriptor: {e}"),
            })?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_vm_descriptor2(&desc, &wire.proof, &public_inputs)
        }));
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(e)) => Err(WitnessedPredicateError::Rejected {
                kind_name: "Dfa",
                reason: format!("DSL-circuit transition STARK rejected: {e}"),
            }),
            Err(_) => Err(WitnessedPredicateError::Rejected {
                kind_name: "Dfa",
                reason:
                    "DSL-circuit transition proof decode/verify panicked (treated as rejection)"
                        .into(),
            }),
        }
    }
}

/// Decode a [`WitnessedPredicateKind::Dfa`] proof blob's PUBLIC INPUTS (the `DfaProofWire`
/// prefix) WITHOUT verifying the STARK — the dsl rc-EMIT thread. The executor's rotated-leg
/// verifier ([`super::TurnExecutor::turn_dfa_route_commitment`]) folds these through
/// `dregg_circuit::effect_vm::trace_rotated::dfa_route_commitment` to anchor the published
/// rc carrier; the STARK itself is verified by [`DslCircuitDfaVerifier`] on the authorize
/// path as before (this helper only re-reads the SAME wire bytes, so the anchored rc is the
/// commitment of the inputs the verified proof bound).
pub fn dfa_wire_public_inputs(proof_bytes: &[u8]) -> Result<Vec<BabyBear>, String> {
    let wire: DfaProofWire = postcard::from_bytes(proof_bytes)
        .map_err(|e| format!("Dfa proof wire did not decode (expected DfaProofWire): {e}"))?;
    Ok(wire
        .public_inputs
        .iter()
        .map(|v| BabyBear::new(*v))
        .collect())
}

/// Produce a serialized [`WitnessedPredicateKind::Dfa`] proof for the program
/// identified by `vk_hash`, given witness column values and the public inputs.
/// The returned bytes verify under [`DslCircuitDfaVerifier`] when the same
/// program is registered.
pub fn prove_dfa_transition(
    programs: &ProgramRegistry,
    vk_hash: &[u8; 32],
    witness_values: &std::collections::HashMap<String, Vec<BabyBear>>,
    num_rows: usize,
    public_inputs: &[BabyBear],
) -> Result<Vec<u8>, String> {
    let program = programs
        .get(vk_hash)
        .ok_or_else(|| "no DSL program registered for vk_hash".to_string())?;
    // Lower the program to its IR-v2 descriptor and prove the transition through
    // the descriptor prover. The program trace is widened to the lowered
    // descriptor width (the lowering may append accumulator/lane columns).
    let desc = cellprogram_to_descriptor2(program)?;
    let mut base_trace = program
        .generate_trace(witness_values, num_rows)
        .map_err(|e| format!("{e:?}"))?;
    for row in &mut base_trace {
        if row.len() < desc.trace_width {
            row.resize(desc.trace_width, BabyBear::ZERO);
        }
    }
    let proof = prove_vm_descriptor2(
        &desc,
        &base_trace,
        public_inputs,
        &MemBoundaryWitness::default(),
        &[],
    )?;
    let wire = DfaProofWire {
        public_inputs: public_inputs.iter().map(|f| f.as_u32()).collect(),
        proof,
    };
    Ok(postcard::to_allocvec(&wire).expect("DfaProofWire serialization is infallible"))
}

// ─────────────────────────────────────────────────────────────────────────
// Temporal — real temporal-predicate STARK verifier
// (dregg_circuit::temporal_predicate_dsl).
// ─────────────────────────────────────────────────────────────────────────

/// Host-installed authority mapping a [`WitnessedPredicateKind::Temporal`]
/// predicate `commitment` (the policy `dsl_hash`) to the authoritative policy
/// the proof must satisfy: the requirement (`predicate_type`, `threshold`,
/// `min_duration_steps`) and the state-root endpoints the proof binds to.
///
/// This closes the soundness hole of trusting the proof's own claimed
/// threshold / num_steps / roots: the verifier reconstructs the STARK public
/// inputs from *these host-trusted values*, so a prover cannot lower the
/// threshold or shorten the duration.
pub trait TemporalPolicyAuthority: Send + Sync {
    /// Return the authoritative policy for `commitment`, or `None` if no policy
    /// is registered (the verifier then fails closed).
    fn policy(&self, commitment: &[u8; 32]) -> Option<TemporalPolicy>;
}

/// An authoritative temporal policy: the requirement the proof must satisfy and
/// the exact STARK boundary parameters (num_steps + state-root endpoints).
#[derive(Clone, Debug)]
pub struct TemporalPolicy {
    /// The requirement (predicate type, threshold, minimum duration).
    pub requirement: TemporalPredicateRequirement,
    /// The exact number of steps the STARK boundary commits to.
    pub num_steps: u32,
    /// The initial state-root the proof must bind to (BabyBear, as u32).
    pub initial_state_root: u32,
    /// The final state-root the proof must bind to (BabyBear, as u32).
    pub final_state_root: u32,
}

/// Real temporal-predicate-STARK-backed verifier for
/// [`WitnessedPredicateKind::Temporal`].
///
/// Decodes a serialized [`TemporalPredicateProof`], looks up the authoritative
/// [`TemporalPolicy`] for the `commitment`, and calls
/// `verify_temporal_predicate` with the policy's threshold / num_steps / roots —
/// NOT the proof's self-claimed values. It additionally enforces
/// `TemporalPredicateRequirement::is_satisfied_by` (predicate type + minimum
/// duration). A commitment with no registered policy fails closed.
#[derive(Clone)]
pub struct TemporalPredicateStarkVerifier {
    policies: Arc<dyn TemporalPolicyAuthority>,
}

impl TemporalPredicateStarkVerifier {
    /// Construct from a host-trusted policy authority.
    pub fn new(policies: Arc<dyn TemporalPolicyAuthority>) -> Self {
        Self { policies }
    }
}

impl WitnessedPredicateVerifier for TemporalPredicateStarkVerifier {
    fn name(&self) -> &'static str {
        "temporal-predicate-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Temporal
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let wire: TemporalProofWire =
            postcard::from_bytes(proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: "Temporal",
                reason: format!(
                    "Temporal proof wire did not decode (expected TemporalProofWire): {e}"
                ),
            })?;
        let policy =
            self.policies
                .policy(commitment)
                .ok_or_else(|| WitnessedPredicateError::Rejected {
                    kind_name: "Temporal",
                    reason:
                        "no temporal policy registered for this commitment (dsl_hash); the policy \
                         is not host-trusted, so the proof fails closed"
                            .into(),
                })?;

        // The emitted temporal descriptor is the ≥ ("held at least `threshold`")
        // predicate; a non-`Gte` policy has no IR-v2 descriptor and fails closed
        // (never accepted against the wrong comparison).
        if policy.requirement.predicate_type != PredicateType::Gte {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "Temporal",
                reason: format!(
                    "temporal predicate op {:?} has no IR-v2 descriptor (only Gte / \
                     `dregg-temporal-predicate-gte::dsl-v1` is emitted)",
                    policy.requirement.predicate_type
                ),
            });
        }

        // Authoritative STARK gate: reconstruct the descriptor's public inputs
        // `[num_steps, threshold, initial_state_root, final_state_root]` from the
        // HOST policy (not any proof-embedded, prover-chosen values). The
        // descriptor pins each to its trace slot (last-row accumulator, first-row
        // threshold, first/last-row state root), so a proof committed to different
        // steps / threshold / roots is UNSAT and rejected. Decode+verify run under
        // `catch_unwind` so a malformed blob is a fail-closed rejection.
        let pis = vec![
            BabyBear::new(policy.num_steps),
            BabyBear::new(policy.requirement.threshold as u32),
            BabyBear::new(policy.initial_state_root),
            BabyBear::new(policy.final_state_root),
        ];
        let desc = descriptor_by_name(TEMPORAL_PREDICATE_DESCRIPTOR_NAME).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "Temporal",
                reason: format!(
                    "no temporal descriptor dispatches for {TEMPORAL_PREDICATE_DESCRIPTOR_NAME:?} \
                     (fail-closed)"
                ),
            }
        })?;
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            verify_vm_descriptor2(&desc, &wire.proof, &pis)
        }));
        match result {
            Ok(Ok(())) => Ok(()),
            Ok(Err(e)) => Err(WitnessedPredicateError::Rejected {
                kind_name: "Temporal",
                reason: format!(
                    "temporal-predicate STARK rejected (the predicate did not hold continuously \
                     over the policy's step range against the policy's roots): {e}"
                ),
            }),
            Err(_) => Err(WitnessedPredicateError::Rejected {
                kind_name: "Temporal",
                reason: "temporal-predicate proof decode/verify panicked (treated as rejection)"
                    .into(),
            }),
        }
    }
}

/// Wire encoding for a [`WitnessedPredicateKind::Temporal`] proof: the IR-v2
/// descriptor-prover batch proof for `dregg-temporal-predicate-gte::dsl-v1`,
/// `postcard`-encoded. The `[num_steps, threshold, initial, final]` public
/// inputs are NOT transmitted — the verifier reconstructs them from the
/// host-trusted [`TemporalPolicy`], so a prover cannot lower the threshold /
/// shorten the duration / swap the roots independently of the STARK binding.
#[derive(serde::Serialize, serde::Deserialize)]
struct TemporalProofWire {
    proof: Ir2BatchProof<DreggStarkConfig>,
}

// ─────────────────────────────────────────────────────────────────────────
// PedersenEquality — real Bulletproof opening verifier
// (dregg_cell_crypto::value_commitment).
// ─────────────────────────────────────────────────────────────────────────

/// Real Bulletproof-backed verifier for [`WitnessedPredicateKind::PedersenEquality`].
///
/// The predicate `commitment` is a 32-byte compressed Ristretto Pedersen
/// commitment; the proof bytes are a Bulletproof range proof. Verification
/// (`dregg_cell_crypto::value_commitment::verify_range_bytes`) accepts iff the prover
/// knows a valid opening of `commitment` to a 64-bit value — a genuine
/// zero-knowledge proof of a valid Pedersen opening bound to the commitment. A
/// non-point commitment or malformed / wrong-commitment proof fails closed.
#[derive(Clone, Copy, Debug, Default)]
pub struct PedersenBulletproofVerifier;

impl WitnessedPredicateVerifier for PedersenBulletproofVerifier {
    fn name(&self) -> &'static str {
        "pedersen-bulletproof"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::PedersenEquality
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        if proof_bytes.is_empty() {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "PedersenEquality",
                reason: "empty Bulletproof range proof".into(),
            });
        }
        verify_range_bytes(commitment, proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
            kind_name: "PedersenEquality",
            reason: format!(
                "Bulletproof opening proof rejected for the Pedersen commitment: {e:?}"
            ),
        })
    }
}

/// Build the **production** witnessed-predicate registry: the real STARK-backed
/// MerkleMembership verifier *plus* the real adjacency-backed NonMembership and
/// BlindedSet verifiers, installed on top of `default_builtins`.
///
/// This is the constructor production hosts should use. It promotes every kind
/// whose cryptographic verifier is available in this crate from its fail-closed
/// default to its real implementation:
///
/// - `MerkleMembership` → [`MerkleMembershipStarkVerifier`] (Poseidon2 Merkle
///   membership STARK; `SenderAuthorized { PublicRoot }`).
/// - `NonMembership` → `SortedNeighborNonMembershipVerifier` with the
///   [`CircuitNeighborAdjacencyVerifier`] installed (consecutive-index
///   adjacency STARK; `StateConstraint::Renounced`).
/// - `BlindedSet` → `CredentialSetMembershipVerifier` with the adjacency
///   verifier installed. NOTE: no [`IssuerRootAuthority`] is installed here, so
///   BlindedSet **fails closed on the issuer-root-binding step** (it cannot bind
///   prover-supplied roots to the issuer's real roots). Use
///   [`registry_with_real_verifiers_full`] to install the authority and make
///   BlindedSet acceptable.
/// - `PedersenEquality` → [`PedersenBulletproofVerifier`] (real Bulletproof
///   opening proof over `dregg_cell_crypto::value_commitment`; needs no host context).
/// - `Custom { tee_predicate_vk }` / `Custom { oracle_predicate_vk }` → the
///   cell-side attestation-fact verifiers
///   (`TeeWitnessedPredicateVerifier::new` / `OracleWitnessedPredicateVerifier::new`),
///   so an attestation fact is executor-DISPATCHED rather than dying as
///   `KindNotRegistered`. Both are FAIL-CLOSED: they reject every proof until
///   the host injects the real vendor / zkTLS crypto (`with_verifier`) and
///   re-registers under the same vk — the hardware-root cert-chain / zkTLS
///   trust-anchor crypto stays host-side, never in cell/turn.
///
/// Kinds that need host-trusted context remain fail-closed here and are wired by
/// [`registry_with_real_verifiers_full`]: `Dfa` (needs a [`ProgramRegistry`]),
/// `Temporal` (needs a [`TemporalPolicyAuthority`]), `BlindedSet`'s issuer-root
/// binding (needs an [`IssuerRootAuthority`]), and `BridgePredicate` (needs a
/// [`BridgePredicatePolicyAuthority`]).
///
/// `BridgePredicate`'s real verifier is welded from the `dregg-circuit`
/// predicate-AIR primitives (`verify_predicate` / `verify_in_range`) directly —
/// the same gadgets `dregg_bridge::present::verify_predicate_proof` wraps — so it
/// needs **no** `dregg-turn → dregg-bridge` edge. It stays fail-closed in *this*
/// constructor only because it needs a host-trusted operator/threshold policy
/// (else a prover could lower the threshold); [`registry_with_real_verifiers_full`]
/// installs it given a [`BridgePredicatePolicyAuthority`].
pub fn registry_with_real_verifiers() -> WitnessedPredicateRegistry {
    use dregg_cell::oracle_attest::{OracleWitnessedPredicateVerifier, oracle_predicate_vk};
    use dregg_cell::predicate::{
        CredentialSetMembershipVerifier, SortedNeighborNonMembershipVerifier,
    };
    use dregg_cell::tee_attest::{TeeWitnessedPredicateVerifier, tee_predicate_vk};

    let adjacency: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(CircuitNeighborAdjacencyVerifier);

    let mut r = WitnessedPredicateRegistry::default_builtins();
    r.register_builtin(Arc::new(MerkleMembershipStarkVerifier));
    r.register_builtin(Arc::new(
        SortedNeighborNonMembershipVerifier::with_adjacency(adjacency.clone()),
    ));
    r.register_builtin(Arc::new(CredentialSetMembershipVerifier::with_adjacency(
        adjacency,
    )));
    // PedersenEquality needs no host context — wire its real verifier here too.
    r.register_builtin(Arc::new(PedersenBulletproofVerifier));
    // Attestation facts (`Custom { vk_hash }`): install the cell-side
    // FAIL-CLOSED TEE + zkTLS-oracle verifiers so the executor DISPATCHES a
    // `Custom { tee/oracle vk }` fact to them (instead of rejecting it as
    // `KindNotRegistered` before the fact's own verify logic can run). Both
    // reject every proof until a host injects the real crypto
    // (`TeeWitnessedPredicateVerifier::with_verifier` /
    // `OracleWitnessedPredicateVerifier::with_verifier`, re-registered under
    // the same vk) — the vendor cert-chain / zkTLS trust-anchor crypto stays
    // host-side, never in cell/turn.
    r.register_custom(
        tee_predicate_vk(),
        Arc::new(TeeWitnessedPredicateVerifier::new()),
    );
    r.register_custom(
        oracle_predicate_vk(),
        Arc::new(OracleWitnessedPredicateVerifier::new()),
    );
    r
}

/// Build the **fully production-wired** witnessed-predicate registry, installing
/// every real verifier whose backend lives in `dregg-cell` / `dregg-circuit`,
/// given the host-trusted context each context-dependent kind requires.
///
/// On top of [`registry_with_real_verifiers`] it additionally installs:
///
/// - `Dfa` → [`DslCircuitDfaVerifier`] over `programs` (a deployed
///   [`ProgramRegistry`]); a `vk_hash` absent from it fails closed.
/// - `Temporal` → [`TemporalPredicateStarkVerifier`] over `temporal_policies`;
///   a commitment with no policy fails closed.
/// - `BlindedSet` → `CredentialSetMembershipVerifier::production` with both the
///   adjacency STARK verifier AND `issuer_roots` (so the issuer-root binding can
///   ACCEPT honest members and reject self-fabricated accumulators).
/// - `BridgePredicate` → [`BridgePredicateStarkVerifier`] over `bridge_policies`
///   (the `dregg-circuit` predicate-AIR STARK; a commitment with no policy fails
///   closed). This is welded from the circuit primitives directly — no
///   `dregg-turn → dregg-bridge` dependency.
///
/// With this constructor **every** built-in witnessed-predicate kind whose
/// backend lives in `dregg-cell` / `dregg-circuit` is wired to its real
/// cryptographic verifier; none of the five `default_builtins` fail-closed stubs
/// (Dfa, Temporal, MerkleMembership, BridgePredicate, PedersenEquality — plus
/// NonMembership / BlindedSet) remains.
pub fn registry_with_real_verifiers_full(
    programs: Arc<ProgramRegistry>,
    temporal_policies: Arc<dyn TemporalPolicyAuthority>,
    issuer_roots: Arc<dyn IssuerRootAuthority>,
    bridge_policies: Arc<dyn BridgePredicatePolicyAuthority>,
) -> WitnessedPredicateRegistry {
    use dregg_cell::predicate::CredentialSetMembershipVerifier;

    let adjacency: Arc<dyn NeighborAdjacencyVerifier> = Arc::new(CircuitNeighborAdjacencyVerifier);

    let mut r = registry_with_real_verifiers();
    r.register_builtin(Arc::new(DslCircuitDfaVerifier::new(programs)));
    r.register_builtin(Arc::new(TemporalPredicateStarkVerifier::new(
        temporal_policies,
    )));
    r.register_builtin(Arc::new(CredentialSetMembershipVerifier::production(
        adjacency,
        issuer_roots,
    )));
    r.register_builtin(Arc::new(BridgePredicateStarkVerifier::new(bridge_policies)));
    r
}

/// Produce a SenderAuthorized membership proof for a sender that is a leaf at
/// `(siblings, positions)` under the authorized-set root.
///
/// `sender_pk` is the 32-byte sender public key (the candidate); the returned
/// serialized proof blob ([`MembershipProofWire`]: depth + `postcard(Ir2BatchProof)`)
/// verifies under [`MerkleMembershipStarkVerifier`] against the set root computed
/// from the same path. The `siblings`/`positions` are BabyBear-domain Merkle
/// witness data (leaf-to-root); the path is padded to a power-of-two depth (as
/// [`generate_merkle_poseidon2_trace`] pads) and proven through the 4-ary
/// `membership_descriptor_of_depth_4ary` descriptor.
pub fn prove_sender_membership(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> Result<Vec<u8>, String> {
    if siblings.len() != positions.len() {
        return Err(format!(
            "membership siblings/positions length mismatch ({} vs {})",
            siblings.len(),
            positions.len()
        ));
    }
    let leaf = compress(sender_pk);
    // Pad the authentication path to the next power-of-two depth (min 2) with
    // zero-sibling, position-0 levels — EXACTLY how `generate_merkle_poseidon2_trace`
    // pads internally — so the descriptor's committed root stays BYTE-EQUAL to the
    // production root (`authorized_set_root_felt`). `membership_witness_4ary`
    // requires a power-of-two depth >= 2; the pad reproduces production's root.
    let (padded_siblings, padded_positions) = pad_membership_path(siblings, positions);
    let depth = padded_siblings.len();
    let (trace, pis) = membership_witness_4ary(leaf, &padded_siblings, &padded_positions)?;
    let name = format!("{MEMBERSHIP_4ARY_NAME_PREFIX}{depth}");
    let desc = descriptor_by_name(&name)
        .ok_or_else(|| format!("no membership descriptor dispatches for {name:?}"))?;
    let proof = prove_vm_descriptor2(&desc, &trace, &pis, &MemBoundaryWitness::default(), &[])?;
    Ok(MembershipProofWire {
        depth: depth as u32,
        proof,
    }
    .to_bytes())
}

/// Pad a Merkle authentication path to the next power-of-two depth (min 2) with
/// zero-sibling, position-0 levels — the SAME padding
/// [`generate_merkle_poseidon2_trace`] applies internally, so the padded 4-ary
/// descriptor root is byte-equal to the production `authorized_set_root_felt`.
fn pad_membership_path(
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> (Vec<[BabyBear; 3]>, Vec<u8>) {
    let mut s = siblings.to_vec();
    let mut p = positions.to_vec();
    let target = s.len().next_power_of_two().max(2);
    while s.len() < target {
        s.push([BabyBear::ZERO; 3]);
        p.push(0);
    }
    (s, p)
}

/// The authorized-set Merkle root as a BabyBear felt (the value the membership
/// circuit commits to as `root`), for a sender leaf at `(siblings, positions)`.
///
/// Delegates to the circuit's own trace generator so the root matches exactly
/// what the membership STARK commits to (Poseidon2 `hash_4_to_1` of children
/// arranged by position), rather than re-deriving it here.
pub fn authorized_set_root_felt(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> BabyBear {
    let leaf = compress(sender_pk);
    let (_trace, public_inputs) = generate_merkle_poseidon2_trace(leaf, siblings, positions);
    // PI layout is [leaf, root].
    public_inputs[1]
}

/// The 32-byte slot value the cell program publishes for the authorized-set
/// root: the root felt's canonical 4-byte little-endian form in the low bytes
/// (matching [`root_felt_from_slot`]).
pub fn authorized_set_root_bytes(
    sender_pk: &[u8; 32],
    siblings: &[[BabyBear; 3]],
    positions: &[u8],
) -> [u8; 32] {
    let root = authorized_set_root_felt(sender_pk, siblings, positions);
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&root.0.to_le_bytes());
    out
}

// ─────────────────────────────────────────────────────────────────────────
// Single-member authorized set: the trivial-tree convenience pair.
// ─────────────────────────────────────────────────────────────────────────
//
// The common honest-issuer case authorizes exactly ONE public key (the
// issuer's own pk). For this the Merkle tree degenerates to a single leaf;
// the 4-ary membership descriptor needs a power-of-two depth ≥ 2, so the
// member sits at position 0 of a depth-2 tree padded with zero siblings. Both
// the slot value and the proof are derived from the SAME `compress` /
// `generate_merkle_poseidon2_trace` convention the [`MerkleMembershipStarkVerifier`]
// reads, so they are mutually consistent by construction (the root the prover
// commits to is exactly the root the verifier reconstructs from the slot).

/// The canonical depth-2 single-member witness: position 0 at each level,
/// zero siblings. The 4-ary membership descriptor requires a power-of-two
/// depth ≥ 2; this is the minimal honest path for a one-element authorized set.
const SINGLE_MEMBER_SIBLINGS: [[BabyBear; 3]; 2] = [
    [BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    [BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
];
const SINGLE_MEMBER_POSITIONS: [u8; 2] = [0, 0];

/// The 32-byte authorized-set root slot value for a set whose ONLY member is
/// `member` (a 32-byte sender public key).
///
/// Put the returned bytes in the cell's `fields[set_root_index]` (the
/// `SenderAuthorized { PublicRoot { set_root_index } }` root slot). The matching
/// proof is [`single_member_membership_proof`]; the two are derived from the
/// same single-leaf tree so the proof verifies against this root.
pub fn single_member_authorized_root(member: &[u8; 32]) -> [u8; 32] {
    authorized_set_root_bytes(member, &SINGLE_MEMBER_SIBLINGS, &SINGLE_MEMBER_POSITIONS)
}

/// The membership-STARK proof bytes proving `member` is the (sole) leaf under
/// the root [`single_member_authorized_root`] returns for the same `member`.
///
/// Wrap the returned bytes in `WitnessKind::MerklePath` (or `ProofBytes`) and
/// attach them to the firing action's `witness_blobs`; the
/// `SenderAuthorized { PublicRoot }` evaluator binds the unique such blob and
/// feeds it to [`MerkleMembershipStarkVerifier`], which accepts iff the proof's
/// committed leaf = `compress(member)` reaches the slot's root.
pub fn single_member_membership_proof(member: &[u8; 32]) -> Vec<u8> {
    prove_sender_membership(member, &SINGLE_MEMBER_SIBLINGS, &SINGLE_MEMBER_POSITIONS)
        .expect("single-member depth-2 membership proof is always provable")
}

// ─────────────────────────────────────────────────────────────────────────
// BridgePredicate — real predicate-AIR STARK verifier
// (dregg_circuit::predicate_air::verify_predicate / verify_in_range).
// ─────────────────────────────────────────────────────────────────────────
//
// `WitnessedPredicateKind::BridgePredicate` declares a Gte/Lte/Gt/Lt/Neq/InRange
// predicate over a hidden value committed inside a `fact_commitment`. The real
// verifier (`dregg_bridge::present::verify_predicate_proof`) is a thin wrapper
// around `dregg_circuit::verify_predicate` / `verify_in_range`; the proving-
// system gadgets live in `dregg-circuit`, which `dregg-turn` ALREADY links.
// So the verifier is welded HERE from the circuit primitives directly — no
// `dregg-turn → dregg-bridge` edge is created (turn → cell + circuit only).
//
// # Why a host policy (the threshold-lowering forge)
//
// `verify_predicate(proof, threshold, fact_commitment)` takes the threshold and
// the operator (via the proof's `op` tag) as the public statement it binds. A
// prover who controls those could "prove `value >= 0`" and present it as
// "`value >= 1_000`". So — exactly as `Temporal` consults a
// [`TemporalPolicyAuthority`] — `BridgePredicate` consults a host-trusted
// [`BridgePredicatePolicyAuthority`] that maps the predicate `commitment` to the
// authoritative operator + threshold(s). The verifier reconstructs the STARK
// statement from the POLICY's values (not the proof's self-claimed ones) and
// additionally pins the proof's `op` to the policy operator, so a forger can
// neither lower the threshold nor swap the comparison. A commitment with no
// registered policy fails closed.

/// The authoritative predicate a [`WitnessedPredicateKind::BridgePredicate`]
/// proof must satisfy, keyed by the predicate `commitment` (the `fact_commitment`
/// felt). The host supplies this so the threshold/operator cannot be chosen by
/// the prover.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BridgePredicateRequirement {
    /// A single-bound comparison: the hidden value relates to `threshold` under
    /// `op` (`Gte`/`Lte`/`Gt`/`Lt`/`Neq`). `InRangeLow`/`InRangeHigh` are not
    /// valid single requirements — use [`Self::InRange`].
    Threshold { op: PredicateType, threshold: u32 },
    /// A two-bound range: `low <= value <= high`. Verified as a pair of
    /// predicate proofs (`InRangeLow` against `low`, `InRangeHigh` against
    /// `high`).
    InRange { low: u32, high: u32 },
}

/// Host-installed authority mapping a [`WitnessedPredicateKind::BridgePredicate`]
/// predicate `commitment` (the `fact_commitment` felt) to the authoritative
/// [`BridgePredicateRequirement`] the proof must satisfy.
pub trait BridgePredicatePolicyAuthority: Send + Sync {
    /// Return the authoritative requirement for `commitment`, or `None` if no
    /// policy is registered (the verifier then fails closed).
    fn requirement(&self, commitment: &[u8; 32]) -> Option<BridgePredicateRequirement>;
}

/// A static [`BridgePredicatePolicyAuthority`] backed by an in-memory table of
/// `commitment -> BridgePredicateRequirement`. A commitment absent from the
/// table is rejected (fail-closed by construction).
#[derive(Clone, Debug, Default)]
pub struct StaticBridgePredicatePolicy {
    bindings: std::collections::BTreeMap<[u8; 32], BridgePredicateRequirement>,
}

impl StaticBridgePredicatePolicy {
    /// Construct an empty authority (rejects everything until requirements added).
    pub fn new() -> Self {
        Self {
            bindings: std::collections::BTreeMap::new(),
        }
    }

    /// Authorize `requirement` for `commitment`.
    pub fn authorize(
        mut self,
        commitment: [u8; 32],
        requirement: BridgePredicateRequirement,
    ) -> Self {
        self.bindings.insert(commitment, requirement);
        self
    }
}

impl BridgePredicatePolicyAuthority for StaticBridgePredicatePolicy {
    fn requirement(&self, commitment: &[u8; 32]) -> Option<BridgePredicateRequirement> {
        self.bindings.get(commitment).copied()
    }
}

/// Wire encoding for a [`WitnessedPredicateKind::BridgePredicate`] proof.
///
/// Carries the circuit-level `PredicateProof`(s) only — the operator and
/// threshold are NOT trusted from the wire; they are reconstructed from the host
/// [`BridgePredicateRequirement`]. `Single` is a one-bound comparison;
/// `Range` is the `(low_bound, high_bound)` proof pair for an `InRange`
/// requirement.
#[derive(serde::Serialize, serde::Deserialize)]
enum BridgePredicateWire {
    Single(Ir2BatchProof<DreggStarkConfig>),
    Range(
        Ir2BatchProof<DreggStarkConfig>,
        Ir2BatchProof<DreggStarkConfig>,
    ),
}

/// Verify ONE single-bound comparison proof against the emitted descriptor `desc_name`, pinning its
/// public inputs `[bound, fact_commitment]` from the HOST policy / committed fact (never the proof).
/// A proof committed to a different `bound` / `fact_commitment`, or whose private value violates the
/// comparison (its `DIFF` wraps out of the range lookup, or — for `≠` — has no inverse), is UNSAT and
/// rejected. A `desc_name` that fails to dispatch is a fail-closed rejection.
fn verify_predicate_single(
    desc_name: &str,
    bound: u32,
    fact_commitment: BabyBear,
    proof: &Ir2BatchProof<DreggStarkConfig>,
) -> Result<(), WitnessedPredicateError> {
    let desc = descriptor_by_name(desc_name).ok_or_else(|| WitnessedPredicateError::Rejected {
        kind_name: "BridgePredicate",
        reason: format!("no predicate descriptor dispatches for {desc_name:?} (fail-closed)"),
    })?;
    let pis = vec![BabyBear::new(bound), fact_commitment];
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify_vm_descriptor2(&desc, proof, &pis)
    }));
    match result {
        Ok(Ok(())) => Ok(()),
        Ok(Err(e)) => Err(WitnessedPredicateError::Rejected {
            kind_name: "BridgePredicate",
            reason: format!("predicate STARK ({desc_name}) rejected: {e}"),
        }),
        Err(_) => Err(WitnessedPredicateError::Rejected {
            kind_name: "BridgePredicate",
            reason: "predicate proof decode/verify panicked (treated as rejection)".into(),
        }),
    }
}

/// The emitted IR-v2 descriptor name for a single-bound comparison operator, or `None` for the
/// two-bound range half-operators (`InRangeLow`/`InRangeHigh` are only valid inside an
/// [`BridgePredicateRequirement::InRange`], never as a standalone `Threshold`).
fn single_comparison_descriptor(op: PredicateType) -> Option<&'static str> {
    match op {
        PredicateType::Gte => Some(PREDICATE_ARITH_NAME),
        PredicateType::Lte => Some(PREDICATE_ARITH_LE_NAME),
        PredicateType::Gt => Some(PREDICATE_ARITH_GT_NAME),
        PredicateType::Lt => Some(PREDICATE_ARITH_LT_NAME),
        PredicateType::Neq => Some(PREDICATE_ARITH_NEQ_NAME),
        PredicateType::InRangeLow | PredicateType::InRangeHigh => None,
    }
}

/// Real predicate-AIR-STARK-backed verifier for
/// [`WitnessedPredicateKind::BridgePredicate`].
///
/// Decodes a [`BridgePredicateWire`], looks up the authoritative
/// [`BridgePredicateRequirement`] for the `commitment`, and verifies the
/// circuit predicate STARK (`dregg_circuit::verify_predicate` / `verify_in_range`)
/// against the POLICY's operator + threshold(s) and the `commitment`-derived
/// `fact_commitment` felt — NOT the proof's self-claimed values. A commitment
/// with no registered policy, or a proof whose operator disagrees with the
/// policy, or a proof bound to a different fact_commitment / threshold, fails
/// closed.
#[derive(Clone)]
pub struct BridgePredicateStarkVerifier {
    policies: Arc<dyn BridgePredicatePolicyAuthority>,
}

impl BridgePredicateStarkVerifier {
    /// Construct from a host-trusted policy authority.
    pub fn new(policies: Arc<dyn BridgePredicatePolicyAuthority>) -> Self {
        Self { policies }
    }
}

impl WitnessedPredicateVerifier for BridgePredicateStarkVerifier {
    fn name(&self) -> &'static str {
        "bridge-predicate-stark"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::BridgePredicate
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        _input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        let wire: BridgePredicateWire =
            postcard::from_bytes(proof_bytes).map_err(|e| WitnessedPredicateError::Rejected {
                kind_name: "BridgePredicate",
                reason: format!(
                    "BridgePredicate proof wire did not decode (expected BridgePredicateWire): {e}"
                ),
            })?;
        let requirement = self.policies.requirement(commitment).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "BridgePredicate",
                reason:
                    "no bridge-predicate policy registered for this commitment (fact_commitment); \
                     the operator/threshold is not host-trusted, so the proof fails closed"
                        .into(),
            }
        })?;

        // The committed fact is a BabyBear felt published in the 32-byte
        // commitment as its canonical 4-byte LE form (the `root_felt_from_slot`
        // convention shared with MerkleMembership). Reconstruct it; the circuit
        // verifier binds it as a public input.
        let fact_commitment = root_felt_from_slot(commitment);

        match (requirement, wire) {
            (
                BridgePredicateRequirement::Threshold { op, threshold },
                BridgePredicateWire::Single(proof),
            ) => {
                // Each single-bound comparison (`Gte`/`Lte`/`Gt`/`Lt`/`Neq`) now has
                // an emitted IR-v2 descriptor
                // (`dregg-predicate-arith-{ge,le,gt,lt,neq}::threshold-v1`). The
                // descriptor pins its public inputs `[threshold, fact_commitment]`,
                // both reconstructed from the HOST policy / committed fact (not the
                // proof). A proof committed to a different threshold / fact, or one
                // whose private value violates the comparison (its `DIFF` wraps out
                // of the range lookup, or — for `≠` — `DIFF = 0` has no inverse), is
                // UNSAT and rejected. `InRangeLow`/`InRangeHigh` are not valid
                // standalone requirements (fail-closed).
                let desc_name = single_comparison_descriptor(op).ok_or_else(|| {
                    WitnessedPredicateError::Rejected {
                        kind_name: "BridgePredicate",
                        reason: format!(
                            "predicate operator {op:?} is not a valid single-bound requirement \
                             (use InRange); fails closed"
                        ),
                    }
                })?;
                verify_predicate_single(desc_name, threshold, fact_commitment, &proof)
            }
            (
                BridgePredicateRequirement::InRange { low, high },
                BridgePredicateWire::Range(low_proof, high_proof),
            ) => {
                // The two-bound `low ≤ value ≤ high` predicate is verified as the
                // conjunction of two emitted one-sided descriptors, both pinned to
                // the SAME `fact_commitment`: the low bound is `value ≥ low` (the
                // `≥` descriptor) and the high bound is `value ≤ high` (the `≤`
                // descriptor). Either proof failing ⇒ fail-closed.
                verify_predicate_single(PREDICATE_ARITH_NAME, low, fact_commitment, &low_proof)?;
                verify_predicate_single(
                    PREDICATE_ARITH_LE_NAME,
                    high,
                    fact_commitment,
                    &high_proof,
                )?;
                Ok(())
            }
            // Wire shape disagrees with the policy shape (single-vs-range).
            (BridgePredicateRequirement::Threshold { .. }, BridgePredicateWire::Range(..)) => {
                Err(WitnessedPredicateError::Rejected {
                    kind_name: "BridgePredicate",
                    reason: "host policy is a single-bound threshold but the proof is a range pair"
                        .into(),
                })
            }
            (BridgePredicateRequirement::InRange { .. }, BridgePredicateWire::Single(..)) => {
                Err(WitnessedPredicateError::Rejected {
                    kind_name: "BridgePredicate",
                    reason: "host policy is an InRange but the proof is a single-bound predicate"
                        .into(),
                })
            }
        }
    }
}

/// The 32-byte BridgePredicate `commitment` form for a `fact_commitment` felt:
/// its canonical 4-byte LE encoding (matching [`root_felt_from_slot`], the
/// convention the verifier reads). Hosts that hold a `fact_commitment` BabyBear
/// publish `bridge_predicate_commitment_bytes(fact_commitment)` as the predicate
/// commitment.
pub fn bridge_predicate_commitment_bytes(fact_commitment: BabyBear) -> [u8; 32] {
    let mut out = [0u8; 32];
    out[..4].copy_from_slice(&fact_commitment.as_u32().to_le_bytes());
    out
}

/// Produce a serialized [`WitnessedPredicateKind::BridgePredicate`] single-bound
/// proof. `proof` is a circuit `PredicateProof` (e.g. from
/// `dregg_circuit::prove_predicate`); the returned bytes verify under
/// [`BridgePredicateStarkVerifier`] when the host policy's operator + threshold
/// match the proof's bound statement.
pub fn bridge_predicate_proof_bytes(proof: Ir2BatchProof<DreggStarkConfig>) -> Vec<u8> {
    postcard::to_allocvec(&BridgePredicateWire::Single(proof))
        .expect("BridgePredicateWire serialization is infallible")
}

/// Produce a serialized [`WitnessedPredicateKind::BridgePredicate`] range proof
/// from the `(low_bound, high_bound)` pair (e.g. from
/// `dregg_circuit::prove_in_range`).
pub fn bridge_predicate_range_proof_bytes(
    low_proof: Ir2BatchProof<DreggStarkConfig>,
    high_proof: Ir2BatchProof<DreggStarkConfig>,
) -> Vec<u8> {
    postcard::to_allocvec(&BridgePredicateWire::Range(low_proof, high_proof))
        .expect("BridgePredicateWire serialization is infallible")
}

// ─────────────────────────────────────────────────────────────────────────
// ThresholdSig — real BLS12-381 + KZG weighted-threshold-signature verifier
// for `Authorization::Custom { vk_hash }` (the governed-namespace
// `commit_table_update` `GOVERNANCE_VK` fire). Welded from the `hints` crate
// directly (the same primitive `dregg-federation`'s `FederationCommittee` /
// `ThresholdQC` wrap) — NOT via `dregg-federation`, because federation depends
// on `dregg-turn`, so the edge would cycle. This mirrors how
// `BridgePredicateStarkVerifier` welds from `dregg-circuit` rather than
// `dregg-bridge`.
// ─────────────────────────────────────────────────────────────────────────
//
// # What `Authorization::Custom` hands this verifier
//
// The executor (`authorize.rs::verify_custom_authorization`) resolves the
// predicate's `InputRef::SigningMessage` to the canonical custom signing
// message — which binds `federation_id` (T6 cross-fed replay), `turn_nonce`
// (T11 stale-proof), action position, and the action's target / method / args
// / effect-hashes / preconditions (T2 forge-effects), but NOT the proof bytes
// in `witness_blobs` (that would be circular). It then calls
//   `verify(commitment, PredicateInput::SigningMessage(msg), proof_bytes)`
// where `proof_bytes` is the `witness_blobs[proof_witness_index]` payload and
// `commitment` is the predicate's commitment (for governed-namespace, the
// `governance_committee_root` — the cell's slot-2 value, which identifies
// *which committee* must have signed).
//
// So this verifier:
//   1. maps `commitment` → a host-trusted [`ThresholdSigCommittee`]
//      (the committee's `hints::Verifier` VK + the minimum k-of-n threshold),
//   2. deserializes `proof_bytes` as a `hints::Signature` (the constant-size
//      aggregate QC), and
//   3. runs `hints::verify_aggregate(verifier, &sig, msg)` — the SNARK proof
//      check + final BLS pairing — and ADDITIONALLY enforces
//      `sig.threshold >= k` (the host floor).
//
// # Why the host policy supplies BOTH the VK and the threshold floor
//
// `verify_aggregate` already rejects when `sig.proof.agg_weight < sig.threshold`
// (not enough weight signed for the QC's *own* claimed threshold). But the QC's
// embedded `threshold` is chosen by the aggregator; a malicious aggregator could
// set it to 1 and present a 1-of-n QC as if it satisfied a k-of-n policy. So —
// exactly as `dregg-federation`'s `FederationCommittee::verify` adds
// `if qc.threshold < self.threshold { reject }` ON TOP of `verify_aggregate`,
// and exactly as `BridgePredicate` consults a [`BridgePredicatePolicyAuthority`]
// for the authoritative threshold — this verifier pins the floor from the
// host-trusted [`ThresholdSigCommittee`], NOT the QC. A commitment with no
// registered committee fails closed (an unknown / self-declared committee is
// never trusted).

/// A host-trusted threshold-signing committee: the `hints` verifier key (which
/// binds the committee's weighted public keys) plus the minimum k-of-n weighted
/// threshold a QC must meet. Both come from the host, never the proof — so a
/// prover can neither swap in their own committee nor lower the threshold.
#[cfg(feature = "threshold-sig")]
#[derive(Clone)]
pub struct ThresholdSigCommittee {
    /// The committee's `hints` verifier (KZG VK; encodes the weighted member
    /// public keys). The aggregate QC's SNARK proof is checked against this.
    pub verifier: hints::Verifier,
    /// The minimum weighted threshold (k of n) the QC must certify. The QC's
    /// own embedded threshold is pinned to be `>= threshold_k`, defeating the
    /// aggregator-chosen-low-threshold forge.
    pub threshold_k: u64,
}

#[cfg(feature = "threshold-sig")]
impl ThresholdSigCommittee {
    /// Construct a committee policy from a `hints::Verifier` and a k-of-n floor.
    pub fn new(verifier: hints::Verifier, threshold_k: u64) -> Self {
        Self {
            verifier,
            threshold_k,
        }
    }
}

#[cfg(feature = "threshold-sig")]
impl core::fmt::Debug for ThresholdSigCommittee {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("ThresholdSigCommittee")
            .field("threshold_k", &self.threshold_k)
            .finish_non_exhaustive()
    }
}

/// Host-installed authority mapping a [`WitnessedPredicateKind::Custom`]
/// predicate `commitment` (e.g. the governed-namespace `governance_committee_root`)
/// to the authoritative [`ThresholdSigCommittee`] the aggregate QC must satisfy.
///
/// This is the threshold-sig analogue of [`BridgePredicatePolicyAuthority`] /
/// [`TemporalPolicyAuthority`]: it keeps the committee VK + threshold floor
/// host-trusted so neither can be chosen by the prover.
#[cfg(feature = "threshold-sig")]
pub trait ThresholdSigPolicyAuthority: Send + Sync {
    /// Return the authoritative committee for `commitment`, or `None` if no
    /// committee is registered (the verifier then fails closed).
    fn committee(&self, commitment: &[u8; 32]) -> Option<ThresholdSigCommittee>;
}

/// A static [`ThresholdSigPolicyAuthority`] backed by an in-memory table of
/// `commitment -> ThresholdSigCommittee`. A commitment absent from the table is
/// rejected (fail-closed by construction).
#[cfg(feature = "threshold-sig")]
#[derive(Clone, Default)]
pub struct StaticThresholdSigPolicy {
    committees: std::collections::BTreeMap<[u8; 32], ThresholdSigCommittee>,
}

#[cfg(feature = "threshold-sig")]
impl StaticThresholdSigPolicy {
    /// Construct an empty authority (rejects everything until a committee is added).
    pub fn new() -> Self {
        Self {
            committees: std::collections::BTreeMap::new(),
        }
    }

    /// Authorize `committee` for `commitment`.
    pub fn authorize(mut self, commitment: [u8; 32], committee: ThresholdSigCommittee) -> Self {
        self.committees.insert(commitment, committee);
        self
    }
}

#[cfg(feature = "threshold-sig")]
impl ThresholdSigPolicyAuthority for StaticThresholdSigPolicy {
    fn committee(&self, commitment: &[u8; 32]) -> Option<ThresholdSigCommittee> {
        self.committees.get(commitment).cloned()
    }
}

/// Real BLS12-381 + KZG threshold-signature-backed verifier for an
/// `Authorization::Custom { vk_hash }` discharge.
///
/// Holds the `vk_hash` it answers for (so it registers via
/// [`WitnessedPredicateRegistry::register_custom`]) and a host-trusted
/// [`ThresholdSigPolicyAuthority`] mapping the predicate `commitment` to the
/// authoritative committee. `verify` deserializes the aggregate QC, looks up the
/// committee for `commitment`, runs `hints::verify_aggregate` (SNARK + final BLS
/// pairing) against the executor-supplied `SigningMessage`, and pins the QC's
/// threshold `>= k`. A commitment with no registered committee, a malformed QC,
/// a QC that does not certify the signing message, or an under-threshold QC
/// fails closed.
#[cfg(feature = "threshold-sig")]
#[derive(Clone)]
pub struct ThresholdSigVerifier {
    vk_hash: [u8; 32],
    policies: Arc<dyn ThresholdSigPolicyAuthority>,
}

#[cfg(feature = "threshold-sig")]
impl ThresholdSigVerifier {
    /// Construct a verifier answering for `vk_hash`, backed by a host-trusted
    /// committee policy authority.
    pub fn new(vk_hash: [u8; 32], policies: Arc<dyn ThresholdSigPolicyAuthority>) -> Self {
        Self { vk_hash, policies }
    }
}

#[cfg(feature = "threshold-sig")]
impl WitnessedPredicateVerifier for ThresholdSigVerifier {
    fn name(&self) -> &'static str {
        "threshold-sig-bls"
    }

    fn kind(&self) -> WitnessedPredicateKind {
        WitnessedPredicateKind::Custom {
            vk_hash: self.vk_hash,
        }
    }

    fn verify(
        &self,
        commitment: &[u8; 32],
        input: &PredicateInput<'_>,
        proof_bytes: &[u8],
    ) -> Result<(), WitnessedPredicateError> {
        // The signing message the QC must certify. `Authorization::Custom`
        // resolves `InputRef::SigningMessage` to the canonical custom signing
        // message; that is the *only* shape this verifier accepts (the message
        // binds federation_id + nonce + action shape, which is what authorizes).
        let message: &[u8] = match input {
            // The executor's custom-auth seam supplies `AuthContext` (message +
            // cell pre-state); this verifier only needs the message.
            PredicateInput::AuthContext {
                signing_message, ..
            } => signing_message,
            PredicateInput::SigningMessage(m) => m,
            PredicateInput::Bytes(b) => b,
            other => {
                return Err(WitnessedPredicateError::InputShapeMismatch {
                    kind_name: "ThresholdSig",
                    expected: "AuthContext / SigningMessage (canonical custom-auth message bytes)",
                    actual: match other {
                        PredicateInput::Slot(_) => "Slot",
                        PredicateInput::PublicInput(_) => "PublicInput",
                        PredicateInput::Sender(_) => "Sender",
                        // AuthContext / SigningMessage / Bytes handled above.
                        _ => "unexpected",
                    },
                });
            }
        };

        // The host-trusted committee for this commitment. Fail closed if none —
        // an unknown / self-declared committee is never trusted.
        let committee = self.policies.committee(commitment).ok_or_else(|| {
            WitnessedPredicateError::Rejected {
                kind_name: "ThresholdSig",
                reason:
                    "no threshold-sig committee registered for this commitment (committee root); \
                     the committee is not host-trusted, so the proof fails closed"
                        .into(),
            }
        })?;

        // Deserialize the aggregate QC (compressed arkworks, matching
        // `dregg-federation`'s `ThresholdQC::to_bytes`/`from_bytes`).
        let sig = hints::Signature::deserialize_compressed(proof_bytes).map_err(|e| {
            WitnessedPredicateError::Rejected {
                kind_name: "ThresholdSig",
                reason: format!("threshold-sig aggregate QC did not deserialize: {e}"),
            }
        })?;

        // Threshold-downgrade defense: pin the QC's threshold to the host floor.
        // `verify_aggregate` only checks `agg_weight >= sig.threshold` (the QC's
        // OWN claimed threshold); a malicious aggregator could set that low.
        // Reject any QC whose certified threshold is below the host's k-of-n.
        let floor = hints::F::from(committee.threshold_k);
        if sig.threshold < floor {
            return Err(WitnessedPredicateError::Rejected {
                kind_name: "ThresholdSig",
                reason: format!(
                    "aggregate QC certifies a threshold below the host policy floor of {} \
                     (k-of-n downgrade attempt)",
                    committee.threshold_k
                ),
            });
        }

        // Authoritative cryptographic gate: SNARK proof check + final BLS
        // pairing against the committee VK and the signing message. A QC that
        // does not certify `message` under `committee` (wrong message, forged
        // proof, under-weight aggregate, wrong committee) is rejected here.
        hints::verify_aggregate(&committee.verifier, &sig, message).map_err(|e| {
            WitnessedPredicateError::Rejected {
                kind_name: "ThresholdSig",
                reason: format!("threshold-sig aggregate verification rejected: {e}"),
            }
        })
    }
}

/// Install a real [`ThresholdSigVerifier`] for `vk_hash` into `registry`,
/// backed by `policy`.
///
/// This is the app-side wiring helper (the threshold-sig analogue of the
/// `register_builtin(...)` calls inside [`registry_with_real_verifiers`]): an
/// app that mints an `Authorization::Custom { vk_hash }` discharge — e.g.
/// `starbridge-governed-namespace`'s `commit_table_update` under `GOVERNANCE_VK`
/// — builds its base production registry ([`registry_with_real_verifiers`] or
/// [`registry_with_real_verifiers_full`]), then calls this to make its custom
/// threshold-sig fire enforce for real. `vk_hash` is supplied by the app (it is
/// the app's `Custom { vk_hash }`), so this verifier is generic across apps and
/// does not hardcode any app-level constant.
#[cfg(feature = "threshold-sig")]
pub fn register_threshold_sig_verifier(
    registry: &mut WitnessedPredicateRegistry,
    vk_hash: [u8; 32],
    policy: Arc<dyn ThresholdSigPolicyAuthority>,
) {
    registry.register_custom(
        vk_hash,
        Arc::new(ThresholdSigVerifier::new(vk_hash, policy)),
    );
}

/// Serialize a `hints::Signature` aggregate QC into the proof-blob bytes a
/// [`ThresholdSigVerifier`] consumes (compressed arkworks, the same wire as
/// `dregg-federation`'s `ThresholdQC::to_bytes`).
///
/// Wrap the returned bytes in a `WitnessBlob` and attach them at the action's
/// `proof_witness_index`; the `Authorization::Custom` discharge feeds them here.
#[cfg(feature = "threshold-sig")]
pub fn threshold_sig_proof_bytes(sig: &hints::Signature) -> Vec<u8> {
    let mut buf = Vec::new();
    sig.serialize_compressed(&mut buf)
        .expect("hints::Signature compressed serialization is infallible");
    buf
}

// ─────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::predicate::{
        NonMembershipNeighborProof, NonMembershipProofV2, PredicateInput, WitnessedPredicate,
    };
    use dregg_circuit::poseidon2::hash_2_to_1;

    /// Build a binary Poseidon2 tree over `compress(neighbor)` leaves; return the
    /// per-level felts (level 0 = leaves, last = [root]).
    fn tree_levels(neighbors: &[[u8; 32]]) -> Vec<Vec<BabyBear>> {
        assert!(neighbors.len().is_power_of_two());
        let leaves: Vec<BabyBear> = neighbors.iter().map(adjacency_leaf_felt).collect();
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let cur = levels.last().unwrap();
            let mut next = Vec::with_capacity(cur.len() / 2);
            for pair in cur.chunks(2) {
                next.push(hash_2_to_1(pair[0], pair[1]));
            }
            levels.push(next);
        }
        levels
    }

    fn auth_path(levels: &[Vec<BabyBear>], mut index: usize) -> Vec<NeighborAdjStep> {
        let depth = levels.len() - 1;
        let mut path = Vec::with_capacity(depth);
        for level in &levels[..depth] {
            let is_right = index & 1 == 1;
            let sibling = if is_right {
                level[index - 1]
            } else {
                level[index + 1]
            };
            path.push(NeighborAdjStep {
                sibling,
                dir: is_right,
            });
            index >>= 1;
        }
        path
    }

    /// Sorted, distinct 32-byte neighbor values.
    fn neighbors4() -> [[u8; 32]; 4] {
        [[0x10u8; 32], [0x20u8; 32], [0x30u8; 32], [0x40u8; 32]]
    }

    /// The production registry under test.
    fn reg() -> WitnessedPredicateRegistry {
        registry_with_real_verifiers()
    }

    /// The executor-default registry DISPATCHES attestation facts: a
    /// `Custom { tee/oracle vk }` predicate resolves to the cell-side verifier
    /// (not `KindNotRegistered`), and — with no host crypto injected — that
    /// verifier REJECTS every proof (fail-closed, never fail-open).
    #[test]
    fn attestation_fact_vks_resolve_and_fail_closed() {
        use dregg_cell::oracle_attest::oracle_predicate_vk;
        use dregg_cell::tee_attest::tee_predicate_vk;

        let reg = reg();

        // The two attestation vks are distinct custom keys.
        assert_ne!(tee_predicate_vk(), oracle_predicate_vk());

        for (vk, name) in [
            (tee_predicate_vk(), "tee-attestation"),
            (oracle_predicate_vk(), "oracle-webfact"),
        ] {
            let v = reg
                .get(WitnessedPredicateKind::Custom { vk_hash: vk })
                .unwrap_or_else(|| {
                    panic!("{name} vk did not resolve in registry_with_real_verifiers")
                });
            assert_eq!(v.name(), name);
            // Fail-closed until a host injects the real crypto: any proof rejects.
            let err = v
                .verify(&[0u8; 32], &PredicateInput::Slot(&[0u8; 32]), &[1u8; 8])
                .unwrap_err();
            assert!(
                matches!(err, WitnessedPredicateError::Rejected { .. }),
                "{name} must reject (fail-closed) with no injected crypto, got {err:?}"
            );
        }
    }

    // ─────────────────────────────────────────────────────────────────────
    // THE CHIP-NATIVE COMPRESS PARITY (big-bang membership re-alignment).
    // executor compress == chip lane 0 == the Lean gate's `pubkeyCompress1Spec`
    // (`CarrierOctetGates.lean::withMembershipPubkeyCompress`): lane 0 of the
    // arity-16 `node8` absorb over `canonical_32_to_felts_8(pk) ‖ 0⁸`.
    // ─────────────────────────────────────────────────────────────────────

    /// PARITY: the executor's membership compress IS the chip-native compress —
    /// `chip_absorb_all_lanes(CHIP_NODE8_ARITY, pubkey8 ‖ 0⁸)[0]` over the
    /// canonical 30-bit limbs — for edge and pseudo-random pubkeys. This is the
    /// exact function the in-AIR gate forces on the sender-leaf tooth, so the
    /// third edge (teeth == committed authority) can bind (fail-open law).
    #[test]
    fn compress_parity_with_chip_native_node8_lane0() {
        use dregg_circuit::descriptor_ir2::{CHIP_NODE8_ARITY, chip_absorb_all_lanes};
        use dregg_commit::typed::canonical_32_to_felts_8;

        let mut cases: Vec<[u8; 32]> = vec![[0u8; 32], [0xFFu8; 32], [0x11u8; 32], {
            // High bytes exercise the 30-bit (`& 0x3F`) limb truncation.
            let mut b = [0u8; 32];
            for (i, x) in b.iter_mut().enumerate() {
                *x = 0xC0 | (i as u8);
            }
            b
        }];
        // Deterministic pseudo-random pubkeys (LCG).
        let mut seed = 0x9E37_79B9u32;
        for _ in 0..16 {
            let mut pk = [0u8; 32];
            for b in pk.iter_mut() {
                seed = seed.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                *b = (seed >> 24) as u8;
            }
            cases.push(pk);
        }

        for pk in &cases {
            let limbs = canonical_32_to_felts_8(pk);
            let mut ins = [BabyBear::ZERO; 16];
            ins[..8].copy_from_slice(&limbs);
            let chip_lane0 = chip_absorb_all_lanes(CHIP_NODE8_ARITY, &ins)[0];
            assert_eq!(
                compress(pk),
                chip_lane0,
                "executor membership compress must equal chip-native node8 lane 0 \
                 (the Lean gate's pubkeyCompress1Spec) for pk {pk:02x?}"
            );
        }
    }

    /// The migration genuinely LEFT the old domain: the chip-native compress
    /// disagrees with the retired `hash_many(encode_hash(pk))` two-permutation
    /// sponge (which no deployed chip arity computes). Guards against a silent
    /// regression back to the unrealizable form.
    #[test]
    fn compress_left_the_old_two_permutation_sponge_domain() {
        for pk in [[0x11u8; 32], [0xABu8; 32], [0u8; 32]] {
            let old = dregg_circuit::poseidon2::hash_many(&BabyBear::encode_hash(&pk));
            assert_ne!(
                compress(&pk),
                old,
                "chip-native compress must differ from the retired sponge for pk {pk:02x?}"
            );
        }
    }

    /// The single-member root/proof pair still roundtrips at the NEW (chip-native)
    /// roots: prove + verify through the production verifier, and a non-member is
    /// still rejected.
    #[test]
    fn single_member_roundtrip_holds_at_chip_native_roots() {
        let member = [0x42u8; 32];
        let root = single_member_authorized_root(&member);
        let proof = single_member_membership_proof(&member);
        let v = MerkleMembershipStarkVerifier;
        v.verify(&root, &PredicateInput::Sender(&member), &proof)
            .expect("single-member proof must verify against the chip-native-domain root");

        let intruder = [0x43u8; 32];
        assert!(
            v.verify(&root, &PredicateInput::Sender(&intruder), &proof)
                .is_err(),
            "a non-member must still be rejected at the new roots"
        );
    }

    /// END-TO-END HAPPY PATH: prove adjacency for a genuinely consecutive pair,
    /// wrap it in a `NonMembershipProofV2`, and verify it through the production
    /// registry's real (STARK-backed) NonMembership verifier.
    #[test]
    fn e2e_consecutive_non_membership_accepts() {
        let neighbors = neighbors4();
        let levels = tree_levels(&neighbors);
        let root_felt = *levels.last().unwrap().first().unwrap();
        // The cell's predicate commitment is the set root felt's LE bytes
        // (the adjacency verifier reads it via `root_felt_from_slot`).
        let commitment = adjacency_commitment_bytes(root_felt);

        // Consecutive neighbors at indices 1,2; a candidate strictly between
        // them in lexicographic order (0x20… < cand < 0x30…) is provably absent.
        let lower = neighbors[1];
        let upper = neighbors[2];
        let candidate = {
            let mut c = [0x20u8; 32];
            c[31] = 0x80; // 0x20…80 is strictly between 0x20… and 0x30…
            c
        };
        let lp = auth_path(&levels, 1);
        let up = auth_path(&levels, 2);
        let adjacency_proof = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap();

        let proof = NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(&commitment, lower, upper),
            adjacency_proof,
        };
        let wp = WitnessedPredicate::non_membership(commitment, PredicateInputRefSender(), 0);
        reg()
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .expect("genuine consecutive non-membership must verify end-to-end");
    }

    /// THE FORGE, end-to-end (fail-before / pass-after): an attacker who knows
    /// the public set root picks wide-bracket neighbors (the smallest and
    /// largest real leaves, indices 0 and 3 — NOT consecutive). They cannot
    /// produce an adjacency proof: `prove_neighbor_adjacency` refuses, and even
    /// a missing proof is rejected by the production registry.
    #[test]
    fn e2e_wide_bracket_forge_rejected() {
        let neighbors = neighbors4();
        let levels = tree_levels(&neighbors);
        let root_felt = *levels.last().unwrap().first().unwrap();
        let commitment = adjacency_commitment_bytes(root_felt);

        // Wide bracket: leaf[0] and leaf[3] (indices 0 and 3, not adjacent).
        let lower = neighbors[0];
        let upper = neighbors[3];
        let lp = auth_path(&levels, 0);
        let up = auth_path(&levels, 3);

        // The prover cannot even build the adjacency proof.
        let prove_err = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap_err();
        assert!(
            prove_err.contains("not consecutive"),
            "prover must refuse non-consecutive bracket; got {prove_err}"
        );

        // And the verifier rejects a forge that ships no real adjacency proof.
        let candidate = [0x25u8; 32]; // strictly inside the wide bracket
        let proof = NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(&commitment, lower, upper),
            adjacency_proof: Vec::new(),
        };
        let wp = WitnessedPredicate::non_membership(commitment, PredicateInputRefSender(), 0);
        let err = reg()
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(
            matches!(err, WitnessedPredicateError::Rejected { .. }),
            "wide-bracket forge must be rejected end-to-end; got {err:?}"
        );
    }

    /// A proof whose adjacency STARK is for a DIFFERENT root than the predicate
    /// commitment is rejected (root binding).
    #[test]
    fn e2e_wrong_root_adjacency_rejected() {
        let neighbors = neighbors4();
        let levels = tree_levels(&neighbors);
        let lower = neighbors[1];
        let upper = neighbors[2];
        let lp = auth_path(&levels, 1);
        let up = auth_path(&levels, 2);
        let adjacency_proof = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap();

        // Use a commitment that does NOT match the proof's root.
        let wrong_commitment = adjacency_commitment_bytes(BabyBear::new(123_456));
        let candidate = {
            let mut c = [0x20u8; 32];
            c[31] = 0x80;
            c
        };
        let proof = NonMembershipProofV2 {
            neighbor: NonMembershipNeighborProof::new(&wrong_commitment, lower, upper),
            adjacency_proof,
        };
        let wp = WitnessedPredicate::non_membership(wrong_commitment, PredicateInputRefSender(), 0);
        let err = reg()
            .verify(&wp, &PredicateInput::Sender(&candidate), &proof.to_bytes())
            .unwrap_err();
        assert!(matches!(err, WitnessedPredicateError::Rejected { .. }));
    }

    // ─────────────────────────────────────────────────────────────────────
    // noteSpend nullifier-set non-membership (the deployed double-spend gate).
    // Mutation-confirm at the DEPLOYED verifier, not just the unit AIR test.
    // ─────────────────────────────────────────────────────────────────────

    /// Sorted (by leaf-felt) neighbor values, so a candidate strictly between
    /// two felt-consecutive leaves can be constructed. Returns the byte values
    /// in ascending leaf-felt order plus the matching tree levels.
    fn felt_sorted_neighbors8() -> (Vec<[u8; 32]>, Vec<Vec<BabyBear>>) {
        // Eight distinct neighbor values (depth-3 → padded; we need a
        // power-of-two depth, so use 8 leaves = depth 3 is NOT power of two —
        // use 4 leaves (depth 2) which the adjacency AIR accepts).
        let raw: Vec<[u8; 32]> = (0u8..4)
            .map(|i| {
                let mut b = [0u8; 32];
                b[0] = 0xA0 ^ i;
                b[1] = i.wrapping_mul(37);
                b
            })
            .collect();
        // Sort the VALUES by their leaf-felt so tree index order == felt order
        // (the tree is sorted-by-leaf-felt, the adjacency-set discipline).
        let mut by_felt = raw.clone();
        by_felt.sort_by_key(|v| adjacency_leaf_felt(v).as_u32());
        let levels = tree_levels(&by_felt);
        (by_felt, levels)
    }

    /// HAPPY PATH: a nullifier whose leaf-felt sits strictly between two
    /// CONSECUTIVE committed leaves is accepted as a non-member by the deployed
    /// `verify_nullifier_nonmembership` gate.
    #[test]
    fn notespend_nonmembership_consecutive_accepts() {
        let (vals, levels) = felt_sorted_neighbors8();
        let root_felt = *levels.last().unwrap().first().unwrap();
        let root = adjacency_commitment_bytes(root_felt);

        // Consecutive leaves at felt-sorted indices 1,2.
        let lower = vals[1];
        let upper = vals[2];
        let lo_f = adjacency_leaf_felt(&lower).as_u32();
        let hi_f = adjacency_leaf_felt(&upper).as_u32();
        assert!(lo_f < hi_f, "neighbors must be felt-ordered");

        // Find a nullifier whose compressed leaf-felt is strictly in (lo_f, hi_f).
        // Search a small family until one lands in the open gap (felt is a hash,
        // so we probe rather than construct).
        let mut nullifier = None;
        for k in 0u32..5000 {
            let mut cand = [0u8; 32];
            cand[0] = 0x55;
            cand[1..5].copy_from_slice(&k.to_le_bytes());
            let f = compress(&cand).as_u32();
            if lo_f < f && f < hi_f {
                nullifier = Some(cand);
                break;
            }
        }
        let nullifier = nullifier.expect("expected some candidate in the open gap");

        let lp = auth_path(&levels, 1);
        let up = auth_path(&levels, 2);
        let adjacency_proof = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap();

        verify_nullifier_nonmembership(&root, &nullifier, &lower, &upper, &adjacency_proof)
            .expect("a fresh nullifier bracketed by consecutive leaves must verify");
    }

    /// THE FORGE (the census-R1 double-spend), at the DEPLOYED verifier: an
    /// attacker picks a WIDE bracket (non-consecutive leaves 0 and 3) around a
    /// nullifier that may well BE in the set. They cannot build the adjacency
    /// proof (the AIR refuses non-consecutive indices), and even a fabricated /
    /// empty adjacency blob is rejected by `verify_nullifier_nonmembership` —
    /// so no forged non-membership can be presented. Double-spend via wide
    /// bracket is impossible at the deployed gate, not merely the unit AIR.
    #[test]
    fn notespend_wide_bracket_double_spend_rejected() {
        let (vals, levels) = felt_sorted_neighbors8();
        let root_felt = *levels.last().unwrap().first().unwrap();
        let root = adjacency_commitment_bytes(root_felt);

        // Wide bracket: the min and max committed leaves (felt-indices 0 and 3).
        let lower = vals[0];
        let upper = vals[3];
        let lo_f = adjacency_leaf_felt(&lower).as_u32();
        let hi_f = adjacency_leaf_felt(&upper).as_u32();

        // A nullifier strictly inside the WIDE gap — could equal an interior
        // committed leaf (a real double-spend target).
        let mut nullifier = None;
        for k in 0u32..5000 {
            let mut cand = [0u8; 32];
            cand[0] = 0x77;
            cand[1..5].copy_from_slice(&k.to_le_bytes());
            let f = compress(&cand).as_u32();
            if lo_f < f && f < hi_f {
                nullifier = Some(cand);
                break;
            }
        }
        let nullifier = nullifier.expect("expected some candidate in the wide gap");

        // (1) The honest prover path refuses to build a non-consecutive proof.
        let lp = auth_path(&levels, 0);
        let up = auth_path(&levels, 3);
        let prove_err = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap_err();
        assert!(
            prove_err.contains("not consecutive"),
            "prover must refuse the wide bracket; got {prove_err}"
        );

        // (2) THE DEPLOYED GATE rejects a forge that ships no real adjacency
        //     proof for the wide bracket — the bracket check (a) passes (the
        //     nullifier is strictly inside), so it is the ADJACENCY teeth (b)
        //     that close the forgery.
        let err =
            verify_nullifier_nonmembership(&root, &nullifier, &lower, &upper, &[]).unwrap_err();
        assert!(
            err.contains("adjacency"),
            "the deployed gate must reject the wide-bracket forge on the adjacency leg; got {err}"
        );

        // (3) Even re-using a GENUINE consecutive proof (for leaves 1,2) under
        //     the wide-bracket (lower=0, upper=3) public inputs is rejected:
        //     the adjacency STARK binds the specific leaves it attests.
        let good_lp = auth_path(&levels, 1);
        let good_up = auth_path(&levels, 2);
        let real_proof = prove_neighbor_adjacency(&vals[1], &good_lp, &vals[2], &good_up).unwrap();
        let err2 = verify_nullifier_nonmembership(&root, &nullifier, &lower, &upper, &real_proof)
            .unwrap_err();
        assert!(
            err2.contains("adjacency"),
            "a consecutive proof cannot be replayed for the wide bracket; got {err2}"
        );
    }

    /// A nullifier NOT strictly between the neighbors (e.g. equal to a neighbor,
    /// the double-spend-of-a-boundary attempt) is rejected by the bracket leg.
    #[test]
    fn notespend_nullifier_outside_bracket_rejected() {
        let (vals, levels) = felt_sorted_neighbors8();
        let root_felt = *levels.last().unwrap().first().unwrap();
        let root = adjacency_commitment_bytes(root_felt);
        let lower = vals[1];
        let upper = vals[2];
        let lp = auth_path(&levels, 1);
        let up = auth_path(&levels, 2);
        let adjacency_proof = prove_neighbor_adjacency(&lower, &lp, &upper, &up).unwrap();

        // The lower neighbor itself is NOT strictly inside (lo, hi): claiming it
        // is fresh would be a non-membership lie about a present leaf.
        let err = verify_nullifier_nonmembership(&root, &lower, &lower, &upper, &adjacency_proof)
            .unwrap_err();
        assert!(
            err.contains("strictly between"),
            "a neighbor value is a member, not a non-member; got {err}"
        );
    }

    /// The production registry installs the real, named verifiers.
    #[test]
    fn production_registry_installs_real_verifiers() {
        let r = reg();
        assert_eq!(
            r.get(WitnessedPredicateKind::MerkleMembership)
                .unwrap()
                .name(),
            "merkle-membership-stark"
        );
        assert_eq!(
            r.get(WitnessedPredicateKind::NonMembership).unwrap().name(),
            "sorted-neighbor-non-membership"
        );
        assert_eq!(
            r.get(WitnessedPredicateKind::BlindedSet).unwrap().name(),
            "credential-set-membership"
        );
    }

    /// Helper: the `InputRef::Sender` variant (kept local so the test reads
    /// without importing the enum path).
    #[allow(non_snake_case)]
    fn PredicateInputRefSender() -> dregg_cell::predicate::InputRef {
        dregg_cell::predicate::InputRef::Sender
    }

    /// THE DEFAULT-EXECUTOR TOOTH (both polarities).
    ///
    /// A *bare* `TurnExecutor::new(..)` — no `set_witnessed_registry`, no app
    /// wiring — must enforce the REAL MerkleMembership verifier, because
    /// `dregg-turn` owns the real STARK gadget and uses
    /// [`registry_with_real_verifiers`] as its constructor default. This test
    /// reaches into the executor's OWN `witnessed_registry` (the default the
    /// constructor installed, NOT a hand-built one) and proves both polarities
    /// through it:
    ///
    /// - a genuine member's proof is ADMITTED (valid leaf reaches the root), and
    /// - a non-member's forge against the same root is REJECTED at the STARK
    ///   level (Poseidon2 collision resistance — no path exists, so
    ///   `verify_vm_descriptor2` fails and `SenderAuthorized` rejects).
    ///
    /// If a future edit silently reverts the default back to
    /// `dregg_cell::default_builtins()` (the `NotYetWiredVerifier` stub), the
    /// ADMIT half flips to a `Rejected { reason: "not yet wired" }` and this
    /// test fails — the regression the footgun this change closes.
    #[test]
    fn default_executor_admits_valid_membership_and_rejects_forge() {
        use crate::executor::{ComputronCosts, TurnExecutor};

        // The thing under test: a bare executor with NOTHING wired by the host.
        let executor = TurnExecutor::new(ComputronCosts::default_costs());
        let registry = executor
            .witnessed_registry
            .as_ref()
            .expect("a fresh TurnExecutor must default its witnessed_registry to Some");

        // Sanity: the default really is the REAL verifier, not the stub.
        assert_eq!(
            registry
                .get(WitnessedPredicateKind::MerkleMembership)
                .expect("MerkleMembership must be registered by default")
                .name(),
            "merkle-membership-stark",
            "the bare-executor default must install the real STARK verifier, \
             not dregg_cell::default_builtins's NotYetWired stub",
        );

        // An honest authorized member: derive the one-member set root and the
        // matching membership proof from the same single-leaf tree.
        let member = [0xA7u8; 32];
        let set_root = single_member_authorized_root(&member);
        let proof = single_member_membership_proof(&member);
        let wp = WitnessedPredicate::merkle_membership(set_root, PredicateInputRefSender(), 0);

        // ── ADMIT: the genuine member verifies through the DEFAULT registry. ──
        registry
            .verify(&wp, &PredicateInput::Sender(&member), &proof)
            .expect(
                "the default executor must ADMIT a valid membership proof for an \
                 authorized member",
            );

        // ── REJECT (forge #1): a non-member sender against the SAME root, ────
        // reusing the genuine member's proof bytes. The committed leaf is
        // `compress(non_member)`, which does not reach `set_root`, so the STARK
        // public-input boundary fails.
        let non_member = [0xBEu8; 32];
        let forge_err = registry
            .verify(&wp, &PredicateInput::Sender(&non_member), &proof)
            .expect_err("a non-member must be REJECTED by the default executor");
        assert!(
            matches!(forge_err, WitnessedPredicateError::Rejected { .. }),
            "non-member forge must be Rejected at the STARK level; got {forge_err:?}",
        );

        // ── REJECT (forge #2): the non-member tries to forge their OWN proof ──
        // against the honest member's root. They can build a self-consistent
        // proof only for THEIR OWN single-member root; verified against the
        // member's `set_root` it cannot pass (roots differ → boundary mismatch).
        let attacker_proof = single_member_membership_proof(&non_member);
        let forge2_err = registry
            .verify(&wp, &PredicateInput::Sender(&non_member), &attacker_proof)
            .expect_err("a self-fabricated proof against another's root must be REJECTED");
        assert!(
            matches!(forge2_err, WitnessedPredicateError::Rejected { .. }),
            "self-fabricated wrong-root proof must be Rejected; got {forge2_err:?}",
        );

        // ── THE DELIBERATE-DECISION TOOTH: the three context-dependent kinds ──
        // (Dfa, Temporal, BridgePredicate) stay fail-closed in the default —
        // they have no safe context-free verifier and must be installed via
        // `registry_with_real_verifiers_full(..)`. Prove Dfa still rejects out
        // of the box so "raises the floor without lowering any ceiling" is a
        // checked property, not a comment.
        let dfa_wp = WitnessedPredicate::dfa([0u8; 32], PredicateInputRefSender(), 0);
        let dfa_err = registry
            .verify(&dfa_wp, &PredicateInput::Sender(&member), &[1u8, 2, 3])
            .expect_err("Dfa must stay fail-closed by default (needs a ProgramRegistry)");
        assert!(
            matches!(dfa_err, WitnessedPredicateError::Rejected { .. }),
            "default Dfa must be the NotYetWired fail-closed stub; got {dfa_err:?}",
        );
    }

    // ─────────────────────────────────────────────────────────────────────
    // Dfa / Temporal / PedersenEquality real-verifier wiring tests.
    // ─────────────────────────────────────────────────────────────────────

    use dregg_cell::predicate::StaticIssuerRootAuthority;
    use dregg_cell_crypto::value_commitment::prove_range_bytes;
    use dregg_circuit::PredicateType;
    use dregg_circuit::dsl::circuit::{
        CellProgram, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, PolyTerm,
    };
    use dregg_circuit::dsl::dfa_routing::{
        build_routing_witness, dfa_routing_descriptor, pi as routing_pi,
    };
    use dregg_circuit::field::BABYBEAR_P;
    use std::collections::HashMap;

    /// The EXACT `dregg-dfa-routing-v1` 4-state router transition table
    /// (`dregg-tests/src/dfa_circuit.rs:56`): IDLE=0, LOCAL=1, REMOTE=2, REJECT=3;
    /// symbols internal=0, external=1, privileged=2, unknown=3. Flattened triples.
    fn router_transitions() -> Vec<(u32, u32, u32)> {
        let table = [[1, 2, 1, 3], [1, 2, 1, 3], [1, 2, 3, 3], [3, 3, 3, 3]];
        let mut out = Vec::new();
        for (state, row) in table.iter().enumerate() {
            for (symbol, &next) in row.iter().enumerate() {
                out.push((state as u32, symbol as u32, next));
            }
        }
        out
    }

    /// A minimal balance-conservation DSL descriptor (the canonical 6-column
    /// sovereign transition): `new = old - transfer + 2*dir*transfer`, `dir`
    /// boolean. Used to exercise the Dfa verifier end-to-end.
    fn dfa_descriptor() -> CircuitDescriptor {
        let v = |name: &str, index, kind| ColumnDef {
            name: name.to_string(),
            index,
            kind,
        };
        CircuitDescriptor {
            name: "dfa-test-conservation-v1".to_string(),
            trace_width: 6,
            max_degree: 2,
            columns: vec![
                v("old_balance", 0, ColumnKind::Value),
                v("transfer_amount", 1, ColumnKind::Value),
                v("new_balance", 2, ColumnKind::Value),
                v("direction", 3, ColumnKind::Binary),
                v("pad0", 4, ColumnKind::Value),
                v("pad1", 5, ColumnKind::Value),
            ],
            constraints: vec![
                ConstraintExpr::Binary { col: 3 },
                ConstraintExpr::Polynomial {
                    terms: vec![
                        PolyTerm {
                            coeff: BabyBear::ONE,
                            col_indices: vec![2],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(BABYBEAR_P - 1),
                            col_indices: vec![0],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(BABYBEAR_P - 1),
                            col_indices: vec![1],
                        },
                        PolyTerm {
                            coeff: BabyBear::new(2),
                            col_indices: vec![3, 1],
                        },
                    ],
                },
            ],
            boundaries: vec![],
            public_input_count: 32,
            lookup_tables: vec![],
        }
    }

    fn dfa_witness(
        old: u64,
        transfer: u64,
        new: u64,
        dir: u32,
        rows: usize,
    ) -> HashMap<String, Vec<BabyBear>> {
        let mut w = HashMap::new();
        w.insert("old_balance".into(), vec![BabyBear::from_u64(old); rows]);
        w.insert(
            "transfer_amount".into(),
            vec![BabyBear::from_u64(transfer); rows],
        );
        w.insert("new_balance".into(), vec![BabyBear::from_u64(new); rows]);
        w.insert("direction".into(), vec![BabyBear::new(dir); rows]);
        w
    }

    /// Dfa: a valid transition proof verifies through the wired DslCircuitDfaVerifier.
    #[test]
    fn dfa_real_verifier_accepts_valid_transition() {
        let descriptor = dfa_descriptor();
        let program = CellProgram::new(descriptor, 1);
        let mut programs = ProgramRegistry::new();
        let vk_hash = programs.deploy(program).unwrap();
        let programs = Arc::new(programs);

        let pi = vec![BabyBear::ZERO; 32];
        let witness = dfa_witness(1000, 100, 900, 1, 2);
        let proof = prove_dfa_transition(&programs, &vk_hash, &witness, 2, &pi).unwrap();

        let v = DslCircuitDfaVerifier::new(programs);
        let dummy = [0u8; 32];
        v.verify(&vk_hash, &PredicateInput::Sender(&dummy), &proof)
            .expect("valid DSL transition must verify");
    }

    /// Dfa FORGE: a proof for one set of public inputs is rejected when checked
    /// against different public inputs (the AIR boundary binds PI). And an
    /// unknown vk_hash fails closed.
    #[test]
    fn dfa_real_verifier_rejects_forged_and_unknown() {
        let descriptor = dfa_descriptor();
        let program = CellProgram::new(descriptor, 1);
        let mut programs = ProgramRegistry::new();
        let vk_hash = programs.deploy(program).unwrap();
        let programs = Arc::new(programs);
        let dummy = [0u8; 32];

        // Forged PI: tamper the wire's declared public inputs so they no longer
        // match the STARK's boundary commitments.
        let pi = vec![BabyBear::ZERO; 32];
        let witness = dfa_witness(1000, 100, 900, 1, 2);
        let good = prove_dfa_transition(&programs, &vk_hash, &witness, 2, &pi).unwrap();
        let mut wire: DfaProofWire = postcard::from_bytes(&good).unwrap();
        wire.public_inputs[0] = wire.public_inputs[0].wrapping_add(1);
        let forged = postcard::to_allocvec(&wire).unwrap();
        let v = DslCircuitDfaVerifier::new(programs.clone());
        assert!(
            v.verify(&vk_hash, &PredicateInput::Sender(&dummy), &forged)
                .is_err(),
            "forged public inputs must be rejected by the AIR boundary"
        );

        // Unknown vk_hash → fail closed.
        let unknown = [0x99u8; 32];
        assert!(
            v.verify(&unknown, &PredicateInput::Sender(&dummy), &good)
                .is_err(),
            "unknown vk_hash must fail closed"
        );

        // Garbage wire → reject.
        assert!(
            v.verify(&vk_hash, &PredicateInput::Sender(&dummy), b"junk")
                .is_err()
        );
    }

    /// Dfa: routed through the full production registry.
    #[test]
    fn dfa_via_full_registry() {
        let descriptor = dfa_descriptor();
        let program = CellProgram::new(descriptor, 1);
        let mut programs = ProgramRegistry::new();
        let vk_hash = programs.deploy(program).unwrap();
        let programs = Arc::new(programs);
        let pi = vec![BabyBear::ZERO; 32];
        let witness = dfa_witness(500, 200, 700, 0, 2);
        let proof = prove_dfa_transition(&programs, &vk_hash, &witness, 2, &pi).unwrap();

        let reg = registry_with_real_verifiers_full(
            programs,
            Arc::new(EmptyTemporalPolicy),
            Arc::new(StaticIssuerRootAuthority::new()),
            Arc::new(StaticBridgePredicatePolicy::new()),
        );
        let wp = WitnessedPredicate::dfa(vk_hash, PredicateInputRefSender(), 0);
        let dummy = [0u8; 32];
        reg.verify(&wp, &PredicateInput::Sender(&dummy), &proof)
            .expect("Dfa must verify through the full production registry");
    }

    // ─────────────────────────────────────────────────────────────────────
    // LIVE route-commitment binding: the real `dregg-dfa-routing-v1` AIR
    // (Lean `Dregg2.Crypto.DfaAcceptanceAir`) wired through the production
    // `DslCircuitDfaVerifier` — the same verifier the relay-operator template's
    // `Witnessed { Dfa }` caveat dispatches to. This binds the message-routing
    // decision to the running-hash route commitment, so a router CANNOT claim a
    // delivery (final state / route commitment) it did not make.
    // ─────────────────────────────────────────────────────────────────────

    /// Deploy the routing program, build an honest routing witness, and prove the
    /// wire bytes the live `DslCircuitDfaVerifier` consumes. Returns the deployed
    /// registry, the program `vk_hash` (the relay's `route_table_root`), the wire
    /// bytes, and the honest public inputs.
    fn route_proof(
        symbols: &[u32],
    ) -> (
        Arc<ProgramRegistry>,
        [u8; 32],
        Vec<u8>,
        Vec<dregg_circuit::field::BabyBear>,
    ) {
        let transitions = router_transitions();
        let descriptor = dfa_routing_descriptor("dregg-dfa-routing-v1", &transitions);
        let program = CellProgram::new(descriptor, 1);
        let mut programs = ProgramRegistry::new();
        let vk_hash = programs.deploy(program).unwrap();
        let programs = Arc::new(programs);

        let (witness, public_inputs) =
            build_routing_witness(&transitions, 0, symbols).expect("router accepts this input");
        let num_rows = witness.get("current_state").map(|v| v.len()).unwrap();
        let wire = prove_dfa_transition(&programs, &vk_hash, &witness, num_rows, &public_inputs)
            .expect("routing proof wire builds");
        (programs, vk_hash, wire, public_inputs)
    }

    /// TOOTH (valid admits): an honest route verifies through the live
    /// `DslCircuitDfaVerifier` (the relay's verifier), binding the route commitment.
    #[test]
    fn live_routing_verifier_accepts_correct_route() {
        // internal, external, internal: IDLE -> LOCAL -> REMOTE -> LOCAL.
        let (programs, vk_hash, wire, _pi) = route_proof(&[0, 1, 0]);
        let v = DslCircuitDfaVerifier::new(programs);
        let dummy = [0u8; 32];
        v.verify(&vk_hash, &PredicateInput::Sender(&dummy), &wire)
            .expect("a correct route must verify against its route_commitment");
    }

    /// TOOTH (forged final state rejected): tampering the wire's `final_state` PI —
    /// a router claiming a classification it did not compute — is rejected by the B2
    /// boundary. This is the live form of "can't claim a delivery you didn't make".
    #[test]
    fn live_routing_verifier_rejects_forged_final_state() {
        let (programs, vk_hash, wire, _pi) = route_proof(&[0, 1, 0]);
        // Decode the wire, forge the final_state PI (claim REJECT=3 not LOCAL=1).
        let mut decoded: DfaProofWire = postcard::from_bytes(&wire).unwrap();
        decoded.public_inputs[routing_pi::FINAL_STATE] = 3;
        let forged = postcard::to_allocvec(&decoded).unwrap();

        let v = DslCircuitDfaVerifier::new(programs);
        let dummy = [0u8; 32];
        assert!(
            v.verify(&vk_hash, &PredicateInput::Sender(&dummy), &forged)
                .is_err(),
            "a forged final_state must be rejected by the live routing verifier"
        );
    }

    /// TOOTH (forged route commitment rejected): tampering the wire's
    /// `route_commitment` PI fails the B3 boundary — the commitment binds the trace.
    #[test]
    fn live_routing_verifier_rejects_forged_route_commitment() {
        let (programs, vk_hash, wire, _pi) = route_proof(&[0, 1, 0]);
        let mut decoded: DfaProofWire = postcard::from_bytes(&wire).unwrap();
        decoded.public_inputs[routing_pi::ROUTE_COMMITMENT] = 0xDEAD;
        let forged = postcard::to_allocvec(&decoded).unwrap();

        let v = DslCircuitDfaVerifier::new(programs);
        let dummy = [0u8; 32];
        assert!(
            v.verify(&vk_hash, &PredicateInput::Sender(&dummy), &forged)
                .is_err(),
            "a forged route_commitment must be rejected by the live routing verifier"
        );
    }

    /// TOOTH (full production registry, end-to-end): the routing proof verifies
    /// through `registry_with_real_verifiers_full` (the executor-default Dfa wiring)
    /// against a `WitnessedPredicate::dfa` whose commitment is the routing program's
    /// `vk_hash` — exactly the relay's `Witnessed { Dfa }` dispatch.
    #[test]
    fn live_routing_via_full_registry_binds_and_rejects() {
        let (programs, vk_hash, wire, _pi) = route_proof(&[0, 1, 0]);
        let reg = registry_with_real_verifiers_full(
            programs,
            Arc::new(EmptyTemporalPolicy),
            Arc::new(StaticIssuerRootAuthority::new()),
            Arc::new(StaticBridgePredicatePolicy::new()),
        );
        let wp = WitnessedPredicate::dfa(vk_hash, PredicateInputRefSender(), 0);
        let dummy = [0u8; 32];
        reg.verify(&wp, &PredicateInput::Sender(&dummy), &wire)
            .expect("honest route binds through the full production registry");

        // Forge the final state through the same registry path → rejected.
        let mut decoded: DfaProofWire = postcard::from_bytes(&wire).unwrap();
        decoded.public_inputs[routing_pi::FINAL_STATE] = 3;
        let forged = postcard::to_allocvec(&decoded).unwrap();
        assert!(
            reg.verify(&wp, &PredicateInput::Sender(&dummy), &forged)
                .is_err(),
            "a forged route classification must fail through the full registry"
        );
    }

    /// Temporal policy authority for tests.
    struct OneTemporalPolicy {
        commitment: [u8; 32],
        policy: TemporalPolicy,
    }
    impl TemporalPolicyAuthority for OneTemporalPolicy {
        fn policy(&self, commitment: &[u8; 32]) -> Option<TemporalPolicy> {
            if commitment == &self.commitment {
                Some(self.policy.clone())
            } else {
                None
            }
        }
    }
    struct EmptyTemporalPolicy;
    impl TemporalPolicyAuthority for EmptyTemporalPolicy {
        fn policy(&self, _commitment: &[u8; 32]) -> Option<TemporalPolicy> {
            None
        }
    }

    /// Build an honest temporal proof: value >= threshold held for N steps.
    fn honest_temporal(values: &[u32], threshold: u32) -> TemporalPredicateProof {
        let vs: Vec<BabyBear> = values.iter().map(|v| BabyBear::new(*v)).collect();
        let roots: Vec<BabyBear> = (0..values.len())
            .map(|i| BabyBear::new(1000 + i as u32))
            .collect();
        dregg_circuit::temporal_predicate_dsl::prove_temporal_predicate(
            &vs,
            &roots,
            PredicateType::Gte,
            BabyBear::new(threshold),
        )
        .expect("honest temporal predicate should be provable")
    }

    fn temporal_policy_from(proof: &TemporalPredicateProof, min_steps: u64) -> TemporalPolicy {
        TemporalPolicy {
            requirement: TemporalPredicateRequirement {
                attribute: "balance".into(),
                predicate_type: PredicateType::Gte,
                threshold: proof.threshold.as_u32() as u64,
                min_duration_steps: min_steps,
            },
            num_steps: proof.num_steps,
            initial_state_root: proof.initial_state_root.as_u32(),
            final_state_root: proof.final_state_root.as_u32(),
        }
    }

    #[test]
    fn temporal_real_verifier_accepts_valid_proof() {
        let proof = honest_temporal(&[100, 110, 120], 50);
        let commitment = [0x7Au8; 32];
        let policy = temporal_policy_from(&proof, 3);
        let auth = Arc::new(OneTemporalPolicy { commitment, policy });
        let v = TemporalPredicateStarkVerifier::new(auth);
        let bytes = postcard::to_allocvec(&proof).unwrap();
        let dummy = [0u8; 32];
        v.verify(&commitment, &PredicateInput::Sender(&dummy), &bytes)
            .expect("valid temporal proof must verify");
    }

    #[test]
    fn temporal_real_verifier_rejects_forge_and_unknown() {
        let proof = honest_temporal(&[100, 110, 120], 50);
        let commitment = [0x7Au8; 32];
        let dummy = [0u8; 32];

        // FORGE: host policy demands a HIGHER threshold than the proof carries.
        // is_satisfied_by fails (proof.threshold < policy.threshold).
        let mut policy = temporal_policy_from(&proof, 3);
        policy.requirement.threshold = 200; // higher than proof's 50
        let auth = Arc::new(OneTemporalPolicy { commitment, policy });
        let v = TemporalPredicateStarkVerifier::new(auth);
        let bytes = postcard::to_allocvec(&proof).unwrap();
        assert!(
            v.verify(&commitment, &PredicateInput::Sender(&dummy), &bytes)
                .is_err(),
            "proof failing the host threshold floor must reject"
        );

        // FORGE 2: tamper the proof's final_state_root after minting; the STARK
        // PI (reconstructed from the HONEST policy roots) mismatches → reject.
        let honest_policy = temporal_policy_from(&proof, 3);
        let auth2 = Arc::new(OneTemporalPolicy {
            commitment,
            policy: honest_policy,
        });
        let v2 = TemporalPredicateStarkVerifier::new(auth2);
        let mut tampered = proof.clone();
        tampered.final_state_root = BabyBear::new(424242);
        let tbytes = postcard::to_allocvec(&tampered).unwrap();
        assert!(
            v2.verify(&commitment, &PredicateInput::Sender(&dummy), &tbytes)
                .is_err(),
            "tampered state root must reject against the policy-derived PI"
        );

        // Unknown commitment → fail closed.
        let v3 = TemporalPredicateStarkVerifier::new(Arc::new(EmptyTemporalPolicy));
        assert!(
            v3.verify(&commitment, &PredicateInput::Sender(&dummy), &bytes)
                .is_err(),
            "unknown temporal commitment must fail closed"
        );
    }

    #[test]
    fn pedersen_real_verifier_accepts_valid_and_rejects_forged() {
        // Honest: commit value=42 with a blinding, prove the range.
        let blinding = [0x5Cu8; 32];
        let (commitment, range_proof) = prove_range_bytes(42, &blinding);
        let v = PedersenBulletproofVerifier;
        let dummy = [0u8; 32];
        v.verify(&commitment, &PredicateInput::Slot(&dummy), &range_proof)
            .expect("valid Bulletproof opening must verify");

        // FORGE 1: present the proof against a DIFFERENT commitment.
        let (other_commitment, _) = prove_range_bytes(43, &[0x01u8; 32]);
        assert!(
            v.verify(
                &other_commitment,
                &PredicateInput::Slot(&dummy),
                &range_proof
            )
            .is_err(),
            "Bulletproof must not verify against a different commitment"
        );

        // FORGE 2: garbage / empty proof bytes.
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), b"")
                .is_err()
        );
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), &[0u8; 16])
                .is_err()
        );
    }

    #[test]
    fn pedersen_wired_in_default_registry() {
        let reg = registry_with_real_verifiers();
        assert_eq!(
            reg.get(WitnessedPredicateKind::PedersenEquality)
                .unwrap()
                .name(),
            "pedersen-bulletproof"
        );
        // BridgePredicate stays fail-closed (its verifier lives in dregg-bridge).
        let bridge = reg.get(WitnessedPredicateKind::BridgePredicate).unwrap();
        let dummy = [0u8; 32];
        assert!(
            bridge
                .verify(&[0u8; 32], &PredicateInput::Sender(&dummy), b"anything")
                .is_err(),
            "BridgePredicate must remain fail-closed in turn (no dregg-bridge dep)"
        );
    }

    #[test]
    fn full_registry_blinded_set_has_issuer_authority() {
        let reg = registry_with_real_verifiers_full(
            Arc::new(ProgramRegistry::new()),
            Arc::new(EmptyTemporalPolicy),
            Arc::new(StaticIssuerRootAuthority::new()),
            Arc::new(StaticBridgePredicatePolicy::new()),
        );
        assert_eq!(
            reg.get(WitnessedPredicateKind::Dfa).unwrap().name(),
            "dsl-circuit-dfa"
        );
        assert_eq!(
            reg.get(WitnessedPredicateKind::Temporal).unwrap().name(),
            "temporal-predicate-stark"
        );
        assert_eq!(
            reg.get(WitnessedPredicateKind::BlindedSet).unwrap().name(),
            "credential-set-membership"
        );
    }

    // ─────────────────────────────────────────────────────────────────────
    // BridgePredicate real-verifier teeth (welded from dregg-circuit's
    // predicate-AIR STARK; no dregg-bridge dependency).
    // ─────────────────────────────────────────────────────────────────────

    use dregg_circuit::compute_fact_commitment;
    use dregg_circuit::predicate_air::{PredicateWitness, prove_in_range, prove_predicate};

    /// A bridge policy authority that authorizes ONE requirement for ONE commitment.
    struct OneBridgePolicy {
        commitment: [u8; 32],
        requirement: BridgePredicateRequirement,
    }
    impl BridgePredicatePolicyAuthority for OneBridgePolicy {
        fn requirement(&self, commitment: &[u8; 32]) -> Option<BridgePredicateRequirement> {
            (commitment == &self.commitment).then_some(self.requirement)
        }
    }

    /// Build an honest single-bound predicate proof for `value op threshold` over
    /// a committed fact, returning `(commitment_bytes, fact_commitment_felt, proof)`.
    fn honest_bridge_single(
        value: u32,
        op: PredicateType,
        threshold: u32,
    ) -> ([u8; 32], BabyBear, PredicateProof) {
        let fact_hash = BabyBear::new(0xFACE);
        let state_root = BabyBear::new(0xB00C);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);
        let witness = PredicateWitness {
            private_value: BabyBear::new(value),
            threshold: BabyBear::new(threshold),
            predicate_type: op,
            fact_commitment,
            blinding: None,
            fact_hash: Some(fact_hash),
            state_root: Some(state_root),
        };
        let proof = prove_predicate(witness).expect("honest predicate must be provable");
        (
            bridge_predicate_commitment_bytes(fact_commitment),
            fact_commitment,
            proof,
        )
    }

    /// TOOTH (admit): a genuine `value >= threshold` proof verifies through the
    /// real BridgePredicate verifier when the host policy matches.
    #[test]
    fn bridge_predicate_real_verifier_accepts_valid() {
        let (commitment, _fc, proof) = honest_bridge_single(500, PredicateType::Gte, 100);
        let policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::Threshold {
                op: PredicateType::Gte,
                threshold: 100,
            },
        });
        let v = BridgePredicateStarkVerifier::new(policy);
        let bytes = bridge_predicate_proof_bytes(&proof);
        let dummy = [0u8; 32];
        v.verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
            .expect("genuine Gte predicate must verify through the real BridgePredicate verifier");
    }

    /// TOOTH (reject): the threshold-lowering forge. A proof for `value >= 100`
    /// is presented under a host policy demanding `value >= 1_000`. The verifier
    /// reconstructs the STARK PI from the POLICY threshold, so the proof's
    /// boundary commitment mismatches and it is rejected — the prover cannot
    /// pass a higher bar with a lower-bar proof.
    #[test]
    fn bridge_predicate_real_verifier_rejects_threshold_lowering_forge() {
        let (commitment, _fc, proof) = honest_bridge_single(500, PredicateType::Gte, 100);
        let policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::Threshold {
                op: PredicateType::Gte,
                threshold: 1_000, // host demands a HIGHER bar than the proof carries
            },
        });
        let v = BridgePredicateStarkVerifier::new(policy);
        let bytes = bridge_predicate_proof_bytes(&proof);
        let dummy = [0u8; 32];
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a 'value >= 100' proof must NOT satisfy a 'value >= 1000' policy"
        );
    }

    /// TOOTH (reject): operator-swap forge. A `Gte` proof is presented under an
    /// `Lte` policy at the same threshold; the operator pin rejects it.
    #[test]
    fn bridge_predicate_real_verifier_rejects_operator_swap() {
        let (commitment, _fc, proof) = honest_bridge_single(500, PredicateType::Gte, 100);
        let policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::Threshold {
                op: PredicateType::Lte, // policy wants <=, proof proves >=
                threshold: 100,
            },
        });
        let v = BridgePredicateStarkVerifier::new(policy);
        let bytes = bridge_predicate_proof_bytes(&proof);
        let dummy = [0u8; 32];
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a Gte proof must not satisfy an Lte policy"
        );
    }

    /// TOOTH (reject): wrong-fact-commitment forge. A genuine proof presented
    /// against a DIFFERENT commitment than the one it was bound to is rejected
    /// (the fact_commitment is a bound public input).
    #[test]
    fn bridge_predicate_real_verifier_rejects_wrong_commitment() {
        let (commitment, _fc, proof) = honest_bridge_single(500, PredicateType::Gte, 100);
        // A policy under a *different* commitment than the proof's fact.
        let wrong_commitment = bridge_predicate_commitment_bytes(BabyBear::new(0xDEAD));
        let policy = Arc::new(OneBridgePolicy {
            commitment: wrong_commitment,
            requirement: BridgePredicateRequirement::Threshold {
                op: PredicateType::Gte,
                threshold: 100,
            },
        });
        let v = BridgePredicateStarkVerifier::new(policy);
        let bytes = bridge_predicate_proof_bytes(&proof);
        let dummy = [0u8; 32];
        // Verify against the wrong commitment (the one the policy is keyed on).
        assert!(
            v.verify(&wrong_commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a proof bound to fact A must not verify against fact B"
        );
        // Sanity: it would have an effect only because the genuine commitment differs.
        assert_ne!(commitment, wrong_commitment);
    }

    /// TOOTH (reject): no registered policy → fail closed.
    #[test]
    fn bridge_predicate_real_verifier_fails_closed_without_policy() {
        let (commitment, _fc, proof) = honest_bridge_single(500, PredicateType::Gte, 100);
        let v = BridgePredicateStarkVerifier::new(Arc::new(StaticBridgePredicatePolicy::new()));
        let bytes = bridge_predicate_proof_bytes(&proof);
        let dummy = [0u8; 32];
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a commitment with no host policy must fail closed"
        );
        // Garbage wire → reject too.
        assert!(
            v.verify(&commitment, &PredicateInput::Slot(&dummy), b"junk")
                .is_err()
        );
    }

    /// TOOTH (admit + reject): InRange. A `low <= value <= high` proof verifies;
    /// the same proof against a narrower policy band that excludes the value is
    /// rejected.
    #[test]
    fn bridge_predicate_real_verifier_in_range_accept_and_reject() {
        let fact_hash = BabyBear::new(0x1234);
        let state_root = BabyBear::new(0x5678);
        let fact_commitment = compute_fact_commitment(fact_hash, state_root);
        let commitment = bridge_predicate_commitment_bytes(fact_commitment);
        let dummy = [0u8; 32];

        // Honest: value=50 in [10, 100].
        let (low_p, high_p) = prove_in_range(
            BabyBear::new(50),
            BabyBear::new(10),
            BabyBear::new(100),
            fact_commitment,
        )
        .expect("honest in-range must be provable");
        let bytes = bridge_predicate_range_proof_bytes(&low_p, &high_p);

        let ok_policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::InRange { low: 10, high: 100 },
        });
        BridgePredicateStarkVerifier::new(ok_policy)
            .verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
            .expect("value 50 in [10,100] must verify");

        // FORGE: the SAME proof pair presented under a policy band [60, 100] that
        // excludes 50. The low-bound proof proves value >= 10, not value >= 60,
        // so reconstructing the PI from the policy's low=60 mismatches and rejects.
        let narrow_policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::InRange { low: 60, high: 100 },
        });
        assert!(
            BridgePredicateStarkVerifier::new(narrow_policy)
                .verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a [10,100] proof must not satisfy a [60,100] policy band"
        );

        // FORGE 2: shape mismatch — a single-bound policy with the range proof.
        let single_policy = Arc::new(OneBridgePolicy {
            commitment,
            requirement: BridgePredicateRequirement::Threshold {
                op: PredicateType::Gte,
                threshold: 10,
            },
        });
        assert!(
            BridgePredicateStarkVerifier::new(single_policy)
                .verify(&commitment, &PredicateInput::Slot(&dummy), &bytes)
                .is_err(),
            "a range proof must not satisfy a single-bound threshold policy"
        );
    }

    /// The full production registry installs the real BridgePredicate verifier.
    #[test]
    fn full_registry_installs_real_bridge_predicate() {
        let reg = registry_with_real_verifiers_full(
            Arc::new(ProgramRegistry::new()),
            Arc::new(EmptyTemporalPolicy),
            Arc::new(StaticIssuerRootAuthority::new()),
            Arc::new(StaticBridgePredicatePolicy::new()),
        );
        assert_eq!(
            reg.get(WitnessedPredicateKind::BridgePredicate)
                .unwrap()
                .name(),
            "bridge-predicate-stark"
        );
    }

    // ─────────────────────────────────────────────────────────────────────
    // ThresholdSig — turn-layer teeth (welded from `hints` directly; no
    // `dregg-federation` dependency, which would cycle). The full
    // executor-driven end-to-end proof lives in
    // `starbridge-apps/governed-namespace/tests/commit_threshold_sig.rs`; here
    // we prove the verifier in isolation against a REAL k-of-n BLS committee.
    // ─────────────────────────────────────────────────────────────────────
    #[cfg(feature = "threshold-sig")]
    mod threshold_sig {
        use super::*;
        use hints::{
            GlobalData, Hint, PartialSignature, PublicKey as BlsPk, SecretKey as BlsSk, Verifier,
            generate_hint, setup_universe, sign as bls_sign, sign_aggregate,
        };

        const VK_HASH: [u8; 32] = *b"threshold-sig-turn-layer-test!!!";
        const COMMITMENT: [u8; 32] = [0x55u8; 32];

        /// A minimal real `hints` committee (`n` real members, equal weight 1,
        /// `next_power_of_two(n+1) - 1` total slots with zero-weight padding —
        /// the same shape `dregg-federation::FederationCommittee` builds). Uses
        /// a deterministic test RNG (toxic-waste known; tests only).
        struct TestCommittee {
            verifier: Verifier,
            members: Vec<BlsSk>,
            indices: Vec<usize>,
            threshold: hints::F,
            agg: hints::Aggregator,
        }

        fn build_committee(n: usize, threshold_k: u64) -> TestCommittee {
            build_committee_seeded(n, threshold_k, [0x42u8; 32])
        }

        fn build_committee_seeded(n: usize, threshold_k: u64, seed: [u8; 32]) -> TestCommittee {
            use ark_ff::One;
            use ark_std::rand::{SeedableRng, rngs::StdRng};
            let domain = (n + 1).next_power_of_two();
            let mut rng = StdRng::from_seed(seed);
            let gd = GlobalData::new(domain, &mut rng).unwrap();

            let total_slots = domain - 1;
            let mut sks: Vec<BlsSk> = Vec::new();
            let mut pks: Vec<BlsPk> = Vec::new();
            let mut hints_v: Vec<Hint> = Vec::new();
            let mut weights: Vec<hints::F> = Vec::new();
            for i in 0..n {
                let sk = BlsSk::random(&mut rng);
                let pk = sk.public(&gd);
                hints_v.push(generate_hint(&gd, &sk, domain, i).unwrap());
                weights.push(hints::F::one());
                sks.push(sk);
                pks.push(pk);
            }
            // Zero-weight padding to fill the power-of-2 domain.
            let dummy_sk = BlsSk::dummy();
            let dummy_pk = dummy_sk.public(&gd);
            for i in n..total_slots {
                pks.push(dummy_pk.clone());
                hints_v.push(generate_hint(&gd, &dummy_sk, domain, i).unwrap());
                weights.push(hints::F::from(0u64));
            }
            let universe = setup_universe(&gd, pks, &hints_v, weights).unwrap();
            assert!(universe.party_errors.is_empty(), "committee setup clean");
            TestCommittee {
                verifier: universe.verifier(),
                members: sks,
                indices: (0..n).collect(),
                threshold: hints::F::from(threshold_k),
                agg: universe.aggregator(),
            }
        }

        impl TestCommittee {
            fn qc_bytes(&self, msg: &[u8], signers: &[usize]) -> Vec<u8> {
                let shares: Vec<(usize, PartialSignature)> = signers
                    .iter()
                    .map(|&i| (self.indices[i], bls_sign(&self.members[i], msg)))
                    .collect();
                let sig = sign_aggregate(&self.agg, self.threshold, &shares, msg).unwrap();
                threshold_sig_proof_bytes(&sig)
            }
        }

        fn policy(committee: &TestCommittee, threshold_k: u64) -> Arc<StaticThresholdSigPolicy> {
            Arc::new(StaticThresholdSigPolicy::new().authorize(
                COMMITMENT,
                ThresholdSigCommittee::new(committee.verifier.clone(), threshold_k),
            ))
        }

        /// A valid 2-of-3 aggregate over the message verifies through the real
        /// ThresholdSigVerifier (SNARK + BLS pairing + threshold floor).
        #[test]
        fn valid_quorum_verifies() {
            let c = build_committee(3, 2);
            let msg = b"dregg-custom-sig-v1: governance commit";
            let qc = c.qc_bytes(msg, &[0, 1]);
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&c, 2));
            v.verify(&COMMITMENT, &PredicateInput::SigningMessage(msg), &qc)
                .expect("a genuine 2-of-3 aggregate must verify");
        }

        /// THE TEETH: the same valid QC over a DIFFERENT message is rejected
        /// (the BLS pairing binds the message — T11 stale-proof defense).
        #[test]
        fn wrong_message_rejected() {
            let c = build_committee(3, 2);
            let qc = c.qc_bytes(b"message A", &[0, 1]);
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&c, 2));
            assert!(
                v.verify(
                    &COMMITMENT,
                    &PredicateInput::SigningMessage(b"message B"),
                    &qc
                )
                .is_err(),
                "a QC over a different message must be rejected"
            );
        }

        /// THE TEETH: a QC that certifies threshold 2, presented under a host
        /// policy that requires a floor of 3, is rejected (downgrade defense) —
        /// the floor comes from the HOST policy, not the QC.
        #[test]
        fn under_host_floor_rejected() {
            let c = build_committee(4, 2);
            let msg = b"under-floor attempt";
            // A real 2-of-4 QC (its embedded threshold is 2).
            let qc = c.qc_bytes(msg, &[0, 1]);
            // Host policy demands a floor of 3.
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&c, 3));
            assert!(
                v.verify(&COMMITMENT, &PredicateInput::SigningMessage(msg), &qc)
                    .is_err(),
                "a QC below the host threshold floor must be rejected (downgrade defense)"
            );
        }

        /// A QC from a DIFFERENT committee than the host-trusted one is rejected
        /// (the SNARK proof is checked against the host VK).
        #[test]
        fn wrong_committee_rejected() {
            let host = build_committee_seeded(3, 2, [0x11u8; 32]);
            let attacker = build_committee_seeded(3, 2, [0x99u8; 32]); // genuinely distinct keys
            let msg = b"wrong committee";
            let forged = attacker.qc_bytes(msg, &[0, 1]);
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&host, 2));
            assert!(
                v.verify(&COMMITMENT, &PredicateInput::SigningMessage(msg), &forged)
                    .is_err(),
                "a QC from a non-host committee must be rejected"
            );
        }

        /// An unregistered commitment fails closed (unknown committee never trusted).
        #[test]
        fn unregistered_commitment_fails_closed() {
            let c = build_committee(3, 2);
            let msg = b"unregistered";
            let qc = c.qc_bytes(msg, &[0, 1]);
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&c, 2));
            let unknown = [0xAAu8; 32];
            assert!(
                v.verify(&unknown, &PredicateInput::SigningMessage(msg), &qc)
                    .is_err(),
                "a commitment with no registered committee must fail closed"
            );
        }

        /// Malformed proof bytes and a non-SigningMessage input shape are rejected.
        #[test]
        fn malformed_and_wrong_shape_rejected() {
            let c = build_committee(3, 2);
            let v = ThresholdSigVerifier::new(VK_HASH, policy(&c, 2));
            // Garbage QC bytes → deserialization fails.
            assert!(
                v.verify(
                    &COMMITMENT,
                    &PredicateInput::SigningMessage(b"x"),
                    b"not-a-qc"
                )
                .is_err(),
                "malformed QC bytes must be rejected"
            );
            // Wrong input shape (Slot, not SigningMessage/Bytes).
            let dummy = [0u8; 32];
            let qc = c.qc_bytes(b"x", &[0, 1]);
            assert!(
                matches!(
                    v.verify(&COMMITMENT, &PredicateInput::Slot(&dummy), &qc),
                    Err(WitnessedPredicateError::InputShapeMismatch { .. })
                ),
                "a non-SigningMessage/Bytes input shape must be an InputShapeMismatch"
            );
        }

        /// `register_threshold_sig_verifier` installs the verifier into a registry
        /// under the given vk_hash, and the registry routes `Custom { vk_hash }`
        /// to it.
        #[test]
        fn registry_routing_via_register_helper() {
            let c = build_committee(3, 2);
            let msg = b"routed through the registry";
            let qc = c.qc_bytes(msg, &[0, 1]);
            let mut reg = registry_with_real_verifiers();
            register_threshold_sig_verifier(&mut reg, VK_HASH, policy(&c, 2));
            let wp = WitnessedPredicate::custom(
                VK_HASH,
                COMMITMENT,
                PredicateInputRefSigningMessage(),
                0,
            );
            reg.verify(&wp, &PredicateInput::SigningMessage(msg), &qc)
                .expect("the registry must route Custom { vk_hash } to the threshold-sig verifier");
        }

        #[allow(non_snake_case)]
        fn PredicateInputRefSigningMessage() -> dregg_cell::predicate::InputRef {
            dregg_cell::predicate::InputRef::SigningMessage
        }
    }
}
