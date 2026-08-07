//! The SHIELD-OPENING verifier — the Rust half that CALLS the Lean-emitted
//! `dregg-shielded-shield::v1` golden (`metatheory/Dregg2/Circuit/Emit/ShieldedShieldDescriptor.lean`).
//!
//! **The AIR is AUTHORED IN LEAN.** This module reads the byte-pinned golden out of the Lean source,
//! parses it as IR-v2, and proves/verifies through the hiding-FRI backend — it authors NO constraint.
//! The relation proved is the C6 note-commitment opening with the value/asset PUBLIC:
//!
//! ```text
//! piCM = hash_fact(piVALUE, [piASSET, owner, randomness])    (owner, randomness hidden)
//! ```
//!
//! so the minted note commitment binds to the executor-debited PUBLIC value. Its soundness lives in
//! Lean: `ShieldedShieldDescriptor.shield_opening_binds_public_value` (the minted commitment is the
//! note commitment of the public value), `shield_value_decouple_unsat` (a value decoupled from the
//! public PI is UNSAT — mint-worth-more is unrepresentable). This is the on-ramp keystone the executor
//! `Effect::Shield` handler will call so its GATE-4 append of `piCM` (replacing the prover's Pedersen
//! bytes) is bound to the debited value — `ShieldedOnRampPin §3`'s `shieldAppend_is_ledger_note`.
//!
//! NOT wired into the executor yet: the `apply_shield` handler (the money-moving debit + append) is the
//! next pass; this is the sound, non-money-moving verifier it depends on.

use std::sync::LazyLock;

use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriReference,
    Plonky3HidingFriWitness,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::stark_zk::DreggZkStarkConfig;

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/ShieldedShieldDescriptor.lean");

/// Column layout — mirrors `ShieldedShieldDescriptor.lean §1` (checked against the parsed width).
mod col {
    pub const VALUE: usize = 0;
    pub const ASSET: usize = 1;
    pub const OWNER: usize = 2;
    pub const RAND: usize = 3;
    pub const CM: usize = 4;
    pub const WIDTH: usize = 5;
}
/// Public-input layout — mirrors `ShieldedShieldDescriptor.lean §1` (checked against the parsed count).
mod pi {
    pub const COUNT: usize = 3;
}

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module (the
/// `wide_value_binding.rs` pattern — one splitter, one convention).
fn lean_raw_golden(source: &'static str, name: &str) -> &'static str {
    let open = format!("def {name} : String := r#\"");
    let (_, after) = source
        .split_once(open.as_str())
        .unwrap_or_else(|| panic!("the Lean module still exposes {name}"));
    let (json, _) = after
        .split_once("\"#")
        .unwrap_or_else(|| panic!("{name} remains a raw string"));
    json
}

/// The byte-pinned IR-v2 wire string, read out of the Lean source.
pub fn shield_opening_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "SHIELDED_SHIELD_GOLDEN")
}

/// Parse-once cache of the Lean-emitted relation; the asserts detect a Lean layout move.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(shield_opening_descriptor_json())
        .expect("the Lean-emitted shield-opening descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors ShieldedShieldDescriptor.lean §1"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors ShieldedShieldDescriptor.lean §1"
    );
    desc
});

/// The Lean-emitted shield-opening relation.
pub fn shield_opening_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

#[derive(Debug)]
pub enum ShieldOpeningError {
    StatementRejected { reason: String },
    ProveFailed { reason: String },
    VerifyFailed { reason: String },
}

/// The public claim carried alongside a shield-opening proof: the minted note commitment binds this
/// PUBLIC `(value, asset)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldOpeningClaim {
    pub value: BabyBear,
    pub asset: BabyBear,
    pub note_commitment: BabyBear,
}

impl ShieldOpeningClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        vec![self.value, self.asset, self.note_commitment]
    }
}

/// A hiding shield-opening proof plus its public claim.
pub struct ShieldOpeningProof {
    pub claim: ShieldOpeningClaim,
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

fn statement_for(claim: &ShieldOpeningClaim) -> Result<DescriptorStatement, ShieldOpeningError> {
    DescriptorStatement::try_new(
        shield_opening_descriptor().clone(),
        claim.public_inputs().iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| ShieldOpeningError::StatementRejected { reason })
}

/// The note commitment of a preimage — the C6 site, byte-twin of the Lean chip absorb
/// `factIns [value, asset, owner, rand] = [value, asset, owner, rand, 0, 0xFACF, 1]`
/// (`hash_fact` sets `state[0]=value`, `state[1..4]=asset,owner,rand`, `state[5]=0xFACF`, `state[6]=1`).
pub fn shield_note_commitment(
    value: BabyBear,
    asset: BabyBear,
    owner: BabyBear,
    randomness: BabyBear,
) -> BabyBear {
    hash_fact(value, &[asset, owner, randomness])
}

/// Generate the constant MAIN trace in the Lean column layout, and its public claim. The IR-v2 prover
/// fills the Poseidon2 chip lanes itself.
fn generate_trace(
    value: BabyBear,
    asset: BabyBear,
    owner: BabyBear,
    randomness: BabyBear,
) -> (Vec<Vec<BabyBear>>, ShieldOpeningClaim) {
    let cm = shield_note_commitment(value, asset, owner, randomness);
    let mut row = vec![BabyBear::ZERO; col::WIDTH];
    row[col::VALUE] = value;
    row[col::ASSET] = asset;
    row[col::OWNER] = owner;
    row[col::RAND] = randomness;
    row[col::CM] = cm;
    (
        vec![row.clone(), row],
        ShieldOpeningClaim {
            value,
            asset,
            note_commitment: cm,
        },
    )
}

/// Prove a shield opening for the given (public `value`/`asset`, hidden `owner`/`randomness`).
pub fn prove_shield_opening(
    value: BabyBear,
    asset: BabyBear,
    owner: BabyBear,
    randomness: BabyBear,
) -> Result<ShieldOpeningProof, ShieldOpeningError> {
    let (trace, claim) = generate_trace(value, asset, owner, randomness);
    let statement = statement_for(&claim)?;
    let mem = MemBoundaryWitness::default();
    let umem = UMemBoundaryWitness::default();
    let proof = Plonky3HidingFriReference::prove(
        &statement,
        Plonky3HidingFriWitness {
            base_trace: &trace,
            mem_boundary: &mem,
            map_heaps: &[],
            umem_boundary: &umem,
        },
    )
    .map_err(|reason| ShieldOpeningError::ProveFailed { reason })?;
    Ok(ShieldOpeningProof { claim, proof })
}

/// Verify a shield-opening proof against its public claim `(value, asset, note_commitment)`. The
/// `.piBinding`s force the claim to equal the proven cells, so a claim decoupled from the proof
/// REJECTS — the Rust twin of Lean `shield_value_decouple_unsat`.
pub fn verify_shield_opening(proof: &ShieldOpeningProof) -> Result<(), ShieldOpeningError> {
    let statement = statement_for(&proof.claim)?;
    Plonky3HidingFriReference::verify(&statement, &proof.proof)
        .map_err(|reason| ShieldOpeningError::VerifyFailed { reason })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shield_opening_proves_and_verifies() {
        let p = prove_shield_opening(
            BabyBear::new(100),
            BabyBear::new(1),
            BabyBear::new(7),
            BabyBear::new(9),
        )
        .expect("a genuine shield opening proves");
        verify_shield_opening(&p).expect("a genuine shield opening verifies");
    }

    #[test]
    fn shield_opening_value_decouple_rejects() {
        // A genuine proof for value=100, then CLAIM a different public value (mint-worth-more).
        // The `.piBinding .first cVAL piVALUE` forces value; verify against the tampered claim must
        // REJECT. This is the Rust twin of Lean `shield_value_decouple_unsat`.
        let mut p = prove_shield_opening(
            BabyBear::new(100),
            BabyBear::new(1),
            BabyBear::new(7),
            BabyBear::new(9),
        )
        .expect("a genuine shield opening proves");
        p.claim.value = BabyBear::new(999);
        assert!(
            verify_shield_opening(&p).is_err(),
            "a value decoupled from the proof must not verify — else Shield could mint worth-more"
        );
    }

    #[test]
    fn shield_opening_forged_commitment_rejects() {
        // Claim a note commitment that is NOT hash_fact(value,[asset,owner,rand]) — must reject.
        let mut p = prove_shield_opening(
            BabyBear::new(100),
            BabyBear::new(1),
            BabyBear::new(7),
            BabyBear::new(9),
        )
        .expect("a genuine shield opening proves");
        p.claim.note_commitment = p.claim.note_commitment + BabyBear::new(1);
        assert!(
            verify_shield_opening(&p).is_err(),
            "a commitment not equal to the C6 opening must not verify"
        );
    }
}
