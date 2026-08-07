//! The shielded transfer's **VALUE LINK** — the Rust half that CALLS the Lean-emitted
//! `dregg-shielded-transfer-value-link::v1` relation
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLinkEmit.lean`).
//!
//! **THE AIR IS AUTHORED IN LEAN.** This module reads the byte-pinned golden out of the Lean
//! source, produces a WITNESS TRACE that satisfies it, and proves/verifies through the hiding
//! IR-v2 backend. It authors NO constraint.
//!
//! ## The residual this closes
//!
//! `turn-prover/src/shielded_transfer_verifier.rs` carried this, verbatim, at HEAD:
//!
//! > the Pedersen leg's own `v` is bound to the STARK-side `v` only through this TRANSCRIPT, not
//! > by an equality the circuit enforces … The wide join makes both proofs open the SAME
//! > `(value, asset)` as each other; it does not make either of them open the value the Ristretto
//! > commitment holds.
//!
//! A spender who genuinely owned a note worth `1` published input and output Ristretto legs
//! committing to `1_000_000`; `verify_full_conservation_bytes` cleared `Σ C_in = Σ C_out` over
//! those PROVER-CHOSEN legs, the complete-spend STARK proved membership of the REAL note, and
//! nothing compared the two. The value the transfer moved was decided by the leg.
//!
//! **There is no check that closes that across the two systems.** A BabyBear STARK cannot open a
//! Ristretto point without non-native curve arithmetic in-AIR, and a Ristretto sigma protocol
//! cannot open a Poseidon2 image without the hash in-group. `cell-crypto/src/value_link_zk.rs`
//! records the same finding and names the exit: *"faithfully encode value/asset in a wide in-AIR
//! hash commitment and enforce no-mint in AIR."* So the Pedersen leg is GONE, and with it the two
//! systems it straddled.
//!
//! ## What the relation says (164 columns, 17 PIs `wide[16] ++ [outCm]`)
//!
//! Over a private witness `(value, asset, inRand, inBlind[6], outOwner, outRand)`:
//!
//! * `value` and `asset` ride four canonical 16-bit limb cells each, booleanity FORCED in the AIR
//!   (128 boolean pins + 8 recompositions) — so `0 ≤ value < 2^64` is a property of the trace, not
//!   a Bulletproof;
//! * the SIXTEEN published lanes are `cap_node8` at `DOMAIN_A`/`DOMAIN_B` over
//!   `[domain, v0..v3, a0..a3, inRand, inBlind0..5]` — the SAME absorb block, column for column,
//!   that `WideValueBindingEmit` and the complete spend's `carrierPins` use (the Lean file imports
//!   those absorb terms rather than re-typing them);
//! * the published `outCm` is `hash_fact(value mod p, [asset mod p, outOwner, outRand])` — the
//!   deployed note commitment, over the SAME recomposed felts.
//!
//! **The link is that the carrier and the note commitment read one set of limb columns.** There is
//! no second value in the trace, so a satisfying assignment in which the minted note is worth more
//! than the spent one does not exist.
//!
//! ## Why the verifier's inputs make it non-vacuous
//!
//! [`verify_shielded_transfer_link`] takes the sixteen lanes from the CALLER, not from the proof's
//! own claim, and the caller is [`crate::shielded::ShieldedTransfer::verify`], which reads them off
//! the complete-spend proof's PI-pinned `wide[16]` AFTER that proof has verified against the
//! executor's committed root. So the carrier is a public input of a SEPARATE, already-checked
//! proof — the same discipline `ShieldedWideJoinPin.join_still_decouples` names for the sidecar
//! join, and the reason this is a binding and not a claim handed back to itself.

use std::sync::LazyLock;

use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriReference,
    Plonky3HidingFriWitness,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::stark_zk::DreggZkStarkConfig;

use super::wide_value_binding::{
    BINDING_BLIND_LANES, DOMAIN_A, DOMAIN_B, LIMB_BITS, U64_LIMBS, WIDE_VALUE_BINDING_LANES,
};

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLinkEmit.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module (the shared
/// `wide_value_binding.rs` / `spend_complete.rs` convention — one splitter).
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
pub fn shielded_transfer_value_link_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "SHIELDED_TRANSFER_VALUE_LINK_GOLDEN")
}

/// Parse-once cache of the Lean-emitted relation.
///
/// The two asserts are the DETECTOR for this file's witness-layout mirror: if the Lean author moves
/// the width or the public-input count, first use goes red HERE rather than silently producing a
/// witness for a layout that no longer exists.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(shielded_transfer_value_link_descriptor_json())
        .expect("the Lean-emitted shielded transfer value-link descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors \
         ShieldedTransferValueLinkEmit.lean §1"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors \
         ShieldedTransferValueLinkEmit.lean §2"
    );
    desc
});

/// The Lean-emitted value-link relation.
pub fn shielded_transfer_value_link_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

/// **Witness-layout mirror** of the Lean column layout (`ShieldedTransferValueLinkEmit.lean` §1,
/// whose named theorems pin every index below). Authors no algebra — it only says where the trace
/// producer places each cell — and [`LEAN_DESCRIPTOR`] checks it against the emitted width.
pub mod col {
    use super::{BINDING_BLIND_LANES, LIMB_BITS, U64_LIMBS};

    /// `cV i` — value limb `i` (little-endian), shared by the carrier and the output commitment.
    pub const VALUE_LIMBS: usize = 0;
    /// `cA i` — asset limb `i`.
    pub const ASSET_LIMBS: usize = VALUE_LIMBS + U64_LIMBS;
    /// `cVMOD` — `value mod p`.
    pub const VALUE_MOD_P: usize = ASSET_LIMBS + U64_LIMBS;
    /// `cAMOD` — `asset mod p`.
    pub const ASSET_MOD_P: usize = VALUE_MOD_P + 1;
    /// `cRAND` — the SPENT note's randomness.
    pub const IN_RANDOMNESS: usize = ASSET_MOD_P + 1;
    /// `cBL i` — the SPENT note's carrier blind lane `i`.
    pub const IN_BLIND: usize = IN_RANDOMNESS + 1;
    /// `cOWNER` — the MINTED note's owner felt.
    pub const OUT_OWNER: usize = IN_BLIND + BINDING_BLIND_LANES;
    /// `cORAND` — the MINTED note's randomness.
    pub const OUT_RANDOMNESS: usize = OUT_OWNER + 1;
    /// `cWA j` — `DOMAIN_A` carrier lane `j`.
    pub const WIDE_A: usize = OUT_RANDOMNESS + 1;
    /// `cWB j` — `DOMAIN_B` carrier lane `j`.
    pub const WIDE_B: usize = WIDE_A + 8;
    /// `cOUTCM` — the MINTED note's commitment.
    pub const OUT_CM: usize = WIDE_B + 8;
    /// `BITS_BASE` — base of the bit-decomposition block.
    pub const BITS: usize = OUT_CM + 1;
    /// `LINK_WIDTH` — the main-trace width.
    pub const WIDTH: usize = BITS + 2 * U64_LIMBS * LIMB_BITS;

    /// `cBit k i b`.
    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        BITS + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// **Public-input layout mirror** `[wide_binding[0..16], out_note_commitment]`
/// (`ShieldedTransferValueLinkEmit.lean` §2).
pub mod pi {
    /// First lane of the SPENT note's carrier — supplied by the verifier from the complete-spend
    /// proof's own public inputs, never by this proof's claim.
    pub const WIDE_BINDING: usize = 0;
    /// The MINTED note's commitment felt.
    pub const OUT_CM: usize = 16;
    /// Total public-input count.
    pub const COUNT: usize = 17;
}

fn u64_limbs(value: u64) -> [u16; U64_LIMBS] {
    core::array::from_fn(|i| ((value >> (i * LIMB_BITS)) & 0xffff) as u16)
}

fn u64_mod_p(value: u64) -> BabyBear {
    BabyBear::new((value % BABYBEAR_P as u64) as u32)
}

/// The private witness for one input→output value link.
///
/// `value`, `asset_type`, `in_randomness` and `in_binding_blind` are the SPENT note's — they must
/// be the same values the complete-spend witness carries, or the sixteen lanes this proof publishes
/// will not equal the ones that proof PI-pins and the join refuses. `out_owner` and
/// `out_randomness` are the MINTED note's, and they are the only things about the output a sender
/// chooses: not its value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedTransferLinkWitness {
    /// The spent note's full, unreduced value — and therefore the minted note's.
    pub value: u64,
    /// The spent note's full, unreduced asset identifier — and therefore the minted note's.
    pub asset_type: u64,
    /// The spent note's randomness (absorbed by the carrier the spend proof published).
    pub in_randomness: BabyBear,
    /// The spent note's six carrier blind lanes.
    pub in_binding_blind: [BabyBear; BINDING_BLIND_LANES],
    /// The MINTED note's owner felt — `hash_fact(key0,[key1,key2,key3])` of the recipient's
    /// spending key, which is what makes the new note spendable by them and nobody else.
    pub out_owner: BabyBear,
    /// The MINTED note's randomness. Freshly chosen; it is what makes the published commitment
    /// hiding even when the same value moves twice.
    pub out_randomness: BabyBear,
}

impl ShieldedTransferLinkWitness {
    /// The sixteen-lane carrier of the SPENT note — bit-identical to
    /// `WideValueBindingWitness::wide_binding` and to the complete-spend proof's PI-pinned
    /// `wide[16]` for the same opening. (One absorb block, three producers.)
    pub fn in_wide_binding(&self) -> [BabyBear; WIDE_VALUE_BINDING_LANES] {
        let value = u64_limbs(self.value);
        let asset = u64_limbs(self.asset_type);
        let right = [
            BabyBear::new(asset[3] as u32),
            self.in_randomness,
            self.in_binding_blind[0],
            self.in_binding_blind[1],
            self.in_binding_blind[2],
            self.in_binding_blind[3],
            self.in_binding_blind[4],
            self.in_binding_blind[5],
        ];
        let left = |domain| {
            [
                BabyBear::new(domain),
                BabyBear::new(value[0] as u32),
                BabyBear::new(value[1] as u32),
                BabyBear::new(value[2] as u32),
                BabyBear::new(value[3] as u32),
                BabyBear::new(asset[0] as u32),
                BabyBear::new(asset[1] as u32),
                BabyBear::new(asset[2] as u32),
            ]
        };
        let a = cap_node8(left(DOMAIN_A), right);
        let b = cap_node8(left(DOMAIN_B), right);
        let mut out = [BabyBear::ZERO; WIDE_VALUE_BINDING_LANES];
        out[..8].copy_from_slice(&a);
        out[8..].copy_from_slice(&b);
        out
    }

    /// The MINTED note's commitment felt — `hash_fact(value mod p, [asset mod p, owner, rand])`,
    /// the SAME site `ShieldedSpendCompleteWitness::note_commitment_felt` opens and
    /// `dregg-shielded-shield::v1` mints. That identity is what makes the output SPENDABLE: the
    /// complete-spend relation can open this leaf, so the value that arrives can leave again.
    pub fn out_note_commitment_felt(&self) -> BabyBear {
        hash_fact(
            u64_mod_p(self.value),
            &[
                u64_mod_p(self.asset_type),
                self.out_owner,
                self.out_randomness,
            ],
        )
    }
}

/// Generate a constant two-row trace in the LEAN column layout, and its public claim.
///
/// The returned matrix is the descriptor-width MAIN trace; the IR-v2 prover fills the Poseidon2
/// chip lanes itself (`trace_with_chip_lanes`).
pub fn generate_shielded_transfer_link_trace(
    witness: &ShieldedTransferLinkWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let value = u64_limbs(witness.value);
    let asset = u64_limbs(witness.asset_type);
    let wide = witness.in_wide_binding();
    let out_cm = witness.out_note_commitment_felt();

    let mut row = vec![BabyBear::ZERO; col::WIDTH];
    for i in 0..U64_LIMBS {
        row[col::VALUE_LIMBS + i] = BabyBear::new(value[i] as u32);
        row[col::ASSET_LIMBS + i] = BabyBear::new(asset[i] as u32);
        for bit in 0..LIMB_BITS {
            row[col::bit(0, i, bit)] = BabyBear::new(((value[i] >> bit) & 1) as u32);
            row[col::bit(1, i, bit)] = BabyBear::new(((asset[i] >> bit) & 1) as u32);
        }
    }
    row[col::VALUE_MOD_P] = u64_mod_p(witness.value);
    row[col::ASSET_MOD_P] = u64_mod_p(witness.asset_type);
    row[col::IN_RANDOMNESS] = witness.in_randomness;
    row[col::IN_BLIND..col::IN_BLIND + BINDING_BLIND_LANES]
        .copy_from_slice(&witness.in_binding_blind);
    row[col::OUT_OWNER] = witness.out_owner;
    row[col::OUT_RANDOMNESS] = witness.out_randomness;
    row[col::WIDE_A..col::WIDE_A + 8].copy_from_slice(&wide[..8]);
    row[col::WIDE_B..col::WIDE_B + 8].copy_from_slice(&wide[8..]);
    row[col::OUT_CM] = out_cm;

    let mut public_inputs = Vec::with_capacity(pi::COUNT);
    public_inputs.extend_from_slice(&wide);
    public_inputs.push(out_cm);
    (vec![row.clone(), row], public_inputs)
}

/// The public claim a value-link proof is checked against.
///
/// ⚑ Held for CONSTRUCTION and for tests. The deployed verifier does NOT trust it: it builds the
/// statement from the complete-spend proof's carrier and the wire's published note commitment
/// ([`verify_shielded_transfer_link`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedTransferLinkClaim {
    /// The SPENT note's sixteen carrier lanes.
    pub in_wide_binding: [BabyBear; WIDE_VALUE_BINDING_LANES],
    /// The MINTED note's commitment felt.
    pub out_note_commitment: BabyBear,
}

impl ShieldedTransferLinkClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(pi::COUNT);
        out.extend_from_slice(&self.in_wide_binding);
        out.push(self.out_note_commitment);
        out
    }
}

/// A hiding proof that the sixteen published carrier lanes and the published output note
/// commitment open to ONE `(value, asset)`.
pub struct ShieldedTransferLinkProof {
    /// The public claim (construction-side; the deployed verifier supplies its own).
    pub claim: ShieldedTransferLinkClaim,
    /// The hiding IR-v2 proof. Value, asset, both randomnesses, the blind lanes and the recipient
    /// owner all stay witness-only.
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl ShieldedTransferLinkProof {
    /// Canonical postcard encoding for the wire's `link_proof` field.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("Ir2BatchProof postcard serialize")
    }
}

/// Errors from value-link construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedTransferLinkError {
    /// The statement (relation + public inputs) was rejected before proving/verifying.
    StatementRejected { reason: String },
    /// Proving failed.
    ProveFailed { reason: String },
    /// The serialized proof failed to deserialize.
    ProofDecode { reason: String },
    /// **The value-link refusal.** The proof does not verify against the carrier the complete-spend
    /// proof published together with the note commitment this transfer wants to append — i.e. the
    /// minted note does not open to the value the spent note holds.
    ProofRejected { reason: String },
    /// A published note commitment is not the canonical `felt_to_bytes32` encoding of a BabyBear
    /// element (four little-endian bytes, twenty-eight zero). Accepting anything else would let a
    /// leaf be appended that no spend can ever open.
    NonCanonicalNoteCommitment { bytes: [u8; 32] },
}

impl core::fmt::Display for ShieldedTransferLinkError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StatementRejected { reason } => {
                write!(f, "shielded value-link statement rejected: {reason}")
            }
            Self::ProveFailed { reason } => {
                write!(f, "shielded value-link proving failed: {reason}")
            }
            Self::ProofDecode { reason } => {
                write!(
                    f,
                    "shielded value-link proof failed to deserialize: {reason}"
                )
            }
            Self::ProofRejected { reason } => write!(
                f,
                "shielded value-link REFUSED: the output note commitment does not open to the \
                 value the spent note's carrier binds ({reason})"
            ),
            Self::NonCanonicalNoteCommitment { bytes } => write!(
                f,
                "shielded output note commitment {bytes:02x?} is not a canonical felt encoding"
            ),
        }
    }
}

impl std::error::Error for ShieldedTransferLinkError {}

/// The backend-neutral statement: the Lean relation plus these canonical public inputs.
fn statement_for(
    public_inputs: &[BabyBear],
) -> Result<DescriptorStatement, ShieldedTransferLinkError> {
    DescriptorStatement::try_new(
        shielded_transfer_value_link_descriptor().clone(),
        public_inputs.iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| ShieldedTransferLinkError::StatementRejected { reason })
}

/// Prove one input→output value link through the hiding path.
pub fn prove_shielded_transfer_link(
    witness: &ShieldedTransferLinkWitness,
) -> Result<ShieldedTransferLinkProof, ShieldedTransferLinkError> {
    let (trace, pis) = generate_shielded_transfer_link_trace(witness);
    let statement = statement_for(&pis)?;
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
    .map_err(|reason| ShieldedTransferLinkError::ProveFailed { reason })?;
    let mut in_wide_binding = [BabyBear::ZERO; WIDE_VALUE_BINDING_LANES];
    in_wide_binding.copy_from_slice(&pis[pi::WIDE_BINDING..pi::OUT_CM]);
    Ok(ShieldedTransferLinkProof {
        claim: ShieldedTransferLinkClaim {
            in_wide_binding,
            out_note_commitment: pis[pi::OUT_CM],
        },
        proof,
    })
}

/// **THE VALUE-LINK GATE.**
///
/// Verify a serialized value-link proof against public inputs the CALLER supplies:
///
/// * `spend_wide_binding` — the sixteen carrier lanes the input's complete-spend proof PI-pins,
///   read off that proof AFTER it verified under the executor's committed root;
/// * `out_note_commitment` — the felt the executor is about to append to `note_shielded`.
///
/// Neither comes from this proof's own claim, which is the whole point: the relation forces both to
/// be functions of ONE limb opening, so a transfer that mints a note worth more than it spends has
/// no satisfying trace, and one that mints a note worth *less* has no satisfying trace either.
///
/// **Substrate: the relation is AUTHORED IN LEAN** (`ShieldedTransferValueLinkEmit.lean`, 164
/// columns, 17 PIs, byte-pinned by `link_emits_golden`). Rust supplies the statement and calls the
/// verifier.
pub fn verify_shielded_transfer_link(
    proof_bytes: &[u8],
    spend_wide_binding: &[BabyBear; WIDE_VALUE_BINDING_LANES],
    out_note_commitment: BabyBear,
) -> Result<(), ShieldedTransferLinkError> {
    let proof: Ir2BatchProof<DreggZkStarkConfig> =
        postcard::from_bytes(proof_bytes).map_err(|error| {
            ShieldedTransferLinkError::ProofDecode {
                reason: error.to_string(),
            }
        })?;
    let claim = ShieldedTransferLinkClaim {
        in_wide_binding: *spend_wide_binding,
        out_note_commitment,
    };
    let statement = statement_for(&claim.public_inputs())?;
    Plonky3HidingFriReference::verify(&statement, &proof)
        .map_err(|reason| ShieldedTransferLinkError::ProofRejected { reason })
}

/// Decode a wire note commitment (`dregg_cell::felt_to_bytes32`: four little-endian bytes, the rest
/// zero) back to its felt, refusing anything else.
///
/// This is not decoration. The shielded accumulator addresses a leaf by its RAW 32 bytes, while a
/// SPENDABLE note's address is exactly this four-significant-byte subspace (the complete-spend
/// relation pins `cADDR0`/`cADDR1` and constrains the higher limbs to zero). A commitment outside
/// it could be appended and never opened again — value in, never out.
pub fn note_commitment_felt_from_bytes(
    bytes: &[u8; 32],
) -> Result<BabyBear, ShieldedTransferLinkError> {
    if bytes[4..].iter().any(|b| *b != 0) {
        return Err(ShieldedTransferLinkError::NonCanonicalNoteCommitment { bytes: *bytes });
    }
    let raw = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
    if raw >= BABYBEAR_P {
        return Err(ShieldedTransferLinkError::NonCanonicalNoteCommitment { bytes: *bytes });
    }
    Ok(BabyBear::new(raw))
}
