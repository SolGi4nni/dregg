//! Faithful full-`u64` value/asset binding for the shielded-transfer cutover.
//!
//! **THE AIR IS AUTHORED IN LEAN.** `metatheory/Dregg2/Circuit/Emit/WideValueBindingEmit.lean`
//! emits the whole relation — 162 columns, 17 public inputs, 158 IR-v2 constraints — and byte-pins
//! it there with an `emitVmJson2` `#guard`. This module reads that pinned wire string straight out
//! of the Lean source ([`EMIT_LEAN`]), so there is no hand-transcription hop between the author and
//! the consumer. Nothing in this file constructs a constraint; it produces the WITNESS, decodes the
//! Turn wire, and calls the deployed hiding IR-v2 backend.
//!
//! The semantic content lives in `WideValueBindingRefine.lean`, over the ACTUAL emitted object:
//! `limb_canonical` (each limb is FORCED into `[0, 2^16)` — canonicality produced, not assumed),
//! `seventeenth_bit_unsat`, `forged_lane_unsat`, `legacy_is_hash_fact`,
//! `legacy_join_cannot_separate_aliases` (which needs no hypotheses and no crypto: on the pair `v`
//! and `v + p` the legacy site's four inputs are IDENTICAL, so the one-felt join is provably blind
//! for ANY hash), and `alias_separated_by_the_wide_carrier`.
//!
//! ## What the relation says
//!
//! The deployed shielded-spend circuit still exposes a one-felt
//! `hash_fact(value mod p, [asset mod p, randomness, 0])`.  That statement is
//! useful as a compatibility join, but it is not injective on either `u64`:
//! values separated by the BabyBear modulus alias before hashing.  This module
//! carries the native wide carrier that the Turn/no-mint boundary can consume
//! without making that false claim:
//!
//! * value and asset are each represented by four canonical 16-bit limbs;
//! * every limb is bit-constrained in the AIR;
//! * the legacy one-felt representations are recomposed from those limbs modulo
//!   BabyBear and the legacy binding is recomputed in the same AIR;
//! * two domain-separated `node8` Poseidon2 permutations publish sixteen output
//!   felts over the complete limbs plus seven blinding felts.
//!
//! The resulting 16-felt carrier distinguishes every `(value, asset)` pair in
//! the `u64 × u64` domain before hashing and has a much wider collision surface
//! than the compatibility felt.  Turn carries it as mandatory input evidence
//! and the live conservation transcript absorbs all sixteen lanes.  The legacy
//! one-felt note tree remains a separately named migration seam: until note
//! creation precommits this wide carrier (or the combined transfer AIR replaces
//! that tree), the compatibility join alone cannot choose between two distinct
//! full-width openings that reduce to the same felt.
//!
//! ## The backend, and why hiding is not lost
//!
//! Proving/verifying goes through [`Plonky3HidingFriReference`], whose `prove`/`verify` call
//! `prove_vm_descriptor2_for_config` / `verify_vm_descriptor2_with_config` on `create_zk_config()`
//! — the SAME config the retired v1 route (`prove_dsl_zk`) used: salted-leaf hiding MMCS
//! (`HidingFriPcs`, `Pcs::ZK == true`) plus four random extension-field codewords. Value, asset and
//! the seven blinding felts stay witness-only exactly as before.
//!
//! ## The row-domain delta this swap introduces (stated, not hidden)
//!
//! IR-v2 evaluates `VmConstraint2::Base(VmConstraint::Gate _)` inside `builder.when_transition()`
//! (`circuit/src/descriptor_ir2.rs`), whereas the retired v1 `DslP3Air` asserted every
//! `ConstraintExpr` on EVERY row. Lookups carry no row guard and all 17 PI pins are first-row, so
//! the published claim is row 0's — and row 0 is a transition row on any trace of height >= 2, so
//! every gate that constrains the published cells still fires on the row that carries them. The
//! LAST ROW is left unconstrained by the gates and is read by nothing. Closing that would be a
//! `.boundary .last` twin per gate (138 more constraints) on the Lean side; it is not emitted.

use std::sync::LazyLock;

use super::transfer::{ShieldedError, ShieldedTransfer};
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

/// Number of 16-bit limbs in a canonical `u64` encoding.
pub const U64_LIMBS: usize = 4;
/// Bits in each canonical value/asset limb.
pub const LIMB_BITS: usize = 16;
/// Number of independently constrained public binding lanes.
pub const WIDE_VALUE_BINDING_LANES: usize = 16;
/// Extra field-valued blinding lanes, in addition to the legacy randomness felt.
pub const BINDING_BLIND_LANES: usize = 6;

// Two distinct in-band domain separators.  `node8` seeds all sixteen permutation
// lanes directly, so the domain is an explicit first input.  The Lean family pins
// these as literal constants inside the chip tuples (a constant in a tuple cannot
// be tampered), which is why it needs no `domain_a`/`domain_b`/`zero` column.
pub const DOMAIN_A: u32 = 0x5642_4e30; // "VBN0"
pub const DOMAIN_B: u32 = 0x5642_4e31; // "VBN1"

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/WideValueBindingEmit.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module.
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
pub fn wide_value_binding_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "WIDE_VALUE_BINDING_GOLDEN")
}

/// Parse-once cache of the Lean-emitted relation.
///
/// The two asserts are the DETECTOR for this file's witness-layout mirror: if the Lean author
/// moves the width or the public-input count, first use of the sidecar goes red here rather than
/// silently producing a witness for a layout that no longer exists.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(wide_value_binding_descriptor_json())
        .expect("the Lean-emitted wide value binding descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors WideValueBindingEmit.lean §2"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors WideValueBindingEmit.lean §3"
    );
    desc
});

/// The Lean-emitted full-`u64` value/asset binding relation.
pub fn wide_value_binding_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

/// **Witness-layout mirror** of the Lean column layout (`WideValueBindingEmit.lean` §2, whose
/// `#guard`s pin every index below).  This authors no algebra — it only says where the trace
/// producer must place each cell — and [`LEAN_DESCRIPTOR`] checks it against the emitted width.
pub mod col {
    use super::{BINDING_BLIND_LANES, LIMB_BITS, U64_LIMBS};

    /// `cV i` — value limb `i` (little-endian).
    pub const VALUE_LIMBS: usize = 0;
    /// `cA i` — asset limb `i`.
    pub const ASSET_LIMBS: usize = VALUE_LIMBS + U64_LIMBS;
    /// `cVMOD` — the compatibility felt `value mod p`.
    pub const VALUE_MOD_P: usize = ASSET_LIMBS + U64_LIMBS;
    /// `cAMOD` — the compatibility felt `asset mod p`.
    pub const ASSET_MOD_P: usize = VALUE_MOD_P + 1;
    /// `cRAND` — the legacy randomness felt.
    pub const RANDOMNESS: usize = ASSET_MOD_P + 1;
    /// `cBL i` — binding blind lane `i`.
    pub const BLIND: usize = RANDOMNESS + 1;
    /// `cLEGACY` — the compatibility one-felt binding.
    pub const LEGACY_BINDING: usize = BLIND + BINDING_BLIND_LANES;
    /// `cWA j` — `DOMAIN_A` carrier lane `j`.
    pub const WIDE_A: usize = LEGACY_BINDING + 1;
    /// `cWB j` — `DOMAIN_B` carrier lane `j`.
    pub const WIDE_B: usize = WIDE_A + 8;
    /// `BITS_BASE` — base of the bit-decomposition block.
    pub const BITS: usize = WIDE_B + 8;
    /// `WVB_WIDTH` — the main-trace width.
    pub const WIDTH: usize = BITS + 2 * U64_LIMBS * LIMB_BITS;

    /// `cLimb k i`.
    pub const fn limb(kind: usize, i: usize) -> usize {
        if kind == 0 {
            VALUE_LIMBS + i
        } else {
            ASSET_LIMBS + i
        }
    }

    /// `cBit k i b`.
    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        BITS + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// **Public-input layout mirror** `[legacy_binding, wide_binding[0..16]]`
/// (`WideValueBindingEmit.lean` §3).
pub mod pi {
    /// Compatibility join to the current shielded-spend C7 public input.
    pub const LEGACY_BINDING: usize = 0;
    /// First lane of the faithful wide binding.
    pub const WIDE_BINDING: usize = 1;
    /// Total public-input count.
    pub const COUNT: usize = 17;
}

fn u64_limbs(value: u64) -> [u16; U64_LIMBS] {
    core::array::from_fn(|i| ((value >> (i * LIMB_BITS)) & 0xffff) as u16)
}

fn u64_mod_p(value: u64) -> BabyBear {
    BabyBear::new((value % BABYBEAR_P as u64) as u32)
}

/// The backend-neutral statement: the Lean relation plus these canonical public inputs.
fn statement_for(public_inputs: &[BabyBear]) -> Result<DescriptorStatement, WideValueBindingError> {
    DescriptorStatement::try_new(
        wide_value_binding_descriptor().clone(),
        public_inputs.iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| WideValueBindingError::StatementRejected { reason })
}

/// Private witness for one input's wide value/asset binding sidecar.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WideValueBindingWitness {
    /// Full, unreduced note value.
    pub value: u64,
    /// Full, unreduced asset identifier.
    pub asset_type: u64,
    /// The exact randomness felt used by the current spend circuit's C7 join.
    pub legacy_randomness: BabyBear,
    /// Additional field-valued binding blinding.  Together with
    /// `legacy_randomness`, this contributes seven hidden BabyBear lanes.
    pub binding_blind: [BabyBear; BINDING_BLIND_LANES],
}

impl WideValueBindingWitness {
    /// The compatibility one-felt value binding that the current spend exposes.
    pub fn legacy_binding(&self) -> BabyBear {
        hash_fact(
            u64_mod_p(self.value),
            &[
                u64_mod_p(self.asset_type),
                self.legacy_randomness,
                BabyBear::ZERO,
            ],
        )
    }

    /// The sixteen-felt, domain-separated full-u64 commitment carrier.
    pub fn wide_binding(&self) -> [BabyBear; WIDE_VALUE_BINDING_LANES] {
        let value = u64_limbs(self.value);
        let asset = u64_limbs(self.asset_type);
        let right = [
            BabyBear::new(asset[3] as u32),
            self.legacy_randomness,
            self.binding_blind[0],
            self.binding_blind[1],
            self.binding_blind[2],
            self.binding_blind[3],
            self.binding_blind[4],
            self.binding_blind[5],
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
}

/// Generate a constant two-row trace in the LEAN column layout, and its public claim.
///
/// The returned matrix is the descriptor-width MAIN trace; the IR-v2 prover fills the Poseidon2
/// chip lanes itself (`trace_with_chip_lanes`).
pub fn generate_wide_value_binding_trace(
    witness: &WideValueBindingWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let value = u64_limbs(witness.value);
    let asset = u64_limbs(witness.asset_type);
    let wide = witness.wide_binding();
    let legacy = witness.legacy_binding();

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
    row[col::RANDOMNESS] = witness.legacy_randomness;
    row[col::BLIND..col::BLIND + BINDING_BLIND_LANES].copy_from_slice(&witness.binding_blind);
    row[col::LEGACY_BINDING] = legacy;
    row[col::WIDE_A..col::WIDE_A + 8].copy_from_slice(&wide[..8]);
    row[col::WIDE_B..col::WIDE_B + 8].copy_from_slice(&wide[8..]);

    let mut public_inputs = Vec::with_capacity(pi::COUNT);
    public_inputs.push(legacy);
    public_inputs.extend_from_slice(&wide);
    (vec![row.clone(), row], public_inputs)
}

/// The public claim carried alongside a hiding proof.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WideValueBindingClaim {
    /// Compatibility join to current shielded spend C7.
    pub legacy_binding: BabyBear,
    /// Faithful wide carrier over canonical full-u64 limbs.
    pub wide_binding: [BabyBear; WIDE_VALUE_BINDING_LANES],
}

impl WideValueBindingClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(pi::COUNT);
        out.push(self.legacy_binding);
        out.extend_from_slice(&self.wide_binding);
        out
    }
}

/// Hiding proof that a public wide carrier opens to canonical full-u64 value
/// and asset limbs and reduces to the current spend's compatibility binding.
pub struct WideValueBindingProof {
    /// Public carrier claim.
    pub claim: WideValueBindingClaim,
    /// Hiding IR-v2 batch proof; value, asset and blinding remain witness-only.
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl WideValueBindingProof {
    /// Canonical postcard encoding for the Turn input's wide-proof field.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("Ir2BatchProof postcard serialize")
    }

    /// Reconstruct hostile Turn-wire parts.  Every public field element must
    /// use its canonical BabyBear integer encoding; accepting `x + p` here
    /// would reintroduce the exact alias this carrier exists to remove.
    pub fn from_serialized_parts(
        legacy_binding: u32,
        wide_binding: [u32; WIDE_VALUE_BINDING_LANES],
        proof_bytes: &[u8],
    ) -> Result<Self, WideValueBindingError> {
        if legacy_binding >= BABYBEAR_P {
            return Err(WideValueBindingError::NonCanonicalPublicField {
                lane: 0,
                value: legacy_binding,
            });
        }
        for (index, value) in wide_binding.iter().copied().enumerate() {
            if value >= BABYBEAR_P {
                return Err(WideValueBindingError::NonCanonicalPublicField {
                    lane: index + 1,
                    value,
                });
            }
        }
        let proof = postcard::from_bytes(proof_bytes).map_err(|error| {
            WideValueBindingError::ProofDecode {
                reason: error.to_string(),
            }
        })?;
        Ok(Self {
            claim: WideValueBindingClaim {
                legacy_binding: BabyBear::new(legacy_binding),
                wide_binding: wide_binding.map(BabyBear::new),
            },
            proof,
        })
    }
}

/// Prove one faithful value/asset binding sidecar through the hiding path.
pub fn prove_wide_value_binding(
    witness: &WideValueBindingWitness,
) -> Result<WideValueBindingProof, WideValueBindingError> {
    let (trace, pis) = generate_wide_value_binding_trace(witness);
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
    .map_err(|reason| WideValueBindingError::ProveFailed { reason })?;
    let mut wide_binding = [BabyBear::ZERO; WIDE_VALUE_BINDING_LANES];
    wide_binding.copy_from_slice(&pis[pi::WIDE_BINDING..pi::COUNT]);
    Ok(WideValueBindingProof {
        claim: WideValueBindingClaim {
            legacy_binding: pis[pi::LEGACY_BINDING],
            wide_binding,
        },
        proof,
    })
}

/// Verify a wide sidecar against an exact current-spend compatibility binding.
pub fn verify_wide_value_binding(
    sidecar: &WideValueBindingProof,
    expected_legacy_binding: BabyBear,
) -> Result<(), WideValueBindingError> {
    if sidecar.claim.legacy_binding != expected_legacy_binding {
        return Err(WideValueBindingError::LegacyBindingMismatch);
    }
    let statement = statement_for(&sidecar.claim.public_inputs())?;
    Plonky3HidingFriReference::verify(&statement, &sidecar.proof)
        .map_err(|reason| WideValueBindingError::ProofRejected { reason })
}

/// Verify the current hidden-membership STARK and exactly one faithful wide
/// binding proof per input.  Turn calls this at its shielded-effect entry; the
/// old standalone one-felt spend verifier is no longer sufficient acceptance.
pub fn verify_stark_with_wide_bindings(
    transfer: &ShieldedTransfer,
    sidecars: &[WideValueBindingProof],
) -> Result<(), WideValueBindingError> {
    transfer
        .verify_stark_side()
        .map_err(WideValueBindingError::ShieldedSpendRejected)?;
    if sidecars.len() != transfer.inputs.len() {
        return Err(WideValueBindingError::SidecarCountMismatch {
            inputs: transfer.inputs.len(),
            sidecars: sidecars.len(),
        });
    }
    for (i, (input, sidecar)) in transfer.inputs.iter().zip(sidecars).enumerate() {
        verify_wide_value_binding(sidecar, input.value_binding).map_err(|source| {
            WideValueBindingError::InputSidecarRejected {
                input_index: i,
                reason: source.to_string(),
            }
        })?;
    }
    Ok(())
}

/// Transcript extension that a downstream no-mint proof must absorb to make
/// every full-width carrier load-bearing.  This function only constructs those
/// bytes; it is not itself a no-mint verifier. Callers should only use the
/// returned bytes after [`verify_stark_with_wide_bindings`] succeeds.
pub fn wide_transfer_message(
    transfer: &ShieldedTransfer,
    sidecars: &[WideValueBindingProof],
) -> Result<Vec<u8>, WideValueBindingError> {
    if sidecars.len() != transfer.inputs.len() {
        return Err(WideValueBindingError::SidecarCountMismatch {
            inputs: transfer.inputs.len(),
            sidecars: sidecars.len(),
        });
    }
    let mut message = Vec::new();
    message.extend_from_slice(b"dregg-shielded-transfer-wide-binding-v1");
    let base = transfer.transfer_message();
    message.extend_from_slice(&(base.len() as u64).to_le_bytes());
    message.extend_from_slice(&base);
    message.extend_from_slice(&(sidecars.len() as u64).to_le_bytes());
    for sidecar in sidecars {
        message.extend_from_slice(&sidecar.claim.legacy_binding.as_u32().to_le_bytes());
        for lane in sidecar.claim.wide_binding {
            message.extend_from_slice(&lane.as_u32().to_le_bytes());
        }
    }
    Ok(message)
}

/// Construction/verification failures for the native wide carrier.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WideValueBindingError {
    ProveFailed { reason: String },
    ProofDecode { reason: String },
    ProofRejected { reason: String },
    StatementRejected { reason: String },
    NonCanonicalPublicField { lane: usize, value: u32 },
    LegacyBindingMismatch,
    SidecarCountMismatch { inputs: usize, sidecars: usize },
    ShieldedSpendRejected(ShieldedError),
    InputSidecarRejected { input_index: usize, reason: String },
}

impl core::fmt::Display for WideValueBindingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::ProveFailed { reason } => write!(f, "wide binding proving failed: {reason}"),
            Self::ProofDecode { reason } => write!(f, "wide binding proof decode failed: {reason}"),
            Self::ProofRejected { reason } => write!(f, "wide binding proof rejected: {reason}"),
            Self::StatementRejected { reason } => {
                write!(f, "wide binding statement rejected: {reason}")
            }
            Self::NonCanonicalPublicField { lane, value } => write!(
                f,
                "wide binding public lane {lane} is not canonical BabyBear: {value}"
            ),
            Self::LegacyBindingMismatch => {
                write!(f, "wide binding does not join the shielded spend C7 claim")
            }
            Self::SidecarCountMismatch { inputs, sidecars } => write!(
                f,
                "shielded transfer has {inputs} inputs but {sidecars} wide binding sidecars"
            ),
            Self::ShieldedSpendRejected(source) => {
                write!(
                    f,
                    "shielded spend proof rejected before wide join: {source}"
                )
            }
            Self::InputSidecarRejected {
                input_index,
                reason,
            } => write!(f, "wide binding sidecar {input_index} rejected: {reason}"),
        }
    }
}

impl std::error::Error for WideValueBindingError {}
