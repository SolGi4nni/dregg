//! Faithful full-`u64` value/asset binding for the shielded-transfer cutover.
//!
//! The deployed shielded-spend circuit still exposes a one-felt
//! `hash_fact(value mod p, [asset mod p, randomness, 0])`.  That statement is
//! useful as a compatibility join, but it is not injective on either `u64`:
//! values separated by the BabyBear modulus alias before hashing.  This module
//! adds the native wide carrier that the Turn/no-mint boundary can consume
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

use super::transfer::{ShieldedError, ShieldedTransfer};
use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use dregg_circuit::dsl::dsl_p3_air::{DslZkProof, prove_dsl_zk, verify_dsl_zk};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;

/// Number of 16-bit limbs in a canonical `u64` encoding.
pub const U64_LIMBS: usize = 4;
/// Bits in each canonical value/asset limb.
pub const LIMB_BITS: usize = 16;
/// Number of independently constrained public binding lanes.
pub const WIDE_VALUE_BINDING_LANES: usize = 16;
/// Extra field-valued blinding lanes, in addition to the legacy randomness felt.
pub const BINDING_BLIND_LANES: usize = 6;

// Two distinct in-band domain separators.  `MerkleHash8` seeds all sixteen
// permutation lanes directly, so the domain is an explicit first input.
const DOMAIN_A: u32 = 0x5642_4e30; // "VBN0"
const DOMAIN_B: u32 = 0x5642_4e31; // "VBN1"

mod col {
    use super::{BINDING_BLIND_LANES, LIMB_BITS, U64_LIMBS};

    pub const VALUE_LIMBS: usize = 0;
    pub const ASSET_LIMBS: usize = VALUE_LIMBS + U64_LIMBS;
    pub const VALUE_MOD_P: usize = ASSET_LIMBS + U64_LIMBS;
    pub const ASSET_MOD_P: usize = VALUE_MOD_P + 1;
    pub const RANDOMNESS: usize = ASSET_MOD_P + 1;
    pub const BLIND: usize = RANDOMNESS + 1;
    pub const DOMAIN_A: usize = BLIND + BINDING_BLIND_LANES;
    pub const DOMAIN_B: usize = DOMAIN_A + 1;
    pub const ZERO: usize = DOMAIN_B + 1;
    pub const LEGACY_BINDING: usize = ZERO + 1;
    pub const WIDE_A: usize = LEGACY_BINDING + 1;
    pub const WIDE_B: usize = WIDE_A + 8;
    pub const BITS: usize = WIDE_B + 8;
    pub const WIDTH: usize = BITS + 2 * U64_LIMBS * LIMB_BITS;

    pub const fn limb(kind: usize, i: usize) -> usize {
        if kind == 0 {
            VALUE_LIMBS + i
        } else {
            ASSET_LIMBS + i
        }
    }

    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        BITS + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// Public-input layout `[legacy_binding, wide_binding[0..16]]`.
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

fn limb_weight(i: usize) -> BabyBear {
    let shift = i * LIMB_BITS;
    BabyBear::new(((1u64 << shift) % BABYBEAR_P as u64) as u32)
}

fn constant_gate(col: usize, value: BabyBear) -> ConstraintExpr {
    ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col],
            },
            PolyTerm {
                coeff: -value,
                col_indices: vec![],
            },
        ],
    }
}

fn limb_recompose(kind: usize, limb: usize) -> ConstraintExpr {
    let mut terms = vec![PolyTerm {
        coeff: BabyBear::ONE,
        col_indices: vec![col::limb(kind, limb)],
    }];
    for bit in 0..LIMB_BITS {
        terms.push(PolyTerm {
            coeff: -BabyBear::new(1u32 << bit),
            col_indices: vec![col::bit(kind, limb, bit)],
        });
    }
    ConstraintExpr::Polynomial { terms }
}

fn u64_recompose(kind: usize, output: usize) -> ConstraintExpr {
    let mut terms = vec![PolyTerm {
        coeff: BabyBear::ONE,
        col_indices: vec![output],
    }];
    for limb in 0..U64_LIMBS {
        terms.push(PolyTerm {
            coeff: -limb_weight(limb),
            col_indices: vec![col::limb(kind, limb)],
        });
    }
    ConstraintExpr::Polynomial { terms }
}

fn wide_input_columns(domain: usize) -> ([usize; 8], [usize; 8]) {
    // [domain, value limbs 0..4, asset limbs 0..3] ||
    // [asset limb 3, legacy randomness, blind 0..6]
    let left = [
        domain,
        col::VALUE_LIMBS,
        col::VALUE_LIMBS + 1,
        col::VALUE_LIMBS + 2,
        col::VALUE_LIMBS + 3,
        col::ASSET_LIMBS,
        col::ASSET_LIMBS + 1,
        col::ASSET_LIMBS + 2,
    ];
    let right = [
        col::ASSET_LIMBS + 3,
        col::RANDOMNESS,
        col::BLIND,
        col::BLIND + 1,
        col::BLIND + 2,
        col::BLIND + 3,
        col::BLIND + 4,
        col::BLIND + 5,
    ];
    (left, right)
}

/// The faithful full-u64 value/asset binding circuit.
pub fn wide_value_binding_descriptor() -> CircuitDescriptor {
    let mut constraints = Vec::new();

    // Canonical 16-bit encodings: there is exactly one limb vector per u64.
    for kind in 0..2 {
        for limb in 0..U64_LIMBS {
            for bit in 0..LIMB_BITS {
                constraints.push(ConstraintExpr::Binary {
                    col: col::bit(kind, limb, bit),
                });
            }
            constraints.push(limb_recompose(kind, limb));
        }
    }

    // Compatibility values are derived from, never independent of, the full
    // limbs.  This is the exact field reduction the v1 spend circuit sees.
    constraints.push(u64_recompose(0, col::VALUE_MOD_P));
    constraints.push(u64_recompose(1, col::ASSET_MOD_P));

    constraints.push(constant_gate(col::DOMAIN_A, BabyBear::new(DOMAIN_A)));
    constraints.push(constant_gate(col::DOMAIN_B, BabyBear::new(DOMAIN_B)));
    constraints.push(constant_gate(col::ZERO, BabyBear::ZERO));

    let (left_a, right) = wide_input_columns(col::DOMAIN_A);
    let (left_b, _) = wide_input_columns(col::DOMAIN_B);
    constraints.push(ConstraintExpr::MerkleHash8 {
        output_cols: core::array::from_fn(|i| col::WIDE_A + i),
        left_cols: left_a,
        right_cols: right,
    });
    constraints.push(ConstraintExpr::MerkleHash8 {
        output_cols: core::array::from_fn(|i| col::WIDE_B + i),
        left_cols: left_b,
        right_cols: right,
    });

    // Byte-for-byte semantic twin of shielded_spend_circuit C7 after the
    // canonical limbs have been reduced into its compatibility field view.
    constraints.push(ConstraintExpr::Hash {
        output_col: col::LEGACY_BINDING,
        input_cols: vec![
            col::VALUE_MOD_P,
            col::ASSET_MOD_P,
            col::RANDOMNESS,
            col::ZERO,
        ],
    });

    let mut boundaries = vec![BoundaryDef::PiBinding {
        row: BoundaryRow::First,
        col: col::LEGACY_BINDING,
        pi_index: pi::LEGACY_BINDING,
    }];
    for lane in 0..WIDE_VALUE_BINDING_LANES {
        boundaries.push(BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: if lane < 8 {
                col::WIDE_A + lane
            } else {
                col::WIDE_B + lane - 8
            },
            pi_index: pi::WIDE_BINDING + lane,
        });
    }

    let mut columns = Vec::with_capacity(col::WIDTH);
    for i in 0..U64_LIMBS {
        columns.push(ColumnDef {
            name: format!("value_limb_{i}"),
            index: col::VALUE_LIMBS + i,
            kind: ColumnKind::Value,
        });
    }
    for i in 0..U64_LIMBS {
        columns.push(ColumnDef {
            name: format!("asset_limb_{i}"),
            index: col::ASSET_LIMBS + i,
            kind: ColumnKind::Value,
        });
    }
    for (name, index, kind) in [
        ("value_mod_p", col::VALUE_MOD_P, ColumnKind::Value),
        ("asset_mod_p", col::ASSET_MOD_P, ColumnKind::Value),
        ("randomness", col::RANDOMNESS, ColumnKind::Value),
    ] {
        columns.push(ColumnDef {
            name: name.into(),
            index,
            kind,
        });
    }
    for i in 0..BINDING_BLIND_LANES {
        columns.push(ColumnDef {
            name: format!("binding_blind_{i}"),
            index: col::BLIND + i,
            kind: ColumnKind::Value,
        });
    }
    for (name, index) in [
        ("domain_a", col::DOMAIN_A),
        ("domain_b", col::DOMAIN_B),
        ("zero", col::ZERO),
    ] {
        columns.push(ColumnDef {
            name: name.into(),
            index,
            kind: ColumnKind::Value,
        });
    }
    columns.push(ColumnDef {
        name: "legacy_binding".into(),
        index: col::LEGACY_BINDING,
        kind: ColumnKind::Hash,
    });
    for lane in 0..8 {
        columns.push(ColumnDef {
            name: format!("wide_a_{lane}"),
            index: col::WIDE_A + lane,
            kind: ColumnKind::Hash,
        });
    }
    for lane in 0..8 {
        columns.push(ColumnDef {
            name: format!("wide_b_{lane}"),
            index: col::WIDE_B + lane,
            kind: ColumnKind::Hash,
        });
    }
    for kind in 0..2 {
        let prefix = if kind == 0 { "value" } else { "asset" };
        for limb in 0..U64_LIMBS {
            for bit in 0..LIMB_BITS {
                columns.push(ColumnDef {
                    name: format!("{prefix}_limb_{limb}_bit_{bit}"),
                    index: col::bit(kind, limb, bit),
                    kind: ColumnKind::Binary,
                });
            }
        }
    }
    debug_assert_eq!(columns.len(), col::WIDTH);

    CircuitDescriptor {
        name: "dregg-shielded-wide-value-binding-v1".into(),
        trace_width: col::WIDTH,
        max_degree: 7,
        columns,
        constraints,
        boundaries,
        public_input_count: pi::COUNT,
        lookup_tables: vec![],
    }
}

/// The faithful full-u64 value/asset binding circuit.
pub fn wide_value_binding_circuit() -> DslCircuit {
    DslCircuit::new(wide_value_binding_descriptor())
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

/// Generate a constant two-row trace and its public claim.
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
    row[col::DOMAIN_A] = BabyBear::new(DOMAIN_A);
    row[col::DOMAIN_B] = BabyBear::new(DOMAIN_B);
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
    /// Hiding uni-STARK proof; value, asset and blinding remain witness-only.
    pub proof: DslZkProof,
}

impl WideValueBindingProof {
    /// Canonical postcard encoding for the Turn input's wide-proof field.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("DslZkProof postcard serialize")
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
    let circuit = wide_value_binding_circuit();
    let (trace, pis) = generate_wide_value_binding_trace(witness);
    let proof =
        prove_dsl_zk(&circuit, &trace, &pis).map_err(|e| WideValueBindingError::ProveFailed {
            reason: format!("{e}"),
        })?;
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
    verify_dsl_zk(
        &wide_value_binding_circuit(),
        &sidecar.proof,
        &sidecar.claim.public_inputs(),
    )
    .map_err(|e| WideValueBindingError::ProofRejected {
        reason: format!("{e}"),
    })
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
