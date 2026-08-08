//! The shielded OFF-RAMP's **VALUE LINK** — the Rust half that CALLS the Lean-emitted
//! `dregg-shielded-deshield-value-link::v1` relation
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedDeshieldValueLinkEmit.lean`).
//!
//! **THE AIR IS AUTHORED IN LEAN.** This module reads the byte-pinned golden out of the Lean
//! source, produces a WITNESS TRACE that satisfies it, and proves/verifies through the hiding
//! IR-v2 backend. It authors NO constraint.
//!
//! ## The wound this closes
//!
//! Value could ENTER the shielded pool (`Effect::Shield`) and MOVE inside it (`ShieldedTransfer`,
//! whose value link is `dregg-shielded-transfer-value-link::v1`). It could never LEAVE: there was
//! no `Deshield`, so every note that entered was trapped. A one-way money-mover is not a privacy
//! pool.
//!
//! The off-ramp inherits the on-ramp's failure mode, pointed the other way. A `Shield` that mints
//! more than it debits is a mint; a **`Deshield` that credits more cleartext than the note it
//! spends holds** is the same theft, and it is the *easier* one — the credited value is a plain
//! `u64` on the wire while the spent note's value is hidden.
//!
//! ## What the relation says (161 columns, 24 PIs `wide[16] ++ vLimb[4] ++ aLimb[4]`)
//!
//! Over a private witness `(value, asset, inRand, inBlind[6])`:
//!
//! * `value` and `asset` ride four canonical 16-bit limb cells each, booleanity FORCED in the AIR
//!   (128 boolean pins + 8 recompositions) — so `0 ≤ value < 2^64` is a property of the trace, not
//!   a Bulletproof;
//! * the SIXTEEN published lanes are `cap_node8` at `DOMAIN_A`/`DOMAIN_B` over
//!   `[domain, v0..v3, a0..a3, inRand, inBlind0..5]` — the SAME absorb block, column for column,
//!   that `WideValueBindingEmit`, the complete spend's `carrierPins` and the TRANSFER's value link
//!   use (the Lean file imports those absorb terms rather than re-typing them, and
//!   `absorb_block_is_the_transfer_value_links` is an `rfl` against the transfer link's site);
//! * the EIGHT published limbs ARE `cV i` / `cA i` — the very cells the carrier absorbs.
//!
//! **The link is that the carrier and the public credit read one set of limb columns.** There is no
//! second value in the trace, so a satisfying assignment in which the cleartext credit is worth
//! more than the spent note does not exist (`inflated_credit_unsat`).
//!
//! ## Why the credit rides LIMBS and not `value mod p`
//!
//! `value mod p` is a single BabyBear felt and `value` is a `u64`: `v` and `v + p` share it. If the
//! public credit were the reduction, a note worth `v` would fund a cleartext credit of `v + p` —
//! free money arriving at the exact place the value becomes public. The four 16-bit limbs are
//! injective on `u64` (Lean `deshield_limb_canonical` forces each into `[0, 2^16)`), so
//! [`credit_from_public_limbs`] recomposes over the integers with no alias and no truncation.
//!
//! ## Why the verifier's inputs make it non-vacuous
//!
//! [`verify_shielded_deshield_link`] takes BOTH sides from the CALLER, never from the proof's own
//! claim:
//!
//! * the sixteen lanes come from the complete-spend proof's PI-pinned `wide[16]`, read off AFTER
//!   that proof verified against the executor's committed root;
//! * the eight limbs are derived from the EFFECT's declared public `value`/`asset_type` — the
//!   cleartext credit the executor is about to land.
//!
//! So the relation is handed the two ends of the boundary and forces them to be one opening. Same
//! discipline `ShieldedWideJoinPin.join_still_decouples` names for the sidecar join.
//!
//! ## The privacy residual, named
//!
//! A Deshield **reveals the value and the asset** of the note it spends — it must, because the
//! cleartext credit is public. What stays hidden is everything else the complete-spend proof hides:
//! WHICH leaf was spent, its owner, its spending key, its randomness, its whole membership path.

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
use dregg_circuit::stark_zk::DreggZkStarkConfig;

use super::wide_value_binding::{
    BINDING_BLIND_LANES, DOMAIN_A, DOMAIN_B, LIMB_BITS, U64_LIMBS, WIDE_VALUE_BINDING_LANES,
};

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/ShieldedDeshieldValueLinkEmit.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module (the shared
/// `wide_value_binding.rs` / `transfer_link.rs` convention — one splitter).
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
pub fn shielded_deshield_value_link_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "SHIELDED_DESHIELD_VALUE_LINK_GOLDEN")
}

/// Parse-once cache of the Lean-emitted relation.
///
/// The two asserts are the DETECTOR for this file's witness-layout mirror: if the Lean author moves
/// the width or the public-input count, first use goes red HERE rather than silently producing a
/// witness for a layout that no longer exists.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(shielded_deshield_value_link_descriptor_json())
        .expect("the Lean-emitted shielded deshield value-link descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors \
         ShieldedDeshieldValueLinkEmit.lean §1"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors \
         ShieldedDeshieldValueLinkEmit.lean §2"
    );
    desc
});

/// The Lean-emitted off-ramp value-link relation.
pub fn shielded_deshield_value_link_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

/// **Witness-layout mirror** of the Lean column layout (`ShieldedDeshieldValueLinkEmit.lean` §1,
/// whose named theorems pin every index below). Authors no algebra — it only says where the trace
/// producer places each cell — and [`LEAN_DESCRIPTOR`] checks it against the emitted width.
pub mod col {
    use super::{BINDING_BLIND_LANES, LIMB_BITS, U64_LIMBS};

    /// `cV i` — value limb `i` (little-endian), shared by the carrier and the public credit.
    pub const VALUE_LIMBS: usize = 0;
    /// `cA i` — asset limb `i`.
    pub const ASSET_LIMBS: usize = VALUE_LIMBS + U64_LIMBS;
    /// `cVMOD` — `value mod p`. Constrained but NOT published (see the module docs: the reduction
    /// cannot separate `v` from `v + p`, so the credit rides the limbs).
    pub const VALUE_MOD_P: usize = ASSET_LIMBS + U64_LIMBS;
    /// `cAMOD` — `asset mod p`.
    pub const ASSET_MOD_P: usize = VALUE_MOD_P + 1;
    /// `cRAND` — the SPENT note's randomness.
    pub const IN_RANDOMNESS: usize = ASSET_MOD_P + 1;
    /// `cBL i` — the SPENT note's carrier blind lane `i`.
    pub const IN_BLIND: usize = IN_RANDOMNESS + 1;
    /// `cWA j` — `DOMAIN_A` carrier lane `j`.
    pub const WIDE_A: usize = IN_BLIND + BINDING_BLIND_LANES;
    /// `cWB j` — `DOMAIN_B` carrier lane `j`.
    pub const WIDE_B: usize = WIDE_A + 8;
    /// `BITS_BASE` — base of the bit-decomposition block.
    pub const BITS: usize = WIDE_B + 8;
    /// `DESHIELD_WIDTH` — the main-trace width.
    pub const WIDTH: usize = BITS + 2 * U64_LIMBS * LIMB_BITS;

    /// `cBit k i b`.
    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        BITS + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// **Public-input layout mirror** `[wide_binding[0..16], value_limbs[0..4], asset_limbs[0..4]]`
/// (`ShieldedDeshieldValueLinkEmit.lean` §2). Neither half is the prover's claim — see the module
/// docs.
pub mod pi {
    /// First lane of the SPENT note's carrier — supplied by the verifier from the complete-spend
    /// proof's own public inputs.
    pub const WIDE_BINDING: usize = 0;
    /// First 16-bit limb of the CLEARTEXT CREDIT's value — supplied by the verifier from the
    /// effect's declared public `value`.
    pub const VALUE_LIMBS: usize = 16;
    /// First 16-bit limb of the cleartext credit's asset.
    pub const ASSET_LIMBS: usize = 20;
    /// Total public-input count.
    pub const COUNT: usize = 24;
}

fn u64_limbs(value: u64) -> [u16; U64_LIMBS] {
    core::array::from_fn(|i| ((value >> (i * LIMB_BITS)) & 0xffff) as u16)
}

fn u64_mod_p(value: u64) -> BabyBear {
    BabyBear::new((value % BABYBEAR_P as u64) as u32)
}

/// The private witness for one shielded-note → cleartext-credit value link.
///
/// Every field is the SPENT note's. There is deliberately **no credit field**: what the cleartext
/// side is worth is not something a prover chooses here, it is read off these limbs by the Lean
/// relation and published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ShieldedDeshieldLinkWitness {
    /// The spent note's full, unreduced value — and therefore the cleartext credit's.
    pub value: u64,
    /// The spent note's full, unreduced asset identifier — and therefore the credit's.
    pub asset_type: u64,
    /// The spent note's randomness (absorbed by the carrier the spend proof published).
    pub in_randomness: BabyBear,
    /// The spent note's six carrier blind lanes.
    pub in_binding_blind: [BabyBear; BINDING_BLIND_LANES],
}

impl ShieldedDeshieldLinkWitness {
    /// The sixteen-lane carrier of the SPENT note — bit-identical to
    /// `WideValueBindingWitness::wide_binding`, to `ShieldedTransferLinkWitness::in_wide_binding`
    /// and to the complete-spend proof's PI-pinned `wide[16]` for the same opening. (One absorb
    /// block, four producers; the Lean side proves the emitted SITES equal, not merely alike.)
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

    /// The eight PUBLIC limb felts this proof publishes — the cleartext credit, in the canonical
    /// 16-bit encoding the AIR forces. `[v0, v1, v2, v3, a0, a1, a2, a3]`.
    pub fn credit_limbs(&self) -> [BabyBear; 2 * U64_LIMBS] {
        let value = u64_limbs(self.value);
        let asset = u64_limbs(self.asset_type);
        core::array::from_fn(|i| {
            if i < U64_LIMBS {
                BabyBear::new(value[i] as u32)
            } else {
                BabyBear::new(asset[i - U64_LIMBS] as u32)
            }
        })
    }
}

/// The eight public limb felts a `(value, asset)` cleartext credit MUST publish — the function the
/// deployed verifier applies to the effect's declared fields before it builds the statement.
pub fn credit_limbs_of(value: u64, asset_type: u64) -> [BabyBear; 2 * U64_LIMBS] {
    let v = u64_limbs(value);
    let a = u64_limbs(asset_type);
    core::array::from_fn(|i| {
        if i < U64_LIMBS {
            BabyBear::new(v[i] as u32)
        } else {
            BabyBear::new(a[i - U64_LIMBS] as u32)
        }
    })
}

/// Recompose a `(value, asset)` pair from eight PUBLIC limb felts, refusing any lane that is not a
/// canonical 16-bit limb.
///
/// ⚑ The refusal is defence in depth, not the binding. A lane `≥ 2^16` has no satisfying trace
/// (the Lean `deshield_limb_canonical` forces the column into `[0, 2^16)` and the pin forces the
/// column to the public input), so such a proof cannot verify. Refusing here means a malformed
/// public input is named as malformed rather than surfacing as an opaque STARK rejection — and it
/// means this function can never be the place a `u64` silently overflows.
pub fn credit_from_public_limbs(
    limbs: &[BabyBear; 2 * U64_LIMBS],
) -> Result<(u64, u64), ShieldedDeshieldLinkError> {
    let mut value = 0u64;
    let mut asset = 0u64;
    for (i, limb) in limbs.iter().enumerate() {
        let raw = limb.as_u32();
        if raw >= 1 << LIMB_BITS {
            return Err(ShieldedDeshieldLinkError::NonCanonicalCreditLimb { index: i, raw });
        }
        let shifted = (raw as u64) << (LIMB_BITS * (i % U64_LIMBS));
        if i < U64_LIMBS {
            value |= shifted;
        } else {
            asset |= shifted;
        }
    }
    Ok((value, asset))
}

/// Generate a constant two-row trace in the LEAN column layout, and its public claim.
///
/// The returned matrix is the descriptor-width MAIN trace; the IR-v2 prover fills the Poseidon2
/// chip lanes itself (`trace_with_chip_lanes`).
pub fn generate_shielded_deshield_link_trace(
    witness: &ShieldedDeshieldLinkWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let value = u64_limbs(witness.value);
    let asset = u64_limbs(witness.asset_type);
    let wide = witness.in_wide_binding();

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
    row[col::WIDE_A..col::WIDE_A + 8].copy_from_slice(&wide[..8]);
    row[col::WIDE_B..col::WIDE_B + 8].copy_from_slice(&wide[8..]);

    let mut public_inputs = Vec::with_capacity(pi::COUNT);
    public_inputs.extend_from_slice(&wide);
    public_inputs.extend_from_slice(&witness.credit_limbs());
    (vec![row.clone(), row], public_inputs)
}

/// The public claim a deshield value-link proof is checked against.
///
/// ⚑ Held for CONSTRUCTION and for tests. The deployed verifier does NOT trust it: it builds the
/// statement from the complete-spend proof's carrier and the effect's declared credit
/// ([`verify_shielded_deshield_link`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedDeshieldLinkClaim {
    /// The SPENT note's sixteen carrier lanes.
    pub in_wide_binding: [BabyBear; WIDE_VALUE_BINDING_LANES],
    /// The CLEARTEXT CREDIT's eight canonical 16-bit limbs, `[v0..v3, a0..a3]`.
    pub credit_limbs: [BabyBear; 2 * U64_LIMBS],
}

impl ShieldedDeshieldLinkClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(pi::COUNT);
        out.extend_from_slice(&self.in_wide_binding);
        out.extend_from_slice(&self.credit_limbs);
        out
    }

    /// The `(value, asset)` this claim credits, recomposed over the integers from its limbs.
    pub fn credit(&self) -> Result<(u64, u64), ShieldedDeshieldLinkError> {
        credit_from_public_limbs(&self.credit_limbs)
    }
}

/// A hiding proof that the sixteen published carrier lanes and the eight published credit limbs
/// open to ONE `(value, asset)`.
pub struct ShieldedDeshieldLinkProof {
    /// The public claim (construction-side; the deployed verifier supplies its own).
    pub claim: ShieldedDeshieldLinkClaim,
    /// The hiding IR-v2 proof. The randomness and the blind lanes stay witness-only; the value and
    /// asset become public, because a deshield's whole purpose is to make them so.
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl ShieldedDeshieldLinkProof {
    /// Canonical postcard encoding for the wire's `link_proof` field.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("Ir2BatchProof postcard serialize")
    }
}

/// Errors from off-ramp value-link construction / verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedDeshieldLinkError {
    /// The statement (relation + public inputs) was rejected before proving/verifying.
    StatementRejected { reason: String },
    /// Proving failed.
    ProveFailed { reason: String },
    /// The serialized proof failed to deserialize.
    ProofDecode { reason: String },
    /// **THE OFF-RAMP REFUSAL.** The proof does not verify against the carrier the complete-spend
    /// proof published together with the cleartext credit this deshield wants to land — i.e. the
    /// credit is not what the spent note is worth.
    ProofRejected { reason: String },
    /// A published credit limb is not a canonical 16-bit limb. Such a proof has no satisfying trace
    /// (`deshield_limb_canonical`); refusing by name keeps a malformed public input from surfacing
    /// as an opaque STARK rejection, and keeps the `u64` recomposition total.
    NonCanonicalCreditLimb { index: usize, raw: u32 },
}

impl core::fmt::Display for ShieldedDeshieldLinkError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StatementRejected { reason } => {
                write!(
                    f,
                    "shielded deshield value-link statement rejected: {reason}"
                )
            }
            Self::ProveFailed { reason } => {
                write!(f, "shielded deshield value-link proving failed: {reason}")
            }
            Self::ProofDecode { reason } => write!(
                f,
                "shielded deshield value-link proof failed to deserialize: {reason}"
            ),
            Self::ProofRejected { reason } => write!(
                f,
                "shielded deshield value-link REFUSED: the cleartext credit does not equal the \
                 value the spent note's carrier binds ({reason})"
            ),
            Self::NonCanonicalCreditLimb { index, raw } => write!(
                f,
                "shielded deshield credit limb {index} = {raw} is not a canonical 16-bit limb"
            ),
        }
    }
}

impl std::error::Error for ShieldedDeshieldLinkError {}

/// The backend-neutral statement: the Lean relation plus these canonical public inputs.
fn statement_for(
    public_inputs: &[BabyBear],
) -> Result<DescriptorStatement, ShieldedDeshieldLinkError> {
    DescriptorStatement::try_new(
        shielded_deshield_value_link_descriptor().clone(),
        public_inputs.iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| ShieldedDeshieldLinkError::StatementRejected { reason })
}

/// Prove one shielded-note → cleartext-credit value link through the hiding path.
pub fn prove_shielded_deshield_link(
    witness: &ShieldedDeshieldLinkWitness,
) -> Result<ShieldedDeshieldLinkProof, ShieldedDeshieldLinkError> {
    let (trace, pis) = generate_shielded_deshield_link_trace(witness);
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
    .map_err(|reason| ShieldedDeshieldLinkError::ProveFailed { reason })?;
    let mut in_wide_binding = [BabyBear::ZERO; WIDE_VALUE_BINDING_LANES];
    in_wide_binding.copy_from_slice(&pis[pi::WIDE_BINDING..pi::VALUE_LIMBS]);
    let mut credit_limbs = [BabyBear::ZERO; 2 * U64_LIMBS];
    credit_limbs.copy_from_slice(&pis[pi::VALUE_LIMBS..pi::COUNT]);
    Ok(ShieldedDeshieldLinkProof {
        claim: ShieldedDeshieldLinkClaim {
            in_wide_binding,
            credit_limbs,
        },
        proof,
    })
}

/// **THE OFF-RAMP VALUE-LINK GATE.**
///
/// Verify a serialized value-link proof against public inputs the CALLER supplies:
///
/// * `spend_wide_binding` — the sixteen carrier lanes the input's complete-spend proof PI-pins,
///   read off that proof AFTER it verified under the executor's committed root;
/// * `credit_value` / `credit_asset` — the effect's DECLARED public cleartext credit, the `u64`s
///   the executor is about to record in the cleartext ledger.
///
/// Neither comes from this proof's own claim, which is the whole point: the relation forces the
/// carrier and the credit limbs to be functions of ONE limb opening, so a deshield that credits
/// more cleartext than it spends has no satisfying trace — and one that credits *less* has none
/// either, so the pool cannot quietly swallow value on the way out.
///
/// **Substrate: the relation is AUTHORED IN LEAN** (`ShieldedDeshieldValueLinkEmit.lean`, 161
/// columns, 24 PIs, byte-pinned by `deshield_emits_golden`). Rust supplies the statement and calls
/// the verifier.
pub fn verify_shielded_deshield_link(
    proof_bytes: &[u8],
    spend_wide_binding: &[BabyBear; WIDE_VALUE_BINDING_LANES],
    credit_value: u64,
    credit_asset: u64,
) -> Result<(), ShieldedDeshieldLinkError> {
    let proof: Ir2BatchProof<DreggZkStarkConfig> =
        postcard::from_bytes(proof_bytes).map_err(|error| {
            ShieldedDeshieldLinkError::ProofDecode {
                reason: error.to_string(),
            }
        })?;
    let claim = ShieldedDeshieldLinkClaim {
        in_wide_binding: *spend_wide_binding,
        credit_limbs: credit_limbs_of(credit_value, credit_asset),
    };
    let statement = statement_for(&claim.public_inputs())?;
    Plonky3HidingFriReference::verify(&statement, &proof)
        .map_err(|reason| ShieldedDeshieldLinkError::ProofRejected { reason })
}
