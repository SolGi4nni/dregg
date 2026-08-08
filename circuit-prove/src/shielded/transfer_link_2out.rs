//! The shielded transfer's **SPLIT** — the Rust half that CALLS the Lean-emitted
//! `dregg-shielded-transfer-value-link-2out::v1` relation
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLink2OutEmit.lean`).
//!
//! **THE AIR IS AUTHORED IN LEAN.** This module reads the byte-pinned golden out of the Lean
//! source, produces a WITNESS TRACE that satisfies it, and proves/verifies through the hiding
//! IR-v2 backend. It authors NO constraint.
//!
//! ## The wound this closes
//!
//! `dregg-shielded-transfer-value-link::v1` binds ONE spent note to ONE minted note of EQUAL
//! value. That is a whole-note transfer — a change of owner — and it was the only arity the
//! deployed path admitted. **So a shielded note was all-or-nothing: you could spend it, but you
//! could never get change.** Holding `1000` and owing `7`, the only move the chain stated was to
//! hand over the whole `1000`.
//!
//! The workaround — pre-splitting into denomination notes at shield time — is worse than it looks:
//! it leaks the amount into the note COUNT, which is public.
//!
//! ## What the relation says (309 columns, 18 PIs `wide[16] ++ [outCm¹, outCm²]`)
//!
//! Over a private witness `(value, asset, inRand, inBlind[6], out[2].{value, owner, rand})`:
//!
//! * `value`, `asset` and BOTH output values ride four canonical 16-bit limb cells each, booleanity
//!   FORCED in the AIR (256 boolean pins + 16 recompositions) — so `0 <= x < 2^64` is a property of
//!   the trace for every value in the relation, not a Bulletproof;
//! * the SIXTEEN published lanes are `cap_node8` at `DOMAIN_A`/`DOMAIN_B` over
//!   `[domain, v0..v3, a0..a3, inRand, inBlind0..5]` — the SAME absorb block, column for column,
//!   that `WideValueBindingEmit`, the complete spend's `carrierPins` and the 1-out value link use
//!   (the Lean file IMPORTS those absorb terms rather than re-typing them);
//! * each published `outCm_k` is `hash_fact(out_k mod p, [asset mod p, owner_k, rand_k])` — the
//!   deployed note commitment, over the SHARED asset felt, so a split cannot change the asset;
//! * ⚑ **the limbwise CARRY CHAIN** `v_i = o1_i + o2_i - 65536*c_i + c_{i-1}` ties them: every
//!   `c_i` boolean-pinned, `c_{-1}` structurally ABSENT from the emitted gate, and `c_3` GATE-pinned
//!   to zero.
//!
//! ## ⚑ Why the terminal carry gate is the whole thing
//!
//! The Lean `carry_chain_sums` states the algebraic core with `c_3` FREE:
//!
//! ```text
//! o1 + o2 = v + 2^64 * c_3
//! ```
//!
//! Every one of the four chain gates is satisfied by a witness with `c_3 = 1` — the limb equations
//! balance perfectly, because absorbing an overflow is exactly what a carry is FOR. A limbwise
//! chain without a terminal pin therefore does not state conservation; it states conservation up to
//! a free `2^64`, which is the entire `u64` range minted from nothing.
//!
//! [`generate_shielded_transfer_link_2out_trace`] derives the carries FROM THE OUTPUTS, so that
//! attack is CONSTRUCTIBLE here: hand it two outputs whose sum wraps to `value` and it emits a
//! trace with `c_3 = 1` in which all four limb equations hold. `carryTopZero` is the only thing
//! that refuses it, which is what makes the negative test a real falsifier rather than a
//! restatement of the positive.
//!
//! ## Why the verifier's inputs make it non-vacuous
//!
//! [`verify_shielded_transfer_link_2out`] takes the sixteen lanes from the CALLER, not from the
//! proof's own claim, and the caller is [`crate::shielded::ShieldedTransfer::verify`], which reads
//! them off the complete-spend proof's PI-pinned `wide[16]` AFTER that proof has verified against
//! the executor's committed root. So the carrier is a public input of a SEPARATE, already-checked
//! proof — the same discipline `ShieldedWideJoinPin.join_still_decouples` names for the sidecar
//! join.
//!
//! ## ⚑ ONE proof, TWO outputs — and why it cannot be two proofs
//!
//! Conservation across two outputs is a JOINT statement. Two independent per-output proofs would
//! each separately claim the whole input value, and their conjunction would say `o1 = v` and
//! `o2 = v` — a double-mint, not a split. So the link proof moves from PER-OUTPUT to PER-TRANSFER;
//! see the flag day in `transfer.rs`.

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
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::stark_zk::DreggZkStarkConfig;

use super::transfer_link::{ShieldedTransferLinkError, lean_raw_golden, u64_limbs, u64_mod_p};
use super::wide_value_binding::{
    BINDING_BLIND_LANES, DOMAIN_A, DOMAIN_B, LIMB_BITS, U64_LIMBS, WIDE_VALUE_BINDING_LANES,
};

/// The number of minted notes this relation binds. Widening it is a NEW descriptor in the Lean
/// family, not a parameter.
pub const LINK_2OUT_OUTPUTS: usize = 2;

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/ShieldedTransferValueLink2OutEmit.lean");

/// The byte-pinned IR-v2 wire string, read out of the Lean source.
///
/// The splitter is `transfer_link`'s — SHARED, not re-typed. (⚑ Debt, not mine to fix here: four
/// sibling modules in this directory each carry their own hand-typed copy of `lean_raw_golden`.)
pub fn shielded_transfer_value_link_2out_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "SHIELDED_TRANSFER_VALUE_LINK_2OUT_GOLDEN")
}

/// Parse-once cache of the Lean-emitted relation.
///
/// The asserts are the DETECTOR for this file's witness-layout mirror: if the Lean author moves the
/// width or the public-input count, first use goes red HERE rather than silently producing a
/// witness for a layout that no longer exists.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(shielded_transfer_value_link_2out_descriptor_json())
        .expect("the Lean-emitted 2-out value-link descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors \
         ShieldedTransferValueLink2OutEmit.lean §1"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors \
         ShieldedTransferValueLink2OutEmit.lean §2"
    );
    desc
});

/// The Lean-emitted 1-in/2-out value-link relation.
pub fn shielded_transfer_value_link_2out_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

/// **Witness-layout mirror** of the Lean column layout (`ShieldedTransferValueLink2OutEmit.lean`
/// §1, whose named theorems pin every index below). Authors no algebra — it only says where the
/// trace producer places each cell — and [`LEAN_DESCRIPTOR`] checks it against the emitted width.
pub mod col {
    use super::{BINDING_BLIND_LANES, LIMB_BITS, LINK_2OUT_OUTPUTS, U64_LIMBS};

    /// `cV i` — the SPENT note's value limb `i` (little-endian).
    pub const VALUE_LIMBS: usize = 0;
    /// `cA i` — the asset limb `i`, SHARED by the spent note and both mints.
    pub const ASSET_LIMBS: usize = VALUE_LIMBS + U64_LIMBS;
    /// `cVMOD` — the sidecar's `value mod p` slot. ⚑ **Unconstrained and unread**: unlike the
    /// 1-out link, no site here hashes it (each mint hashes its own value), so the Lean file emits
    /// NO gate over it. The column index exists only so columns `0..16` stay the sidecar's index
    /// for index, which is what makes the IMPORTED absorb term denote the right cells.
    pub const SIDECAR_VALUE_MOD_P_SLOT: usize = ASSET_LIMBS + U64_LIMBS;
    /// `cAMOD` — `asset mod p`, hashed into BOTH note commitments.
    pub const ASSET_MOD_P: usize = SIDECAR_VALUE_MOD_P_SLOT + 1;
    /// `cRAND` — the SPENT note's randomness.
    pub const IN_RANDOMNESS: usize = ASSET_MOD_P + 1;
    /// `cBL i` — the SPENT note's carrier blind lane `i`.
    pub const IN_BLIND: usize = IN_RANDOMNESS + 1;
    /// `cO k i` — minted note `k`'s value limb `i`.
    pub const OUT_LIMBS: usize = IN_BLIND + BINDING_BLIND_LANES;
    /// `cOMOD k` — minted note `k`'s `value mod p`.
    pub const OUT_MOD_P: usize = OUT_LIMBS + LINK_2OUT_OUTPUTS * U64_LIMBS;
    /// `cOWNER k` / `cORAND k` — minted note `k`'s owner and randomness, interleaved.
    pub const OUT_OWNER: usize = OUT_MOD_P + LINK_2OUT_OUTPUTS;
    /// `cWA j` — `DOMAIN_A` carrier lane `j`.
    pub const WIDE_A: usize = OUT_OWNER + 2 * LINK_2OUT_OUTPUTS;
    /// `cWB j` — `DOMAIN_B` carrier lane `j`.
    pub const WIDE_B: usize = WIDE_A + 8;
    /// `cOUTCM k` — minted note `k`'s commitment.
    pub const OUT_CM: usize = WIDE_B + 8;
    /// `cCARRY i` — the carry OUT of limb `i`. `CARRY + 3` is gate-pinned to zero.
    pub const CARRY: usize = OUT_CM + LINK_2OUT_OUTPUTS;
    /// `BITS_BASE` — base of the bit-decomposition block.
    pub const BITS: usize = CARRY + U64_LIMBS;
    /// `LINK2_WIDTH` — the main-trace width.
    pub const WIDTH: usize = BITS + 4 * U64_LIMBS * LIMB_BITS;

    /// `cO k i`.
    pub const fn out_limb(out: usize, limb: usize) -> usize {
        OUT_LIMBS + out * U64_LIMBS + limb
    }
    /// `cOWNER k`.
    pub const fn out_owner(out: usize) -> usize {
        OUT_OWNER + 2 * out
    }
    /// `cORAND k`.
    pub const fn out_randomness(out: usize) -> usize {
        OUT_OWNER + 1 + 2 * out
    }
    /// `cBit k i b` (`k`: 0 = spent value, 1 = asset, 2 = mint¹, 3 = mint²).
    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        BITS + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// **Public-input layout mirror** `[wide_binding[0..16], out_cm[0], out_cm[1]]`
/// (`ShieldedTransferValueLink2OutEmit.lean` §2).
pub mod pi {
    use super::LINK_2OUT_OUTPUTS;

    /// First lane of the SPENT note's carrier — supplied by the verifier from the complete-spend
    /// proof's own public inputs, never by this proof's claim.
    pub const WIDE_BINDING: usize = 0;
    /// The minted note commitment felts, in order.
    pub const OUT_CM: usize = 16;
    /// Total public-input count.
    pub const COUNT: usize = OUT_CM + LINK_2OUT_OUTPUTS;
}

/// One minted note's private witness: what it is worth, who owns it, and what hides it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedLink2OutMint {
    /// The minted note's full, unreduced value.
    pub value: u64,
    /// The recipient's owner felt — `hash_fact(key0,[key1,key2,key3])` of their spending key,
    /// which is what makes the new note spendable by them and nobody else.
    pub owner: BabyBear,
    /// Freshly chosen randomness; it is what makes the published commitment hiding.
    pub randomness: BabyBear,
}

/// The private witness for one spent input split across two minted outputs.
///
/// `value`, `asset_type`, `in_randomness` and `in_binding_blind` are the SPENT note's — they must
/// be the same values the complete-spend witness carries, or the sixteen lanes this proof publishes
/// will not equal the ones that proof PI-pins and the join refuses.
///
/// ⚑ **The two output values are given EXPLICITLY, and that is deliberate.** A witness type that
/// derived `out[1].value = value - out[0].value` could not express a non-conserving split, which
/// would make every negative test here vacuous — the floor must be satisfiable AND refutable. The
/// AIR is what refuses; the witness type is not.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedTransferLink2OutWitness {
    /// The spent note's full, unreduced value.
    pub value: u64,
    /// The asset identifier — the spent note's, and therefore both mints'.
    pub asset_type: u64,
    /// The spent note's randomness (absorbed by the carrier the spend proof published).
    pub in_randomness: BabyBear,
    /// The spent note's six carrier blind lanes.
    pub in_binding_blind: [BabyBear; BINDING_BLIND_LANES],
    /// The two minted notes.
    pub outputs: [ShieldedLink2OutMint; LINK_2OUT_OUTPUTS],
}

impl ShieldedTransferLink2OutWitness {
    /// An HONEST split: `value` divided into `first` and the remainder.
    ///
    /// Returns `None` when `first > value` — the caller cannot accidentally build a non-conserving
    /// witness through this door. (The struct literal remains open for adversarial construction;
    /// see the type docs.)
    pub fn split(
        value: u64,
        asset_type: u64,
        in_randomness: BabyBear,
        in_binding_blind: [BabyBear; BINDING_BLIND_LANES],
        first: ShieldedLink2OutMint,
        change_owner: BabyBear,
        change_randomness: BabyBear,
    ) -> Option<Self> {
        let change = value.checked_sub(first.value)?;
        Some(Self {
            value,
            asset_type,
            in_randomness,
            in_binding_blind,
            outputs: [
                first,
                ShieldedLink2OutMint {
                    value: change,
                    owner: change_owner,
                    randomness: change_randomness,
                },
            ],
        })
    }

    /// The sixteen-lane carrier of the SPENT note — bit-identical to
    /// `ShieldedTransferLinkWitness::in_wide_binding`, to `WideValueBindingWitness::wide_binding`
    /// and to the complete-spend proof's PI-pinned `wide[16]` for the same opening. (One absorb
    /// block, four producers; the Lean file IMPORTS the absorb term, so they cannot drift.)
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

    /// Minted note `k`'s commitment felt — `hash_fact(value_k mod p, [asset mod p, owner, rand])`,
    /// the SAME site `ShieldedSpendCompleteWitness::note_commitment_felt` opens and
    /// `dregg-shielded-shield::v1` mints. That identity is what makes BOTH outputs SPENDABLE: the
    /// complete-spend relation can open either leaf, so the value that arrives can leave again.
    pub fn out_note_commitment_felt(&self, k: usize) -> BabyBear {
        let mint = &self.outputs[k];
        hash_fact(
            u64_mod_p(mint.value),
            &[u64_mod_p(self.asset_type), mint.owner, mint.randomness],
        )
    }

    /// The two minted note commitments, in order.
    pub fn out_note_commitment_felts(&self) -> [BabyBear; LINK_2OUT_OUTPUTS] {
        core::array::from_fn(|k| self.out_note_commitment_felt(k))
    }
}

/// The carry chain the AIR states, computed FROM THE OUTPUTS.
///
/// ⚑ Deriving the carries from `o1 + o2` rather than solving them against `value` is what keeps
/// the `2^64` smuggle CONSTRUCTIBLE: two outputs whose sum wraps to `value` produce a trace in
/// which all four limb equations hold and `carry[3] == 1`, so only the Lean `carryTopZero` gate
/// stands between it and a mint. A generator that clamped the top carry would silently disarm the
/// adversary and leave the negative test asserting nothing.
///
/// Returns `(sum_limbs, carries)`: the limbs `o1 + o2` actually produces, and the four carries.
fn carry_chain(out0: u64, out1: u64) -> ([u16; U64_LIMBS], [u32; U64_LIMBS]) {
    let a = u64_limbs(out0);
    let b = u64_limbs(out1);
    let mut sum_limbs = [0u16; U64_LIMBS];
    let mut carries = [0u32; U64_LIMBS];
    let mut carry_in: u32 = 0;
    for i in 0..U64_LIMBS {
        let s = a[i] as u32 + b[i] as u32 + carry_in;
        sum_limbs[i] = (s & 0xffff) as u16;
        carry_in = s >> LIMB_BITS;
        carries[i] = carry_in;
    }
    (sum_limbs, carries)
}

/// Generate a constant two-row trace in the LEAN column layout, and its public claim.
///
/// The returned matrix is the descriptor-width MAIN trace; the IR-v2 prover fills the Poseidon2
/// chip lanes itself (`trace_with_chip_lanes`).
///
/// ⚑ This does NOT check conservation. It lays down exactly what the witness claims — the spent
/// value's own limbs, both outputs' limbs, and the carries `o1 + o2` produces — and lets the AIR
/// decide. A non-conserving witness yields a trace that no proof of this relation accepts.
pub fn generate_shielded_transfer_link_2out_trace(
    witness: &ShieldedTransferLink2OutWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let value = u64_limbs(witness.value);
    let asset = u64_limbs(witness.asset_type);
    let out_limbs: [[u16; U64_LIMBS]; LINK_2OUT_OUTPUTS] =
        core::array::from_fn(|k| u64_limbs(witness.outputs[k].value));
    let (_sum_limbs, carries) = carry_chain(witness.outputs[0].value, witness.outputs[1].value);
    let wide = witness.in_wide_binding();
    let out_cms = witness.out_note_commitment_felts();

    let mut row = vec![BabyBear::ZERO; col::WIDTH];
    for i in 0..U64_LIMBS {
        row[col::VALUE_LIMBS + i] = BabyBear::new(value[i] as u32);
        row[col::ASSET_LIMBS + i] = BabyBear::new(asset[i] as u32);
        for bit in 0..LIMB_BITS {
            row[col::bit(0, i, bit)] = BabyBear::new(((value[i] >> bit) & 1) as u32);
            row[col::bit(1, i, bit)] = BabyBear::new(((asset[i] >> bit) & 1) as u32);
        }
        for k in 0..LINK_2OUT_OUTPUTS {
            row[col::out_limb(k, i)] = BabyBear::new(out_limbs[k][i] as u32);
            for bit in 0..LIMB_BITS {
                row[col::bit(2 + k, i, bit)] = BabyBear::new(((out_limbs[k][i] >> bit) & 1) as u32);
            }
        }
        row[col::CARRY + i] = BabyBear::new(carries[i]);
    }
    // ⚑ `col::SIDECAR_VALUE_MOD_P_SLOT` is deliberately left ZERO: the Lean relation emits no gate
    // over it and no site reads it. Writing the reduction there would suggest it was bound.
    row[col::ASSET_MOD_P] = u64_mod_p(witness.asset_type);
    row[col::IN_RANDOMNESS] = witness.in_randomness;
    row[col::IN_BLIND..col::IN_BLIND + BINDING_BLIND_LANES]
        .copy_from_slice(&witness.in_binding_blind);
    for k in 0..LINK_2OUT_OUTPUTS {
        row[col::OUT_MOD_P + k] = u64_mod_p(witness.outputs[k].value);
        row[col::out_owner(k)] = witness.outputs[k].owner;
        row[col::out_randomness(k)] = witness.outputs[k].randomness;
        row[col::OUT_CM + k] = out_cms[k];
    }
    row[col::WIDE_A..col::WIDE_A + 8].copy_from_slice(&wide[..8]);
    row[col::WIDE_B..col::WIDE_B + 8].copy_from_slice(&wide[8..]);

    let mut public_inputs = Vec::with_capacity(pi::COUNT);
    public_inputs.extend_from_slice(&wide);
    public_inputs.extend_from_slice(&out_cms);
    (vec![row.clone(), row], public_inputs)
}

/// The public claim a 2-out value-link proof is checked against.
///
/// ⚑ Held for CONSTRUCTION and for tests. The deployed verifier does NOT trust it: it builds the
/// statement from the complete-spend proof's carrier and the wire's published note commitments
/// ([`verify_shielded_transfer_link_2out`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedTransferLink2OutClaim {
    /// The SPENT note's sixteen carrier lanes.
    pub in_wide_binding: [BabyBear; WIDE_VALUE_BINDING_LANES],
    /// The two MINTED notes' commitment felts, in order.
    pub out_note_commitments: [BabyBear; LINK_2OUT_OUTPUTS],
}

impl ShieldedTransferLink2OutClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(pi::COUNT);
        out.extend_from_slice(&self.in_wide_binding);
        out.extend_from_slice(&self.out_note_commitments);
        out
    }
}

/// A hiding proof that the sixteen published carrier lanes and BOTH published output note
/// commitments open to ONE `(value, asset)` split conservatively in two.
pub struct ShieldedTransferLink2OutProof {
    /// The public claim (construction-side; the deployed verifier supplies its own).
    pub claim: ShieldedTransferLink2OutClaim,
    /// The hiding IR-v2 proof. Both values, the asset, every randomness, the blind lanes, the
    /// carries and both recipient owners all stay witness-only.
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

impl ShieldedTransferLink2OutProof {
    /// Canonical postcard encoding for the wire's `link_proof` field.
    pub fn proof_bytes(&self) -> Vec<u8> {
        postcard::to_allocvec(&self.proof).expect("Ir2BatchProof postcard serialize")
    }
}

/// The backend-neutral statement: the Lean relation plus these canonical public inputs.
fn statement_for(
    public_inputs: &[BabyBear],
) -> Result<DescriptorStatement, ShieldedTransferLinkError> {
    DescriptorStatement::try_new(
        shielded_transfer_value_link_2out_descriptor().clone(),
        public_inputs.iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| ShieldedTransferLinkError::StatementRejected { reason })
}

/// Prove a 1-in/2-out value link from a RAW trace and public inputs.
///
/// ⚑ This is the ONE prover: [`prove_shielded_transfer_link_2out`] calls it after generating the
/// honest trace, and adversarial construction calls it with a mutated one. There is no second
/// proving path for tests to drift from — a `#[cfg(test)]` twin here would keep this module green
/// while the deployed path broke.
pub fn prove_shielded_transfer_link_2out_from_trace(
    trace: &[Vec<BabyBear>],
    public_inputs: &[BabyBear],
) -> Result<ShieldedTransferLink2OutProof, ShieldedTransferLinkError> {
    let statement = statement_for(public_inputs)?;
    let mem = MemBoundaryWitness::default();
    let umem = UMemBoundaryWitness::default();
    let proof = Plonky3HidingFriReference::prove(
        &statement,
        Plonky3HidingFriWitness {
            base_trace: trace,
            mem_boundary: &mem,
            map_heaps: &[],
            umem_boundary: &umem,
        },
    )
    .map_err(|reason| ShieldedTransferLinkError::ProveFailed { reason })?;
    let mut in_wide_binding = [BabyBear::ZERO; WIDE_VALUE_BINDING_LANES];
    in_wide_binding.copy_from_slice(&public_inputs[pi::WIDE_BINDING..pi::OUT_CM]);
    Ok(ShieldedTransferLink2OutProof {
        claim: ShieldedTransferLink2OutClaim {
            in_wide_binding,
            out_note_commitments: core::array::from_fn(|k| public_inputs[pi::OUT_CM + k]),
        },
        proof,
    })
}

/// Prove one input→two-output value link through the hiding path.
pub fn prove_shielded_transfer_link_2out(
    witness: &ShieldedTransferLink2OutWitness,
) -> Result<ShieldedTransferLink2OutProof, ShieldedTransferLinkError> {
    let (trace, pis) = generate_shielded_transfer_link_2out_trace(witness);
    prove_shielded_transfer_link_2out_from_trace(&trace, &pis)
}

/// **THE SPLIT VALUE-LINK GATE.**
///
/// Verify a serialized 2-out value-link proof against public inputs the CALLER supplies:
///
/// * `spend_wide_binding` — the sixteen carrier lanes the input's complete-spend proof PI-pins,
///   read off that proof AFTER it verified under the executor's committed root;
/// * `out_note_commitments` — the two felts the executor is about to append to `note_shielded`.
///
/// Neither comes from this proof's own claim, which is the whole point: the relation forces all
/// three to be functions of ONE limb opening tied by the carry chain, so a split that mints more
/// than it spends — by any amount, including exactly `2^64` — has no satisfying trace.
///
/// **Substrate: the relation is AUTHORED IN LEAN**
/// (`ShieldedTransferValueLink2OutEmit.lean`, 309 columns, 18 PIs, 305 constraints, byte-pinned by
/// `link2_emits_golden`). Rust supplies the statement and calls the verifier.
pub fn verify_shielded_transfer_link_2out(
    proof_bytes: &[u8],
    spend_wide_binding: &[BabyBear; WIDE_VALUE_BINDING_LANES],
    out_note_commitments: &[BabyBear; LINK_2OUT_OUTPUTS],
) -> Result<(), ShieldedTransferLinkError> {
    let proof: Ir2BatchProof<DreggZkStarkConfig> =
        postcard::from_bytes(proof_bytes).map_err(|error| {
            ShieldedTransferLinkError::ProofDecode {
                reason: error.to_string(),
            }
        })?;
    let claim = ShieldedTransferLink2OutClaim {
        in_wide_binding: *spend_wide_binding,
        out_note_commitments: *out_note_commitments,
    };
    let statement = statement_for(&claim.public_inputs())?;
    Plonky3HidingFriReference::verify(&statement, &proof)
        .map_err(|reason| ShieldedTransferLinkError::ProofRejected { reason })
}
