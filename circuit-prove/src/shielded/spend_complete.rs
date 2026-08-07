//! The COMPLETE FSI2 shielded-spend witness generator — the Rust half that CALLS the Lean-emitted
//! `dregg-shielded-spend-complete-fsi2::v1` golden
//! (`metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean`).
//!
//! **THE AIR IS AUTHORED IN LEAN.** This module reads the byte-pinned golden out of the Lean source,
//! parses it as IR-v2, produces a WITNESS TRACE that satisfies it, and proves/verifies through the
//! hiding-FRI backend. It authors NO constraint. The trace it produces is a second, independent
//! source; the FRI proof verifying against the Lean-emitted constraint system is the two-source
//! agreement (the Rust generator's trace vs the Lean-emitted golden).
//!
//! ## The relation (557 columns, 25 PIs `[nullifier] ++ committedRoot[8] ++ wideCarrier[16]`)
//!
//! Mirrors `ShieldedSpendCompleteEmit.lean` §1-§6 exactly:
//!
//! * **Membership fold** (cols 0..209): a depth-16, arity-4 FSN2 (`0x46534e32`) exact-linked
//!   indexed-Merkle fold. Row `L` carries `current` (`MCUR`), position bits (`MB0`/`MB1`), three
//!   siblings (`MSIB`), the 16 wide-carrier lanes (`MWIDE`, PI-pinned), and the 10-step FSN2 node
//!   sponge state (`MNODE`). The last row's node digest is pinned to the 8-lane committed root.
//! * **Leaf sponge** (cols 253..428): the 11-step FSI2 (`0x46534932`) leaf sponge over the 39-felt
//!   `[FSI2, REAL=1, addr0, addr1, 0×14, 0×4, nextTag, next0..15]` block; its digest is bound to
//!   row-0 `MCUR` (`leafBind`), and `cCM ≡ addr0 + 2^16·addr1` (`noteTie`).
//! * **Narrow fact chips** (cols 210..219): `cCM = hash_fact(cVMOD,[cAMOD,cOWNER,cRAND])` (`lkCM` —
//!   the same relation Shield mints), `cNUL = hash_fact(cCM,[key0..3])` pinned to PI 0 (`lkNullifier`),
//!   `cOWNER = hash_fact(key0,[key1,key2,key3])` (`lkOwnerDerive` — the double-spend closure).
//! * **Wide carrier** (cols 429..556): 128 boolean bit pins + 8 limb recompositions + the
//!   `cVMOD`/`cAMOD` reductions, and two domain-separated `cap_node8` sites whose outputs are the 16
//!   `MWIDE` lanes — column-for-column the `wide_value_binding.rs` sidecar, so the routed join
//!   `verify_same_opening` compares like against like.
//!
//! ## The backend (hiding is not lost)
//!
//! Proving/verifying goes through [`Plonky3HidingFriReference`] reading `SHIELDED_SPEND_COMPLETE_GOLDEN`
//! — the same salted-leaf hiding MMCS config the whole shielded family uses. Value, asset, owner,
//! spending key, randomness, blinding and the whole membership path stay witness-only.
//!
//! ## What the generator fills vs what the prover fills
//!
//! The generator places only MAIN-trace columns: the full 16-lane state16 sponge blocks (`fill_sponge`
//! is a WITNESS-ONLY replica of the deployed rate-4 sponge — it authors no constraint, it runs the
//! same `chip_permute_state16` the chip does), the narrow-fact digest outputs, and the wide-carrier
//! `out0` lanes. `Plonky3HidingFriReference::prove` builds every separate Poseidon2 chip table itself
//! (state16, narrow, wide) and welds the wide lanes 1..7 — see `trace_with_chip_lanes`.

use std::sync::LazyLock;

use dregg_circuit::cap_root::cap_node8;
use dregg_circuit::descriptor_ir2::{
    EffectVmDescriptor2, Ir2BatchProof, MemBoundaryWitness, UMemBoundaryWitness,
    chip_permute_state16, parse_vm_descriptor2,
};
use dregg_circuit::descriptor_proof_backend::{
    DescriptorProofProver, DescriptorProofVerifier, DescriptorStatement, Plonky3HidingFriReference,
    Plonky3HidingFriWitness,
};
use dregg_circuit::exact_nullifier_aafi::{
    Digest8, ExactLinkedDomains, TaggedKeyWire, exact_node_preimage_in,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use dregg_circuit::stark_zk::DreggZkStarkConfig;

/// The shielded exact-linked domain triple (`cell/src/shielded_note_set.rs`, Lean
/// `ShieldedExactMembershipFold.SHIELDED_*_DOMAIN`): `FSI2` leaf, `FSN2` node, `FSE2` empty.
const SHIELDED_DOMAINS: ExactLinkedDomains = ExactLinkedDomains {
    leaf: 0x4653_4932,  // "FSI2"
    node: 0x4653_4e32,  // "FSN2"
    empty: 0x4653_4532, // "FSE2"
};

/// Two distinct in-band carrier domain separators — the `wide_value_binding.rs` twins, so the routed
/// same-opening join compares like against like.
const DOMAIN_A: u32 = 0x5642_4e30; // "VBN0"
const DOMAIN_B: u32 = 0x5642_4e31; // "VBN1"

/// Number of 16-bit limbs in a canonical `u64`.
pub const U64_LIMBS: usize = 4;
/// Bits per canonical value/asset limb.
pub const LIMB_BITS: usize = 16;
/// Digest / root lanes.
pub const ROOT_LANES: usize = 8;
/// Extra field-valued blinding lanes.
pub const BINDING_BLIND_LANES: usize = 6;
/// Tree depth (rows of the membership fold).
pub const TREE_DEPTH: usize = 16;
/// The 16-lane wide carrier (two `cap_node8` sites of 8 lanes each).
pub const WIDE_LANES: usize = 16;

/// The Lean module that AUTHORS this AIR and byte-pins its wire string.
const EMIT_LEAN: &str =
    include_str!("../../../metatheory/Dregg2/Circuit/Emit/ShieldedSpendCompleteEmit.lean");

/// Split a `def <NAME> : String := r#"…"#` raw-string golden out of a Lean module (the shared
/// `wide_value_binding.rs`/`shield_opening.rs` convention — one splitter).
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
pub fn shielded_spend_complete_descriptor_json() -> &'static str {
    lean_raw_golden(EMIT_LEAN, "SHIELDED_SPEND_COMPLETE_GOLDEN")
}

/// **Witness-layout mirror** of the Lean column layout (`ShieldedSpendCompleteEmit.lean` §1 +
/// `ShieldedSpendExactMembershipEmit.lean` §1). This authors no algebra — it only says where the
/// trace producer places each cell — and [`LEAN_DESCRIPTOR`] checks `WIDTH` against the emitted width.
pub mod col {
    use super::{LIMB_BITS, U64_LIMBS};

    // Membership core (`ShieldedSpendExactMembershipEmit.lean` §1).
    /// `MCUR` — current node digest, 8 lanes.
    pub const MCUR: usize = 0;
    /// `MB0` — position bit 0.
    pub const MB0: usize = 8;
    /// `MB1` — position bit 1.
    pub const MB1: usize = 9;
    /// `MSIB` — three sibling digests, 3 × 8 lanes.
    pub const MSIB: usize = 10;
    /// `MWIDE` — the 16-lane wide carrier (PI-pinned first row).
    pub const MWIDE: usize = 34;
    /// `MNODE` — the FSN2 node sponge state (10 state16 steps × 16 lanes).
    pub const MNODE: usize = 50;

    // Completion columns (`ShieldedSpendCompleteEmit.lean` §1).
    /// `cVMOD` — `value mod p`.
    pub const CVMOD: usize = 210;
    /// `cAMOD` — `asset mod p`.
    pub const CAMOD: usize = 211;
    /// `cOWNER` — derived note owner.
    pub const COWNER: usize = 212;
    /// `cRAND` — note randomness.
    pub const CRAND: usize = 213;
    /// `cCM` — recomputed note commitment.
    pub const CCM: usize = 214;
    /// `cNUL` — published nullifier.
    pub const CNUL: usize = 215;
    /// `cKEY i` — spending-key limb `i`.
    pub const CKEY: usize = 216;
    /// `cV i` — value `u16` limb `i`.
    pub const CV: usize = 220;
    /// `cA i` — asset `u16` limb `i`.
    pub const CA: usize = 224;
    /// `cBL i` — carrier blind lane `i`.
    pub const CBL: usize = 228;
    /// `cADDR0` — leaf address limb 0.
    pub const CADDR0: usize = 234;
    /// `cADDR1` — leaf address limb 1.
    pub const CADDR1: usize = 235;
    /// `cNEXTTAG` — opened leaf's next-address tag (free witness).
    pub const CNEXTTAG: usize = 236;
    /// `cNEXT i` — opened leaf's next-address limb `i` (free witness).
    pub const CNEXT: usize = 237;
    /// `LEAF_STATE_BASE` — the FSI2 leaf sponge state (11 state16 steps × 16 lanes).
    pub const LEAF_STATE_BASE: usize = 253;
    /// `SPEND_BITS_BASE` — base of the carrier bit-decomposition block.
    pub const SPEND_BITS_BASE: usize = 429;
    /// `C_WIDTH` — the completed main-trace width.
    pub const WIDTH: usize = SPEND_BITS_BASE + 2 * U64_LIMBS * LIMB_BITS;

    /// `cLimbS k i` — value (`k=0`) / asset (`k=1`) limb `i`.
    pub const fn limb(kind: usize, i: usize) -> usize {
        if kind == 0 { CV + i } else { CA + i }
    }

    /// `cBit k i b` — bit `b` of limb `i` of kind `k`.
    pub const fn bit(kind: usize, limb: usize, bit: usize) -> usize {
        SPEND_BITS_BASE + (kind * U64_LIMBS + limb) * LIMB_BITS + bit
    }
}

/// **Public-input layout mirror** `[nullifier] ++ committedRoot[8] ++ wideCarrier[16]`
/// (`ShieldedSpendExactMembershipDescriptor.lean` §2).
pub mod pi {
    /// The published nullifier.
    pub const NUL: usize = 0;
    /// The 8-lane committed shielded-accumulator root.
    pub const COMMITTED: usize = 1;
    /// The 16-lane wide-`u64` value carrier.
    pub const WIDE: usize = 9;
    /// Total public-input count.
    pub const COUNT: usize = 25;
}

/// Parse-once cache of the Lean-emitted relation; the asserts detect a Lean layout move.
static LEAN_DESCRIPTOR: LazyLock<EffectVmDescriptor2> = LazyLock::new(|| {
    let desc = parse_vm_descriptor2(shielded_spend_complete_descriptor_json())
        .expect("the Lean-emitted complete shielded-spend descriptor parses as IR-v2");
    assert_eq!(
        desc.trace_width,
        col::WIDTH,
        "the Lean column layout moved; `col` no longer mirrors ShieldedSpendCompleteEmit.lean §1"
    );
    assert_eq!(
        desc.public_input_count,
        pi::COUNT,
        "the Lean public-input layout moved; `pi` no longer mirrors the 25-PI spend layout"
    );
    desc
});

/// The Lean-emitted complete FSI2 shielded-spend relation.
pub fn shielded_spend_complete_descriptor() -> &'static EffectVmDescriptor2 {
    &LEAN_DESCRIPTOR
}

/// The 8 digest columns of a state16 sponge based at `base` with `absorb_chunks` absorbs
/// (`ExactNullifierAafiDescriptorPlan.digestColsAt`): the last-absorb low-4 ‖ final-squeeze low-4.
/// Used by the layout-mirror test to pin the convention against the Lean golden's `pi_binding`
/// columns; the generator reads the digest straight off [`fill_sponge`]'s return.
#[cfg(test)]
const fn digest_cols(base: usize, absorb_chunks: usize) -> [usize; ROOT_LANES] {
    let lo = base + 16 * (absorb_chunks - 1);
    let hi = base + 16 * absorb_chunks;
    [lo, lo + 1, lo + 2, lo + 3, hi, hi + 1, hi + 2, hi + 3]
}

/// **The witness-only rate-4 state16 sponge filler.** A faithful replica of the deployed
/// `hash_many_8` sponge (`shielded_whole_note_swap_substrate.rs::fill_sponge`) — it AUTHORS NO
/// CONSTRAINT; it runs the exact `chip_permute_state16` the state16 chip runs, so the trace it fills
/// satisfies the Lean-emitted state16 lookups by construction. Writes the full 16-lane post-state of
/// every step into `row[state_base + 16*stage ..]` and returns the 8-lane squeezed digest.
fn fill_sponge(row: &mut [BabyBear], state_base: usize, inputs: &[BabyBear]) -> Digest8 {
    debug_assert!(!inputs.is_empty());
    let mut state = [BabyBear::ZERO; 16];
    state[4] = BabyBear::new(inputs.len() as u32);
    let chunks = inputs.len().div_ceil(4);
    let mut first_squeeze = [BabyBear::ZERO; 4];
    for (stage, chunk) in inputs.chunks(4).enumerate() {
        for (lane, value) in chunk.iter().copied().enumerate() {
            state[lane] += value;
        }
        state = chip_permute_state16(state);
        row[state_base + 16 * stage..state_base + 16 * (stage + 1)].copy_from_slice(&state);
        if stage + 1 == chunks {
            first_squeeze.copy_from_slice(&state[..4]);
        }
    }
    state = chip_permute_state16(state);
    row[state_base + 16 * chunks..state_base + 16 * (chunks + 1)].copy_from_slice(&state);
    [
        first_squeeze[0],
        first_squeeze[1],
        first_squeeze[2],
        first_squeeze[3],
        state[0],
        state[1],
        state[2],
        state[3],
    ]
}

fn u64_limbs(value: u64) -> [u16; U64_LIMBS] {
    core::array::from_fn(|i| ((value >> (i * LIMB_BITS)) & 0xffff) as u16)
}

fn u64_mod_p(value: u64) -> BabyBear {
    BabyBear::new((value % BABYBEAR_P as u64) as u32)
}

/// The note's authenticated place in the committed `ShieldedNoteSet` tree — the
/// membership half of a complete spend. Built at the route step from
/// `dregg_cell::ShieldedNoteSet::membership_path` (`ShieldedMembershipPath`), so the
/// leaf the spend opens is a GENUINE member of the committed accumulator and the fold
/// reaches its real `root8()` — not a synthetic single-leaf tree.
#[derive(Clone, Debug)]
pub struct ShieldedSpendMembership {
    /// The child position digit (0..4) at each level, least-significant level first.
    /// The membership core reads it as `pos = MB0 + 2·MB1`.
    pub positions: [u8; TREE_DEPTH],
    /// The three sibling digests at each level, in increasing child-slot order — the
    /// `recompose` co-path convention the Lean `childExpr`/`exactChildren4` realizes.
    pub siblings: [[Digest8; 3]; TREE_DEPTH],
    /// The opened leaf's linked `next_addr` successor (a free witness — the committed
    /// leaf's content, `cNEXTTAG`/`cNEXT*`). For the largest present key this is `TOP`.
    pub next_addr: TaggedKeyWire,
}

/// Private witness for a complete FSI2 shielded spend. The value/asset/owner/key/randomness/blind and
/// the whole membership path are witness-only; the note is a GENUINE member of a committed
/// [`dregg_cell::ShieldedNoteSet`] whose `root8()` the fold reaches — the membership path
/// ([`ShieldedSpendMembership`]) supplies its authenticated place in that tree.
#[derive(Clone, Debug)]
pub struct ShieldedSpendCompleteWitness {
    /// Full, unreduced note value.
    pub value: u64,
    /// Full, unreduced asset identifier.
    pub asset_type: u64,
    /// Note randomness (absorbed by BOTH `lkCM` and the wide carrier — the coupling).
    pub randomness: BabyBear,
    /// The four-limb spending key: `cOWNER = hash_fact(key0,[key1,key2,key3])`, and the nullifier
    /// `cNUL = hash_fact(cCM,[key0..3])`.
    pub spending_key: [BabyBear; 4],
    /// The six carrier blind lanes.
    pub binding_blind: [BabyBear; BINDING_BLIND_LANES],
    /// The note's authenticated place in the committed shielded accumulator.
    pub membership: ShieldedSpendMembership,
}

impl ShieldedSpendCompleteWitness {
    /// **The Poseidon2 note-commitment felt this spend opens** —
    /// `hash_fact(value mod p, [asset mod p, hash_fact(key0,[key1,key2,key3]), rand])`. Its
    /// [`dregg_cell::felt_to_bytes32`] encoding (low 4 bytes, the rest zero) is BOTH the leaf
    /// address the membership fold pins (`cADDR0 = cCM & 0xFFFF`, `cADDR1 = cCM >> 16`, higher
    /// limbs zero) AND the exact 32-byte commitment a `dregg-shielded-shield::v1` mint appends to
    /// the `ShieldedNoteSet`. So a note minted by Shield is spendable HERE iff the mint used the
    /// same `(value mod p, asset mod p, owner = hash_fact(key), rand)`.
    pub fn note_commitment_felt(&self) -> BabyBear {
        let cvmod = u64_mod_p(self.value);
        let camod = u64_mod_p(self.asset_type);
        let cowner = hash_fact(
            self.spending_key[0],
            &[
                self.spending_key[1],
                self.spending_key[2],
                self.spending_key[3],
            ],
        );
        hash_fact(cvmod, &[camod, cowner, self.randomness])
    }
}

/// The public claim a complete shielded-spend proof carries: the nullifier, the 8-lane committed root
/// the membership fold reaches, and the 16-lane wide value/asset carrier.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShieldedSpendCompleteClaim {
    /// The published nullifier (PI 0).
    pub nullifier: BabyBear,
    /// The 8-lane committed accumulator root (PI 1..9).
    pub committed_root: Digest8,
    /// The 16-lane wide value/asset carrier (PI 9..25).
    pub wide_binding: [BabyBear; WIDE_LANES],
}

impl ShieldedSpendCompleteClaim {
    fn public_inputs(&self) -> Vec<BabyBear> {
        let mut out = Vec::with_capacity(pi::COUNT);
        out.push(self.nullifier);
        out.extend_from_slice(&self.committed_root);
        out.extend_from_slice(&self.wide_binding);
        out
    }
}

/// The two domain-separated `cap_node8` carrier images over the note's canonical limb opening — the
/// `wide_value_binding.rs` `wide_binding()` shape (`spendWideLeft`/`spendWideRight`).
fn wide_carrier(
    value: [u16; U64_LIMBS],
    asset: [u16; U64_LIMBS],
    randomness: BabyBear,
    blind: &[BabyBear; BINDING_BLIND_LANES],
) -> [BabyBear; WIDE_LANES] {
    let right = [
        BabyBear::new(asset[3] as u32),
        randomness,
        blind[0],
        blind[1],
        blind[2],
        blind[3],
        blind[4],
        blind[5],
    ];
    let left = |domain: u32| {
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
    let mut out = [BabyBear::ZERO; WIDE_LANES];
    out[..8].copy_from_slice(&a);
    out[8..].copy_from_slice(&b);
    out
}

/// Generate the 557-column, 16-row MAIN trace and its public claim. The IR-v2 prover fills the
/// Poseidon2 chip lanes itself.
pub fn generate_shielded_spend_complete_trace(
    witness: &ShieldedSpendCompleteWitness,
) -> (Vec<Vec<BabyBear>>, ShieldedSpendCompleteClaim) {
    // --- Derived note cells (identical on every row: the note lookups carry no row guard) ---
    let value_limbs = u64_limbs(witness.value);
    let asset_limbs = u64_limbs(witness.asset_type);
    let cvmod = u64_mod_p(witness.value);
    let camod = u64_mod_p(witness.asset_type);
    let key = witness.spending_key;
    // cOWNER = hash_fact(key0, [key1, key2, key3]) — the C8 owner derivation (double-spend closure).
    let cowner = hash_fact(key[0], &[key[1], key[2], key[3]]);
    // cCM = hash_fact(cVMOD, [cAMOD, cOWNER, cRAND]) — byte-for-byte the relation Shield mints.
    let ccm = hash_fact(cvmod, &[camod, cowner, witness.randomness]);
    // cNUL = hash_fact(cCM, [key0..3]) — the nullifier derives from the OPENED note.
    let cnul = hash_fact(ccm, &[key[0], key[1], key[2], key[3]]);
    debug_assert_eq!(
        ccm,
        witness.note_commitment_felt(),
        "the generator's cCM must be the witness's note-commitment felt (one source)"
    );
    // cADDR = raw_to_u16_le(cCM) low limbs: bytes 0..4 = the felt LE, so limbs 0,1 carry it.
    let ccm_u32 = ccm.as_u32();
    let addr0 = BabyBear::new(ccm_u32 & 0xffff);
    let addr1 = BabyBear::new(ccm_u32 >> 16);
    // The opened leaf's next pointer is a free witness — its content is the linked successor the
    // committed leaf holds (the membership path carries it; `TOP` for the largest present key).
    let next = witness.membership.next_addr;
    let next_tag = BabyBear::new(u32::from(next.tag));
    let next_limbs: [BabyBear; 16] =
        core::array::from_fn(|i| BabyBear::new(u32::from(next.raw_u16_le[i])));

    let wide = wide_carrier(
        value_limbs,
        asset_limbs,
        witness.randomness,
        &witness.binding_blind,
    );

    // The 39-felt FSI2 leaf block: [FSI2, REAL=1, addr0, addr1, 0×14, 0×4 (hidden value), next17].
    let mut leaf_preimage: Vec<BabyBear> = Vec::with_capacity(39);
    leaf_preimage.push(BabyBear::new(SHIELDED_DOMAINS.leaf));
    leaf_preimage.push(BabyBear::ONE);
    leaf_preimage.push(addr0);
    leaf_preimage.push(addr1);
    leaf_preimage.extend(core::iter::repeat_n(BabyBear::ZERO, 14)); // addr limbs 2..15
    leaf_preimage.extend(core::iter::repeat_n(BabyBear::ZERO, 4)); // hidden value block
    leaf_preimage.push(next_tag);
    leaf_preimage.extend_from_slice(&next_limbs);
    debug_assert_eq!(leaf_preimage.len(), 39);

    // The leaf digest = the sponge of the FSI2 leaf block (row-0 `MCUR`, via `leafBind`).
    let leaf_digest = {
        let mut scratch = vec![BabyBear::ZERO; col::WIDTH];
        fill_sponge(&mut scratch, col::LEAF_STATE_BASE, &leaf_preimage)
    };

    let mut rows: Vec<Vec<BabyBear>> = Vec::with_capacity(TREE_DEPTH);
    let mut current: Digest8 = leaf_digest;
    for level in 0..TREE_DEPTH {
        let mut row = vec![BabyBear::ZERO; col::WIDTH];

        let position = witness.membership.positions[level];
        debug_assert!(position < 4, "membership position digit must be in 0..4");
        let level_siblings = &witness.membership.siblings[level];

        // Membership core: current, the 2-bit position (`pos = MB0 + 2·MB1`), the three siblings
        // (increasing child-slot order), and the PI-pinned wide carrier.
        row[col::MCUR..col::MCUR + 8].copy_from_slice(&current);
        row[col::MB0] = BabyBear::new(u32::from(position & 1));
        row[col::MB1] = BabyBear::new(u32::from((position >> 1) & 1));
        for s in 0..3 {
            row[col::MSIB + s * 8..col::MSIB + s * 8 + 8].copy_from_slice(&level_siblings[s]);
        }
        row[col::MWIDE..col::MWIDE + WIDE_LANES].copy_from_slice(&wide);

        // FSN2 node sponge over the four children with `current` at slot `position` and the three
        // siblings filling the rest in increasing slot order — the deployed `exactChildren4` /
        // `recompose` placement the Lean `childExpr` realizes.
        let mut children: [Digest8; 4] = [[BabyBear::ZERO; ROOT_LANES]; 4];
        let mut sib = 0usize;
        for (slot, child) in children.iter_mut().enumerate() {
            if slot == usize::from(position) {
                *child = current;
            } else {
                *child = level_siblings[sib];
                sib += 1;
            }
        }
        let node_preimage = exact_node_preimage_in(SHIELDED_DOMAINS, children);
        let parent = fill_sponge(&mut row, col::MNODE, &node_preimage);

        // Note cells (constant across rows — the note lookups carry no row guard).
        row[col::CVMOD] = cvmod;
        row[col::CAMOD] = camod;
        row[col::COWNER] = cowner;
        row[col::CRAND] = witness.randomness;
        row[col::CCM] = ccm;
        row[col::CNUL] = cnul;
        row[col::CKEY..col::CKEY + 4].copy_from_slice(&key);
        for i in 0..U64_LIMBS {
            row[col::CV + i] = BabyBear::new(value_limbs[i] as u32);
            row[col::CA + i] = BabyBear::new(asset_limbs[i] as u32);
        }
        row[col::CBL..col::CBL + BINDING_BLIND_LANES].copy_from_slice(&witness.binding_blind);
        row[col::CADDR0] = addr0;
        row[col::CADDR1] = addr1;
        row[col::CNEXTTAG] = next_tag;
        row[col::CNEXT..col::CNEXT + 16].copy_from_slice(&next_limbs);

        // FSI2 leaf sponge (constant across rows; row-0 `leafBind` reads its digest columns).
        let ld = fill_sponge(&mut row, col::LEAF_STATE_BASE, &leaf_preimage);
        debug_assert_eq!(ld, leaf_digest, "leaf sponge digest is stable across rows");

        // Wide carrier felt-width block: 128 bit pins + limbs (limbs already placed at CV/CA).
        for kind in 0..2 {
            let limbs = if kind == 0 { value_limbs } else { asset_limbs };
            for i in 0..U64_LIMBS {
                for b in 0..LIMB_BITS {
                    row[col::bit(kind, i, b)] = BabyBear::new(((limbs[i] >> b) & 1) as u32);
                }
            }
        }

        rows.push(row);
        current = parent;
    }
    // After folding all 16 levels, `current` is the fold root — the last row's node digest, which
    // `rootPins` pins to the 8-lane committed PI.
    let committed_root = current;

    let claim = ShieldedSpendCompleteClaim {
        nullifier: cnul,
        committed_root,
        wide_binding: wide,
    };
    (rows, claim)
}

/// Construction/verification failures.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShieldedSpendCompleteError {
    StatementRejected { reason: String },
    ProveFailed { reason: String },
    VerifyFailed { reason: String },
}

impl core::fmt::Display for ShieldedSpendCompleteError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::StatementRejected { reason } => {
                write!(f, "complete shielded-spend statement rejected: {reason}")
            }
            Self::ProveFailed { reason } => {
                write!(f, "complete shielded-spend proving failed: {reason}")
            }
            Self::VerifyFailed { reason } => {
                write!(f, "complete shielded-spend proof rejected: {reason}")
            }
        }
    }
}

impl std::error::Error for ShieldedSpendCompleteError {}

/// A hiding complete-shielded-spend proof plus its public claim.
pub struct ShieldedSpendCompleteProof {
    pub claim: ShieldedSpendCompleteClaim,
    pub proof: Ir2BatchProof<DreggZkStarkConfig>,
}

fn statement_for(
    claim: &ShieldedSpendCompleteClaim,
) -> Result<DescriptorStatement, ShieldedSpendCompleteError> {
    DescriptorStatement::try_new(
        shielded_spend_complete_descriptor().clone(),
        claim.public_inputs().iter().map(|f| f.as_u32()).collect(),
    )
    .map_err(|reason| ShieldedSpendCompleteError::StatementRejected { reason })
}

/// Prove a complete FSI2 shielded spend through the hiding IR-v2 backend.
pub fn prove_shielded_spend_complete(
    witness: &ShieldedSpendCompleteWitness,
) -> Result<ShieldedSpendCompleteProof, ShieldedSpendCompleteError> {
    let (trace, claim) = generate_shielded_spend_complete_trace(witness);
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
    .map_err(|reason| ShieldedSpendCompleteError::ProveFailed { reason })?;
    Ok(ShieldedSpendCompleteProof { claim, proof })
}

/// Verify a complete shielded-spend proof against its public claim `(nullifier, committedRoot[8],
/// wide[16])`. The `.piBinding`s force the claim to equal the proven cells: a claim decoupled from
/// the proof REJECTS (the nullifier pin, the 8-lane root pin, the 16-lane carrier pins).
pub fn verify_shielded_spend_complete(
    proof: &ShieldedSpendCompleteProof,
) -> Result<(), ShieldedSpendCompleteError> {
    let statement = statement_for(&proof.claim)?;
    Plonky3HidingFriReference::verify(&statement, &proof.proof)
        .map_err(|reason| ShieldedSpendCompleteError::VerifyFailed { reason })
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_cell::{ShieldedNoteCommitment, ShieldedNoteSet, felt_to_bytes32};

    /// Build a complete-spend witness whose note is a GENUINE member of a fresh
    /// `ShieldedNoteSet` (populated with the note plus any `decoys`), and return the
    /// witness, the populated set, and the note's committed 32-byte commitment. The
    /// witness's membership path is the note's REAL authenticated place in that set,
    /// so the generated trace folds to the set's `root8()`. This is the honest route
    /// the executor drives: a Shield mint lands the note, a spend opens it against the
    /// committed accumulator.
    fn witness_in_set(
        value: u64,
        asset_type: u64,
        randomness: BabyBear,
        spending_key: [BabyBear; 4],
        decoys: &[[u8; 32]],
    ) -> (
        ShieldedSpendCompleteWitness,
        ShieldedNoteSet,
        ShieldedNoteCommitment,
    ) {
        let binding_blind = core::array::from_fn(|i| BabyBear::new(100 + i as u32));
        // A probe witness (trivial membership) just to derive the note-commitment felt.
        let probe = ShieldedSpendCompleteWitness {
            value,
            asset_type,
            randomness,
            spending_key,
            binding_blind,
            membership: ShieldedSpendMembership {
                positions: [0; TREE_DEPTH],
                siblings: [[[BabyBear::ZERO; ROOT_LANES]; 3]; TREE_DEPTH],
                next_addr: TaggedKeyWire::top(),
            },
        };
        // The 32-byte commitment a Shield mint would append for this note.
        let commitment = ShieldedNoteCommitment(felt_to_bytes32(probe.note_commitment_felt()));

        let mut set = ShieldedNoteSet::new();
        for d in decoys {
            set.insert(ShieldedNoteCommitment(*d))
                .expect("decoy commitment inserts");
        }
        set.insert(commitment).expect("the spent note is committed");

        // The note's REAL authenticated place in the committed tree.
        let path = set
            .membership_path(&commitment)
            .expect("the committed note has a membership path");
        let membership = ShieldedSpendMembership {
            positions: path.path.positions,
            siblings: path.path.siblings,
            next_addr: path.leaf.next_addr().wire(),
        };
        let witness = ShieldedSpendCompleteWitness {
            membership,
            ..probe
        };
        (witness, set, commitment)
    }

    /// Distinct canonical single-felt decoy commitments (the shape a Shield mint lands).
    fn decoys(n: u32) -> Vec<[u8; 32]> {
        (0..n)
            .map(|i| felt_to_bytes32(BabyBear::new(0x0A0A_0000 + i)))
            .collect()
    }

    fn honest_witness() -> ShieldedSpendCompleteWitness {
        witness_in_set(
            123_456_789_012,
            7,
            BabyBear::new(0x1234_5678),
            [
                BabyBear::new(11),
                BabyBear::new(22),
                BabyBear::new(33),
                BabyBear::new(44),
            ],
            &decoys(2),
        )
        .0
    }

    #[test]
    fn descriptor_parses_and_layout_mirrors() {
        let desc = shielded_spend_complete_descriptor();
        assert_eq!(desc.trace_width, col::WIDTH);
        assert_eq!(desc.trace_width, 557);
        assert_eq!(desc.public_input_count, pi::COUNT);
        assert_eq!(desc.public_input_count, 25);
        assert_eq!(desc.name, "dregg-shielded-spend-complete-fsi2::v1");
        // The digest-column convention matches the Lean golden's pinned columns.
        assert_eq!(
            digest_cols(col::MNODE, 9),
            [178, 179, 180, 181, 194, 195, 196, 197]
        );
        assert_eq!(
            digest_cols(col::LEAF_STATE_BASE, 10),
            [397, 398, 399, 400, 413, 414, 415, 416]
        );
    }

    /// **PHASE 2a MILESTONE — the honest spend proves over a REAL member of a
    /// populated `ShieldedNoteSet`, and the fold reaches its committed `root8()`.**
    ///
    /// The note is a genuine member of a multi-member accumulator (two decoys + the
    /// note), so the membership path carries non-trivial positions and real sibling
    /// digests — not a synthetic single-leaf tree. The claim's `committed_root` IS the
    /// set's `root8()`, so the executor route can pin `piCommitted` to executor state.
    #[test]
    fn honest_spend_proves_and_verifies() {
        let (witness, set, _cm) = witness_in_set(
            123_456_789_012,
            7,
            BabyBear::new(0x1234_5678),
            [
                BabyBear::new(11),
                BabyBear::new(22),
                BabyBear::new(33),
                BabyBear::new(44),
            ],
            &decoys(2),
        );
        let (trace, claim) = generate_shielded_spend_complete_trace(&witness);
        assert_eq!(trace.len(), TREE_DEPTH);
        assert!(trace.iter().all(|r| r.len() == col::WIDTH));
        // THE PIN SOURCE: the fold reaches the REAL committed accumulator root8(), so
        // the route can source `piCommitted` from executor state (never the wire).
        assert_eq!(
            claim.committed_root,
            set.root8().limbs(),
            "the membership fold must reach the populated set's committed root8()"
        );
        // The generated trace satisfies the emitted golden and the hiding-FRI proof verifies:
        // the two-source agreement (Rust generator trace vs Lean-emitted constraint system).
        let proof =
            prove_shielded_spend_complete(&witness).expect("the honest complete spend must prove");
        assert_eq!(proof.claim, claim);
        verify_shielded_spend_complete(&proof).expect("the honest complete spend must verify");
    }

    /// **THE THEFT REFUSES (both polarities) — the #15 route mechanism, at the
    /// descriptor + root-sourcing level.**
    ///
    /// This is the cryptographic heart of the #15 close: once `piCommitted` is sourced
    /// from the executor's real `note_shielded.root8()` (never the wire), a forged-tree
    /// proof has no satisfying assignment.
    ///
    /// * **HONEST** — a note genuinely committed in the real accumulator proves
    ///   membership; the proof's `committed_root` IS the real `root8()`, and it
    ///   verifies.
    /// * **THEFT** — the attacker builds their OWN accumulator holding an UNAUTHORIZED
    ///   note (never committed in the real set) and honestly proves membership at THAT
    ///   tree's root `R`. The membership STARK is perfectly sound — it just proves
    ///   membership in the ATTACKER's tree (the falsifier `root_substitution_forges`).
    ///   The route then judges that proof under the REAL committed root: the fold
    ///   reached `R ≠ root8()`, so `rootPins` (the `.piBinding .last` 8-lane pin) has no
    ///   satisfying assignment and it REFUSES. That refusal is how the theft dies.
    ///
    /// ⚠ SCOPE — honest, not laundered: this exercises the refusal at the level of the
    /// complete-spend verifier plus the executor's root-sourcing (substituting the real
    /// `root8()` for the wire root). The full route through `apply_shielded_transfer`
    /// (the `ShieldedTransfer`/Pedersen-conservation object, the trait plumbing, the
    /// wire drop of `merkle_root`) is the deferred executor-plumbing pass; the
    /// cryptographic mechanism it must invoke is exactly this.
    #[test]
    fn theft_forged_tree_refuses_under_real_committed_root() {
        // The REAL committed accumulator: an authorized note the spender owns + decoys.
        let (honest_w, real_set, _cm) = witness_in_set(
            500_000_000,
            3,
            BabyBear::new(0xBEEF),
            [
                BabyBear::new(5),
                BabyBear::new(6),
                BabyBear::new(7),
                BabyBear::new(8),
            ],
            &decoys(3),
        );
        let real_root = real_set.root8().limbs();

        // HONEST: the spender's proof carries the REAL committed root and verifies.
        let honest_proof =
            prove_shielded_spend_complete(&honest_w).expect("the honest spend proves");
        assert_eq!(
            honest_proof.claim.committed_root, real_root,
            "the honest proof's committed root IS the real accumulator root8()"
        );
        verify_shielded_spend_complete(&honest_proof)
            .expect("the honest spend verifies under the executor-sourced real root");

        // THEFT: the attacker builds their OWN accumulator holding an UNAUTHORIZED note
        // and proves membership at THAT tree's root R.
        let (attacker_w, attacker_set, forged_cm) = witness_in_set(
            999_999_999,
            3,
            BabyBear::new(0xDEAD),
            [
                BabyBear::new(90),
                BabyBear::new(91),
                BabyBear::new(92),
                BabyBear::new(93),
            ],
            &[],
        );
        let forged_root = attacker_set.root8().limbs();
        // Vacuity guards: the forged note is NOT committed in the real accumulator, and
        // the attacker's tree root differs from the real committed root.
        assert!(
            !real_set.contains(&forged_cm),
            "the forged note must NOT be committed in the real accumulator"
        );
        assert_ne!(
            forged_root, real_root,
            "the forged tree's root R must differ from the real committed root"
        );

        let mut forged_proof = prove_shielded_spend_complete(&attacker_w)
            .expect("the attacker can prove membership in THEIR OWN tree");
        assert_eq!(
            forged_proof.claim.committed_root, forged_root,
            "the attacker's proof proves membership at R (self-consistent in their tree)"
        );
        // The forged proof is a GENUINE membership proof — in the attacker's tree at R.
        // The STARK is sound; it just proves the wrong tree. This is the falsifier.
        verify_shielded_spend_complete(&forged_proof)
            .expect("the forged proof is valid AT R (membership in the attacker's own tree)");

        // THE ROUTE (#15): `piCommitted` is sourced from the REAL executor accumulator
        // `root8()`, NEVER the wire. Judging the attacker's proof under the real root:
        forged_proof.claim.committed_root = real_root;
        assert!(
            verify_shielded_spend_complete(&forged_proof).is_err(),
            "a forged-tree proof, judged under the REAL committed root8(), must REFUSE — \
             the fold reached R != root8() and the 8-lane rootPins pin has no satisfying \
             assignment. The theft dies once piCommitted comes from executor state, not the wire."
        );
    }

    /// **The 8-lane committed-root pin BITES (the #15 mechanism, descriptor half).** A genuine proof,
    /// then a CLAIM whose committed root differs from the one the membership fold actually reached,
    /// must REFUSE. `rootPins` (`.piBinding .last`) forces the last-row node digest to equal
    /// `piCommitted`, so a published root decoupled from the fold has no satisfying assignment.
    ///
    /// ⚠ SCOPE: this is the "you cannot LIE about which root your fold reached" half. It is NOT yet
    /// the route theft. At the descriptor level an attacker CAN prove membership in their OWN tree
    /// with `piCommitted` = their own fold root (self-consistent). #15 closes only when the ROUTE
    /// (Phase 2) sources `piCommitted` from the executor's `note_shielded.root8()` — never the wire —
    /// so a forged tree's root `R ≠ root8` has no satisfying assignment. `deployed_admits_but_pin
    /// _rejects` stays LIVE by design until then.
    #[test]
    fn decoupled_committed_root_refuses() {
        let mut proof = prove_shielded_spend_complete(&honest_witness())
            .expect("the honest complete spend must prove");
        // Tamper one lane of the published committed root away from the fold's reached root.
        proof.claim.committed_root[0] += BabyBear::ONE;
        assert!(
            verify_shielded_spend_complete(&proof).is_err(),
            "a committed root decoupled from the membership fold must not verify"
        );
    }

    /// **The nullifier pin BITES.** `nulPin` (`.piBinding .first cNUL piNUL`) forces the published
    /// nullifier to equal the in-trace derivation `hash_fact(cCM,[key0..3])`; a decoupled nullifier
    /// claim REFUSES — a spend cannot publish a nullifier for a note it did not open.
    #[test]
    fn decoupled_nullifier_refuses() {
        let mut proof = prove_shielded_spend_complete(&honest_witness())
            .expect("the honest complete spend must prove");
        proof.claim.nullifier += BabyBear::ONE;
        assert!(
            verify_shielded_spend_complete(&proof).is_err(),
            "a nullifier decoupled from the opened note must not verify"
        );
    }

    /// **The wide-carrier pins BITE (the same-opening join).** `carrierPins` force the 16 `piWide`
    /// lanes to equal the `cap_node8` carrier images; a decoupled carrier lane REFUSES — the routed
    /// `verify_same_opening` join has a genuine full-`u64` opening to compare against.
    #[test]
    fn decoupled_wide_carrier_refuses() {
        let mut proof = prove_shielded_spend_complete(&honest_witness())
            .expect("the honest complete spend must prove");
        proof.claim.wide_binding[15] += BabyBear::ONE;
        assert!(
            verify_shielded_spend_complete(&proof).is_err(),
            "a wide-carrier lane decoupled from the note opening must not verify"
        );
    }
}
