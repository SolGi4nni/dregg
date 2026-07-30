//! Helper functions for the Effect VM AIR.
//!
//! Limb splitting/joining and the `compute_effects_hash` family that
//! produces the per-cell effects digest pinned into PI[EFFECTS_HASH_BASE].

use crate::field::BabyBear;
use crate::poseidon2::{hash_2_to_1, hash_many, hash_many_8};

use super::{AUX_BASE, Effect, aux_off};

/// Split a u64 into two BabyBear elements: `(lo = value mod 2^30, hi = value >> 30)`.
///
/// ⚠ **NOT INJECTIVE, IN TWO SEPARATE PLACES — and the contract that stood here
/// ("both values fit in BabyBear (< 2^31)" / "fits in u32 since val < 2^64") was
/// FALSE.** Measured, both poles pinned by
/// `circuit/tests/split_u64_is_not_injective.rs`:
///
///  * `hi` is `(val >> 30) as u32`, and `val >> 30` reaches `2^34` — so the `as u32`
///    **truncates bits 62..64 outright**. `split_u64(2^62)` equals `split_u64(0)` in
///    BOTH limbs, not merely the low one.
///  * `BabyBear::new` then reduces mod `p ≈ 2^31`, so `hi` aliases again at a value
///    period of `p · 2^30 ≈ 2^61`.
///
/// The limb pair is therefore faithful only on `[0, 2^61)`, and the LOW LIMB ALONE
/// — which is what every committed note-accumulator leaf carries
/// (`cell/src/commitment_set.rs` / `cell/src/nullifier_set.rs` `accumulator_leaf`)
/// — is faithful only on `[0, 2^30)`. `param::NOTE_VALUE_HI` (the companion limb)
/// is written by `effect_vm/trace.rs` on both note rows and read by NOTHING: no
/// gate, no PI pin, no accumulator, no verifier. See `HORIZONLOG.md` A8 and the Lean
/// tooth `metatheory/Dregg2/Bignum/LedgerBalance.lean` `accumulatorLeaf_aliases_at_2_30`.
///
/// ⚑ The arithmetic is DEPLOYED and is deliberately not changed here: this felt pair
/// is the balance-limb encoding the in-circuit 30-bit range proof runs on, it is the
/// preimage `compute_effects_hash_4` absorbs, and the low limb is the leaf value the
/// noteSpend/noteCreate grow-gates open against BY CONSTRAINT
/// (`prmCol NOTE_VALUE_LO`). Widening any of that is a descriptor re-emit plus a VK
/// rotation, not a helper edit.
pub fn split_u64(val: u64) -> (BabyBear, BabyBear) {
    let lo = (val & 0x3FFF_FFFF) as u32; // lower 30 bits
    let hi = (val >> 30) as u32; // bits 30..62 ONLY — bits 62..64 are truncated here
    (BabyBear::new(lo), BabyBear::new(hi))
}

/// Reconstruct a u64 from split BabyBear limbs.
#[allow(dead_code)]
fn join_u64(lo: BabyBear, hi: BabyBear) -> u64 {
    (lo.0 as u64) | ((hi.0 as u64) << 30)
}

/// **THE single family-F1 encoding in the tree** — 8 BabyBear limbs, 4 little-endian bytes each,
/// reduced mod `p`. Position 0 carries bytes `[0..4]`; position 7 carries bytes `[28..32]`.
///
/// Every former duplicate (`bytes32_to_8_limbs`'s callers, the three nested
/// `bytes32_to_8_felts` clones, `bytes32_to_limbs`, `bytes_to_babybear_vec`,
/// `stark_delegation_bytes32_to_babybear`) now calls THIS body. That collapse moved zero bytes:
/// all of them computed the same map. Keeping one body is the point — a second name for the same
/// arithmetic is how the ~17-implementation zoo grew.
///
/// ⚠ **NOT injective, and NOT "canonical".** The word "canonical" used to appear here and is
/// exactly what invited the re-inventions. The mod-`p` reduction identifies a 4-byte chunk `x`
/// with `x + p`, and a uniformly random chunk needs reducing with probability
/// `1 − p/2^32 = 53.1%`, so a colliding pair is CONSTRUCTED in `O(1)` — no grind — wherever the
/// bytes are attacker-chosen. It is deterministic and identical on both projectors, which is why
/// a collision over-includes (an honest turn goes UNSAT) rather than authorizing a forgery; that
/// is an availability property, not a binding one.
///
/// The canonical codec is `dregg_codec::Limbs16` (16 little-endian u16 limbs, injective) with
/// `dregg_codec::Digest8` for committed fixed-width slots. Migrating this call graph onto it is
/// Stage 2 of `docs/DESIGN-canonical-byte-felt-codec.md` — VK-affecting, so not done here.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
#[inline]
pub fn bytes32_to_8_limbs(b: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    for i in 0..8 {
        let off = i * 4;
        let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
        out[i] = BabyBear::new(v % crate::field::BABYBEAR_P);
    }
    out
}

/// **THE SHARED FIELDS-OCTET PROJECTION (v13)** — decompose a 32-byte flat-record
/// field value (`fields[0..7]`) into 8 BabyBear lanes, **u64-lane first**.
///
/// This is the faithful 8-felt replacement for the `fold_bytes32_to_bb` Horner
/// fold at the welded rotated limbs `4 + i` (r3..r10): lane 0 rides the existing
/// welded limb; lanes 1..7 ride the appended fields completion pre-limbs. Every
/// producer of a fields[0..7] felt (the v1 `SetField` param projection, the two
/// flat-record pre-limb twins `cell::commitment::compute_rotated_pre_limbs` /
/// `dregg_turn::rotation_witness::produce`, the rotated trace `fill_block` v1
/// source, and the slot-caveat manifest params) MUST project through THIS
/// function so all projectors agree byte-for-byte.
///
/// ## Lane layout — WHY NOT plain [`bytes32_to_8_limbs`] (THE ENCODING AUDIT)
///
/// The kernel's numeric field encoding is `field_from_u64`
/// (`cell/src/program/eval.rs:2741`): the u64 value packs **big-endian into
/// bytes `[24..32]`**, bytes `[0..24]` zero. The kernel spec reads it back via
/// `field_to_u64` (BE bytes `24..32`) — every capacity gate
/// (`StateConstraint::{SettleEscrow, DischargeObligation, Vault}` in `eval.rs`)
/// evaluates over that u64 lane.
///
/// The staged capacity welds (`satisfaction_weld` escrow `Deposited=1/Consumed=2`
/// equalities, `discharge_weld` cursor/total additive advances + the
/// `DUE_BITS=28` due-ness range check, `vault_weld` 15-bit operand
/// decompositions) all read the ONE welded field limb and require it to carry
/// the **raw numeric value**. Under plain `bytes32_to_8_limbs` (LE 4-byte
/// chunks, byte 0 first):
///
///  * lane 0 = LE bytes `[0..4]` — **identically 0** for every
///    `field_from_u64` value (the value lives in bytes 24..32): the escrow
///    equality gates go UNSAT for honest settles, the discharge/vault
///    arithmetic reads 0 — broken;
///  * lane 7 = LE bytes `[28..32]` = **byte-swapped** lo32 (e.g. status 1 →
///    `0x0100_0000`) — equality constants could be re-derived, but the
///    additive/range welds cannot (byte-swap is not add-compatible) — broken.
///
/// NO plain-LE lane carries the numeric value, so the fields octet takes a
/// fields-specific grouping of the same 32 bytes:
///
/// ```text
///   lane 0 = u32::from_be_bytes(b[28..32])   // lo32 of the kernel u64 lane
///   lane 1 = u32::from_be_bytes(b[24..28])   // hi32 of the kernel u64 lane
///   lane k = u32::from_le_bytes(b[4(k-2)..4(k-2)+4])  for k = 2..7  // bytes 0..24
/// ```
///
/// Each lane reduced mod `p` (same as `bytes32_to_8_limbs`; deterministic,
/// total, identical on all projectors).
///
/// ⚠ **ALL 32 BYTES ARE READ. THEY ARE NOT BOUND.** This doc used to say "All 32 bytes are bound
/// across the 8 lanes — the same ~124-bit faithful bar as every other committed octet", and that is
/// false in the same way the word "canonical" was false twenty lines up, for the same reason.
///
/// The *layout* is exhaustive and correct — lanes 0/1 are BE over `b[28..32]`/`b[24..28]`, lanes 2..7
/// are LE over `b[0..24]`, every byte covered once with no gap or overlap. The loss is entirely the
/// per-lane `% p`:
///
///  * `p = 2013265921`, so `log2 p = 30.907` and eight lanes carry **247.26 bits** against 256.
///    **No 8-lane encoding of 32 bytes is injective under any chunking** — pigeonhole.
///  * `2p = 4026531842 < 2^32`, so **every** residue has ≥2 u32 preimages (`c`, `c + p`), and
///    residues below `2^32 − 2p` have three. A colliding sibling is CONSTRUCTED by adding `p` to any
///    4-byte chunk, with no grind — e.g. `01000000` and `02000078` share a lane.
///
/// ⚑ This is load-bearing here and nowhere else in the octet family: `fields[0..7]` are deliberately
/// excluded from the byte-exact authority residue (`cell/src/commitment.rs:1099`), so these lanes are
/// their only binding and they reach `TurnReceipt::{pre,post}_state_hash`. Every other consumer of a
/// mod-`p` octet either hashes the same preimage byte-exactly alongside, or takes a hash image the
/// caller cannot choose.
///
/// ## Consequences (the derivation, pinned)
///
///  * `field_limbs8(field_from_u64(v))[0] == v` for `v < 2^31` (and `== lo32(v)
///    mod p` generally); lanes 2..7 are 0. **The escrow/discharge/vault weld
///    constants survive verbatim** — the valve outcome of the v13 encoding
///    audit: `sel·(before[leg] − 1)`, `after = before + period`, the 28-bit
///    range checks and 15-bit decompositions all operate on the genuine value.
///    (Honest numeric domain: values `< 2^31`; the staged welds already assume
///    small numeric fields — DUE_BITS=28, 30-bit vault operands — so this is
///    not a new restriction.)
///  * For EXACT spec parity (`field_to_u64` reads the full u64 lane) the staged
///    capacity descriptors should ALSO pin lane 1 == 0 on their gated slots
///    when they regen — a named rider on their own big-bang rows (they are
///    STAGED, not in a committed VK; adding the hi-lane pin is not a deployed
///    gate change).
///  * `fold_bytes32_to_bb(x) ≠ field_limbs8(x)[0]` in general — every consumer
///    of the welded limbs 4+i re-derives at genesis (the re-genesis rider, the
///    bridge-mint_hash pattern).
///  * LANE-ORDER HAZARD: this order differs from [`bytes32_to_8_limbs`] (used
///    for hashes / EmitEvent / Custom / cap entries) AND from the historical
///    `fe_to_bb` LE-bytes-0..4 truncation (`turn::executor` manifest params).
///    Do not mix: flat-record fields[0..7] lanes are `field_limbs8`; 32-byte
///    hash identities remain `bytes32_to_8_limbs`.
// crypto index loops kept verbatim
#[allow(clippy::needless_range_loop)]
#[inline]
pub fn field_limbs8(b: &[u8; 32]) -> [BabyBear; 8] {
    let mut out = [BabyBear::ZERO; 8];
    let lo = u32::from_be_bytes([b[28], b[29], b[30], b[31]]);
    let hi = u32::from_be_bytes([b[24], b[25], b[26], b[27]]);
    out[0] = BabyBear::new(lo % crate::field::BABYBEAR_P);
    out[1] = BabyBear::new(hi % crate::field::BABYBEAR_P);
    for k in 2..8 {
        let off = (k - 2) * 4;
        let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
        out[k] = BabyBear::new(v % crate::field::BABYBEAR_P);
    }
    out
}

/// Fold of a full 32-byte value into a single BabyBear. **⚠ NOT collision-resistant — `O(1)`, and
/// `O(1)` even for a CHOSEN TARGET.** This doc used to open with "Collision-resistant fold" and
/// claim `~2^-31`; both are wrong, and the repo's own test says so
/// (`circuit/tests/effects_hash_fold_and_burn_target_width.rs`,
/// `fold_bytes32_to_bb_collides_in_o1_because_it_is_linear`, which exhibits the constructor).
///
/// `Σ limbᵢ · MIX^i (mod p)` is an **onto F_p-linear form** on the limb vector. Therefore:
/// finding a colliding pair is one linear solve, and finding a preimage of ANY chosen felt is one
/// linear solve. The `~2^-31` figure is the probability that two INDEPENDENT UNIFORM inputs
/// happen to collide — it is not an adversarial cost, and an adversary here pays none. It also
/// sits on top of the mod-`p` limb encoding, so it inherits that aliasing upstream.
///
/// This is the single worst arithmetic in the tree by attacker cost. It survives here because a
/// collision over-includes (both producer and verifier project identically, so an honest turn goes
/// UNSAT) rather than authorizing a forgery — availability, not theft. Migrating it is Stage 2/4 of
/// `docs/DESIGN-canonical-byte-felt-codec.md`; the replacement is `dregg_codec::Digest8`, never a
/// better one-felt fold, because no one-felt image of a 32-byte value is acceptable at a security
/// boundary (`2^15.45` birthday).
///
/// CLOSED (effect-vm-hash-truncation lane, 2026-05-28): the previous
/// `hash_to_bb` / `field_element_to_bb` projectors took ONLY the first 4 bytes
/// of each 32-byte hash/field element, so the EffectVM proof bound only 4
/// bytes of each value (P1-2 in AUDIT-turn-executor.md). Two effects differing
/// solely in bytes `[4..32]` projected to the *identical* BabyBear and thus to
/// the identical `compute_effects_hash` / `PI[EFFECTS_HASH]` — interchangeable
/// proofs.
///
/// This fold makes the felt a function of ALL 32 bytes via a Horner evaluation
/// over the 8 four-byte limbs in the BabyBear field:
///
/// ```text
///   fold = Σ_{i=0}^{7} limb_i · MIX^i   (mod p)
/// ```
///
/// where `limb_i` is the i-th little-endian 4-byte chunk and `MIX` is a fixed non-trivial field
/// element. Distinct invertible weights mean flipping a byte changes the output *by default*, and
/// two INDEPENDENT UNIFORM inputs collide with ~`1/p ≈ 2^-31` — which is strictly better than the
/// previous *guaranteed* collision whenever the low 4 bytes matched, and is still not a binding
/// property. Linearity means an adversary never draws from that distribution: they solve.
///
/// Both the executor projector (`effect_vm_bridge.rs`) and the SDK projector
/// (`cipherclerk.rs`) call THIS function, so their per-effect felts agree
/// byte-for-byte by construction. The full-strength 256-bit binding for the
/// EmitEvent/Custom families is carried by their 8-limb fields; this fold is
/// the single-felt closure for the remaining identity/hash params, which the
/// AIR pins into a param column and `compute_effects_hash` absorbs.
#[inline]
pub fn fold_bytes32_to_bb(b: &[u8; 32]) -> BabyBear {
    // Fixed non-trivial mixing constant (a 31-bit prime, < p). Chosen to be
    // far from 0/1 so the Horner weights MIX^i are well-distributed.
    const MIX: u32 = 0x4FD3_9C8B % crate::field::BABYBEAR_P;
    let mix = BabyBear::new(MIX);
    let limbs = bytes32_to_8_limbs(b);
    let mut acc = BabyBear::ZERO;
    // Horner: acc = ((..(limb7)*mix + limb6)*mix + ...)*mix + limb0
    for i in (0..8).rev() {
        acc = acc * mix + limbs[i];
    }
    acc
}

/// Canonical 32-byte encoding of an `Effect::Refusal` reason: the
/// `offered_action_commitment` with the reason discriminant XOR'd into its
/// low 4 bytes (little-endian). Projected into 8 limbs by both the executor
/// and SDK projectors, this binds the FULL 32-byte commitment plus the
/// discriminant across all 8 limbs (the prior single-felt
/// `discriminant + fold_bytes32_to_bb(commitment)` form bound only ~31 bits). ⚠ The "~256-bit
/// strength" this doc used to claim holds only because the input is a Poseidon2/BLAKE3 IMAGE, not
/// because of the encoder: the 8-limb split is mod-`p` aliasable in `O(1)` for CHOSEN bytes. The
/// strength is the hash's, borrowed.
///
/// Both `turn::executor::effect_vm_bridge` and `sdk::cipherclerk` call this so
/// their `[BabyBear; 8]` encodings agree byte-for-byte (protocol-tests
/// differential invariant).
#[inline]
pub fn refusal_reason_bytes(commitment: &[u8; 32], discriminant: u32) -> [u8; 32] {
    let mut out = *commitment;
    let low = u32::from_le_bytes([out[0], out[1], out[2], out[3]]) ^ discriminant;
    out[0..4].copy_from_slice(&low.to_le_bytes());
    out
}

/// Decompose a u64 into 4 BabyBear limbs (16 bits each, little-endian).
/// Returns `[lo16, mid_lo16, mid_hi16, hi16]` so the limbs sum back to
/// the original via `Σ limbs[i] * 2^(16*i)`. Used to project full-u64
/// effect values into the AIR PI without 30-bit truncation
/// (CAVEAT-LAYER-COVERAGE.md §6.5).
#[inline]
pub fn u64_to_4_limbs_16(value: u64) -> [BabyBear; 4] {
    [
        BabyBear::new((value & 0xFFFF) as u32),
        BabyBear::new(((value >> 16) & 0xFFFF) as u32),
        BabyBear::new(((value >> 32) & 0xFFFF) as u32),
        BabyBear::new(((value >> 48) & 0xFFFF) as u32),
    ]
}

/// Inverse of [`u64_to_4_limbs_16`]: reconstruct a u64 from 4 BabyBear
/// limbs of 16 bits each. Returns `None` if any limb exceeds 2^16
/// (rejects out-of-range limbs — adversarial-test entry point).
#[inline]
pub fn u64_from_4_limbs_16(limbs: &[BabyBear; 4]) -> Option<u64> {
    let mut acc: u64 = 0;
    for (i, l) in limbs.iter().enumerate() {
        let v = l.0 as u64;
        if v >= (1u64 << 16) {
            return None;
        }
        acc |= v << (16 * i);
    }
    Some(acc)
}

/// Stage 2 (sealing honesty): bit-decompose `reserved = sealed_mask | (mode << 8)`
/// into 8 boolean mask bits + 1 boolean mode bit, and write them into the
/// row's reserved-bit aux slots. The AIR's per-row unconditional decomposition
/// constraint verifies the witness against `state_before.RESERVED`.
pub(crate) fn fill_reserved_bits(row: &mut [BabyBear], sealed_mask: u32, mode_flag: u32) {
    row[AUX_BASE + aux_off::RESERVED_BIT_0] = BabyBear::new(sealed_mask & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_1] = BabyBear::new((sealed_mask >> 1) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_2] = BabyBear::new((sealed_mask >> 2) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_3] = BabyBear::new((sealed_mask >> 3) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_4] = BabyBear::new((sealed_mask >> 4) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_5] = BabyBear::new((sealed_mask >> 5) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_6] = BabyBear::new((sealed_mask >> 6) & 1);
    row[AUX_BASE + aux_off::RESERVED_BIT_7] = BabyBear::new((sealed_mask >> 7) & 1);
    row[AUX_BASE + aux_off::RESERVED_MODE] = BabyBear::new(mode_flag & 1);
}

/// W9-RANGECHECK: bit-decompose the *new* (state_after) balance limbs into
/// the `NEW_BAL_LO_BIT_BASE` / `NEW_BAL_HI_BIT_BASE` aux columns so the AIR's
/// per-row range / underflow constraint (booleanity + recomposition) is
/// satisfiable for honest traces.
///
/// `new_balance` is the post-effect cell balance. We split it the same way
/// `split_u64` does (lo = low 30 bits, hi = balance >> 30) and write 30
/// boolean bits per limb. The AIR enforces `Σ bit_i 2^i == balance_{lo,hi}`,
/// which pins each limb into `[0, 2^30)` and — because a wrapped (underflowed)
/// debit lands ≥ 2^30 — rejects modular-subtraction underflow in-circuit.
///
/// Honest balances always fit (init limbs asserted `< 2^30` at trace gen, so
/// every limb stays `< 2^30`). A malicious prover that writes a wrapped limb
/// cannot produce a consistent 30-bit decomposition; the AIR then rejects.
pub(crate) fn fill_balance_limb_bits(row: &mut [BabyBear], new_balance: u64) {
    let lo = (new_balance & 0x3FFF_FFFF) as u32; // low 30 bits
    let hi = new_balance >> 30; // remaining bits
    debug_assert!(
        hi < (1u64 << super::BAL_LIMB_BITS),
        "balance_hi {} exceeds 2^{} — out of the in-circuit range proof",
        hi,
        super::BAL_LIMB_BITS
    );
    for i in 0..super::BAL_LIMB_BITS {
        row[AUX_BASE + aux_off::NEW_BAL_LO_BIT_BASE + i] = BabyBear::new((lo >> i) & 1);
        row[AUX_BASE + aux_off::NEW_BAL_HI_BIT_BASE + i] = BabyBear::new(((hi >> i) & 1) as u32);
    }
}

/// The ordered felt preimage of the effects hash — one domain tag per effect
/// followed by that effect's bound parameters.
///
/// Split out of `compute_effects_hash` so the NARROW legacy squeeze and the wide
/// [`compute_effects_hash_4`] squeeze absorb the **same** preimage through the
/// same sponge, rather than the wide form re-hashing the narrow form's output
/// (`finalSqueezeOnly_still_conflates` — the laundering shape this repair
/// removed; see `docs/WOUND-felt-width-boundaries-2026-07-19.md` #30).
fn effects_hash_inputs(effects: &[Effect]) -> Vec<BabyBear> {
    let mut hasher_inputs = Vec::new();
    for effect in effects {
        match effect {
            Effect::NoOp => {
                hasher_inputs.push(BabyBear::ZERO);
            }
            Effect::Transfer { amount, direction } => {
                hasher_inputs.push(BabyBear::ONE);
                let (lo, hi) = split_u64(*amount);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
                hasher_inputs.push(BabyBear::new(*direction));
            }
            Effect::SetField { field_idx, value } => {
                hasher_inputs.push(BabyBear::new(2));
                hasher_inputs.push(BabyBear::new(*field_idx));
                hasher_inputs.push(*value);
            }
            Effect::GrantCapability { cap_entry, phase_b } => {
                hasher_inputs.push(BabyBear::new(3));
                // 32-byte widening: absorb all 8 limbs (~256-bit binding).
                hasher_inputs.extend_from_slice(cap_entry);
                // Phase B2: a witnessed granter-side delegation row absorbs its
                // direction felt + the held slot_hash, so the public encoding
                // distinguishes the delegation row from a recipient install and
                // commits to WHICH held slot the membership-open authenticates.
                // Legacy (None) rows absorb nothing extra — byte-identical to
                // the pre-B2 encoding.
                if let Some(w) = phase_b {
                    hasher_inputs.push(BabyBear::ONE);
                    hasher_inputs.push(w.held.slot_hash);
                }
            }
            Effect::RevokeCapability { slot_hash, .. } => {
                hasher_inputs.push(BabyBear::new(24));
                hasher_inputs.extend_from_slice(slot_hash);
            }
            Effect::EmitEvent {
                topic_hash,
                payload_hash,
            } => {
                hasher_inputs.push(BabyBear::new(25));
                hasher_inputs.extend_from_slice(topic_hash);
                hasher_inputs.extend_from_slice(payload_hash);
            }
            Effect::SetPermissions { permissions_hash } => {
                hasher_inputs.push(BabyBear::new(26));
                hasher_inputs.extend_from_slice(permissions_hash);
            }
            Effect::SetVerificationKey { vk_hash } => {
                hasher_inputs.push(BabyBear::new(27));
                hasher_inputs.extend_from_slice(vk_hash);
            }

            Effect::RefreshDelegation {
                child_hash,
                snapshot_value,
            } => {
                hasher_inputs.push(BabyBear::new(29));
                // 32-byte widening: absorb all 8 limbs of the refreshed child
                // key AND all 8 of the new snapshot commitment, so the public
                // encoding binds WHICH delegation was re-armed and to WHAT value
                // (no reflexive ambiguity — a forged snapshot/child changes the hash).
                hasher_inputs.extend_from_slice(child_hash);
                hasher_inputs.extend_from_slice(snapshot_value);
            }
            Effect::IncrementNonce => {
                hasher_inputs.push(BabyBear::new(53));
            }
            Effect::RevokeDelegation { child_hash } => {
                hasher_inputs.push(BabyBear::new(30));
                hasher_inputs.extend_from_slice(child_hash);
            }
            Effect::CreateCell { create_hash } => {
                hasher_inputs.push(BabyBear::new(31));
                hasher_inputs.extend_from_slice(create_hash);
            }
            Effect::SpawnWithDelegation { spawn_hash } => {
                hasher_inputs.push(BabyBear::new(32));
                hasher_inputs.extend_from_slice(spawn_hash);
            }

            Effect::ExerciseViaCapability { exercise_hash } => {
                hasher_inputs.push(BabyBear::new(34));
                hasher_inputs.extend_from_slice(exercise_hash);
            }
            Effect::Introduce { intro_hash } => {
                hasher_inputs.push(BabyBear::new(35));
                hasher_inputs.extend_from_slice(intro_hash);
            }
            Effect::PipelinedSend { send_hash } => {
                hasher_inputs.push(BabyBear::new(36));
                hasher_inputs.extend_from_slice(send_hash);
            }

            Effect::BridgeMint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                hasher_inputs.push(BabyBear::new(40));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }

            Effect::Mint {
                value_lo,
                mint_hash,
                value_full,
            } => {
                // SUPPLY-MODEL.md Stage 2b: the dedicated supply-mint binds under
                // its OWN domain tag (`sel::MINT = 14`), distinct from BridgeMint's
                // 40, so the two mints commit to disjoint effects-hash classes — a
                // supply-mint can never collide with / be replayed as a bridge-mint.
                hasher_inputs.push(BabyBear::new(14));
                hasher_inputs.push(*value_lo);
                hasher_inputs.push(*mint_hash);
                let limbs = u64_to_4_limbs_16(*value_full);
                hasher_inputs.extend_from_slice(&limbs);
            }

            Effect::NoteSpend { nullifier, value } => {
                hasher_inputs.push(BabyBear::new(4));
                hasher_inputs.push(*nullifier);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }
            Effect::NoteCreate { commitment, value } => {
                hasher_inputs.push(BabyBear::new(5));
                hasher_inputs.push(*commitment);
                let (lo, hi) = split_u64(*value);
                hasher_inputs.push(lo);
                hasher_inputs.push(hi);
            }

            Effect::Custom {
                program_vk_hash,
                proof_commitment,
            } => {
                hasher_inputs.push(BabyBear::new(8));
                hasher_inputs.extend_from_slice(program_vk_hash);
                hasher_inputs.extend_from_slice(proof_commitment);
            }

            Effect::MakeSovereign => {
                hasher_inputs.push(BabyBear::new(12));
            }
            Effect::CreateCellFromFactory {
                factory_vk,
                child_vk_derived,
            } => {
                hasher_inputs.push(BabyBear::new(13));
                hasher_inputs.push(*factory_vk);
                hasher_inputs.push(*child_vk_derived);
            }

            // ---- Near-miss aliasing closure (#100 follow-up) ----
            // Domain-tag bytes are reserved in the selector index space
            // (46, 47, 48 — matching `sel::BURN`, `sel::CELL_DESTROY`,
            // `sel::ATTENUATE_CAPABILITY`).
            Effect::Burn {
                target_hash,
                amount_lo,
                amount_full,
            } => {
                hasher_inputs.push(BabyBear::new(46));
                // 32-byte widening (felt-width #25): absorb all 8 limbs of the
                // burn target, the shape `CellDestroy` twenty lines below already
                // used. The prior single `push` bound ~31 bits of the target cell.
                hasher_inputs.extend_from_slice(target_hash);
                hasher_inputs.push(*amount_lo);
                // Bind the full u64 via 4×16-bit limbs (mirrors
                // BridgeMint / BridgeLock / CreateEscrow) so the proof
                // commits to the entire amount, not just the low 30 bits.
                let limbs = u64_to_4_limbs_16(*amount_full);
                hasher_inputs.extend_from_slice(&limbs);
            }
            Effect::CellDestroy {
                target_hash,
                death_certificate_hash,
            } => {
                hasher_inputs.push(BabyBear::new(47));
                hasher_inputs.extend_from_slice(target_hash);
                hasher_inputs.extend_from_slice(death_certificate_hash);
            }
            Effect::AttenuateCapability {
                cap_slot_hash,
                narrower_commitment,
                // Phase-B witness is NOT part of the public effects_hash binding;
                // the two 8-limb commitments are the canonical commitment.
                phase_b: _,
            } => {
                hasher_inputs.push(BabyBear::new(48));
                hasher_inputs.extend_from_slice(cap_slot_hash);
                hasher_inputs.extend_from_slice(narrower_commitment);
            }
            // ---- AIR-impl lane #119: CellSeal / CellUnseal / ReceiptArchive / Refusal ----
            // Domain tags 49–52 match `sel::CELL_SEAL` through `sel::REFUSAL`.
            Effect::CellSeal {
                target,
                reason_hash,
            } => {
                hasher_inputs.push(BabyBear::new(49));
                hasher_inputs.extend_from_slice(target);
                hasher_inputs.extend_from_slice(reason_hash);
            }
            Effect::CellUnseal { target } => {
                hasher_inputs.push(BabyBear::new(50));
                hasher_inputs.extend_from_slice(target);
            }
            Effect::ReceiptArchive {
                target,
                archive_end_height,
                terminal_receipt_hash,
            } => {
                hasher_inputs.push(BabyBear::new(51));
                hasher_inputs.extend_from_slice(target);
                // archive_end_height is a scalar height, not a 32-byte hash.
                hasher_inputs.push(*archive_end_height);
                hasher_inputs.extend_from_slice(terminal_receipt_hash);
            }
            Effect::Refusal {
                target,
                reason_hash,
            } => {
                hasher_inputs.push(BabyBear::new(52));
                hasher_inputs.extend_from_slice(target);
                hasher_inputs.extend_from_slice(reason_hash);
            }
        }
    }
    hasher_inputs
}

/// Compute the NARROW legacy effects hash for a sequence of effects.
/// Returns (lo, hi) BabyBear elements.
///
/// ⚠ **This is a ~31-bit digest** — `hash_many` squeezes ONE rate felt, and the
/// "hi" element is `hash_2_to_1(h, 0xEFFEC7)`, a function of that same felt, so
/// the pair's image has at most `p ≈ 2^31` points. Its collision resistance is
/// ~2^15.5 (birthday), NOT the width the two felts suggest. Use
/// [`compute_effects_hash_4`] at any boundary that binds; this form is kept for
/// the legacy `PI[EFFECTS_HASH_LO]` alias and for callers that only need the
/// historical felt. `sdk::full_turn_proof::effect_action_binding` still binds
/// position 0 alone — the residual named in
/// `docs/WOUND-felt-width-boundaries-2026-07-19.md` #31.
pub fn compute_effects_hash(effects: &[Effect]) -> (BabyBear, BabyBear) {
    let h = hash_many(&effects_hash_inputs(effects));
    // Split into two elements for wider coverage (legacy 2-felt form).
    let h2 = hash_2_to_1(h, BabyBear::new(0xEFFEC7));
    (h, h2)
}

/// The 4-felt effects hash carried at `PI[EFFECTS_HASH_BASE..+4]` — FOUR GENUINE
/// SPONGE SQUEEZES over the effect preimage.
///
/// Each lane is a rate-position squeeze of the Poseidon2 sponge that absorbed
/// [`effects_hash_inputs`], so every lane depends on the ENTIRE effect list and
/// the four together give ~124-bit collision resistance — matching the FRI floor
/// and the `Faithful8` state commitment beside them in the same PI vector.
///
/// # What this replaced, and why the old form's claimed width was FALSE
///
/// Until the felt-width #30 repair this was
/// `[h, hash_4_to_1([h,1,0,0]), hash_4_to_1([h,2,0,0]), hash_4_to_1([h,3,0,0])]`
/// with `h = compute_effects_hash(effects).0` — a single ~31-bit felt. All four
/// lanes were FUNCTIONS OF THAT ONE FELT, so the tuple's image had at most
/// `p ≈ 2^31` points and two effect lists agreeing on `h` produced a BYTE-IDENTICAL
/// 4-felt PI. The doc-comment claimed "~124-bit collision resistance"; the true
/// figure was ~2^15.5 birthday. That is exactly `finalSqueezeOnly_still_conflates`
/// (`metatheory/Dregg2/Cell/InterfaceIdWidth.lean`) with the sign flipped —
/// widening the FINAL SQUEEZE of a one-felt chain launders nothing, and here the
/// chain's own output *was* the one felt. Every "32-byte widening: absorb all 8
/// limbs (~256-bit binding)" arm inside `effects_hash_inputs` was therefore
/// cosmetic AT THIS BOUNDARY until this repair; they are load-bearing now.
///
/// `hash_many_8`'s own contract states the law this obeys: it "must not be bolted
/// only onto the final squeeze of a one-felt chain" — so it absorbs the REAL
/// preimage, not `h`.
///
/// Position 0 is NO LONGER guaranteed to equal `compute_effects_hash(effects).0`
/// (`hash_many_8` squeezes the same absorb state, but the equality is explicitly
/// not part of that primitive's contract — do not rely on it).
pub fn compute_effects_hash_4(effects: &[Effect]) -> [BabyBear; 4] {
    let wide = hash_many_8(&effects_hash_inputs(effects));
    [wide[0], wide[1], wide[2], wide[3]]
}

#[cfg(test)]
mod field_limbs8_tests {
    use super::*;

    /// `field_from_u64` twin (BE bytes 24..32) — the kernel numeric encoding
    /// (`cell/src/program/eval.rs:2741`), reproduced here so the derivation is
    /// pinned inside the circuit crate without a dep cycle.
    fn field_from_u64(v: u64) -> [u8; 32] {
        let mut f = [0u8; 32];
        f[24..32].copy_from_slice(&v.to_be_bytes());
        f
    }

    /// THE VALVE FACT: lane 0 of a kernel-numeric field IS the raw value
    /// (v < 2^31) — the escrow/discharge/vault weld constants survive verbatim.
    #[test]
    fn lane0_is_the_raw_value_for_kernel_numeric_fields() {
        for v in [0u64, 1, 2, 1000, 1_000_000, (1 << 31) - 1] {
            let lanes = field_limbs8(&field_from_u64(v));
            assert_eq!(lanes[0], BabyBear::new(v as u32), "lane0 == v for v={v}");
            assert_eq!(lanes[1], BabyBear::ZERO, "hi32 zero for v={v} < 2^32");
            for k in 2..8 {
                assert_eq!(lanes[k], BabyBear::ZERO, "bytes 0..24 zero for v={v}");
            }
        }
        // hi32 rides lane 1 (the staged capacity descriptors' named hi-pin slot).
        let v = (7u64 << 32) | 42;
        let lanes = field_limbs8(&field_from_u64(v));
        assert_eq!(lanes[0], BabyBear::new(42));
        assert_eq!(lanes[1], BabyBear::new(7));
    }

    /// The escrow weld constants (`Deposited = 1` / `Consumed = 2`) match the
    /// lane-0 projection of the spec-conforming BE status mirror.
    #[test]
    fn escrow_weld_constants_survive_lane0() {
        assert_eq!(field_limbs8(&field_from_u64(1))[0], BabyBear::new(1));
        assert_eq!(field_limbs8(&field_from_u64(2))[0], BabyBear::new(2));
        // Non-vacuous: Empty (0) is distinct from Deposited (1).
        assert_ne!(
            field_limbs8(&field_from_u64(0))[0],
            field_limbs8(&field_from_u64(1))[0]
        );
    }

    /// The refuted route, pinned: plain `bytes32_to_8_limbs` has NO lane
    /// carrying the numeric value (lane 0 is identically zero; lane 7 is
    /// byte-swapped) — the reason the fields octet takes its own grouping.
    #[test]
    fn plain_le_lanes_do_not_carry_the_numeric_value() {
        let one = field_from_u64(1);
        let plain = bytes32_to_8_limbs(&one);
        assert_eq!(plain[0], BabyBear::ZERO, "plain lane0 == 0 for BE numerics");
        assert_eq!(
            plain[7],
            BabyBear::new(0x0100_0000),
            "plain lane7 is the byte-swapped lo32"
        );
        // And the deployed Horner fold is NOT the raw value either.
        assert_ne!(fold_bytes32_to_bb(&one), BabyBear::new(1));
    }

    /// Faithfulness: all 32 bytes are bound — flipping any single byte moves
    /// exactly one lane (each byte belongs to exactly one 4-byte lane chunk).
    #[test]
    fn every_byte_moves_a_lane() {
        let base = [0u8; 32];
        let lanes0 = field_limbs8(&base);
        for i in 0..32 {
            let mut b = base;
            b[i] = 0x5A;
            let lanes = field_limbs8(&b);
            let moved = (0..8).filter(|&k| lanes[k] != lanes0[k]).count();
            assert_eq!(moved, 1, "byte {i} must move exactly one lane");
        }
    }

    /// Lane additivity on the welded limb: `after = before + delta` holds on
    /// lane 0 for the honest numeric domain (no lo32 carry) — the discharge
    /// cursor/total additive gates and the vault delta decompositions work.
    #[test]
    fn lane0_addition_matches_u64_addition_in_the_honest_domain() {
        for (before, delta) in [(1000u64, 100u64), (0, 1), (12345, 54321)] {
            let b = field_limbs8(&field_from_u64(before))[0];
            let a = field_limbs8(&field_from_u64(before + delta))[0];
            assert_eq!(a, b + BabyBear::new(delta as u32));
        }
    }
}
