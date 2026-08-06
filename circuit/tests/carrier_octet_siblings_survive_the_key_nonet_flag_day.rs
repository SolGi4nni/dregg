//! # The OTHER two carrier octets — what the key-nonet flag day did NOT close, MEASURED.
//!
//! The 2026-08-01/08-02 flag days closed the **owner key**: the base-`2^29` nonet reaches the
//! signed anchor (`B_PUBKEY_NINTH_LANE = 186`, an absorbed pre-limb), the canonicity envelope is
//! emitted and on the wire, and `A` / `−A` are exhibited colliding then separating
//! (`key_nonet_anchor_old_admits_new_rejects.rs`,
//! `key_nonet_canonicity_envelope_old_admits_new_rejects.rs`).
//!
//! The `187`-limb grow bought **three** ninth lanes — `ROTATED_OCTET_NINTH_LANES = [184, 185, 186]`
//! — and **one is used**. This file measures the other two rather than reading a doc about them.
//!
//! ## What survives, in one paragraph
//!
//! `child_vk` (octet `89..=96` ‖ ninth lane `184`) and `contract_hash` (`97..=104` ‖ `185`) are
//! still written by `Faithful8::from_bytes32` = `bytes32_to_8_limbs`: eight 4-byte little-endian
//! chunks reduced `mod p`. `2p = 4026531842 < 2^32`, so every chunk value has at least one other
//! `u32` representative and **every committed octet is shared by between `2^8` and `3^8` distinct
//! 32-byte values**. Columns 184 and 185 are emitted, tiled, `#guard`-ed and folded by
//! `wireCommitR`, and no producer writes them: they carry `BabyBear::ZERO` on every turn, including
//! turns that DO carry the material.
//!
//! ## ⚑⚑ A CORRECTION TO THE SEVERITY THIS FILE WAS WRITTEN UNDER — measured here, not relayed
//!
//! `docs/FAITHFUL-COMMITMENT-LAW.md` states the surviving wound as *"`O(1)` … and it is `O(1)` for
//! the attacker's own chosen bytes, which is what these two carriers hold."* **The second clause is
//! false, and the difference is not cosmetic.** Measured at the source:
//!
//! * `child_vk` is `ChildVkStrategy::derive_child_vk` = `blake3_derive_key("dregg-derived-child-vk-v1",
//!   factory_vk ‖ param_hash)` (`cell/src/factory.rs`). It is a **BLAKE3 image**, not a free field.
//! * `contract_hash` is `HpresProof::Attested{contract_hash}`, a `[u8; 32]` the SDK caller passes
//!   verbatim (`sdk/src/hatchery_mint.rs::attest_hpres`) — and `circuit-prove/src/hatchery_leaf_adapter.rs`
//!   names its own residual: *"anchoring `contract_hash` to a VERIFYING contract proof in-circuit"*
//!   is **not done**. So that value is already unconstrained, and an alias buys an attacker nothing
//!   there that choosing the value outright does not already buy.
//!
//! So the sibling is `O(1)` **in the byte domain** — [`sibling_by_adding_p`] constructs one with a
//! single addition, no search, and this file exhibits it at the deployed producer — but turning it
//! into a forgery at `child_vk` requires landing a *semantically valid* VK inside the alias set,
//! i.e. a second preimage on BLAKE3 aimed at a target set of size ~`2^8.74`: about `2^247`, not
//! `O(1)`. ⚠ **Say that bound, not the flattering one.** This is NOT the owner-key situation, where
//! `A` and `−A` were both valid keys, the attacker held the private half of the negation, and the
//! two packed identically for free. That is why the owner key was the correct first repair and why
//! it is the one that is done.
//!
//! **What IS true today, and is enough to justify the cutover:** the committed carrier does not
//! *determine* the 32 bytes — it determines a set of size `≥ 2^8` — so no statement of the form
//! "the committed octet determines the installed child VK" is available, and the eventual
//! `keyCanon9_determines_…`-shaped capstone cannot be stated for these two carriers at all. The
//! ambiguity is also PI-published (`factoryVmDescriptor2R24`, `child_vk8 → PI[47..54]`,
//! `contract_hash8 → PI[55..62]`), so it reaches a light client that has no ledger to disambiguate
//! against.
//!
//! ## ⚠ This file is a TRIPWIRE and is meant to go RED
//!
//! [`the_two_ninth_lanes_carry_zero_on_every_turn`] asserts columns 184/185 are zero. The day the
//! carrier cutover lands — producers on `Faithful9::from_key_lanes9` over
//! `CHILD_VK_NONET_LANE_COL` / `CONTRACT_HASH_NONET_LANE_COL` — that assertion FAILS, and the
//! failure is the flag day working. Flip it then; do not relax it before then.
//!
//! ## ⚠ Resolution, said out loud
//!
//! These run the deployed PRODUCER (`dregg_cell::commitment::compute_rotated_pre_limbs`) and the
//! deployed FOLD (`dregg_turn::rotation_witness::wire_commit`). They do **not** run a STARK.

use dregg_cell::Cell;
use dregg_cell::commitment::{
    RotationCarrierMaterial, V9RotationContext, compute_rotated_pre_limbs,
};
use dregg_cell::factory::ChildVkStrategy;
use dregg_circuit::effect_vm::layout_generated::{
    B_CHILD_VK_NINTH_LANE, B_CHILD_VK_OCTET, B_CONTRACT_HASH_NINTH_LANE, B_CONTRACT_HASH_OCTET,
    NUM_PRE_LIMBS, ROTATED_OCTET_BASES, ROTATED_OCTET_NINTH_LANES,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::{Faithful8, Faithful9};

/// A REAL derived child VK — a BLAKE3 image, exactly as `apply.rs`'s `effective_vk` produces it.
/// Using a hand-picked `[0xAB; 32]` here would make the alias look freer than it is.
fn a_real_derived_child_vk() -> [u8; 32] {
    ChildVkStrategy::derive_child_vk(&[0x11; 32], &[0x22; 32])
}

/// **THE SIBLING, CONSTRUCTED BY ONE ADDITION.** `bytes32_to_8_limbs` reduces each 4-byte
/// little-endian window `mod p`, so a window whose value `v` satisfies `v + p < 2^32` has a second
/// `u32` representative `v + p` that reduces to the same limb. No search, no grind: scan the eight
/// windows and take the first that admits the bump.
///
/// Returns `None` only if all eight windows are at or above `2^32 − p` — for a BLAKE3 output that
/// is a `(1 − 0.531)^8 ≈ 2.4·10^-3` event, and the fixed input above is not one of them.
fn sibling_by_adding_p(b: &[u8; 32]) -> Option<([u8; 32], usize)> {
    let headroom = (1u64 << 32) - u64::from(BABYBEAR_P);
    (0..8).find_map(|w| {
        let off = w * 4;
        let v = u32::from_le_bytes([b[off], b[off + 1], b[off + 2], b[off + 3]]);
        (u64::from(v) < headroom).then(|| {
            let mut out = *b;
            out[off..off + 4].copy_from_slice(&(v + BABYBEAR_P).to_le_bytes());
            (out, w)
        })
    })
}

/// The exact number of byte-distinct 32-byte values sharing this value's committed octet: the
/// product over the eight windows of that limb's `u32` representative count (2, or 3 when the
/// residue is below `2^32 − 2p`). MEASURED per value, never quoted from a doc.
fn alias_set_size(b: &[u8; 32]) -> u64 {
    let p = u64::from(BABYBEAR_P);
    (0..8)
        .map(|w| {
            let off = w * 4;
            let v = u64::from(u32::from_le_bytes([
                b[off],
                b[off + 1],
                b[off + 2],
                b[off + 3],
            ]));
            let r = v % p;
            // representatives of `r` inside [0, 2^32): r, r+p, r+2p, … while still below 2^32
            (0..)
                .take_while(|k| r + (*k as u64) * p < (1u64 << 32))
                .count() as u64
        })
        .product()
}

fn fixed_context(material: RotationCarrierMaterial) -> V9RotationContext {
    V9RotationContext {
        cells_root: dregg_circuit::heap_root::compute_canonical_heap_root_8_entries(&[(
            (BabyBear::ZERO, BabyBear::new(0x5678)),
            BabyBear::ONE,
        )]),
        nullifier_root: dregg_circuit::heap_root::empty_heap_root_8(),
        commitments_root: dregg_circuit::heap_root::empty_heap_root_8(),
        revoked_root: dregg_circuit::heap_root::empty_heap_root_8(),
        iroot: BabyBear::new(0x1234),
        material,
    }
}

fn a_cell() -> Cell {
    Cell::with_balance([7u8; 32], [0u8; 32], 100_000)
}

/// The committed limb vector for a turn carrying exactly this carrier material.
fn committed_with(material: RotationCarrierMaterial) -> Vec<BabyBear> {
    let pre = compute_rotated_pre_limbs(&a_cell(), &fixed_context(material));
    assert_eq!(pre.len(), NUM_PRE_LIMBS);
    pre
}

/// ⚑ **THE 187-GROW BOUGHT THREE NINTH LANES AND ONE IS USED** — measured at the deployed producer,
/// on a turn that DOES carry both carriers' material. Columns 184 and 185 are absorbed pre-limbs
/// (`wireCommitR` folds `[0, 187)`), so what the anchor absorbs there is two constant zeros.
///
/// ⚠ THIS TEST IS A TRIPWIRE. It FAILS the day the carrier cutover lands, and that failure is the
/// flag day working. See the module header.
#[test]
fn the_two_ninth_lanes_carry_zero_on_every_turn() {
    // the ninth lanes are positionally parallel to the octet bases — the layout's own table, not a
    // stride, and not three loose constants.
    assert_eq!(
        ROTATED_OCTET_BASES,
        [B_CHILD_VK_OCTET, B_CONTRACT_HASH_OCTET, 105],
        "the carrier octet base table must be the one this file reads"
    );
    assert_eq!(
        ROTATED_OCTET_NINTH_LANES,
        [B_CHILD_VK_NINTH_LANE, B_CONTRACT_HASH_NINTH_LANE, 186],
        "…and the ninth-lane table likewise: lane 8 of octet `i` is \
         ROTATED_OCTET_NINTH_LANES[i], never ROTATED_OCTET_BASES[i] + 8"
    );
    // all three are absorbed pre-limbs, so `state_commit` folds whatever they hold — including a
    // zero nobody wrote.
    for &c in ROTATED_OCTET_NINTH_LANES.iter() {
        assert!(
            c < NUM_PRE_LIMBS,
            "column {c} must be an ABSORBED pre-limb or wireCommitR never folds it"
        );
    }

    let material = RotationCarrierMaterial {
        child_vk: Some(a_real_derived_child_vk()),
        contract_hash: Some([0x5A; 32]),
    };
    let pre = committed_with(material);

    // The octets ARE filled — so this is not "the material was absent".
    assert!(
        (0..8).any(|k| pre[B_CHILD_VK_OCTET + k] != BabyBear::ZERO),
        "precondition: the child_vk octet must actually carry material, or the ninth-lane \
         assertion below is vacuous"
    );
    assert!(
        (0..8).any(|k| pre[B_CONTRACT_HASH_OCTET + k] != BabyBear::ZERO),
        "precondition: the contract_hash octet must actually carry material"
    );

    // …and the ninth lanes are not.
    assert_eq!(
        pre[B_CHILD_VK_NINTH_LANE],
        BabyBear::ZERO,
        "⚑ column {B_CHILD_VK_NINTH_LANE} is emitted, tiled and ABSORBED, and no producer writes \
         it. If this now fails, the carrier cutover has landed — flip this tripwire to assert the \
         lane instead."
    );
    assert_eq!(
        pre[B_CONTRACT_HASH_NINTH_LANE],
        BabyBear::ZERO,
        "⚑ column {B_CONTRACT_HASH_NINTH_LANE}, same. The owner key's lane 186 is written; these \
         two are not."
    );

    // The owner key's ninth lane, by contrast, IS written — so the difference is the producer, not
    // the geometry. This is what makes "one of three is used" a measurement.
    assert_ne!(
        pre[186],
        BabyBear::ZERO,
        "the owner-key ninth lane must be written (key_nonet_anchor_old_admits_new_rejects.rs); if \
         it is zero, the 08-02 cutover has regressed"
    );
}

/// ⚑ **OLD ADMITS, at the deployed producer and the deployed fold** — two distinct 32-byte
/// `child_vk` values whose committed octet is BYTE-IDENTICAL, the sibling built by ONE addition.
///
/// ⚠ Read the module header for what this does and does not license. The construction is free; the
/// *exploitation* is not, because the value is a BLAKE3 image.
#[test]
fn the_deployed_carrier_encoder_admits_a_sibling_at_cost_zero() {
    let vk = a_real_derived_child_vk();
    let (vk_sibling, window) = sibling_by_adding_p(&vk)
        .expect("a BLAKE3 output with no bumpable window is a 2.4e-3 event");
    assert_ne!(
        vk, vk_sibling,
        "the pair must be two distinct 32-byte values"
    );
    // …and they differ ONLY inside the bumped window. Anything outside it would mean the sibling
    // was built by something other than the single `+p`, which is the whole cost claim.
    let differing: Vec<usize> = (0..32).filter(|&i| vk[i] != vk_sibling[i]).collect();
    assert!(
        !differing.is_empty() && differing.iter().all(|&i| i / 4 == window),
        "the sibling must differ from the original only inside 4-byte window {window}; measured \
         differing byte indices {differing:?}"
    );

    // ── the ENCODER identifies them. ─────────────────────────────────────────────────────────
    assert_eq!(
        Faithful8::from_bytes32(&vk).limbs(),
        Faithful8::from_bytes32(&vk_sibling).limbs(),
        "⚑ THE WOUND: `bytes32_to_8_limbs` maps two distinct 32-byte values to the same octet, \
         constructed by adding p to one 4-byte window. No search."
    );

    // ── and so does the deployed PRODUCER, at the committed columns. ──────────────────────────
    let pre = committed_with(RotationCarrierMaterial {
        child_vk: Some(vk),
        contract_hash: None,
    });
    let pre_sib = committed_with(RotationCarrierMaterial {
        child_vk: Some(vk_sibling),
        contract_hash: None,
    });
    let carrier = |v: &[BabyBear]| -> Vec<BabyBear> {
        (0..8)
            .map(|k| v[B_CHILD_VK_OCTET + k])
            .chain(std::iter::once(v[B_CHILD_VK_NINTH_LANE]))
            .collect()
    };
    assert_eq!(
        carrier(&pre),
        carrier(&pre_sib),
        "the child_vk carrier's NINE columns are identical for the pair — the eight because the \
         encoder identifies them, the ninth because nobody writes it"
    );
    assert_eq!(
        pre, pre_sib,
        "and the WHOLE committed vector is identical: unlike the owner key, `child_vk` reaches the \
         anchor by exactly ONE path, so there is no authority-digest leg to separate the pair"
    );

    // ── and at the DEPLOYED FOLD. ─────────────────────────────────────────────────────────────
    let iroot = BabyBear::new(0x1234);
    assert_eq!(
        dregg_turn::rotation_witness::wire_commit(&pre, iroot),
        dregg_turn::rotation_witness::wire_commit(&pre_sib, iroot),
        "OLD ADMITS at the anchor: both child VKs publish ONE state_commit, and the PI face \
         (child_vk8 → PI[47..54]) publishes one octet for both"
    );
}

/// ⚑ **ANTI-VACUITY: the replacement SEPARATES the same pair AND round-trips the 32 bytes.**
/// "The octets differ" would prove nothing — a scrambling change passes that. This decodes the
/// nine committed lanes back to the exact input bytes, which only an injection can do.
#[test]
fn the_nine_lane_replacement_separates_the_pair_and_round_trips() {
    let vk = a_real_derived_child_vk();
    let (vk_sibling, _) = sibling_by_adding_p(&vk).expect("bumpable window");

    let nonet = Faithful9::from_key_lanes9(&vk);
    let nonet_sib = Faithful9::from_key_lanes9(&vk_sibling);

    assert_ne!(
        nonet.lanes(),
        nonet_sib.lanes(),
        "NEW REJECTS: the base-2^29 nonet must separate a pair the mod-p octet identifies"
    );

    // THE ROUND TRIP — the anti-vacuity leg. Both values are recovered byte-for-byte from their
    // nine lanes, so the encoding determines the input rather than merely differing on it.
    assert_eq!(
        nonet.to_key_bytes(),
        vk,
        "the 32 bytes must come back out of the nine lanes"
    );
    assert_eq!(
        nonet_sib.to_key_bytes(),
        vk_sibling,
        "…and so must the sibling's"
    );

    // The eight-lane octet cannot do this at all: it maps both to one vector, so no decoder exists.
    assert_eq!(
        Faithful8::from_bytes32(&vk).limbs(),
        Faithful8::from_bytes32(&vk_sibling).limbs(),
        "the contrast is the point: the retired encoder has no left inverse on this pair"
    );
}

/// **THE ALIAS SET SIZE, MEASURED PER VALUE.** The number to quote when pricing this wound is the
/// one this computes, not a remembered `53.1%`. Every 32-byte value has between `2^8 = 256` and
/// `3^8 = 6561` byte-distinct siblings; the expectation is `(2^32/p)^8 = 2^8.74`.
///
/// ⚠ And the number this does NOT license: `2^8.74` is the size of the target set, not the cost of
/// hitting it with a *valid* VK. That cost is a BLAKE3 second preimage aimed at the set, ~`2^247`.
#[test]
fn the_alias_set_size_is_measured_not_quoted() {
    let vk = a_real_derived_child_vk();
    let n = alias_set_size(&vk);
    assert!(
        (256..=6561).contains(&n),
        "every committed octet is shared by between 2^8 and 3^8 byte-distinct values; measured {n}"
    );
    // …and it is never 1. That is the whole claim: the committed carrier does not DETERMINE the
    // 32 bytes, so no `determines_the_child_vk` capstone is available for this carrier.
    assert!(
        n > 1,
        "if this ever reads 1 the encoder became injective and this file's premise is gone"
    );

    // The sibling this file exhibits is a member of that set, which is what ties the constructive
    // half to the counting half.
    let (sib, _) = sibling_by_adding_p(&vk).expect("bumpable window");
    assert_eq!(
        Faithful8::from_bytes32(&vk).limbs(),
        Faithful8::from_bytes32(&sib).limbs()
    );
    assert_eq!(
        alias_set_size(&sib),
        n,
        "siblings share an octet, so they share an alias set"
    );
}
