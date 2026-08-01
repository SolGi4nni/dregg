//! **THE LIVE DOUBLE-SPEND GATE'S SORT KEY AND IMT POINTER ARE ONE FELT EACH INSIDE A 247-BIT
//! TREE — MEASURED, NOT DESCRIBED.**
//!
//! `Ir2Air::MapAbsent` (`circuit/src/descriptor_ir2.rs`, reached through
//! `noteSpendVmDescriptor2R24`'s `nullifierFreshOp`) is the in-circuit freshness gate for a note
//! spend: an Indexed-Merkle-Tree pointer bracket `lo_addr < key < lo_next` over ONE committed low
//! leaf. Its roots, leaf digests and node folds are all `node8` — eight BabyBear lanes,
//! 247.26 bits. But three of its columns are **one felt each**:
//!
//! ```text
//! const MA_KEY:     usize = MA_ROOT + CHIP_OUT_LANES;  // col  8 — the sort key
//! const MA_LO_ADDR: usize = MA_IS_REAL + 1;            // col 18 — the low leaf's address
//! const MA_LO_NEXT: usize = MA_LO_VALUE + 1;           // col 20 — the IMT pointer (hi bracket)
//! ```
//!
//! (`descriptor_ir2.rs:2044`, `:2047`, `:2049`. `MA_NEW_ROOT = MA_KEY + 1` and
//! `MA_LO_LEAF = MA_LO_NEXT + 1` are the arithmetic PROOF that each is a single column: the next
//! field starts one column later, not eight. `MA_LO_VALUE` is also one felt but it is a stored
//! value, not a key — it is not part of this finding.)
//!
//! Those columns are private, so this file pins the SAME one-felt-ness through the public surface
//! that produces them — `MapOpSpec.key : LeanExpr` (ONE expression beside `root : Vec<LeanExpr>`
//! of eight) and `HeapLeaf { addr: BabyBear, next_addr: BabyBear }` with
//! `HEAP_LEAF_ARITY = 3` — and then MEASURES what the width costs at the deployed prover.
//!
//! # The two bounds, derived (§2)
//!
//! `p = 15·2^27 + 1 = 2013265921`, `log2 p = 30.9069`.
//!
//! | | the three retired columns (1 felt) | `node8`, the tree around them (8 felts) |
//! |---|---|---|
//! | codomain | 30.9069 bits | 247.2551 bits |
//! | **collision — the binding figure** | **2^15.45** | **2^123.63** |
//! | second-preimage | 2^30.91 | 2^247.26 |
//!
//! ⚑ The COLLISION bound binds. An attacker who contributes a note chooses **both** sides of the
//! pair, so the birthday figure is the one that governs; quoting `2^30.91` here would be quoting
//! the flattering number of a pair.
//!
//! # ⚑ WHAT THE NARROW KEY ACTUALLY BUYS — AND WHAT IT DOES NOT (§4)
//!
//! This file's headline was going to be "a nullifier that was already spent passing as fresh."
//! **It is not constructible at the deployed all-narrow width, and this file says so with a
//! construction instead of an opinion.** The nullifier tree is keyed BY the fold and bracketed ON
//! the fold — sort order and compared quantity are the same projection — so a fold collision can
//! only make the gate REFUSE a true absence, never ADMIT a false one. That is exactly what this
//! repo's own Lean already proves: `MapOpWideKey.narrow_only_over_revokes` ("a projection is a
//! function ⇒ the same-fold-keyed `.absent` op can only OVER-revoke ⇒ soundness NONE") paired with
//! `narrowAbsent_unprovable` ("availability HIGH, permanent"), packaged as `dosDelta_site20`.
//!
//! What the collision DOES buy, and it is not small:
//! [`spent_note_freezes_a_stranger_note_forever`] finds a real collision at the deployed parameter
//! and shows a nullifier that was **never spent** being certified **already spent** by the
//! deployed prover, permanently and deterministically. The note is not stolen; it is destroyed.
//! Cost: one offline birthday search plus one ordinary note spend.
//!
//! # ⚑ AND THE SOUNDNESS BREAK IS THE HALF-WIDENED STATE (§5)
//!
//! The forgery direction — a PRESENT key certified ABSENT — appears the moment the key is widened
//! while the pointer is left narrow. `MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present`
//! proves it in Lean for EVERY hash with no collision-resistance hypothesis;
//! [`half_widening_conflates_the_pointer_and_forges_absence`] exhibits the same arithmetic here.
//! **That is why the key and the pointer must widen in one step or not at all** — a half-widened
//! intermediate is strictly worse than today's narrow gate, which is merely incomplete.
//!
//! # ⚑ THIS FILE IS A TRIPWIRE, NOT A MONUMENT — it MUST go red at the cutover
//!
//! [`spent_note_freezes_a_stranger_note_forever`] asserts that the deployed prover **refuses** a
//! genuinely fresh nullifier. That assertion pins the WOUND. When `MA_KEY`/`MA_LO_ADDR`/
//! `MA_LO_NEXT` widen and the map key becomes injective, the refusal becomes an acceptance and
//! **this test goes red**. That is the intended behaviour: the flag day has to be findable, and a
//! red here is the cutover announcing itself. Flip the assertion then — do not weaken it now.
//! The same is true of [`imt_leaf_is_arity_three_so_addr_and_pointer_are_one_felt_each`] (arity
//! 3 → 17) and [`mapop_key_is_one_expression_beside_eight_lane_roots`] (`key` becomes eight).

use dregg_circuit::descriptor_ir2::{
    CHIP_OUT_LANES, EffectVmDescriptor2, MapKind, MapOpSpec, MemBoundaryWitness, VmConstraint2,
    prove_vm_descriptor2, verify_vm_descriptor2,
};
use dregg_circuit::effect_vm::{
    bytes32_to_8_limbs, field_from_lanes9, field_limbs9, fold_bytes32_to_bb,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::heap_root::{
    CanonicalHeapTree8, HEAP_LEAF_ARITY, HEAP_TREE_DEPTH, HeapLeaf, SENTINEL_MAX,
};
use dregg_circuit::lean_descriptor_air::LeanExpr;
use std::collections::HashMap;
use std::time::Instant;

// ---------------------------------------------------------------------------------------------
// §1 — THE THREE COLUMNS ARE ONE FELT EACH, pinned through the public producer surface.
// ---------------------------------------------------------------------------------------------

/// **MA_KEY is one column.** The descriptor node that FEEDS it — `MapOpSpec` — types the eight-felt
/// root groups as `Vec<LeanExpr>` of length `CHIP_OUT_LANES` and the key as a bare `LeanExpr`.
/// That asymmetry is the wound at its source (`DescriptorIR2.lean`'s `MapOp` has
/// `root : Fin 8 → EmittedExpr` and `key : EmittedExpr`), and it is why the deployed
/// `MA_KEY = MA_ROOT + CHIP_OUT_LANES` is followed by `MA_NEW_ROOT = MA_KEY + 1`.
#[test]
fn mapop_key_is_one_expression_beside_eight_lane_roots() {
    let op = MapOpSpec {
        guard: LeanExpr::Var(17),
        root: (0..CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
        key: LeanExpr::Var(8),
        value: LeanExpr::Const(0),
        new_root: (9..9 + CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
        op: MapKind::Absent,
    };
    assert_eq!(op.root.len(), CHIP_OUT_LANES, "the pre-root is eight lanes");
    assert_eq!(
        op.new_root.len(),
        CHIP_OUT_LANES,
        "the post-root is eight lanes"
    );
    // `op.key` is a single `LeanExpr`, not a `Vec<LeanExpr>`. Reading it as one column is the
    // whole statement; the assertion below is the observable shadow of that type.
    assert!(
        matches!(op.key, LeanExpr::Var(_)),
        "the map-op key is ONE column expression while the roots either side of it are eight"
    );
}

/// **MA_LO_ADDR and MA_LO_NEXT are one column each.** The low leaf the `.absent` bracket opens is
/// `hash[addr, value, next_addr]` — arity THREE, so addr and next_addr occupy one felt apiece.
/// The wide schema this must become is arity **17** (`addr8 ‖ value ‖ next8`,
/// `HeapLeafWideEmit.wideLeafBlock_length`).
#[test]
fn imt_leaf_is_arity_three_so_addr_and_pointer_are_one_felt_each() {
    assert_eq!(
        HEAP_LEAF_ARITY, 3,
        "the deployed IMT leaf absorbs [addr, value, next_addr] — three felts, so the sort key \
         and the pointer are ONE felt each inside a node8 tree"
    );
    let leaf = HeapLeaf {
        addr: BabyBear::new(11),
        value: BabyBear::new(22),
        next_addr: BabyBear::new(33),
    };
    let pre = leaf.preimage();
    assert_eq!(pre.len(), 3);
    assert_eq!(
        [pre[0].as_u32(), pre[1].as_u32(), pre[2].as_u32()],
        [11, 22, 33],
        "one felt of address, one of value, one of pointer"
    );
    // The wide replacement, for contrast: 8 + 1 + 8.
    assert_eq!(
        bytes32_to_8_limbs(&[0u8; 32]).len() + 1 + bytes32_to_8_limbs(&[0u8; 32]).len(),
        17,
        "the Lean-authored wide schema (HeapLeafWideEmit) is arity 17"
    );
}

// ---------------------------------------------------------------------------------------------
// §2 — BOTH BOUNDS, derived from the deployed prime rather than transcribed.
// ---------------------------------------------------------------------------------------------

/// **The two collision bounds, computed from `BABYBEAR_P` itself.**
///
/// Two INDEPENDENT sources, not a constant compared against its own definition: the left-hand side
/// is computed from the deployed field modulus and the deployed lane count `CHIP_OUT_LANES`; the
/// right-hand side is the figure this repo publishes for the same construction
/// (`HORIZONLOG.md`'s August 1 table, `persist/src/lib.rs:459`).
#[test]
fn both_collision_bounds_are_derived_not_transcribed() {
    assert_eq!(BABYBEAR_P, 15 * (1 << 27) + 1, "p = 15·2^27 + 1");
    assert_eq!(BABYBEAR_P, 2_013_265_921);

    let log2_p = (BABYBEAR_P as f64).log2();
    assert!(
        (log2_p - 30.9069).abs() < 5e-5,
        "log2 p = {log2_p:.6}, expected 30.9069"
    );

    // ONE felt — the three retired columns.
    let narrow_collision = log2_p / 2.0;
    assert!(
        (narrow_collision - 15.4534).abs() < 5e-5,
        "one-felt collision bound = {narrow_collision:.4}, expected 2^15.45"
    );

    // EIGHT felts — `node8`, which the roots/leaves/folds around those columns already use.
    let wide_bits = log2_p * CHIP_OUT_LANES as f64;
    assert!(
        (wide_bits - 247.2551).abs() < 5e-4,
        "node8 codomain = {wide_bits:.4} bits, expected 247.2551"
    );
    let wide_collision = wide_bits / 2.0;
    assert!(
        (wide_collision - 123.6276).abs() < 5e-4,
        "node8 collision bound = {wide_collision:.4}, expected 2^123.63"
    );

    // ⚑ The gap the three columns open inside their own tree.
    assert!(
        wide_collision - narrow_collision > 108.0,
        "the sort key and the pointer sit {:.2} bits of collision resistance below the tree that \
         contains them",
        wide_collision - narrow_collision
    );
}

// ---------------------------------------------------------------------------------------------
// §3 — A REAL COLLISION AT THE DEPLOYED PARAMETER, MEASURED.
// ---------------------------------------------------------------------------------------------

/// A nullifier as the protocol makes one: `cell::note::Nullifier` is a 32-byte BLAKE3 image of the
/// spent note. The attacker chooses the note, so they choose the preimage — a birthday search over
/// notes is a birthday search over nullifiers.
fn nullifier_of_note(nonce: u64) -> [u8; 32] {
    let mut h = blake3::Hasher::new();
    h.update(b"dregg-note-nullifier-v1");
    h.update(&nonce.to_le_bytes());
    *h.finalize().as_bytes()
}

/// The deployed map key for a nullifier: `fold_bytes32_to_bb`, the Horner fold over the eight
/// 4-byte limbs (`circuit/src/effect_vm/helpers.rs:298`). This is the felt that lands in
/// `param::NULLIFIER`, in PI[38]/PI[46], and — through `nullifierFreshOp` — in `MA_KEY`.
fn deployed_key(nf: &[u8; 32]) -> BabyBear {
    fold_bytes32_to_bb(nf)
}

/// Deterministic birthday search for two DISTINCT notes whose nullifiers land on ONE deployed map
/// key. Returns `(nf_a, nf_b, evaluations)`.
fn find_deployed_key_collision() -> ([u8; 32], [u8; 32], u64) {
    let mut seen: HashMap<u32, [u8; 32]> = HashMap::new();
    let mut evaluations = 0u64;
    for nonce in 0u64.. {
        let nf = nullifier_of_note(nonce);
        evaluations += 1;
        let k = deployed_key(&nf).as_u32();
        if let Some(prev) = seen.get(&k) {
            if *prev != nf {
                return (*prev, nf, evaluations);
            }
        } else {
            seen.insert(k, nf);
        }
        assert!(
            nonce < 50_000_000,
            "no collision after 50M draws — that would refute the 2^15.45 bound"
        );
    }
    unreachable!()
}

/// **THE COLLISION, MEASURED.** Two distinct 32-byte nullifiers, each a genuine BLAKE3 image of a
/// note an attacker may freely construct, sharing ONE deployed map key.
#[test]
fn deployed_nullifier_key_collides_at_the_measured_birthday_bound() {
    let t0 = Instant::now();
    let (nf_a, nf_b, evaluations) = find_deployed_key_collision();
    let elapsed = t0.elapsed();

    assert_ne!(
        nf_a, nf_b,
        "the two nullifiers must be DISTINCT 32-byte values"
    );
    assert_eq!(
        deployed_key(&nf_a),
        deployed_key(&nf_b),
        "…and must share ONE deployed map key"
    );

    println!(
        "MEASURED: deployed map-key collision in {evaluations} evaluations ({:.3} s) — \
         key {} shared by two distinct nullifiers",
        elapsed.as_secs_f64(),
        deployed_key(&nf_a).as_u32()
    );

    // The bound predicts ~sqrt(pi/2 · p) ≈ 56,150 draws; allow a generous deterministic window.
    assert!(
        evaluations < 1_000_000,
        "collision took {evaluations} evaluations — far above the 2^15.45 birthday bound"
    );

    // ANTI-VACUITY: the collision is in the FOLD, not in BLAKE3. The full 32-byte images differ,
    // and the eight-lane and nine-lane encodings of them differ too.
    assert_ne!(
        bytes32_to_8_limbs(&nf_a),
        bytes32_to_8_limbs(&nf_b),
        "the EIGHT-lane encoding must separate the pair the one-felt fold conflates"
    );
    assert_ne!(
        field_limbs9(&nf_a),
        field_limbs9(&nf_b),
        "the NINE-lane encoding must separate the pair the one-felt fold conflates"
    );
}

/// **ANTI-VACUITY, THE ROUND-TRIP.** The brief's rule: assert a round-trip OUT of the widened key,
/// not merely that digests differ. `field_limbs9` / `field_from_lanes9` is the injective nonet with
/// a TOTAL decoder (Lean `FieldLanes9.lanes9ToField`, left inverse `lanes9ToField_fieldToLanes9`).
///
/// ⚑ And the contrast that decides which encoder the cutover must use: the deployed EIGHT-lane
/// `bytes32_to_8_limbs` has **no decoder and cannot have one** — eight BabyBear lanes carry
/// 247.26 bits against 256, so by pigeonhole it is not injective on 32 bytes. This test exhibits a
/// concrete O(1) second preimage for it: adding `p` to one 4-byte limb leaves the lane vector
/// byte-identical.
#[test]
fn nine_lanes_round_trip_and_eight_lanes_provably_cannot() {
    let (nf_a, nf_b, _) = find_deployed_key_collision();

    // NINE lanes: a real round-trip, both directions, on both members of the colliding pair.
    for nf in [&nf_a, &nf_b] {
        let lanes = field_limbs9(nf);
        let back = field_from_lanes9(&lanes);
        assert_eq!(
            &back, nf,
            "the nine-lane key must decode back to the exact 32-byte nullifier"
        );
    }

    // EIGHT lanes: an O(1) second preimage. `bytes32_to_8_limbs` reduces each 4-byte LE chunk mod
    // p, and `x + p < 2^32` for every `x < 2^32 - p = 2281701375`, so one addition produces a
    // DIFFERENT 32-byte string with an IDENTICAL lane vector.
    let mut alias = nf_a;
    let lane0 = u32::from_le_bytes([alias[0], alias[1], alias[2], alias[3]]);
    let bumped = lane0
        .checked_add(BABYBEAR_P)
        .expect("lane 0 admits the +p alias");
    alias[0..4].copy_from_slice(&bumped.to_le_bytes());

    assert_ne!(alias, nf_a, "the alias is a DIFFERENT 32-byte string");
    assert_eq!(
        bytes32_to_8_limbs(&alias),
        bytes32_to_8_limbs(&nf_a),
        "…with an IDENTICAL eight-lane encoding — an O(1) second preimage, no search"
    );
    assert_ne!(
        field_limbs9(&alias),
        field_limbs9(&nf_a),
        "the nine-lane encoding refuses the same alias"
    );
    assert_eq!(
        field_from_lanes9(&field_limbs9(&alias)),
        alias,
        "…and still round-trips"
    );
}

// ---------------------------------------------------------------------------------------------
// §4 — OLD vs NEW AT THE DEPLOYED PROVER, on a genuinely well-formed tree.
// ---------------------------------------------------------------------------------------------

/// The `.absent` descriptor the deployed `nullifierFreshOp` realizes, at its own minimal width:
/// `root8 [0..8) · key 8 · new_root8 [9..17) · guard 17`. Byte-for-byte the shape
/// `descriptor_ir2.rs`'s own `absent_desc()` uses, so this is the deployed gate and not a straw man.
fn absent_desc() -> EffectVmDescriptor2 {
    EffectVmDescriptor2 {
        name: "mapabsent-key-width-tooth".to_string(),
        trace_width: 18,
        public_input_count: 0,
        tables: vec![],
        constraints: vec![VmConstraint2::MapOp(MapOpSpec {
            guard: LeanExpr::Var(17),
            root: (0..CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            key: LeanExpr::Var(8),
            value: LeanExpr::Const(0),
            new_root: (9..9 + CHIP_OUT_LANES).map(LeanExpr::Var).collect(),
            op: MapKind::Absent,
        })],
        hash_sites: vec![],
        ranges: vec![],
    }
}

fn absent_trace(heap: &[HeapLeaf], key: BabyBear) -> Vec<Vec<BabyBear>> {
    let tree = CanonicalHeapTree8::new(heap.to_vec(), HEAP_TREE_DEPTH);
    let root = tree.root8();
    let mk = |guard: BabyBear| {
        let mut r = vec![BabyBear::ZERO; 18];
        r[0..CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[8] = key;
        r[9..9 + CHIP_OUT_LANES].copy_from_slice(&root[..]);
        r[17] = guard;
        r
    };
    vec![
        mk(BabyBear::ONE),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
        mk(BabyBear::ZERO),
    ]
}

/// A genuinely well-formed nullifier set: honest spent nullifiers at their honest deployed keys,
/// every leaf relinked into a sorted IMT chain by `CanonicalHeapTree8::new`. Nothing here is a
/// fixture address — every `addr` is `fold_bytes32_to_bb` of a real BLAKE3 nullifier.
fn honest_spent_set(spent: &[[u8; 32]]) -> Vec<HeapLeaf> {
    spent
        .iter()
        .map(|nf| HeapLeaf::entry(deployed_key(nf), BabyBear::new(7)))
        .collect()
}

/// ⚑⚑ **THE WOUND, EXHIBITED AT THE DEPLOYED PROVER: a note nobody has ever spent is certified
/// ALREADY SPENT, permanently.**
///
/// `nf_a` is spent — its deployed key sits in a genuinely well-formed IMT. `nf_b` is a DIFFERENT
/// note that has never been spent and whose owner is a stranger. Because the tree is keyed by the
/// one-felt fold, `nf_b`'s freshness proof asks the `.absent` gate for a bracket around a key that
/// is PRESENT, and the deployed prover refuses — forever, deterministically, at every root that
/// contains `nf_a`. The note is not stolen. It is destroyed.
///
/// Both acceptance conditions are honest on the `nf_a` side: the low leaf is a real member, the
/// chain is really sorted, the root is really the committed one. The only thing that is false is
/// the identification of `nf_b` with `nf_a`, and that identification is the one-felt column.
#[test]
fn spent_note_freezes_a_stranger_note_forever() {
    let t0 = Instant::now();
    let (nf_a, nf_b, evaluations) = find_deployed_key_collision();
    let search = t0.elapsed();

    // Honest set: the spent `nf_a` plus unrelated honest spends, all at genuine deployed keys.
    let others: Vec<[u8; 32]> = (10_000_000u64..10_000_016).map(nullifier_of_note).collect();
    let mut spent = vec![nf_a];
    spent.extend_from_slice(&others);
    let heap = honest_spent_set(&spent);

    let tree = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH);
    assert!(
        tree.position_of(deployed_key(&nf_a)).is_some(),
        "nf_a is genuinely committed"
    );

    // ⚑ nf_b has NEVER been spent — it is not in `spent` — yet its deployed key IS present.
    assert!(!spent.contains(&nf_b), "nf_b was never spent by anyone");
    assert!(
        tree.position_of(deployed_key(&nf_b)).is_some(),
        "…and yet the deployed one-felt key says it is already in the set"
    );

    // THE DEPLOYED PROVER REFUSES nf_b's honest freshness claim.
    let desc = absent_desc();
    let refused = prove_vm_descriptor2(
        &desc,
        &absent_trace(&heap, deployed_key(&nf_b)),
        &[],
        &MemBoundaryWitness::default(),
        &[heap.clone()],
    );
    assert!(
        refused.is_err(),
        "the deployed `.absent` gate must refuse — that refusal IS the wound: an unspent note \
         can never be spent again"
    );
    println!(
        "MEASURED: freeze constructed in {evaluations} evaluations ({:.3} s search); deployed \
         prover refusal: {}",
        search.as_secs_f64(),
        refused.err().unwrap_or_default()
    );

    // ⚑ THE NEW SHAPE ADMITS IT. At an injective nine-lane key the two nullifiers are two
    // DIFFERENT addresses, so nf_b's freshness is a true statement with a real bracket. We assert
    // the separation that makes it true, and the round-trip that makes the separation meaningful.
    assert_ne!(
        field_limbs9(&nf_a),
        field_limbs9(&nf_b),
        "the widened key separates them"
    );
    assert_eq!(field_from_lanes9(&field_limbs9(&nf_b)), nf_b);

    // ⚑⚑ AND THE DIRECTION THAT IS *NOT* AVAILABLE, stated as a construction rather than an
    // opinion: a fold collision can never make a SPENT nullifier pass as fresh. The tree is keyed
    // by the fold AND bracketed on the fold, so `.absent` is sound and merely incomplete. Every
    // member of the colliding class is present exactly when any member is.
    for nf in [&nf_a, &nf_b] {
        assert!(
            tree.position_of(deployed_key(nf)).is_some(),
            "the whole colliding class is present together — there is no member of it the gate \
             would admit as fresh (Lean: MapOpWideKey.narrow_only_over_revokes)"
        );
    }
}

/// **COMPLETENESS AT THE DEPLOYED PROVER.** An honest note spend — a nullifier whose deployed key
/// is genuinely absent and genuinely bracketed by the committed chain — still proves and still
/// verifies. The wound above is incompleteness on a colliding key, not a broken gate.
#[test]
fn honest_note_spend_still_proves_and_verifies() {
    let spent: Vec<[u8; 32]> = (20_000_000u64..20_000_024).map(nullifier_of_note).collect();
    let heap = honest_spent_set(&spent);
    let tree = CanonicalHeapTree8::new(heap.clone(), HEAP_TREE_DEPTH);

    // A fresh note whose deployed key is absent and strictly inside the committed range.
    let fresh = (30_000_000u64..30_010_000)
        .map(nullifier_of_note)
        .find(|nf| {
            let k = deployed_key(nf);
            tree.position_of(k).is_none()
                && k.as_u32() > 0
                && k.as_u32() < SENTINEL_MAX.as_u32()
                && tree
                    .sorted_leaves()
                    .iter()
                    .any(|l| l.addr.as_u32() < k.as_u32() && l.next_addr.as_u32() > k.as_u32())
        })
        .expect("an honest fresh nullifier exists");

    let desc = absent_desc();
    let proof = prove_vm_descriptor2(
        &desc,
        &absent_trace(&heap, deployed_key(&fresh)),
        &[],
        &MemBoundaryWitness::default(),
        &[heap.clone()],
    )
    .expect("an honest freshness witness must still prove at the deployed prover");
    verify_vm_descriptor2(&desc, &proof, &[]).expect("…and must still verify");
}

/// The anti-ghost control: a genuinely SPENT nullifier is refused. Paired with the completeness
/// test above, this shows the gate has both polarities and the freeze above is not simply "the
/// prover refuses everything."
#[test]
fn a_genuinely_spent_nullifier_is_refused() {
    let spent: Vec<[u8; 32]> = (20_000_000u64..20_000_024).map(nullifier_of_note).collect();
    let heap = honest_spent_set(&spent);
    let desc = absent_desc();
    assert!(
        prove_vm_descriptor2(
            &desc,
            &absent_trace(&heap, deployed_key(&spent[3])),
            &[],
            &MemBoundaryWitness::default(),
            &[heap.clone()],
        )
        .is_err(),
        "a genuinely spent nullifier must be refused"
    );
}

// ---------------------------------------------------------------------------------------------
// §5 — THE HALF-WIDENED STATE IS A NON-MEMBERSHIP FORGERY. WIDEN BOTH OR NEITHER.
// ---------------------------------------------------------------------------------------------

/// The half-widened leaf schema the cutover must NOT pass through: the address absorbed at all
/// eight lanes, the pointer still projected to lane 0. Arity 10 (`8 + 1 + 1`) — the Rust mirror of
/// Lean `MapOpWideKeyGate.halfWideLeafHash`.
fn half_wide_preimage(addr: &[u8; 32], value: u32, next: &[u8; 32]) -> Vec<BabyBear> {
    let mut pre: Vec<BabyBear> = bytes32_to_8_limbs(addr).to_vec();
    pre.push(BabyBear::new(value));
    pre.push(bytes32_to_8_limbs(next)[0]); // ← the projection that forges
    pre
}

/// The full wide schema (`HeapLeafWideEmit.wideLeafBlock`): arity 17, `addr8 ‖ value ‖ next8`.
fn full_wide_preimage(addr: &[u8; 32], value: u32, next: &[u8; 32]) -> Vec<BabyBear> {
    let mut pre: Vec<BabyBear> = bytes32_to_8_limbs(addr).to_vec();
    pre.push(BabyBear::new(value));
    pre.extend_from_slice(&bytes32_to_8_limbs(next));
    pre
}

/// ⚑⚑ **THE HALF-WIDENED STATE FORGES ABSENCE OF A PRESENT KEY — for EVERY hash, with no
/// collision-resistance hypothesis, at O(1).**
///
/// Widening the sort key while leaving the pointer at lane 0 means the honest low leaf
/// `⟨lowAddr, v, keyE⟩` and a FABRICATED leaf `⟨lowAddr, v, ptrHi⟩` have the SAME digest preimage
/// whenever `keyE` and `ptrHi` agree in lane 0 — which one addition arranges. The fabricated
/// pointer then brackets `keyE`, an address the honest chain PRESENTS: a present key certified
/// absent. This is the Rust exhibit of `MapOpWideKeyGate.halfWideLeaf_forges_absence_of_present`,
/// and it is the reason the key and the pointer are one move.
///
/// The arity-17 schema separates the same pair, which is the repair.
#[test]
fn half_widening_conflates_the_pointer_and_forges_absence() {
    // The lexicographic order the widened bracket compares (`toLex` on the lane vector: lane 0
    // first, then lane 1, …). Everything below is CONSTRUCTED to land in a fixed order — there is
    // no search and no branch, so no execution of this test can take an easy path.
    let lex = |b: &[u8; 32]| bytes32_to_8_limbs(b).map(|f| f.as_u32());

    // `key_e` — a genuinely PRESENT address. Lane 0 (bytes 0..4) is pinned to 7 and lane 1
    // (bytes 4..8) to 100, so its position in the order is known, not observed.
    let mut key_e = nullifier_of_note(2);
    key_e[0..4].copy_from_slice(&7u32.to_le_bytes());
    key_e[4..8].copy_from_slice(&100u32.to_le_bytes());

    // `low_addr` — the honest low leaf, strictly BELOW `key_e`: same construction, lane 0 = 3.
    let mut low_addr = nullifier_of_note(1);
    low_addr[0..4].copy_from_slice(&3u32.to_le_bytes());

    // `ptr_hi` — the FABRICATED pointer. Identical to `key_e` in lane 0, strictly greater in
    // lane 1. One edit, no search: this is the O(1) the theorem claims.
    let mut ptr_hi = key_e;
    ptr_hi[4..8].copy_from_slice(&101u32.to_le_bytes());

    let (lo, ke, ph) = (lex(&low_addr), lex(&key_e), lex(&ptr_hi));

    // The bracket is REAL and STRICT, unconditionally — `low_addr < key_e < ptr_hi` at the full
    // eight-lane width. This is what makes the conflation below a forgery and not a curiosity.
    assert!(lo < ke, "low_addr < key_e at the widened order");
    assert!(
        ke < ph,
        "key_e < ptr_hi at the widened order — the fabricated bracket CONTAINS a \
                      present address"
    );

    assert_ne!(
        ptr_hi, key_e,
        "the fabricated pointer is a DIFFERENT address"
    );
    assert_eq!(
        bytes32_to_8_limbs(&ptr_hi)[0],
        bytes32_to_8_limbs(&key_e)[0],
        "…that the lane-0 projection cannot tell apart"
    );

    // ⚑ THE FORGERY: at the half-widened schema the honest low leaf ⟨low_addr, 1, key_e⟩ and the
    // fabricated ⟨low_addr, 1, ptr_hi⟩ are ONE preimage, so EVERY hash gives them one digest. A
    // verifier that authenticates the honest leaf authenticates the fabricated one, and the
    // fabricated one brackets a key the honest chain PRESENTS: a present key certified absent.
    // No collision-resistance hypothesis is used or needed.
    assert_eq!(
        half_wide_preimage(&low_addr, 1, &key_e),
        half_wide_preimage(&low_addr, 1, &ptr_hi),
        "half-widening makes the honest low leaf and the fabricated one ONE preimage — every \
         hash maps them to one digest, no CR hypothesis needed"
    );
    assert_eq!(
        half_wide_preimage(&low_addr, 1, &key_e).len(),
        10,
        "the half-widened leaf is arity 10 (addr8 ‖ value ‖ proj0 next)"
    );

    // ⚑ THE REPAIR: the arity-17 schema separates the pair the half-wide schema conflated.
    assert_ne!(
        full_wide_preimage(&low_addr, 1, &key_e),
        full_wide_preimage(&low_addr, 1, &ptr_hi),
        "the arity-17 wide leaf (addr8 ‖ value ‖ next8) separates them — key and pointer must \
         widen together"
    );
    assert_eq!(full_wide_preimage(&low_addr, 1, &key_e).len(), 17);
}
