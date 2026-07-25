//! **THE ~31-BIT `interface_id` FORGE IS CLOSED — leaves, chain accumulator, tail.**
//!
//! The hole this pins: `InterfaceDescriptor::compute_interface_id` used to be
//! 1-felt END TO END — each method leaf was ONE ~31-bit Poseidon2 felt
//! (`MethodSig::leaf_felt`, `hash_many` over the method's canonical lanes), the
//! fold accumulator was ONE felt (`acc = hash_many([acc, leaf])`), and the tail
//! wrote that felt's 4 low bytes into a `[u8; 32]` (`felt_to_bytes32`, bytes
//! 4..32 zero). The WHOLE id carried ~31 bits, so an adversary grinding method
//! names could birthday-collide two genuinely DIFFERENT interfaces at ~2^15.5
//! candidates. Downstream that is not cosmetic: `directory`'s
//! `derive_service_factory_vk` BLAKE3s the interface_id — colliding interfaces
//! SHARE a factory VK — and `discover_by_interface` conflates them.
//!
//! The fix is the faithful widening: 8-felt leaf digests (`hash_many_8`), an
//! 8-felt chain accumulator at EVERY fold step, and the injective
//! `digest8_to_bytes32` tail. These tests are the teeth, modeled on
//! `offchain_root_forge_closed.rs`: each derives its colliding pair at test
//! time by a live birthday search against the code as it exists NOW — no
//! pinned constants to go stale.
//!
//! Three exhibits, in ascending strength:
//!
//! 1. [`old_1felt_fold_collision_now_separated`] — two method sets
//!    byte-IDENTICAL under the pre-widening 1-felt fold (reconstructed here
//!    exactly as it stood at `cell/src/interface.rs:163-258` @ `8b08e15c9`),
//!    separated by the new id. Documents the closed hole.
//! 2. [`leaf_lane0_collision_separated_by_wide_leaf`] — two methods whose NEW
//!    8-felt LEAVES collide on lane 0 (differ only in lanes 1..7): the ids
//!    still separate, so the leaf's high lanes are load-bearing. A pipeline
//!    that narrowed the leaf back to one felt would conflate this pair.
//! 3. [`chain_interior_lane0_collision_separated`] — THE anti-laundering
//!    exhibit: two 2-method sets whose 8-felt chain ACCUMULATOR after fold
//!    step 1 collides on lane 0, and whose remaining fold input (the closing
//!    leaf) is IDENTICAL — so the ONLY separating information entering the
//!    final fold step is accumulator lanes 1..7. The ids differ, therefore the
//!    deployed chain transmits the WIDE accumulator between steps. A laundered
//!    widening (1-felt interior carrier, wide final squeeze only) would
//!    REQUIRE these two ids to be equal.
//!
//! The reconstructions of fold interiors below are bound back to the deployed
//! code by full-fold consistency assertions (the reconstructed id must equal
//! `InterfaceDescriptor::new(..).interface_id` byte-for-byte), so exhibit 3 is
//! about the REAL interior values, not a mirror's.

use std::collections::HashMap;

use dregg_cell::commitment::digest8_to_bytes32;
use dregg_cell::interface::{InterfaceDescriptor, MethodSig, Symbol};
use dregg_circuit::field::BabyBear;
use dregg_circuit::poseidon2::{hash_many, hash_many_8};

/// Candidate budget for each birthday search. The collided projection is one
/// ~31-bit BabyBear lane, so a collision is expected after ~sqrt(π/2 · 2^31)
/// ≈ 58k candidates; 2M is ~35× that. Exhausting it does not mean "unlucky" —
/// it means the projection is no longer ~31-bit (a structural change this test
/// must report rather than paper over).
const SEARCH_BUDGET: u64 = 2_000_000;

/// A synthetic 32-byte method symbol from a search seed. Real symbols are
/// BLAKE3 method-name hashes; the descriptor binds whatever 32 bytes the
/// symbol IS, and an adversary grinding METHOD NAMES controls the symbol
/// distribution just as freely as this seed loop does — so seed-derived
/// symbols model the forge faithfully (and cheaply).
fn symbol(seed: u64) -> Symbol {
    let mut s = [0u8; 32];
    s[0..8].copy_from_slice(&seed.to_le_bytes());
    s[8] = 0xA7; // domain-ish separator from other planes' synthetic keys
    s
}

/// A closing-method symbol from a DISJOINT seed domain (separator differs), so
/// exhibit 3's closing method can never equal a searched method.
fn closer_symbol(seed: u64) -> Symbol {
    let mut s = [0u8; 32];
    s[0..8].copy_from_slice(&seed.to_le_bytes());
    s[8] = 0xB3;
    s
}

fn method(sym: Symbol) -> MethodSig {
    MethodSig::replayable(sym)
}

/// Generic birthday search: derive two DISTINCT seeds whose `value_of` outputs
/// **collide on the u32 projection** but **differ overall**. Panics loudly if
/// the budget is exhausted (a silent skip would be a green that means the
/// forge regression stopped running).
fn find_lane0_collision<V, F>(what: &str, mut value_of: F) -> (u64, u64, V, V)
where
    V: PartialEq + Clone,
    F: FnMut(u64) -> (u32, V),
{
    let mut seen: HashMap<u32, (u64, V)> = HashMap::new();
    for seed in 0..SEARCH_BUDGET {
        let (proj, full) = value_of(seed);
        match seen.get(&proj) {
            Some((prev_seed, prev_full)) if *prev_full != full => {
                println!(
                    "{what}: derived lane-0 collision after {} candidates: \
                     seed {prev_seed} vs seed {seed} (proj = {proj})",
                    seed + 1
                );
                return (*prev_seed, seed, prev_full.clone(), full);
            }
            // Same projection AND same full value: not a separation — skip.
            Some(_) => {}
            None => {
                seen.insert(proj, (seed, full));
            }
        }
    }
    panic!(
        "{what}: no lane-0 collision in {SEARCH_BUDGET} candidates. The projection is one \
         ~31-bit BabyBear lane, so the birthday expectation is ~58k — exhausting the budget \
         means the projection changed shape (no longer ~31-bit, or the seed space no longer \
         varies it). This test's premise is that a lane-0 collision EXISTS and the wide \
         pipeline separates it; if the premise is gone, re-derive the test, don't pass it."
    );
}

// ─── The PRE-WIDENING algorithm, reconstructed verbatim ──────────────────────
//
// Mirrors `cell/src/interface.rs:163-258` as of commit `8b08e15c9` (the last
// commit before the widening): the 1-felt leaf, the 1-felt fold, the 4-low-
// bytes tail. Kept ONLY as the historical forge target for exhibit 1 — nothing
// in the deployed crate computes this anymore.

/// The pre-widening `MethodSig::leaf_felt` for a `MethodSig::replayable` sig:
/// `hash_many([symbol_limbs(8), args_tag=1 (Variadic), args_n=0, auth_tag=0
/// (AuthRequired::None tier), semantics_tag=0 (Replayable)])` — ONE ~31-bit felt.
fn old_leaf_felt_replayable(sym: &Symbol) -> BabyBear {
    let mut inputs: Vec<BabyBear> = Vec::with_capacity(12);
    inputs.extend_from_slice(&dregg_circuit::effect_vm::bytes32_to_8_limbs(sym));
    inputs.push(BabyBear::new(1)); // ArgsSchema::Variadic commitment tag
    inputs.push(BabyBear::new(0)); // Variadic carries no arity
    inputs.push(BabyBear::new(0)); // AuthRequired::None tier felt
    inputs.push(BabyBear::new(0)); // Semantics::Replayable tag
    hash_many(&inputs)
}

/// The pre-widening `compute_interface_id`: sort 1-felt leaves by `as_u32`,
/// seed `hash_many([0x1FACE, len])`, fold `acc = hash_many([acc, leaf])`, tail
/// = the felt's 4 LE bytes ‖ 28 zero bytes (`felt_to_bytes32`). ~31 bits end
/// to end.
fn old_interface_id(symbols: &[Symbol]) -> [u8; 32] {
    let mut leaves: Vec<BabyBear> = symbols.iter().map(old_leaf_felt_replayable).collect();
    leaves.sort_by_key(|f| f.as_u32());
    let mut acc = hash_many(&[BabyBear::new(0x1FACE), BabyBear::new(leaves.len() as u32)]);
    for leaf in &leaves {
        acc = hash_many(&[acc, *leaf]);
    }
    let mut out = [0u8; 32];
    out[0..4].copy_from_slice(&acc.as_u32().to_le_bytes());
    out
}

// ─── Exhibit 1: the OLD fold collides byte-identically; the NEW id separates ─

#[test]
fn old_1felt_fold_collision_now_separated() {
    // ── HONEST POLE FIRST: both producers are deterministic — else every
    // equality/separation below measures noise.
    assert_eq!(
        old_interface_id(&[symbol(7)]),
        old_interface_id(&[symbol(7)]),
        "honest pole: the reconstructed old fold must be deterministic"
    );
    assert_eq!(
        InterfaceDescriptor::compute_interface_id(&[method(symbol(7))]),
        InterfaceDescriptor::compute_interface_id(&[method(symbol(7))]),
        "honest pole: the deployed wide fold must be deterministic"
    );

    // Birthday-search two single-method interfaces colliding under the OLD
    // fold. The old id is its own u32 projection (bytes 4..32 are zero), so a
    // projection collision IS a full 32-byte old-id collision.
    let (seed_a, seed_b, old_a, old_b) = find_lane0_collision("OLD-FOLD", |seed| {
        let id = old_interface_id(&[symbol(seed)]);
        (
            u32::from_le_bytes([id[0], id[1], id[2], id[3]]),
            symbol(seed),
        )
    });
    assert_ne!(
        old_a, old_b,
        "the two method symbols are genuinely different"
    );

    // THE CLOSED HOLE: under the pre-widening fold these two DIFFERENT
    // interfaces carried the SAME 32-byte interface_id — indistinguishable to
    // verify_id, to discover_by_interface, and to the factory-VK derivation.
    assert_eq!(
        old_interface_id(&[symbol(seed_a)]),
        old_interface_id(&[symbol(seed_b)]),
        "the pre-widening 1-felt fold collides byte-identically (the closed hole)"
    );

    // THE FIX: the wide fold separates them.
    let iface_a = InterfaceDescriptor::new(vec![method(symbol(seed_a))]);
    let iface_b = InterfaceDescriptor::new(vec![method(symbol(seed_b))]);
    assert_ne!(
        iface_a.interface_id, iface_b.interface_id,
        "the 8-felt interface_id must separate the old-fold-colliding pair"
    );

    // Round-trip: the carried id re-verifies (announce()'s anti-forgery gate).
    assert!(iface_a.verify_id() && iface_b.verify_id());
}

// ─── Exhibit 2: leaf lane-0 collision; the wide leaf's high lanes separate ───

#[test]
fn leaf_lane0_collision_separated_by_wide_leaf() {
    // Birthday-search two methods whose NEW 8-felt leaves collide on lane 0.
    let (seed_a, seed_b, leaf_a, leaf_b) = find_lane0_collision("LEAF", |seed| {
        let leaf = method(symbol(seed)).leaf_digest8();
        (leaf[0].as_u32(), leaf.map(|f| f.as_u32()))
    });
    assert_eq!(leaf_a[0], leaf_b[0], "leaf lane 0 collides");
    assert_ne!(
        leaf_a[1..],
        leaf_b[1..],
        "the leaves differ ONLY in lanes 1..7"
    );

    // A pipeline that carried only lane 0 of the leaf would fold identical
    // inputs for these two methods. The deployed id separates them, so the
    // leaf's lanes 1..7 are load-bearing in the fold.
    assert_ne!(
        InterfaceDescriptor::compute_interface_id(&[method(symbol(seed_a))]),
        InterfaceDescriptor::compute_interface_id(&[method(symbol(seed_b))]),
        "the interface_id must separate leaf-lane-0-colliding methods"
    );
}

// ─── Exhibit 3: chain-INTERIOR lane-0 collision; the wide carrier separates ──

#[test]
fn chain_interior_lane0_collision_separated() {
    // The deployed fold for a 2-method set {m, z} with leaf8(m) sorting before
    // leaf8(z) is:
    //   seed8 = hash_many_8([0x1FACE, 2])
    //   acc1  = hash_many_8(seed8 ‖ leaf8(m))    ← the INTERIOR carrier
    //   acc2  = hash_many_8(acc1  ‖ leaf8(z))
    //   id    = digest8_to_bytes32(acc2)
    // (bound back to the deployed code below by a full-fold consistency check).
    let seed8 = hash_many_8(&[BabyBear::new(0x1FACE), BabyBear::new(2)]);
    let step1 = |sym: &Symbol| -> [BabyBear; 8] {
        let leaf = method(*sym).leaf_digest8();
        let mut inputs = [BabyBear::ZERO; 16];
        inputs[0..8].copy_from_slice(&seed8);
        inputs[8..16].copy_from_slice(&leaf);
        hash_many_8(&inputs)
    };

    // Birthday-search two first-methods whose INTERIOR accumulator acc1
    // collides on lane 0 but differs in lanes 1..7.
    let (seed_a, seed_b, acc1_a, acc1_b) = find_lane0_collision("CHAIN-INTERIOR", |seed| {
        let acc1 = step1(&symbol(seed));
        (acc1[0].as_u32(), acc1.map(|f| f.as_u32()))
    });
    assert_eq!(acc1_a[0], acc1_b[0], "interior carrier lane 0 collides");
    assert_ne!(
        acc1_a[1..],
        acc1_b[1..],
        "the interior carriers differ ONLY in lanes 1..7"
    );

    // A shared CLOSING method z whose leaf sorts strictly AFTER both searched
    // leaves (sort is lexicographic over the lanes, so a strictly larger lane
    // 0 suffices) — guaranteeing the searched method is fold step 1 and z is
    // fold step 2 in BOTH sets.
    let lane0_of = |sym: &Symbol| method(*sym).leaf_digest8()[0].as_u32();
    let max_lane0 = lane0_of(&symbol(seed_a)).max(lane0_of(&symbol(seed_b)));
    let z = (0..10_000u64)
        .map(closer_symbol)
        .find(|z| lane0_of(z) > max_lane0)
        .expect("a closing method with a larger leaf lane 0 exists (p ≈ 1 per try at u32 scale)");

    let set_a = vec![method(symbol(seed_a)), method(z)];
    let set_b = vec![method(symbol(seed_b)), method(z)];

    // Bind the reconstruction to the DEPLOYED fold: reconstructing both full
    // folds must reproduce compute_interface_id byte-for-byte, so the interior
    // values asserted above are the real chain's, not a mirror's.
    let full_fold = |first: &Symbol| -> [u8; 32] {
        let mut acc = step1(first);
        let leaf_z = method(z).leaf_digest8();
        let mut inputs = [BabyBear::ZERO; 16];
        inputs[0..8].copy_from_slice(&acc);
        inputs[8..16].copy_from_slice(&leaf_z);
        acc = hash_many_8(&inputs);
        digest8_to_bytes32(acc)
    };
    let id_a = InterfaceDescriptor::compute_interface_id(&set_a);
    let id_b = InterfaceDescriptor::compute_interface_id(&set_b);
    assert_eq!(
        full_fold(&symbol(seed_a)),
        id_a,
        "consistency: the reconstructed fold IS the deployed fold (set A)"
    );
    assert_eq!(
        full_fold(&symbol(seed_b)),
        id_b,
        "consistency: the reconstructed fold IS the deployed fold (set B)"
    );

    // THE ANTI-LAUNDERING TOOTH. The two final fold steps see inputs that are
    // IDENTICAL at carrier lane 0 (the collision) and IDENTICAL at all 8 leaf
    // lanes (same closing method z): the ONLY difference entering the last
    // step is interior-carrier lanes 1..7. The ids differ, therefore the
    // deployed chain transmits the WIDE accumulator between steps. Under a
    // laundered widening — a 1-felt interior carrier with only the final
    // squeeze widened — these two ids would be EQUAL by construction.
    assert_ne!(
        id_a, id_b,
        "the interface_id must separate interior-carrier-lane-0-colliding sets \
         (a 1-felt interior carrier would conflate them)"
    );
}
