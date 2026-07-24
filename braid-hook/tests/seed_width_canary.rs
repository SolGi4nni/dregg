//! **THE SEED-WIDTH CANARY — the hook deploys FAR past the old `u8` cap of 255, no collision.**
//!
//! The Braid hook's earlier residual: `deploy_entity` took a `u8` seed, so any deployer (a
//! `dreggnet-companion` roost, say) could carry at most 256 live entities before the seed wrapped
//! — and a wrap meant two entities colliding onto ONE cell id, so the caller had to fail closed at
//! 255. That is a property of the WIRING, not of anything a game means, so it was widened where it
//! belonged: `entity_key(n: u64)` is now the injective little-endian encoding of a full `u64`
//! ordinal into the entity's 32-byte cell key, and `deploy_entity` takes that full-width key.
//!
//! This canary DRIVES that widening through the hook's own re-exported `entity_key` +
//! `deploy_entity` (content-free — no game rule, no creature, no stat): more than 255 distinct
//! ordinals deploy to more than 255 DISTINCT cell ids, and the exact ordinals a `u8` seed would
//! have wrapped onto each other are now distinct cells. Genuine exhaustion still failing closed is
//! the sibling property, covered by `dreggnet-companion`'s
//! `an_exhausted_ordinal_refuses_rather_than_wrapping_onto_a_live_cell` (the roost advances a
//! CHECKED `u64` counter and refuses at `u64::MAX` rather than wrapping onto a live cell).

use std::collections::HashSet;

use dregg_braid_hook::{Subject, deploy_entity, entity_key};

/// A content-free subject — the canary is about the cell-key namespace, not the projection.
fn subject() -> Subject {
    Subject {
        identity: 1,
        role: 1,
        params: vec![0, 0, 0, 0],
    }
}

/// **More than 255 ordinals → more than 255 distinct cell ids.** The old `u8` seed capped this at
/// 256 and wrapped `256 → 0`; the widened key never collides across a range far past the cap.
#[test]
fn ordinals_past_the_old_u8_cap_deploy_without_collision() {
    // 600 is comfortably past 255/256 — the exact regime the old `u8` seed could not represent.
    const N: u64 = 600;
    let mut keys: HashSet<[u8; 32]> = HashSet::new();
    let mut cells = HashSet::new();
    for n in 0..N {
        let key = entity_key(n);
        assert!(
            keys.insert(key),
            "entity_key({n}) collided with an earlier ordinal — the key is not injective"
        );
        let cell = deploy_entity(key, 0, subject()).cell_id();
        assert!(
            cells.insert(cell),
            "deploy_entity(entity_key({n})) landed on an already-live cell id — the cap is back"
        );
    }
    assert_eq!(keys.len(), N as usize, "every ordinal is a distinct key");
    assert_eq!(cells.len(), N as usize, "every ordinal is a distinct cell");
}

/// **The exact `u8`-wrap witnesses are now distinct cells.** With the old byte seed, ordinal `k`
/// and `k + 256` (equal mod 256) shared one cell; each pair is now a distinct entity.
#[test]
fn the_u8_wrap_witnesses_are_now_distinct_cells() {
    let cell = |n: u64| deploy_entity(entity_key(n), 0, subject()).cell_id();
    for (low, wrapped) in [(0u64, 256u64), (1, 257), (5, 261), (255, 511)] {
        assert_ne!(
            cell(low),
            cell(wrapped),
            "ordinals {low} and {wrapped} (≡ {low} mod 256) must be distinct cells after widening"
        );
    }
}
