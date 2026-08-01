//! **THE $0 PERMANENT-CONSENSUS-HALT TOOTH — old-halts / new-survives, at a measured cost.**
//!
//! Until 2026-08-01 `rotation_witness::cells_root` keyed each present-cell existence leaf by
//! `heap_addr(CELLS_COLLECTION, hash_bytes(id))` — ONE BabyBear felt (`p < 2^31`, ~30.9 bits) per
//! 32-byte `CellId`. Two separate decisions turned that width into a liveness kill:
//!
//! 1. **2026-07-28**: `heap_root::assert_addr_unique` began *panicking* (release-active) on a
//!    repeated leaf address instead of silently deduping. That was RIGHT — a dedup makes a
//!    colliding cell's REMOVAL invisible to the signed anchor — but it converted an ambiguous
//!    commitment into an abort.
//! 2. The key stayed one felt. `CellId::derive_raw` is
//!    `blake3::derive_key("dregg-cell-id-v1", public_key ‖ token_id)` over two ATTACKER-CHOSEN
//!    32-byte arrays, and `Effect::CreateCell` validates only `balance == 0` — no possession
//!    check on `public_key`, no token registry, no rate limit. So the grind below is entirely
//!    offline and the follow-through is two ordinary cell creations.
//!
//! `cells_root` sits on the unconditional per-turn anchor path (`state_commit::consensus_ctx` →
//! `consensus_state_commitment`, computed for pre-state and post-state on every turn by every
//! node). A panic there is classified `FatalIntegrity`, the finality executor stops with the
//! block unacknowledged, and a restart replays the same block and stops again — deterministically,
//! on every node, forever.
//!
//! ## What this file asserts, in both polarities
//!
//! * **THE GRIND IS REAL AND ITS PRICE IS MEASURED**, not assumed: [`grind_key_collision`] finds
//!   two `token_id`s whose derived `CellId`s share the retired one-felt key, and the test REPORTS
//!   the evaluation count rather than pinning it.
//! * **OLD HALTS**: the retired producer body — transcribed verbatim here, calling the DEPLOYED
//!   `compute_canonical_heap_root_8_entries` — PANICS on a ledger holding both cells.
//! * **NEW SURVIVES**: the deployed `cells_root` commits that same ledger, and the deployed
//!   consensus anchor computes over it.
//! * **ANTI-VACUITY**: the two ids ROUND-TRIP out of the widened key. "The keys differ" would
//!   prove nothing — a wider *hash* also makes keys differ while remaining collidable. What is
//!   claimed here is INJECTIVITY, so the test recovers each id back out of its committed limbs.
//! * **COMPLETENESS**: honest traffic still commits, the root is set-valued, and the removal of
//!   ANY cell — including a member of the colliding pair — MOVES the anchor. That last one is the
//!   soundness property the deleted dedup destroyed; it must survive the liveness repair.

use std::collections::HashMap;

use dregg_cell::{Cell, CellId, Ledger};
use dregg_circuit::exact_nullifier_aafi::{
    ExactTaggedKey, exact_linked_append_root8, raw_to_u16_le, u16_le_to_raw,
};
use dregg_circuit::field::BabyBear;
use dregg_circuit::heap_root::{compute_canonical_heap_root_8_entries, heap_addr};
use dregg_circuit::poseidon2::hash_bytes;
use dregg_turn::rotation_witness::{
    EXACT_CELLS_LINKED_DOMAINS, cells_root, empty_commitments_root_8, empty_nullifier_root_8,
    empty_revoked_root_8,
};
use dregg_turn::state_commit::{consensus_ctx, consensus_state_commitment};

/// The value of the RETIRED private `rotation_witness::CELLS_COLLECTION`. Kept here because the
/// retired producer must be reconstructible in VALUE — a wound demonstrated only by a git-history
/// claim decays into an assertion nobody can re-run.
const RETIRED_CELLS_COLLECTION: u32 = 0;

/// The attacker's single public key. They never need a second one, and never need the private
/// half: `apply_create_cell` never checks possession, so `token_id` alone is a free 32-byte
/// grinding domain. This is the cheaper form of the attack.
const ATTACKER_PK: [u8; 32] = [0xA7; 32];

/// An honest bystander whose cell is present in every ledger below.
const VICTIM_PK: [u8; 32] = [0x11; 32];
const VICTIM_TOKEN: [u8; 32] = [0x22; 32];

/// A hard ceiling on the birthday search, ~64x the analytic price. Bounding it loosely (rather
/// than pinning an exact count) is what keeps this a measurement instead of a fixture.
const GRIND_CEILING: u64 = 3_000_000;

// ---------------------------------------------------------------------------------------------
// The retired key and the retired producer, transcribed
// ---------------------------------------------------------------------------------------------

/// **THE RETIRED KEY**, verbatim: one felt per 32-byte `CellId`.
fn retired_key_addr(id: &CellId) -> BabyBear {
    heap_addr(
        BabyBear::new(RETIRED_CELLS_COLLECTION),
        hash_bytes(id.as_bytes()),
    )
}

/// **THE RETIRED `cells_root` PRODUCER**, verbatim — the body at `rotation_witness.rs` before
/// 2026-08-01. It calls the *deployed* `compute_canonical_heap_root_8_entries`, so this is the
/// real abort path and not a model of it: only the KEY derivation is reconstructed.
fn retired_cells_root(ledger: &Ledger) -> dregg_circuit::Faithful8 {
    let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
    for (id, _) in ledger.iter() {
        let key = hash_bytes(id.as_bytes());
        entries.push((
            (BabyBear::new(RETIRED_CELLS_COLLECTION), key),
            BabyBear::ONE, // existence bit
        ));
    }
    compute_canonical_heap_root_8_entries(&entries)
}

// ---------------------------------------------------------------------------------------------
// The grind
// ---------------------------------------------------------------------------------------------

struct Collision {
    token_a: [u8; 32],
    token_b: [u8; 32],
    id_a: CellId,
    id_b: CellId,
    addr: BabyBear,
    evaluations: u64,
}

/// A deterministic offline birthday search over `token_id`, exactly the attacker's work: derive
/// `CellId::derive_raw(ATTACKER_PK, token_id)`, fold it to the retired one-felt key, and stop at
/// the first repeat. No chain interaction, no signature, no proof, no key material.
fn grind_key_collision() -> Collision {
    let mut seen: HashMap<u32, ([u8; 32], CellId)> = HashMap::new();
    let mut evaluations = 0u64;

    for counter in 0u64..GRIND_CEILING {
        evaluations += 1;
        let mut token = [0u8; 32];
        token[..8].copy_from_slice(&counter.to_le_bytes());

        let id = CellId::derive_raw(&ATTACKER_PK, &token);
        let addr = retired_key_addr(&id);

        if let Some((prev_token, prev_id)) = seen.insert(addr.as_u32(), (token, id)) {
            // A repeat on the ADDRESS. Guard against the degenerate case where we somehow
            // re-derived the same id: the pair must be two DISTINCT cells.
            if prev_id != id {
                return Collision {
                    token_a: prev_token,
                    token_b: token,
                    id_a: prev_id,
                    id_b: id,
                    addr,
                    evaluations,
                };
            }
        }
    }
    panic!(
        "no one-felt key collision within {GRIND_CEILING} offline evaluations — the retired key \
         derivation changed under this test, or `p` grew by ~12 bits"
    );
}

fn ledger_with_victim() -> Ledger {
    let mut ledger = Ledger::new();
    ledger
        .insert_cell(Cell::with_balance(VICTIM_PK, VICTIM_TOKEN, 500))
        .expect("insert victim");
    ledger
}

fn anchor_of(ledger: &Ledger, agent: &CellId) -> [u8; 32] {
    let ctx = consensus_ctx(
        ledger,
        empty_nullifier_root_8(),
        empty_commitments_root_8(),
        empty_revoked_root_8(),
    );
    consensus_state_commitment(ledger, agent, &ctx)
}

// ---------------------------------------------------------------------------------------------
// POLARITY 1 — the retired key HALTS, at a measured price
// ---------------------------------------------------------------------------------------------

/// **THE TOOTH.** Two ordinary cell creations, ground offline, abort the retired `cells_root`;
/// the deployed one commits them and the turn proceeds.
#[test]
fn two_ground_cells_halt_the_retired_key_and_the_widened_key_survives() {
    let started = std::time::Instant::now();
    let c = grind_key_collision();
    let elapsed = started.elapsed();

    // ---- The price, MEASURED. Reported, not pinned: a birthday search is a random variable. ----
    eprintln!(
        "GRIND: {} offline CellId::derive_raw evaluations in {:.2?} — two token_ids whose derived \
         ids share the retired one-felt key {} (analytic birthday price over p = 2^30.91 is \
         ~2^15.45 ≈ 45k)",
        c.evaluations,
        elapsed,
        c.addr.as_u32()
    );
    assert!(
        c.evaluations < GRIND_CEILING,
        "the price must be MEASURED, not assumed: {} evaluations",
        c.evaluations
    );

    // The pair is genuinely two distinct cells that collide on the retired key.
    assert_ne!(c.id_a, c.id_b, "two DISTINCT cell ids");
    assert_ne!(c.token_a, c.token_b, "two DISTINCT token domains");
    assert_eq!(
        retired_key_addr(&c.id_a),
        retired_key_addr(&c.id_b),
        "the pair must COLLIDE on the retired one-felt key — otherwise there is nothing to halt"
    );

    // Both cells are creatable by the ordinary effect path: `Cell::new` derives the id with the
    // same `derive_raw` the executor's `apply_create_cell` uses, from an attacker-chosen
    // `(public_key, token_id)` with no possession check.
    let cell_a = Cell::new(ATTACKER_PK, c.token_a);
    let cell_b = Cell::new(ATTACKER_PK, c.token_b);
    assert_eq!(cell_a.id(), c.id_a, "Cell::new derives the ground id");
    assert_eq!(cell_b.id(), c.id_b, "Cell::new derives the ground id");

    let victim = Cell::with_balance(VICTIM_PK, VICTIM_TOKEN, 500);
    let mut poisoned = ledger_with_victim();
    poisoned.insert_cell(cell_a).expect("first creation");
    poisoned.insert_cell(cell_b).expect("second creation");
    assert_eq!(
        poisoned.len(),
        3,
        "the ledger holds BOTH colliding cells — a HashMap<CellId, _> keyed on the full 32 bytes \
         admits the pair; the collision only exists at commitment time"
    );

    // ---- POLARITY 1: THE RETIRED PRODUCER HALTS. ----
    let halted = std::panic::catch_unwind(|| retired_cells_root(&poisoned));
    assert!(
        halted.is_err(),
        "THE WOUND: the retired one-felt key must PANIC `assert_addr_unique` on this ledger. If \
         this assertion ever fails, either the transcription above has drifted from the body it \
         reconstructs or the release-active refusal was weakened — in both cases the \
         demonstration below is worthless."
    );

    // And it halts on the ANCHOR path, not merely in a helper: the same two cells are what a
    // turn's pre-state and post-state commitments fold over.
    let halted_anchor = std::panic::catch_unwind(|| {
        let mut entries: Vec<((BabyBear, BabyBear), BabyBear)> = Vec::new();
        for (id, _) in poisoned.iter() {
            entries.push((
                (
                    BabyBear::new(RETIRED_CELLS_COLLECTION),
                    hash_bytes(id.as_bytes()),
                ),
                BabyBear::ONE,
            ));
        }
        compute_canonical_heap_root_8_entries(&entries)
    });
    assert!(
        halted_anchor.is_err(),
        "the abort is in the committed fold itself, so every per-turn anchor computation hits it"
    );

    // ---- POLARITY 2: THE DEPLOYED PRODUCER SURVIVES, AND THE TURN PROCEEDS. ----
    let widened = cells_root(&poisoned);
    let anchor = anchor_of(&poisoned, &victim.id());
    assert_ne!(
        anchor, [0u8; 32],
        "the deployed consensus anchor computes over the poisoned-under-the-old-key ledger"
    );

    // The two cells occupy DISTINCT leaves now — the property no root width could buy.
    let key_a = ExactTaggedKey::from_raw(*c.id_a.as_bytes());
    let key_b = ExactTaggedKey::from_raw(*c.id_b.as_bytes());
    assert_ne!(
        key_a, key_b,
        "the widened key must SEPARATE the pair the one-felt key merged"
    );

    // ---- ANTI-VACUITY: the ids ROUND-TRIP out of the committed key. ----
    // "Two keys differ" is what a wider HASH also gives, and a wider hash is still collidable.
    // The claim here is INJECTIVITY (2^256 on the nose, `card_key16` /
    // `u16_limbs_admit_a_bijection` in `Dregg2.Circuit.MapOpWideKeyPigeonhole`), so the test
    // decodes each id back out of the limbs the leaf actually commits.
    for id in [&c.id_a, &c.id_b, &victim.id()] {
        let raw = *id.as_bytes();
        let limbs = raw_to_u16_le(raw);
        assert_eq!(
            u16_le_to_raw(limbs),
            raw,
            "the sixteen u16 limbs must be a LOSSLESS encoding of the 32-byte CellId — a left \
             inverse, not a bound"
        );
        assert_eq!(
            ExactTaggedKey::from_raw(raw).real_raw_bytes(),
            Some(raw),
            "the committed tagged key must decode back to exactly this CellId"
        );
    }

    // ---- And the SOUNDNESS property the deleted dedup destroyed still holds. ----
    // Under the retired key with a dedup, removing either colliding cell left the root
    // byte-identical. Removing ANY cell must move it.
    for victim_id in [c.id_a, c.id_b, victim.id()] {
        let mut reduced = Ledger::new();
        for (id, cell) in poisoned.iter() {
            if *id != victim_id {
                reduced.insert_cell(cell.clone()).expect("re-insert");
            }
        }
        assert_eq!(reduced.len(), 2, "exactly one cell removed");
        assert_ne!(
            cells_root(&reduced),
            widened,
            "removing a cell — INCLUDING a member of the colliding pair — must MOVE the committed \
             root; a removal that is a fixed point of the anchor is the ambiguity the refusal \
             exists to prevent"
        );
    }
}

// ---------------------------------------------------------------------------------------------
// POLARITY 2 — completeness: ordinary traffic is unaffected
// ---------------------------------------------------------------------------------------------

/// Ordinary cell creation and every existing cell still resolve; `cells_root` still computes.
#[test]
fn honest_traffic_commits_and_the_root_is_set_valued() {
    let mut ledger = ledger_with_victim();
    let mut ids = vec![CellId::derive_raw(&VICTIM_PK, &VICTIM_TOKEN)];
    for n in 0u64..24 {
        let mut token = [0u8; 32];
        token[..8].copy_from_slice(&n.to_le_bytes());
        let cell = Cell::with_balance(ATTACKER_PK, token, 0);
        ids.push(cell.id());
        ledger.insert_cell(cell).expect("ordinary creation");
    }
    assert_eq!(ledger.len(), 25);

    let root = cells_root(&ledger);

    // SET-VALUED: the same set inserted in the reverse order commits identically. `Ledger` is a
    // HashMap, so an unsorted fold here would be a consensus split rather than a nondeterminism
    // nit — this is the assertion that catches it.
    let mut reversed = Ledger::new();
    let mut cells: Vec<Cell> = ledger.iter().map(|(_, c)| c.clone()).collect();
    cells.reverse();
    for cell in cells {
        reversed.insert_cell(cell).expect("re-insert");
    }
    assert_eq!(
        cells_root(&reversed),
        root,
        "the root must be a function of the SET of present cells, never the insertion or \
         iteration order"
    );

    // Every cell is individually load-bearing.
    for dropped in &ids {
        let mut reduced = Ledger::new();
        for (id, cell) in ledger.iter() {
            if id != dropped {
                reduced.insert_cell(cell.clone()).expect("re-insert");
            }
        }
        assert_ne!(
            cells_root(&reduced),
            root,
            "removing cell {dropped} must move the committed root"
        );
    }

    // The empty ledger commits the domain's empty-tree root, and NOT the zero digest.
    let empty = cells_root(&Ledger::new());
    let expected_empty = dregg_circuit::exact_nullifier_aafi::exact_root_faithful8(
        exact_linked_append_root8(EXACT_CELLS_LINKED_DOMAINS, &[]).expect("empty fold"),
    );
    assert_eq!(
        empty, expected_empty,
        "the empty ledger must commit the FLI2/FLN2/FLE2 empty-tree root"
    );
    assert_ne!(empty, root, "a populated ledger is not the empty one");
}

/// The cells accumulator is domain-separated from all four siblings — even at EMPTY, where the
/// leaf sets are identical and only the sponge tags differ. Without this, a sibling's empty root
/// could be replayed as "no cells present".
#[test]
fn the_cells_domain_is_separated_from_every_sibling_accumulator() {
    let empty_cells = cells_root(&Ledger::new());
    for (name, sibling) in [
        ("nullifier", empty_nullifier_root_8()),
        ("commitments", empty_commitments_root_8()),
        ("revoked", empty_revoked_root_8()),
    ] {
        assert_ne!(
            empty_cells, sibling,
            "the EMPTY cells root must differ from the EMPTY {name} root — same tree shape, same \
             sentinel leaf, different statement"
        );
    }
}

/// The widened key is not merely wider — it is INJECTIVE, and the retired one was demonstrably
/// not. This restates the counting the repair rests on over the deployed codecs, so a future
/// narrowing of either side fails here rather than silently.
#[test]
fn the_retired_key_was_lossy_and_the_widened_key_is_not() {
    let c = grind_key_collision();

    // RETIRED: two distinct 32-byte ids, ONE committed key. Exhibited, not argued.
    assert_ne!(c.id_a.as_bytes(), c.id_b.as_bytes());
    assert_eq!(
        retired_key_addr(&c.id_a),
        retired_key_addr(&c.id_b),
        "the retired key is NOT injective on 32-byte ids, and here is the witness"
    );

    // WIDENED: distinct ids give distinct keys, and each key decodes back to its id. The second
    // half is what makes this injectivity rather than an unbroken hash.
    let (raw_a, raw_b) = (*c.id_a.as_bytes(), *c.id_b.as_bytes());
    assert_ne!(raw_to_u16_le(raw_a), raw_to_u16_le(raw_b));
    assert_eq!(u16_le_to_raw(raw_to_u16_le(raw_a)), raw_a);
    assert_eq!(u16_le_to_raw(raw_to_u16_le(raw_b)), raw_b);

    // ANTI-VACUITY on the anti-vacuity: the round-trip must be sensitive to every byte, so a
    // codec that dropped one would fail here instead of passing on the two fixture values.
    for byte in 0..32usize {
        let mut mutated = raw_a;
        mutated[byte] ^= 0x01;
        assert_ne!(
            raw_to_u16_le(mutated),
            raw_to_u16_le(raw_a),
            "flipping byte {byte} must move the committed key — the encoding reads ALL 32 bytes"
        );
        assert_eq!(u16_le_to_raw(raw_to_u16_le(mutated)), mutated);
    }
}
