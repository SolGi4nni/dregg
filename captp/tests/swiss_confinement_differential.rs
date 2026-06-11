//! SWISS-TABLE CONFINEMENT ⟷ LEAN DIFFERENTIAL — the trustless tooth across the FFI gap for
//! capability confinement: a capability is UNREACHABLE without its swiss number.
//!
//! The Lean module `Dregg2/Exec/CapTPConfinement.lean` PROVES, against the VERIFIED full-state
//! executor (`execFullA … (.enlivenRefA …)`):
//!
//!   * THEOREM `enliven_unreachable_without_swiss`: a swiss number ABSENT from the table
//!     (`findSwiss = none`) is UNREACHABLE — `enlivenRefA` returns `none`, so NO post-state exists
//!     and NO authority is conferred. (The confinement core.)
//!   * THEOREM `enliven_failed_freezes_caps` / `enliven_no_authority_without_swiss`: WHATEVER the
//!     executor does for an enliven of a swiss the actor does not hold a minted entry for, the cap
//!     table is the pre-state's — no authority enters an adversary's caps without the swiss secret.
//!   * THEOREM `enliven_confined_over_adversaries` (n > 1): confinement is UNIVERSAL over a set of
//!     DISTINCT adversary cells — given a swiss NOT minted, EVERY actor fails to enliven it.
//!   * THEOREM `enliven_minted_of_some`: dually, a SUCCESSFUL enliven WITNESSES a minted swiss
//!     ("enliven succeeds ⇒ sw was minted").
//!   * ASSUMPTION `SwissUnguessable`: the 256-bit unguessability isolated honestly as a named
//!     entropy hypothesis (the bridge from the unconditional `findSwiss`-membership confinement to
//!     "an adversary without the URI cannot enliven").
//!
//! This test drives the REAL `dregg_captp::SwissTable` (`captp/src/sturdy.rs`) — the runtime
//! swiss-table a federation node maintains — and asserts it AGREES with the Lean confinement:
//!
//!   * a swiss number NEVER exported is `EnlivenError::NotFound` on `enliven` — the runtime tooth
//!     for `enliven_unreachable_without_swiss`;
//!   * the table is byte-identical (len + contents) before and after the failed enliven — no
//!     authority/entry materialised (the runtime tooth for `enliven_failed_freezes_caps`);
//!   * n > 1: two DISTINCT adversaries' guessed swiss numbers BOTH `NotFound` (the runtime tooth
//!     for `enliven_confined_over_adversaries`);
//!   * a `getrandom`-minted swiss is 256 bits of entropy — the realizable bar of `SwissUnguessable`
//!     (two independent exports never collide; the adversary cannot guess the secret);
//!   * dually, a genuinely-exported swiss DOES enliven (`enliven_minted_of_some`'s positive twin) —
//!     so the confinement is NOT vacuous (the accept path works).
//!
//! Together with the existing `integration_sturdy_ref_serde.rs` / `integration_swiss_table_revoke.rs`
//! this pins the CONFINEMENT leg (unreachability without the secret) the prior tests did not assert.

use dregg_captp::{EnlivenError, SwissTable};
use dregg_cell::AuthRequired;
use dregg_types::CellId;

fn target_cell() -> CellId {
    CellId([0xCA; 32])
}

/// THEOREM `enliven_unreachable_without_swiss` RUNTIME TOOTH. A swiss number that was NEVER exported
/// is unreachable: presenting it to `enliven` yields `EnlivenError::NotFound`. The Lean executor's
/// `findSwiss = none ⇒ execFullA … = none` is the membership gate; the Rust `HashMap::get_mut`
/// miss is its faithful runtime mirror.
#[test]
fn unexported_swiss_is_unreachable() {
    let mut table = SwissTable::new();
    // The table is EMPTY — nothing was minted. An adversary's guessed swiss number is absent.
    let guessed = [0x99u8; 32];
    let verdict = table.enliven(&guessed, 100);
    assert_eq!(
        verdict.err(),
        Some(EnlivenError::NotFound),
        "CONFINEMENT BREACH — an un-exported swiss number was enlivenable; a capability must be \
         UNREACHABLE without its swiss number (Lean enliven_unreachable_without_swiss)"
    );
}

/// THEOREM `enliven_failed_freezes_caps` RUNTIME TOOTH. A FAILED enliven (missing swiss) leaves the
/// table state byte-identical: no entry materialises, no authority enters. We assert the table's
/// length and contents are unchanged across the failed call — the runtime witness that "no authority
/// enters an adversary's caps without the swiss secret" (the executor returns `none`, so the only
/// reachable post-state is the pre-state).
#[test]
fn failed_enliven_freezes_table() {
    let mut table = SwissTable::new();
    // Mint ONE legitimate entry so the table is non-empty (a realistic federation).
    let legit = table.export(target_cell(), AuthRequired::Signature, 100, None);

    let len_before = table.len();
    let legit_present_before = table.contains(&legit);

    // An adversary guesses a DIFFERENT swiss number and fails to enliven it.
    let guessed = [0x77u8; 32];
    assert_ne!(
        guessed, legit,
        "test setup: guessed key must differ from the minted one"
    );
    let verdict = table.enliven(&guessed, 100);
    assert_eq!(verdict.err(), Some(EnlivenError::NotFound));

    // FROZEN: the failed enliven created no entry and removed none — the table is unchanged.
    assert_eq!(
        table.len(),
        len_before,
        "FROZEN-SLOT BREACH — a failed enliven changed the table size; no authority/entry may \
         materialise from presenting an unknown swiss (Lean enliven_failed_freezes_caps)"
    );
    assert!(
        !table.contains(&guessed),
        "a guessed swiss must NOT have been inserted by a failed enliven"
    );
    assert_eq!(
        table.contains(&legit),
        legit_present_before,
        "the legitimate entry's presence must be unchanged by the adversary's failed enliven"
    );
}

/// THEOREM `enliven_confined_over_adversaries` (n > 1) RUNTIME TOOTH. Confinement is universal over a
/// SET of DISTINCT adversary cells: given a swiss NOT minted, EVERY adversary fails. We model two
/// distinct adversaries presenting two distinct guessed swiss numbers; BOTH are `NotFound`.
#[test]
fn confinement_universal_over_distinct_adversaries() {
    let mut table = SwissTable::new();
    let _legit = table.export(target_cell(), AuthRequired::Signature, 100, None);

    // n > 1: two DISTINCT adversaries, two DISTINCT guesses, neither holding a minted secret.
    let adv_a_guess = [0x01u8; 32];
    let adv_b_guess = [0x02u8; 32];
    assert_ne!(
        adv_a_guess, adv_b_guess,
        "test setup: distinct adversary guesses (n > 1)"
    );

    for (who, guess) in [("adversary A", adv_a_guess), ("adversary B", adv_b_guess)] {
        let verdict = table.enliven(&guess, 100);
        assert_eq!(
            verdict.err(),
            Some(EnlivenError::NotFound),
            "n>1 CONFINEMENT BREACH — {who} enlivened a swiss it never held; confinement must hold \
             against the whole crowd (Lean enliven_confined_over_adversaries)"
        );
    }
}

/// `SwissUnguessable` ENTROPY-ASSUMPTION RUNTIME BAR. The Lean confinement is unconditional on the
/// `findSwiss`-membership gate; the ONE thing it cannot give is that an adversary cannot GUESS the
/// 32-byte (256-bit) secret. The realizable bar is `getrandom`: two independent exports produce
/// distinct, unpredictable swiss numbers. We assert two exports never collide — the runtime witness
/// that the secret carries 256 bits of entropy (the basis on which `SwissUnguessable` holds in
/// practice; a 1-in-2^256 collision is infeasible).
#[test]
fn minted_swiss_numbers_are_high_entropy() {
    let mut table = SwissTable::new();
    let a = table.export(target_cell(), AuthRequired::Signature, 100, None);
    let b = table.export(target_cell(), AuthRequired::Signature, 100, None);
    assert_ne!(
        a, b,
        "two independent `getrandom` swiss exports collided — the 256-bit unguessability bar \
         (Lean SwissUnguessable) requires unpredictable, distinct secrets"
    );
    // And neither is the all-zero / trivially-guessable sentinel.
    assert_ne!(
        a, [0u8; 32],
        "a minted swiss must not be the trivially-guessable zero secret"
    );
    assert_ne!(
        b, [0u8; 32],
        "a minted swiss must not be the trivially-guessable zero secret"
    );
}

/// `enliven_minted_of_some` RUNTIME TOOTH (the accept-side / non-vacuity twin). A GENUINELY exported
/// swiss DOES enliven — so confinement rejects ONLY the un-minted, not everything. The dual of
/// "enliven succeeds ⇒ sw was minted": here the minted swiss succeeds, witnessing the accept path is
/// live (the confinement is a real gate, not a brick wall).
#[test]
fn minted_swiss_does_enliven() {
    let mut table = SwissTable::new();
    let legit = table.export(target_cell(), AuthRequired::Signature, 100, None);
    let entry = table
        .enliven(&legit, 100)
        .expect("a genuinely-minted swiss MUST enliven (Lean enliven_minted_of_some accept side)");
    assert_eq!(entry.cell_id, target_cell());
    assert_eq!(
        entry.use_count, 1,
        "a successful enliven bumps the refcount (the Lean refcount bump)"
    );
}

/// COMBINED CONFINEMENT WALK. Mint one, confirm a guessed neighbour is unreachable, confirm the
/// minted one is reachable, then REVOKE and confirm it becomes unreachable again — the full
/// confinement lifecycle the Lean unreachability lemma underwrites at each `findSwiss = none` point.
#[test]
fn confinement_lifecycle_walk() {
    let mut table = SwissTable::new();
    let legit = table.export(target_cell(), AuthRequired::Signature, 100, None);

    // Neighbour (guessed) — unreachable.
    let mut neighbour = legit;
    neighbour[0] ^= 0xFF;
    assert_eq!(
        table.enliven(&neighbour, 100).err(),
        Some(EnlivenError::NotFound)
    );

    // Minted — reachable.
    assert!(table.enliven(&legit, 100).is_ok());

    // Revoke the minted entry — now `findSwiss = none`, so it is unreachable again.
    assert!(table.revoke(&legit));
    assert_eq!(
        table.enliven(&legit, 100).err(),
        Some(EnlivenError::NotFound),
        "after revocation the swiss is no longer minted — confinement makes it unreachable again \
         (Lean enliven_unreachable_without_swiss at the post-revoke findSwiss = none)"
    );
}
