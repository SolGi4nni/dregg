//! # The note↔order adapter — a REAL shielded clearing over REAL pool notes.
//!
//! This closes the single highest-leverage seam named in
//! `docs/deos/SHIELDED-DEPOSIT-BRIDGE.md` stage (c): the wire that turns two
//! ALREADY-PROVEN stages — the shielded HOLD (stage (b), `ShieldedValue.lean §6`
//! + `RealCrypto.lean`, real Poseidon2 notes) and the private CLEAR (stage (c),
//! `fhegg-solver`'s uniform-price crossing + `Allocation::conserves`) — into a
//! single SHIELDED CLEARING OVER POOL NOTES. It needs NO new crypto: both halves'
//! primitives are real; the adapter is the translation between their data shapes.
//!
//! ## The three adapter pieces (this file)
//!
//!   * [`note_to_order`] — seal a pool [`BoundNote`] (its hidden value bound under
//!     the Poseidon2 commitment `value_binding = hash_fact(value,[asset,rand,0])`,
//!     the spend circuit's C7 / `RealCrypto §1.3`) as a REAL `fhegg_solver`
//!     `Order`. The order's economic terms (side, qty = the note's value, price
//!     limit) are the note's; the sealed order REFERENCES the note's commitment +
//!     nullifier so the clearing runs over real pool notes, not abstract orders.
//!   * [`order_to_note`] — mint each cleared FILL as a fresh conserving output
//!     note: a FILL note of value = the allocated fill, plus a CHANGE note of
//!     value = (order qty − fill), each a fresh [`BoundNote`] with a fresh
//!     Poseidon2 commitment + value-binding + nullifier. The two output notes of
//!     an input sum EXACTLY to the input's value (no value minted across a spend).
//!   * [`check_conservation`] — the load-bearing soundness seam. Recomputes, from
//!     the notes + the fills, that the clearing over notes CONSERVES:
//!       (1) NO-MINT (per asset): Σ input-note value = Σ output-note value — the
//!           Rust mirror of `ShieldedValue.lean created_value_conservation`
//!           (`Σ commit = commit(Σ value)`), the "created no value" invariant;
//!       (2) CROSSING (per asset): Σ bid FILL notes = Σ ask FILL notes = V* — the
//!           Rust mirror of `fhegg` `Allocation::conserves` (`buy == sell == V*`);
//!       (3) each output note is VALUE-BOUND (its `value_binding` recomputes to its
//!           claimed value — a value-mismatch note forces a HashCR collision);
//!       (4) every input nullifier is consumed exactly once (no double-spend).
//!
//! ## What is REAL here (no mock, no minting-across-the-seam)
//!
//!   * The notes are REAL Poseidon2 `BoundNote`s — the exact `hash_fact`
//!     value-binding / leaf / nullifier the shielded spend circuit binds
//!     (`shielded_deposit_bridge_poc.rs`). ⚠ This line cited `shielded/spend_circuit.rs`
//!     C6/C7 until 2026-08-07; that Rust-authored AIR is deleted (house law #1) and the
//!     binding the deployed spend proves is now the 16-lane wide carrier of the
//!     Lean-emitted `dregg-shielded-spend-complete-fsi2::v1`, NOT the one-felt C7 these
//!     notes carry. So the notes here are real Poseidon2 objects, but they are no longer
//!     the same shape any live circuit binds.
//!   * The clearing is the REAL `fhegg_solver::clearing::{clear, allocate}` —
//!     the uniform-price fold + volume-maximising crossing + conserving pro-rata
//!     allocation, run over the ORDERS the adapter seals from actual notes. NOT an
//!     abstract/mock clear.
//!   * The conservation `Σ in = Σ out = V*` is GENUINELY recomputed from the notes
//!     and the fills; a minted output note (Σ out > Σ in) and a value-mismatch note
//!     are each REJECTED — this is soundness, not a display.
//!
//! ## Honest scope (per the bridge map)
//!
//! This brick closes stage (c)'s note↔order SEAM — a real shielded clearing over
//! real pool notes, conserving. It does NOT build: the deposit LC→mint glue (stage
//! (a)), the settle-back output-note→unshield→release (stage (d)), or the
//! persistent federation for the no-viewer MPC (ember-gated). Those remain, named.

use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;
use fhegg_solver::clearing::{Order, Side, allocate, clear};
use std::collections::BTreeMap;

/// Map a `u64` into BabyBear (the note fields are conceptually field elements).
fn felt(v: u64) -> BabyBear {
    BabyBear::new((v % (BABYBEAR_P as u64)) as u32)
}

// ---------------------------------------------------------------------------
// The pool BoundNote — REAL Poseidon2 commitments (mirrors ShieldedValue.lean
// `BoundNote` + the spend circuit C6/C7, exactly as `shielded_deposit_bridge_poc`).
// ---------------------------------------------------------------------------

/// A pool note: a hidden `(value, asset)` bound under the Poseidon2 commitment.
#[derive(Clone, Debug)]
struct BoundNote {
    /// Leaf commitment (C6): `hash_fact(value, [asset, owner, randomness])`.
    leaf: BabyBear,
    /// PQ value-binding (C7 / `RealCrypto §1.3`): `hash_fact(value,[asset,rand,0])`
    /// — binds `(value, asset)` jointly under Poseidon2 collision-resistance.
    value_binding: BabyBear,
    /// Spend nullifier: `hash_fact(leaf, [key, 0, 0, 0])`.
    nullifier: BabyBear,
    /// The hidden amount (lives only in the witness; never published in the clear).
    value: u64,
    /// The asset class.
    asset: u64,
    // The blinding inputs (witness) — retained so `order_to_note` can mint fresh,
    // distinct commitments and so the value-binding can be re-checked.
    owner: u64,
    randomness: u64,
    key: u64,
}

/// Compute the REAL Poseidon2 facts for a note `(asset, value)` blinded by
/// `(owner, randomness)` and keyed by `key`.
fn mint_note(asset: u64, value: u64, owner: u64, randomness: u64, key: u64) -> BoundNote {
    let v = felt(value);
    let a = felt(asset);
    let o = felt(owner);
    let r = felt(randomness);
    let leaf = hash_fact(v, &[a, o, r]);
    let value_binding = hash_fact(v, &[a, r, BabyBear::ZERO]);
    let nullifier = hash_fact(
        leaf,
        &[felt(key), BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
    );
    BoundNote {
        leaf,
        value_binding,
        nullifier,
        value,
        asset,
        owner,
        randomness,
        key,
    }
}

impl BoundNote {
    /// Re-derive the value-binding for a CLAIMED value+asset and check it matches
    /// the note's published commitment. A note whose `value` field does not open
    /// its `value_binding` is REJECTED here (binding under HashCR: a hidden mint /
    /// value-swap forces a Poseidon2 collision, `RealCrypto.mint_forces_collision`).
    fn value_binding_opens(&self) -> bool {
        let expect = hash_fact(
            felt(self.value),
            &[felt(self.asset), felt(self.randomness), BabyBear::ZERO],
        );
        expect == self.value_binding
    }
}

// ---------------------------------------------------------------------------
// note_to_order — seal a pool note as a REAL fhEgg Order (value hidden under the
// commitment; the order references the note's commitment + nullifier).
// ---------------------------------------------------------------------------

/// A pool note SEALED as an fhEgg order. The economic terms (`order`: side, qty =
/// the note's value, price-level `limit`) are the note's; the sealed order carries
/// the note's Poseidon2 commitment + nullifier + value-binding by reference, so the
/// `fhegg` clearing runs over ACTUAL pool notes.
#[derive(Clone, Debug)]
struct SealedOrder {
    /// The REAL `fhegg_solver` order the engine folds. `qty` = the note's value.
    order: Order,
    /// The pool note's leaf commitment (the value stays hidden under it).
    note_commitment: BabyBear,
    /// The pool note's spend nullifier (consumed when the clear settles).
    note_nullifier: BabyBear,
    /// The pool note's C7 value-binding (rebound on every output note).
    note_value_binding: BabyBear,
    /// The asset class the note (and its fills) carry.
    asset: u64,
    /// Blinding lineage for minting fresh, distinct output notes.
    owner: u64,
    randomness: u64,
    key: u64,
    /// The hidden value (witness), = `order.qty`.
    value: u64,
}

/// **`note_to_order`** — seal a pool `BoundNote` as an fhEgg `Order`. The order's
/// qty is the note's value (hidden under `value_binding`); `side`/`limit` are the
/// note's economic terms. The value never appears in the order in the clear — it
/// rides under the commitment, which the SealedOrder references.
fn note_to_order(note: &BoundNote, side: Side, limit: u32) -> SealedOrder {
    // Sanity: the note we seal must actually open its own value-binding (a
    // malformed note cannot be sealed into a clearing).
    assert!(
        note.value_binding_opens(),
        "note_to_order: the note's value_binding must open to its (value,asset)"
    );
    let order = Order {
        side,
        qty: note.value,
        limit,
    };
    SealedOrder {
        order,
        note_commitment: note.leaf,
        note_nullifier: note.nullifier,
        note_value_binding: note.value_binding,
        asset: note.asset,
        owner: note.owner,
        randomness: note.randomness,
        key: note.key,
        value: note.value,
    }
}

// ---------------------------------------------------------------------------
// order_to_note — mint each cleared fill as a fresh conserving output note (+ the
// change note for the unfilled remainder). Σ output = the input's value, exactly.
// ---------------------------------------------------------------------------

/// The output notes minted from one cleared sealed order.
struct FillOutput {
    /// The FILL note — value = the allocated fill (the crossed volume this order
    /// contributed). Fresh Poseidon2 commitment, value-bound to (fill, asset).
    fill_note: BoundNote,
    /// The CHANGE note — value = (order qty − fill), the unfilled remainder
    /// returned to the owner. Fresh commitment, value-bound to (change, asset).
    change_note: BoundNote,
}

/// **`order_to_note`** — mint the cleared FILL of a sealed order as a fresh output
/// note, plus a CHANGE note for the unfilled remainder. Fresh
/// `(owner, randomness, key)` blinding derived from the input's lineage give both
/// output notes DISTINCT Poseidon2 commitments + nullifiers. By construction
/// `fill + change == the input note's value` — no value is created or destroyed
/// across the note→order→note round-trip (the per-spend conservation the pool's
/// `noteCreateBound` / `created_value_conservation` enforce).
fn order_to_note(sealed: &SealedOrder, fill: u64) -> FillOutput {
    assert!(
        fill <= sealed.value,
        "order_to_note: a fill cannot exceed the sealed order's qty (no over-fill)"
    );
    let change = sealed.value - fill;
    // Fresh, distinct blinding for each output leg (domain-separated off the input
    // lineage so the two output commitments + nullifiers differ from each other and
    // from the input).
    let fill_note = mint_note(
        sealed.asset,
        fill,
        sealed.owner ^ 0xF11_1,
        sealed.randomness ^ 0xF11_1,
        sealed.key ^ 0xF11_1,
    );
    let change_note = mint_note(
        sealed.asset,
        change,
        sealed.owner ^ 0xC0_0,
        sealed.randomness ^ 0xC0_0,
        sealed.key ^ 0xC0_0,
    );
    FillOutput {
        fill_note,
        change_note,
    }
}

// ---------------------------------------------------------------------------
// The conservation seam — the load-bearing soundness check.
// ---------------------------------------------------------------------------

/// Per-asset conservation ledger for one shielded clearing.
#[derive(Debug, Default, Clone)]
struct AssetConservation {
    /// Σ input-note value for this asset.
    in_sum: u64,
    /// Σ output-note value (fills + change) for this asset.
    out_sum: u64,
    /// Σ FILL-note value on the BID side (should equal `V*`).
    bid_fill: u64,
    /// Σ FILL-note value on the ASK side (should equal `V*`).
    ask_fill: u64,
    /// The cleared volume `V*` for this asset's book.
    vstar: u64,
}

impl AssetConservation {
    /// The full soundness conjunction, per asset:
    ///   * NO-MINT: `in_sum == out_sum` (`created_value_conservation`);
    ///   * CROSSING: `bid_fill == ask_fill == vstar` (`Allocation::conserves`).
    fn conserves(&self) -> bool {
        self.in_sum == self.out_sum && self.bid_fill == self.ask_fill && self.bid_fill == self.vstar
    }
}

/// The result of checking a shielded clearing's conservation.
#[derive(Debug)]
struct ConservationReport {
    /// Per-asset ledgers.
    per_asset: BTreeMap<u64, AssetConservation>,
    /// Every output note is value-bound (opens its own commitment).
    all_value_bound: bool,
    /// Every INPUT note is value-bound: its published `value_binding` opens to the
    /// `(value, asset)` the sealed order clears (the clearing runs over REAL
    /// committed notes, not free-floating orders).
    all_inputs_bound: bool,
    /// Every input note commitment is distinct (each real pool note enters once).
    inputs_distinct: bool,
    /// Every input nullifier is consumed exactly once (no double-spend).
    no_double_spend: bool,
}

impl ConservationReport {
    /// The whole clearing conserves iff EVERY asset conserves AND every input+output
    /// note is value-bound AND inputs are distinct AND no nullifier is double-spent.
    fn valid(&self) -> bool {
        self.all_value_bound
            && self.all_inputs_bound
            && self.inputs_distinct
            && self.no_double_spend
            && self.per_asset.values().all(|a| a.conserves())
    }
}

/// **`check_conservation`** — recompute, from the sealed inputs + their fills +
/// their minted output notes, that the clearing over notes CONSERVES per asset.
/// This is the note-mint ⋈ Cert-F conservation join: Σ in = Σ out (no value
/// minted) AND Σ bid fills = Σ ask fills = V* (the crossing), per asset.
fn check_conservation(
    sealed: &[SealedOrder],
    outputs: &[FillOutput],
    vstar_by_asset: &BTreeMap<u64, u64>,
) -> ConservationReport {
    assert_eq!(
        sealed.len(),
        outputs.len(),
        "one FillOutput per sealed order"
    );
    let mut per_asset: BTreeMap<u64, AssetConservation> = BTreeMap::new();
    let mut all_value_bound = true;
    let mut all_inputs_bound = true;
    let mut inputs_distinct = true;
    // No-double-spend: every input nullifier distinct + counted once.
    let mut seen_nullifiers: Vec<BabyBear> = Vec::new();
    let mut seen_commitments: Vec<BabyBear> = Vec::new();
    let mut no_double_spend = true;

    for (s, o) in sealed.iter().zip(outputs.iter()) {
        let entry = per_asset.entry(s.asset).or_default();
        // NO-MINT ledger: input value in; fill + change out.
        entry.in_sum += s.value;
        entry.out_sum += o.fill_note.value + o.change_note.value;
        // CROSSING ledger: fills split by the order's side.
        match s.order.side {
            Side::Bid => entry.bid_fill += o.fill_note.value,
            Side::Ask => entry.ask_fill += o.fill_note.value,
        }
        // Every output note must open its value-binding (a minted / value-mismatch
        // output note fails this — HashCR binding).
        all_value_bound &= o.fill_note.value_binding_opens();
        all_value_bound &= o.change_note.value_binding_opens();

        // The INPUT note the order seals must be a real committed note: its
        // published value_binding must open to the (value, asset) being cleared,
        // and its leaf commitment must be consistent with the order's qty. This is
        // what makes the clearing run over REAL pool notes.
        let expect_binding = hash_fact(
            felt(s.value),
            &[felt(s.asset), felt(s.randomness), BabyBear::ZERO],
        );
        all_inputs_bound &= expect_binding == s.note_value_binding;
        let expect_leaf = hash_fact(
            felt(s.value),
            &[felt(s.asset), felt(s.owner), felt(s.randomness)],
        );
        all_inputs_bound &= expect_leaf == s.note_commitment;

        // Each real pool note enters the clearing once (distinct commitments).
        if seen_commitments.contains(&s.note_commitment) {
            inputs_distinct = false;
        } else {
            seen_commitments.push(s.note_commitment);
        }
        // No-double-spend: the input note's nullifier must be fresh.
        if seen_nullifiers.contains(&s.note_nullifier) {
            no_double_spend = false;
        } else {
            seen_nullifiers.push(s.note_nullifier);
        }
    }
    for (asset, entry) in per_asset.iter_mut() {
        entry.vstar = vstar_by_asset.get(asset).copied().unwrap_or(0);
    }
    ConservationReport {
        per_asset,
        all_value_bound,
        all_inputs_bound,
        inputs_distinct,
        no_double_spend,
    }
}

// ---------------------------------------------------------------------------
// Drive a single asset's book through the REAL fhEgg clear and back to notes.
// ---------------------------------------------------------------------------

/// One asset's book: input notes each already sealed to a `(side, limit)`.
struct BookInput {
    sealed: Vec<SealedOrder>,
}

/// Run the REAL `fhegg_solver` clear/allocate over the sealed notes of ONE asset,
/// mint the fills back into output notes, and return `(outputs, V*)`.
fn clear_book(book: &BookInput, k: usize) -> (Vec<FillOutput>, u64) {
    // Extract the REAL fhEgg orders from the sealed notes and run the REAL engine.
    let orders: Vec<Order> = book.sealed.iter().map(|s| s.order).collect();
    let clearing = clear(&orders, k);
    let alloc = allocate(&orders, &clearing);
    // fhegg's own conservation invariant on the allocation (sanity, its own check).
    assert!(
        alloc.conserves(),
        "the fhEgg allocation must conserve (buy == sell)"
    );
    // order_to_note: mint each fill (+ change) as a fresh output note.
    let outputs: Vec<FillOutput> = book
        .sealed
        .iter()
        .zip(alloc.fills.iter())
        .map(|(s, &fill)| order_to_note(s, fill))
        .collect();
    (outputs, clearing.cleared_volume)
}

// ===========================================================================
// The shielded-clearing PoC.
// ===========================================================================

#[test]
fn shielded_clearing_over_pool_notes_conserves() {
    println!("\n=== NOTE↔ORDER ADAPTER — a REAL shielded clearing over REAL pool notes ===\n");

    // A price grid of K = 10 levels for each book.
    const K: usize = 10;

    // -----------------------------------------------------------------------
    // Two assets, two independent books — to exercise per-asset conservation.
    //   asset 1: a genuine two-sided crossing book.
    //   asset 2: a supply-heavy book (opposite polarity; demand is the short side).
    // Each note is a REAL Poseidon2 BoundNote; each is sealed as a REAL fhEgg order.
    // -----------------------------------------------------------------------

    // asset 1 — bids willing up to levels 7,6; asks from levels 3,4. They overlap.
    let a1_notes = vec![
        (mint_note(1, 100, 0x1B0, 0xA01, 0x101), Side::Bid, 7u32),
        (mint_note(1, 50, 0x1B1, 0xA02, 0x102), Side::Bid, 6),
        (mint_note(1, 80, 0x1A0, 0xA03, 0x103), Side::Ask, 3),
        (mint_note(1, 40, 0x1A1, 0xA04, 0x104), Side::Ask, 4),
    ];
    // asset 2 — supply-heavy: one small bid (30), three big asks. Demand is short.
    let a2_notes = vec![
        (mint_note(2, 30, 0x2B0, 0xB01, 0x201), Side::Bid, 8u32),
        (mint_note(2, 100, 0x2A0, 0xB02, 0x202), Side::Ask, 2),
        (mint_note(2, 100, 0x2A1, 0xB03, 0x203), Side::Ask, 3),
        (mint_note(2, 100, 0x2A2, 0xB04, 0x204), Side::Ask, 4),
    ];

    // note_to_order: seal every pool note as a real fhEgg order.
    let book1 = BookInput {
        sealed: a1_notes
            .iter()
            .map(|(n, side, limit)| note_to_order(n, *side, *limit))
            .collect(),
    };
    let book2 = BookInput {
        sealed: a2_notes
            .iter()
            .map(|(n, side, limit)| note_to_order(n, *side, *limit))
            .collect(),
    };
    println!(
        "note_to_order: {} pool notes (asset 1) + {} pool notes (asset 2) sealed as fhEgg orders",
        book1.sealed.len(),
        book2.sealed.len()
    );

    // The REAL fhEgg clear over each asset's sealed notes → order_to_note (outputs).
    let (out1, vstar1) = clear_book(&book1, K);
    let (out2, vstar2) = clear_book(&book2, K);
    println!("REAL fhEgg clear: asset 1 V* = {vstar1}, asset 2 V* = {vstar2}");
    assert!(vstar1 > 0, "asset 1 book must cross");
    assert_eq!(
        vstar2, 30,
        "asset 2: demand (30) is the short side ⇒ V* = 30"
    );

    // Aggregate all sealed inputs + outputs across both assets for the joint check.
    let mut all_sealed = Vec::new();
    all_sealed.extend(book1.sealed.iter().cloned());
    all_sealed.extend(book2.sealed.iter().cloned());
    let mut all_outputs = Vec::new();
    all_outputs.extend(out1);
    all_outputs.extend(out2);

    let mut vstar_by_asset = BTreeMap::new();
    vstar_by_asset.insert(1u64, vstar1);
    vstar_by_asset.insert(2u64, vstar2);

    // -----------------------------------------------------------------------
    // THE CONSERVATION SEAM (positive polarity): Σ in = Σ out = V* per asset.
    // -----------------------------------------------------------------------
    let report = check_conservation(&all_sealed, &all_outputs, &vstar_by_asset);
    for (asset, a) in report.per_asset.iter() {
        println!(
            "  asset {asset}: Σin = {}, Σout = {}, bid_fill = {}, ask_fill = {}, V* = {}",
            a.in_sum, a.out_sum, a.bid_fill, a.ask_fill, a.vstar
        );
        assert!(
            a.conserves(),
            "asset {asset} must conserve: Σin == Σout AND bid_fill == ask_fill == V*"
        );
        // Explicit Σin = Σout = V* wording of the seam.
        assert_eq!(
            a.in_sum, a.out_sum,
            "NO-MINT: Σ input = Σ output (asset {asset})"
        );
        assert_eq!(
            a.bid_fill, a.vstar,
            "CROSSING: Σ bid fills = V* (asset {asset})"
        );
        assert_eq!(
            a.ask_fill, a.vstar,
            "CROSSING: Σ ask fills = V* (asset {asset})"
        );
    }
    assert!(
        report.all_value_bound,
        "every output note must be value-bound"
    );
    assert!(
        report.all_inputs_bound,
        "every input note must open its value-binding"
    );
    assert!(
        report.inputs_distinct,
        "each real pool note enters the clearing once"
    );
    assert!(
        report.no_double_spend,
        "every input nullifier consumed once"
    );
    assert!(report.valid(), "the whole shielded clearing must conserve");
    println!(
        "  [pos] genuine shielded clearing CONSERVES + every output note value-bound + no double-spend\n"
    );

    // -----------------------------------------------------------------------
    // NEGATIVE polarity #1 — a MINTED output note (value inflated across the seam).
    // We honestly re-bind the inflated value (so it PASSES the value-binding check),
    // proving conservation ITSELF is the gate: Σ out > Σ in ⇒ REJECTED.
    // -----------------------------------------------------------------------
    let mut minted_outputs: Vec<FillOutput> = Vec::new();
    minted_outputs.extend(clear_book(&book1, K).0);
    minted_outputs.extend(clear_book(&book2, K).0);
    // Inflate the first asset-1 output's FILL note by +1000 (mint value), rebinding
    // it honestly so the value-binding check cannot be what catches it.
    let victim_asset = minted_outputs[0].fill_note.asset;
    let victim_new_value = minted_outputs[0].fill_note.value + 1000;
    minted_outputs[0].fill_note = mint_note(victim_asset, victim_new_value, 0xDEAD, 0xBEEF, 0xF00D);
    let bad_report = check_conservation(&all_sealed, &minted_outputs, &vstar_by_asset);
    assert!(
        bad_report.per_asset[&victim_asset].in_sum != bad_report.per_asset[&victim_asset].out_sum,
        "a minted output note must break Σin == Σout"
    );
    assert!(
        !bad_report.valid(),
        "a minted output note (value across the seam) MUST be REJECTED"
    );
    println!("  [neg] MINTED output note (Σout > Σin, honestly re-bound) REJECTED by conservation");

    // -----------------------------------------------------------------------
    // NEGATIVE polarity #2 — a VALUE-MISMATCH output note: its `value` field does
    // not open its `value_binding` (a note claiming more than it commits to). The
    // binding check catches it (HashCR: a value-swap forces a collision).
    // -----------------------------------------------------------------------
    let mut mismatch_outputs: Vec<FillOutput> = Vec::new();
    mismatch_outputs.extend(clear_book(&book1, K).0);
    mismatch_outputs.extend(clear_book(&book2, K).0);
    // Tamper the claimed value WITHOUT recomputing the commitment: the note now
    // claims a value its Poseidon2 value_binding does not open.
    mismatch_outputs[0].fill_note.value += 7;
    assert!(
        !mismatch_outputs[0].fill_note.value_binding_opens(),
        "the tampered note must NOT open its value-binding"
    );
    let mismatch_report = check_conservation(&all_sealed, &mismatch_outputs, &vstar_by_asset);
    assert!(
        !mismatch_report.all_value_bound,
        "a value-mismatch output note must fail the value-binding check"
    );
    assert!(
        !mismatch_report.valid(),
        "a value-mismatch output note MUST be REJECTED"
    );
    println!("  [neg] VALUE-MISMATCH output note (value does not open its commitment) REJECTED");

    // -----------------------------------------------------------------------
    // NEGATIVE polarity #3 — a DOUBLE-SPEND: the same input nullifier appears twice.
    // -----------------------------------------------------------------------
    let mut dup_sealed = all_sealed.clone();
    let mut dup_outputs: Vec<FillOutput> = Vec::new();
    dup_outputs.extend(clear_book(&book1, K).0);
    dup_outputs.extend(clear_book(&book2, K).0);
    // Replay the first input (same nullifier) with a matching zero-fill output.
    dup_sealed.push(all_sealed[0].clone());
    dup_outputs.push(order_to_note(&all_sealed[0], 0));
    let dup_report = check_conservation(&dup_sealed, &dup_outputs, &vstar_by_asset);
    assert!(
        !dup_report.no_double_spend,
        "a replayed input nullifier must be caught"
    );
    assert!(!dup_report.valid(), "a double-spend MUST be REJECTED");
    println!("  [neg] DOUBLE-SPEND (replayed input nullifier) REJECTED\n");

    println!(
        "=== SEAM CLOSED — real pool notes → note_to_order → REAL fhEgg clear → order_to_note ==="
    );
    println!(
        "    Σ in = Σ out = V* per asset (real conservation); minted / mismatched / double-spent REJECTED."
    );
    println!(
        "    Remaining (bridge map): stage (a) LC→mint glue, stage (d) settle-back, the MPC federation."
    );
}
