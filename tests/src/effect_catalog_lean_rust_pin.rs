//! The Lean effect catalog and the Rust `Effect` enum must describe the SAME vocabulary.
//!
//! ═══ THE WOUND THIS CLOSES ═══════════════════════════════════════════════════════
//! Measured 2026-07-28. `metatheory/Dregg2/CatalogInstances.lean`'s `EffectKind` colored
//! 52 effect kinds. `turn/src/action.rs`'s `Effect` had 36 variants. **The overlap was
//! 27.** Twenty-five kinds existed only in Lean (the whole bridge / queue / escrow /
//! obligation / CapTP-sturdy-ref families, dissolved by the verb-reduction campaign) and
//! nine only in Rust — including `Mint` and `ShieldedTransfer`, i.e. **the Lean theory did
//! not classify two of the effects whose conservation matters most.**
//!
//! The catalog's own docstring said it was "transcribed verbatim from `Effect::linearity`
//! (`turn/src/action.rs:1675`)" — a function DELETED that same day, at a line number that
//! had been wrong for far longer.
//!
//! ═══ WHY THE EXISTING TRIPWIRE COULD NOT CATCH IT ════════════════════════════════
//! `CatalogEffects §2` carries a per-effect `rfl` for every kind, advertised as a tripwire
//! against coloring drift. It is a real tripwire and it works — **on Lean edits.** Nothing
//! in it observes `turn/src/action.rs`. A Rust variant could be added, renamed or deleted
//! and every `rfl` stayed green, which is exactly how both sides drifted unobserved for a
//! design generation.
//!
//! A one-sided pin is the shape this repo has closed repeatedly: a comment claiming a gate
//! is armed, a fixture standing in for a caller, a mirror that only fires on a path nobody
//! takes. So this check READS BOTH SOURCES AS TEXT and compares the vocabularies. Same
//! shape as `cell/tests/fields_root_reserved_band_pin.rs`, and for the same reason stated
//! there: "a test asserting `STATE_SLOTS == 16` would pin ONE side; the drift that happened
//! is the two sides moving independently, which only a check that READS BOTH can catch."
//!
//! ═══ WHAT IT ASSERTS ═════════════════════════════════════════════════════════════
//! The symmetric difference must equal the two rosters below EXACTLY — no extra, no
//! missing, in either direction. Adding a variant to either side goes red until it is
//! either mirrored on the other side or written into the roster with a reason. The rosters
//! are a DECLARATION of known divergence, not a mute allowlist: each entry says why.
//!
//! ⚠ This pins the VOCABULARY, not the coloring. There is no Rust coloring left to compare
//! against — `Effect::linearity` was deleted as a dead hand-maintained twin of the Lean
//! theory (the LAW: AIR/constraint/classification logic is authored in Lean). The coloring
//! is pinned on the Lean side by `CatalogEffects §2`'s `rfl`s. What this file adds on the
//! Rust side is the one coloring fact the executor can actually be asked: that a `Burn`
//! CONSERVES — see `burn_is_a_conserving_holder_to_well_move` at the bottom.

use std::collections::BTreeSet;

/// The Lean module that owns `EffectKind` (the spec-side effect vocabulary).
const LEAN_CATALOG: &str = "../metatheory/Dregg2/CatalogInstances.lean";
/// The Rust module that owns `Effect` (the deployed effect vocabulary).
const RUST_ACTION: &str = "../turn/src/action.rs";

/// Kinds the LEAN catalog colors that the Rust `Effect` does not have.
///
/// These are the verb families dissolved by the dregg3 verb-reduction campaign (see the
/// same note in `every_variant_roundtrip.rs`: "their `Effect` variants no longer exist, so
/// they are absent from the table below — the coverage loss is the deletion of those verbs").
/// The Lean theory keeps them because several downstream modules
/// (`Exec/EffectsPaired`, `Exec/EffectsSupply`, `Verify/QueueFactoryProbe`) instantiate
/// their conservation templates over these kinds, and `bridgeFinalize` in particular is the
/// SOLE witness of the `Annihilative` color after the 2026-07-28 burn recoloring.
const LEAN_ONLY: &[&str] = &[
    // CapTP seal/sturdy-ref lifecycle.
    "createSealPair",
    "seal",
    "unseal",
    "exportSturdyRef",
    "enlivenRef",
    "dropRef",
    "validateHandoff",
    // Bridge phases. `bridgeFinalize` is load-bearing: it is the only `Annihilative` kind.
    "bridgeLock",
    "bridgeFinalize",
    "bridgeCancel",
    // Queue family.
    "queueAllocate",
    "queueEnqueue",
    "queueDequeue",
    "queueResize",
    "queueAtomicTx",
    "queuePipelineStep",
    // Escrow family (plain + committed).
    "createEscrow",
    "releaseEscrow",
    "refundEscrow",
    "createCommittedEscrow",
    "releaseCommittedEscrow",
    "refundCommittedEscrow",
    // Obligation family.
    "createObligation",
    "fulfillObligation",
    "slashObligation",
];

/// Variants the Rust `Effect` has that the Lean catalog does not color.
///
/// ⚑ Every one of these is an UNCOLORED DEPLOYED VERB — the spec has no conservation
/// reading of it. That is a real residual, not a benign gap, and this roster is where it is
/// visible. `Mint` came OFF this list on 2026-07-28 (it is now `EffectKind.mint`,
/// `Conservative`); `ShieldedTransfer` is the remaining value-moving entry and is the next
/// one that should leave.
const RUST_ONLY: &[&str] = &[
    // Value-moving, uncolored. The Pedersen conservation proof rides the payload, so the
    // honest color is Conservative — but stating that in Lean means modelling the committed
    // note domain, which the catalog does not yet do.
    "ShieldedTransfer",
    // Reactive vocabulary (Track 2). Their own doc comments assert colors
    // ("Generative: it creates a hole", "Terminal: one-way consume of the hole") which
    // nothing in Lean has checked.
    "Promise",
    "Notify",
    "React",
    // Cell/program administration — no resource delta, so Neutral is the expected color.
    "SetProgram",
    "CreateHybridCell",
    "RotatePqIdentity",
    // THE CUSTOM-VK DOOR. Deliberately uncolored: a custom program's resource semantics are
    // program-defined, so assigning one linearity color to `Custom` would be a claim about
    // every program that ever rides it. See the custom-effect carve-out.
    "Custom",
];

// ---------------------------------------------------------------------------
// parsers — pure functions over source text, so the red-proofs below can feed
// them doctored input without mutating the shared working tree.
// ---------------------------------------------------------------------------

/// Comparison key: case- and separator-insensitive, so Lean `rotatePqIdentity` and Rust
/// `RotatePqIdentity` are the same symbol without a hand-written acronym table.
fn key(name: &str) -> String {
    name.chars()
        .filter(|c| c.is_ascii_alphanumeric())
        .map(|c| c.to_ascii_lowercase())
        .collect()
}

/// Extract the constructor names of Lean's `inductive EffectKind`.
///
/// Deliberately anchored on the `inductive` line rather than grepping for the identifier:
/// `EffectKind` appears in a dozen doc comments in that file, and matching prose is how a
/// reader reports a vocabulary nobody wrote.
pub fn lean_effect_kinds(src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut inside = false;
    for line in src.lines() {
        let t = line.trim();
        if !inside {
            if t.starts_with("inductive EffectKind") {
                inside = true;
            }
            continue;
        }
        if t.starts_with("deriving") {
            break;
        }
        // Strip Lean line comments before looking for `|` — the constructor block carries
        // explanatory `--` comments that mention constructor names in prose.
        let code = t.split("--").next().unwrap_or("").trim();
        if !code.starts_with('|') {
            continue;
        }
        for piece in code.split('|') {
            let name: String = piece
                .trim()
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() {
                out.insert(name);
            }
        }
    }
    out
}

/// Extract the variant names of Rust's `pub enum Effect { .. }`.
///
/// Walks brace/paren depth so field types and nested braces cannot be mistaken for
/// variants, and skips doc comments, line comments and attributes.
pub fn rust_effect_variants(src: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut inside = false;
    let mut depth: i32 = 0;
    for line in src.lines() {
        let t = line.trim();
        if !inside {
            if t.starts_with("pub enum Effect {") {
                inside = true;
            }
            continue;
        }
        let is_comment = t.starts_with("//");
        let is_attr = t.starts_with("#[");
        if !is_comment && !is_attr && depth == 0 {
            let name: String = t
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() && name.starts_with(|c: char| c.is_ascii_uppercase()) {
                out.insert(name);
            }
        }
        if !is_comment {
            for c in t.chars() {
                match c {
                    '{' | '(' | '[' => depth += 1,
                    '}' | ')' | ']' => {
                        depth -= 1;
                        // The enum's own closing brace takes us to -1.
                        if depth < 0 {
                            return out;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

fn read(path: &str) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| {
        panic!(
            "cannot read {path}: {e}. This pin compares the Lean effect catalog against the \
             deployed Rust `Effect` enum; if the module moved, RE-POINT it rather than deleting \
             the check — an unread pin is the drift it exists to catch."
        )
    })
}

fn keyset(names: impl IntoIterator<Item = String>) -> BTreeSet<String> {
    names.into_iter().map(|n| key(&n)).collect()
}

// ---------------------------------------------------------------------------
// the pin
// ---------------------------------------------------------------------------

/// The four ways the two vocabularies can disagree, computed over source TEXT so the
/// red-proof can drive it with doctored input instead of mutating the shared tree.
///
/// Returns `(undeclared_lean_only, stale_lean_roster, undeclared_rust_only,
/// stale_rust_roster)`. All four empty ⇔ the pin is green.
pub fn divergence(
    lean_src: &str,
    rust_src: &str,
) -> (Vec<String>, Vec<String>, Vec<String>, Vec<String>) {
    let lean = keyset(lean_effect_kinds(lean_src));
    let rust = keyset(rust_effect_variants(rust_src));
    let lean_only: BTreeSet<_> = lean.difference(&rust).cloned().collect();
    let rust_only: BTreeSet<_> = rust.difference(&lean).cloned().collect();
    let declared_lean = keyset(LEAN_ONLY.iter().map(|s| s.to_string()));
    let declared_rust = keyset(RUST_ONLY.iter().map(|s| s.to_string()));
    (
        lean_only.difference(&declared_lean).cloned().collect(),
        declared_lean.difference(&lean_only).cloned().collect(),
        rust_only.difference(&declared_rust).cloned().collect(),
        declared_rust.difference(&rust_only).cloned().collect(),
    )
}

#[test]
fn lean_effect_catalog_and_rust_effect_enum_agree_modulo_the_declared_roster() {
    let lean_src = read(LEAN_CATALOG);
    let rust_src = read(RUST_ACTION);
    let lean_names = lean_effect_kinds(&lean_src);
    let rust_names = rust_effect_variants(&rust_src);

    // ANTI-VACUITY. A parser that silently matched nothing would make both differences
    // empty, and empty-vs-a-nonempty-roster would fail below — but say it out loud anyway,
    // because a check whose failure mode is "found nothing" must not be able to pass.
    assert!(
        lean_names.len() >= 40,
        "parsed only {} Lean `EffectKind` constructors — the parser lost the inductive block, \
         it did not find a shrunken catalog. Names: {lean_names:?}",
        lean_names.len()
    );
    assert!(
        rust_names.len() >= 30,
        "parsed only {} Rust `Effect` variants — the parser lost the enum body. Names: \
         {rust_names:?}",
        rust_names.len()
    );

    let lean = keyset(lean_names.iter().cloned());
    let rust = keyset(rust_names.iter().cloned());

    let (unexpected_lean, stale_lean, unexpected_rust, stale_rust) =
        divergence(&lean_src, &rust_src);

    assert!(
        unexpected_lean.is_empty()
            && stale_lean.is_empty()
            && unexpected_rust.is_empty()
            && stale_rust.is_empty(),
        "\nTHE LEAN EFFECT CATALOG AND THE DEPLOYED `Effect` ENUM DESCRIBE DIFFERENT \
         VOCABULARIES.\n\n  \
           Lean  metatheory/Dregg2/CatalogInstances.lean::EffectKind = {nl} kinds\n  \
           Rust  turn/src/action.rs::Effect                          = {nr} variants\n  \
           overlap                                                   = {no}\n\n\
         UNDECLARED Lean-only (colored by the spec, absent from the executor): {unexpected_lean:?}\n\
         STALE roster entries claiming Lean-only (no longer Lean-only): {stale_lean:?}\n\
         UNDECLARED Rust-only (deployed but UNCOLORED by the spec): {unexpected_rust:?}\n\
         STALE roster entries claiming Rust-only (no longer Rust-only): {stale_rust:?}\n\n\
         A Rust-only variant is a deployed verb with NO conservation reading in the spec. A \
         Lean-only kind is a theorem about an effect the executor cannot produce. Either \
         mirror the variant on the other side, or add it to LEAN_ONLY / RUST_ONLY in this \
         file WITH THE REASON — the roster is a declaration of known divergence, not a mute \
         allowlist.\n",
        nl = lean.len(),
        nr = rust.len(),
        no = lean.intersection(&rust).count(),
    );
}

/// The rosters must not name something both sides have — a stale entry that silently
/// "explains" a divergence that closed is how an allowlist outlives its subject.
#[test]
fn the_divergence_rosters_do_not_overlap_each_other() {
    let l = keyset(LEAN_ONLY.iter().map(|s| s.to_string()));
    let r = keyset(RUST_ONLY.iter().map(|s| s.to_string()));
    let both: Vec<_> = l.intersection(&r).cloned().collect();
    assert!(
        both.is_empty(),
        "a name cannot be both Lean-only and Rust-only: {both:?}"
    );
}

// ---------------------------------------------------------------------------
// RED-PROOFS — both poles, over doctored source text, so the shared tree is
// never mutated to demonstrate them.
// ---------------------------------------------------------------------------

/// The Lean parser must find the real catalog AND must go red on a real edit. Both poles:
/// a source where the kind is present, and the same source with it removed.
#[test]
fn lean_parser_tracks_the_actual_inductive_both_ways() {
    let real = read(LEAN_CATALOG);
    let present = lean_effect_kinds(&real);
    assert!(
        present.contains("burn") && present.contains("mint") && present.contains("transfer"),
        "the live catalog must contain the supply pair and transfer; got {present:?}"
    );

    // POLE 2: delete a constructor from a COPY of the text. The parser must notice.
    let doctored = real.replace(" | burn | attenuateCapability", " | attenuateCapability");
    assert_ne!(
        doctored, real,
        "the doctoring substitution matched nothing — the red-proof would be vacuous, so the \
         inductive's layout changed and this proof must be re-pointed, not deleted"
    );
    let after = lean_effect_kinds(&doctored);
    assert!(
        !after.contains("burn"),
        "removing `burn` from the source did not change what the parser reports — the parser \
         is not reading the inductive, and this whole pin would be decorative"
    );

    // And a comment MENTIONING a constructor must not be mistaken for one. This is the
    // failure the anchored parse exists to prevent, and the block really does carry prose.
    let commented = real.replace(
        "inductive EffectKind where",
        "inductive EffectKind where\n  -- | phantomKind is only mentioned in prose",
    );
    assert!(
        !lean_effect_kinds(&commented).contains("phantomKind"),
        "a `--` comment was parsed as a constructor"
    );
}

/// Same discipline for the Rust side: it must see the real enum, and must go red when a
/// variant is added or removed in the text it is given.
#[test]
fn rust_parser_tracks_the_actual_enum_both_ways() {
    let real = read(RUST_ACTION);
    let present = rust_effect_variants(&real);
    assert!(
        present.contains("Burn") && present.contains("Mint") && present.contains("Transfer"),
        "the deployed enum must contain the supply pair and Transfer; got {present:?}"
    );
    assert!(
        !present.contains("Effect"),
        "the type's own name leaked in as a variant — the depth walk is wrong"
    );

    // POLE 2: append a variant to a COPY. The parser must see it.
    let marker = "    RotatePqIdentity {";
    assert!(
        real.contains(marker),
        "the last-variant anchor moved; re-point this red-proof rather than deleting it"
    );
    let doctored = real.replacen(marker, "    PhantomVariant {\n        x: u64,\n    },\n", 1);
    let after = rust_effect_variants(&doctored);
    assert!(
        after.contains("PhantomVariant"),
        "adding a variant to the source did not change what the parser reports — the parser is \
         not reading the enum, so a Rust-side addition could never turn this pin red"
    );
}

// ---------------------------------------------------------------------------
// THE COLORING FACT THE EXECUTOR CAN BE ASKED
// ---------------------------------------------------------------------------

/// `EffectKind.burn` was colored `Annihilative` — *disclosed non-conservation* — until
/// 2026-07-28. This is the executor-side evidence that `Conservative` is the right color:
/// a burn moves value from the holder to the asset's issuer WELL, so the ledger sum is
/// INVARIANT across it.
///
/// Both poles, so the invariance cannot be read as "nothing happened":
///   * the total over every cell is UNCHANGED (the conservation claim), and
///   * the burner's own balance strictly DECREASED (the effect really ran).
///
/// A one-sided destroy — the pre-well `Annihilative` reading — would fail the first.
/// A no-op would fail the second.
#[test]
fn burn_is_a_conserving_holder_to_well_move() {
    use dregg_cell::{AuthRequired, Cell, Ledger, Permissions};
    use dregg_turn::{ComputronCosts, Effect, TurnExecutor};

    fn open_cell(seed: u8, balance: i64) -> Cell {
        let mut pk = [0u8; 32];
        pk[0] = seed;
        pk[31] = seed.wrapping_mul(37);
        let mut cell = Cell::with_balance(pk, [0u8; 32], balance);
        cell.permissions = Permissions {
            send: AuthRequired::None,
            receive: AuthRequired::None,
            set_state: AuthRequired::None,
            set_permissions: AuthRequired::None,
            set_verification_key: AuthRequired::None,
            increment_nonce: AuthRequired::None,
            delegate: AuthRequired::None,
            access: AuthRequired::None,
        };
        cell
    }

    // i128 so a NEGATIVE well (the `-supply` account the model calls for once wells are
    // initialized at issuance) cannot silently wrap the sum.
    fn ledger_total(ledger: &Ledger) -> i128 {
        ledger
            .iter()
            .map(|(_, c)| i128::from(c.state.balance()))
            .sum()
    }

    const START: i64 = 1_000;
    const BURN: u64 = 250;

    let burner = open_cell(0x71, START);
    let burner_id = burner.id();
    let mut ledger = Ledger::new();
    ledger.insert_cell(burner).unwrap();

    let before_total = ledger_total(&ledger);
    let before_burner = ledger.get(&burner_id).unwrap().state.balance();
    assert_eq!(before_burner, START);

    let mut builder = dregg_turn::TurnBuilder::new(burner_id, 0);
    builder.add_action(
        dregg_turn::ActionBuilder::new_unchecked_for_tests(burner_id, "burn", burner_id)
            .effect(Effect::Burn {
                target: burner_id,
                slot: 0,
                amount: BURN,
            })
            .build(),
    );
    let turn = builder.fee(0).build();

    let result = TurnExecutor::new(ComputronCosts::zero()).execute(&turn, &mut ledger);
    assert!(
        result.is_committed(),
        "the burn must COMMIT for either pole to mean anything; got: {result:?}"
    );

    let after_total = ledger_total(&ledger);
    let after_burner = ledger.get(&burner_id).unwrap().state.balance();

    // POLE 1 — the effect really ran (not a silent no-op).
    assert_eq!(
        after_burner,
        START - BURN as i64,
        "the burner's balance must fall by exactly the burned amount"
    );

    // POLE 2 — and the ledger sum is INVARIANT: the debit was paired by a credit to the
    // asset's issuer well. This is `Conservative`, not `Annihilative`.
    assert_eq!(
        after_total, before_total,
        "\nBURN DID NOT CONSERVE.\n  ledger total before = {before_total}\n  \
           ledger total after  = {after_total}\n\n\
         `metatheory/Dregg2/CatalogInstances.lean` colors `EffectKind.burn` `Conservative` \
         (`burn_requires_paired`, `burn_not_annihilative`) on the strength of this: post-W1 \
         `apply_burn` debits the holder and credits `issuer_well_for(target)`, and the well is \
         a real cell inside the per-asset conservation walk. If a burn stops conserving, that \
         Lean color is wrong and `Annihilative` should come back — do not weaken this \
         assertion to keep the color.\n"
    );

    // The counterparty must actually exist — a total that balances because the executor
    // refused to write anywhere would be a different story.
    assert!(
        ledger.iter().count() >= 2,
        "the conserving half of the burn must be a REAL cell (the lazily-created issuer well); \
         the ledger still holds only the burner"
    );
}

/// ⚑ **THE PIN ITSELF MUST BE ABLE TO GO RED — all four ways.**
///
/// The parser red-proofs above show the two readers track their sources. This one shows the
/// COMPARISON turns red, which is the property that actually matters: a check whose failure
/// mode is unreachable is not a check. Every mutation is applied to an in-memory COPY of the
/// source text, so no lane compiling concurrently ever sees a broken tree.
#[test]
fn the_pin_goes_red_on_a_change_to_either_side() {
    let lean_src = read(LEAN_CATALOG);
    let rust_src = read(RUST_ACTION);

    // Baseline: green as committed. Without this the four reds below prove nothing —
    // a permanently-red check "detects" everything.
    let (a, b, c, d) = divergence(&lean_src, &rust_src);
    assert!(
        a.is_empty() && b.is_empty() && c.is_empty() && d.is_empty(),
        "baseline must be GREEN for the red-proof to mean anything: {a:?} {b:?} {c:?} {d:?}"
    );

    // (1) A NEW Lean kind with no Rust counterpart — the spec growing a verb the executor
    //     cannot produce. This is the direction the 25 orphans came from.
    let lean_grown = lean_src.replace(
        "  | receiptArchive
",
        "  | receiptArchive | phantomLeanVerb
",
    );
    assert_ne!(lean_grown, lean_src, "anchor for mutation (1) moved");
    let (u, _, _, _) = divergence(&lean_grown, &rust_src);
    assert_eq!(
        u,
        vec!["phantomleanverb".to_string()],
        "a new UNMIRRORED Lean kind must be reported as undeclared Lean-only"
    );

    // (2) A Lean kind DELETED while the roster still claims it — the stale-allowlist
    //     direction, where an entry outlives its subject.
    let lean_shrunk = lean_src.replace(" | bridgeLock | bridgeFinalize | bridgeCancel", "");
    assert_ne!(lean_shrunk, lean_src, "anchor for mutation (2) moved");
    let (_, stale, _, _) = divergence(&lean_shrunk, &rust_src);
    assert_eq!(
        stale.len(),
        3,
        "deleting three rostered Lean kinds must report three STALE roster entries, got {stale:?}"
    );

    // (3) A NEW Rust variant the spec does not color — a deployed verb with no conservation
    //     reading. THE `rfl` TRIPWIRE IN LEAN CANNOT SEE THIS AT ALL; it is the whole reason
    //     this file exists.
    let rust_grown = rust_src.replacen(
        "    RotatePqIdentity {",
        "    PhantomDeployedVerb {
        x: u64,
    },
    RotatePqIdentity {",
        1,
    );
    assert_ne!(rust_grown, rust_src, "anchor for mutation (3) moved");
    let (_, _, undeclared, _) = divergence(&lean_src, &rust_grown);
    assert_eq!(
        undeclared,
        vec!["phantomdeployedverb".to_string()],
        "a new UNCOLORED Rust variant must be reported as undeclared Rust-only"
    );

    // (4) A Rust variant RENAMED — the silent case, where counts stay equal on both sides
    //     and only a name-level comparison notices. It must show up in BOTH directions.
    let rust_renamed = rust_src.replacen("    Burn {", "    Incinerate {", 1);
    assert_ne!(rust_renamed, rust_src, "anchor for mutation (4) moved");
    let (u4, _, r4, _) = divergence(&lean_src, &rust_renamed);
    assert_eq!(
        u4,
        vec!["burn".to_string()],
        "renaming Rust `Burn` must orphan the Lean `burn` kind"
    );
    assert_eq!(
        r4,
        vec!["incinerate".to_string()],
        "renaming Rust `Burn` must surface the new name as uncolored"
    );
}
