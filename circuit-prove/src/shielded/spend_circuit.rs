//! The shielded-spend DSL circuit: membership + nullifier, p3/uni-STARK-clean.
//!
//! This is the STARK side of an M2-a shielded transfer for ONE input note,
//! authored as a `CircuitDescriptor` (data — **zero hand-written AIR**) using
//! only the constraint forms the audited `DslP3Air` symbolic arithmetization
//! supports (`Hash`, `Transition`, `Polynomial`, `Binary`, boundary
//! `PiBinding`), so it proves through the **hiding** uni-STARK path
//! ([`dregg_circuit::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`).
//!
//! # Why not reuse `dsl::note_spending` directly
//!
//! `note_spending`'s DSL trace is designed for the hand-rolled `dregg_circuit::stark`
//! prover: its commitment-preimage row and power-of-two PADDING rows do not
//! satisfy the chain-continuity `Transition` under p3's `when_transition`
//! gating (which fires on row0→row1 and on interior padding rows). That is why
//! `note_spending` is `dregg_circuit::stark`-only. Rather than perturb that shared
//! circuit, this lane authors a membership chain whose padding **forward-chains**
//! (`pad.current = prev.parent`, `pad.parent = hash_fact(pad.current,[0,0,0,0])`)
//! so the `Transition` holds on every checked row, and whose leaf IS the input
//! note commitment (no separate preimage row) so there is no row0→row1 break.
//!
//! # What it proves (in zero knowledge, openings blind)
//!
//! Given a published `(nullifier, merkle_root)` and a HIDDEN witness
//! `(leaf_commitment, spending_key[4], merkle path)`:
//! - **(b) membership:** the leaf commitment hashes up the 4-ary Merkle path to
//!   `merkle_root` — `parent = hash_fact(current, [sib0,sib1,sib2,position])` per
//!   level, chained by `next.current == local.parent`, last row's `current`
//!   pinned to `merkle_root`;
//! - **(c) nullifier:** `nullifier = hash_fact(leaf_commitment, key[0..4])`, bound
//!   UNGATED on every row (C4) and pinned to the published `nullifier` PI on row 0.
//!   ⚠ This binds the nullifier to the note; it does **not** by itself refuse a
//!   double-spend — see residual (3) below.
//!
//! ⚠⚠ **HISTORY 2026-07-30 — two defects found and REPAIRED in this commit; one
//! remains open.** What the three were:
//!
//! 1. **C4 was ERASED on the `DslP3Air` path** — not gated off, erased. C4 read
//!    `Gated{is_leaf, Hash{..}}`, and `dsl_p3_air::is_hash` matched only TOP-LEVEL
//!    hash forms, so a wrapped `Hash` got no Poseidon2 aux block, was not counted by
//!    `hash_count`, and fell to the `c => builder.assert_zero(eval_expr(c))` arm —
//!    where `eval_expr` returned `AB::Expr::ZERO` for every hash form. The emitted
//!    constraint was `assert_zero(is_leaf · 0)`: satisfied by EVERY assignment,
//!    including `is_leaf = 1`. `col::NULLIFIER` was a free cell whose only tie was
//!    the row-0 `PiBinding` to `pi[0]` — i.e. it equalled whatever the prover chose to
//!    publish. `verify_stark_side` (`transfer.rs`) verifies through exactly that path.
//!    This module's own §"IMPLEMENTATION NOTE" stated the rule three paragraphs above
//!    the constraint that broke it; it explains why C6a/C6b were split and was never
//!    applied to C4. **REPAIRED:** C4 is now an ungated per-row `Hash` over
//!    `col::LEAF_COMMIT`, and `DslP3Air::try_from_dsl` now REFUSES any descriptor with
//!    a nested hash (`DslP3Error::ErasedConstraint`) instead of erasing it.
//! 2. **`is_leaf` was pinned to nothing.** Its only constraint was `Binary{is_leaf}`,
//!    and `boundaries` held three `PiBinding`s and no `Fixed{First, IS_LEAF, 1}`. A
//!    prover setting `is_leaf = 0` on every row also discharged **C6b** (the
//!    value-theft tooth) on ALL THREE lowerings, including the two that DO honour
//!    gated hashes (`dsl/circuit.rs::evaluate_with_tables`,
//!    `shielded_spend_leaf_adapter.rs`'s `SiteSel::When`), so row 0's `current` was a
//!    free cell. **REPAIRED:** `BoundaryDef::Fixed{First, IS_LEAF, 1}` now arms C6b.
//! 3. ⚠ **STILL OPEN — the spending key is CARRIED, not BOUND.** `col::KEY0..KEY3`
//!    appear in C4 and nowhere else; `col::OWNER` appears in C6a and nowhere else; no
//!    constraint relates the two. A fresh key per spend therefore yields a fresh
//!    nullifier for the SAME note, so a nullifier SET cannot detect the replay — a
//!    double-spend survives a fully repaired C4. Closing it needs an **in-AIR owner
//!    derivation** (`owner == KDF(spending_key)` inside the circuit), which no
//!    shielded descriptor emits today. The same gap is in the Lean re-authoring
//!    (`Emit/ShieldedSpendDescriptor.lean` `lkNullifier`), and
//!    `ShieldedSpendPortResidual.emitted_nullifier_determined` carries `hk0..hk3`
//!    ("SAME key") as HYPOTHESES — it proves replay determinism, not double-spend
//!    refusal. NOT attempted here; named so it is findable.
//!
//! The Lean-authored replacement `dregg-shielded-spend-pinned-root::v1` fixes (1) and
//! (2) structurally (its `lkNullifier` is ungated per-row and it deletes `is_leaf` for
//! IR2 row boundaries), but no Rust source references that descriptor and it is absent
//! from `descriptor_by_name`'s `STATIC_GOLDENS`; it exists only as
//! `circuit/descriptors/by-name/dregg-shielded-spend-pinned-root-v1.json`. Routing this
//! module onto it remains the real cutover; the repairs above make THIS descriptor
//! honest in the meantime. (3) is open in both.
//!
//! ⚑ **FLAG DAY.** The descriptor and the trace both changed shape: C4 moved from a
//! gated row-0 hash over `CURRENT` to an ungated per-row hash over `LEAF_COMMIT`, a
//! `Fixed{First, IS_LEAF, 1}` boundary was added, and
//! `generate_shielded_spend_trace` now carries `NULLIFIER`/`KEY0..3` on every row
//! instead of row 0 only. Every previously produced shielded-spend proof no longer
//! verifies, and any recorded VK for `dregg-shielded-spend-v1` must be re-emitted.
//! Nothing holds an old one: greenfield, no persisted shielded proofs.
//!
//! The leaf commitment, key, and path live only in the witness; the hiding PCS
//! makes the proof's openings reveal nothing about them. *Owner/leaf is blind.*
//!
//! This circuit publishes a hiding Poseidon2 **value-binding**
//! `value_binding = hash_fact(value, [asset_type, randomness, 0])` (C7), computed
//! from the SAME value/asset/randomness cells the membership leaf is built from, so
//! the STARK leaf value+asset cannot float free of what the transfer actually
//! balances. ⚠ POSTURE (honest, 2026-07-21 — corrected from an overstated claim):
//! this one-felt tag is only the SHAPE of the intended PQ commitment. The current u64
//! mirror reduces value and asset modulo BabyBear p and the output is one felt, so it
//! neither binds the full u64 pair nor has a PQ-strength collision margin. On the CURRENTLY
//! DEPLOYED single-transfer path, conservation still runs through the Ristretto
//! three-generator Pedersen `commit_hidden_asset` (DLog, Shor-broken), and the
//! value_binding↔leaf link (`verify_value_link`) is checked ONLY in tests, not in
//! `apply_shielded_transfer`. The PQ cutover COMPLETES only when the deployed transfer is
//! routed through the ring-clearing apex (`shielded_ring_clearing_nleg_air`) as a 1-leg
//! ring — the approved Option-A redesign (docs/DECISION-shielded-redesign-2026-07-20.md +
//! docs/PLAN-shielded-apex-redesign-2026-07-20.md) — with faithful multi-limb inputs and
//! a wide Poseidon output. Only then can it retire Ristretto. Until then the real posture is
//! Ristretto-DLog conservation, not the PQ gate this comment previously claimed. The Rust mirror
//! `dregg_cell_crypto::value_commitment::value_link_binding` re-derives this felt.

use dregg_circuit::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use dregg_circuit::field::{BABYBEAR_P, BabyBear};
use dregg_circuit::poseidon2::hash_fact;

/// Trace column layout (width 11), one row per Merkle level (leaf→root).
pub mod col {
    /// Current hash at this level (row 0: the leaf = input note commitment).
    pub const CURRENT: usize = 0;
    pub const SIB0: usize = 1;
    pub const SIB1: usize = 2;
    pub const SIB2: usize = 3;
    /// Child position 0..3.
    pub const POSITION: usize = 4;
    /// Parent = hash_fact(current, [sib0, sib1, sib2, position]).
    pub const PARENT: usize = 5;
    /// 1 on row 0 (the leaf row, where the nullifier is bound), 0 elsewhere.
    pub const IS_LEAF: usize = 6;
    /// The nullifier (bound on row 0 to hash_fact(current, key[0..4])).
    pub const NULLIFIER: usize = 7;
    /// Spending-key limbs key[0..4] (4 of the 8 limbs suffice for a binding
    /// nullifier here; the full 8-limb derivation lives in `note_spending`).
    pub const KEY0: usize = 8;
    pub const KEY1: usize = 9;
    pub const KEY2: usize = 10;
    pub const KEY3: usize = 11;
    // --- Note-commitment preimage (the leaf is NOT a free cell). ---
    // The leaf (`current` on the leaf row) is CONSTRAINED to equal the note
    // commitment `hash_fact(value, [asset_type, owner, randomness])` (constraints
    // C6a/C6b). Without this the leaf floats free of the note's content, and a
    // spender could prove membership of an arbitrary tree leaf they did NOT
    // create (whose preimage they don't know) — value theft. With it, the leaf
    // can only be a note whose full preimage the spender knows, i.e. their own.
    //
    // IMPLEMENTATION NOTE (why an ungated Hash + a gated Equality, not one gated
    // Hash): in the `DslP3Air` p3 path a Poseidon2 `Hash` is enforced ONLY as a
    // TOP-LEVEL constraint (its aux block fires on every row); a `Hash` wrapped
    // in `Gated`/`InvertedGated` is folded through `eval_expr`, which returns ZERO
    // for hash forms — i.e. a gated Hash is NOT enforced on this path. So the
    // commitment hash is emitted UNGATED into a dedicated `LEAF_COMMIT` column
    // (the preimage limbs are carried constant on every row, so it holds
    // everywhere), and the leaf row pins `current == LEAF_COMMIT` via a
    // `Gated{is_leaf, Equality}` (a degree-1 algebraic constraint, which IS
    // enforced under gating).
    //
    // ⚑ 2026-07-30: this note was correct and was NEVER APPLIED TO C4, three
    // paragraphs below, which stayed a `Gated{Hash}` and was erased on the deployed
    // verifier for as long as it existed. C4 now follows the same recipe. And the
    // rule the note states is no longer a convention a reader must remember:
    // `DslP3Air::try_from_dsl` REFUSES a nested hash outright
    // (`DslP3Error::ErasedConstraint`), so a descriptor that ignores this note fails
    // to lower instead of lowering to nothing.
    /// Note value, bound into the leaf commitment (C6). Hidden, carried on all rows.
    pub const VALUE: usize = 12;
    /// Note asset type, bound into the leaf commitment (C6). Hidden, all rows.
    pub const ASSET_TYPE: usize = 13;
    /// Note owner field, bound into the leaf commitment (C6). Hidden, all rows.
    pub const OWNER: usize = 14;
    /// Note randomness / creation nonce, bound into the leaf (C6). Hidden, all rows.
    pub const RANDOMNESS: usize = 15;
    /// Recomputed note commitment `hash_fact(value,[asset,owner,randomness])`,
    /// bound on every row (C6a) and pinned to `current` on the leaf row (C6b).
    pub const LEAF_COMMIT: usize = 16;
    // --- Value-binding (the leaf↔Pedersen-leg VALUE LINK, C7). ---
    // The STARK witnesses the input note's `value` (col::VALUE) and binds it into
    // the membership leaf (C6). But the published transfer's value balance is
    // carried by a SEPARATE Pedersen value commitment over the SAME value. Nothing
    // tied the STARK's value to the Pedersen leg's value, so a spender could prove
    // membership of a note worth V while the Pedersen leg conserved a DIFFERENT V'.
    //
    // C7 publishes a HIDING Poseidon2 commitment to exactly the value AND asset type
    // (with the note randomness as blinding) the STARK leaf is built from:
    //   value_binding = hash_fact(value, [asset_type, randomness, 0]).
    // It is recomputed UNGATED on every row (so the p3 Poseidon2 aux block fires)
    // from the SAME col::VALUE / col::ASSET_TYPE / col::RANDOMNESS cells C6 binds into
    // the leaf, then pinned to a public input. Because those are the cells the leaf
    // commitment already constrains, the published `value_binding` is provably a
    // commitment to the very value AND asset this spend's membership leaf encodes — it
    // cannot float free of them.
    //
    // PQ CUTOVER TARGET (Option A): after a faithful multi-limb input encoding and a
    // wide commitment output replace this one-felt tag, the same in-AIR structure can
    // become the authoritative shielded value commitment. Today both u64 inputs are
    // represented by one BabyBear felt and the output is one felt; the off-circuit Rust
    // mirror reduces them modulo p. It therefore neither binds full u64 values nor has a
    // PQ-strength collision margin, and it has not retired the live Ristretto path.
    // The Rust mirror
    // `dregg_cell_crypto::value_commitment::value_link_binding(value, asset_type,
    // randomness)` re-derives this felt.
    /// Value-binding commitment `hash_fact(value, [asset_type, randomness, 0])`,
    /// recomputed every row (C7a) from the leaf's own value/asset/randomness cells and
    /// pinned to PI[VALUE_BINDING] (C7b). This is a one-felt cutover prototype,
    /// not yet an authoritative full-u64/PQ-strength commitment.
    pub const VALUE_BINDING: usize = 17;
    /// Trailing constant-zero pad so the `value_binding` hash absorbs exactly
    /// `[asset_type, randomness, 0]`.
    pub const VB_PAD0: usize = 18;
    /// Vestigial zeroed layout column (was the 3rd absorbed term before the asset_type
    /// cutover; retained at index 19 to keep the trace width stable).
    pub const VB_PAD1: usize = 19;
}

/// Trace width.
pub const WIDTH: usize = 20;

/// Public-input indices: `[nullifier, merkle_root, value_binding]`.
pub mod pi {
    pub const NULLIFIER: usize = 0;
    pub const MERKLE_ROOT: usize = 1;
    /// Hiding Poseidon2 commitment binding the input note's value AND asset type
    /// (with the note randomness as blinding): `hash_fact(value, [asset_type,
    /// randomness, 0])`. One-felt cutover prototype; not a full-u64/PQ-strength
    /// commitment. Re-derived off-circuit by
    /// `dregg_cell_crypto::value_commitment::value_link_binding`.
    pub const VALUE_BINDING: usize = 2;
}

/// Number of public inputs.
pub const PUBLIC_INPUT_COUNT: usize = 3;

/// Build the shielded-spend circuit descriptor.
///
/// Constraints (all DslP3Air-supported):
/// - C1: `is_leaf` is binary.
/// - C2: position validity `pos*(pos-1)*(pos-2)*(pos-3) == 0` (degree 4).
/// - C3: Merkle hash binding `parent == hash_fact(current,[sib0,sib1,sib2,pos])`
///   (every row; padding rows satisfy it by forward-chaining).
/// - C4: nullifier binding, **ungated, every row** (repaired 2026-07-30):
///   `nullifier == hash_fact(leaf_commit,[key0,key1,key2,key3])`. It reads
///   `col::LEAF_COMMIT` (constant on every row, C6a) rather than `col::CURRENT`
///   (which climbs the path), so an ungated per-row Poseidon2 aux block enforces it
///   on the `DslP3Air` path. It previously read
///   `Gated{is_leaf, Hash{NULLIFIER,[CURRENT,key0..3]}}`, which that lowering ERASED
///   — see the module-header correction and
///   `circuit-prove/tests/gated_hash_erasure_probe.rs` for the measurement.
/// - C5: chain continuity `next.current == local.parent` (Transition; the
///   forward-chained padding satisfies it on every checked row).
/// - C6a: leaf-commitment recompute (ungated Hash, every row):
///   `leaf_commit == hash_fact(value,[asset_type,owner,randomness])`.
/// - C6b: leaf binding on the leaf row (gated by `is_leaf`):
///   `current == leaf_commit`. Together C6a+C6b force the membership leaf to be
///   the commitment of a note whose full preimage the spender knows — closing
///   the value-theft hole where `current` was a free, prover-chosen cell.
/// - C7a: value-binding recompute (ungated Hash, every row) from the leaf's own
///   value/asset/randomness cells: `value_binding ==
///   hash_fact(value,[asset_type,randomness,0])` (the trailing pad pinned to 0).
///   Publishes a hiding Poseidon2 commitment binding exactly the value AND asset the
///   membership leaf encodes modulo the circuit field. This is a one-felt cutover
///   prototype, not yet a faithful full-u64/PQ-strength commitment.
/// - C7b: pin `value_binding` to `pi[2]`. `verify_value_link` exercises the intended
///   leaf↔Pedersen bridge in tests only; the deployed executor does not call it.
///
/// Boundaries:
/// - Row 0: `nullifier == pi[0]`.
/// - Row 0: `is_leaf == 1` (Fixed) — arms C6b. Added 2026-07-30; without it a
///   prover set `is_leaf = 0` everywhere and `current[0]` was a free cell again.
/// - Last row: `current == pi[1]` (merkle_root). The padding's last row carries
///   the root in `current` (= the last real level's parent), so the bound holds.
/// - Row 0: `value_binding == pi[2]` (carried constant on every row).
pub fn shielded_spend_descriptor() -> CircuitDescriptor {
    let p = BABYBEAR_P;
    // position validity coefficients for pos*(pos-1)*(pos-2)*(pos-3):
    //   = pos^4 - 6 pos^3 + 11 pos^2 - 6 pos
    let neg_6 = BabyBear::new(p - 6);
    let pos_11 = BabyBear::new(11);

    let mut constraints = Vec::new();

    // C1: is_leaf binary.
    constraints.push(ConstraintExpr::Binary { col: col::IS_LEAF });

    // C2: position validity (degree 4).
    constraints.push(ConstraintExpr::Polynomial {
        terms: vec![
            PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION, col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: pos_11,
                col_indices: vec![col::POSITION, col::POSITION],
            },
            PolyTerm {
                coeff: neg_6,
                col_indices: vec![col::POSITION],
            },
        ],
    });

    // C3: Merkle hash binding (every row).
    constraints.push(ConstraintExpr::Hash {
        output_col: col::PARENT,
        input_cols: vec![col::CURRENT, col::SIB0, col::SIB1, col::SIB2, col::POSITION],
    });

    // C4: nullifier binding — UNGATED, over LEAF_COMMIT rather than CURRENT.
    //
    // ⚑ REPAIRED 2026-07-30 (flag day; see the module header). This read
    //   Gated{is_leaf, Hash{NULLIFIER, [CURRENT, KEY0..3]}}
    // and a `Gated{Hash}` is ERASED on the `DslP3Air` path — no Poseidon2 aux block,
    // folded to `assert_zero(is_leaf · 0)`, satisfied by every assignment. Measured:
    // an arbitrary nullifier proved and verified with `is_leaf = 1`.
    //
    // The repair is the one this file's own IMPLEMENTATION NOTE (above `col::VALUE`)
    // already prescribed for C6a/C6b and never applied here: emit the hash UNGATED so
    // its aux block fires on every row, over a column carried CONSTANT on every row.
    // `CURRENT` is not such a column (it climbs the Merkle path), but `LEAF_COMMIT`
    // is — and on an honest trace `current[leaf] == leaf_commit` (C6b), so the bound
    // value is unchanged: `hash_fact(leaf_commitment, key[0..4])`, exactly what
    // `ShieldedSpendWitness::nullifier()` computes.
    //
    // Being ungated, this also survives the `is_leaf = 0` disarm that discharges C6b.
    constraints.push(ConstraintExpr::Hash {
        output_col: col::NULLIFIER,
        input_cols: vec![col::LEAF_COMMIT, col::KEY0, col::KEY1, col::KEY2, col::KEY3],
    });

    // C5: chain continuity (Transition; forward-chained padding satisfies it).
    constraints.push(ConstraintExpr::Transition {
        next_col: col::CURRENT,
        local_col: col::PARENT,
    });

    // C6a: recompute the note commitment EVERY row into LEAF_COMMIT (ungated, so
    // the Poseidon2 aux block enforces it on this p3 path). The preimage limbs
    // are carried constant on every row, so this holds throughout.
    constraints.push(ConstraintExpr::Hash {
        output_col: col::LEAF_COMMIT,
        input_cols: vec![col::VALUE, col::ASSET_TYPE, col::OWNER, col::RANDOMNESS],
    });

    // C6b: pin the leaf to that commitment (gated by is_leaf — a degree-1
    // Equality, enforced under gating).
    //
    // THE VALUE-THEFT TOOTH, now ARMED (2026-07-30): `current` on the leaf row must
    // equal `hash_fact(value,[asset,owner,randomness])`, so a spender can only spend a
    // leaf whose full preimage they know (their own note), not an arbitrary commitment
    // observed in the public tree.
    //
    // ⚑ Between its introduction and 2026-07-30 the tooth was real but UNARMED:
    // `is_leaf` carried only `Binary{is_leaf}` and no boundary, so a prover setting
    // `is_leaf = 0` on every row made this Equality `0 · (current − leaf_commit)` and
    // `current` became a free cell again. The claimed property was a property of the
    // HONEST trace generator, not of the constraint system. `boundaries` below now
    // carries `Fixed{First, IS_LEAF, 1}`, which is what arms it.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_LEAF,
        inner: Box::new(ConstraintExpr::Equality {
            col_a: col::CURRENT,
            col_b: col::LEAF_COMMIT,
        }),
    });

    // C7a: recompute the value-binding commitment EVERY row (ungated Hash, so the
    // Poseidon2 aux block enforces it on this p3 path) from the SAME value/asset/
    // randomness cells the leaf commitment (C6) binds:
    //   value_binding == hash_fact(value, [asset_type, randomness, vb_pad0]).
    // The trailing pad cell vb_pad0 is pinned to 0 (below) so the absorbed terms are
    // [asset_type, randomness, 0]. This constrains the one-field representations
    // jointly inside the AIR; it is not yet the faithful multi-limb, wide-output
    // commitment required by the PQ cutover. Because `value`/`asset_type`/`randomness`
    // are constant on every row, this holds throughout. (vb_pad1 is retained as a
    // zeroed layout column, no longer an absorbed term.)
    constraints.push(ConstraintExpr::Hash {
        output_col: col::VALUE_BINDING,
        input_cols: vec![col::VALUE, col::ASSET_TYPE, col::RANDOMNESS, col::VB_PAD0],
    });
    // The two value-binding pad terms are constant-zero (Polynomial, every row).
    for pad in [col::VB_PAD0, col::VB_PAD1] {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm {
                coeff: BabyBear::ONE,
                col_indices: vec![pad],
            }],
        });
    }

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::NULLIFIER,
            pi_index: pi::NULLIFIER,
        },
        // ⚑ ARMS C6b (added 2026-07-30). Before this, `is_leaf` carried only
        // `Binary{is_leaf}` and no boundary at all, so a prover setting `is_leaf = 0`
        // on every row turned C6b into `0 · (current − leaf_commit)` and `current[0]`
        // became a free cell again — the value-theft hole, open on ALL THREE
        // lowerings, including the two that honour gated hashes. Measured: a foreign
        // leaf with the chain recomputed forward proved and verified.
        //
        // Pinning row 0 to 1 arms C6b exactly where the leaf lives. A prover cannot
        // dodge it by setting `is_leaf = 1` on a later row either: C6b would then
        // demand `current[k] == leaf_commit` for k > 0, which the Merkle chain makes
        // unsatisfiable.
        BoundaryDef::Fixed {
            row: BoundaryRow::First,
            col: col::IS_LEAF,
            value: BabyBear::ONE,
        },
        // The root is the LAST row's PARENT (the membership.rs convention): with
        // forward-chained padding the last row folds the running hash one more
        // time with zero siblings, and that final parent is the committed root.
        BoundaryDef::PiBinding {
            row: BoundaryRow::Last,
            col: col::PARENT,
            pi_index: pi::MERKLE_ROOT,
        },
        // C7b: pin the value-binding commitment to its public input (row 0; it is
        // carried constant on every row, so any row pins the same value). This is
        // what surfaces `value_binding` to the verifier and the Fiat-Shamir
        // transcript. It does not by itself prove equality with the Pedersen leg.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::VALUE_BINDING,
            pi_index: pi::VALUE_BINDING,
        },
    ];

    let columns = vec![
        ColumnDef {
            name: "current".into(),
            index: col::CURRENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "sib0".into(),
            index: col::SIB0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib1".into(),
            index: col::SIB1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "sib2".into(),
            index: col::SIB2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "position".into(),
            index: col::POSITION,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "parent".into(),
            index: col::PARENT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "is_leaf".into(),
            index: col::IS_LEAF,
            kind: ColumnKind::Binary,
        },
        ColumnDef {
            name: "nullifier".into(),
            index: col::NULLIFIER,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "key0".into(),
            index: col::KEY0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "key1".into(),
            index: col::KEY1,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "key2".into(),
            index: col::KEY2,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "key3".into(),
            index: col::KEY3,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "value".into(),
            index: col::VALUE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "asset_type".into(),
            index: col::ASSET_TYPE,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "owner".into(),
            index: col::OWNER,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "randomness".into(),
            index: col::RANDOMNESS,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "leaf_commit".into(),
            index: col::LEAF_COMMIT,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "value_binding".into(),
            index: col::VALUE_BINDING,
            kind: ColumnKind::Hash,
        },
        ColumnDef {
            name: "vb_pad0".into(),
            index: col::VB_PAD0,
            kind: ColumnKind::Value,
        },
        ColumnDef {
            name: "vb_pad1".into(),
            index: col::VB_PAD1,
            kind: ColumnKind::Value,
        },
    ];

    CircuitDescriptor {
        name: "dregg-shielded-spend-v1".into(),
        trace_width: WIDTH,
        max_degree: 4,
        columns,
        constraints,
        boundaries,
        public_input_count: PUBLIC_INPUT_COUNT,
        lookup_tables: vec![],
    }
}

/// The shielded-spend DSL circuit.
pub fn shielded_spend_circuit() -> DslCircuit {
    DslCircuit::new(shielded_spend_descriptor())
}

/// A hidden witness for one shielded spend: the leaf (input note commitment),
/// 4 spending-key limbs, and the 4-ary Merkle path to the root.
#[derive(Clone, Debug)]
pub struct ShieldedSpendWitness {
    /// The note's value. Bound into the leaf commitment (C6) and published so it
    /// links to the input value-commitment leg. Hidden in the proof openings.
    pub value: BabyBear,
    /// The note's asset type. Bound into the leaf commitment (C6) and published.
    pub asset_type: BabyBear,
    /// The note owner field. Bound into the leaf commitment (C6). Hidden.
    pub owner: BabyBear,
    /// The note randomness / creation nonce. Bound into the leaf (C6). Hidden.
    pub randomness: BabyBear,
    /// 4 spending-key limbs binding the nullifier. Hidden.
    pub key: [BabyBear; 4],
    /// Merkle path siblings (3 per level), leaf→root. Hidden.
    pub siblings: Vec<[BabyBear; 3]>,
    /// Merkle path positions (0..3 per level). Hidden.
    pub positions: Vec<u8>,
}

impl ShieldedSpendWitness {
    /// The input note commitment (the Merkle leaf): the C6-bound
    /// `hash_fact(value, [asset_type, owner, randomness])`. This is NOT a free
    /// cell — the circuit forces `current[leaf] == leaf_commitment()`.
    pub fn leaf_commitment(&self) -> BabyBear {
        hash_fact(self.value, &[self.asset_type, self.owner, self.randomness])
    }

    /// The nullifier this spend reveals: `hash_fact(leaf, key[0..4])`.
    pub fn nullifier(&self) -> BabyBear {
        hash_fact(self.leaf_commitment(), &self.key)
    }

    /// The value-binding commitment this spend publishes (C7): a hiding Poseidon2
    /// commitment to the note's value AND asset type jointly, blinded by the note
    /// randomness — `hash_fact(value, [asset_type, randomness, 0])`. It is computed
    /// from the SAME value/asset/randomness cells the membership leaf (C6) is built
    /// from, so the published binding cannot float free of the leaf's value or asset.
    ///
    /// ⚠ POSTURE (honest, 2026-07-21 — corrected from an overstated claim): this
    /// one-felt tag is the shape of the intended Poseidon commitment, but is not yet a
    /// faithful full-u64/PQ-strength commitment: the Rust mirror reduces both u64 inputs
    /// modulo BabyBear and the output is one felt. It is also NOT the deployed no-mint gate.
    /// The value_binding↔leaf link (`verify_value_link`)
    /// runs ONLY in tests, and deployed conservation gates on the Shor-broken Ristretto
    /// `commit_hidden_asset(value, asset_type, blinding)` DLog. This becomes authoritative
    /// only after the Option-A redesign adds multi-limb inputs, a wide output, and routes
    /// the transfer through the ring-clearing apex. The Rust mirror
    /// `dregg_cell_crypto::value_commitment::value_link_binding(value, asset_type,
    /// randomness)` re-derives exactly this felt.
    pub fn value_binding(&self) -> BabyBear {
        hash_fact(
            self.value,
            &[self.asset_type, self.randomness, BabyBear::ZERO],
        )
    }

    /// The Merkle root this spend proves membership under — the LAST trace row's
    /// PARENT, i.e. the running hash after folding the real levels with
    /// `hash_fact(current, [sib0,sib1,sib2,position])` AND the zero-sibling
    /// padding folds the power-of-two trace appends. This is what the root
    /// boundary pins, so it must include the padding folds (the membership.rs
    /// convention). Derived from [`generate_shielded_spend_trace`] so the witness
    /// root and the trace agree by construction.
    pub fn merkle_root(&self) -> BabyBear {
        let (trace, _pis) = generate_shielded_spend_trace(self);
        trace.last().unwrap()[col::PARENT]
    }
}

/// Generate the shielded-spend trace + public inputs `[nullifier, merkle_root]`.
///
/// One row per Merkle level (leaf→root), padded to a power of two by
/// **forward-chaining** (each padding row's `current = prev.parent`,
/// `parent = hash_fact(current,[0,0,0,0])`), so the chain-continuity transition
/// holds on every checked row and the final row's `current == merkle_root`.
pub fn generate_shielded_spend_trace(
    witness: &ShieldedSpendWitness,
) -> (Vec<Vec<BabyBear>>, Vec<BabyBear>) {
    let depth = witness.siblings.len();
    assert_eq!(witness.positions.len(), depth);
    assert!(depth >= 2, "need at least depth 2");

    let mut trace: Vec<Vec<BabyBear>> = Vec::new();
    let nullifier = witness.nullifier();
    // The note commitment, recomputed into LEAF_COMMIT on EVERY row (C6a is
    // ungated, so its aux block fires per-row). The preimage limbs are carried
    // constant on every row so this binding holds throughout.
    let leaf_commit = witness.leaf_commitment();

    // The value-binding commitment (C7), recomputed into VALUE_BINDING on EVERY
    // row (ungated, like LEAF_COMMIT) from the same value/randomness cells.
    let value_binding = witness.value_binding();

    let mut current = leaf_commit;
    for i in 0..depth {
        let pos = witness.positions[i];
        assert!(pos < 4, "position must be 0..3");
        let position = BabyBear::new(pos as u32);
        let sib = witness.siblings[i];
        let parent = hash_fact(current, &[sib[0], sib[1], sib[2], position]);

        let mut row = vec![BabyBear::ZERO; WIDTH];
        row[col::CURRENT] = current;
        row[col::SIB0] = sib[0];
        row[col::SIB1] = sib[1];
        row[col::SIB2] = sib[2];
        row[col::POSITION] = position;
        row[col::PARENT] = parent;
        // Note-commitment preimage + recomputed commitment, carried on EVERY row
        // (constant) so the ungated C6a hash binding holds throughout.
        row[col::VALUE] = witness.value;
        row[col::ASSET_TYPE] = witness.asset_type;
        row[col::OWNER] = witness.owner;
        row[col::RANDOMNESS] = witness.randomness;
        row[col::LEAF_COMMIT] = leaf_commit;
        // Value-binding (C7), constant on every row; pads stay zero.
        row[col::VALUE_BINDING] = value_binding;
        // Nullifier + key limbs, constant on EVERY row (C4 is ungated as of
        // 2026-07-30, so its Poseidon2 aux block fires per-row over the constant
        // LEAF_COMMIT / KEY cells). Previously these were written on row 0 only,
        // which is what a gated C4 needed — and that gating is what erased it.
        row[col::NULLIFIER] = nullifier;
        row[col::KEY0] = witness.key[0];
        row[col::KEY1] = witness.key[1];
        row[col::KEY2] = witness.key[2];
        row[col::KEY3] = witness.key[3];
        if i == 0 {
            // C6b's selector, now PINNED by a first-row Fixed boundary.
            row[col::IS_LEAF] = BabyBear::ONE;
        }
        trace.push(row);
        current = parent;
    }

    // Forward-chained padding to a power of two: each padding row sets
    // `current = prev.parent` (so the chain-continuity Transition holds) and
    // `parent = hash_fact(current,[0,0,0,0])` (so the Merkle-hash constraint
    // holds with zero siblings). `is_leaf = 0` so the nullifier binding does not
    // fire and `position = 0` satisfies position validity.
    let target = depth.next_power_of_two().max(2);
    while trace.len() < target {
        let prev_parent = trace.last().unwrap()[col::PARENT];
        let pad_parent = hash_fact(
            prev_parent,
            &[
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
                BabyBear::ZERO,
            ],
        );
        let mut row = vec![BabyBear::ZERO; WIDTH];
        row[col::CURRENT] = prev_parent;
        row[col::PARENT] = pad_parent;
        // Carry the note preimage + recomputed commitment on padding rows too, so
        // the ungated C6a hash binding holds on every row (is_leaf = 0 here, so
        // C6b does not pin the leaf — only the real leaf row does).
        row[col::VALUE] = witness.value;
        row[col::ASSET_TYPE] = witness.asset_type;
        row[col::OWNER] = witness.owner;
        row[col::RANDOMNESS] = witness.randomness;
        row[col::LEAF_COMMIT] = leaf_commit;
        // Value-binding (C7) carried on padding rows too (constant); pads zero.
        row[col::VALUE_BINDING] = value_binding;
        // Nullifier + keys carried on padding rows too — C4 is ungated, so its
        // per-row hash binding must hold here as well. `is_leaf` stays 0 (C6b fires
        // only on row 0, where the Fixed boundary pins the selector to 1).
        row[col::NULLIFIER] = nullifier;
        row[col::KEY0] = witness.key[0];
        row[col::KEY1] = witness.key[1];
        row[col::KEY2] = witness.key[2];
        row[col::KEY3] = witness.key[3];
        trace.push(row);
    }

    // The committed root is the LAST row's PARENT (membership.rs convention):
    // the running hash after the real levels AND any zero-sibling padding folds.
    // The root boundary pins exactly this cell.
    let merkle_root = trace.last().unwrap()[col::PARENT];
    let public_inputs = vec![nullifier, merkle_root, value_binding];
    (trace, public_inputs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use dregg_circuit::dsl::dsl_p3_air::{prove_dsl_zk, verify_dsl_zk};

    /// A bad trace makes the self-verifying prover EITHER return `Err` OR (in a
    /// debug build) panic in p3's `check_constraints` debug assertion. Either way
    /// it does NOT yield a verifying proof. This helper treats both as
    /// "rejected", which is the soundness property we test.
    fn proving_rejects(circuit: &DslCircuit, trace: &[Vec<BabyBear>], pis: &[BabyBear]) -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_zk(circuit, trace, pis)
        }));
        match r {
            Err(_) => true,     // panicked in the debug constraint check
            Ok(Err(_)) => true, // self-verify rejected
            Ok(Ok(_)) => false, // produced a verifying proof — UNSOUND
        }
    }

    fn test_witness(depth: usize) -> ShieldedSpendWitness {
        let mut siblings = Vec::with_capacity(depth);
        let mut positions = Vec::with_capacity(depth);
        for i in 0..depth {
            positions.push((i % 4) as u8);
            siblings.push([
                BabyBear::new((i as u32) * 5 + 1),
                BabyBear::new((i as u32) * 5 + 2),
                BabyBear::new((i as u32) * 5 + 3),
            ]);
        }
        ShieldedSpendWitness {
            value: BabyBear::new(1_000),
            asset_type: BabyBear::new(42),
            owner: BabyBear::new(0xABCDE),
            randomness: BabyBear::new(0x13579),
            key: [
                BabyBear::new(7),
                BabyBear::new(8),
                BabyBear::new(9),
                BabyBear::new(10),
            ],
            siblings,
            positions,
        }
    }

    /// The descriptor routes through the audited `DslP3Air` symbolic
    /// arithmetization (no unsupported constraint form). If this fails, the
    /// circuit is not p3-clean.
    #[test]
    fn descriptor_is_p3_clean() {
        let dsl = shielded_spend_circuit();
        // Every constraint must be an algebraic / supported form (Hash forms
        // included); `try_from_dsl` errors on MerkleHash / Lookup / cross-row.
        dregg_circuit::dsl::dsl_p3_air::DslP3Air::try_from_dsl(&dsl)
            .expect("shielded-spend descriptor must be DslP3Air-clean");
    }

    /// Both polarities at the circuit level: an honest trace proves+verifies
    /// through the hiding path; a trace whose membership is forged (a tampered
    /// sibling) cannot produce a verifying proof.
    #[test]
    fn honest_proves_forged_membership_fails() {
        let circuit = shielded_spend_circuit();

        // TRUE: honest membership+nullifier proves and verifies (blind).
        let w = test_witness(4);
        let (trace, pis) = generate_shielded_spend_trace(&w);
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("honest shielded-spend must prove through the hiding path");
        verify_dsl_zk(&circuit, &proof, &pis).expect("honest proof must verify");

        // FALSE: corrupt a Merkle sibling in the trace WITHOUT updating the
        // chained parent — the Merkle-hash constraint no longer holds, so the
        // self-verifying prover must refuse to produce a proof.
        let mut bad = trace.clone();
        bad[1][col::SIB0] = bad[1][col::SIB0] + BabyBear::ONE;
        assert!(
            proving_rejects(&circuit, &bad, &pis),
            "a forged-membership trace must NOT produce a verifying hiding proof"
        );
    }

    /// THE NULLIFIER BINDING (C4) BITES — and this test is written so that ONLY C4
    /// can make it bite.
    ///
    /// ⚠ CORRECTED 2026-07-30. It previously bumped the row-0 nullifier cell and left
    /// the PI alone, then claimed "BOTH the C4 binding AND the row-0 boundary fail".
    /// Only the BOUNDARY failed. C4 was a `Gated{Hash}`, erased on this path, so the
    /// test passed for a reason other than the one it named and could not detect the
    /// loss of C4 at all — deleting C4 from the descriptor left it green (measured:
    /// `circuit-prove/tests/gated_hash_erasure_probe.rs::probe_a`).
    ///
    /// The corrected instance moves the published PI to MATCH the tampered cell, so
    /// the row-0 boundary is satisfied and every other constraint is honest. The only
    /// thing left that can refuse is C4 itself.
    #[test]
    fn forged_nullifier_fails() {
        let circuit = shielded_spend_circuit();
        let w = test_witness(4);
        let (mut trace, mut pis) = generate_shielded_spend_trace(&w);

        let chosen = w.nullifier() + BabyBear::ONE;
        // C4 is ungated and per-row, so the tamper must be on every row for the trace
        // to be internally consistent everywhere EXCEPT at the hash binding — which
        // is precisely the constraint under test.
        for row in trace.iter_mut() {
            row[col::NULLIFIER] = chosen;
        }
        // Publish the tampered value, so the row-0 PiBinding boundary HOLDS.
        pis[pi::NULLIFIER] = chosen;

        assert!(
            proving_rejects(&circuit, &trace, &pis),
            "a nullifier that is not hash_fact(leaf_commit, key) must NOT prove — C4 bites, \
             and with the PI moved to match, C4 is the ONLY constraint that can refuse"
        );

        // And the tooth is not a tautology: the SAME trace with the honest nullifier
        // restored proves and verifies.
        for row in trace.iter_mut() {
            row[col::NULLIFIER] = w.nullifier();
        }
        pis[pi::NULLIFIER] = w.nullifier();
        let proof = prove_dsl_zk(&circuit, &trace, &pis).expect("the honest nullifier must prove");
        verify_dsl_zk(&circuit, &proof, &pis).expect("and must verify");
    }

    /// C4 IS ACTUALLY EMITTED — the standing regression for the erasure class.
    ///
    /// Deleting C4 from the descriptor must make a MEASURABLE difference to the p3
    /// AIR. It did not, for as long as C4 was a `Gated{Hash}`: the AIR width was
    /// bit-identical with and without it, because a wrapped hash is allocated no
    /// Poseidon2 aux block. This is the cheap invariant that catches a regression to
    /// that shape in this specific descriptor.
    #[test]
    fn deleting_c4_changes_the_p3_air() {
        use dregg_circuit::dsl::dsl_p3_air::DslP3Air;

        let full = shielded_spend_descriptor();
        let mut without_c4 = full.clone();
        // C4 is the ungated Hash whose output is col::NULLIFIER.
        let idx = full
            .constraints
            .iter()
            .position(|c| {
                matches!(c, ConstraintExpr::Hash { output_col, .. } if *output_col == col::NULLIFIER)
            })
            .expect("C4 must be a top-level (ungated) Hash into col::NULLIFIER");
        without_c4.constraints.remove(idx);

        let a = DslP3Air::try_from_dsl(&DslCircuit::new(full)).expect("full descriptor lowers");
        let b = DslP3Air::try_from_dsl(&DslCircuit::new(without_c4))
            .expect("stripped descriptor lowers");
        let wa = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&a);
        let wb = <DslP3Air as p3_air::BaseAir<p3_baby_bear::BabyBear>>::width(&b);
        assert!(
            wa > wb,
            "C4 must cost a Poseidon2 aux block ({wa} vs {wb}); equal widths mean it is \
             emitting nothing, which is exactly the erasure this descriptor shipped with"
        );
    }

    /// THE VALUE-THEFT TOOTH (both polarities). The leaf (`current` on the leaf
    /// row) is no longer a free cell: C6 forces it to equal the note commitment
    /// `hash_fact(value,[asset,owner,randomness])`. A spender therefore can only
    /// spend a leaf whose full preimage they know (their own note), not an
    /// arbitrary commitment observed in the public tree.
    ///
    /// TRUE: an honest spend whose leaf IS the commitment of the witnessed
    /// preimage proves and verifies.
    ///
    /// FALSE (the attack): a spender substitutes a DIFFERENT leaf into
    /// `current[0]` — e.g. some other high-value note's commitment observed in
    /// the public tree — while keeping their own preimage in the value/asset/
    /// owner/randomness columns. Before the fix `current` was free, so the
    /// membership chain + nullifier still closed and the proof verified → value
    /// theft. With C6 the leaf no longer equals
    /// `hash_fact(value,[asset,owner,randomness])`, so no verifying proof exists.
    #[test]
    fn substituted_leaf_value_theft_rejected() {
        let circuit = shielded_spend_circuit();

        // TRUE: honest spend; the leaf is the bound commitment.
        let w = test_witness(4);
        let (trace, pis) = generate_shielded_spend_trace(&w);
        assert_eq!(
            trace[0][col::CURRENT],
            w.leaf_commitment(),
            "leaf must be the C6-bound note commitment, not a free cell"
        );
        let proof =
            prove_dsl_zk(&circuit, &trace, &pis).expect("honest leaf-bound spend must prove");
        verify_dsl_zk(&circuit, &proof, &pis).expect("honest proof must verify");

        // FALSE: substitute a foreign leaf into current[0] (the classic free-leaf
        // attack) WITHOUT changing the value/asset/owner/randomness preimage. We
        // rebuild the whole upward chain AND the nullifier/root PIs from the
        // foreign leaf so that membership (C3/C5), the nullifier binding (C4), and
        // both boundaries stay internally consistent — isolating C6 (leaf ==
        // commitment(preimage)) as the single constraint that bites.
        let foreign_leaf = w.leaf_commitment() + BabyBear::new(0xDEAD);
        let mut attack = trace.clone();
        let mut cur = foreign_leaf;
        for i in 0..attack.len() {
            let sib0 = attack[i][col::SIB0];
            let sib1 = attack[i][col::SIB1];
            let sib2 = attack[i][col::SIB2];
            let posv = attack[i][col::POSITION];
            let parent = hash_fact(cur, &[sib0, sib1, sib2, posv]);
            attack[i][col::CURRENT] = cur;
            attack[i][col::PARENT] = parent;
            cur = parent;
        }
        // ⚠ CORRECTED 2026-07-30. This built `vec![null_attack, root_attack]` — TWO
        // entries against `PUBLIC_INPUT_COUNT == 3`, and the circuit reads
        // `public_values[2]` for the C7b value_binding boundary. The rejection was
        // therefore attributable to a MALFORMED PI VECTOR, not to C6, so the tooth was
        // UNEXERCISED and the assertion message was unsupported by the instance.
        //
        // The nullifier is NOT rebuilt from the foreign leaf: C4 now binds
        // `nullifier == hash_fact(leaf_commit, key)`, and the attacker leaves their own
        // preimage in place, so the honest nullifier is what a consistent trace carries.
        let root_attack = attack.last().unwrap()[col::PARENT];
        let attack_pis = vec![w.nullifier(), root_attack, w.value_binding()];
        assert_eq!(
            attack_pis.len(),
            PUBLIC_INPUT_COUNT,
            "the PI vector must be WELL-FORMED, or the rejection proves nothing about C6"
        );

        assert!(
            proving_rejects(&circuit, &attack, &attack_pis),
            "a substituted free leaf (value-theft attack) must NOT prove — C6b bites"
        );

        // THE CHEAP ATTACK, and the reason C6b needed a pinned selector: the same
        // substitution with `is_leaf = 0` on every row. Until 2026-07-30 that turned
        // C6b into `0 · (current − leaf_commit)` and the whole thing proved and
        // verified on the deployed hiding verifier (measured:
        // `circuit-prove/tests/gated_hash_erasure_probe.rs::probe_b2`). The
        // `Fixed{First, IS_LEAF, 1}` boundary is what refuses it now.
        let mut disarmed = attack.clone();
        for row in disarmed.iter_mut() {
            row[col::IS_LEAF] = BabyBear::ZERO;
        }
        assert!(
            proving_rejects(&circuit, &disarmed, &attack_pis),
            "setting is_leaf = 0 must NOT disarm the value-theft tooth — the first-row \
             Fixed boundary pins the selector"
        );
    }

    /// THE LEAF↔LEG VALUE LINK (C7), both polarities at the circuit level. The
    /// spend publishes `value_binding == hash_fact(value, [randomness, 0, 0])` as
    /// PI[VALUE_BINDING], recomputed from the SAME value/randomness cells the
    /// membership leaf (C6) is built from.
    ///
    /// TRUE: the honest trace's PI[VALUE_BINDING] equals the witness value-binding
    /// and the proof verifies.
    ///
    /// FALSE (the splice): an adversary who wants the STARK to attest one value
    /// while the Pedersen leg conserves another must publish a `value_binding`
    /// PI that disagrees with `hash_fact(value,[randomness,0,0])` for the leaf's
    /// own value. Re-pointing PI[VALUE_BINDING] to any other felt breaks the C7b
    /// boundary (and, if instead the trace cell is tampered, the ungated C7a hash);
    /// no verifying proof exists. This is exactly what stops a "STARK value V,
    /// Pedersen value V'" mismatch: the published binding is forced to be a
    /// commitment to the leaf's own value.
    #[test]
    fn value_binding_links_leaf_value_to_pi() {
        let circuit = shielded_spend_circuit();

        // TRUE: honest spend; PI[2] is the witness value-binding.
        let w = test_witness(4);
        let (trace, pis) = generate_shielded_spend_trace(&w);
        assert_eq!(pis.len(), PUBLIC_INPUT_COUNT);
        assert_eq!(
            pis[pi::VALUE_BINDING],
            w.value_binding(),
            "PI[VALUE_BINDING] must be hash_fact(value,[randomness,0,0])"
        );
        // And it is genuinely a commitment to the LEAF's value (same cells as C6).
        assert_eq!(
            trace[0][col::VALUE_BINDING],
            hash_fact(
                trace[0][col::VALUE],
                &[
                    trace[0][col::ASSET_TYPE],
                    trace[0][col::RANDOMNESS],
                    BabyBear::ZERO
                ]
            ),
            "the value-binding cell must be computed from the leaf's own value/asset/randomness"
        );
        let proof =
            prove_dsl_zk(&circuit, &trace, &pis).expect("honest value-bound spend must prove");
        verify_dsl_zk(&circuit, &proof, &pis).expect("honest proof must verify");

        // FALSE: publish a value_binding PI for a DIFFERENT value (the splice an
        // attacker would use to mismatch the Pedersen leg). The C7b boundary
        // (`value_binding == pi[2]`) no longer holds — no verifying proof.
        let mut mismatched_pis = pis.clone();
        mismatched_pis[pi::VALUE_BINDING] = hash_fact(
            w.value + BabyBear::new(0xBADCA5),
            &[w.asset_type, w.randomness, BabyBear::ZERO],
        );
        assert!(
            proving_rejects(&circuit, &trace, &mismatched_pis),
            "a value_binding PI for a different value must NOT prove — C7b bites"
        );

        // FALSE (the harder splice): tamper the in-trace value-binding cell to
        // match a forged PI, leaving the leaf's value/randomness untouched. Now the
        // UNGATED C7a hash (value_binding == hash_fact(value,[randomness,0,0]))
        // disagrees on every row — no verifying proof.
        let forged_vb = hash_fact(
            w.value + BabyBear::new(7),
            &[w.asset_type, w.randomness, BabyBear::ZERO],
        );
        let mut attack = trace.clone();
        for row in attack.iter_mut() {
            row[col::VALUE_BINDING] = forged_vb;
        }
        let mut attack_pis = pis.clone();
        attack_pis[pi::VALUE_BINDING] = forged_vb;
        assert!(
            proving_rejects(&circuit, &attack, &attack_pis),
            "a value-binding decoupled from the leaf's value must NOT prove — C7a bites"
        );
    }

    /// Prototype asset-absorption check. The one-felt tag includes `(value, asset_type)`
    /// JOINTLY —
    /// `hash_fact(value, [asset_type, randomness, 0])` — the multi-asset binding the
    /// and this test witnesses that the two selected small field values produce
    /// different outputs. It is not a collision-resistance test, does not cover the
    /// modulo-p u64 aliases, and does not establish a PQ-strength commitment.
    #[test]
    fn value_binding_binds_asset_type() {
        let mut w = test_witness(4);
        w.asset_type = BabyBear::new(42);
        let vb_asset42 = w.value_binding();

        // Same value/randomness, a DIFFERENT asset type ⇒ a different commitment.
        let mut w2 = w.clone();
        w2.asset_type = BabyBear::new(43);
        assert_ne!(
            vb_asset42,
            w2.value_binding(),
            "the one-felt tag must absorb asset_type for these two field values"
        );

        // And it is exactly hash_fact(value, [asset_type, randomness, 0]).
        assert_eq!(
            vb_asset42,
            hash_fact(w.value, &[w.asset_type, w.randomness, BabyBear::ZERO]),
            "value_binding == hash_fact(value, [asset_type, randomness, 0])"
        );
    }
}
