//! The shielded-spend DSL circuit: membership + nullifier, p3/uni-STARK-clean.
//!
//! This is the STARK side of an M2-a shielded transfer for ONE input note,
//! authored as a `CircuitDescriptor` (data — **zero hand-written AIR**) using
//! only the constraint forms the audited `DslP3Air` symbolic arithmetization
//! supports (`Hash`, `Transition`, `Polynomial`, `Binary`, boundary
//! `PiBinding`), so it proves through the **hiding** uni-STARK path
//! ([`crate::dsl::dsl_p3_air::prove_dsl_zk`], `HidingFriPcs`).
//!
//! # Why not reuse `dsl::note_spending` directly
//!
//! `note_spending`'s DSL trace is designed for the hand-rolled `crate::stark`
//! prover: its commitment-preimage row and power-of-two PADDING rows do not
//! satisfy the chain-continuity `Transition` under p3's `when_transition`
//! gating (which fires on row0→row1 and on interior padding rows). That is why
//! `note_spending` is `crate::stark`-only. Rather than perturb that shared
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
//! - **(c) nullifier:** `nullifier = hash_fact(leaf_commitment, key[0..4])`,
//!   bound on row 0 and pinned to the published `nullifier` PI. Reusing a note
//!   (same commitment+key) yields the same nullifier → the chain's nullifier set
//!   rejects the double-spend.
//!
//! The leaf commitment, key, and path live only in the witness; the hiding PCS
//! makes the proof's openings reveal nothing about them. *Owner/leaf is blind.*
//!
//! The note's value/asset live in the Pedersen value commitment (the other half
//! of the transfer). This circuit additionally publishes a hiding Poseidon2
//! **value-binding** `value_binding = hash_fact(value, [randomness, 0, 0])` (C7),
//! computed from the SAME value/randomness cells the membership leaf is built
//! from, so the STARK leaf value cannot float free of the value the transfer
//! actually balances. The downstream
//! `dregg_cell::value_commitment::verify_value_link` ties this binding to the
//! Pedersen leg (closing the leaf↔leg VALUE LINK residual).

use crate::dsl::circuit::{
    BoundaryDef, BoundaryRow, CircuitDescriptor, ColumnDef, ColumnKind, ConstraintExpr, DslCircuit,
    PolyTerm,
};
use crate::field::{BABYBEAR_P, BabyBear};
use crate::poseidon2::hash_fact;

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
    // C7 publishes a HIDING Poseidon2 commitment to exactly the value (and the
    // note randomness, as blinding) the STARK leaf is built from:
    //   value_binding = hash_fact(value, [randomness, 0, 0]).
    // It is recomputed UNGATED on every row (so the p3 Poseidon2 aux block fires)
    // from the SAME col::VALUE / col::RANDOMNESS cells C6 binds into the leaf, then
    // pinned to a public input. Because `value` and `randomness` are the cells the
    // leaf commitment already constrains, the published `value_binding` is provably
    // a commitment to the very value this spend's membership leaf encodes — it
    // cannot float free of the leaf value. The downstream value-link check
    // (`dregg_cell::value_commitment::verify_value_link`) re-derives `value_binding`
    // from the Pedersen leg's opening and rejects any leg whose value differs.
    /// Value-binding commitment `hash_fact(value, [randomness, 0, 0])`, recomputed
    /// every row (C7a) from the leaf's own value/randomness cells and pinned to
    /// PI[VALUE_BINDING] (C7b). The leaf↔leg value link.
    pub const VALUE_BINDING: usize = 17;
    /// Constant-zero pad cells so the `value_binding` hash absorbs exactly
    /// `[randomness, 0, 0]` (3 of the 4 hash_fact terms; the 4th is implicit zero).
    pub const VB_PAD0: usize = 18;
    pub const VB_PAD1: usize = 19;
}

/// Trace width.
pub const WIDTH: usize = 20;

/// Public-input indices: `[nullifier, merkle_root, value_binding]`.
pub mod pi {
    pub const NULLIFIER: usize = 0;
    pub const MERKLE_ROOT: usize = 1;
    /// Hiding Poseidon2 commitment to the input note's value (with the note
    /// randomness as blinding): `hash_fact(value, [randomness, 0, 0])`. Ties the
    /// STARK-witnessed leaf value to the published Pedersen value-commitment leg
    /// (see `dregg_cell::value_commitment::verify_value_link`).
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
/// - C4: nullifier binding on the leaf row (gated by `is_leaf`):
///   `nullifier == hash_fact(current,[key0,key1,key2,key3])`.
/// - C5: chain continuity `next.current == local.parent` (Transition; the
///   forward-chained padding satisfies it on every checked row).
/// - C6a: leaf-commitment recompute (ungated Hash, every row):
///   `leaf_commit == hash_fact(value,[asset_type,owner,randomness])`.
/// - C6b: leaf binding on the leaf row (gated by `is_leaf`):
///   `current == leaf_commit`. Together C6a+C6b force the membership leaf to be
///   the commitment of a note whose full preimage the spender knows — closing
///   the value-theft hole where `current` was a free, prover-chosen cell.
/// - C7a: value-binding recompute (ungated Hash, every row) from the leaf's own
///   value/randomness cells: `value_binding == hash_fact(value,[randomness,0,0])`
///   (the two pad cells pinned to 0). Publishes a hiding commitment to exactly the
///   value the membership leaf encodes.
/// - C7b: pin `value_binding` to `pi[2]` (the leaf↔Pedersen-leg VALUE LINK). The
///   downstream `verify_value_link` re-derives this from the Pedersen leg's
///   opening, rejecting any leg whose value differs from the STARK leaf value.
///
/// Boundaries:
/// - Row 0: `nullifier == pi[0]`.
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

    // C4: nullifier binding on the leaf row (gated by is_leaf).
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_LEAF,
        inner: Box::new(ConstraintExpr::Hash {
            output_col: col::NULLIFIER,
            input_cols: vec![col::CURRENT, col::KEY0, col::KEY1, col::KEY2, col::KEY3],
        }),
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
    // Equality, enforced under gating). THE VALUE-THEFT TOOTH: `current` is no
    // longer a free cell; it must equal hash_fact(value,[asset,owner,randomness]),
    // so a spender can only spend a leaf whose full preimage they know (their own
    // note), not an arbitrary commitment observed in the public tree.
    constraints.push(ConstraintExpr::Gated {
        selector_col: col::IS_LEAF,
        inner: Box::new(ConstraintExpr::Equality {
            col_a: col::CURRENT,
            col_b: col::LEAF_COMMIT,
        }),
    });

    // C7a: recompute the value-binding commitment EVERY row (ungated Hash, so the
    // Poseidon2 aux block enforces it on this p3 path) from the SAME value/
    // randomness cells the leaf commitment (C6) binds:
    //   value_binding == hash_fact(value, [randomness, vb_pad0, vb_pad1]).
    // The pad cells are pinned to 0 (below) so the absorbed terms are
    // [randomness, 0, 0]. Because `value`/`randomness` are constant on every row,
    // this holds throughout.
    constraints.push(ConstraintExpr::Hash {
        output_col: col::VALUE_BINDING,
        input_cols: vec![col::VALUE, col::RANDOMNESS, col::VB_PAD0, col::VB_PAD1],
    });
    // The two value-binding pad terms are constant-zero (Polynomial, every row).
    for pad in [col::VB_PAD0, col::VB_PAD1] {
        constraints.push(ConstraintExpr::Polynomial {
            terms: vec![PolyTerm { coeff: BabyBear::ONE, col_indices: vec![pad] }],
        });
    }

    let boundaries = vec![
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::NULLIFIER,
            pi_index: pi::NULLIFIER,
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
        // transcript, tying the STARK leaf value to the Pedersen leg.
        BoundaryDef::PiBinding {
            row: BoundaryRow::First,
            col: col::VALUE_BINDING,
            pi_index: pi::VALUE_BINDING,
        },
    ];

    let columns = vec![
        ColumnDef { name: "current".into(), index: col::CURRENT, kind: ColumnKind::Hash },
        ColumnDef { name: "sib0".into(), index: col::SIB0, kind: ColumnKind::Value },
        ColumnDef { name: "sib1".into(), index: col::SIB1, kind: ColumnKind::Value },
        ColumnDef { name: "sib2".into(), index: col::SIB2, kind: ColumnKind::Value },
        ColumnDef { name: "position".into(), index: col::POSITION, kind: ColumnKind::Value },
        ColumnDef { name: "parent".into(), index: col::PARENT, kind: ColumnKind::Hash },
        ColumnDef { name: "is_leaf".into(), index: col::IS_LEAF, kind: ColumnKind::Binary },
        ColumnDef { name: "nullifier".into(), index: col::NULLIFIER, kind: ColumnKind::Hash },
        ColumnDef { name: "key0".into(), index: col::KEY0, kind: ColumnKind::Value },
        ColumnDef { name: "key1".into(), index: col::KEY1, kind: ColumnKind::Value },
        ColumnDef { name: "key2".into(), index: col::KEY2, kind: ColumnKind::Value },
        ColumnDef { name: "key3".into(), index: col::KEY3, kind: ColumnKind::Value },
        ColumnDef { name: "value".into(), index: col::VALUE, kind: ColumnKind::Value },
        ColumnDef { name: "asset_type".into(), index: col::ASSET_TYPE, kind: ColumnKind::Value },
        ColumnDef { name: "owner".into(), index: col::OWNER, kind: ColumnKind::Value },
        ColumnDef { name: "randomness".into(), index: col::RANDOMNESS, kind: ColumnKind::Value },
        ColumnDef { name: "leaf_commit".into(), index: col::LEAF_COMMIT, kind: ColumnKind::Hash },
        ColumnDef { name: "value_binding".into(), index: col::VALUE_BINDING, kind: ColumnKind::Hash },
        ColumnDef { name: "vb_pad0".into(), index: col::VB_PAD0, kind: ColumnKind::Value },
        ColumnDef { name: "vb_pad1".into(), index: col::VB_PAD1, kind: ColumnKind::Value },
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
    /// commitment to the note's value, blinded by the note randomness —
    /// `hash_fact(value, [randomness, 0, 0])`. It is computed from the SAME value/
    /// randomness cells the membership leaf (C6) is built from, so the published
    /// binding cannot float free of the leaf value. The downstream
    /// `dregg_cell::value_commitment::value_link_binding` re-derives exactly this
    /// from the Pedersen leg's `(value, randomness)` opening to tie the two halves.
    pub fn value_binding(&self) -> BabyBear {
        hash_fact(self.value, &[self.randomness, BabyBear::ZERO, BabyBear::ZERO])
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
        if i == 0 {
            row[col::IS_LEAF] = BabyBear::ONE;
            row[col::NULLIFIER] = nullifier;
            row[col::KEY0] = witness.key[0];
            row[col::KEY1] = witness.key[1];
            row[col::KEY2] = witness.key[2];
            row[col::KEY3] = witness.key[3];
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
            &[BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO, BabyBear::ZERO],
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
    use crate::dsl::dsl_p3_air::{prove_dsl_zk, verify_dsl_zk};

    /// A bad trace makes the self-verifying prover EITHER return `Err` OR (in a
    /// debug build) panic in p3's `check_constraints` debug assertion. Either way
    /// it does NOT yield a verifying proof. This helper treats both as
    /// "rejected", which is the soundness property we test.
    fn proving_rejects(
        circuit: &DslCircuit,
        trace: &[Vec<BabyBear>],
        pis: &[BabyBear],
    ) -> bool {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            prove_dsl_zk(circuit, trace, pis)
        }));
        match r {
            Err(_) => true,        // panicked in the debug constraint check
            Ok(Err(_)) => true,    // self-verify rejected
            Ok(Ok(_)) => false,    // produced a verifying proof — UNSOUND
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
        crate::dsl::dsl_p3_air::DslP3Air::try_from_dsl(&dsl)
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

    /// The nullifier binding bites: a trace whose row-0 nullifier disagrees with
    /// `hash_fact(leaf, key)` cannot prove.
    #[test]
    fn forged_nullifier_fails() {
        let circuit = shielded_spend_circuit();
        let w = test_witness(4);
        let (mut trace, pis) = generate_shielded_spend_trace(&w);
        // Tamper ONLY the row-0 nullifier cell (leave the PI). Now BOTH the C4
        // binding (`nullifier == hash_fact(current,key)`) AND the row-0 boundary
        // (`nullifier == pi[0]`) fail — the prover must not yield a proof.
        trace[0][col::NULLIFIER] = trace[0][col::NULLIFIER] + BabyBear::ONE;
        assert!(
            proving_rejects(&circuit, &trace, &pis),
            "a forged-nullifier trace must NOT produce a verifying hiding proof"
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
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("honest leaf-bound spend must prove");
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
        let null_attack = hash_fact(foreign_leaf, &w.key);
        attack[0][col::NULLIFIER] = null_attack;
        let root_attack = attack.last().unwrap()[col::PARENT];
        let attack_pis = vec![null_attack, root_attack];

        assert!(
            proving_rejects(&circuit, &attack, &attack_pis),
            "a substituted free leaf (value-theft attack) must NOT prove — C6 bites"
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
            hash_fact(trace[0][col::VALUE], &[trace[0][col::RANDOMNESS], BabyBear::ZERO, BabyBear::ZERO]),
            "the value-binding cell must be computed from the leaf's own value/randomness"
        );
        let proof = prove_dsl_zk(&circuit, &trace, &pis)
            .expect("honest value-bound spend must prove");
        verify_dsl_zk(&circuit, &proof, &pis).expect("honest proof must verify");

        // FALSE: publish a value_binding PI for a DIFFERENT value (the splice an
        // attacker would use to mismatch the Pedersen leg). The C7b boundary
        // (`value_binding == pi[2]`) no longer holds — no verifying proof.
        let mut mismatched_pis = pis.clone();
        mismatched_pis[pi::VALUE_BINDING] =
            hash_fact(w.value + BabyBear::new(0xBADCA5), &[w.randomness, BabyBear::ZERO, BabyBear::ZERO]);
        assert!(
            proving_rejects(&circuit, &trace, &mismatched_pis),
            "a value_binding PI for a different value must NOT prove — C7b bites"
        );

        // FALSE (the harder splice): tamper the in-trace value-binding cell to
        // match a forged PI, leaving the leaf's value/randomness untouched. Now the
        // UNGATED C7a hash (value_binding == hash_fact(value,[randomness,0,0]))
        // disagrees on every row — no verifying proof.
        let forged_vb = hash_fact(w.value + BabyBear::new(7), &[w.randomness, BabyBear::ZERO, BabyBear::ZERO]);
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
}
