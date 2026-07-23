use super::*;

/// A per-element decision predicate over the felt fields of one collection
/// element (the Rust mirror of the Lean `ElemPred := Value → Bool`, built
/// from `elemScalar`/`elemSym`). An element is its heap stride
/// `&[Option<FieldElement>]` — `field[f]` is the value at element-relative
/// offset `f` (absent ⇒ `None`). Each atom reads ONE element field by
/// offset (the felt dual of reading a record field by name) and is
/// fail-closed on an absent field.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ElemPredAtom {
    /// `element[offset] == value` (full 32-byte; absent field ⇒ false).
    FieldEquals { offset: u32, value: FieldElement },
    /// `element[offset] >= value` (big-endian; absent ⇒ false).
    FieldGte { offset: u32, value: FieldElement },
    /// `element[offset] <= value` (big-endian; absent ⇒ false).
    FieldLte { offset: u32, value: FieldElement },
    /// `element[offset] ∈ set` (u64 lane; absent ⇒ false).
    FieldInSet { offset: u32, set: Vec<u64> },
}

impl ElemPredAtom {
    /// The element-relative offset this atom reads — its ANCHOR field. A
    /// collection element is "present" iff its anchor (and, for the
    /// council, its key) reads; this drives the `readIndexed` truncation.
    pub fn anchor_offset(&self) -> u32 {
        match self {
            ElemPredAtom::FieldEquals { offset, .. }
            | ElemPredAtom::FieldGte { offset, .. }
            | ElemPredAtom::FieldLte { offset, .. }
            | ElemPredAtom::FieldInSet { offset, .. } => *offset,
        }
    }

    /// Decide this atom against one element's heap stride `elem` (indexed
    /// by element-relative offset; `None` = absent field). Fail-closed:
    /// an absent field is `false` (the `elemScalar`/`elemSym` fail-closed
    /// read — `Value.scalar` over a missing field is `none`, so the
    /// predicate built from it is `false`).
    pub(crate) fn eval(&self, elem: &[Option<FieldElement>]) -> bool {
        let read = |off: u32| -> Option<FieldElement> { elem.get(off as usize).copied().flatten() };
        match self {
            ElemPredAtom::FieldEquals { offset, value } => read(*offset) == Some(*value),
            ElemPredAtom::FieldGte { offset, value } => {
                read(*offset).is_some_and(|x| field_gte(&x, value))
            }
            ElemPredAtom::FieldLte { offset, value } => {
                read(*offset).is_some_and(|x| field_lte(&x, value))
            }
            ElemPredAtom::FieldInSet { offset, set } => {
                read(*offset).is_some_and(|x| set.contains(&field_to_u64(&x)))
            }
        }
    }
}

/// The AGGREGATE predicate fragment over a named collection — the Rust
/// mirror of the Lean `Dregg2.Exec.Collections.CollPred` PLUS the council
/// lift `mOfNDistinct`. Each shape is a decidable function of the
/// read-out collection, fail-closed.
///
/// Lean twin: `Dregg2.Exec.Collections.CollPred` (the first five) +
/// `mOfNDistinct` (the council). Each evaluator arm implements the
/// corresponding `eval_*_iff` / `mOfNDistinct_iff` admit-characterization
/// (`metatheory/Dregg2/Exec/Collections.lean`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CollPred {
    /// **≥ `m` elements satisfy `p`** — the in-data M-of-N count statistic
    /// (NOT distinct — the distinct council gate is [`Self::MOfNDistinct`]).
    /// Lean: `CollPred.countSatGe` / `eval_countSatGe_iff`.
    CountSatGe { m: u32, p: ElemPredAtom },
    /// **Σ of element field at `offset` ≤ `bound`** — a treasury/supply
    /// ceiling (absent/ill-typed reads contribute 0 — total). Lean:
    /// `CollPred.sumOfLe` / `eval_sumOfLe_iff`.
    SumOfLe { offset: u32, bound: i64 },
    /// **Σ of element field at `offset` ≥ `bound`** — a treasury/supply
    /// floor. Lean: `CollPred.sumOfGe` / `eval_sumOfGe_iff`.
    SumOfGe { offset: u32, bound: i64 },
    /// **∀ element, `p`** — every entry obeys the invariant (bounded
    /// universal). Lean: `CollPred.allMembers` / `eval_allMembers_iff`.
    AllMembers { p: ElemPredAtom },
    /// **∃ element, `p`** — some entry matches (bounded existential).
    /// Lean: `CollPred.existsMember` / `eval_existsMember_iff`.
    ExistsMember { p: ElemPredAtom },
    /// **THE COUNCIL LIFT — arbitrary-N M-of-N, distinctness-enforced**:
    /// ≥ `m` elements whose `key_offset` identities are DISTINCT satisfy
    /// `approved`. The duplicate-padded forge collapses (one distinct
    /// key); the unbound forge is filtered (fails `approved`). Lean:
    /// `mOfNDistinct` / `mOfNDistinct_iff` / `mOfNDistinct_le_countSat`.
    MOfNDistinct {
        m: u32,
        key_offset: u32,
        approved: ElemPredAtom,
    },
}

impl CollPred {
    /// The element-relative offset whose presence ANCHORS the collection
    /// read (drives the `readIndexed` truncation — the contiguous prefix
    /// whose anchor is present). For the council it is the `key_offset`
    /// (an element with no identity does not count); for the others it is
    /// the predicate's read offset (or the summed field's). An element
    /// missing its anchor truncates the collection there.
    pub fn anchor_offset(&self) -> u32 {
        match self {
            CollPred::CountSatGe { p, .. }
            | CollPred::AllMembers { p }
            | CollPred::ExistsMember { p } => p.anchor_offset(),
            CollPred::SumOfLe { offset, .. } | CollPred::SumOfGe { offset, .. } => *offset,
            CollPred::MOfNDistinct { key_offset, .. } => *key_offset,
        }
    }

    /// Evaluate this aggregate over the read-out collection `coll` (each
    /// element a heap stride `Vec<Option<FieldElement>>`). Mirrors
    /// `CollPred.eval` / `mOfNDistinct` exactly. Fail-closed by
    /// construction (an absent element field is a `false`/`0` read).
    pub(crate) fn eval(&self, coll: &[Vec<Option<FieldElement>>]) -> bool {
        match self {
            CollPred::CountSatGe { m, p } => {
                let n = coll.iter().filter(|e| p.eval(e)).count();
                (n as u64) >= (*m as u64)
            }
            CollPred::SumOfLe { offset, bound } => coll_sum(coll, *offset) <= (*bound as i128),
            CollPred::SumOfGe { offset, bound } => coll_sum(coll, *offset) >= (*bound as i128),
            CollPred::AllMembers { p } => coll.iter().all(|e| p.eval(e)),
            CollPred::ExistsMember { p } => coll.iter().any(|e| p.eval(e)),
            CollPred::MOfNDistinct {
                m,
                key_offset,
                approved,
            } => {
                // distinctApproverKeys: filter to approving elements, read
                // each one's key identity (drop keyless — fail-closed),
                // then dedup. A `BTreeSet` IS the `eraseDups` distinctness
                // (the duplicate-padded forge collapses to ONE key).
                let distinct: std::collections::BTreeSet<u64> = coll
                    .iter()
                    .filter(|e| approved.eval(e))
                    .filter_map(|e| e.get(*key_offset as usize).copied().flatten())
                    .map(|k| field_to_u64(&k))
                    .collect();
                (distinct.len() as u64) >= (*m as u64)
            }
        }
    }
}

/// Σ of the element field at `offset` over the collection — absent/missing
/// reads contribute 0 (total, the Lean `sumOfField` `getD 0` discipline).
/// Folded as `i128` (the u64-lane value lifted signed, like `affine_sum`).
fn coll_sum(coll: &[Vec<Option<FieldElement>>], offset: u32) -> i128 {
    coll.iter()
        .map(|e| {
            e.get(offset as usize)
                .copied()
                .flatten()
                .map(|x| field_to_u64(&x) as i128)
                .unwrap_or(0)
        })
        .sum()
}

/// Read the named collection out of a cell's heap as the contiguous run of
/// element strides under `collection_id`. The Rust mirror of the Lean
/// `Value.collectionField` (`readIndexed`): element `i` occupies heap keys
/// `[i*stride .. i*stride + stride)` under `collection_id`; the collection
/// is the prefix whose ANCHOR key (`anchor_off`) is present, truncating at
/// the first absent index (fail-closed — no phantom tail beyond a gap),
/// bounded by `fuel`. `None` if even element 0's anchor is absent (the
/// `collectionField` "absent or not a record" `none`: no collection to
/// aggregate ⇒ fail-closed reject upstream).
pub(crate) fn read_collection(
    new_state: &CellState,
    collection_id: u32,
    stride: u32,
    fuel: u32,
    anchor_off: u32,
) -> Option<Vec<Vec<Option<FieldElement>>>> {
    if stride == 0 {
        // A zero-width element has no fields — an ill-formed collection
        // shape; fail closed (the `collectionField` non-record `none`).
        return None;
    }
    let mut coll: Vec<Vec<Option<FieldElement>>> = Vec::new();
    for i in 0..fuel {
        let base = (i as u64) * (stride as u64);
        // The element's anchor key presence decides truncation (the
        // `readIndexed` `match elems.field (toString i)` — stop at the
        // first absent index).
        let anchor_key = base + (anchor_off as u64);
        // Heap keys are u32-lane; an out-of-range key cannot be present.
        let anchor_present = u32::try_from(anchor_key)
            .ok()
            .and_then(|k| new_state.get_heap(collection_id, k))
            .is_some();
        if !anchor_present {
            break;
        }
        let mut elem: Vec<Option<FieldElement>> = Vec::with_capacity(stride as usize);
        for f in 0..stride {
            let key = base + (f as u64);
            let v = u32::try_from(key)
                .ok()
                .and_then(|k| new_state.get_heap(collection_id, k));
            elem.push(v);
        }
        coll.push(elem);
    }
    if coll.is_empty() { None } else { Some(coll) }
}

/// Read a contiguous collection out of the cell's EXECUTOR-REACHABLE user-field
/// MAP (`fields_map`, the `_RECORD-LAYER-UPGRADE.md` deliverable) — the
/// executor-writable twin of [`read_collection`]. Element `i` occupies map keys
/// `[base + i*stride .. base + i*stride + stride)`; element `i`'s field at
/// element-relative offset `f` is the map value at key `base + i*stride + f`
/// ([`CellState::get_field_ext`]). The collection is the prefix whose ANCHOR key
/// (`anchor_off`) is present, truncating at the first absent index (fail-closed —
/// no phantom tail beyond a gap), bounded by `fuel`. `None` if even element 0's
/// anchor is absent (no collection to aggregate ⇒ fail-closed reject upstream),
/// or if `stride == 0` (an ill-formed shape).
///
/// Reads route through [`CellState::get_field_ext`], so keys `< STATE_SLOTS`
/// would resolve to the fixed register file; callers MUST pass `base >=
/// STATE_SLOTS` so the run lives wholly in the committed map tail (the executor
/// `SetField` path that writes those keys is what makes this reachable).
pub(crate) fn read_collection_fields(
    new_state: &CellState,
    base: u64,
    stride: u32,
    fuel: u32,
    anchor_off: u32,
) -> Option<Vec<Vec<Option<FieldElement>>>> {
    if stride == 0 {
        return None;
    }
    let mut coll: Vec<Vec<Option<FieldElement>>> = Vec::new();
    for i in 0..fuel {
        let elem_base = base + (i as u64) * (stride as u64);
        let anchor_present = new_state
            .get_field_ext(elem_base + (anchor_off as u64))
            .is_some();
        if !anchor_present {
            break;
        }
        let mut elem: Vec<Option<FieldElement>> = Vec::with_capacity(stride as usize);
        for f in 0..stride {
            elem.push(new_state.get_field_ext(elem_base + (f as u64)));
        }
        coll.push(elem);
    }
    if coll.is_empty() { None } else { Some(coll) }
}
