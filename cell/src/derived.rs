//! Derived / relational cells — a cell whose committed state IS a verifiable
//! function of OTHER cells' committed states (a view / materialized aggregate).
//!
//! # The capacity (Track 2)
//!
//! The base substrate lets a light client verify *"this cell changed"* — the
//! canonical state commitment ([`crate::commitment::compute_canonical_state_commitment`])
//! binds a cell's full state, and a membership proof binds it into the ledger
//! root. This module adds the next thing a light client should be able to
//! verify: *"this cell is correctly DERIVED FROM those cells"*.
//!
//! A **derived cell** carries a [`DerivationSpec`] — a declaration of the form
//! *"my value = sum(those cells' balances)"* (or a join / filter / count over a
//! set of source cells) — together with the **claimed result** of evaluating
//! that spec. The derived cell is sound iff its committed claimed result EQUALS
//! the spec evaluated over its sources' committed states.
//!
//! # The weld (what already existed, disconnected)
//!
//! This is built, not memoed — but it welds onto substrate that already exists:
//!
//!  * **The committed heap** ([`CellState::set_heap`] / [`compute_heap_root`])
//!    is an openable sorted-Poseidon2 `(collection, key) → FieldElement` map
//!    that is ALREADY folded into the canonical state commitment. We reserve a
//!    collection id ([`DERIVATION_COLL`]) inside it for the derivation binding —
//!    so binding a derivation is a heap write, and the derived cell's commitment
//!    binds the derivation FOR FREE, with no commitment-version bump.
//!
//!  * **The signed balance ledger** ([`CellState::balance`]) and its
//!    conservation discipline give the source quantity to aggregate. The same
//!    `i64` the kernel's `bal : cell → asset → ℤ` ledger carries.
//!
//!  * The **derivation provenance** machinery ([`crate::derivation`]) is the
//!    *capability* derivation tree (who delegated this cap). This module is the
//!    orthogonal *state* derivation: not "who may act" but "what value this cell
//!    must hold given those cells".
//!
//! # The soundness story (what binds the derivation)
//!
//! Let `D` be a derived cell over sources `S = [s_1, ..., s_n]` with spec
//! `f`. The binding is:
//!
//! 1. `D`'s heap holds, under [`DERIVATION_COLL`], the **spec digest**
//!    `H(spec)` (key [`KEY_SPEC_DIGEST`]) and the **claimed result**
//!    `f(S)` (key [`KEY_CLAIMED_VALUE`]).
//! 2. Because the heap is in `D`'s canonical commitment, `D`'s commitment binds
//!    BOTH the spec and the claimed result.
//! 3. A verifier holding `D`'s commitment, `D`'s heap-openings for those two
//!    keys, and the source cells' committed states (each itself ledger-bound)
//!    recomputes `f(S)` and checks it equals the claimed result.
//!
//! A **forged** derived cell — one whose claimed result ≠ `f(S)` — fails step 3.
//! A **stale** derived cell — one whose source changed but which was not
//! re-derived — ALSO fails step 3, because the claimed result still reflects the
//! OLD sources. Both are rejected by the SAME check. There is no honest way to
//! present a derived cell whose committed claim disagrees with its sources.
//!
//! # The minimal genuine slice (this module)
//!
//! - [`DerivationSpec`]: the declaration. The seed op is [`Aggregate::SumBalance`]
//!   — sum of the source cells' (signed) balances — with [`Aggregate::SumField`]
//!   / [`Aggregate::Count`] / [`Aggregate::FilteredSumBalance`] alongside it so
//!   the shape is a join/filter view, not a single hardcoded sum.
//! - [`bind_derivation`]: evaluate the spec over the sources and write the
//!   (spec-digest, claimed-value) binding into the derived cell's heap — the
//!   **re-derive** step. A turn that updates a source MUST re-bind here, or the
//!   commitment goes stale.
//! - [`verify_derivation`]: the **forge detector** — recompute the spec over the
//!   sources and reject any derived cell whose bound claim disagrees.
//!
//! # Formal grounding (the invariant is PROVEN, not just smoke-tested)
//!
//! The derivation invariant enforced here — a derived cell's committed claim
//! EQUALS the derivation evaluated over its sources, with a forged/stale claim
//! rejected and the claim BOUND into the committed root — is the EXECUTOR image
//! of a proven Lean rung: `metatheory/Dregg2/Deos/DerivedCell.lean`. There the
//! committed-heap binding is the SAME proven sorted-Poseidon2 root
//! (`Substrate.Heap`, the cap-root machinery generalized to a generic leaf), and
//!
//!   * `bind_verifies` — re-deriving (`bind`) produces a cell the same spec+
//!     sources verify (honest round-trip);
//!   * `forged_value_rejected` — a committed claim ≠ `f(sources)` does NOT verify
//!     (the Lean image of [`tests::forged_value_is_rejected`]);
//!   * `stale_rejected` — a cell bound at old sources, verified against new ones
//!     whose fold differs, is rejected by the SAME check (the image of
//!     [`tests::stale_after_source_change_is_rejected`]);
//!   * `wrong_spec_rejected` — a cell cannot be re-interpreted under a spec it did
//!     not bind (the image of [`tests::wrong_spec_is_rejected`]);
//!   * **`claim_bound_in_root`** — equal committed roots ⟹ equal claim: the claim
//!     rides the committed root, so a forge cannot keep the honest root with a
//!     lying claim (the image of [`tests::claim_is_bound_into_commitment`]), with
//!     `forged_claim_moves_root` the anti-ghost,
//!
//! all `#assert_all_clean` (kernel-axiom-clean), proven BY REUSE of the heap root
//! (`Heap.hget_hset_self` / `hget_hset_frame` / `root_binds_get`) — no derived-
//! cell-local commitment. The test [`tests::invariant_matches_lean_rung`] mirrors
//! that rung's witnesses (Σ[100,250,50] = 400, forge 999, stale, wrong-spec,
//! filtered) so the Rust is checked against the proven statement.
//!
//! # The next slice (named, the VK-affecting follow-up)
//!
//! The Lean rung above grounds the EXECUTOR forge-rejection: a verifier holding
//! the sources rejects forges and staleness. The remaining slice is the
//! **in-circuit witness**: a light client verifying a *batch* should see the
//! derivation constraint enforced by the EffectVM circuit, so the re-derivation
//! is part of the proven kernel transition rather than an out-of-band executor
//! check. That requires (a) a `DeriveCell` effect descriptor whose gate binds
//! `claimed == f(sources)` into the commitment, and (b) membership proofs for the
//! sources' commitments as circuit witnesses — the VK-affecting weld named in
//! `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md` (derived row) and
//! `docs/deos/DERIVED-CELLS.md` §"Next slice: circuit binding". The value tooth
//! here is the *executor* tooth; the circuit tooth is its shadow.

use serde::{Deserialize, Serialize};

use crate::cell::Cell;
use crate::id::CellId;
use crate::state::{CellState, FieldElement};

/// Reserved heap collection id for the derivation binding. Lives inside the
/// cell's committed heap (so the binding is folded into the canonical state
/// commitment). Chosen high to avoid colliding with application heap
/// collections.
pub const DERIVATION_COLL: u32 = 0x07DE_717E_u32; // a fixed reserved id ("DERIVE")

/// Heap key (within [`DERIVATION_COLL`]) holding the 32-byte digest of the
/// derived cell's [`DerivationSpec`]. Binds *which* derivation this cell claims.
pub const KEY_SPEC_DIGEST: u32 = 0;

/// Heap key (within [`DERIVATION_COLL`]) holding the claimed RESULT of the
/// derivation as a canonical little-endian-encoded `i64`. Binds the *value*.
pub const KEY_CLAIMED_VALUE: u32 = 1;

/// How a derived cell aggregates its source cells into a single value.
///
/// Every variant is a deterministic function of the sources' COMMITTED states
/// (the same bytes a light client sees), so the verifier can recompute it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Aggregate {
    /// `value = Σ source.balance`. The materialized-aggregate seed: a treasury
    /// cell whose balance is the sum of its member accounts' balances.
    SumBalance,
    /// `value = Σ source.state.fields[index]` (each field read as a little-endian
    /// `i64`). A relational view over a user state field.
    SumField {
        /// Which of the 16 state field slots to sum.
        field_index: usize,
    },
    /// `value = | sources |`. A count view (the cardinality of the relation).
    Count,
    /// `value = Σ { source.balance : source.balance >= threshold }`. A
    /// filter-then-sum view (a join/filter over the source relation).
    FilteredSumBalance {
        /// Only sources whose balance is `>= threshold` contribute.
        threshold: i64,
    },
}

/// A derivation specification: a derived cell's state is a function of these
/// `sources` under this `aggregate`.
///
/// The `sources` are the cells the derived cell is a view OVER. The order is
/// significant for the spec digest (so reordering sources is a distinct spec),
/// but each [`Aggregate`] here is order-insensitive in its *value* (sums /
/// counts), which is the intended semantics for a set-aggregate view.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DerivationSpec {
    /// The source cells this view is derived from.
    pub sources: Vec<CellId>,
    /// How the sources are aggregated into the derived value.
    pub aggregate: Aggregate,
}

/// Why a derived cell failed verification.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DerivationError {
    /// The cell carries no derivation binding (no spec digest in its heap).
    NotADerivedCell,
    /// A source cell named by the spec was not supplied to the verifier.
    MissingSource(CellId),
    /// The supplied spec's digest does not match the one bound in the cell —
    /// the verifier was handed the wrong derivation for this cell.
    SpecMismatch,
    /// THE FORGE / STALE REJECTION: the value bound in the derived cell's
    /// commitment does not equal the derivation evaluated over the sources.
    ValueMismatch {
        /// What the cell claims (and committed to).
        claimed: i64,
        /// What the derivation actually evaluates to over the sources.
        actual: i64,
    },
}

impl std::fmt::Display for DerivationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DerivationError::NotADerivedCell => write!(f, "cell carries no derivation binding"),
            DerivationError::MissingSource(id) => {
                write!(f, "source cell {id:?} not supplied to verifier")
            }
            DerivationError::SpecMismatch => {
                write!(
                    f,
                    "supplied spec digest does not match the bound derivation"
                )
            }
            DerivationError::ValueMismatch { claimed, actual } => write!(
                f,
                "derived value forged or stale: cell claims {claimed} but derivation evaluates to {actual}"
            ),
        }
    }
}

impl std::error::Error for DerivationError {}

impl DerivationSpec {
    /// Build a "sum of source balances" view — the materialized-aggregate seed.
    pub fn sum_balance(sources: impl IntoIterator<Item = CellId>) -> Self {
        DerivationSpec {
            sources: sources.into_iter().collect(),
            aggregate: Aggregate::SumBalance,
        }
    }

    /// A 32-byte canonical digest of this spec. Domain-separated so a spec
    /// digest can never collide with any other heap value's preimage. This is
    /// what gets bound at [`KEY_SPEC_DIGEST`] in the derived cell's heap.
    pub fn digest(&self) -> FieldElement {
        let mut hasher = blake3::Hasher::new_derive_key("dregg.derived-cell.spec.v1");
        hasher.update(&(self.sources.len() as u64).to_le_bytes());
        for s in &self.sources {
            hasher.update(s.as_bytes());
        }
        match &self.aggregate {
            Aggregate::SumBalance => hasher.update(&[0u8]),
            Aggregate::SumField { field_index } => {
                hasher.update(&[1u8]);
                hasher.update(&(*field_index as u64).to_le_bytes())
            }
            Aggregate::Count => hasher.update(&[2u8]),
            Aggregate::FilteredSumBalance { threshold } => {
                hasher.update(&[3u8]);
                hasher.update(&threshold.to_le_bytes())
            }
        };
        *hasher.finalize().as_bytes()
    }

    /// Evaluate the derivation over a set of source cells, returning the value
    /// the derived cell MUST hold. The single source of truth shared by
    /// [`bind_derivation`] (the writer) and [`verify_derivation`] (the checker):
    /// the prover and the verifier compute the SAME function, so a forge cannot
    /// hide in a discrepancy between them.
    ///
    /// `resolve` maps each source [`CellId`] to its (committed) cell; returns
    /// `None` if a source is missing.
    pub fn evaluate<'a>(
        &self,
        mut resolve: impl FnMut(&CellId) -> Option<&'a Cell>,
    ) -> Result<i64, DerivationError> {
        let mut sources: Vec<&Cell> = Vec::with_capacity(self.sources.len());
        for id in &self.sources {
            let c = resolve(id).ok_or(DerivationError::MissingSource(*id))?;
            sources.push(c);
        }
        Ok(self.aggregate.fold(&sources))
    }
}

impl Aggregate {
    /// Fold this aggregate over already-resolved source cells. Saturating
    /// arithmetic: an overflowing aggregate clamps rather than wrapping (a
    /// wrap would let a forger drive the sum to an attacker-chosen value).
    fn fold(&self, sources: &[&Cell]) -> i64 {
        match self {
            Aggregate::SumBalance => sources
                .iter()
                .fold(0i64, |acc, c| acc.saturating_add(c.state.balance())),
            Aggregate::SumField { field_index } => sources.iter().fold(0i64, |acc, c| {
                let v = c
                    .state
                    .get_field(*field_index)
                    .map(|f| field_to_i64(f))
                    .unwrap_or(0);
                acc.saturating_add(v)
            }),
            Aggregate::Count => sources.len() as i64,
            Aggregate::FilteredSumBalance { threshold } => sources.iter().fold(0i64, |acc, c| {
                let b = c.state.balance();
                if b >= *threshold {
                    acc.saturating_add(b)
                } else {
                    acc
                }
            }),
        }
    }
}

/// Read a 32-byte state field as a little-endian `i64` (low 8 bytes). The
/// inverse of how [`encode_value_into_field`] writes a small integer field.
fn field_to_i64(f: &FieldElement) -> i64 {
    let mut buf = [0u8; 8];
    buf.copy_from_slice(&f[0..8]);
    i64::from_le_bytes(buf)
}

/// Encode an `i64` value as a 32-byte heap [`FieldElement`] (little-endian in
/// the low 8 bytes, zero-padded). Round-trips with [`field_to_i64`] and
/// [`decode_value_from_field`].
pub fn encode_value_into_field(value: i64) -> FieldElement {
    let mut f = [0u8; 32];
    f[0..8].copy_from_slice(&value.to_le_bytes());
    f
}

/// Decode a [`KEY_CLAIMED_VALUE`] heap field back to the `i64` it encodes.
pub fn decode_value_from_field(f: &FieldElement) -> i64 {
    field_to_i64(f)
}

/// Whether a cell carries a derivation binding (a spec digest in its reserved
/// heap collection). A plain (non-derived) cell returns `false`.
pub fn is_derived(cell: &Cell) -> bool {
    cell.state
        .get_heap(DERIVATION_COLL, KEY_SPEC_DIGEST)
        .is_some()
}

/// The spec digest bound in a derived cell's committed heap, if any.
pub fn bound_spec_digest(cell: &Cell) -> Option<FieldElement> {
    cell.state.get_heap(DERIVATION_COLL, KEY_SPEC_DIGEST)
}

/// The claimed value bound in a derived cell's committed heap, if any.
pub fn bound_claimed_value(cell: &Cell) -> Option<i64> {
    cell.state
        .get_heap(DERIVATION_COLL, KEY_CLAIMED_VALUE)
        .map(|f| decode_value_from_field(&f))
}

/// **Re-derive**: evaluate `spec` over the sources resolved by `resolve` and
/// write the (spec-digest, claimed-value) binding into the derived cell's
/// committed heap. This is the step a turn that updates a source MUST perform —
/// it is what re-seals the derived cell's commitment to its current sources.
///
/// Returns the freshly derived value on success. After this call,
/// [`verify_derivation`] with the SAME spec and sources accepts; if the sources
/// later change without a re-bind, the bound value goes stale and verification
/// rejects.
pub fn bind_derivation<'a>(
    derived: &mut Cell,
    spec: &DerivationSpec,
    resolve: impl FnMut(&CellId) -> Option<&'a Cell>,
) -> Result<i64, DerivationError> {
    let value = spec.evaluate(resolve)?;
    write_binding(&mut derived.state, spec, value);
    Ok(value)
}

/// Write the derivation binding directly into a [`CellState`]'s heap. Lower-level
/// than [`bind_derivation`] (does not evaluate): used by the executor when it has
/// already computed the value, and by tests constructing forged/stale cells.
pub fn write_binding(state: &mut CellState, spec: &DerivationSpec, value: i64) {
    state.set_heap(DERIVATION_COLL, KEY_SPEC_DIGEST, spec.digest());
    state.set_heap(
        DERIVATION_COLL,
        KEY_CLAIMED_VALUE,
        encode_value_into_field(value),
    );
}

/// **The forge detector.** Verify that a derived cell's committed claim equals
/// the derivation `spec` evaluated over its sources (resolved by `resolve`).
///
/// This is the single check that rejects BOTH forges (claimed ≠ derivation) and
/// staleness (sources moved on, claim did not). It rejects:
///
/// - [`DerivationError::NotADerivedCell`] if the cell has no binding,
/// - [`DerivationError::SpecMismatch`] if the supplied spec is not the one the
///   cell bound (a verifier handed the wrong derivation),
/// - [`DerivationError::MissingSource`] if a source is unavailable,
/// - [`DerivationError::ValueMismatch`] — THE FORGE — if the bound value ≠ the
///   recomputed derivation.
///
/// Returns the verified value on acceptance.
pub fn verify_derivation<'a>(
    derived: &Cell,
    spec: &DerivationSpec,
    resolve: impl FnMut(&CellId) -> Option<&'a Cell>,
) -> Result<i64, DerivationError> {
    // 1. The cell must actually carry a binding.
    let bound_digest = bound_spec_digest(derived).ok_or(DerivationError::NotADerivedCell)?;

    // 2. The supplied spec must be the one the cell committed to. Otherwise a
    //    verifier could "verify" cell D against a spec it never claimed.
    if bound_digest != spec.digest() {
        return Err(DerivationError::SpecMismatch);
    }

    // 3. The claimed (committed) value.
    let claimed = bound_claimed_value(derived).ok_or(DerivationError::NotADerivedCell)?;

    // 4. Recompute the derivation over the SOURCES — the same `evaluate` the
    //    binder used. The forge/stale cell diverges here.
    let actual = spec.evaluate(resolve)?;

    if claimed != actual {
        return Err(DerivationError::ValueMismatch { claimed, actual });
    }
    Ok(actual)
}

/// Convenience: resolve sources from a slice of `(CellId, &Cell)` pairs. Returns
/// a closure suitable for [`verify_derivation`] / [`bind_derivation`].
pub fn resolver_from_pairs<'a>(
    pairs: &'a [(CellId, &'a Cell)],
) -> impl FnMut(&CellId) -> Option<&'a Cell> {
    move |id| pairs.iter().find(|(pid, _)| pid == id).map(|(_, c)| *c)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cell::Cell;

    fn cell_with_balance(seed: u8, balance: i64) -> Cell {
        Cell::with_balance([seed; 32], [seed; 32], balance)
    }

    /// THE HONEST PATH: a derived-sum cell whose claim equals the sum of its
    /// sources verifies.
    #[test]
    fn honest_sum_verifies() {
        let s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let s3 = cell_with_balance(3, 50);
        let spec = DerivationSpec::sum_balance([s1.id(), s2.id(), s3.id()]);

        let mut derived = cell_with_balance(9, 0);
        let pairs = [(s1.id(), &s1), (s2.id(), &s2), (s3.id(), &s3)];

        let v = bind_derivation(&mut derived, &spec, resolver_from_pairs(&pairs)).unwrap();
        assert_eq!(v, 400, "100 + 250 + 50");

        // The derived cell's commitment now binds the derivation.
        assert!(is_derived(&derived));
        assert_eq!(bound_claimed_value(&derived), Some(400));

        // The forge detector accepts the honest cell.
        let ok = verify_derivation(&derived, &spec, resolver_from_pairs(&pairs));
        assert_eq!(ok, Ok(400));
    }

    /// THE FORGE: a derived cell that claims a value != the sum of its sources
    /// is REJECTED by the derivation check. This is the genuine slice — the
    /// rejection is the derivation constraint biting, not a stub.
    #[test]
    fn forged_value_is_rejected() {
        let s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let spec = DerivationSpec::sum_balance([s1.id(), s2.id()]);
        let pairs = [(s1.id(), &s1), (s2.id(), &s2)];

        // Construct a forged derived cell: it bears a VALID spec binding (so it
        // looks like a derived cell and the spec digest matches) but a LYING
        // claimed value of 999 instead of the true 350.
        let mut forged = cell_with_balance(9, 0);
        write_binding(&mut forged.state, &spec, 999);

        let result = verify_derivation(&forged, &spec, resolver_from_pairs(&pairs));
        assert_eq!(
            result,
            Err(DerivationError::ValueMismatch {
                claimed: 999,
                actual: 350,
            }),
            "a forged derived value must be rejected by the derivation constraint"
        );
    }

    /// THE STALE REJECTION: a derived cell that was honestly derived, but whose
    /// source then changed without a re-derive, is rejected by the SAME check.
    #[test]
    fn stale_after_source_change_is_rejected() {
        let mut s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let spec = DerivationSpec::sum_balance([s1.id(), s2.id()]);

        // Honestly derive at the old source state.
        let mut derived = cell_with_balance(9, 0);
        {
            let pairs = [(s1.id(), &s1), (s2.id(), &s2)];
            let v = bind_derivation(&mut derived, &spec, resolver_from_pairs(&pairs)).unwrap();
            assert_eq!(v, 350);
        }

        // A source moves on. The derived cell is NOT re-derived.
        s1.state.apply_balance_change(500);
        assert_eq!(s1.state.balance(), 600);

        // Verification against the NEW sources rejects the stale claim.
        let pairs = [(s1.id(), &s1), (s2.id(), &s2)];
        let result = verify_derivation(&derived, &spec, resolver_from_pairs(&pairs));
        assert_eq!(
            result,
            Err(DerivationError::ValueMismatch {
                claimed: 350,
                actual: 850,
            })
        );

        // Re-deriving (the turn that touched the source MUST do this) restores
        // acceptance — and the derived cell's commitment changes, so a light
        // client sees the update.
        let before = derived.state_commitment();
        bind_derivation(&mut derived, &spec, resolver_from_pairs(&pairs)).unwrap();
        let after = derived.state_commitment();
        assert_ne!(before, after, "re-derivation re-seals the commitment");
        assert_eq!(
            verify_derivation(&derived, &spec, resolver_from_pairs(&pairs)),
            Ok(850)
        );
    }

    /// The binding is bound into the canonical state commitment: two derived
    /// cells with different claimed values have different commitments. This is
    /// WHY a forge cannot be hidden — the claim is part of what the light client
    /// verifies.
    #[test]
    fn claim_is_bound_into_commitment() {
        let s1 = cell_with_balance(1, 100);
        let spec = DerivationSpec::sum_balance([s1.id()]);

        let mut honest = cell_with_balance(9, 0);
        write_binding(&mut honest.state, &spec, 100);

        let mut forged = cell_with_balance(9, 0);
        write_binding(&mut forged.state, &spec, 999);

        assert_ne!(
            honest.state_commitment(),
            forged.state_commitment(),
            "the claimed derived value is folded into the canonical commitment"
        );
    }

    /// Verifying a derived cell against the WRONG spec is rejected (you cannot
    /// re-interpret a cell as deriving from a different relation than it bound).
    #[test]
    fn wrong_spec_is_rejected() {
        let s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let spec_sum = DerivationSpec::sum_balance([s1.id(), s2.id()]);
        let spec_count = DerivationSpec {
            sources: vec![s1.id(), s2.id()],
            aggregate: Aggregate::Count,
        };
        let pairs = [(s1.id(), &s1), (s2.id(), &s2)];

        let mut derived = cell_with_balance(9, 0);
        bind_derivation(&mut derived, &spec_sum, resolver_from_pairs(&pairs)).unwrap();

        // Re-interpreting the sum-cell as a count-cell is rejected at the spec
        // digest, before any value comparison.
        assert_eq!(
            verify_derivation(&derived, &spec_count, resolver_from_pairs(&pairs)),
            Err(DerivationError::SpecMismatch)
        );
    }

    /// A filtered-sum view (a filter/join over the relation) derives and
    /// verifies, and a forged filtered value is rejected.
    #[test]
    fn filtered_sum_view() {
        let s1 = cell_with_balance(1, 100); // included
        let s2 = cell_with_balance(2, 30); // filtered out (< 50)
        let s3 = cell_with_balance(3, 250); // included
        let spec = DerivationSpec {
            sources: vec![s1.id(), s2.id(), s3.id()],
            aggregate: Aggregate::FilteredSumBalance { threshold: 50 },
        };
        let pairs = [(s1.id(), &s1), (s2.id(), &s2), (s3.id(), &s3)];

        let mut derived = cell_with_balance(9, 0);
        let v = bind_derivation(&mut derived, &spec, resolver_from_pairs(&pairs)).unwrap();
        assert_eq!(v, 350, "100 + 250, the 30-balance source filtered out");
        assert_eq!(
            verify_derivation(&derived, &spec, resolver_from_pairs(&pairs)),
            Ok(350)
        );

        // forge it
        let mut forged = cell_with_balance(9, 0);
        write_binding(&mut forged.state, &spec, 380); // pretends s2 counted
        assert!(matches!(
            verify_derivation(&forged, &spec, resolver_from_pairs(&pairs)),
            Err(DerivationError::ValueMismatch { .. })
        ));
    }

    /// A missing source is rejected (the verifier was not given everything the
    /// relation depends on).
    #[test]
    fn missing_source_is_rejected() {
        let s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let spec = DerivationSpec::sum_balance([s1.id(), s2.id()]);

        let mut derived = cell_with_balance(9, 0);
        {
            let pairs = [(s1.id(), &s1), (s2.id(), &s2)];
            bind_derivation(&mut derived, &spec, resolver_from_pairs(&pairs)).unwrap();
        }

        // Only supply s1.
        let pairs = [(s1.id(), &s1)];
        assert_eq!(
            verify_derivation(&derived, &spec, resolver_from_pairs(&pairs)),
            Err(DerivationError::MissingSource(s2.id()))
        );
    }

    /// The Lean rung: this executor invariant is PROVEN, not just smoke-tested.
    ///
    /// Mirror of the witnesses in `metatheory/Dregg2/Deos/DerivedCell.lean`
    /// (`bind_verifies` / `forged_value_rejected` / `stale_rejected` /
    /// `wrong_spec_rejected` / `claim_bound_in_root`, all `#assert_all_clean`).
    /// The Lean binds the claim into the proven sorted-Poseidon2 `Heap.root`;
    /// here the SAME structure is checked over the deployed [`CellState`] heap, so
    /// the Rust forge-rejection is checked against the proven statement, not just
    /// an ad-hoc tampering.
    ///
    /// Lean: sources balances [100, 250, 50], Σ = 400; a forged 999 is rejected
    /// and MOVES the root; a stale claim (a source moves 100 → 600, Σ = 900) is
    /// rejected; the wrong spec (count vs sum) is rejected; a filtered-sum at
    /// threshold 60 keeps {100, 250} = 350.
    #[test]
    fn invariant_matches_lean_rung() {
        let s1 = cell_with_balance(1, 100);
        let s2 = cell_with_balance(2, 250);
        let s3 = cell_with_balance(3, 50);
        let spec = DerivationSpec::sum_balance([s1.id(), s2.id(), s3.id()]);
        let pairs = [(s1.id(), &s1), (s2.id(), &s2), (s3.id(), &s3)];

        // `bind_verifies`: re-deriving binds the fold (Σ = 400) and verifies.
        let mut honest = cell_with_balance(9, 0);
        let v = bind_derivation(&mut honest, &spec, resolver_from_pairs(&pairs)).unwrap();
        assert_eq!(v, 400);
        assert_eq!(
            verify_derivation(&honest, &spec, resolver_from_pairs(&pairs)),
            Ok(400)
        );

        // `forged_value_rejected` + `forged_claim_moves_root`: a lying 999 does
        // NOT verify AND moves the committed root (cannot hide under the honest one).
        let mut forged = honest.clone();
        write_binding(&mut forged.state, &spec, 999);
        assert!(matches!(
            verify_derivation(&forged, &spec, resolver_from_pairs(&pairs)),
            Err(DerivationError::ValueMismatch {
                claimed: 999,
                actual: 400
            })
        ));
        assert_ne!(
            honest.state_commitment(),
            forged.state_commitment(),
            "claim_bound_in_root: a forged claim moves the committed root"
        );

        // `stale_rejected`: a source moves (100 → 600, Σ = 900); the un-re-derived
        // cell is rejected against the new sources by the SAME value check.
        let mut s1b = cell_with_balance(1, 100);
        s1b.state.apply_balance_change(500);
        assert_eq!(s1b.state.balance(), 600);
        let new_pairs = [(s1b.id(), &s1b), (s2.id(), &s2), (s3.id(), &s3)];
        assert!(matches!(
            verify_derivation(&honest, &spec, resolver_from_pairs(&new_pairs)),
            Err(DerivationError::ValueMismatch {
                claimed: 400,
                actual: 900
            })
        ));

        // `wrong_spec_rejected`: re-interpreting the sum-cell as a count-cell is
        // rejected at the spec digest.
        let count_spec = DerivationSpec {
            sources: vec![s1.id(), s2.id(), s3.id()],
            aggregate: Aggregate::Count,
        };
        assert_eq!(
            verify_derivation(&honest, &count_spec, resolver_from_pairs(&pairs)),
            Err(DerivationError::SpecMismatch)
        );

        // The filtered-sum view (threshold 60 keeps {100, 250}) = 350.
        let filt_spec = DerivationSpec {
            sources: vec![s1.id(), s2.id(), s3.id()],
            aggregate: Aggregate::FilteredSumBalance { threshold: 60 },
        };
        let mut filtered = cell_with_balance(9, 0);
        assert_eq!(
            bind_derivation(&mut filtered, &filt_spec, resolver_from_pairs(&pairs)).unwrap(),
            350
        );
        assert_eq!(
            verify_derivation(&filtered, &filt_spec, resolver_from_pairs(&pairs)),
            Ok(350)
        );
    }

    /// The value encode/decode round-trips across the full i64 range, including
    /// negatives (issuer wells carry negative balances).
    #[test]
    fn value_encoding_roundtrips() {
        for v in [0i64, 1, -1, 42, -42, i64::MAX, i64::MIN, 1_000_000_000] {
            assert_eq!(decode_value_from_field(&encode_value_into_field(v)), v);
        }
    }
}
