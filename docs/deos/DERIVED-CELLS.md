# Derived / Relational Cells — a cell whose state IS a verifiable function of other cells

A light client of dregg can already verify *"this cell changed"*: the canonical
state commitment binds a cell's full state, and a ledger membership proof binds
that commitment into the global root. The next thing a light client should be
able to verify is *"this cell is correctly **derived from** those cells"* — that
a treasury cell's balance really is the sum of its member accounts, that a view
cell really is the join/filter it claims to be over its sources.

This is Track 2 (capacity) of *safely live within dregg*, VK-freedom era. It is
**built, not memoed** — a new module `cell/src/derived.rs` — and it is a **weld**:
the substrate it needs (an openable committed heap, the signed balance ledger)
already exists; the module joins it into the derived-cell capacity and adds the
**forge detector** that makes the derivation load-bearing.

---

## 1. What a derived cell is

A **derived cell** `D` carries a `DerivationSpec`: a declaration of the form

> *my value = `f`(those source cells)*

together with the **claimed result** of evaluating `f` over the sources. `f` is
one of the `Aggregate` ops (the minimal genuine slice ships four):

| `Aggregate`            | meaning                                            | the view it is        |
|------------------------|----------------------------------------------------|-----------------------|
| `SumBalance`           | `Σ source.balance`                                 | a materialized sum    |
| `SumField { i }`       | `Σ source.fields[i]` (as i64)                      | a relational aggregate |
| `Count`                | `| sources |`                                      | a cardinality view    |
| `FilteredSumBalance { t }` | `Σ { b : b ≥ t }`                              | a filter/join + sum   |

The seed is `SumBalance` — the treasury cell whose balance is the sum of its
member accounts. The other three are present so the shape is a join/filter view,
not a single hardcoded sum.

---

## 2. The weld (what already existed, disconnected)

`cell/src/derived.rs` builds on substrate already in the tree:

- **The committed heap** — `CellState::set_heap` / `compute_heap_root`
  (`cell/src/state.rs`). An openable sorted-Poseidon2 `(collection, key) →
  FieldElement` map that is **already folded into the canonical state
  commitment** (`compute_canonical_state_commitment` absorbs `heap_root`). We
  reserve a collection id, `DERIVATION_COLL`, inside it. Binding a derivation is
  therefore a heap write, and the derived cell's commitment binds the derivation
  **for free, with no commitment-version bump**.

- **The signed balance ledger** — `CellState::balance` (`i64`), the same `bal :
  cell → asset → ℤ` the Lean kernel carries. This is the source quantity the
  `SumBalance`/`FilteredSumBalance` views aggregate, negatives (issuer wells)
  included.

- **`cell/src/derivation.rs`** is the orthogonal *capability* derivation tree
  (the seL4-style CDT: who delegated this cap, provenance for revocation). This
  module is *state* derivation: not "who may act" but "what value this cell must
  hold given those cells". The two names sit side by side deliberately.

The reactive effect (`turn/src/reactive.rs`) and the cap region are owned by
sibling work; this module touches neither.

---

## 3. The soundness story — what binds the derivation

Let `D` be derived over sources `S = [s₁ … sₙ]` with spec `f`. The binding:

1. `D`'s committed heap holds, under `DERIVATION_COLL`:
   - at key `KEY_SPEC_DIGEST` — `H(spec)`, the domain-separated digest of the
     spec (which sources, which aggregate);
   - at key `KEY_CLAIMED_VALUE` — `f(S)`, the claimed result, as a canonical
     little-endian `i64`.
2. Because the heap is in `D`'s canonical commitment, **`D`'s commitment binds
   both the spec and the claimed result.** (`claim_is_bound_into_commitment`
   proves two derived cells with different claims have different commitments.)
3. A verifier holding `D`'s commitment, `D`'s heap-openings for those two keys,
   and the source cells' committed states (each itself ledger-bound) recomputes
   `f(S)` — with the *same* `evaluate` the binder used — and checks it equals the
   claimed result.

**The forge.** A derived cell whose claimed result ≠ `f(S)` fails step 3:
`verify_derivation` returns `ValueMismatch { claimed, actual }`. There is no
discrepancy a forger can hide in, because the prover (`bind_derivation`) and the
verifier (`verify_derivation`) call the *one* `DerivationSpec::evaluate`.

**Staleness is the same rejection.** A derived cell honestly derived at the old
source state, whose source then changed without a re-derive, still carries the
*old* claimed value. Verified against the *new* sources it fails the *same*
`ValueMismatch` check. So a turn that updates a source **must re-derive** (call
`bind_derivation`) or the derived cell's commitment is stale = rejected. There is
no honest way to present a derived cell whose committed claim disagrees with its
sources.

---

## 4. The API (the genuine slice)

`cell/src/derived.rs`:

- `DerivationSpec { sources: Vec<CellId>, aggregate: Aggregate }` — the
  declaration; `DerivationSpec::sum_balance(sources)` builds the seed view.
- `DerivationSpec::digest()` — the 32-byte domain-separated spec digest.
- `DerivationSpec::evaluate(resolve)` — the single source of truth, shared by
  binder and verifier.
- `bind_derivation(&mut derived, &spec, resolve)` — **re-derive**: evaluate over
  the sources and write `(spec-digest, claimed-value)` into the derived cell's
  committed heap. This re-seals the commitment to the current sources.
- `verify_derivation(&derived, &spec, resolve)` — **the forge detector**:
  recompute and reject `NotADerivedCell` / `SpecMismatch` / `MissingSource` /
  `ValueMismatch` (the forge/stale rejection). Returns the verified value on
  acceptance.
- `is_derived` / `bound_spec_digest` / `bound_claimed_value` — read the binding.

### The forge is genuinely rejected

The unit tests in `cell/src/derived.rs` (all green, `cargo test -p dregg-cell
--lib derived::`):

- `honest_sum_verifies` — an honest derived-sum cell verifies (`100+250+50=400`).
- `forged_value_is_rejected` — a cell claiming `999` over sources summing to
  `350` is rejected by `ValueMismatch`. **Not a stub** — the derivation
  constraint bites.
- `stale_after_source_change_is_rejected` — honest derive, then a source moves;
  the un-re-derived cell is rejected; re-deriving restores acceptance *and*
  changes the commitment (a light client sees the update).
- `claim_is_bound_into_commitment` — different claims ⇒ different commitments
  (why a forge cannot be hidden).
- `wrong_spec_is_rejected`, `filtered_sum_view`, `missing_source_is_rejected`,
  `value_encoding_roundtrips` (incl. `i64::MIN`/`MAX` and negatives).
- `invariant_matches_lean_rung` — the Rust↔Lean tie: the executor forge/stale
  rejection agrees with the `Dregg2/Deos/DerivedCell.lean` theorem (see §5).

---

## 5. Next slice: circuit binding

The check in §3–4 is **executor-level** — a genuine forge rejection a verifier
runs in the clear. The **executor-invariant Lean rung has since landed**:
`metatheory/Dregg2/Deos/DerivedCell.lean` proves `bind_verifies` (honest
round-trip), `forged_value_rejected` (the forge tooth), and `stale_rejected` (the
stale tooth) as theorems, and `cell/src/derived.rs::tests::invariant_matches_lean_rung`
ties the Rust rejection to it. What remains is the **in-circuit witness**, so that a
light client verifying a *batch* sees the derivation enforced by the EffectVM
circuit (part of the proven kernel transition) rather than re-running the check
out of band:

1. A `DeriveCell` effect descriptor whose **gate binds `claimed == f(sources)`**
   into the commitment — the same shape as the value/note gates already in
   `circuit/descriptors/`. The gate must bind the re-derivation into the
   commitment, else the rung is FALSE (the standing circuit-soundness apex bar).
2. The sources' committed states as **membership-proof witnesses** (each source's
   commitment proven in the ledger root, the heap-opening for the
   `KEY_CLAIMED_VALUE` key proven against the derived cell's `heap_root`).
3. A Lean rung: `verifyBatch accept ⟹ derived.claimed = f(sources.committed)`,
   joining the circuit-soundness obligation table (the grounded circuit what-is now
   lives at `docs/reference/lean-circuit.md`). This is the *in-circuit* sibling of
   the executor-invariant `DerivedCell.lean` rung above.

Until that lands, derived cells are sound under the executor check, the landed
executor-invariant Lean rung, and the commitment binding; the **in-circuit**
verifyBatch rung is the one named follow-up, not a silent gap.
