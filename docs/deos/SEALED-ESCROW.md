# Sealed Escrow — an atomic two-party value exchange a sovereign agent can trust

An autonomous agent living inside dregg needs to *exchange* value with a
counterparty it does not trust: *"I give you X iff you give me Y."* The danger is
the half-open trade — A hands over its leg and B never reciprocates, or B walks
away with A's leg without ever locking its own. A **sealed escrow** closes that
gap. Each party locks one *leg* into a shared escrow cell; the exchange completes
**atomically** only when both conforming legs are present; and until completion
each party may **reclaim** its own leg. No party can ever leave holding the
counterparty's leg without having genuinely deposited its own conforming leg, and
no leg is ever claimable twice.

This is Track 2 (capacity) of *safely live within dregg*, VK-freedom era. It is
**built, not memoed** — a new module `cell/src/escrow_sealed.rs` — and it is a
**weld**: the substrate it needs (an openable committed heap, the signed balance
ledger, the one-shot nullifier discipline) already exists; the module joins it
into the escrow capacity and adds the **forge detectors** that make atomicity and
one-shot consumption load-bearing.

---

## 1. What a sealed escrow is

An escrow cell carries `EscrowTerms` — a 2-of-2 swap declaration:

> party **A** must lock at least `min_a` of `asset_a`; party **B** must lock at
> least `min_b` of `asset_b`.

and a pair of **legs**, each tracked by a status (`Empty` / `Deposited` /
`Consumed`) and a committed amount. The lifecycle:

| op            | meaning                                                         |
|---------------|----------------------------------------------------------------|
| `open_escrow` | bind the terms digest; both legs `Empty`                       |
| `deposit_leg` | lock a conforming leg; that side → `Deposited` (one-shot from `Empty`) |
| `settle`      | both legs present & conforming ⟹ consume BOTH atomically       |
| `reclaim_leg` | the depositor pulls its own un-consumed leg back; that side → `Consumed` |

The genuine minimal slice is the **2-of-2 atomic swap**. HTLC timelocks, k-of-n,
and multi-asset baskets are the named next slice, not stubs here.

---

## 2. The weld (what already existed, disconnected)

`cell/src/escrow_sealed.rs` builds on substrate already in the tree:

- **The committed heap** — `CellState::set_heap` / `compute_heap_root`
  (`cell/src/state.rs`). An openable sorted-Poseidon2 `(collection, key) →
  FieldElement` map **already folded into the canonical state commitment**. We
  reserve a collection id, `ESCROW_COLL`, inside it for the escrow ledger (terms
  digest, both legs' amounts, both legs' status flags). Binding the whole escrow
  is therefore a handful of heap writes, and the escrow cell's commitment binds
  the exchange **for free, with no commitment-version bump** — the same discipline
  `cell/src/derived.rs` uses for the derivation binding.

- **The signed `i64` balance ledger** — `CellState::balance`, the same `bal :
  cell → asset → ℤ` the Lean kernel carries — is the value primitive. A leg locks
  an `amount` of value; settlement returns the `(amount_a, amount_b)` the executor
  moves to the counterparties.

- **The one-shot nullifier / spend discipline** (the note/membrane "consume
  exactly once" tooth) is the shape the leg-`Consumed` flag takes. Settling or
  reclaiming flips a per-leg status felt in the committed heap to `Consumed`, and
  every claim/settle/reclaim path checks it first — a consumed leg is a spent
  nullifier, refused on replay.

The circuit, the reactive/conditional effects, and the facet bits are owned by
sibling work; this module touches none of them. It reuses the existing
`EFFECT_ESCROW_OPS` / `EFFECT_SEAL_OPS` facet bits rather than adding any.

---

## 3. The soundness story — what binds the exchange

The terms digest, each leg's status, and each leg's committed amount live under
`ESCROW_COLL` in the escrow cell's heap, hence in its canonical commitment
(`escrow_state_is_bound_into_commitment` proves depositing a leg changes the
commitment — a light client sees value enter). Against a holder of the commitment
+ heap openings, the binding enforces:

1. **No claim without a conforming own deposit.** To take the counterparty's leg,
   a `Claim` must present the claimant's OWN deposited leg, and that leg must
   (a) conform to the terms (right party, right asset, amount `≥` the required
   minimum and `> 0`), and (b) be `Deposited` and live in the committed state at
   the committed amount. A claimant that never deposited — or under-deposited —
   is rejected (`LegNotDeposited` / `NoConformingOwnDeposit`).

2. **Atomic settlement.** `settle` completes only when BOTH legs are `Deposited`
   and conforming; it then consumes both in one step. There is no partial
   settlement — if either leg is missing or non-conforming, nothing is consumed.

3. **One-shot.** Each leg's `Consumed` flag is in the commitment. Settling or
   reclaiming sets it; any later claim/settle/reclaim of a consumed leg is
   rejected (`LegAlreadyConsumed`). A settled leg cannot be replayed; a reclaimed
   leg cannot also be settled, and vice-versa.

4. **No over-claim.** The claimed value is bounded by the taken leg's committed
   amount: a claim asserting more than the leg locks diverges from the commitment
   and is rejected (`OverClaim { claimed, locked }`) — exactly as a forged derived
   value diverges from its sources in `cell/src/derived.rs`.

**Non-vacuity by construction.** The honest-accept path (`settle` accepting, and
a pre-settlement `check_claim` returning `Ok`) and every forge-reject path run
through the SAME `EscrowState::check_claim` / `EscrowState::settlement`
verification core. A stub in either direction fails one polarity: the replay and
over-claim tests first assert the honest claim *accepts*, then assert the forged
variant *rejects*, against the one core.

---

## 4. The API (the genuine slice)

`cell/src/escrow_sealed.rs`:

- `EscrowTerms::swap(a, b)` — the 2-of-2 declaration; `EscrowTerms::digest()` the
  domain-separated terms digest bound at `KEY_TERMS_DIGEST`.
- `open_escrow(&mut cell, &terms)` — seal the terms; both legs `Empty`.
- `deposit_leg(&mut cell, &terms, side, &leg)` — lock a conforming leg
  (one-shot from `Empty`; rejects non-conforming or double-lock).
- `EscrowState::read(&cell)` — recover the committed escrow state; the single
  source of truth every verification path consults.
- `EscrowState::check_claim(&terms, &claim)` — **the claim forge detector**:
  rejects `TermsMismatch` / `WrongClaimant` / `NoConformingOwnDeposit` /
  `LegNotDeposited` / `LegAlreadyConsumed` (one-shot) / `OverClaim`.
- `EscrowState::settlement(&terms)` — **the settlement forge detector**: accepts
  only when both legs are present, conforming, and unconsumed.
- `settle(&mut cell, &terms)` — atomic completion; consumes both legs, returns
  `(amount_a, amount_b)`.
- `reclaim_leg(&mut cell, &terms, side, by)` — depositor pulls back an un-consumed
  leg; one-shot (`NotYourLeg` for the wrong party).

### The forges are genuinely rejected

The unit tests in `cell/src/escrow_sealed.rs` (all 16 green, `cargo test -p
dregg-cell --lib escrow_sealed::`):

- `honest_two_leg_exchange_completes` — both legs deposited, settles atomically,
  both end `Consumed`, moves `(100, 250)`. **The accept path that makes every
  reject meaningful.**
- `claim_without_own_deposit_is_rejected` — B tries to take A's leg without ever
  depositing its own; `LegNotDeposited(B)`.
- `under_deposited_own_leg_cannot_claim` — an own leg below the required minimum
  does not conform; `NoConformingOwnDeposit` (and the deposit path refuses it up
  front).
- `replay_of_settled_leg_is_rejected` — the SAME claim that accepts before
  settlement is `LegAlreadyConsumed` after (one-shot); settlement cannot replay.
- `reclaim_and_settle_are_mutually_exclusive_one_shot` — reclaim consumes the leg
  so settlement then refuses; double-reclaim refused.
- `over_claim_is_rejected` — an honest claim of exactly the locked `100` accepts;
  a claim of `9999` is `OverClaim { claimed: 9999, locked: 100 }`.
- `wrong_terms_is_rejected`, `settlement_before_both_legs_is_rejected`,
  `wrong_claimant_is_rejected`, `wrong_asset_leg_is_rejected`,
  `redeposit_over_live_leg_is_rejected`, `reclaim_of_anothers_leg_is_rejected`,
  `escrow_state_is_bound_into_commitment`, `non_escrow_cell_is_rejected`,
  `amount_encoding_roundtrips` (incl. `i64::MIN`/`MAX` and negatives).

None are stubs: each rejection is the binding constraint biting, gated against an
honest accept through the same core.

---

## 5. Next slice: circuit binding

The checks in §3–4 are **executor-level** — genuine forge rejections a verifier
runs in the clear. The remaining slice is the **in-circuit witness**, so that a
light client verifying a *batch* sees settlement atomicity and one-shot
consumption enforced by the EffectVM circuit (part of the proven kernel
transition) rather than re-running the check out of band:

1. A `SettleEscrow` effect descriptor whose **gate binds** *"both legs
   `Deposited` ∧ conforming ∧ not-yet-`Consumed` ⟹ both `Consumed`"* into the
   commitment — the same shape as the value/note gates already in
   `circuit/descriptors/`. The gate must bind the atomic both-legs transition
   into the commitment, else the rung is FALSE (the standing circuit-soundness
   apex bar). The deposit/reclaim descriptors bind the per-leg status transition
   the same way (the one-shot nullifier shape the noteSpend grow-gate already
   carries).

2. The two parties' deposited-leg amounts as **heap-opening witnesses** (each leg
   amount/status opened against the escrow cell's `heap_root`, the escrow cell's
   commitment proven in the ledger root).

3. A Lean rung: `verifyBatch accept ⟹ exchange atomic` — concretely, a settled
   batch implies both legs were `Deposited`+conforming before and both `Consumed`
   after, with no leg consumed twice across the batch — joining the
   circuit-soundness obligation table in `docs/reference/lean-circuit.md`.

Until that lands, sealed escrows are sound under the executor checks and the
commitment binding; the circuit rung is the named follow-up, not a silent gap.

**Design + first rung (landed).** The in-circuit weld is now designed and begun,
STAGED and VK-risk-free, in `docs/deos/SETTLE-ESCROW-WELD-DESIGN.md`. Rather than a
new `SettleEscrow` `Effect` with new AIR columns (VK-affecting), the gate is carried
as an off-AIR `SettleEscrow` manifest entry (a new slot/heap caveat tag, re-evaluated
against the bound `state_before`/`state_after` views) — the same vehicle that staged
the temporal caveats (`circuit/src/effect_vm/verify.rs` tags 13–16), so the AIR
constraint polynomials (the VK bytes) are **unchanged**. The first soundness rung is
built and `#assert_axioms`-clean in `metatheory/Dregg2/Deos/SealedEscrow.lean` §6:
`SettleGate` (the transition gate), `settle_gate_forces_atomic` (a satisfying witness
forces both-legs-or-none), `partial_settle_rejected` (the half-open trade is
inexpressible), `phantom_settle_rejected`, and `settle_gate_root_bound` (the
light-client tooth: the gate verdict is fixed by the committed roots, so a forger must
move a root where the §5 status binding bites). The eventual verifier arm inherits this
proof; deploying it is the named **sealed-escrow verifier epoch** (a verifier-code
rollout, not a VK rotation).
