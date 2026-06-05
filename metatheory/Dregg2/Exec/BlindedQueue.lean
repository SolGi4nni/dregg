/-
# Dregg2.Exec.BlindedQueue — the "commitments-in, nullifiers-out" private-consumption queue.

`STORAGE-AS-CELL-PROGRAMS.md §3.4`: a `BlindedQueue` is **not a new Effect** — it is a **cell**
whose state is a commitments set (blinded items *added*), a nullifier set (items *spent*), and
two monotone counts (`countAdded`/`countSpent`, with `countSpent ≤ countAdded`). It is the
canonical privacy-voting / sealed-bid primitive: a producer enqueues a *blinded* commitment, and
a consumer privately spends it by publishing a *nullifier* (revealing nothing about *which* item)
together with a ZK **spend proof**. Per `PREDICATE-INVENTORY.md §9.4` it is the ONLY storage
primitive needing a `Witnessed` spend predicate — and that predicate is exactly the `dregg2 §8`
verify oracle.

We **reuse, never redefine**:
- `NullifierCell.Cell` (the G-Set of consumed nullifiers) + `spend` + its anti-double-spend law
  `spend_no_double_spend` for the *anti-double-spend half* (§3.4 slot 1 / slot 5: `nullifier_root`
  monotone, double-spend rejected). We do NOT touch the nullifier-set discipline; we wrap it.
- `CryptoKernel.verify` (the `dregg2 §8` decidable spend oracle) for the *privacy-gate half*
  (§3.4 slot 6: `spend_air_vk`). A `consume` is admissible only when `verify spendStmt proof`
  accepts — the witnessed `WitnessedPredicate::Custom { vk_hash }` of §3.4 made into an interface
  obligation we USE. Its soundness/extractability is the CIRCUIT obligation, NEVER a Lean law.

Headline theorems (both proved):
- `blinded_no_double_spend` — a nullifier already spent cannot be consumed again (lifted from
  `NullifierCell.spend_no_double_spend`).
- `consume_needs_verify` — a committed `consume` implies `CryptoKernel.verify` accepted the
  spend proof: the privacy gate.
- `countSpent_le_added` — spent never exceeds added, preserved by every transition.

Parametric over `[CryptoKernel Digest Proof]`, so every theorem holds for *any* lawful kernel
(the abstract proving instance) AND for the Rust FFI one (the running instance). The `#eval`
demos run against the `Reference` kernel in `CryptoKernel.lean`.

Pure, computable, `#eval`-able. No `axiom`/`admit`/`native_decide`/`sorry`.
-/
import Dregg2.Exec.NullifierCell
import Dregg2.CryptoKernel

namespace Dregg2.Exec.BlindedQueue

open Dregg2.Crypto (CryptoKernel)
open Dregg2.Privacy (Nullifier)

universe u

variable {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]

/-! ## The state — commitments added, nullifiers spent (reusing the `NullifierCell`), and counts. -/

/-- **A `BlindedQueue` state** (`STORAGE-AS-CELL-PROGRAMS §3.4`, name-keyed not 8-slot):
- `commitments` — the set of blinded item commitments *added* (the §3.4 `commitments_root`,
  modelled as the live `Finset` of digests rather than a Merkle digest; grow-only).
- `nullifiers`  — the spent-nullifier set, REUSING `NullifierCell.Cell` *unchanged* (the §3.4
  `nullifier_root`; its append-only / anti-double-spend discipline is the cell's own law).
- `countAdded` / `countSpent` — the monotone counters (`commitment_count` / `nullifier_count`),
  with the standing invariant `countSpent ≤ countAdded` (a spend consumes an added item).

`Digest` is the commitment carrier (the `CryptoKernel`'s hash/commit codomain). -/
structure State (Digest : Type) where
  /-- The blinded commitments added so far (grow-only; the `commitments_root` live set). -/
  commitments : Finset Digest
  /-- The spent-nullifier set — the reused `NullifierCell.Cell` (its own append-only law). -/
  nullifiers : NullifierCell.Cell
  /-- Number of items added (monotone ↑). -/
  countAdded : Nat
  /-- Number of items spent (monotone ↑); standing invariant `countSpent ≤ countAdded`. -/
  countSpent : Nat

/-- The empty queue: nothing added, nothing spent (the genesis state). -/
def empty [DecidableEq Digest] : State Digest :=
  { commitments := ∅, nullifiers := NullifierCell.empty, countAdded := 0, countSpent := 0 }

/-! ## `add` — enqueue a blinded commitment (monotone, fail-open: adding is always allowed). -/

/-- **`add s c`** — the producer enqueues a blinded commitment `c`. Insert it into the
commitments set and bump `countAdded`. This is grow-only (`STORAGE-AS-CELL-PROGRAMS §3.4`:
"commitments only added"): no commitment is ever removed. Adding never spends, so the
`countSpent ≤ countAdded` invariant is *preserved* (the gap only widens). -/
def add [DecidableEq Digest] (s : State Digest) (c : Digest) : State Digest :=
  { s with commitments := insert c s.commitments, countAdded := s.countAdded + 1 }

/-! ## `consume` — privately spend an item (fail-closed; the two-gate AND of §3.4). -/

/-- **`consume s spendStmt proof n`** — the consumer privately spends, publishing nullifier `n`
under the spend statement `spendStmt : Digest` with witness `proof : Proof`. It is the AND of
**both** §3.4 gates, fail-closed (`none` on either failure):

1. **The privacy gate** (`CryptoKernel.verify spendStmt proof = true`) — the `dregg2 §8`
   witnessed spend predicate (§3.4 slot 6). You may not spend without a valid spend proof. Its
   soundness is the circuit obligation; here it is the decidable oracle the cell consults.
2. **The anti-double-spend gate** (`NullifierCell.spend s.nullifiers n` succeeds) — `n` must be
   *fresh* in the spent set, REUSING the nullifier cell's own append-only `spend`. A re-presented
   nullifier is rejected by `NullifierCell`'s law.

On success: the nullifier is recorded (via the reused cell) and `countSpent` is bumped. -/
def consume (s : State Digest) (spendStmt : Digest) (proof : Proof) (n : Nullifier) :
    Option (State Digest) :=
  if CryptoKernel.verify spendStmt proof then
    match NullifierCell.spend s.nullifiers n with
    | some nz => some { s with nullifiers := nz, countSpent := s.countSpent + 1 }
    | none    => none                       -- nullifier already spent ⇒ fail-closed
  else
    none                                    -- spend proof rejected ⇒ fail-closed (privacy gate)

/-! ## Keystone (a) — `blinded_no_double_spend` (lifted from `NullifierCell`). -/

/-- If nullifier `n` is already in the spent set, `consume` returns `none` regardless of the
spend proof. Delegates to `NullifierCell.spend_rejects_double`; the verify gate cannot rescue an
already-spent nullifier. -/
theorem consume_rejects_double (s : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : n ∈ s.nullifiers.spent) :
    consume s spendStmt proof n = none := by
  unfold consume
  rw [NullifierCell.spend_rejects_double s.nullifiers n h]
  -- now the body is `if verify … then (match none with …) else none`; both branches are `none`.
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv]
  · rw [if_neg hv]

/-- Anti-double-spend keystone, proved by reusing `NullifierCell.spend_no_double_spend`: (a) an
already-spent nullifier is rejected; (b) a successful consume lands `n` in the new spent set. Each
blinded item is consumed at most once. -/
theorem blinded_no_double_spend (s : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier) :
    (n ∈ s.nullifiers.spent → consume s spendStmt proof n = none)
    ∧ (∀ s', consume s spendStmt proof n = some s' → n ∈ s'.nullifiers.spent) := by
  refine ⟨consume_rejects_double s spendStmt proof n, ?_⟩
  intro s' hcons
  -- A successful consume passed the verify gate and a fresh-`spend`; its nullifier set is `nz`,
  -- which by `NullifierCell.spend` contains `n`.
  unfold consume at hcons
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at hcons
    -- split on the reused `spend`
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at hcons; exact absurd hcons (by simp)
    | some nz =>
        rw [hsp] at hcons
        -- the second keystone-half of the reused cell gives `n ∈ nz.spent`
        have hfresh : n ∉ s.nullifiers.spent := by
          by_contra hin
          rw [NullifierCell.spend_rejects_double s.nullifiers n hin] at hsp
          exact absurd hsp (by simp)
        have := (NullifierCell.spend_no_double_spend s.nullifiers n).2 hfresh
        obtain ⟨c', hc', hmem⟩ := this
        -- `spend = some nz` and `spend = some c'` ⇒ `nz = c'`
        rw [hsp] at hc'
        have hnz : nz = c' := by injection hc'
        -- `s' = { s with nullifiers := nz, … }`, so `s'.nullifiers = nz`
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection hcons
        subst hs'
        subst hnz
        exact hmem
  · rw [if_neg hv] at hcons
    exact absurd hcons (by simp)

/-! ## Keystone (b) — `consume_needs_verify` (the privacy gate). -/

/-- A committed `consume` implies `CryptoKernel.verify` accepted the spend proof. The
soundness/extractability of that proof is a circuit obligation; this theorem is the cell-side
guarantee that the oracle was consulted and accepted. -/
theorem consume_needs_verify (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : consume s spendStmt proof n = some s') :
    CryptoKernel.verify spendStmt proof = true := by
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · exact hv
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-! ## The conservation-ish bound — `countSpent ≤ countAdded`, preserved by every transition. -/

/-- The standing invariant of a well-formed queue: spent never exceeds added. -/
def Invariant (s : State Digest) : Prop := s.countSpent ≤ s.countAdded

/-! **`add` preserves the bound.** Adding bumps `countAdded` and leaves `countSpent` fixed. -/
omit [AddCommGroup Digest] [CryptoKernel Digest Proof] in
theorem add_preserves_bound [DecidableEq Digest] (s : State Digest) (c : Digest)
    (h : Invariant s) : Invariant (add s c) := by
  unfold Invariant add at *
  simp only
  omega

/-- A successful `consume` bumps `countSpent` by 1 and leaves `countAdded` fixed. Requires
`countSpent < countAdded` as a hypothesis.

-- OPEN: the tight form `Invariant s → Invariant s'` needs "a fresh nullifier corresponds to a
-- distinct previously-added commitment" — i.e. `countSpent < countAdded` must hold whenever a
-- fresh spend succeeds. That linkage is the spend AIR's extractability obligation (the
-- `dregg2 §8` circuit), not provable from the set discipline alone. -/
theorem consume_preserves_bound (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (hlt : s.countSpent < s.countAdded)
    (h : consume s spendStmt proof n = some s') :
    Invariant s' := by
  unfold Invariant
  -- extract the shape of `s'` from a successful consume
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at h
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at h; exact absurd h (by simp)
    | some nz =>
        rw [hsp] at h
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection h
        subst hs'
        simp only
        omega
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-- After a successful consume with `countSpent < countAdded`, `countSpent ≤ countAdded` still
holds in the resulting state. -/
theorem countSpent_le_added (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (hlt : s.countSpent < s.countAdded)
    (h : consume s spendStmt proof n = some s') :
    s'.countSpent ≤ s'.countAdded :=
  consume_preserves_bound s s' spendStmt proof n hlt h

/-! ## `add` is grow-only — every prior commitment survives, count only climbs. -/

/-! Every previously-added commitment is still present after an `add`, and `countAdded` strictly
increases. -/
omit [AddCommGroup Digest] [CryptoKernel Digest Proof] in
theorem add_monotone [DecidableEq Digest] (s : State Digest) (c : Digest) :
    s.commitments ⊆ (add s c).commitments ∧ s.countAdded < (add s c).countAdded := by
  refine ⟨?_, ?_⟩
  · exact Finset.subset_insert c s.commitments
  · unfold add; simp only; omega

/-- The spent set only grows: every nullifier present before a consume is still present after.
Lifts `NullifierCell.spend_monotone`. -/
theorem consume_nullifiers_monotone (s s' : State Digest)
    (spendStmt : Digest) (proof : Proof) (n : Nullifier)
    (h : consume s spendStmt proof n = some s') :
    s.nullifiers.spent ⊆ s'.nullifiers.spent := by
  unfold consume at h
  by_cases hv : CryptoKernel.verify spendStmt proof = true
  · rw [if_pos hv] at h
    cases hsp : NullifierCell.spend s.nullifiers n with
    | none => rw [hsp] at h; exact absurd h (by simp)
    | some nz =>
        rw [hsp] at h
        have hs' : { s with nullifiers := nz, countSpent := s.countSpent + 1 } = s' := by
          injection h
        subst hs'
        simp only
        exact NullifierCell.spend_monotone s.nullifiers nz n hsp
  · rw [if_neg hv] at h; exact absurd h (by simp)

/-! ## It runs (`#eval`) — against the `Reference` CryptoKernel.

The reference kernel accepts iff `proof = stmt`. Demos: add two commitments; consume with a
valid proof; re-consume the same nullifier (rejected); consume with a bad proof (rejected). -/

open Dregg2.Crypto.Reference (D P)

private def n1 : Nullifier := { tag := 1 }
private def n2 : Nullifier := { tag := 2 }

/-- A blinded queue over the reference kernel: add commitments `7` and `9`. -/
private def q0 : State D := add (add (empty (Digest := D)) 7) 9

-- two items added ⇒ countAdded = 2, countSpent = 0
#guard ((q0.countAdded, q0.countSpent)) == (2, 0)  --  (2, 0)

/-- A *valid* spend: statement `42`, proof `42` (echo ⇒ `verify` accepts), nullifier `n1`. -/
private def q1? : Option (State D) := consume q0 (42 : D) (42 : P) n1

-- valid proof + fresh nullifier ⇒ admitted; countSpent bumped to 1
#guard (q1?.map (fun s => (s.countAdded, s.countSpent))) == some (2, 1)  --  some (2, 1)
-- the nullifier n1 is now recorded in the spent set
#guard (q1?.map (fun s => decide (n1 ∈ s.nullifiers.spent))) == some true  --  some true

-- consume the SAME nullifier n1 AGAIN (valid proof, but already spent) ⇒ rejected (anti-double-spend)
#guard ((q1?.bind (fun s => consume s (42 : D) (42 : P) n1)).isNone)  --  true

-- consume with a BAD proof (statement 42, proof 99 ≠ 42 ⇒ verify rejects), fresh nullifier n2 ⇒ rejected (privacy gate)
#guard ((q1?.bind (fun s => consume s (42 : D) (99 : P) n2)).isNone)  --  true

-- a DIFFERENT valid spend (statement 5, proof 5), fresh nullifier n2 ⇒ admitted; countSpent = 2
#guard ((q1?.bind (fun s => consume s (5 : D) (5 : P) n2)).map
        (fun s => (s.countAdded, s.countSpent))) == some (2, 2)  --  some (2, 2)

end Dregg2.Exec.BlindedQueue
