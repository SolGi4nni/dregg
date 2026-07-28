/-
# Dregg2.Deos.DerivedCell — a derived/relational cell's committed value EQUALS `f(sources)` (the
materialized-view house-capacity, grounded BY REUSE of the committed-heap root).

`cell/src/derived.rs` is the Rust house-capacity: a cell whose committed state IS a verifiable
function of OTHER cells' committed states (`Σ balances`, a field-sum, a count, a filter-then-sum) —
a light-client-checkable materialized view. Its soundness is *forge/stale rejection*: a derived
cell is sound iff its committed **claimed value** equals the derivation **evaluated over its
sources**; a forged claim (claim ≠ `f(sources)`) and a stale claim (sources moved, claim did not)
are rejected by the SAME check.

This module is the Lean RUNG for that capacity, in the shape `cae5b2fe` set for the MEMBRANE: add
the invariant leg, prove it **by reuse** of an already-proven commitment (here `Substrate.Heap`'s
sorted-Poseidon2 root), exhibit both-polarity `#guard` witnesses, `#assert_all_clean`, and wire the
Rust to it (`cell/src/derived.rs::tests::invariant_matches_lean_rung`).

## What is proven — and what it REUSES (no derived-cell-local commitment)

The derived cell binds two facts into its committed heap (the SAME `set_heap`/`compute_heap_root`
sorted-Poseidon2 map `cell/src/derived.rs` writes, folded into the canonical state commitment with
NO VK bump): a SPEC DIGEST (which derivation) at `keyDigest`, and the CLAIMED VALUE at `keyValue`.
A verifier holding the cell's committed heap, the spec, and the sources recomputes `f(sources)` and
checks it equals the committed claim. The rung proves:

  * `bind_verifies` (HONEST ROUND-TRIP) — re-deriving (`bind`) writes the freshly-folded value, so a
    verifier with the SAME spec and sources accepts. Read-after-write is `Heap.hget_hset_self`
    (crypto-free); the digest slot survives the value write by `Heap.hget_hset_frame` on the per-instance
    `SlotsDistinct` residual (NO floor).

  * `forged_value_rejected` (THE FORGE TOOTH) — a cell whose committed claim ≠ `f(sources)` does NOT
    verify. The `cell/src/derived.rs` `forged_value_is_rejected` (claim 999 over Σ = 350), as a
    theorem.

  * `stale_rejected` (THE STALE TOOTH) — a cell honestly derived at `oldSrcs`, verified against
    `newSrcs` whose fold differs, is rejected by the SAME value check. The Rust
    `stale_after_source_change_is_rejected`, as the forge tooth instantiated at a moved source.

  * `wrong_spec_rejected` / `wrong_spec_after_bind` — a cell bound under spec A cannot be
    re-interpreted as deriving under a different spec B (distinct digest). The Rust
    `wrong_spec_is_rejected`.

  * **`claim_bound_in_root` (THE REUSE KEYSTONE)** — equal committed roots ⟹ equal committed claim:
    the claimed derived value is bound into the heap root, so a verifier (and a light client) sees
    the SAME claim the cell committed. A DIRECT instance of `Heap.root_binds_get` — the
    `cell/src/derived.rs` `claim_is_bound_into_commitment` test, as a theorem. With it,
    `forged_claim_moves_root` (the anti-ghost): a forged claim CANNOT keep the honest root — it must
    publish a different one, where the value tooth then bites. `spec_bound_in_root` is the twin for
    the spec slot.

This is NOT new mathematics: the fold `f` is an ordinary list aggregate, and the BINDING is the
proven sorted-Poseidon2 root (`Substrate.Heap`, the cap-root machinery generalized to a generic
leaf). The derived cell is a NAMING of "a committed-heap binding whose value slot equals a fold over
sources" — exactly as the membrane is a naming of iterated kernel attenuation.

## The named follow-up (VK-affecting, NOT forced here)

This rung grounds the EXECUTOR-witnessed invariant: a verifier WITH the sources rejects forges and
staleness. Binding the constraint `claim == f(sources)` into the EffectVM circuit — so a light
client verifying a *batch* sees the cross-cell derivation enforced as part of the proven kernel
transition (the sources' commitments as in-circuit membership witnesses) — is the VK-affecting weld
named in `metatheory/docs/HOUSE-CAPACITIES-WELD-PLAN.md` (derived row: "Medium, likely VK-affecting
— new cross-cell `DerivedEquals` constraint in the AIR"), the same lane the cap-root reshape drives.
The value tooth here is the *executor* tooth; the circuit tooth is its shadow.

## Axiom hygiene

`#assert_all_clean` at the close.

## ⚑ NO FLOOR (2026-07-28) — what crypto enters, and what it is worth

Crypto used to enter as the named `Poseidon2SpongeCR` hypothesis, which
`Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed BabyBear: every
theorem under it was VACUOUSLY TRUE where the system stands. It now enters as TWO decidable
per-instance residuals, each with three proved poles (dischargeable / refutable / refutes the floor):

  * `SlotsDistinct hash` (§2.1) — this module's literal slot keys do not alias. A finite kernel check,
    `decide`d at the reference sponge (`slotsDistinct_at_refSponge`). Not a cryptographic assumption
    at all: the deployment fixes the keys, so the honest party can simply evaluate it.
  * `¬ Heap.HeapRootColl hash h₁ h₂` — the deployed sponge does not collide at the ONE pair the root
    extractor hands back for the two heap views in play.

⚑ THE HONEST NUMBER: `Heap.root` is ONE BabyBear felt, so the root residual is worth
`(Q² + 1)/babyBearP ≈ 2^15.5` queries — a BREAK, not a bound. Every keystone here binds exactly as
well as a 31-bit commitment allows. The slot residual costs nothing at all (it is decided, not
assumed).
-/
import Dregg2.Substrate.Heap
import Dregg2.Tactics

namespace Dregg2.Deos.DerivedCell

open Dregg2.Substrate.Heap
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## §1 — the derivation (the fold a derived cell's value MUST equal).

A source cell contributes a (signed) `balance` and one state `field` slot — the two scalars the Rust
`Aggregate` reads (`cell/src/derived.rs`'s `SumBalance` / `SumField`). The aggregate is a
deterministic function of the sources' committed scalars, the SAME function the binder and the
verifier compute — so a forge cannot hide in a discrepancy between them. -/

/-- A source cell's committed scalars the derivation reads: its signed `balance` and one `field`
slot. The Lean image of the bytes a light client sees for a source cell. -/
structure Source where
  /-- The source's signed balance (the `i64` ledger value, `cell/src/derived.rs`'s `SumBalance`). -/
  balance : ℤ
  /-- One state field slot read as an integer (`cell/src/derived.rs`'s `SumField`). -/
  field : ℤ
deriving DecidableEq, Repr

/-- How a derived cell aggregates its sources into a single value — the Lean image of
`cell/src/derived.rs::Aggregate`. Every arm is a deterministic function of the sources' committed
scalars (the bytes a light client sees), so the verifier recomputes it. -/
inductive Aggregate where
  /-- `Σ source.balance` — the materialized-aggregate seed (a treasury = sum of member balances). -/
  | sumBalance
  /-- `Σ source.field` — a relational view over a state field. -/
  | sumField
  /-- `| sources |` — a count view (the cardinality of the relation). -/
  | count
  /-- `Σ { source.balance : threshold ≤ source.balance }` — a filter-then-sum (a join/filter view). -/
  | filteredSumBalance (threshold : ℤ)
deriving DecidableEq, Repr

/-- **`fold agg srcs`** — evaluate the derivation over the sources: the value the derived cell MUST
hold. The single source of truth the binder (writer) and the verifier (checker) BOTH compute. -/
def Aggregate.fold : Aggregate → List Source → ℤ
  | .sumBalance,           srcs => srcs.foldr (fun s acc => s.balance + acc) 0
  | .sumField,             srcs => srcs.foldr (fun s acc => s.field + acc) 0
  | .count,                srcs => (srcs.length : ℤ)
  | .filteredSumBalance t, srcs =>
      srcs.foldr (fun s acc => (if t ≤ s.balance then s.balance else 0) + acc) 0

/-- **`specDigest agg`** — a digest binding WHICH derivation a cell claims (the Lean image of
`DerivationSpec::digest`). Concretely injective on the witnesses below; the rung only needs that a
distinct spec carries a distinct digest, which the `#guard`s exhibit. -/
def specDigest : Aggregate → ℤ
  | .sumBalance           => 100
  | .sumField             => 101
  | .count                => 102
  | .filteredSumBalance t => 1000 + t

/-! ## §2 — a derived cell IS a committed-heap binding (REUSE of `Substrate.Heap`).

The derivation binding lives in a reserved heap collection (`cell/src/derived.rs`'s
`DERIVATION_COLL`), with the spec digest at `keyDigest` and the claimed value at `keyValue` — both
folded into the canonical state commitment by the SAME sorted-Poseidon2 `Heap.root`. We do not add a
commitment: we WRITE into the proven one. -/

/-- The reserved derivation collection (the Lean image of `DERIVATION_COLL = 0x7DE717E`). -/
def derivColl : ℤ := 132052350
/-- Heap key holding the spec digest (`cell/src/derived.rs::KEY_SPEC_DIGEST`). -/
def keyDigest : ℤ := 0
/-- Heap key holding the claimed derived value (`cell/src/derived.rs::KEY_CLAIMED_VALUE`). -/
def keyValue : ℤ := 1

/-- The spec digest bound in a cell's committed heap (`bound_spec_digest`). -/
def boundDigest (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h derivColl keyDigest

/-- The claimed derived value bound in a cell's committed heap (`bound_claimed_value`). -/
def boundValue (hash : List ℤ → ℤ) (h : FeltHeap) : Option ℤ := hget hash h derivColl keyValue

/-- **`bind hash h agg srcs` — RE-DERIVE.** Evaluate the spec over the sources and write the
(spec-digest, claimed-value) binding into the cell's committed heap. The step a turn that updates a
source MUST perform; the Lean image of `cell/src/derived.rs::bind_derivation`. -/
def bind (hash : List ℤ → ℤ) (h : FeltHeap) (agg : Aggregate) (srcs : List Source) : FeltHeap :=
  hset hash (hset hash h derivColl keyDigest (specDigest agg)) derivColl keyValue (agg.fold srcs)

/-- **`Verifies hash h agg srcs`** — the forge detector accepts: the committed spec digest matches
the supplied spec AND the committed claimed value equals the derivation evaluated over the sources.
The Lean image of `cell/src/derived.rs::verify_derivation` returning `Ok`. -/
abbrev Verifies (hash : List ℤ → ℤ) (h : FeltHeap) (agg : Aggregate) (srcs : List Source) : Prop :=
  boundDigest hash h = some (specDigest agg) ∧ boundValue hash h = some (agg.fold srcs)

/-! ### §2.1 — ⚑ THE SLOT-ALIASING RESIDUAL that replaced the refuted floor (2026-07-28).

Every round-trip below used to assume `Poseidon2SpongeCR hash` — global injectivity of a compressing
sponge, which `Circuit.HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE at deployed
BabyBear, so each of them was VACUOUSLY TRUE where the system stands. What the proofs actually NEEDED
was one thing and it is FINITE: the derived cell's TWO literal slot keys must not land on the
same heap address. That is `SlotsDistinct`, and the difference from the floor is not presentational —
it is DECIDABLE at a fixed pair, an honest deployment can CHECK it against the real sponge, and it is
satisfiable where the floor is not. -/

/-- The module's committed heap keys — the literal slot constants the Rust writes. -/
def derivKeys : List ℤ := [keyDigest, keyValue]

/-- **`SlotsDistinct hash`** — the derived cell's committed slots do not ALIAS under `hash`: no two of its
own keys collide the sponge at the pair `Heap.addrFind` hands back. A FINITE, DECIDABLE check over
literal constants — never a global `∀ p q, ¬ Coll`, which pigeonhole refutes exactly like the floor
it would replace. -/
def SlotsDistinct (hash : List ℤ → ℤ) : Prop :=
  ∀ k ∈ derivKeys, ∀ k' ∈ derivKeys, ¬ AddrColl hash derivColl k derivColl k'

instance decidableSlotsDistinct (hash : List ℤ → ℤ) : Decidable (SlotsDistinct hash) := by
  unfold SlotsDistinct; infer_instance

/-- **DISCHARGEABLE — and by COMPUTATION, not by assumption.** At the reference sponge the residual
holds, decided in the kernel. The deployed prover runs the same finite check against the real sponge;
the floor it replaces was unavailable to an honest party at ANY deployed parameters. -/
theorem slotsDistinct_at_refSponge : SlotsDistinct refSponge := by decide

/-- **REFUTABLE.** At the constant sponge every slot aliases, so `SlotsDistinct` is not `True` in
disguise and the residual is doing work. -/
theorem slotsDistinct_refutable : ¬ SlotsDistinct (fun _ => (0 : ℤ)) := by decide

/-- **A REFUTATION, NOT A NEW FLOOR.** A sponge that aliases these slots is not injective, so
`SlotsDistinct` is strictly weaker than the floor it replaces. Stated contrapositively: assumes no
floor content, and the ratchet reads it as the tooth it is. -/
theorem slotsDistinct_failure_refutes_poseidon2CR {hash : List ℤ → ℤ}
    (hf : ¬ SlotsDistinct hash) : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hf (fun _ _ _ _ hc => hc.1 (hCR _ _ hc.2))

/-- **THE FRAME STEP, on the residual.** Writing one slot leaves another slot's opening alone. -/
theorem frameSlot (hash : List ℤ → ℤ) (hd : SlotsDistinct hash) (h : FeltHeap) (k k' v : ℤ)
    (hok : k ∈ derivKeys ∧ k' ∈ derivKeys ∧ k' ≠ k) :
    hget hash (hset hash h derivColl k v) derivColl k' = hget hash h derivColl k' :=
  hget_hset_frame hash h derivColl k derivColl k' v (fun hc => hok.2.2 hc.2)
    (hd k' hok.2.1 k hok.1)

/-! ## §3 — THE HONEST ROUND-TRIP + THE TEETH.

`bind` produces a cell the SAME spec+sources verify (round-trip); a forged claim, a stale claim, and
a wrong spec are each rejected. The forge/stale teeth are crypto-free (the value read-back); the
round-trip's digest leg rides the `SlotsDistinct` residual (frame off the value write; NO floor). -/

/-- **HONEST ROUND-TRIP.** A freshly re-derived cell verifies against the spec+sources it was bound
to. The value slot reads back by `Heap.hget_hset_self` (crypto-free); the digest slot survives the
value write by `Heap.hget_hset_frame` on the `SlotsDistinct` residual (NO floor). -/
theorem bind_verifies (hash : List ℤ → ℤ) (hsd : SlotsDistinct hash)
    (h : FeltHeap) (agg : Aggregate) (srcs : List Source) :
    Verifies hash (bind hash h agg srcs) agg srcs := by
  refine ⟨?_, ?_⟩
  · -- digest slot: frame off the value write (keyValue ≠ keyDigest), then read-after-write.
    show hget hash (hset hash (hset hash h derivColl keyDigest (specDigest agg))
        derivColl keyValue (agg.fold srcs)) derivColl keyDigest = some (specDigest agg)
    rw [frameSlot hash hsd (hset hash h derivColl keyDigest (specDigest agg))
        keyValue keyDigest (agg.fold srcs) (by decide)]
    exact hget_hset_self hash h derivColl keyDigest (specDigest agg)
  · -- value slot: read-after-write (value written last; no crypto).
    exact hget_hset_self hash (hset hash h derivColl keyDigest (specDigest agg))
      derivColl keyValue (agg.fold srcs)

/-- **THE FORGE TOOTH.** A cell whose committed claim ≠ the derivation over the sources does NOT
verify. `cell/src/derived.rs::forged_value_is_rejected` (claim 999 over Σ = 350), as a theorem. -/
theorem forged_value_rejected (hash : List ℤ → ℤ) (h : FeltHeap) (agg : Aggregate)
    (srcs : List Source) (claimed : ℤ)
    (hbound : boundValue hash h = some claimed) (hne : claimed ≠ agg.fold srcs) :
    ¬ Verifies hash h agg srcs := by
  intro hv
  have hval := hv.2
  rw [hbound] at hval
  exact hne (Option.some.inj hval)

/-- **THE STALE TOOTH.** A cell honestly re-derived at `oldSrcs`, verified against `newSrcs` whose
fold differs, is rejected by the SAME value check — staleness IS a forge against the current
sources. `cell/src/derived.rs::stale_after_source_change_is_rejected`, as a theorem. -/
theorem stale_rejected (hash : List ℤ → ℤ) (hsd : SlotsDistinct hash)
    (h : FeltHeap) (agg : Aggregate) (oldSrcs newSrcs : List Source)
    (hne : agg.fold oldSrcs ≠ agg.fold newSrcs) :
    ¬ Verifies hash (bind hash h agg oldSrcs) agg newSrcs :=
  forged_value_rejected hash (bind hash h agg oldSrcs) agg newSrcs (agg.fold oldSrcs)
    (bind_verifies hash hsd h agg oldSrcs).2 hne

/-- **THE WRONG-SPEC TOOTH.** A cell whose committed digest ≠ the supplied spec's digest does not
verify against that spec — you cannot re-interpret a cell as deriving under a relation it never
bound. `cell/src/derived.rs::wrong_spec_is_rejected`, as a theorem. -/
theorem wrong_spec_rejected (hash : List ℤ → ℤ) (h : FeltHeap) (agg' : Aggregate)
    (srcs : List Source) (d : ℤ)
    (hbound : boundDigest hash h = some d) (hne : d ≠ specDigest agg') :
    ¬ Verifies hash h agg' srcs := by
  intro hv
  have hdig := hv.1
  rw [hbound] at hdig
  exact hne (Option.some.inj hdig)

/-- A cell bound under spec `agg` cannot be re-verified under a DIFFERENT spec `agg'` with a distinct
digest. The wrong-spec tooth at a re-derived cell. -/
theorem wrong_spec_after_bind (hash : List ℤ → ℤ) (hsd : SlotsDistinct hash)
    (h : FeltHeap) (agg agg' : Aggregate) (srcs srcs' : List Source)
    (hdig : specDigest agg ≠ specDigest agg') :
    ¬ Verifies hash (bind hash h agg srcs) agg' srcs' :=
  wrong_spec_rejected hash (bind hash h agg srcs) agg' srcs' (specDigest agg)
    (bind_verifies hash hsd h agg srcs).1 hdig

/-! ## §4 — THE REUSE KEYSTONE: the claim is bound into the committed root.

The claimed derived value rides the SAME sorted-Poseidon2 `Heap.root` the cap crown proves binds.
So equal committed roots open to the SAME claim (and the SAME spec) — a verifier and a light client
see EXACTLY the value the cell committed; a forge cannot present the honest root with a lying claim.
A DIRECT instance of `Heap.root_binds_get` (the anti-ghost), on the per-instance `¬ HeapRootColl`
floor. -/

/-- **THE REUSE KEYSTONE — the claimed value is bound into the committed root.** Two heaps with EQUAL
roots open to the SAME claimed value. The `cell/src/derived.rs::claim_is_bound_into_commitment`
test, proven by REUSE of `Heap.root_binds_get` — no derived-cell-local commitment. -/
theorem claim_bound_in_root (hash : List ℤ → ℤ)
    {h₁ h₂ : FeltHeap} (hno : ¬ HeapRootColl hash h₁ h₂) (hroot : root hash h₁ = root hash h₂) :
    boundValue hash h₁ = boundValue hash h₂ :=
  root_binds_get hash hno hroot derivColl keyValue

/-- The spec digest is bound into the committed root too (the twin of `claim_bound_in_root`): a forge
cannot swap WHICH derivation it claims while keeping the honest root. -/
theorem spec_bound_in_root (hash : List ℤ → ℤ)
    {h₁ h₂ : FeltHeap} (hno : ¬ HeapRootColl hash h₁ h₂) (hroot : root hash h₁ = root hash h₂) :
    boundDigest hash h₁ = boundDigest hash h₂ :=
  root_binds_get hash hno hroot derivColl keyDigest

/-- **THE ANTI-GHOST.** A forged cell whose committed claim differs from the honest one CANNOT keep
the honest root — it must publish a different root (where the forge tooth then bites). The
contrapositive of `claim_bound_in_root`: there is no honest way to present a different claim under
the same commitment. -/
theorem forged_claim_moves_root (hash : List ℤ → ℤ)
    {h₁ h₂ : FeltHeap} (hno : ¬ HeapRootColl hash h₁ h₂) (hne : boundValue hash h₁ ≠ boundValue hash h₂) :
    root hash h₁ ≠ root hash h₂ :=
  fun hroot => hne (claim_bound_in_root hash hno hroot)

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the derivation invariant BITES, both polarities.

Computed on the reference sponge (`Substrate.Heap.refSponge`) so a forged/stale claim provably fails
verification AND moves the root — the executable shadow of §3/§4. -/

section Witnesses

/-- Three source cells with balances 100, 250, 50 (and fields 7, 8, 9). -/
private def s1 : Source := ⟨100, 7⟩
private def s2 : Source := ⟨250, 8⟩
private def s3 : Source := ⟨50, 9⟩
private def srcs : List Source := [s1, s2, s3]

-- The fold computes the materialized aggregate (Σ balances = 400; count = 3; Σ fields = 24).
#guard Aggregate.fold .sumBalance srcs == 400
#guard Aggregate.fold .count srcs == 3
#guard Aggregate.fold .sumField srcs == 24
-- Filter-then-sum at threshold 60 keeps 100 and 250 (50 darkened) = 350.
#guard Aggregate.fold (.filteredSumBalance 60) srcs == 350

/-- An honestly re-derived sum-cell (over the empty heap). -/
private def honest : FeltHeap := bind refSponge [] .sumBalance srcs

-- HONEST: the cell binds the fold and its spec, and verifies.
#guard boundValue refSponge honest == some 400
#guard boundDigest refSponge honest == some (specDigest .sumBalance)
#guard decide (Verifies refSponge honest .sumBalance srcs)

-- THE FORGE: overwrite the value slot with a lying 999. It no longer verifies (the forge tooth),
-- and — critically — the forged claim MOVED the committed root (the anti-ghost; it cannot hide
-- under the honest root).
private def forged : FeltHeap := hset refSponge honest derivColl keyValue 999
#guard boundValue refSponge forged == some 999
#guard !decide (Verifies refSponge forged .sumBalance srcs)
#guard (root refSponge forged != root refSponge honest)

-- THE STALE REJECTION: derive at the old sources, then a source moves (s1: 100 → 600, Σ = 900). The
-- old cell, verified against the NEW sources, is rejected by the same value check.
private def newSrcs : List Source := [⟨600, 7⟩, s2, s3]
#guard Aggregate.fold .sumBalance newSrcs == 900
#guard !decide (Verifies refSponge honest .sumBalance newSrcs)
-- Re-deriving against the new sources restores acceptance AND moves the root (a light client sees
-- the update).
#guard decide (Verifies refSponge (bind refSponge honest .sumBalance newSrcs) .sumBalance newSrcs)
#guard (root refSponge (bind refSponge honest .sumBalance newSrcs) != root refSponge honest)

-- THE WRONG-SPEC REJECTION: the sum-cell, re-interpreted as a count-cell, is rejected at the digest
-- (distinct spec digests).
#guard specDigest .sumBalance != specDigest .count
#guard !decide (Verifies refSponge honest .count srcs)

-- A FILTERED-SUM view derives and verifies; a forged filtered value is rejected.
private def filtered : FeltHeap := bind refSponge [] (.filteredSumBalance 60) srcs
#guard boundValue refSponge filtered == some 350
#guard decide (Verifies refSponge filtered (.filteredSumBalance 60) srcs)
#guard !decide (Verifies refSponge (hset refSponge filtered derivColl keyValue 400)
        (.filteredSumBalance 60) srcs)

end Witnesses

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [
  slotsDistinct_at_refSponge,
  slotsDistinct_refutable,
  slotsDistinct_failure_refutes_poseidon2CR,
  frameSlot,
  bind_verifies,
  forged_value_rejected,
  stale_rejected,
  wrong_spec_rejected,
  wrong_spec_after_bind,
  claim_bound_in_root,
  spec_bound_in_root,
  forged_claim_moves_root
]

end Dregg2.Deos.DerivedCell
