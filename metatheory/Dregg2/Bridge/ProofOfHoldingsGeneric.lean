/-
# Metatheory.Bridge.ProofOfHoldingsGeneric — a CHAIN-AGNOSTIC, fold-compatible
non-custodial proof-of-holdings ⟹ weight soundness model.

This is the generalization of `Dregg2.Bridge.ProofOfHoldings` (the SOLANA model) to
"a foldable holding proof on ANY chain". The Solana file proves, over concrete SPL
token accounts, that a granted governance weight is BACKED by a consensus-proven
holding at a finalized slot AND leaves chain state definitionally unchanged
(non-custodial). Here we abstract the chain away.

## The abstraction (`ChainParams`)
A `ChainParams` packages the per-chain data the soundness argument needs:
  * the chain's `Height`/`State`/`Addr`/`Asset`/`Proof` carrier types,
  * `Finalized : Height → State → Prop` — the weak-subjectivity-anchored finality
    ORACLE. It stays an ASSUMED oracle: a STRUCTURE FIELD, never a global `axiom`
    and never a laundered `def FooHard`. (Per no-named-carrier-laundering: a chain's
    finality is data supplied to the model, not a proof obligation we fake.)
  * `Holds : Proof → Addr → Asset → ℕ → Height → Prop` — the holding-proof relation
    "this proof certifies that `addr` held `amount` of `asset` at `height`".

The two-tier trust dial (`GTier`: consensusVerified vs structureOnly) is shared across
chains (it is a property of HOW an observation was obtained, not of the chain).

## Generic theorems (mirror the Solana ones, over `ChainParams`)
  * `weight_backed_and_noncustodial_generic` — a granted weight is backed by a
    `consensusVerified` `Holds` at a `Finalized` height, and the grant is a pure read
    (state unchanged).
  * `gate_discriminates_generic` — a `structureOnly` proof grants nothing; overweight
    is ungrantable. Both discriminator axes, abstractly.
  * `granted_weight_le_amount_generic` + `grant_output_snapshot_pinned` — the
    anti-double-count / snapshot-pinning invariant: a single snapshot yields AT MOST
    its own proven balance, attributed to EXACTLY its own owner.

## Fold-compatibility
The grant's weight is a DETERMINISTIC function of the proof + finality verdict with NO
chain-state dependence (`grant_weight_independent_of_state`), so a recursive/folding
light client can carry it as a pure per-step contribution. `foldWeights` sums those
contributions and `foldWeights_append` is the homomorphism a fold exploits: total
weight over a concatenation = sum of the parts (verify segments independently, add).

## Non-vacuity (the abstraction is REAL, not `True`-shaped)
`solanaChain`/`solanaHolding` instantiate `ChainParams` at the existing Solana model and
`solana_specializes` proves `grantsWeightG` on that instance is EXACTLY the proven Solana
`grantsWeight`. `toyChain` is a SECOND, genuinely different chain (state-dependent
finality `h ≤ st`, a non-trivial `Holds proof amount := proof = amount`). The generic
theorems FIRE on both; `toy_bad_proof_teeth` shows the toy chain's `Holds` relation has
teeth the Solana `True`-instance never could — so the generalization adds real content.

Kernel-clean: `#assert_axioms` hard-gates every generic theorem and every instance.
-/
import Dregg2.Tactics
import Dregg2.Bridge.ProofOfHoldings

namespace Dregg2.Bridge.ProofOfHoldingsGeneric

open Dregg2.Bridge.ProofOfHoldings

/-! ## §1 — The shared trust dial and the generic chain. -/

/-- **`GTier`** — the chain-agnostic trust dial. `consensusVerified` is a trustless
observation (a real supermajority over a finalized head); `structureOnly` is a
plain-read echo that MUST NOT grant weight. Shared across chains because it describes
how an observation was OBTAINED, not the chain itself. -/
inductive GTier
  | consensusVerified
  | structureOnly
deriving DecidableEq, Repr

/-- The executable projection of the tier: `true` only for `consensusVerified`. -/
def GTier.isConsensusVerified : GTier → Bool
  | .consensusVerified => true
  | .structureOnly     => false

/-- **`ChainParams`** — the per-chain data the proof-of-holdings argument abstracts over.
`Finalized` and `Holds` are ASSUMED relations supplied as fields (the finality oracle and
the holding-proof certifier), never global axioms. Solana is ONE instance (`solanaChain`);
`toyChain` is a second. -/
structure ChainParams where
  /-- The chain's block-height / slot carrier. -/
  Height : Type
  /-- The chain's ledger-state carrier (Solana ignores it; the toy chain uses it). -/
  State  : Type
  /-- The account / address carrier. -/
  Addr   : Type
  /-- The asset / token-mint carrier. -/
  Asset  : Type
  /-- The holding-proof carrier (a light-client proof object; Solana uses `Unit`). -/
  Proof  : Type
  /-- The weak-subjectivity-anchored finality ORACLE: is `height` final in `state`?
  Assumed data, NOT an axiom. -/
  Finalized : Height → State → Prop
  /-- The holding-proof relation: this `proof` certifies `addr` held `amount` of `asset`
  at `height`. Assumed data, NOT an axiom. -/
  Holds : Proof → Addr → Asset → Nat → Height → Prop

/-- **`GHolding C`** — a proven holding on chain `C`: the certifying proof, the owner
(its own custody — no vault), the asset, the proven amount, the snapshot height, and the
trust tier. -/
structure GHolding (C : ChainParams) where
  /-- The light-client proof certifying the holding. -/
  proof  : C.Proof
  /-- The owner whose OWN account the holding is proven over (non-custodial). -/
  owner  : C.Addr
  /-- The asset proven held. -/
  asset  : C.Asset
  /-- The balance proven at `height`, in atomic units. -/
  amount : Nat
  /-- The finalized height the holding is pinned to (the snapshot point). -/
  height : C.Height
  /-- Trust tier; weight is granted ONLY for `consensusVerified`. -/
  tier   : GTier

/-! ## §2 — The generic weight-grant predicate and the executable, non-custodial grant. -/

/-- **`grantsWeightG C st g v w`** — the fail-closed generic weight-grant predicate. A
holding `g` grants weight `w` to identity `v` (in ledger state `st`) iff its tier is
`consensusVerified`, its height is `Finalized` in `st`, its proof genuinely `Holds` the
claimed amount, the owner is `v`, and `w` never exceeds the proven amount. Weight is a
pure function of a consensus proof — no custody surrendered, no committee verdict. -/
def grantsWeightG (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat) : Prop :=
  g.tier = GTier.consensusVerified
    ∧ C.Finalized g.height st
    ∧ C.Holds g.proof g.owner g.asset g.amount g.height
    ∧ g.owner = v
    ∧ w ≤ g.amount

/-- **`grantWeightG C g fv pre`** — the deployed non-custodial grant. It reads the holding
`g` and the light client's decidable finality verdict `fv` and returns `(the weight
assignment, the ledger state)`. The state component is `pre` UNCHANGED — the grant is a
pure read of the proof and moves no custody. The gate `isConsensusVerified && fv` enforces
BOTH the proof tier and finalization in the executable itself, not only in the `Prop`. -/
def grantWeightG (C : ChainParams) (g : GHolding C) (fv : Bool) (pre : C.State) :
    Option (C.Addr × Nat) × C.State :=
  (if g.tier.isConsensusVerified && fv then some (g.owner, g.amount) else none, pre)

/-! ## §3 — THE GENERIC TOP THEOREMS — backed, non-custodial, discriminating. -/

/-- **`weight_backed_and_noncustodial_generic`** — the guarantee, over ANY chain. If `w`
is granted to `v` in state `st`, then (BACKING) there is a `consensusVerified`, `Finalized`
proof that `Holds` a balance `≥ w` owned by `v`, AND (NON-CUSTODIAL) the grant leaves the
ledger state definitionally unchanged for every prior state and finality verdict. -/
theorem weight_backed_and_noncustodial_generic
    (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat)
    (hg : grantsWeightG C st g v w) (fv : Bool) (pre : C.State) :
    (g.tier = GTier.consensusVerified
      ∧ C.Finalized g.height st
      ∧ C.Holds g.proof g.owner g.asset g.amount g.height
      ∧ w ≤ g.amount
      ∧ g.owner = v)
    ∧ (grantWeightG C g fv pre).2 = pre := by
  obtain ⟨ht, hf, hh, ho, hle⟩ := hg
  exact ⟨⟨ht, hf, hh, hle, ho⟩, rfl⟩

/-- The backing projection alone: any granted weight is backed by a `consensusVerified`,
`Finalized`, genuinely-`Holds`ing proof of at least that weight. -/
theorem granted_weight_is_backed_generic
    (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat)
    (hg : grantsWeightG C st g v w) :
    g.tier = GTier.consensusVerified
      ∧ C.Finalized g.height st
      ∧ C.Holds g.proof g.owner g.asset g.amount g.height
      ∧ w ≤ g.amount :=
  ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.2⟩

/-- The non-custodial projection alone: the grant NEVER mutates the ledger state, for ANY
holding, ANY verdict, ANY prior state (proven or structureOnly — always a pure read). -/
theorem grant_preserves_custody_generic
    (C : ChainParams) (g : GHolding C) (fv : Bool) (pre : C.State) :
    (grantWeightG C g fv pre).2 = pre := rfl

/-- **TIER DISCRIMINATOR (fail-closed), generic.** A `structureOnly` holding grants no
weight, in any state, to any identity, for any weight. -/
theorem structureOnly_grants_nothing_generic
    (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat)
    (hso : g.tier = GTier.structureOnly) : ¬ grantsWeightG C st g v w := by
  rintro ⟨ht, _, _, _, _⟩
  rw [hso] at ht
  exact absurd ht (by decide)

/-- **AMOUNT DISCRIMINATOR, generic.** A weight strictly above the proven amount is never
grantable, even from a consensus-proven, finalized holding. -/
theorem overweight_not_grantable_generic
    (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat)
    (hover : g.amount < w) : ¬ grantsWeightG C st g v w := by
  rintro ⟨_, _, _, _, hle⟩
  omega

/-- **`gate_discriminates_generic`** (the `gate_discriminates_both_axes` analog, over ANY
chain): SAME state, SAME identity — a consensus-proven holding grants `w`, but its
`structureOnly` variant grants NOTHING, and any weight `wOver > amount` is ungrantable.
The gate turns on BOTH the trust tier AND the amount bound. -/
theorem gate_discriminates_generic
    (C : ChainParams) (st : C.State)
    (gGood gRpc : GHolding C) (v : C.Addr) (w wOver : Nat)
    (hgood : grantsWeightG C st gGood v w)
    (hrpc : gRpc.tier = GTier.structureOnly)
    (hover : gGood.amount < wOver) :
    grantsWeightG C st gGood v w
    ∧ ¬ grantsWeightG C st gRpc v w
    ∧ ¬ grantsWeightG C st gGood v wOver :=
  ⟨hgood,
   structureOnly_grants_nothing_generic C st gRpc v w hrpc,
   overweight_not_grantable_generic C st gGood v wOver hover⟩

/-! ## §4 — ANTI-DOUBLE-COUNT / SNAPSHOT-PINNING (abstract). -/

/-- **Snapshot bound.** Any granted weight is `≤` the single proven balance at the pinned
snapshot — one snapshot can never be counted for more than its own amount. -/
theorem granted_weight_le_amount_generic
    (C : ChainParams) (st : C.State) (g : GHolding C) (v : C.Addr) (w : Nat)
    (hg : grantsWeightG C st g v w) : w ≤ g.amount :=
  hg.2.2.2.2

/-- **Snapshot pinning.** Whenever the deployed grant emits a weight assignment, it is
EXACTLY `(owner, amount)` at the pinned snapshot — the credited identity is the proven
owner and the credited weight is the single proven balance (never a sum, never
misattributed). An accumulator keyed by `(owner, asset, height)` therefore cannot receive
an inflated or misattributed grant from a single snapshot: the anti-double-count core. -/
theorem grant_output_snapshot_pinned
    (C : ChainParams) (g : GHolding C) (fv : Bool) (pre : C.State) (v : C.Addr) (w : Nat)
    (h : (grantWeightG C g fv pre).1 = some (v, w)) :
    v = g.owner ∧ w = g.amount := by
  have h' : (if g.tier.isConsensusVerified && fv then some (g.owner, g.amount) else none)
      = some (v, w) := h
  by_cases hc : (g.tier.isConsensusVerified && fv) = true
  · rw [if_pos hc] at h'
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    exact ⟨h'.1.symm, h'.2.symm⟩
  · simp only [Bool.not_eq_true] at hc
    rw [if_neg (by simp [hc])] at h'
    exact absurd h' (by simp)

/-! ## §5 — FOLD-COMPATIBILITY — the grant is a pure, state-free, foldable contribution.

The fold requirement a recursive light client needs: the per-holding weight must be a
DETERMINISTIC function of (proof, finality verdict) with NO hidden chain state, and the
total over a set of holdings must be a HOMOMORPHISM over concatenation (so segments fold
independently and combine by `+`). Both hold below. -/

/-- **NO HIDDEN STATE (the fold precondition).** The weight assignment the grant emits is
INDEPENDENT of the prior ledger state — `grantWeightG` reads only the proof + finality
verdict. This is exactly what a folding verifier needs: the grant is `f(proof, finality)`
with no state to thread through the recursion. -/
theorem grant_weight_independent_of_state
    (C : ChainParams) (g : GHolding C) (fv : Bool) (pre pre' : C.State) :
    (grantWeightG C g fv pre).1 = (grantWeightG C g fv pre').1 := rfl

/-- The state-free per-step contribution a folding verifier carries: `amount` when the
holding is consensus-proven and its height is (verdict-)final, else `0`. -/
def grantWeightCoreG (isCV finalVerdict : Bool) (amount : Nat) : Nat :=
  if isCV && finalVerdict then amount else 0

/-- **`foldContribution C g fv`** — the fold's per-holding weight, as a pure function of
the holding's tier, the finality verdict, and the proven amount. No chain state. -/
def foldContribution (C : ChainParams) (g : GHolding C) (fv : Bool) : Nat :=
  grantWeightCoreG g.tier.isConsensusVerified fv g.amount

/-- **FOLD-SOUNDNESS BRIDGE.** The state-free `foldContribution` equals the weight the
deployed non-custodial `grantWeightG` actually emits — so the number a folding verifier
sums per step is EXACTLY the deployed grant's weight, for any prior state. -/
theorem foldContribution_eq_grant_weight
    (C : ChainParams) (g : GHolding C) (fv : Bool) (pre : C.State) :
    foldContribution C g fv =
      (match (grantWeightG C g fv pre).1 with
       | some p => p.2
       | none   => 0) := by
  cases hcv : g.tier.isConsensusVerified <;> cases fv <;>
    simp [foldContribution, grantWeightCoreG, grantWeightG, hcv]

/-- **`foldWeights C gs`** — a folding light client's aggregate: the sum of the per-holding
contributions over a list of `(holding, finality-verdict)` steps. -/
def foldWeights (C : ChainParams) (gs : List (GHolding C × Bool)) : Nat :=
  (gs.map (fun gfv => foldContribution C gfv.1 gfv.2)).sum

/-- **FOLD HOMOMORPHISM (the recursion the fold exploits).** Aggregate weight over a
concatenation is the sum of the aggregates of the parts — so a recursive verifier folds
two segments independently and combines them by `+`. This, with `grant_weight_independent_
of_state`, is the clean "foldable holding proof" shape. -/
theorem foldWeights_append
    (C : ChainParams) (l1 l2 : List (GHolding C × Bool)) :
    foldWeights C (l1 ++ l2) = foldWeights C l1 + foldWeights C l2 := by
  unfold foldWeights
  rw [List.map_append, List.sum_append]

/-! ## §6 — NON-VACUITY INSTANCE (a): the existing SOLANA model. -/

/-- Map the Solana `TrustTier` into the shared `GTier`. -/
def GTier.ofTrustTier : TrustTier → GTier
  | .consensusProven => .consensusVerified
  | .rpc             => .structureOnly

theorem ofTrustTier_cv (t : TrustTier) :
    GTier.ofTrustTier t = GTier.consensusVerified ↔ t = TrustTier.consensusProven := by
  cases t <;> simp [GTier.ofTrustTier]

/-- **The Solana instance of `ChainParams`.** `State = Unit` (Solana finality ignores
ledger state — it is a slot-only oracle), `Proof = Unit` (the `ProvenHolding` snapshot IS
the proof, so `Holds ≡ True`), `Finalized` lifts the assumed `HoldingsProof.finalized`
oracle. Solana is thus ONE point of the abstraction. (`@[reducible]` so the carrier-type
projections `(solanaChain o).Addr` etc. unfold during `OfNat` numeral synthesis.) -/
@[reducible] def solanaChain (o : HoldingsProof) : ChainParams where
  Height := Slot
  State  := Unit
  Addr   := Account
  Asset  := Nat
  Proof  := Unit
  Finalized := fun s _ => o.finalized s
  Holds := fun _ _ _ _ _ => True

/-- A Solana `ProvenHolding` as a generic `GHolding` on `solanaChain o`. -/
def solanaHolding (o : HoldingsProof) (h : ProvenHolding) : GHolding (solanaChain o) where
  proof  := ()
  owner  := h.owner
  asset  := h.mint
  amount := h.amount
  height := h.slot
  tier   := GTier.ofTrustTier h.trust

/-- **THE SPECIALIZATION (non-vacuity anchor).** The generic `grantsWeightG` on the Solana
instance is EXACTLY the proven Solana `grantsWeight` — the generalization specializes back
to the deployed model, so every generic theorem above is a genuine generalization of the
Solana ones, not a parallel toy. -/
theorem solana_specializes (o : HoldingsProof) (h : ProvenHolding) (v : VoterId) (w : Weight) :
    grantsWeightG (solanaChain o) () (solanaHolding o h) v w ↔ grantsWeight o h v w := by
  cases ht : h.trust <;>
    simp [grantsWeightG, grantsWeight, solanaChain, solanaHolding, GTier.ofTrustTier, ht]

/-- The generic gate FIRES (positive) on the Solana instance, via the specialization and
the proven Solana `proven_grants_weight`. -/
theorem solana_generic_grants :
    grantsWeightG (solanaChain demoOracle) () (solanaHolding demoOracle provenHolding) 7 100 :=
  (solana_specializes demoOracle provenHolding 7 100).mpr proven_grants_weight

/-- The generic tier discriminator has TEETH on Solana: the same holding on the `rpc`
(structureOnly) tier grants nothing — transported from the proven Solana teeth. -/
theorem solana_generic_rpc_teeth :
    ¬ grantsWeightG (solanaChain demoOracle) () (solanaHolding demoOracle rpcHolding) 7 100 := by
  rw [solana_specializes]; exact rpc_grants_no_weight

/-- **The generic discriminator fires on the Solana instance** (`gate_discriminates_generic`
applied at Solana): consensus grants `100`, the `rpc` variant grants nothing, `101` is
ungrantable. Mirrors the Solana `gate_discriminates_both_axes`, but through the GENERIC gate. -/
theorem solana_gate_discriminates_generic :
    grantsWeightG (solanaChain demoOracle) () (solanaHolding demoOracle provenHolding) 7 100
    ∧ ¬ grantsWeightG (solanaChain demoOracle) () (solanaHolding demoOracle rpcHolding) 7 100
    ∧ ¬ grantsWeightG (solanaChain demoOracle) () (solanaHolding demoOracle provenHolding) 7 101 :=
  gate_discriminates_generic (solanaChain demoOracle) () (solanaHolding demoOracle provenHolding)
    (solanaHolding demoOracle rpcHolding) 7 100 101
    solana_generic_grants (by rfl) (by decide)

/-! ## §7 — NON-VACUITY INSTANCE (b): a SECOND, genuinely different toy chain.

`toyChain` differs from Solana in two load-bearing ways: (1) finality is STATE-DEPENDENT
(`Finalized h st := h ≤ st`, a height is final once the confirmed head `st` passes it —
unlike Solana, which ignores state), and (2) `Holds` is a NON-TRIVIAL relation
(`proof = amount` — the proof must certify exactly the claimed amount, unlike Solana's
vacuous `True`). Firing the generic theorems here — including `toy_bad_proof_teeth`, which
only bites because `Holds` is non-trivial — proves the abstraction is not `True`-shaped. -/

/-- A minimal SECOND chain: heights and states are `Nat` (`st` = confirmed-head height),
finality is `h ≤ st`, a proof is a claimed amount and `Holds` checks it equals the amount.
(`@[reducible]` so `toyChain.Addr` etc. unfold during `OfNat` numeral synthesis.) -/
@[reducible] def toyChain : ChainParams where
  Height := Nat
  State  := Nat
  Addr   := Nat
  Asset  := Unit
  Proof  := Nat
  Finalized := fun h st => h ≤ st
  Holds := fun proof _ _ amount _ => proof = amount

/-- A valid toy holding: proof `50` certifies owner `3` holds `50` at height `4`, consensus tier. -/
def toyProven : GHolding toyChain :=
  { proof := 50, owner := 3, asset := (), amount := 50, height := 4, tier := .consensusVerified }

/-- The SAME toy holding on the `structureOnly` tier — only the trust axis differs. -/
def toyStructureOnly : GHolding toyChain := { toyProven with tier := .structureOnly }

/-- The SAME toy holding but with a proof that does NOT certify the amount (`999 ≠ 50`). -/
def toyBadProof : GHolding toyChain := { toyProven with proof := 999 }

/-- **TOY GATE FIRES (positive).** At confirmed head `10` (so height `4 ≤ 10` is final) the
proof certifies the amount, so the toy holding grants its full weight `50` to owner `3`. -/
theorem toy_grants : grantsWeightG toyChain 10 toyProven 3 50 :=
  ⟨rfl, (by decide : (4 : Nat) ≤ 10), rfl, rfl, Nat.le_refl 50⟩

/-- **TOY TIER TEETH** (via the generic theorem): the `structureOnly` variant grants nothing. -/
theorem toy_structureOnly_teeth : ¬ grantsWeightG toyChain 10 toyStructureOnly 3 50 :=
  structureOnly_grants_nothing_generic toyChain 10 toyStructureOnly 3 50 (by rfl)

/-- **TOY AMOUNT TEETH** (via the generic theorem): `51 > 50` is ungrantable. -/
theorem toy_overweight_teeth : ¬ grantsWeightG toyChain 10 toyProven 3 51 :=
  overweight_not_grantable_generic toyChain 10 toyProven 3 51 (by decide)

/-- **TOY FINALITY TEETH.** With the confirmed head only at `2`, height `4` is NOT final
(`4 ≤ 2` is false) — the STATE-DEPENDENT finality oracle bites (Solana's could not). -/
theorem toy_unfinalized_teeth : ¬ grantsWeightG toyChain 2 toyProven 3 50 := by
  rintro ⟨_, hf, _, _, _⟩
  exact absurd hf (by decide)

/-- **TOY HOLDS TEETH — the content the generalization ADDS.** A proof that does not
certify the amount (`999 ≠ 50`) grants nothing, EVEN consensus-proven and finalized. This
only bites because `toyChain.Holds` is a non-trivial relation — Solana's `Holds ≡ True`
could never reject here, so this witnesses that abstracting `Holds` is load-bearing. -/
theorem toy_bad_proof_teeth : ¬ grantsWeightG toyChain 10 toyBadProof 3 50 := by
  rintro ⟨_, _, hh, _, _⟩
  exact absurd hh (by decide)

/-- **The generic discriminator fires on the toy chain** (`gate_discriminates_generic` at
toy): consensus grants `50`, the `structureOnly` variant grants nothing, `51` is ungrantable. -/
theorem toy_gate_discriminates_generic :
    grantsWeightG toyChain 10 toyProven 3 50
    ∧ ¬ grantsWeightG toyChain 10 toyStructureOnly 3 50
    ∧ ¬ grantsWeightG toyChain 10 toyProven 3 51 :=
  gate_discriminates_generic toyChain 10 toyProven toyStructureOnly 3 50 51
    toy_grants (by rfl) (by decide)

/-- **TOY NON-CUSTODIAL WITNESS.** The grant emits `some (3, 50)` and leaves the ledger
state `st` (here `10`) definitionally unchanged. -/
theorem toy_grant_is_noncustodial :
    (grantWeightG toyChain toyProven true 10).1 = some (3, 50)
    ∧ (grantWeightG toyChain toyProven true 10).2 = 10 := ⟨rfl, rfl⟩

/-- **TOY FOLD.** Two finalized toy holdings fold to `100`; the fold homomorphism lets a
recursive verifier split the list and add. -/
theorem toy_fold_two :
    foldWeights toyChain [(toyProven, true), (toyProven, true)] = 100 := rfl

/-- **TOY FOLD, structureOnly contributes 0.** The `structureOnly` variant adds nothing to
the fold — the fold's per-step contribution is fail-closed too. -/
theorem toy_fold_structureOnly_zero :
    foldWeights toyChain [(toyStructureOnly, true), (toyProven, true)] = 50 := rfl

/-! It runs (`#guard`). -/

#guard foldWeights toyChain [(toyProven, true), (toyProven, true)] == 100
#guard foldWeights toyChain [(toyStructureOnly, true), (toyProven, true)] == 50
#guard foldContribution toyChain toyProven true == 50
#guard foldContribution toyChain toyProven false == 0
#guard foldContribution toyChain toyStructureOnly true == 0

/-! ## §8 — Axiom hygiene — every generic theorem and instance kernel-clean (CI hard-gate). -/

#assert_axioms weight_backed_and_noncustodial_generic
#assert_axioms granted_weight_is_backed_generic
#assert_axioms grant_preserves_custody_generic
#assert_axioms structureOnly_grants_nothing_generic
#assert_axioms overweight_not_grantable_generic
#assert_axioms gate_discriminates_generic
#assert_axioms granted_weight_le_amount_generic
#assert_axioms grant_output_snapshot_pinned
#assert_axioms grant_weight_independent_of_state
#assert_axioms foldContribution_eq_grant_weight
#assert_axioms foldWeights_append

#assert_axioms ofTrustTier_cv
#assert_axioms solana_specializes
#assert_axioms solana_generic_grants
#assert_axioms solana_generic_rpc_teeth
#assert_axioms solana_gate_discriminates_generic

#assert_axioms toy_grants
#assert_axioms toy_structureOnly_teeth
#assert_axioms toy_overweight_teeth
#assert_axioms toy_unfinalized_teeth
#assert_axioms toy_bad_proof_teeth
#assert_axioms toy_gate_discriminates_generic
#assert_axioms toy_grant_is_noncustodial
#assert_axioms toy_fold_two
#assert_axioms toy_fold_structureOnly_zero

#print axioms weight_backed_and_noncustodial_generic
#print axioms gate_discriminates_generic
#print axioms solana_specializes
#print axioms toy_bad_proof_teeth

end Dregg2.Bridge.ProofOfHoldingsGeneric
