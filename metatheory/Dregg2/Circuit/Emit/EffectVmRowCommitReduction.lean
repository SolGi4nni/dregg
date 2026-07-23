/-
# `Dregg2.Circuit.Emit.EffectVmRowCommitReduction` — the RUNNABLE EffectVM row's `state_commit`
binding as a SECURITY REDUCTION over EFFICIENT adversaries, on the shared one-felt sponge spine.

## The sin this retires

Every per-effect emission module exported its commitment binding as a BARE DISJUNCTION:

    absorbedCols e₁ = absorbedCols e₂ ∨ TransferColl hash e₁ e₂                            -- narrow
    (baseAbsorbedCols e₁ = baseAbsorbedCols e₂ ∧ roots agree) ∨ WideColl … ∨ RootsColl …   -- wide

Those were a real repair on their predecessors, which carried `Poseidon2Binding.Poseidon2SpongeCR` —
a floor the deployed BabyBear sponge REFUTES (`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`), so
they were VACUOUS exactly where they were supposed to bind the deployed system. But the disjunctions
are still UNCLOSED: a collision EXISTS at deployed parameters by pigeonhole, so `binds ∨ collides` is
satisfiable through the `collides` branch WITHOUT `binds` ever holding. It quantifies over SOLUTIONS.
Cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

## What replaces them, and where the pieces come from

The reduction spine is NOT re-authored here. `Dregg2.Crypto.SpongeCarrierReduction` already provides
it, once, for every one-felt sponge carrier in the tree: `SpongeKeyed` (the deployed sponge keyed by
its domain-separation tag), `spongeFamily`, `carrierBreakGame` (the forgery, with the break IN the win
relation), `carrierBreakToFinder` (the extractor AS A MAP OF ADVERSARIES), `carrier_adv_le` (the
UNCONDITIONAL advantage inequality — the adversary class does not appear in it),
`carrier_binds_advantage_bound` (the conclusion under `FloorGames.HashCRHardQuant (spongeFamily D) Eff`)
and `carrier_binds_from_polyTime` (`hEff` DISCHARGED at `Eff := IsPolyTime` via `CostTactics.poly_time`).

⚑ Why that spine and not `Circuit.Emit.EffectVmCommitReduction` (a sibling lane's module of the same
shape): `EffectVmCommitReduction` lands on `Circuit.Poseidon2KeyedBridge`, which sits ABOVE the whole
`Emit/*` tree in the import graph (`Poseidon2KeyedBridge → FloorRegroundedConsumers →
CommitFaithfulRegrounded → EffectVmEmitRotationR → EffectVmEmitRotation → EffectVmEmitV2 →
EffectVmEmit*`). Importing it from an emission module is a BUILD CYCLE, which is exactly what the
tree currently reports. `SpongeCarrierReduction` restates the same keyed sponge low in the graph for
precisely this reason, and `Crypto.SpongeCarrierBridge` PROVES (by `rfl`) that its family IS
`Poseidon2KeyedBridge`'s. So this module is landed on the same floor, reachable from where the rows
live.

What THIS module adds, and it is only this:

  * **§1 — the two deployed EffectVM commitments as `SpongeCarrier`s.** `group4Carrier` is the
    narrow (13-column) `commitOf` — the H4-of-H4 whose fourth outer slot is the record digest;
    `wideStateCarrier` is the wide (`system_roots`-absorbing) `wideCommitOf`, whose fourth slot is the
    side-table digest, so ONE carrier covers BOTH of the wide commitment's collision legs (the GROUP-4
    tree and the ordered root list) and the reduction lands on ONE floor with no union bound. Each
    supplies the ONLY thing the spine asks for: a total extractor and its UNCONDITIONAL correctness.

  * **§2/§3 — the per-effect ROW games.** `narrowRowBreakGame E` / `wideRowBreakGame E` take the
    effect's OWN runnable descriptor: a win is two rows BOTH ACCEPTED by the deployed circuit
    (`satisfiedVm`) that publish the same commitment and yet bind different state. The descriptor is
    IN the game, so `mint`'s game and `burn`'s game are different types — the `FloorGames` lesson
    ("five names, one `Prop`" → five `Game`s) applied at the row layer. The lift into the carrier game
    is a map of adversaries with a win-preservation theorem.

  * **§4 — the TAMPER sub-games**, which are the `_rejects_state_tamper` / `_rejects_root_tamper`
    teeth: the same forgery with the disagreement PINNED to an absorbed state column, or to a named
    side-table root index.

  * **§5 — `winsDec` WITHOUT `Classical.propDecidable`.** The deployed row denotation is DECIDABLE
    (§0), so putting `satisfiedVm` inside a counted win event needs no classical choice and
    `Adversary.hit` stays a genuine computation.

## What is NOT closed (named, not faked)

This closes the SPONGE component of the runnable commitment binding. It does not touch the per-effect
ROW SEMANTICS (`decodeFull`/`fullClause`, proved separately and unconditionally), nor the cross-cell
`accounts` membership (the turn layer), nor the FRI/STARK floor beneath the proof system. And
`Eff := IsPolyTime` is a cost-VECTOR model of efficiency, not a machine model: what it buys is that
the ⊤-collapse witness is PROVED excluded (`CostAdversary.bruteForce_not_polyTime`) and the class is
PROVED inhabited, with both floor poles proved in `SpongeCarrierReduction` §5.

No `sorry`, no `axiom`, no `native_decide`, no `decide` on an opaque `Prop`. Cost stays SYNTACTIC.
-/
import Dregg2.Circuit.Emit.EffectVmFullStateRunnable
import Dregg2.Crypto.SpongeCarrierReduction

namespace Dregg2.Circuit.Emit.EffectVmRowCommitReduction

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (transferHashSites)
open Dregg2.Circuit.Emit.EffectVmEmitTransferSound
  (absorbedCols transferBlockA transferBlockB transferBlockC commit_eq_commitOf commitOf)
open Dregg2.Circuit.Emit.EffectVmFullStateRunnable
  (baseAbsorbedCols wideHashSites wideBlockA wideBlockB wideBlockC wideCommitOf wide_commit_eq)
open Dregg2.Circuit.Poseidon2Binding (group4Find group4Find_spec)
open Dregg2.Exec.SystemRoots
  (SysRoots systemRootsDigest rootList N_SYSTEM_ROOTS systemRootsDigest_eq_hash_rootList)
open Dregg2.Crypto.SpongeCarrierReduction
  (SpongeKeyed SpongeCarrier IsSpongeColl spongeFamily carrierBreakGame carrierBreakToFinder
   carrier_adv_le carrier_binds_advantage_bound carrier_binds_from_polyTime carrierAnsSize
   spongeAnsSize carrierFloor_top_false_babyBear carrierFloor_bot_vacuous
   carrierFloor_isPolyTime_inhabited)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §0 — DECIDABILITY of the deployed row denotation.

A `Game`'s win event is COUNTED, so `FloorGames.Game.winsDec` is not decoration. Putting the effect's
own `satisfiedVm` INTO the win relation therefore needs the deployed row denotation to be decidable —
supplied here structurally (field congruences and range bounds over `ℤ`; the site walk by recursion on
the site list). No `Classical.propDecidable`, so `Adversary.hit` stays a genuine computation and the
counting probability is the honest finite one. -/

/-- Deciding ONE constraint on a row window: each `holdsVm` arm is a `ZMOD` congruence or `True`,
guarded by a `Bool` flag. -/
instance instDecidableHoldsVm (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint) :
    Decidable (c.holdsVm env isFirst isLast) := by
  cases c with
  | gate body => cases isLast <;> (unfold VmConstraint.holdsVm; infer_instance)
  | transition hi lo => cases isLast <;> (unfold VmConstraint.holdsVm; infer_instance)
  | boundary row body => cases row <;> (unfold VmConstraint.holdsVm; infer_instance)
  | piBinding row col k => cases row <;> (unfold VmConstraint.holdsVm; infer_instance)

/-- Deciding the ordered hash-site walk, by recursion on the site list (the accumulator is data). -/
instance instDecidableSiteGo (hash : List ℤ → ℤ) (env : VmRowEnv) :
    ∀ (ss : List VmHashSite) (acc : List ℤ), Decidable (siteHoldsAll.go hash env acc ss)
  | [], acc => by
      show Decidable True
      infer_instance
  | s :: ss, acc => by
      have : Decidable (siteHoldsAll.go hash env (acc ++ [hash (s.resolvedInputs env acc)]) ss) :=
        instDecidableSiteGo hash env ss _
      show Decidable (env.loc s.digestCol = hash (s.resolvedInputs env acc)
        ∧ siteHoldsAll.go hash env (acc ++ [hash (s.resolvedInputs env acc)]) ss)
      infer_instance

instance instDecidableSiteHoldsAll (hash : List ℤ → ℤ) (env : VmRowEnv) (ss : List VmHashSite) :
    Decidable (siteHoldsAll hash env ss) := instDecidableSiteGo hash env ss []

instance instDecidableRangeHolds (env : VmRowEnv) (r : VmRange) : Decidable (r.holds env) := by
  unfold VmRange.holds; infer_instance

/-- "Is this pair a genuine collision?" is DECIDABLE, so the wide extractor below may branch on it and
remain a TOTAL computable function with no `Classical.choice` in the walk. -/
instance instDecidableIsSpongeColl (h : List ℤ → ℤ) (p : List ℤ × List ℤ) :
    Decidable (IsSpongeColl h p) := by
  unfold IsSpongeColl; infer_instance

/-- **The deployed row denotation is DECIDABLE.** So "this row is accepted by the effect's circuit"
can sit inside a security game's counted win relation without a classical choice. -/
instance instDecidableSatisfiedVm (hash : List ℤ → ℤ) (d : EffectVmDescriptor)
    (env : VmRowEnv) (isFirst isLast : Bool) :
    Decidable (satisfiedVm hash d env isFirst isLast) := by
  unfold satisfiedVm; infer_instance

/-! ## §1 — the two deployed EffectVM commitments, as `SpongeCarrier`s.

Each supplies exactly what the shared spine asks: a TOTAL extractor and its UNCONDITIONAL correctness.
No injectivity, no collision-resistance, no floor — those all live in the `Eff` parameter now. -/

/-- **THE GROUP-4 TRACE DOES NOT BLOW UP ITS INPUT.** Every branch returns either the freshly built
four-slot outer list (`8` felts) or one of the inner block pairs, so the pair it hands back is bounded
by the two inputs' block sizes plus a constant `8`. In the fall-through branch the guards have already
forced `A₁ = A₂`, which is what makes that branch's `(A₁, A₁)` output honestly bounded. -/
theorem group4Find_len_le (h : List ℤ → ℤ) (A₁ B₁ C₁ : List ℤ) (d₁ : ℤ)
    (A₂ B₂ C₂ : List ℤ) (d₂ : ℤ) :
    (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).1.length
      + (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).2.length
      ≤ (A₁.length + B₁.length + C₁.length) + (A₂.length + B₂.length + C₂.length) + 8 := by
  unfold group4Find
  split_ifs with h0 h1 h2 h3
  · simp only [List.length_cons, List.length_nil]; omega
  · simp only; omega
  · simp only; omega
  · simp only; omega
  · push_neg at h1
    subst h1
    simp only
    omega

/-- The payload the NARROW deployed commitment binds: the three absorbed GROUP-4 blocks and the
fourth outer slot (the record digest). -/
abbrev G4Val : Type := (List ℤ × List ℤ × List ℤ) × ℤ

/-- **`group4Carrier` — the deployed 13-column `state_commit`, as a `SpongeCarrier`.** `enc` IS
`EffectVmEmitTransferSound.commitOf` re-presented over the block decomposition; `find` IS the deployed
GROUP-4 peel `Poseidon2Binding.group4Find`, and `find_spec` is its UNCONDITIONAL correctness. -/
def group4Carrier : SpongeCarrier where
  Ctx := Unit
  Val := G4Val
  valDecEq := inferInstance
  enc := fun h _ v => h [h v.1.1, h v.1.2.1, h v.1.2.2, v.2]
  find := fun h _ a b => group4Find h a.1.1 a.1.2.1 a.1.2.2 a.2 b.1.1 b.1.2.1 b.1.2.2 b.2
  find_spec := by
    rintro h _ ⟨⟨A₁, B₁, C₁⟩, d₁⟩ ⟨⟨A₂, B₂, C₂⟩, d₂⟩ hne henc
    rcases group4Find_spec h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂ henc with ⟨hA, hB, hC, hd⟩ | hcoll
    · exact absurd (by rw [hA, hB, hC, hd]) hne
    · exact hcoll
  size := fun _ v => v.1.1.length + v.1.2.1.length + v.1.2.2.length + 1
  outCo := 1
  outBo := 8
  find_len_le := by
    rintro h _ ⟨⟨A₁, B₁, C₁⟩, d₁⟩ ⟨⟨A₂, B₂, C₂⟩, d₂⟩
    have := group4Find_len_le h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂
    show (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).1.length
        + (group4Find h A₁ B₁ C₁ d₁ A₂ B₂ C₂ d₂).2.length
      ≤ 1 * ((A₁.length + B₁.length + C₁.length + 1)
              + (A₂.length + B₂.length + C₂.length + 1)) + 8
    omega

/-- The payload the WIDE deployed commitment binds: the three absorbed GROUP-4 blocks and the WHOLE
side-table sub-block behind the fourth slot. Carrying `SysRoots` (not just its digest) is what makes
ONE carrier cover BOTH of the wide commitment's collision legs. -/
abbrev WideVal : Type := (List ℤ × List ℤ × List ℤ) × SysRoots

/-- The wide extractor: take the GROUP-4 peel's pair when that pair genuinely collides, otherwise the
two ordered side-table root lists. Decidable branch, so this is a TOTAL computable function with no
`Classical.choice` in the walk. -/
def wideFind (h : List ℤ → ℤ) (a b : WideVal) : List ℤ × List ℤ :=
  if IsSpongeColl h (group4Find h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
                                 b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2)))
  then group4Find h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
                    b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2))
  else (rootList a.2, rootList b.2)

/-- **`wideStateCarrier` — the deployed `system_roots`-absorbing `state_commit`, as a
`SpongeCarrier`.** `enc` IS `EffectVmFullStateRunnable.wideCommitOf` with the fourth slot expanded to
the roots sponge (`systemRootsDigest_eq_hash_rootList`), so the payload is the WHOLE 17-field bound
content: twelve absorbed state columns AND the eight side-table roots. -/
def wideStateCarrier : SpongeCarrier where
  Ctx := Unit
  Val := WideVal
  valDecEq := inferInstance
  enc := fun h _ v => h [h v.1.1, h v.1.2.1, h v.1.2.2, h (rootList v.2)]
  find := fun h _ a b => wideFind h a b
  find_spec := by
    intro h _ a b hne henc
    show IsSpongeColl h (wideFind h a b)
    unfold wideFind
    split_ifs with hg
    · exact hg
    · rcases group4Find_spec h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
          b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2)) henc with ⟨hA, hB, hC, hd⟩ | hcoll
      · -- the blocks agree, so the payloads differ in the SIDE-TABLE sub-block.
        have hsr : a.2 ≠ b.2 := by
          intro hs
          apply hne
          obtain ⟨⟨A₁, B₁, C₁⟩, s₁⟩ := a
          obtain ⟨⟨A₂, B₂, C₂⟩, s₂⟩ := b
          simp only at hA hB hC hs
          rw [hA, hB, hC, hs]
        exact ⟨fun hlist => hsr (List.ofFn_inj.mp hlist), hd⟩
      · exact absurd hcoll hg
  size := fun _ v => v.1.1.length + v.1.2.1.length + v.1.2.2.length + (rootList v.2).length
  outCo := 1
  outBo := 8
  find_len_le := by
    intro h _ a b
    have hr₁ : (rootList a.2).length = 8 := by simp [rootList, N_SYSTEM_ROOTS]
    have hr₂ : (rootList b.2).length = 8 := by simp [rootList, N_SYSTEM_ROOTS]
    show (wideFind h a b).1.length + (wideFind h a b).2.length
      ≤ 1 * ((a.1.1.length + a.1.2.1.length + a.1.2.2.length + (rootList a.2).length)
              + (b.1.1.length + b.1.2.1.length + b.1.2.2.length + (rootList b.2).length)) + 8
    unfold wideFind
    split_ifs with hg
    · have := group4Find_len_le h a.1.1 a.1.2.1 a.1.2.2 (h (rootList a.2))
        b.1.1 b.1.2.1 b.1.2.2 (h (rootList b.2))
      omega
    · show (rootList a.2).length + (rootList b.2).length ≤ _
      omega

/-! ## §2 — the NARROW per-effect ROW game, and its lift into the carrier game. -/

/-- The per-effect data a NARROW (13-column) runnable descriptor supplies to ride this reduction: its
hash sites ARE the deployed GROUP-4 sites. That is the whole obligation. -/
structure NarrowRowSpec where
  /-- The effect's emitted EffectVM descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the deployed narrow GROUP-4 sites. -/
  usesTransferSites : descriptor.hashSites = transferHashSites

/-- **THE NARROW ROW FORGERY GAME, AT ONE EFFECT'S DESCRIPTOR.** The adversary is handed a uniformly
sampled domain-separation tag and WINS iff it outputs two rows that are BOTH ACCEPTED by the deployed
circuit `E.descriptor`, publish the SAME after-`state_commit`, and yet DISAGREE on the absorbed
after-state block. A win is a ghost post-state accepted by the circuit the prover runs. -/
def narrowRowBreakGame (D : SpongeKeyed) (E : NarrowRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => VmRowEnv × VmRowEnv
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
      ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
      ∧ absorbedCols c.1 ≠ absorbedCols c.2
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem narrowRowBreakGame_wins_iff (D : SpongeKeyed) (E : NarrowRowSpec) (l : ℕ) (t : D.Tag)
    (c : VmRowEnv × VmRowEnv) :
    (narrowRowBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2 true true
        ∧ c.1.loc (saCol state.STATE_COMMIT) = c.2.loc (saCol state.STATE_COMMIT)
        ∧ absorbedCols c.1 ≠ absorbedCols c.2) :=
  Iff.rfl

/-- Read a row's narrow GROUP-4 payload off its absorbed columns. -/
def narrowPayload (e : VmRowEnv) : G4Val :=
  ((transferBlockA e, transferBlockB e, transferBlockC e),
   e.loc (auxCol aux_off.STATE_RECORD_DIGEST))

/-- **THE LIFT, AS A MAP OF ADVERSARIES.** A row-level forger IS a `group4Carrier` equivocator: read
the two rows' payloads off their columns. -/
def narrowRowToCarrier (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) : Adversary (carrierBreakGame D group4Carrier) where
  run := fun l t => ((), narrowPayload (A.run l t).1, narrowPayload (A.run l t).2)

/-- **⚑ WIN-PRESERVATION.** A row forgery IS a commitment equivocation: satisfaction gives the
deployed hash sites, so each published `state_commit` IS `commitOf` of that row's payload; the shared
commit column then equates the two encodings, and the absorbed-column disagreement makes the payloads
distinct. -/
theorem narrowRow_wins_imp (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (narrowRowBreakGame D E).wins l t (A.run l t)) :
    (carrierBreakGame D group4Carrier).wins l t ((narrowRowToCarrier D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hcommit, hne⟩ := hwin
  have hs₁ : siteHoldsAll (D.hashAt t) (A.run l t).1 transferHashSites :=
    E.usesTransferSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll (D.hashAt t) (A.run l t).2 transferHashSites :=
    E.usesTransferSites ▸ hsat₂.2.1
  refine ⟨?_, ?_⟩
  · -- the payloads DIFFER: `absorbedCols` is exactly the payload flattened.
    intro hpay
    apply hne
    have hA : transferBlockA (A.run l t).1 = transferBlockA (A.run l t).2 :=
      congrArg (fun v => v.1.1) hpay
    have hB : transferBlockB (A.run l t).1 = transferBlockB (A.run l t).2 :=
      congrArg (fun v => v.1.2.1) hpay
    have hC : transferBlockC (A.run l t).1 = transferBlockC (A.run l t).2 :=
      congrArg (fun v => v.1.2.2) hpay
    have hd : (A.run l t).1.loc (auxCol aux_off.STATE_RECORD_DIGEST)
        = (A.run l t).2.loc (auxCol aux_off.STATE_RECORD_DIGEST) :=
      congrArg (fun v => v.2) hpay
    show transferBlockA (A.run l t).1 ++ transferBlockB (A.run l t).1
          ++ transferBlockC (A.run l t).1
          ++ [(A.run l t).1.loc (auxCol aux_off.STATE_RECORD_DIGEST)]
        = transferBlockA (A.run l t).2 ++ transferBlockB (A.run l t).2
          ++ transferBlockC (A.run l t).2
          ++ [(A.run l t).2.loc (auxCol aux_off.STATE_RECORD_DIGEST)]
    rw [hA, hB, hC, hd]
  · -- the two commitments AGREE: each is `commitOf` of its own payload (`enc` IS `commitOf`).
    have h₁ := commit_eq_commitOf (D.hashAt t) (A.run l t).1 hs₁
    have h₂ := commit_eq_commitOf (D.hashAt t) (A.run l t).2 hs₂
    exact h₁.symm.trans (hcommit.trans h₂)

/-- **THE ADVANTAGE INEQUALITY for the narrow lift — UNCONDITIONAL, over ALL adversaries.** -/
theorem narrowRow_adv_le (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E)) (l : ℕ) :
    gameAdv (narrowRowBreakGame D E) A l
      ≤ gameAdv (carrierBreakGame D group4Carrier) (narrowRowToCarrier D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact narrowRow_wins_imp D E A l t ht

/-- **⚑ THE REDUCED NARROW ROW BINDING — the headline that replaces the `_binds_block_or_collides` /
`_binds_state_or_collides` disjunctions.** Under the DEPLOYED sponge's collision floor at the class
`Eff`, a forger producing two SATISFYING rows of the effect's circuit that publish one commitment
while disagreeing on an absorbed state column has NEGLIGIBLE advantage. -/
theorem narrowRow_binds_advantage_bound (D : SpongeKeyed) (E : NarrowRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (narrowRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D group4Carrier (narrowRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (narrowRowBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (narrowRowBreakGame D E) A l).1)
    (narrowRow_adv_le D E A)
    (carrier_binds_advantage_bound D group4Carrier Eff (narrowRowToCarrier D E A) hEff hCR)

/-! ## §3 — the WIDE per-effect ROW game (all 17 fields), and its lift. -/

/-- The per-effect data a WIDE (`system_roots`-absorbing) runnable descriptor supplies: its hash sites
ARE the wide sites. -/
structure WideRowSpec where
  /-- The effect's WIDE emitted descriptor. -/
  descriptor : EffectVmDescriptor
  /-- Its hash sites ARE the `system_roots`-absorbing wide sites. -/
  usesWideSites : descriptor.hashSites = wideHashSites

/-- **THE WIDE FULL-STATE ROW FORGERY GAME, AT ONE EFFECT'S WIDE DESCRIPTOR.** A win is two rows BOTH
ACCEPTED by the deployed wide circuit, each pinning its after-`state_commit` to the published
`NEW_COMMIT`, each carrying the genuine `systemRootsDigest` of its own side-table sub-block, publishing
the SAME `NEW_COMMIT` — and yet DISAGREEING on the absorbed state block or on some side-table root.

The win relation is EXACTLY the hypotheses of
`EffectVmFullStateRunnable.runnable_full_commit_binds_or_collides` plus its NEGATED conclusion: the
game IS "the whole-state anti-ghost fails at this effect's circuit". -/
def wideRowBreakGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
            ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT.** -/
theorem wideRowBreakGame_wins_iff (D : SpongeKeyed) (E : WideRowSpec) (l : ℕ) (t : D.Tag)
    (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) :
    (wideRowBreakGame D E).wins l t c ↔
      (satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
        ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
        ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
        ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
        ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
        ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
        ∧ ¬ (baseAbsorbedCols c.1.1 = baseAbsorbedCols c.2.1
              ∧ ∀ i : Fin N_SYSTEM_ROOTS, c.1.2 i = c.2.2 i)) :=
  Iff.rfl

/-- Read a wide row's payload: its three absorbed GROUP-4 blocks and its side-table sub-block. -/
def widePayload (c : VmRowEnv × SysRoots) : WideVal :=
  ((wideBlockA c.1, wideBlockB c.1, wideBlockC c.1), c.2)

/-- **THE WIDE LIFT, AS A MAP OF ADVERSARIES.** -/
def wideRowToCarrier (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) : Adversary (carrierBreakGame D wideStateCarrier) where
  run := fun l t => ((), widePayload (A.run l t).1, widePayload (A.run l t).2)

/-- **⚑ WIN-PRESERVATION for the wide lift.** Satisfaction gives the wide hash sites, so each
published `state_commit` IS `wideCommitOf` of that row's blocks and carrier; the carrier IS the roots
sponge, so the encoding is the carrier's `enc` at the row's payload. The two commit pins plus the
shared `NEW_COMMIT` equate them, and the 17-field disagreement makes the payloads distinct. -/
theorem wideRow_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideRowBreakGame D E).wins l t (A.run l t)) :
    (carrierBreakGame D wideStateCarrier).wins l t ((wideRowToCarrier D E A).run l t) := by
  obtain ⟨hsat₁, hsat₂, hpin₁, hpin₂, hpub, hc₁, hc₂, hne⟩ := hwin
  have hs₁ : siteHoldsAll (D.hashAt t) (A.run l t).1.1 wideHashSites :=
    E.usesWideSites ▸ hsat₁.2.1
  have hs₂ : siteHoldsAll (D.hashAt t) (A.run l t).2.1 wideHashSites :=
    E.usesWideSites ▸ hsat₂.2.1
  have hcommit : (A.run l t).1.1.loc (saCol state.STATE_COMMIT)
      = (A.run l t).2.1.loc (saCol state.STATE_COMMIT) := by
    rw [hpin₁, hpin₂, hpub]
  refine ⟨?_, ?_⟩
  · -- the payloads DIFFER.
    intro hpay
    apply hne
    have hA : wideBlockA (A.run l t).1.1 = wideBlockA (A.run l t).2.1 :=
      congrArg (fun v => v.1.1) hpay
    have hB : wideBlockB (A.run l t).1.1 = wideBlockB (A.run l t).2.1 :=
      congrArg (fun v => v.1.2.1) hpay
    have hC : wideBlockC (A.run l t).1.1 = wideBlockC (A.run l t).2.1 :=
      congrArg (fun v => v.1.2.2) hpay
    have hsr : (A.run l t).1.2 = (A.run l t).2.2 := congrArg (fun v => v.2) hpay
    refine ⟨?_, fun i => by rw [hsr]⟩
    show wideBlockA (A.run l t).1.1 ++ wideBlockB (A.run l t).1.1 ++ wideBlockC (A.run l t).1.1
        = wideBlockA (A.run l t).2.1 ++ wideBlockB (A.run l t).2.1 ++ wideBlockC (A.run l t).2.1
    rw [hA, hB, hC]
  · -- the two commitments AGREE.
    have h₁ := wide_commit_eq (D.hashAt t) (A.run l t).1.1 hs₁
    have h₂ := wide_commit_eq (D.hashAt t) (A.run l t).2.1 hs₂
    have hr₁ : (A.run l t).1.1.loc sysRootsDigestCol = (D.hashAt t) (rootList (A.run l t).1.2) := by
      rw [hc₁, systemRootsDigest_eq_hash_rootList]
    have hr₂ : (A.run l t).2.1.loc sysRootsDigestCol = (D.hashAt t) (rootList (A.run l t).2.2) := by
      rw [hc₂, systemRootsDigest_eq_hash_rootList]
    show (D.hashAt t) [ (D.hashAt t) (wideBlockA (A.run l t).1.1),
        (D.hashAt t) (wideBlockB (A.run l t).1.1),
        (D.hashAt t) (wideBlockC (A.run l t).1.1),
        (D.hashAt t) (rootList (A.run l t).1.2) ]
      = (D.hashAt t) [ (D.hashAt t) (wideBlockA (A.run l t).2.1),
        (D.hashAt t) (wideBlockB (A.run l t).2.1),
        (D.hashAt t) (wideBlockC (A.run l t).2.1),
        (D.hashAt t) (rootList (A.run l t).2.2) ]
    rw [← hr₁, ← hr₂]
    exact h₁.symm.trans (hcommit.trans h₂)

/-- **THE ADVANTAGE INEQUALITY for the wide lift — UNCONDITIONAL, over ALL adversaries.** -/
theorem wideRow_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E)) (l : ℕ) :
    gameAdv (wideRowBreakGame D E) A l
      ≤ gameAdv (carrierBreakGame D wideStateCarrier) (wideRowToCarrier D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact wideRow_wins_imp D E A l t ht

/-- **⚑ THE REDUCED WIDE FULL-STATE BINDING — the headline that replaces
`_runnable_binds_full_state_or_collides`.** Under the DEPLOYED sponge's collision floor at the class
`Eff`, a forger of the effect's whole 17-field runnable commitment has NEGLIGIBLE advantage. -/
theorem wideRow_binds_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideRowBreakGame D E) A l).1)
    (wideRow_adv_le D E A)
    (carrier_binds_advantage_bound D wideStateCarrier Eff (wideRowToCarrier D E A) hEff hCR)

/-! ## §4 — the TAMPER sub-games: the `_rejects_*_tamper` teeth, as reductions.

A TAMPER is a forgery whose disagreement is LOCALIZED — at an absorbed state-block column (a forged
balance, a tampered field, a forged `cap_root`), or at a named side-table root index (a dropped
escrow, an omitted nullifier, a reordered queue). Each keeps its own game so the exported tooth keeps
its content, and maps into the full-state game by the identity reshaping. -/

/-- **THE STATE-BLOCK TAMPER GAME.** -/
def wideStateTamperGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ baseAbsorbedCols c.1.1 ≠ baseAbsorbedCols c.2.1
  winsDec := fun _ t c => inferInstance

/-- **THE SIDE-TABLE-ROOT TAMPER GAME.** -/
def wideRootTamperGame (D : SpongeKeyed) (E : WideRowSpec) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    satisfiedVm (D.hashAt t) E.descriptor c.1.1 true true
      ∧ satisfiedVm (D.hashAt t) E.descriptor c.2.1 true true
      ∧ c.1.1.loc (saCol state.STATE_COMMIT) = c.1.1.pub pi.NEW_COMMIT
      ∧ c.2.1.loc (saCol state.STATE_COMMIT) = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.pub pi.NEW_COMMIT = c.2.1.pub pi.NEW_COMMIT
      ∧ c.1.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.1.2
      ∧ c.2.1.loc sysRootsDigestCol = systemRootsDigest (D.hashAt t) c.2.2
      ∧ ∃ i : Fin N_SYSTEM_ROOTS, c.1.2 i ≠ c.2.2 i
  winsDec := fun _ t c => inferInstance

/-- A state-block tamper IS a full-state forgery (the identity reshaping). -/
def stateTamperToWide (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) : Adversary (wideRowBreakGame D E) where
  run := fun l t => A.run l t

/-- A side-table-root tamper IS a full-state forgery (the identity reshaping). -/
def rootTamperToWide (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) : Adversary (wideRowBreakGame D E) where
  run := fun l t => A.run l t

theorem stateTamper_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideStateTamperGame D E).wins l t (A.run l t)) :
    (wideRowBreakGame D E).wins l t ((stateTamperToWide D E A).run l t) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, htamper⟩ := hwin
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun h => htamper h.1⟩

theorem rootTamper_wins_imp (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) (l : ℕ) (t : D.Tag)
    (hwin : (wideRootTamperGame D E).wins l t (A.run l t)) :
    (wideRowBreakGame D E).wins l t ((rootTamperToWide D E A).run l t) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, ⟨i, hi⟩⟩ := hwin
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, fun h => hi (h.2 i)⟩

theorem stateTamper_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E)) (l : ℕ) :
    gameAdv (wideStateTamperGame D E) A l
      ≤ gameAdv (wideRowBreakGame D E) (stateTamperToWide D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact stateTamper_wins_imp D E A l t ht

theorem rootTamper_adv_le (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E)) (l : ℕ) :
    gameAdv (wideRootTamperGame D E) A l
      ≤ gameAdv (wideRowBreakGame D E) (rootTamperToWide D E A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact rootTamper_wins_imp D E A l t ht

/-- **⚑ THE REDUCED STATE-BLOCK TAMPER TOOTH — replaces `_rejects_state_tamper_or_collides`.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering an absorbed state-block
column of the effect's wide row, except with negligible probability. -/
theorem wide_state_tamper_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideStateTamperGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D E (stateTamperToWide D E A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideStateTamperGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideStateTamperGame D E) A l).1)
    (stateTamper_adv_le D E A)
    (wideRow_binds_advantage_bound D E Eff (stateTamperToWide D E A) hEff hCR)

/-- **⚑ THE REDUCED SIDE-TABLE-ROOT TAMPER TOOTH — replaces `_rejects_root_tamper_or_collides`.** An
efficient adversary cannot keep the published `NEW_COMMIT` while tampering a side-table root, except
with negligible probability. -/
theorem wide_root_tamper_advantage_bound (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRootTamperGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier
      (wideRowToCarrier D E (rootTamperToWide D E A))))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRootTamperGame D E) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wideRootTamperGame D E) A l).1)
    (rootTamper_adv_le D E A)
    (wideRow_binds_advantage_bound D E Eff (rootTamperToWide D E A) hEff hCR)

/-! ## §5 — `hEff` DISCHARGED at `Eff := IsPolyTime` (efficiency is a THEOREM, overhead DERIVED).

Every lift here is a pure output reshaping (`CostAdversary.Adversary.postMap`), so `CostTactics.poly_time`
applies `isPolyTime_postMap` — which folds in the tight-δ composition and DERIVES the poly overhead from
the forger's own bound — leaving only the output-growth obligation. Those are CONSTANTS here (the
deployed GROUP-4 blocks are four felts wide and the side-table sub-block is eight), so the only honest
modelling input left is each reshaper's DECLARED instruction count: a Lean function has no runtime, so
that number is charged in the program's syntax and can never be derived. -/

/-- **THE ROW GAMES' ANSWER ENCODING** — the effect's own declared trace width and public inputs, the
symbols a forged row costs to write down. Concrete on purpose: a degenerate `sz := 0` would make the
reduction's output free and the cost model vacuous. -/
def narrowRowAnsSize (D : SpongeKeyed) (E : NarrowRowSpec) : AnsSize (narrowRowBreakGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount)

/-- The wide row encoding — the two rows plus their two eight-wide side-table sub-blocks. -/
def wideRowAnsSize (D : SpongeKeyed) (E : WideRowSpec) : AnsSize (wideRowBreakGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)

def stateTamperAnsSize (D : SpongeKeyed) (E : WideRowSpec) : AnsSize (wideStateTamperGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)

def rootTamperAnsSize (D : SpongeKeyed) (E : WideRowSpec) : AnsSize (wideRootTamperGame D E) :=
  fun _ _ => 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)

/-- **⚑ `hEff` DISCHARGED (narrow row).** A row forger efficient at the game's own answer encoding,
lifted to the carrier game and put through the deployed GROUP-4 peel, stays efficient — so the
collision floor at `Eff := IsPolyTime` applies and its advantage is negligible. The output-growth
obligation is the CONSTANT `26` (two 13-felt payloads), proved by computation on the block widths. -/
theorem narrowRow_binds_from_polyTime (D : SpongeKeyed) (E : NarrowRowSpec)
    (A : Adversary (narrowRowBreakGame D E))
    (hA : IsPolyTime (narrowRowAnsSize D E) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (narrowRowBreakGame D E) A) := by
  have h1 : IsPolyTime (carrierAnsSize D group4Carrier) (narrowRowToCarrier D E A) := by
    poly_time (narrowRowAnsSize D E) (carrierAnsSize D group4Carrier)
      (fun _ _ (c : VmRowEnv × VmRowEnv) => ((), narrowPayload c.1, narrowPayload c.2))
      cw₀ bw₀ 0 26 hA
    intro l t c
    show group4Carrier.size () (narrowPayload c.1) + group4Carrier.size () (narrowPayload c.2)
      ≤ 0 * (narrowRowAnsSize D E l c) + 26
    show 13 + 13 ≤ 0 * (narrowRowAnsSize D E l c) + 26
    omega
  exact negl_of_le (fun l => (gameAdv_mem_unit (narrowRowBreakGame D E) A l).1)
    (narrowRow_adv_le D E A)
    (carrier_binds_from_polyTime D group4Carrier (narrowRowToCarrier D E A) h1 cw bw hCR)

/-- **⚑ `hEff` DISCHARGED (wide full-state row).** The output-growth obligation is the CONSTANT `40`
(two payloads of twelve absorbed felts plus an eight-wide side-table sub-block). -/
theorem wideRow_binds_from_polyTime (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRowBreakGame D E))
    (hA : IsPolyTime (wideRowAnsSize D E) A) (cw₀ bw₀ cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideRowBreakGame D E) A) := by
  have h1 : IsPolyTime (carrierAnsSize D wideStateCarrier) (wideRowToCarrier D E A) := by
    poly_time (wideRowAnsSize D E) (carrierAnsSize D wideStateCarrier)
      (fun _ _ (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) =>
        ((), widePayload c.1, widePayload c.2))
      cw₀ bw₀ 0 40 hA
    intro l t c
    show wideStateCarrier.size () (widePayload c.1) + wideStateCarrier.size () (widePayload c.2)
      ≤ 0 * (wideRowAnsSize D E l c) + 40
    have hr₁ : (rootList c.1.2).length = 8 := by simp [rootList, N_SYSTEM_ROOTS]
    have hr₂ : (rootList c.2.2).length = 8 := by simp [rootList, N_SYSTEM_ROOTS]
    show (wideBlockA c.1.1).length + (wideBlockB c.1.1).length + (wideBlockC c.1.1).length
          + (rootList c.1.2).length
        + ((wideBlockA c.2.1).length + (wideBlockB c.2.1).length + (wideBlockC c.2.1).length
          + (rootList c.2.2).length)
      ≤ 0 * (wideRowAnsSize D E l c) + 40
    simp only [show (wideBlockA c.1.1).length = 4 from rfl,
      show (wideBlockB c.1.1).length = 4 from rfl, show (wideBlockC c.1.1).length = 4 from rfl,
      show (wideBlockA c.2.1).length = 4 from rfl, show (wideBlockB c.2.1).length = 4 from rfl,
      show (wideBlockC c.2.1).length = 4 from rfl, hr₁, hr₂]
    omega
  exact negl_of_le (fun l => (gameAdv_mem_unit (wideRowBreakGame D E) A l).1)
    (wideRow_adv_le D E A)
    (carrier_binds_from_polyTime D wideStateCarrier (wideRowToCarrier D E A) h1 cw bw hCR)

/-- **⚑ `hEff` DISCHARGED (state-block tamper).** -/
theorem wide_state_tamper_from_polyTime (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideStateTamperGame D E))
    (hA : IsPolyTime (stateTamperAnsSize D E) A) (cwT bwT cw₀ bw₀ cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideStateTamperGame D E) A) := by
  have h1 : IsPolyTime (wideRowAnsSize D E) (stateTamperToWide D E A) := by
    poly_time (stateTamperAnsSize D E) (wideRowAnsSize D E)
      (fun _ _ (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) => c) cwT bwT 1 0 hA
    intro l t c
    show 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)
      ≤ 1 * (stateTamperAnsSize D E l c) + 0
    simp [stateTamperAnsSize]
  exact negl_of_le (fun l => (gameAdv_mem_unit (wideStateTamperGame D E) A l).1)
    (stateTamper_adv_le D E A)
    (wideRow_binds_from_polyTime D E (stateTamperToWide D E A) h1 cw₀ bw₀ cw bw hCR)

/-- **⚑ `hEff` DISCHARGED (side-table-root tamper).** -/
theorem wide_root_tamper_from_polyTime (D : SpongeKeyed) (E : WideRowSpec)
    (A : Adversary (wideRootTamperGame D E))
    (hA : IsPolyTime (rootTamperAnsSize D E) A) (cwT bwT cw₀ bw₀ cw bw : ℕ)
    (hCR : HashCRHardQuant (spongeFamily D) (IsPolyTime (spongeAnsSize D))) :
    Negl (gameAdv (wideRootTamperGame D E) A) := by
  have h1 : IsPolyTime (wideRowAnsSize D E) (rootTamperToWide D E A) := by
    poly_time (rootTamperAnsSize D E) (wideRowAnsSize D E)
      (fun _ _ (c : (VmRowEnv × SysRoots) × (VmRowEnv × SysRoots)) => c) cwT bwT 1 0 hA
    intro l t c
    show 2 * (E.descriptor.traceWidth + E.descriptor.piCount + N_SYSTEM_ROOTS)
      ≤ 1 * (rootTamperAnsSize D E l c) + 0
    simp [rootTamperAnsSize]
  exact negl_of_le (fun l => (gameAdv_mem_unit (wideRootTamperGame D E) A l).1)
    (rootTamper_adv_le D E A)
    (wideRow_binds_from_polyTime D E (rootTamperToWide D E A) h1 cw₀ bw₀ cw bw hCR)

/-! ## §6 — the floor, PRICED at both poles, plus the canary and the positive pole.

Re-exported from `SpongeCarrierReduction` §5, where both poles are PROVED, so a reader of any
per-effect site can price its instantiation exactly without leaving the row layer. -/

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
A sponge whose output is a genuine BabyBear felt has finite range while `List ℤ` is infinite, so a
collision exists at every tag and the floor at the UNRESTRICTED class is FALSE. What the reduction buys
is NOT a floor the deployed sponge satisfies at ⊤ — no such floor exists — it is that the residual is
ONE named class with both poles proved, in place of a disjunction whose right branch is unconditionally
available at deployed parameters. -/
theorem rowCommitFloor_top_false_babyBear (D : SpongeKeyed)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ HashCRHardQuant (spongeFamily D) (fun _ => True) :=
  carrierFloor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem rowCommitFloor_bot_vacuous (D : SpongeKeyed) :
    HashCRHardQuant (spongeFamily D) (fun _ => False) :=
  carrierFloor_bot_vacuous D

/-- **(TOOTH — the class §5 instantiates at is NOT EMPTY.)** Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is PROVED excluded) this pins the
instantiated floor STRICTLY between the two poles. -/
theorem rowCommitFloor_isPolyTime_inhabited (D : SpongeKeyed) :
    IsPolyTime (spongeAnsSize D)
      (Dregg2.Crypto.CostAdversary.idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  carrierFloor_isPolyTime_inhabited D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the wide row forger's negligibility from the collision floor applied at some
OTHER finder `B`, not the one EXTRACTED from it. It does not go through — only `wideRow_adv_le` and
`carrier_adv_le` connect the extracted finder to the row game. This tooth REDS if a future edit
reconnects them. -/
example (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (wideRowBreakGame D E) A) := hCR B hB)
  trivial

/-- **(CANARY — the narrow keystone likewise.)** -/
example (D : SpongeKeyed) (E : NarrowRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (narrowRowBreakGame D E))
    (B : Adversary (hashGame (spongeFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (spongeFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (narrowRowBreakGame D E) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the floor at the EXTRACTED finder, the wide row binding fires. -/
theorem the_reduced_wideRow_bound_fires (D : SpongeKeyed) (E : WideRowSpec)
    (Eff : Adversary (hashGame (spongeFamily D)) → Prop)
    (A : Adversary (wideRowBreakGame D E))
    (hEff : Eff (carrierBreakToFinder D wideStateCarrier (wideRowToCarrier D E A)))
    (hCR : HashCRHardQuant (spongeFamily D) Eff) :
    Negl (gameAdv (wideRowBreakGame D E) A) :=
  wideRow_binds_advantage_bound D E Eff A hEff hCR

/-! ## §7 — axiom-hygiene tripwires (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_axioms group4Find_len_le
#assert_axioms narrowRowBreakGame_wins_iff
#assert_axioms narrowRow_wins_imp
#assert_axioms narrowRow_adv_le
#assert_axioms narrowRow_binds_advantage_bound
#assert_axioms narrowRow_binds_from_polyTime
#assert_axioms wideRowBreakGame_wins_iff
#assert_axioms wideRow_wins_imp
#assert_axioms wideRow_adv_le
#assert_axioms wideRow_binds_advantage_bound
#assert_axioms wideRow_binds_from_polyTime
#assert_axioms stateTamper_wins_imp
#assert_axioms rootTamper_wins_imp
#assert_axioms stateTamper_adv_le
#assert_axioms rootTamper_adv_le
#assert_axioms wide_state_tamper_advantage_bound
#assert_axioms wide_root_tamper_advantage_bound
#assert_axioms wide_state_tamper_from_polyTime
#assert_axioms wide_root_tamper_from_polyTime
#assert_axioms rowCommitFloor_top_false_babyBear
#assert_axioms rowCommitFloor_bot_vacuous
#assert_axioms rowCommitFloor_isPolyTime_inhabited
#assert_axioms the_reduced_wideRow_bound_fires

end Dregg2.Circuit.Emit.EffectVmRowCommitReduction
