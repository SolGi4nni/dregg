/-
# Market.WideCommitBoundary — the faithful eight-lane light-client boundary.

The generic circuit apex historically collapsed a deployed state commitment to one `ℤ`.
This module keeps the deployed shape: the commitment is the eight-felt result of the
`wireCommitR8` chain over a 178-limb kernel payload, with the receipt-log root absorbed
last.  The payload's first limb is the already-proved `CommitSurface.commit`; the
remaining 177 lanes are domain-separated headroom for the deployed layout.  Thus the
wide chain adds no new trust: the wide commitment recovers the entire payload and receipt
root, then `CommitSurface.commit_binds` recovers the kernel.

## ⚑ THE HEADLINE BINDING IS A SECURITY REDUCTION, not a disjunction (§R).

The anchor `turn/src/state_commit.rs` consumes is the wide `STATE_COMMIT` carrier
(`wireCommitR8` / `wire_commit_8_chip`).  Its binding used to be exported as the bare
disjunction `stateDecode8_pre_faithful : pre = pre' ∨ WireColl …` — the extraction-as-data
keystone that replaced the FALSE `Poseidon2WideCR` injectivity.  That was true at deployed
BabyBear parameters (unlike injectivity), but it is still a SHIRK: a collision EXISTS at
those parameters by pigeonhole (`VacuitySweepTeeth.widePerm_not_injective_babyBear`), so
`binds ∨ collides` is satisfiable through the `collides` branch WITHOUT `binds` ever
holding.  It NAMES the floor; it does not STAND on it.  It quantifies over SOLUTIONS
(a collision exists), where cryptographic hardness quantifies over EFFICIENT ADVERSARIES.

§R rebuilds it with the correct structure — a SECURITY REDUCTION to a NAMED hardness
assumption over EFFICIENT ADVERSARIES:

  * the honest floor is `FloorGames.HashCRHardQuant (wideFamily D) Eff` — a real collision
    game of the deployed wide permutation at an explicit adversary class `Eff`, negligible
    advantage.  It is NOT injectivity (false), NOT `∃ collision` (a solution).  Both poles
    are proved in `InjectiveFloorRegrounded` §3.6: `Eff := ⊤` is FALSE at deployed BabyBear
    params (the honest price of `hEff`), `Eff := ⊥` is vacuous.
  * a state-endpoint forgery is a first-class `Game` (`stateCommitBreakGame`): the adversary
    wins iff it outputs two chained states whose wide-chain inputs DIFFER yet publish the
    SAME eight-felt commit.  `stateDecode8_forgery_is_break` ties it to the deployed
    `StateDecode8` decode object.
  * the reduction (`stateCommit_binds_advantage_bound`) is the EXTRACTOR as a map of
    adversaries: a state forgery → (`stateBreakToWireBreak`) a wire-commit equivocation →
    (`wireBreakToFinder`, via `wireCommit8Find`) a genuine `permW` collision.  Under the
    named floor with the `hEff` obligation on the composed finder, a state forgery has
    NEGLIGIBLE advantage.  The `_binds_or_collides` extractor is the reduction's INTERNAL
    witness, NOT the headline.

The exact-Prop `stateDecode8_pre_faithful`/`_post_faithful` are RETAINED below as the
deterministic backbone (they are what the win relation rests on), explicitly demoted from
"the deployed binding" to "the exact-Prop skeleton".

## ⚑ THE CROSS-LAYER BRIDGE, and what remains (named, not faked).

The reduction closes the WIDE component of the anchor binding.  A state forgery whose wide
inputs AGREE while the states differ is NOT caught by the wide floor — it is a collision of
the receipt-root sponge (`Poseidon2SpongeCR hash`, the 1-felt residual, ~237 consumers, NOT
part of this sweep) or of the kernel commit (`CommitSurface.commit_binds`, its own field).
Those are the SEPARATELY-priced residuals, named at `stateDecode8_pre_faithful`.  What is
NOT yet closed: the exact-Prop AIR layer and the computational game layer are still bridged
per-instance (the game samples a tag; the deployed trace fixes `deployedTag`), and the tree
has no cost model, so `Eff` is an undischarged PARAMETER (`FloorGames` §8) — the honest name
for "the reduction is efficient".

No axiom, `sorry`, `admit`, or native decision procedure.
-/
import Dregg2.Circuit.CircuitSoundness
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Circuit.InjectiveFloorRegrounded
import Dregg2.Crypto.CostAdversary
import Dregg2.Tactics

namespace Market.WideCommitBoundary

open Dregg2.Exec
open Dregg2.Circuit.CircuitSoundness
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (Poseidon2Width8 chainFrom8_len chainFrom8_snoc wireCommitR8 WireColl
   wireCommitR8_binds_or_collides)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame HashCRHardQuant)
open Dregg2.Crypto.ConcreteSecurity (Negl)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Circuit.InjectiveFloorRegrounded
  (WideKeyed wideFamily wireCommitBreakGame wireBreakToFinder wire_adv_le
   wireCommitR8_binds_advantage_bound wide_floor_top_false_babyBear wide_floor_bot_vacuous)

set_option autoImplicit false

/-- The deployed endpoint payload width. -/
def kernelPayloadWidth : Nat := 178

/-- A full-width kernel payload.  Limb zero is the binding full-kernel commitment;
the remaining positions are explicit zero headroom in this abstract boundary codec.
The deployed descriptor refines this codec by replacing those zeroes with its named
rotated lanes; binding of the endpoint needs only the already-binding first limb. -/
def kernelPayload (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) : List ℤ :=
  S.commit k t :: List.replicate (kernelPayloadWidth - 1) 0

set_option maxRecDepth 1000 in
theorem kernelPayload_length (S : CommitSurface) (k : RecordKernelState) (t : BoundaryTurn) :
    (kernelPayload S k t).length = kernelPayloadWidth := by
  change 1 + (List.replicate 177 (0 : ℤ)).length = 178
  rw [List.length_replicate]

/-- The variable preimage of the deployed `hash_fact` chip.  Its fixed namespace
and padding words do not affect the injectivity argument, so the boundary keeps
only the predicate followed by its terms. -/
def factHash (hash : List ℤ → ℤ) (pred : ℤ) (terms : List ℤ) : ℤ :=
  hash (pred :: terms)

/-- One truthful balance receipt.  Ring actions have `actor = src`, but both
fields remain in the digest because both belong to `Turn`. -/
def turnDigest (hash : List ℤ → ℤ) (t : Turn) : ℤ :=
  factHash hash t.actor [t.src, t.dst, t.amt]

theorem turnDigest_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    {a b : Turn} (h : turnDigest hash a = turnDigest hash b) : a = b := by
  have hp := hCR _ _ h
  cases a
  cases b
  simp only [turnDigest, factHash, List.cons.injEq, Nat.cast_inj] at hp
  simp_all

/-- Receipt-index root with the executor's prepend update.  The empty root has a
one-word preimage; every action step has a two-word preimage, so log length is
also bound by collision resistance. -/
def receiptRoot (hash : List ℤ → ℤ) : List Turn → ℤ
  | [] => factHash hash 0 []
  | t :: ts => factHash hash (receiptRoot hash ts) [turnDigest hash t]

theorem receiptRoot_binds (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash) :
    Function.Injective (receiptRoot hash) := by
  intro xs
  induction xs with
  | nil =>
      intro ys h
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hp := hCR _ _ h
          simp [receiptRoot, factHash] at hp
  | cons x xs ih =>
      intro ys h
      cases ys with
      | nil =>
          have hp := hCR _ _ h
          simp [receiptRoot, factHash] at hp
      | cons y ys =>
          have hp := hCR _ _ h
          simp only [receiptRoot, factHash, List.cons.injEq] at hp
          obtain ⟨hroot, hdigest, _⟩ := hp
          have htail : xs = ys := ih hroot
          have hhead : x = y := turnDigest_binds hash hCR hdigest
          subst ys
          subst y
          rfl

/-- Exactly eight felts, with width carried by the type rather than a side premise. -/
structure Felt8 where
  vals : List ℤ
  width : vals.length = 8

@[ext] theorem Felt8.ext {a b : Felt8} (h : a.vals = b.vals) : a = b := by
  cases a
  cases b
  simp_all

/-- `wireCommitR8` always returns the deployed eight-lane width. -/
theorem wireCommitR8_length (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (limbs : List ℤ) (iroot : ℤ) : (wireCommitR8 permW limbs iroot).length = 8 := by
  unfold wireCommitR8
  rw [chainFrom8_snoc]
  exact hW _

/-- The faithful eight-lane commitment of one chained kernel state. -/
def commit8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (s : RecChainedState)
    (t : BoundaryTurn) : Felt8 :=
  ⟨wireCommitR8 permW (kernelPayload S s.kernel t) (receiptRoot hash s.log),
    wireCommitR8_length permW hW _ _⟩

/-- Published endpoint surface for the shielded-ring batch. -/
structure PublishedCommit8 where
  pubPre : Felt8
  pubPost : Felt8
  turn : BoundaryTurn
  creators : Fin 2 → CellId
  turnCount : Nat
  preReceiptRoot : ℤ
  postReceiptRoot : ℤ

/-- Faithful decode of the eight-lane endpoint, including its receipt-chain roots. -/
structure StateDecode8 (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (S : CommitSurface) (pc : PublishedCommit8)
    (pre post : RecChainedState) : Prop where
  preBinds : pc.pubPre = commit8 permW hW hash S pre pc.turn
  postBinds : pc.pubPost = commit8 permW hW hash S post pc.turn
  preReceiptBinds : pc.preReceiptRoot = receiptRoot hash pre.log
  postReceiptBinds : pc.postReceiptRoot = receiptRoot hash post.log
  preWF : Dregg2.Circuit.StateCommit.AccountsWF pre.kernel
  postWF : Dregg2.Circuit.StateCommit.AccountsWF post.kernel

/-- **EXACT-PROP BACKBONE (NOT the headline binding — see §R).** Equal faithful pre endpoints
determine the entire chained pre-state — OR exhibit a genuine collision of the deployed wide
permutation.  The headline anchor binding is the REDUCTION `stateCommit_binds_advantage_bound` (§R);
this deterministic disjunction is retained as the win relation's exact-Prop skeleton and to name the
two SEPARATELY-priced residuals of the `pre = pre'` branch.

⚑ **NO WIDE CR FLOOR IS CARRIED.** The old form took `hWideCR : Poseidon2WideCR permW` — DELETED,
because the deployed `single_perm_compress` REFUTES it, so the theorem was VACUOUSLY TRUE at deployed
parameters.  The `WireColl` disjunct is now priced by §R's reduction (negligible under the wide
collision floor `HashCRHardQuant (wideFamily D) Eff`).  The `pre = pre'` branch is closed by TWO named
residuals: `CommitSurface.commit_binds` (the kernel commit, unconditional) and
`hReceiptCR : Poseidon2SpongeCR hash` (the 1-felt receipt-root sponge — a NAMED, still-open residual,
~237 files of consumers, NOT part of this sweep). -/
theorem stateDecode8_pre_faithful (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (hReceiptCR : Poseidon2SpongeCR hash)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') :
    pre = pre' ∨ WireColl permW (kernelPayload S pre.kernel pc.turn)
      (receiptRoot hash pre.log) (kernelPayload S pre'.kernel pc.turn)
      (receiptRoot hash pre'.log) := by
  have hwide :
      wireCommitR8 permW (kernelPayload S pre.kernel pc.turn) (receiptRoot hash pre.log) =
        wireCommitR8 permW (kernelPayload S pre'.kernel pc.turn) (receiptRoot hash pre'.log) := by
    have := congrArg Felt8.vals (h.preBinds.symm.trans h'.preBinds)
    simpa [commit8] using this
  rcases wireCommitR8_binds_or_collides permW hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide with ⟨hpayload, hroot⟩ | hcoll
  swap
  · exact Or.inr hcoll
  refine Or.inl ?_
  have hkcommit : S.commit pre.kernel pc.turn = S.commit pre'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  have hk : pre.kernel = pre'.kernel :=
    S.commit_binds pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hkcommit
  have hlog : pre.log = pre'.log := receiptRoot_binds hash hReceiptCR hroot
  cases pre
  cases pre'
  simp_all

/-- **EXACT-PROP BACKBONE (NOT the headline binding — see §R).** Equal faithful post endpoints
determine the entire chained post-state — OR exhibit a genuine collision of the deployed wide
permutation.  The `post` twin of `stateDecode8_pre_faithful`; the headline anchor binding is the
REDUCTION `stateCommit_binds_advantage_bound` (§R).

⚑ **NO WIDE CR FLOOR IS CARRIED.** The old form took `hWideCR : Poseidon2WideCR permW` — DELETED,
because the deployed `single_perm_compress` REFUTES it, so the theorem was VACUOUSLY TRUE at deployed
parameters.  The `WireColl` disjunct is priced by §R's reduction; the `post = post'` branch is closed
by `CommitSurface.commit_binds` (kernel commit) and `hReceiptCR : Poseidon2SpongeCR hash` (the 1-felt
receipt-root sponge residual, NOT part of this sweep). -/
theorem stateDecode8_post_faithful (permW : List ℤ → List ℤ)
    (hW : Poseidon2Width8 permW)
    (hash : List ℤ → ℤ) (hReceiptCR : Poseidon2SpongeCR hash)
    (S : CommitSurface) (pc : PublishedCommit8)
    {pre post pre' post' : RecChainedState}
    (h : StateDecode8 permW hW hash S pc pre post)
    (h' : StateDecode8 permW hW hash S pc pre' post') :
    post = post' ∨ WireColl permW (kernelPayload S post.kernel pc.turn)
      (receiptRoot hash post.log) (kernelPayload S post'.kernel pc.turn)
      (receiptRoot hash post'.log) := by
  have hwide :
      wireCommitR8 permW (kernelPayload S post.kernel pc.turn) (receiptRoot hash post.log) =
        wireCommitR8 permW (kernelPayload S post'.kernel pc.turn) (receiptRoot hash post'.log) := by
    have := congrArg Felt8.vals (h.postBinds.symm.trans h'.postBinds)
    simpa [commit8] using this
  rcases wireCommitR8_binds_or_collides permW hW
    (by rw [kernelPayload_length, kernelPayload_length]) hwide with ⟨hpayload, hroot⟩ | hcoll
  swap
  · exact Or.inr hcoll
  refine Or.inl ?_
  have hkcommit : S.commit post.kernel pc.turn = S.commit post'.kernel pc.turn := by
    simpa [kernelPayload] using congrArg List.head? hpayload
  have hk : post.kernel = post'.kernel :=
    S.commit_binds post.kernel post'.kernel pc.turn h.postWF h'.postWF hkcommit
  have hlog : post.log = post'.log := receiptRoot_binds hash hReceiptCR hroot
  cases post
  cases post'
  simp_all

/-- A one-lane endpoint forgery cannot equal an honest eight-lane publication. -/
theorem Felt8.set_ne (x : Felt8) (i : Fin 8) (v : ℤ)
    (hne : some v ≠ x.vals[i.val]?) :
    x.vals.set i v ≠ x.vals := by
  have hi : i.val < x.vals.length := by simpa [x.width] using i.isLt
  intro h
  have this := congrArg (fun ys => ys[i.val]?) h
  simp [List.getElem?_set, hi] at this
  apply hne
  simpa [hi] using congrArg some this

/-! ## §R — the state-commit anchor binding, as a SECURITY REDUCTION.

⚑ **THE HEADLINE.** This section replaces the bare `_binds_or_collides` disjunction as the deployed
binding of the wide `STATE_COMMIT` carrier (`turn/src/state_commit.rs`).  The disjunction quantified
over SOLUTIONS ("a collision exists"); this reduction quantifies over EFFICIENT ADVERSARIES ("every
`Eff`-adversary that forges the state commit finds a `permW` collision, negligible under the floor").
The extractors (`wireCommit8Find` → `wireBreakToFinder`) are the reduction's WITNESS, not the export.

The wide layer reuses the `InjectiveFloorRegrounded` §3 machinery whole: `wideFamily` (the deployed
`single_perm_compress` as a keyed collision family), `wireCommitBreakGame` (the wire-commit
equivocation game), `wire_adv_le` (its advantage ≤ the extracted collision-finder's), and
`wireCommitR8_binds_advantage_bound` (the reduction to `HashCRHardQuant (wideFamily D) Eff`).  What
§R ADDS is the STATE ENDPOINT: the game whose answers are chained states decoding to a published
commit, and the map of adversaries lifting it onto the wire game. -/

/-- **THE STATE-COMMIT FORGERY GAME.** The adversary is handed a sampled domain-separation tag and
WINS iff it outputs two chained states whose wide-chain inputs `(kernelPayload, receiptRoot)` DIFFER
yet publish the SAME eight-felt wide commitment — i.e. it breaks the anchor's binding on the deployed
`wireCommitR8`.  The break is IN the win relation; the wide-input inequality is the honest side
condition that makes this a WIDE forgery (a state equivocation whose wide inputs AGREE is a receipt- or
kernel-commit collision, priced elsewhere). -/
def stateCommitBreakGame (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => RecChainedState × RecChainedState
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ tag c =>
    ((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log)
        ≠ (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log)) ∧
      wireCommitR8 (D.permWAt tag) (kernelPayload S c.1.kernel t) (receiptRoot hash c.1.log)
        = wireCommitR8 (D.permWAt tag) (kernelPayload S c.2.kernel t) (receiptRoot hash c.2.log)
  winsDec := fun _ tag c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the deployed
wide state anchor. -/
theorem stateCommitBreakGame_wins_iff (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (l : ℕ) (tag : D.Tag) (c : RecChainedState × RecChainedState) :
    (stateCommitBreakGame D S hash t).wins l tag c ↔
      (((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log)
          ≠ (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log)) ∧
        wireCommitR8 (D.permWAt tag) (kernelPayload S c.1.kernel t) (receiptRoot hash c.1.log)
          = wireCommitR8 (D.permWAt tag) (kernelPayload S c.2.kernel t) (receiptRoot hash c.2.log)) :=
  Iff.rfl

/-- **⚑ THE FORGERY IS THE DEPLOYED DECODE OBJECT.** Two faithful `StateDecode8` witnesses of the SAME
published commit at the deployed tag, whose wide-chain inputs differ, ARE a `stateCommitBreakGame`
win.  This ties the abstract game to the very endpoint `turn/src/state_commit.rs` anchors — the game is
not a free-floating construction. -/
theorem stateDecode8_forgery_is_break (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (pc : PublishedCommit8) {pre post pre' post' : RecChainedState}
    (h : StateDecode8 (D.permWAt D.deployedTag) (D.width8At D.deployedTag) hash S pc pre post)
    (h' : StateDecode8 (D.permWAt D.deployedTag) (D.width8At D.deployedTag) hash S pc pre' post')
    (hne : (kernelPayload S pre.kernel pc.turn, receiptRoot hash pre.log)
        ≠ (kernelPayload S pre'.kernel pc.turn, receiptRoot hash pre'.log)) :
    (stateCommitBreakGame D S hash pc.turn).wins 0 D.deployedTag (pre, pre') := by
  refine ⟨hne, ?_⟩
  have := congrArg Felt8.vals (h.preBinds.symm.trans h'.preBinds)
  simpa [commit8] using this

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A state-commit forger becomes a wire-commit
equivocator by reading off the two states' wide-chain inputs.  Composed with
`InjectiveFloorRegrounded.wireBreakToFinder` (the chain-walk `wireCommit8Find`), this is the full
reduction from a state forgery to a genuine `permW` collision. -/
def stateBreakToWireBreak (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) :
    Adversary (wireCommitBreakGame D) where
  run := fun l tag =>
    let c := A.run l tag
    ((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log),
     (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log))

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag the state forger wins, the
extracted wire-commit equivocator wins: the wide inputs are distinct (the forgery's side condition),
of EQUAL length (both `kernelPayload`s are 178 limbs), with EQUAL `wireCommitR8` (the equal published
commit).  That is exactly `wireCommitBreakGame`'s win. -/
theorem state_wins_imp (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) (l : ℕ) (tag : D.Tag)
    (hwin : (stateCommitBreakGame D S hash t).wins l tag (A.run l tag)) :
    (wireCommitBreakGame D).wins l tag ((stateBreakToWireBreak D S hash t A).run l tag) := by
  refine ⟨?_, hwin.1, hwin.2⟩
  show (kernelPayload S (A.run l tag).1.kernel t).length
      = (kernelPayload S (A.run l tag).2.kernel t).length
  rw [kernelPayload_length, kernelPayload_length]

/-- **THE ADVANTAGE INEQUALITY.** The state forger's advantage is at most the extracted wire-commit
equivocator's, at every parameter — over the SAME sampled tag space. -/
theorem state_adv_le (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn) (A : Adversary (stateCommitBreakGame D S hash t)) (l : ℕ) :
    gameAdv (stateCommitBreakGame D S hash t) A l
      ≤ gameAdv (wireCommitBreakGame D) (stateBreakToWireBreak D S hash t A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun tag ht => ?_)
  rw [Adversary.hit_eq_true] at ht ⊢
  exact state_wins_imp D S hash t A l tag ht

/-- **⚑ THE REDUCED ANCHOR BINDING — from the wide permutation's collision floor, VIA the reduction.**

Under the DEPLOYED `single_perm_compress`'s collision floor at the class `Eff`, a state-commit forger
whose extracted (state → wire → collision) finder is in that class has NEGLIGIBLE advantage: the
faithful eight-felt state anchor binds the whole wide-chain input (payload + receipt root) except with
negligible probability.  This is the REDUCTION that replaces the bare `_binds_or_collides` disjunction
as the headline binding of the deployed `STATE_COMMIT` carrier.

The advantage inequality is `state_adv_le` (state forger → wire equivocator); the wire → collision
composition and the floor closure both live INSIDE `wireCommitR8_binds_advantage_bound` (which itself
composes `InjectiveFloorRegrounded.wire_adv_le`), so this domination step is the single new layer.

⚑ `hEff` is UNDISCHARGED — the standard "the reduction is efficient", a PARAMETER, in the open, on the
COMPOSED finder `wireBreakToFinder D (stateBreakToWireBreak … A)` (`FloorGames` §8: the tree has no
cost model).  The floor is priced by §R's two poles below: `⊤` FALSE at deployed BabyBear params,
`⊥` vacuous. -/
theorem stateCommit_binds_advantage_bound (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (hEff : Eff (wireBreakToFinder D (stateBreakToWireBreak D S hash t A)))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (stateCommitBreakGame D S hash t) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (stateCommitBreakGame D S hash t) A l).1)
    (state_adv_le D S hash t A)
    (wireCommitR8_binds_advantage_bound D Eff (stateBreakToWireBreak D S hash t A) hEff hCR)

/-- **⚑ THE ⊤ POLE — the floor is FALSE at the REAL BabyBear parameters** (the honest price of `hEff`).
Re-exported from `InjectiveFloorRegrounded.wide_floor_top_false_babyBear`: an eight-lane squeeze into
bounded lanes has finite range while `List ℤ` is infinite, so a collision exists at every tag and the
floor at `Eff := ⊤` is FALSE.  What the reduction buys is not a floor the deployed permutation
satisfies at ⊤ — no such floor exists — it is that the residual is ONE named parameter with both poles
proved, in place of an unclosed disjunction whose right branch is unconditionally available. -/
theorem stateCommit_floor_top_false_babyBear (D : WideKeyed)
    (hb : ∀ (tag : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt tag xs, 0 ≤ x ∧ x < Dregg2.Circuit.VacuitySweepTeeth.babyBearP) :
    ¬ HashCRHardQuant (wideFamily D) (fun _ => True) :=
  wide_floor_top_false_babyBear D hb

/-- **THE ⊥ POLE — vacuous.** Recorded so the floor's satisfiability cannot be mistaken for evidence. -/
theorem stateCommit_floor_bot_vacuous (D : WideKeyed) :
    HashCRHardQuant (wideFamily D) (fun _ => False) :=
  wide_floor_bot_vacuous D

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the state forger's negligibility from the wide collision floor applied at
some OTHER finder `B`, not the one EXTRACTED from the forger.  It does not go through — only
`state_adv_le`/`wire_adv_le` connect the extracted finder to the state game.  A disjunction whose right
branch is always available would carry no more content than `True`; this tooth reds if a future edit
reconnects the games. -/
example (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ) (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (B : Adversary (hashGame (wideFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (wideFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (stateCommitBreakGame D S hash t) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one: with the wide collision floor at the EXTRACTED (composed) finder, the
anchor binding fires. -/
theorem the_reduced_stateCommit_bound_fires (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (hEff : Eff (wireBreakToFinder D (stateBreakToWireBreak D S hash t A)))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (stateCommitBreakGame D S hash t) A) :=
  stateCommit_binds_advantage_bound D S hash t Eff A hEff hCR

/-! ## §P — `hEff` DISCHARGED: efficiency preservation is now a THEOREM, not a parameter.

⚑ **THE ONE-LINE CHANGE `CostAdversary` ENABLES.** `stateCommit_binds_advantage_bound` (§R) still carries
`hEff : Eff (composed finder)` as a bare PARAMETER — the honest name for "the reduction is efficient",
undischarged because `FloorGames` §8 had no cost model. `Dregg2.Crypto.CostAdversary` supplies one, and at
`Eff := IsPolyTime` the parameter becomes a CONSEQUENCE: both reduction hops are
`CostAdversary.Adversary.postMap` instances (pure output reshaping, tag passed through), and
`isPolyTime_postMap` proves each preserves `IsPolyTime` under a poly-bounded overhead. So a state forger
that is EFFICIENT (`hA : IsPolyTime A`), reshaped by the two poly-overhead extractors, stays efficient —
`hEff` is PROVED, not assumed.

The overheads `ovState`/`ovWire` are the reshapings' costs — the chain walk `wireCommit8Find` (`O(depth)`)
and the payload/receipt-root rebuild (`O(depth)`) — carried as poly bounds. That is the honest residual
`FloorGames` §8 named, now localized to "the reduction's glue is poly" instead of a floating `hEff`; the
⊤-collapse witness (the brute-force scanning solver, `CostAdversary.bruteForce`) is NO LONGER admitted,
because it is `¬ PolyTime` (`CostAdversary.bruteForce_not_polyTime`). -/
theorem stateCommit_binds_from_polyTime (D : WideKeyed) (S : CommitSurface) (hash : List ℤ → ℤ)
    (t : BoundaryTurn)
    (A : Adversary (stateCommitBreakGame D S hash t))
    (hA : Dregg2.Crypto.CostAdversary.IsPolyTime A)
    (ovState ovWire : ℕ → ℕ)
    (hovState : Dregg2.Crypto.ConcreteSecurity.PolyBoundedNat ovState)
    (hovWire : Dregg2.Crypto.ConcreteSecurity.PolyBoundedNat ovWire)
    (hCR : HashCRHardQuant (wideFamily D) Dregg2.Crypto.CostAdversary.IsPolyTime) :
    Negl (gameAdv (stateCommitBreakGame D S hash t) A) := by
  have h1 : Dregg2.Crypto.CostAdversary.IsPolyTime (stateBreakToWireBreak D S hash t A) :=
    Dregg2.Crypto.CostAdversary.isPolyTime_postMap
      (G := stateCommitBreakGame D S hash t) (G' := wireCommitBreakGame D)
      (fun _ => rfl)
      (fun _ _ c => ((kernelPayload S c.1.kernel t, receiptRoot hash c.1.log),
                     (kernelPayload S c.2.kernel t, receiptRoot hash c.2.log)))
      ovState hovState hA
  have hEff : Dregg2.Crypto.CostAdversary.IsPolyTime
      (wireBreakToFinder D (stateBreakToWireBreak D S hash t A)) :=
    Dregg2.Crypto.CostAdversary.isPolyTime_postMap
      (G := wireCommitBreakGame D) (G' := hashGame (wideFamily D))
      (fun _ => rfl)
      (fun _ tag c =>
        Dregg2.Circuit.Emit.EffectVmEmitRotationR.wireCommit8Find
          (D.permWAt tag) c.1.1 c.1.2 c.2.1 c.2.2)
      ovWire hovWire h1
  exact stateCommit_binds_advantage_bound D S hash t
    Dregg2.Crypto.CostAdversary.IsPolyTime A hEff hCR

#guard kernelPayloadWidth == 178
#guard receiptRoot (fun xs => xs.sum)
  [{ actor := 1, src := 1, dst := 2, amt := 3 }] == 7

#assert_axioms kernelPayload_length
#assert_axioms turnDigest_binds
#assert_axioms receiptRoot_binds
#assert_axioms wireCommitR8_length
#assert_axioms stateDecode8_pre_faithful
#assert_axioms stateDecode8_post_faithful
#assert_axioms Felt8.set_ne
#assert_axioms stateCommitBreakGame_wins_iff
#assert_axioms stateDecode8_forgery_is_break
#assert_axioms state_wins_imp
#assert_axioms state_adv_le
#assert_axioms stateCommit_binds_advantage_bound
#assert_axioms stateCommit_binds_from_polyTime
#assert_axioms stateCommit_floor_top_false_babyBear
#assert_axioms stateCommit_floor_bot_vacuous
#assert_axioms the_reduced_stateCommit_bound_fires

end Market.WideCommitBoundary
