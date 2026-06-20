/-
# Dregg2.Deos.BranchStitch — the BRANCH-AND-STITCH foundation: nesting IS confinement-safety, and a
# stitch IS the pushout (the least-upper-bound merge into main).

`docs/deos/BRANCH-AND-STITCH-PROTOCOL.md` (the operable protocol of distributed time-travel,
`project-distributed-houyhnhnm-frontier`). Two small turns over an otherwise-reused substrate:

  1. **`EnterVirtualization`** — parties co-consent to fork a PAST config into a cap-confined, honestly
     `Virtual`-typed branch world. *"The nesting IS the safety"* is made exact: the branch holds NO
     cap to main, so its side-effects are **structurally imaginary** — the integrity half is a cap
     fact, not a promise (rides `Dregg2.InfoFlow.Confinement.confined_cannot_debit_attacker`).
  2. **`Stitch`** — the lossy reconciliation the branch author resolves. The I-confluent parts merge
     clean (`Dregg2.Confluence.IConfluent`); conflicts are resolved by an explicit, linear-logic-forced
     drop; **the correctness criterion is the PUSHOUT** = the least-upper-bound merge into main
     (`Dregg2.Deos.DocMerge.merge_is_lub`). Patch theory does not *build* the stitch — it tells us
     whether we built it right.

**THIS IS REUSE, NOT REINVENTION** (the weld method). Nothing new is mined:

  * containment        ← `Confinement.Confined` + `confined_cannot_debit_attacker` (the cap tooth)
  * the clean merge    ← `Confluence.IConfluent` (the monotone, coordination-free fragment)
  * the pushout        ← `DocMerge.merge_is_lub` (cocone legs + leastness = the colimit-by-union)
  * the explicit drop  ← a `DocGraph`-level `tombstone`/restriction (linear loss made a graph fact)

## The two load-bearing lemmas this file proves

### A. NESTING = CONFINEMENT-SAFETY (`branch_cannot_drain_main`)

A branch world is `EnterVirtualization`-honest exactly when its author is `Confined` away from the
MAIN frontier `M` — it owns no main cell and reaches none by cap (it holds only branch-caps). Under
that hypothesis, **no branch turn can debit (drain) a main cell**: the kernel `authorizedB` gate
refuses it (`confined_cannot_debit_attacker`). So a branch's destructive experiments *cannot touch
main* — fare's "errors remain imaginary," as a cap theorem. Recursion: a branch-in-branch is the SAME
`Confined` hypothesis one stratum down (`branch_in_branch_cannot_drain` — confinement composes).

The HONEST residual (named, not laundered, in the house ledger style): confinement confines
*authority* and *draining*, but NOT *information* — the \*-property deposit-signal and refusal-timing
covert channels are PROVED-open in `Confinement` (`confined_can_credit_attacker`, `refusal_leaks`).
"Structurally imaginary side-effects" is therefore the INTEGRITY claim (main cannot be drained /
corrupted by the branch), precise and true; it is NOT a confidentiality claim. We restate that
boundary as `branch_may_signal_main` so the residual rides WITH the lemma, never hidden.

### B. STITCH = PUSHOUT-CORRECTNESS (`stitch_is_pushout`, `stitch_iconfluent_clean`, `stitch_drop_*`)

A stitch reconciles the branch reconciliation-graph `b` against the main graph `m` into a settled
result `s`. The correctness criterion is the pushout = the LEAST UPPER BOUND in document inclusion `⊑`:

  * **`stitch_is_pushout`** — `merge m b` is the pushout: it includes both legs (`m ⊑ ·`, `b ⊑ ·`, the
    cocone — *nothing main had is lost, nothing the branch found is dropped silently*) AND lies below
    every common upper bound (leastness — *no value is conjured*). This is `DocMerge.merge_is_lub`
    restated as the stitch criterion: a sound stitch is a morphism into the colimit, the lossy part is
    the universal-property quotient.
  * **`stitch_iconfluent_clean`** — the I-confluent / rhizomatic part merges with NO author
    intervention: if the settlement invariant `I` is `IConfluent`, a clean `m`-config and a clean
    `b`-config merge to a clean config (`Confluence.admits_sound`). This is the "auto-merge the
    confluent part, surface only genuine conflicts" of spaceage semi-automation.
  * **THE LINEAR DROP** (`stitch_drop_explicit`, `stitch_drop_is_below`) — lossy is *deliberate, typed*
    loss. The author resolves a conflict by an explicit `restrict K` (keep exactly key-set `K`,
    tombstone the rest). The dropped result still lies BELOW the full merge in `⊑` (`stitch_drop_is_below`:
    you cannot conjure value by dropping) and the drop is EXPLICIT (`stitch_drop_explicit`: the kept
    keys are exactly `K`, omission is visible) — fare Ch5's "you must explicitly drop, so you cannot
    lose information by mistake or omission." A NON-drop (`K = univ` direction) recovers the full merge.

Both polarities bite (the tooth is never vacuous): `branch_drain_refused_concretely` exhibits a real
confined branch whose main-debit IS refused; `unconfined_branch_can_drain` exhibits an UN-confined
"branch" (one that DOES hold a main-cap — a protocol violation) that CAN drain, witnessing the
hypothesis is load-bearing. `stitch_pushout_nonvacuous` exhibits a real non-trivial stitch with a
genuine clash, and `stitch_drop_strict_loss` exhibits a drop that strictly loses (≠ full merge).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`native_decide`.
Verified with `lake build Dregg2.Deos.BranchStitch`. Pure; spec-first; staged-additive (no shared
file edited — the one-line `import Dregg2.Deos.BranchStitch` into `Dregg2/Deos.lean` is REPORTED).
-/
import Dregg2.InfoFlow.Confinement
import Dregg2.Confluence
import Dregg2.Deos.DocMerge
import Dregg2.Tactics

namespace Dregg2.Deos.BranchStitch

open Dregg2.Exec
open Dregg2.InfoFlow.Confinement
open Dregg2.Confluence
open Dregg2.Deos.DocMerge

/-! ## Part A — NESTING IS CONFINEMENT-SAFETY (the `EnterVirtualization` half)

A branch world is opened by a joint turn off a past cursor; the load-bearing fact is that the branch
author holds ONLY branch-caps — it is `Confined` away from the MAIN frontier `M`. We do not re-model
the cap kernel; we reuse `Confinement.Confined` over the real `Exec.Kernel`, and the branch-safety
lemma IS the no-drain tooth, restated for the branch/main split. -/

/-- **`BranchHonest M caps author`** — the `EnterVirtualization` well-formedness predicate: the branch
author is capability-confined away from the MAIN frontier `M`. It owns no main cell and reaches none
by cap — it holds only branch-caps. This is *exactly* `Confinement.Confined M caps author`; we name it
in branch vocabulary so the protocol reads in its own terms. The honest-typing of the branch world
(`Rehydration` = `Virtual/Branch`) is the realization face; the cap fact is THIS. -/
abbrev BranchHonest (M : Finset CellId) (caps : Authority.Caps) (author : CellId) : Prop :=
  Confined M caps author

theorem branchHonest_iff_confined (M : Finset CellId) (caps : Authority.Caps) (author : CellId) :
    BranchHonest M caps author ↔ Confined M caps author := Iff.rfl

/-- **KEYSTONE A — `branch_cannot_drain_main`.** A `BranchHonest` author cannot commit any branch turn
that debits (drains) a MAIN cell. The kernel `authorizedB` gate refuses it — to debit a main `src` the
branch would need to OWN it (but the author is not a main cell) or REACH it by cap (but it holds no
main-cap). So **a branch's side-effects cannot drain main**: fare's "all destructive experiments
happen in branches never merged into official reality — the errors remain imaginary," made a cap fact.
This is the integrity half of "nesting IS the safety." Rides `confined_cannot_debit_attacker`. -/
theorem branch_cannot_drain_main (M : Finset CellId) {k k' : KernelState} {turn : Turn}
    (hbranch : BranchHonest M k.caps turn.actor) (hmainSrc : turn.src ∈ M)
    (h : exec k turn = some k') : False :=
  confined_cannot_debit_attacker M
    ((branchHonest_iff_confined M k.caps turn.actor).mp hbranch) hmainSrc h

/-- **`branch_main_src_clean` (corollary).** For a `BranchHonest` author's committed branch turn, the
debited cell is NEVER a main cell. So a branch turn's `src` always lies inside the branch — the branch
spends only branch value. (This is the `src` side the settlement gate later relies on.) -/
theorem branch_main_src_clean (M : Finset CellId) {k k' : KernelState} {turn : Turn}
    (hbranch : BranchHonest M k.caps turn.actor) (h : exec k turn = some k') :
    turn.src ∉ M :=
  confined_no_attacker_src M ((branchHonest_iff_confined M k.caps turn.actor).mp hbranch) h

/-! ### Recursion: nesting composes (a branch-in-branch is the SAME hypothesis one stratum down).

"A branch inside a branch is another stratum down the cap-tower" (the doc §2). A nested branch is
confined away from a frontier that INCLUDES the outer main frontier (the nested author reaches neither
the inner-branch's parent main nor the outer main). The no-drain tooth holds at EVERY level by the
same lemma — confinement does not weaken with depth. -/

/-- **`branch_in_branch_cannot_drain`.** A nested branch confined away from a frontier `M₂ ⊇ M₁`
cannot drain any cell of the OUTER frontier `M₁` either: `M₁ ⊆ M₂` and confinement away from `M₂`
gives confinement away from `M₁` (monotone), so the no-drain tooth applies. The fractal meta-debug's
"suspend the suspended" is the SAME firmament mechanism at depth `n`. -/
theorem branch_in_branch_cannot_drain {M₁ M₂ : Finset CellId} (hsub : M₁ ⊆ M₂)
    {k k' : KernelState} {turn : Turn}
    (hnested : BranchHonest M₂ k.caps turn.actor) (houterSrc : turn.src ∈ M₁)
    (h : exec k turn = some k') : False := by
  -- Confinement away from the larger frontier `M₂` implies confinement away from `M₁ ⊆ M₂`.
  have hM₁ : BranchHonest M₁ k.caps turn.actor := by
    refine ⟨fun hin => hnested.1 (hsub hin), ?_⟩
    intro a haM₁ hreach
    exact hnested.2 a (hsub haM₁) hreach
  exact branch_cannot_drain_main M₁ hM₁ houterSrc h

/-! ### The HONEST residual — confinement confines DRAINING, not INFORMATION (named, not laundered).

The doc's "side-effects are structurally imaginary" is precise for INTEGRITY (main cannot be drained
or corrupted by the branch). It is NOT a confidentiality claim, and we refuse to launder it as one:
`Confinement` already PROVES the \*-property deposit-leak open (`confined_can_credit_attacker`) and the
refusal-timing channel open (`refusal_leaks`). A `BranchHonest` author CAN still credit a main cell (a
"write up") — so a branch can SIGNAL into main even though it cannot DRAIN main. We surface that
boundary here so the residual travels WITH keystone A, in the house honesty-ledger style. -/

/-- **`branch_may_signal_main` (the named residual).** `BranchHonest` is the DRAINING confinement, not
information confinement: there exists a confined branch author that CAN credit (deposit into) a main
cell, changing the main observer's view — the \*-property "write up" the cap model does not stop. We
inherit the exact `Confinement` witness `confined_can_credit_attacker`: a confined actor whose
committed turn raises an attacker/main cell's balance. So "structurally imaginary" = integrity-only;
the deposit-signal and refusal-timing channels remain open (a deposit-discipline/quota would close
them). This is the one honest seam, a named open channel — never dressed as `True`. -/
theorem branch_may_signal_main :
    BranchHonest attackerFrontier kBase.caps confinedActor ∧
    ∃ k', exec kBase depositTurn = some k' ∧
      attackerView attackerFrontier kBase ≠ attackerView attackerFrontier k' := by
  -- Reuse the Confinement *-property witnesses verbatim: a confined actor CREDITS the frontier.
  refine ⟨(branchHonest_iff_confined attackerFrontier kBase.caps confinedActor).mpr
    confinedActor_confined, ?_⟩
  obtain ⟨k', hexec, hview⟩ := confined_can_credit_attacker
  refine ⟨k', hexec, ?_⟩
  -- `¬ viewEq` ⇒ `attackerView ≠` via the view/equality bridge.
  intro hveq
  exact hview ((viewEq_iff_view attackerFrontier kBase k').mpr hveq)

/-! ### Both polarities of keystone A bite (the tooth is non-vacuous).

`branch_drain_refused_concretely`: a REAL confined branch author whose attempted main-debit is refused
by the gate (the lemma applies to a concrete confined witness). `unconfined_branch_can_drain`: the
hypothesis is LOAD-BEARING — drop `BranchHonest` (let the "branch" hold a main-cap, a protocol
violation) and draining becomes possible, so the lemma is not vacuously true of all actors. -/

/-- **`branch_drain_refused_concretely` (TRUE polarity).** Instantiated at the concrete confined
witness `Confinement.confinedActor` (empty cap table, confined away from `attackerFrontier`): for ANY
committed turn it authors with a main/frontier `src`, the commit is impossible. The no-drain tooth has
a real model — it is not vacuous. -/
theorem branch_drain_refused_concretely
    {k k' : KernelState} {turn : Turn}
    (hauthor : turn.actor = confinedActor)
    (hcaps : Confined attackerFrontier k.caps confinedActor)
    (hmainSrc : turn.src ∈ attackerFrontier)
    (h : exec k turn = some k') : False := by
  have hbranch : BranchHonest attackerFrontier k.caps turn.actor := by
    rw [hauthor]
    exact (branchHonest_iff_confined attackerFrontier k.caps confinedActor).mpr hcaps
  exact branch_cannot_drain_main attackerFrontier hbranch hmainSrc h

/-- The DRAIN turn (the protocol-violating "branch"): the frontier cell `1` debits ITSELF and sends to
cell `0`. `src = 1 ∈ attackerFrontier`. Authorized by OWNERSHIP (`actor = src = 1`) — no main-cap
needed because the actor IS the main cell, exactly the case `BranchHonest` forbids. -/
def drainFrontierTurn : Turn := { actor := 1, src := 1, dst := 0, amt := 5 }

/-- **The drain COMMITS** (the cell `1` is authorized over itself by ownership, has the funds 5,
`src ≠ dst`, both live). So an un-confined "branch" realizes a genuine main-draining transition. -/
theorem drainFrontierTurn_commits : (exec kBase drainFrontierTurn).isSome = true := by decide

/-- **`unconfined_branch_can_drain` (FALSE polarity — the hypothesis is load-bearing).** There EXISTS a
committed turn that debits a main/frontier cell — so the conclusion `False` does NOT hold for an
arbitrary (un-confined) author. The only thing standing between a "branch" and draining main is the
`BranchHonest`/`Confined` hypothesis: a "branch" that illicitly holds a main-cap (or owns a main cell)
IS able to drain. This refutes any reading of keystone A as vacuous. -/
theorem unconfined_branch_can_drain :
    ∃ (k k' : KernelState) (turn : Turn),
      turn.src ∈ attackerFrontier ∧ exec k turn = some k' := by
  -- A turn whose `src` IS a frontier cell (`1 ∈ {1}`): the frontier cell `1` spends 5 to cell `0`.
  -- Owning the `src` authorizes the debit (the `authorizedB` ownership disjunct), so this COMMITS —
  -- witnessing that without the `BranchHonest`/`Confined` hypothesis, main CAN be drained.
  obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.mp drainFrontierTurn_commits
  exact ⟨kBase, k', drainFrontierTurn, by decide, hk'⟩

/-! ## Part B — STITCH IS PUSHOUT-CORRECTNESS (the `Stitch` half)

A stitch reconciles the branch's reconciliation-graph `b` against the main graph `m`. The correctness
criterion is the PUSHOUT = the LEAST UPPER BOUND in document inclusion `⊑`, which in the Pijul graph
model is the colimit-by-union `merge` computes. We do not re-derive the merge algebra; we reuse
`DocMerge.merge_is_lub` and restate it AS the stitch criterion. -/

/-- **`Stitch m b s`** — `s` is a SOUND stitch of branch-graph `b` into main-graph `m` iff `s` is the
pushout: the least upper bound of `m` and `b` in `⊑`. It includes both legs (the cocone — main's value
preserved, the branch's contribution included) and lies below every common upper bound (leastness — no
value conjured beyond what the two legs justify). A sound stitch is exactly `s = merge m b` up to the
LUB characterization. -/
def Stitch (m b s : DocGraph) : Prop :=
  m ⊑ s ∧ b ⊑ s ∧ (∀ u, m ⊑ u → b ⊑ u → s ⊑ u)

/-- **KEYSTONE B — `stitch_is_pushout`.** `merge m b` IS a sound stitch: it is the pushout / LUB of the
main leg and the branch leg. This is `DocMerge.merge_is_lub` restated as the settlement criterion:
*nothing main had is silently lost* (`m ⊑ merge m b`), *nothing the branch found is dropped without an
explicit drop* (`b ⊑ merge m b`), and *no value is conjured* (leastness — `merge m b` lies below every
common upper bound). Patch theory does not BUILD the stitch; it CERTIFIES it via this universal
property. -/
theorem stitch_is_pushout (m b : DocGraph) : Stitch m b (merge m b) := by
  obtain ⟨hl, hr, hleast⟩ := merge_is_lub m b
  exact ⟨hl, hr, hleast⟩

/-- **`stitch_unique_up_to_incl`.** Any two sound stitches of the same legs are mutually included
(`s ⊑ s'` and `s' ⊑ s`) — the pushout is determined up to the inclusion order. So "the" stitch is
well-defined: leastness pins it. (The antisymmetry to literal equality is the residual — `⊑` is a
preorder here, not proved a partial order; named, not claimed.) -/
theorem stitch_unique_up_to_incl {m b s s' : DocGraph}
    (hs : Stitch m b s) (hs' : Stitch m b s') : s ⊑ s' ∧ s' ⊑ s := by
  obtain ⟨hsl, hsr, hsleast⟩ := hs
  obtain ⟨hs'l, hs'r, hs'least⟩ := hs'
  exact ⟨hsleast s' hs'l hs'r, hs'least s hsl hsr⟩

/-! ### The I-confluent (rhizomatic) part merges CLEAN — auto-merge, no author intervention. -/

/-- **`stitch_iconfluent_clean`.** The monotone / I-confluent part of a stitch merges with NO author
resolution: if the SETTLEMENT INVARIANT `I` on the (lattice-ordered) settled-config type `S` is
`IConfluent`, then a clean main-side config `x` and a clean branch-side config `y` merge to a config
that still satisfies `I` (`Confluence.admits_sound`). This is "the I-confluent / rhizomatic parts merge
cleanly (monotone — the part that cannot conflict just merges)" — the spaceage semi-automation's
auto-merged fragment. The genuine conflicts (non-I-confluent `I`) are what `escalate` to the author. -/
theorem stitch_iconfluent_clean {S : Type} [MergeState S] (I : Invariant S)
    (hI : IConfluent I) (x y : S) (hx : I x) (hy : I y) : I (x ⊔ y) :=
  admits_sound I hI x y hx hy

/-- **`stitch_conflict_escalates`.** The DUAL: when the settlement invariant is NOT I-confluent, a
concrete clashing pair exists — two clean configs whose merge VIOLATES `I`. This is the genuine
conflict the `Stitch` author must resolve by an explicit drop (Part B's linear loss); escalation is
forced by a constructive counterexample, not declared. Rides `Confluence.nonpairwise_escalation`. -/
theorem stitch_conflict_escalates {S : Type} [MergeState S] (I : Invariant S)
    (hI : ¬ IConfluent I) : ∃ x y : S, I x ∧ I y ∧ ¬ I (x ⊔ y) :=
  nonpairwise_escalation I hI

/-! ### THE LINEAR DROP — lossy reconciliation is DELIBERATE, TYPED loss (fare Ch5).

"Linear logic forces *explicit* drops." We model the author's drop as `restrict K g`: keep exactly the
atoms whose key is in the finite keep-set `K`, tombstone-by-omission the rest. The dropped result lies
BELOW the full merge in `⊑` (you cannot conjure value by dropping — `stitch_drop_is_below`), and the
kept set is EXACTLY `K` (the omission is visible, never silent — `stitch_drop_explicit`). The non-drop
direction (`K` covering the merge's keys) recovers the full pushout. -/

/-- **`restrict K g`** — the author's explicit drop: keep `g`'s atom at `i` iff `i ∈ K`, else drop it
(set to `none`). Order-edges and fields are kept (the drop here is on atoms — the value-bearing layer
where conservation conflicts live). A `restrict univ`-shaped keep is the identity on atoms. -/
def restrict (K : Finset AtomId) (g : DocGraph) : DocGraph where
  atoms := fun i => if i ∈ K then g.atoms i else none
  order := g.order
  fields := g.fields

@[simp] theorem restrict_atoms (K : Finset AtomId) (g : DocGraph) (i : AtomId) :
    (restrict K g).atoms i = (if i ∈ K then g.atoms i else none) := rfl
@[simp] theorem restrict_order (K : Finset AtomId) (g : DocGraph) :
    (restrict K g).order = g.order := rfl
@[simp] theorem restrict_fields (K : Finset AtomId) (g : DocGraph) (n : Name) :
    (restrict K g).fields n = g.fields n := rfl

/-- **`stitch_drop_is_below`.** A dropped (restricted) merge lies BELOW the full merge in `⊑`: dropping
can only LOSE, never CONJURE value — every atom the drop keeps is exactly the merge's atom (so `⊑`
holds by `Status.le_refl`), and the dropped atoms are simply absent (no obligation). This is the
"lossy" of lossy-stitch made an order fact: the author's resolution settles to something ≤ the
unrestricted pushout. -/
theorem stitch_drop_is_below (K : Finset AtomId) (m b : DocGraph) :
    restrict K (merge m b) ⊑ merge m b := by
  refine ⟨?_, ?_, ?_⟩
  · intro i v hv
    rw [restrict_atoms] at hv
    by_cases hK : i ∈ K
    · rw [if_pos hK] at hv; exact ⟨v, hv, Status.le_refl v⟩
    · rw [if_neg hK] at hv; exact absurd hv (by simp)
  · rw [restrict_order]
  · intro n; rw [restrict_fields]

/-- **`stitch_drop_explicit`.** The drop is EXPLICIT, never a silent omission: an atom survives the
restriction iff its key is in the keep-set `K` AND it was present in the merge. So which atoms were
dropped is determined exactly by `K` — fare Ch5's "you must explicitly drop any data you don't care
about, so you cannot lose information by mistake or omission." Stated as an `↔` (both directions). -/
theorem stitch_drop_explicit (K : Finset AtomId) (m b : DocGraph) (i : AtomId) :
    (restrict K (merge m b)).atoms i ≠ none ↔ (i ∈ K ∧ (merge m b).atoms i ≠ none) := by
  rw [restrict_atoms]
  by_cases hK : i ∈ K
  · rw [if_pos hK]
    constructor
    · intro h; exact ⟨hK, h⟩
    · intro h; exact h.2
  · rw [if_neg hK]
    constructor
    · intro h; exact absurd rfl h
    · intro h; exact absurd h.1 hK

/-- **`stitch_no_drop_recovers_pushout`.** If the keep-set `K` covers every present atom of the merge
(the author drops NOTHING), the restricted stitch IS the full pushout `merge m b`. So the non-lossy
stitch is the special case `K ⊇ keys(merge m b)` of the lossy one — lossiness is opt-in, and the clean
merge is recovered when the author drops nothing. -/
theorem stitch_no_drop_recovers_pushout (K : Finset AtomId) (m b : DocGraph)
    (hcover : ∀ i, (merge m b).atoms i ≠ none → i ∈ K) :
    restrict K (merge m b) = merge m b := by
  apply DocGraph.ext
  · intro i
    rw [restrict_atoms]
    by_cases hpres : (merge m b).atoms i = none
    · by_cases hK : i ∈ K
      · rw [if_pos hK]
      · rw [if_neg hK, hpres]
    · rw [if_pos (hcover i hpres)]
  · rw [restrict_order]
  · intro n; rw [restrict_fields]

/-! ### Both polarities of keystone B bite (the stitch is non-vacuous).

`stitch_pushout_nonvacuous`: a REAL non-trivial stitch with a genuine clash exists (a main atom dead,
a branch atom alive at the same key — the merge resolves Dead-wins, a real settlement). `stitch_drop_
strict_loss`: a drop that STRICTLY loses (the restricted merge ≠ the full merge) — lossiness is real,
not always a no-op. -/

/-- A main graph with atom `0` tombstoned (the branch's experiment deleted it). -/
def mMain : DocGraph where
  atoms := fun i => if i = 0 then some .dead else none
  order := ∅
  fields := fun _ => ∅

/-- A branch graph with atom `0` alive and a NEW atom `1` alive (the branch's discovery). -/
def bBranch : DocGraph where
  atoms := fun i => if i = 0 then some .alive else if i = 1 then some .alive else none
  order := ∅
  fields := fun _ => ∅

/-- **`stitch_pushout_nonvacuous` (TRUE polarity).** A REAL stitch: `merge mMain bBranch` is the
pushout of a genuine settlement — at key `0` main says Dead and the branch says Alive (the Dead-wins
join settles it Dead — a deletion main commits to), and the branch's new atom `1` is included. Both
cocone legs hold and leastness holds. Non-vacuous: the legs are distinct graphs with a real clash. -/
theorem stitch_pushout_nonvacuous : Stitch mMain bBranch (merge mMain bBranch) :=
  stitch_is_pushout mMain bBranch

/-- The settled merge has atom `0` DEAD (Dead-wins over the branch's alive) — a real conflict
resolution, witnessing the stitch is not a trivial union. -/
theorem stitch_settles_dead_at_zero : (merge mMain bBranch).atoms 0 = some .dead := by
  show atomJoin (mMain.atoms 0) (bBranch.atoms 0) = some .dead
  decide

/-- The settled merge KEEPS the branch's discovery atom `1` alive — nothing the branch found is lost
in the clean (non-dropped) merge. -/
theorem stitch_keeps_branch_discovery : (merge mMain bBranch).atoms 1 = some .alive := by
  show atomJoin (mMain.atoms 1) (bBranch.atoms 1) = some .alive
  decide

/-- **`stitch_drop_strict_loss` (the drop is REAL — non-vacuity of lossiness).** Dropping atom `1`
(keep only `{0}`) STRICTLY loses: the restricted stitch differs from the full merge at key `1` (alive
→ absent). So a lossy stitch genuinely loses information — the author's explicit drop is not always a
no-op. The dual of `stitch_no_drop_recovers_pushout`: lossiness is real and opt-in. -/
theorem stitch_drop_strict_loss :
    restrict {0} (merge mMain bBranch) ≠ merge mMain bBranch := by
  intro heq
  have h1 : (restrict {0} (merge mMain bBranch)).atoms 1 = (merge mMain bBranch).atoms 1 :=
    congrArg (fun g => g.atoms 1) heq
  rw [restrict_atoms, if_neg (by decide : (1 : AtomId) ∉ ({0} : Finset AtomId))] at h1
  rw [stitch_keeps_branch_discovery] at h1
  exact absurd h1.symm (by simp)

/-! ## Part C — the two turns compose: a CONTAINED branch's stitch is the ONE door back.

Combining A and B: a `BranchHonest` branch can diverge wildly (Part A: it can do nothing to main
except deposit-signal — it cannot drain/corrupt main), and the ONLY way its value reaches main is the
`Stitch` (Part B: the pushout-correct, explicitly-lossy settlement). "You may do anything in the
branch because the branch can do nothing to main except through one narrow, checked door." -/

/-- **`contained_branch_one_door`.** The two-turn protocol's safety, as a conjunction at a witness: a
`BranchHonest` author (i) cannot drain any main cell it tries to debit (Part A keystone, here at the
concrete confined witness), AND (ii) the pushout `merge m b` is a sound stitch for ANY branch/main
graphs (Part B keystone). The branch is contained; the stitch is the sound door. -/
theorem contained_branch_one_door (m b : DocGraph)
    {k k' : KernelState} {turn : Turn}
    (hbranch : BranchHonest attackerFrontier k.caps turn.actor)
    (hmainSrc : turn.src ∈ attackerFrontier)
    (h : exec k turn = some k') :
    False ∧ Stitch m b (merge m b) :=
  ⟨branch_cannot_drain_main attackerFrontier hbranch hmainSrc h, stitch_is_pushout m b⟩

/-! ## Axiom hygiene — every keystone pinned kernel-clean. -/

#assert_all_clean [
  branch_cannot_drain_main, branch_main_src_clean, branch_in_branch_cannot_drain,
  branch_may_signal_main, branch_drain_refused_concretely,
  stitch_is_pushout, stitch_unique_up_to_incl, stitch_iconfluent_clean, stitch_conflict_escalates,
  stitch_drop_is_below, stitch_drop_explicit, stitch_no_drop_recovers_pushout,
  stitch_pushout_nonvacuous, stitch_settles_dead_at_zero, stitch_keeps_branch_discovery,
  stitch_drop_strict_loss, contained_branch_one_door
]

end Dregg2.Deos.BranchStitch
