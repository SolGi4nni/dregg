/-
# Dregg2.Apps.CommitRevealApp — a REAL commit-reveal app guarded by the causal `causallyAfter` atom.

A commit-reveal cell is the canonical front-running-resistant pattern: a participant first publishes a
binding COMMIT (a hiding commitment to their bid/move/value), and only LATER publishes the REVEAL (the
opening). The safety property the app needs is an ORDERING guarantee — **a reveal is admissible only if
it causally FOLLOWS the commit it opens**. A "reveal" that did not observe its commit (a concurrent or
earlier block) is a front-run and must be rejected by the order, not adjudicated by a wall-clock.

This app installs `Authority.CausalGuard`'s `causallyAfter(commit)` atom (via the NAMED-kind wrapper
`Authority.CausalGuardKinds.installCausalAfter`) as the reveal's admission gate, mirroring the shape of
the `*Gated.lean` apps: a factory-born cell whose ops are gated leaves, the admission condition is the
installed guard, and the end-user theorems are the app contract proved against that guard.

## The cell + its ops

  * the **commit** is a published block `commit` on the lace (the hiding commitment);
  * a **reveal(r)** op publishes a candidate reveal block `r` carrying the opened value `revealValue r`,
    gated by `causallyAfter(commit)`: the op ADMITS iff `r` causally follows `commit`
    (a real ack-chain `commit ⤳ r` exists), exactly the `revealNode` admission below.

## The app contract (the three end-user theorems)

  1. `honest_reveal_admitted`   — an HONEST reveal (one that causally follows its commit) is ADMITTED by
     the installed causal guard, and its admission DENOTES the lightcone fact `CausalAfter commit r`;
  2. `frontrun_reveal_rejected` — a reveal that does NOT causally follow its commit (a concurrent /
     front-running block) is REJECTED for EVERY witness chain, and no prover can forge admission;
  3. `reveal_conserves_value`   — the OUTCOME is conserved: the value an admitted reveal yields is
     EXACTLY the value carried by the reveal block (`revealValue r`); admission gates ordering, it never
     mutates the opened payload. (The "no asset moved by the gate" analogue of the *Gated apps'
     per-asset conservation: the causal gate is value-orthogonal.)

Real `#guard` non-vacuity witnesses on the demo lace: genesis `g0` = the commit, honest successor `g1`
= the admitted reveal; fork blocks `f1`/`f2` = a commit and its concurrent front-run reveal (rejected).

§8 boundary: NONE NEW — every result is a pure order fact on the lace's ack-DAG (CausalGuard's floor)
plus registry dispatch. No clock, no authority, no consensus decides admission. Pure, `#eval`-able.
Touches neither `CausalGuard.lean`, `CausalGuardKinds.lean`, `Predicate.lean`, nor `Dregg2.lean`.
-/
import Dregg2.Authority.CausalGuardKinds

namespace Dregg2.Apps.CommitRevealApp

open Dregg2.Authority.Blocklace
open Dregg2.Time.Causal
open Dregg2.Authority.Predicate
open Dregg2.Authority.CausalGuard
open Dregg2.Authority.CausalGuardKinds

/-! ## §1 — The commit-reveal cell: the installed causal guard + the reveal op.

The app is parameterised by the published `commit` block on a lace `B`. The reveal gate is the
`causallyAfter(commit)` atom installed at its NAMED kind over an empty base registry — fail-closed
everywhere except the reveal gate. -/

/-- **`revealGate B commit`** — the commit-reveal cell's admission registry: `causallyAfter(commit)`
installed at its named kind (`causalAfterKind`) over a fail-closed base. The ONE gate the reveal op
consults. -/
def revealGate (B : Lace) (commit : Block) : Registry GateStmt ChainWit :=
  installCausalAfter (emptyReg) B commit

/-- **`revealAdmits B commit r chain`** — the reveal op's admission bit: ACCEPT the candidate reveal
block `r` (with causal-inclusion witness `chain`) iff the installed `causallyAfter(commit)` gate
accepts — i.e. `r` causally follows `commit`. The app's single decidable admission check. -/
def revealAdmits (B : Lace) (commit r : Block) (chain : ChainWit) : Bool :=
  registryVerify (revealGate B commit) causalAfterKind r chain

/-- **`revealValue r`** — the opened payload a reveal block carries (modelled as the block's `seq`, a
stand-in for the committed value the reveal discloses). The OUTCOME the app yields on admission. -/
def revealValue (r : Block) : Nat := r.seq

/-- **`runReveal B commit r chain`** — the reveal op's outcome: `some (revealValue r)` when the causal
guard admits, `none` when it rejects. A childless gated op in the `*Gated.lean` shape (admit ⇒ commit
the opened value; reject ⇒ roll back). -/
def runReveal (B : Lace) (commit r : Block) (chain : ChainWit) : Option Nat :=
  if revealAdmits B commit r chain then some (revealValue r) else none

/-- **`revealAdmits_dispatch`** — the admission bit IS the CausalGuard verifier (through the
named wrapper): `revealAdmits B commit r chain = causallyAfterVerifier B commit r chain`. The hinge
every contract theorem rewrites through. -/
theorem revealAdmits_dispatch (B : Lace) (commit r : Block) (chain : ChainWit) :
    revealAdmits B commit r chain = causallyAfterVerifier B commit r chain := by
  unfold revealAdmits revealGate
  exact causalAfter_dispatch emptyReg B commit r chain

/-! ## §2 — APP CONTRACT THEOREM 1: an HONEST reveal (causally after its commit) is ADMITTED. -/

/-- **`honest_reveal_admitted` — the headline.** If the reveal `r` causally follows the commit
(witnessed by a genuine ack-chain `chain`, `causallyAfterVerifier B commit r chain = true`), then the
commit-reveal cell ADMITS it — `revealAdmits B commit r chain = true` — and its admission DENOTES the
lightcone fact `CausalAfter B commit r` (the reveal really observed the commit). The op COMMITS the
opened value: `runReveal B commit r chain = some (revealValue r)`. The honest reveal succeeds exactly
because the causal edge exists. -/
theorem honest_reveal_admitted (B : Lace) (commit r : Block) (chain : ChainWit)
    (hcausal : causallyAfterVerifier B commit r chain = true) :
    revealAdmits B commit r chain = true ∧
      CausalAfter B commit r ∧
      runReveal B commit r chain = some (revealValue r) := by
  have hadmit : revealAdmits B commit r chain = true := by
    rw [revealAdmits_dispatch]; exact hcausal
  refine ⟨hadmit, ?_, ?_⟩
  · exact causallyAfter_denotes_precedes B commit r chain hcausal
  · unfold runReveal; rw [hadmit]; rfl

/-- **`honest_reveal_discharges`** — an honest reveal discharges the predicate through the
registry keystone (`registry_sound`): the admission is soundness-by-verification, identical to every
witnessed kind. The causal guard is a first-class registry plugin, not bespoke app logic. -/
theorem honest_reveal_discharges (B : Lace) (commit r : Block) (chain : ChainWit)
    (hcausal : causallyAfterVerifier B commit r chain = true) :
    @Dregg2.Laws.Discharged GateStmt ChainWit
      (verifiableOfRegistry (revealGate B commit) causalAfterKind) r chain := by
  apply causalAfter_named_discharges emptyReg B commit r chain
  rw [← revealAdmits_dispatch] at hcausal
  exact hcausal

/-! ## §3 — APP CONTRACT THEOREM 2: a reveal NOT causally following its commit is REJECTED. -/

/-- **`frontrun_reveal_rejected` — the front-running teeth.** If the reveal `r` does NOT
causally follow the commit (`¬ CausalAfter B commit r` — a concurrent or earlier block), then NO
witness chain can make the cell admit it: for EVERY chain the guard rejects (`revealAdmits = false`)
and the op rolls back (`runReveal = none`). A reveal that never observed its commit is structurally
inadmissible — front-running excluded by the order, not adjudicated by a clock. -/
theorem frontrun_reveal_rejected (B : Lace) (commit r : Block)
    (hnotafter : ¬ CausalAfter B commit r) :
    ∀ chain : ChainWit,
      revealAdmits B commit r chain = false ∧ runReveal B commit r chain = none := by
  intro chain
  have hrej : revealAdmits B commit r chain = false := by
    rw [revealAdmits_dispatch]
    by_contra hne
    have hacc : causallyAfterVerifier B commit r chain = true := by
      cases hb : causallyAfterVerifier B commit r chain
      · exact absurd hb hne
      · rfl
    exact hnotafter (causallyAfter_denotes_precedes B commit r chain hacc)
  refine ⟨hrej, ?_⟩
  unfold runReveal; rw [hrej]; rfl

/-- **`frontrun_reveal_unforgeable` — no prover can admit a front-run.** Installed at its named
kind, the `causallyAfter(commit)` gate rejects a reveal `r` whose causal check fails for EVERY prover
and EVERY witness chain it proposes (`causalAfter_named_cannot_forge`). A reveal that did not causally
follow its commit has no admitting path through the in-TCB gate — the non-amplification statement for
the commit-reveal app. -/
theorem frontrun_reveal_unforgeable (B : Lace) (commit r : Block) (chain : ChainWit)
    (hreject : causallyAfterVerifier B commit r chain = false) :
    ∀ (find : GateStmt → Option ChainWit), find r = some chain →
      revealAdmits B commit r chain = false := by
  intro find hfound
  unfold revealAdmits revealGate
  exact causalAfter_named_cannot_forge emptyReg B commit r chain hreject find hfound

/-! ## §4 — APP CONTRACT THEOREM 3: the OUTCOME is CONSERVED (the gate is value-orthogonal). -/

/-- **`reveal_conserves_value` — admission never mutates the payload.** WHENEVER the reveal op
commits (`runReveal B commit r chain = some v`), the yielded value `v` is EXACTLY the value the reveal
block carries: `v = revealValue r`. The causal guard gates ORDERING, never the opened payload — it
cannot substitute, inflate, or drop the revealed value. The "no asset moved by the gate" property of
the commit-reveal app: a passing/failing gate is value-orthogonal, exactly as the `*Gated.lean` apps'
caveat/credential gate is balance-orthogonal. -/
theorem reveal_conserves_value (B : Lace) (commit r : Block) (chain : ChainWit) {v : Nat}
    (h : runReveal B commit r chain = some v) :
    v = revealValue r := by
  unfold runReveal at h
  by_cases hadmit : revealAdmits B commit r chain
  · rw [if_pos hadmit] at h; exact (Option.some.injEq _ _ ▸ h).symm
  · rw [if_neg hadmit] at h; exact absurd h (by simp)

/-! ## §5 — NON-VACUITY: the commit-reveal app on the concrete demo lace.

The demo cell: genesis `g0` is the COMMIT; honest successor `g1` (which acks `g0`) is the admitted
REVEAL. The fork pair `f1`/`f2` (concurrent, `f2 ∥ f1`) is a commit `f1` and a FRONT-RUN reveal `f2`
that did not observe it (rejected). Both decided by the lace alone — no clock is ever consulted. -/

/-- The demo commit (genesis `g0`). -/
abbrev demoCommit : Block := g0
/-- The demo honest reveal (`g1`, which acks `g0`). -/
abbrev demoReveal : Block := g1
/-- The honest causal-inclusion witness: the empty chain (`g1` directly acks `g0`). -/
def demoChain : ChainWit := []
/-- The demo front-run commit (`f1`) and its concurrent front-run reveal (`f2`). -/
abbrev demoFrontCommit : Block := f1
abbrev demoFrontReveal : Block := f2

-- The honest reveal is ADMITTED (the direct ack edge `g0 ← g1` is the whole causal walk):
#guard revealAdmits demoLace demoCommit demoReveal demoChain                  -- true (admitted)
-- ...and the op COMMITS the opened value (`revealValue g1 = g1.seq = 1`):
#guard (runReveal demoLace demoCommit demoReveal demoChain == some 1)         -- true (some 1)
-- The FRONT-RUN reveal is REJECTED (no ack edge `f1 ← f2`; the reveal never observed the commit):
#guard (revealAdmits demoLace demoFrontCommit demoFrontReveal [] == false)    -- true (rejected)
-- ...and the op ROLLS BACK:
#guard (runReveal demoLace demoFrontCommit demoFrontReveal [] == none)        -- true (none)

/-- **`demo_honest_reveal_admitted`** — the app contract THEOREM 1 witnessed on the demo lace:
the honest reveal is admitted, denotes `CausalAfter`, and commits value `1`. NON-VACUOUS positive. -/
theorem demo_honest_reveal_admitted :
    revealAdmits demoLace demoCommit demoReveal demoChain = true ∧
      CausalAfter demoLace demoCommit demoReveal ∧
      runReveal demoLace demoCommit demoReveal demoChain = some (revealValue demoReveal) :=
  honest_reveal_admitted demoLace demoCommit demoReveal demoChain (by decide)

/-- **`demo_frontrun_reveal_rejected`** — the app contract THEOREM 2 witnessed on the demo
lace: the concurrent front-run reveal `f2` is rejected for EVERY witness chain, and the op rolls back.
NON-VACUOUS negative — the front-running teeth bite. -/
theorem demo_frontrun_reveal_rejected (chain : ChainWit) :
    revealAdmits demoLace demoFrontCommit demoFrontReveal chain = false ∧
      runReveal demoLace demoFrontCommit demoFrontReveal chain = none :=
  frontrun_reveal_rejected demoLace demoFrontCommit demoFrontReveal demo_causalAfter_fails.1 chain

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms revealAdmits_dispatch
#assert_axioms honest_reveal_admitted
#assert_axioms honest_reveal_discharges
#assert_axioms frontrun_reveal_rejected
#assert_axioms frontrun_reveal_unforgeable
#assert_axioms reveal_conserves_value
#assert_axioms demo_honest_reveal_admitted
#assert_axioms demo_frontrun_reveal_rejected

end Dregg2.Apps.CommitRevealApp
