/-
# Dregg2.Authority.CausalGuard — installable guard ATOMS over the blocklace happened-before order.

`Time/Causal.lean` proves the lightcone-fact properties of the partial order `≺` (`precedes`),
and `Time/Frame.lean` shows how an *attested* temporal predicate is built as a witnessed-predicate
atom that the in-TCB registry verifier ACCEPTS or REJECTS. This module joins the two faces: it lifts
the *causal* modalities out of the proof layer and into **installable guard atoms** — verifier
plugins (the `Predicate.Verifier` shape) whose accept bit is a **causal-inclusion check against the
lace order**, exactly as the `temporal` kind's bit is an attested clock reading.

Two atoms, both witnessed-predicate-shaped:

  * **`causallyAfter(E)`** — admissible only if the gated event causally FOLLOWS the named prior
    event `E` (`E ≺ gate`). The verifier is handed a *causal-inclusion witness* — a chain of ack
    edges from `E` up to the gate — and CHECKS each edge is a genuine `pointed` (ack) edge present
    in the lace. A valid chain is exactly a derivation of `precedes B E gate` (soundness); a gate
    that does NOT causally follow `E` has no such chain (the rejected input).

  * **`monotoneOverForks(val)`** — a per-block value never DECREASES along any causal extension:
    whenever `a ≺ b`, `val a ≤ val b`. The guard atom denotes "this quantity is monotone along the
    happened-before order", and the verifier checks the one ack step it gates. A monotone value is
    join-irrelevant in the I-confluence sense (§5): its guard keeps tier-1 coordination-freedom; a
    NON-monotone value's guard couples concurrent branches and forfeits it.

The atoms' denotations are PROVED to coincide with `Time/Causal.precedes` (the happened-before
order), and a concrete commit-reveal guarantee is discharged on the demo lace: a reveal guarded by
`causallyAfter(commit)` is REJECTED when it does not causally follow its commit, ACCEPTED when it
does (the non-vacuity witness).

§8 boundary: NONE NEW. Like `Time/Causal.lean`, every result here is a pure order fact on the lace's
ack-DAG — no clock, no authority, no skew, no signature theorem. The only inherited seams are the
`Blocklace` content-addressing/signature seams, which no theorem below touches. The guard atom needs
NO §8 carrier to decide acceptance — the structural contrast to `Frame.lean`'s attested atom.

Pure, computable, `#eval`-able.
-/
import Dregg2.Time.Causal
import Dregg2.Authority.Predicate
import Dregg2.Confluence

namespace Dregg2.Authority.CausalGuard

open Dregg2.Authority.Blocklace
open Dregg2.Time.Causal
open Dregg2.Authority.Predicate

/-! ## 1. The causal-inclusion WITNESS — a checkable chain of ack edges.

`precedes B E gate` is an inductive `Prop` (the transitive closure of `pointed`); to make it an
INSTALLABLE guard whose verifier emits a `Bool`, the witness it consumes is a concrete *causal
chain*: the list of blocks `[E, m₁, m₂, …, gate]` along which each adjacent pair is a direct ack
edge `mᵢ ← mᵢ₊₁`. The verifier checks every adjacent edge is a genuine `pointed` edge present in the
lace — a per-edge decidable bit (`finality.rs::causal_past`'s BFS, witnessed by the explicit path).
A valid chain DENOTES a derivation of `precedes`; no chain exists when the gate does not observe `E`. -/

/-- **`pointedB B a b`** — the decidable Bool form of `pointed`: `b` directly acks `a`
(`a.id ∈ b.preds`) and both blocks resolve in `B`. This is the per-edge check the guard verifier
runs; `pointedB_iff` ties it to the `Prop` relation. -/
def pointedB (B : Lace) (a b : Block) : Bool :=
  (a.id ∈ b.preds) && (B.lookup a.id == some a) && (B.lookup b.id == some b)

/-- `pointedB` decides `pointed` (the Bool/Prop bridge for one ack edge). -/
theorem pointedB_iff (B : Lace) (a b : Block) : pointedB B a b = true ↔ pointed B a b := by
  unfold pointedB pointed
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  tauto

/-- **`chainOk B src chain dst`** — the verifier's core: the list `chain` is a genuine ack-chain from
`src` to `dst`. `chain` lists the blocks STRICTLY BETWEEN endpoints in observation order; the full
walk is `src :: chain ++ [dst]` and every adjacent pair must be a `pointedB` edge. Decidable by
construction (a fold of per-edge Bool checks). -/
def chainOk (B : Lace) (src : Block) : List Block → Block → Bool
  | [],      dst => pointedB B src dst
  | m :: ms, dst => pointedB B src m && chainOk B m ms dst

/-- **`chainOk_sound` — a valid chain DENOTES `precedes`.** If `chainOk B src chain dst`,
then `precedes B src dst`: every checked edge is a `precedes.base` step, composed by `precedes.trans`
along the chain. The accept bit of the guard is therefore a genuine causal-inclusion fact, never a
free `True`. -/
theorem chainOk_sound (B : Lace) :
    ∀ (chain : List Block) (src dst : Block), chainOk B src chain dst = true → precedes B src dst
  | [],      src, dst, h => .base ((pointedB_iff B src dst).mp h)
  | m :: ms, src, dst, h => by
      simp only [chainOk, Bool.and_eq_true] at h
      exact .trans (.base ((pointedB_iff B src m).mp h.1)) (chainOk_sound B ms m dst h.2)

/-! ## 2. The `causallyAfter(E)` guard ATOM — a witnessed-predicate verifier plugin.

The atom is parameterised by the named PRIOR event `E` (the "commit", the "reveal-must-follow"
block). Its statement is the gate block being judged; its witness is the causal-inclusion chain.
The verifier ACCEPTS iff the witness is a real ack-chain from `E` to the gate — i.e. the gate
causally follows `E`. This is the exact `Predicate.Verifier` shape, so the atom installs into the
registry like any other kind and inherits `registry_sound` / `adversarial_find_cannot_forge`. -/

/-- The statement the `causallyAfter` atom judges: the gate block (the event seeking admission). -/
abbrev GateStmt := Block

/-- The witness the atom consumes: the causal-inclusion chain (intermediate blocks, in order). -/
abbrev ChainWit := List Block

/-- **`causallyAfterVerifier B E` — the installable `causally_after(E)` guard atom.** A
`Predicate.Verifier GateStmt ChainWit` whose accept bit is the causal-inclusion check: given the gate
block `gate` and a witness chain, ACCEPT iff `chainOk B E chain gate` — the chain is a genuine
ack-walk from the named prior event `E` up to the gate. The prover (who supplies the chain) is
untrusted; only this in-TCB check decides. -/
def causallyAfterVerifier (B : Lace) (E : Block) : Verifier GateStmt ChainWit :=
  fun gate chain => chainOk B E chain gate

/-- **`causallyAfter_denotes_precedes` — (a) the atom's denotation MATCHES `precedes`.**
Whenever the `causally_after(E)` verifier ACCEPTS a gate (with any witness chain), the gate causally
follows `E` in the happened-before order: `CausalAfter B E gate` (= `precedes B E gate`). The guard
atom's accept bit is precisely the `Time/Causal` causal-after relation — the modality is the same one
the proof layer reasons about, now installed as a runtime gate. -/
theorem causallyAfter_denotes_precedes (B : Lace) (E gate : Block) (chain : ChainWit)
    (h : causallyAfterVerifier B E gate chain = true) :
    CausalAfter B E gate := by
  rw [causalAfter_iff_precedes]
  exact chainOk_sound B chain E gate h

/-- **`causallyAfter_installs` — the atom is a genuine registry plugin.** Installing the
`causally_after(E)` verifier at a custom kind makes the registry dispatch it, and an accepted chain
discharges the predicate through `registry_sound` — soundness-by-verification, identical to every
other witnessed kind. So the causal modality is a first-class installable guard, not bespoke. -/
theorem causallyAfter_installs (base : Registry GateStmt ChainWit) (vk : Nat)
    (B : Lace) (E gate : Block) (chain : ChainWit)
    (haccept : causallyAfterVerifier B E gate chain = true) :
    let reg : Registry GateStmt ChainWit :=
      fun k => if k = .custom vk then some (causallyAfterVerifier B E) else base k
    @Dregg2.Laws.Discharged GateStmt ChainWit (verifiableOfRegistry reg (.custom vk)) gate chain := by
  intro reg
  apply registry_sound reg (.custom vk) gate chain
  show registryVerify reg (.custom vk) gate chain = true
  unfold registryVerify
  simp only [reg, if_pos rfl]
  exact haccept

/-- **`causallyAfter_adversarial_cannot_forge` — the gate is the sole authority.** No
prover, however the chain is synthesized, can make the atom accept a gate the in-TCB check rejects:
if `chainOk B E chain gate = false` (no valid causal walk), the dispatch rejects for every prover.
A gate that does not causally follow `E` cannot be admitted by supplying a bogus chain. -/
theorem causallyAfter_adversarial_cannot_forge (base : Registry GateStmt ChainWit) (vk : Nat)
    (B : Lace) (E gate : Block) (chain : ChainWit)
    (hreject : causallyAfterVerifier B E gate chain = false) :
    let reg : Registry GateStmt ChainWit :=
      fun k => if k = .custom vk then some (causallyAfterVerifier B E) else base k
    ∀ (find : GateStmt → Option ChainWit), find gate = some chain →
      registryVerify reg (.custom vk) gate chain = false := by
  intro reg find _hfound
  have hreg : reg (.custom vk) = some (causallyAfterVerifier B E) := by
    simp only [reg, if_pos rfl]
  exact adversarial_find_cannot_forge reg (.custom vk) (causallyAfterVerifier B E)
    hreg gate chain hreject find _hfound

/-! ## 3. The `monotoneOverForks(val)` guard ATOM — a value never decreases along causal extension.

The second causal modality: a per-block quantity `val : Block → Nat` is **monotone over forks** when
it never decreases along the happened-before order — `a ≺ b → val a ≤ val b`. This is the causal
analogue of a grow-only register: a sequence number, a high-water mark, a logical clock. The guard
atom denotes this property; the verifier gates ONE ack step, checking the value did not regress across
it (`val a ≤ val b` for the edge `a ← b`). The full monotonicity follows by induction on `precedes`. -/

/-- **`MonotoneOverForks B val`** — the denotation: `val` never decreases along the causal order. For
any two blocks with `a ≺ b` (`b` observes `a`), `val a ≤ val b`. A grow-only quantity over the
happened-before DAG. -/
def MonotoneOverForks (B : Lace) (val : Block → Nat) : Prop :=
  ∀ a b, precedes B a b → val a ≤ val b

/-- **`monotoneStepVerifier B val` — the installable per-edge `monotone_over_forks(val)` guard.**
A `Predicate.Verifier` over an ack-edge pair `(a, b)`: ACCEPT iff `b` directly acks `a` AND the value
did not regress (`val a ≤ val b`). Gating every ack edge with this atom enforces `MonotoneOverForks`
along the whole lace (`monotoneStep_implies_monotone`). The statement is the predecessor `a`; the
witness is the successor `b`. -/
def monotoneStepVerifier (B : Lace) (val : Block → Nat) : Verifier Block Block :=
  fun a b => pointedB B a b && decide (val a ≤ val b)

/-- **`monotoneStep_sound` — an accepted step is a real, non-regressing ack edge.** If the
guard accepts `(a, b)`, then `b` acks `a` (`precedes B a b`) AND `val a ≤ val b`. The accept bit is a
genuine local monotonicity fact on a genuine causal edge. -/
theorem monotoneStep_sound (B : Lace) (val : Block → Nat) (a b : Block)
    (h : monotoneStepVerifier B val a b = true) :
    precedes B a b ∧ val a ≤ val b := by
  unfold monotoneStepVerifier at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨.base ((pointedB_iff B a b).mp h.1), h.2⟩

/-- **`monotoneStep_implies_monotone` — (a) the per-edge atom DENOTES `MonotoneOverForks`.**
If EVERY direct ack edge in the lace passes the `monotone_over_forks(val)` guard (no edge lets `val`
regress), then `val` is monotone along the WHOLE happened-before order: `a ≺ b → val a ≤ val b`.
Proved by induction on `precedes` — base case is the gated edge, transitive case chains `≤`. The
guard atom's local check denotes the global causal-monotonicity modality. -/
theorem monotoneStep_implies_monotone (B : Lace) (val : Block → Nat)
    (hedges : ∀ a b, pointed B a b → val a ≤ val b) :
    MonotoneOverForks B val := by
  intro a b hab
  induction hab with
  | base h => exact hedges _ _ h
  | trans _ _ ihab ihbc => exact le_trans ihab ihbc

/-- **`monotone_preserved_on_extension` — monotone values keep their order on ANY causal
extension.** The MONOTONE-OVER-FORKS guarantee stated forward: given `MonotoneOverForks B val`, if a
later frontier `now'` causally observes an earlier event `E` (`E ≺ now'`), the value at `E` bounds the
value at `now'`. A monotone quantity, once advanced, stays advanced along every fork-extension — the
causal grow-only property the guard installs. -/
theorem monotone_preserved_on_extension (B : Lace) (val : Block → Nat)
    (hmono : MonotoneOverForks B val) {E now' : Block} (h : precedes B E now') :
    val E ≤ val now' :=
  hmono E now' h

/-! ## 4. NON-VACUITY — the concrete commit-reveal guarantee on the demo lace.

The TEETH the mission demands: a "reveal" gated by `causally_after(commit)` is REJECTED when the
reveal does NOT causally follow its commit, ACCEPTED when it does. We use `Blocklace.demoLace`:
treat genesis `g0` as the COMMIT and the honest successor `g1` as the REVEAL (`g1` acks `g0`, so the
reveal observed the commit); treat fork block `f1` as a commit and the concurrent `f2` as a would-be
reveal (`f2 ∥ f1`, so the reveal did NOT observe the commit). Both decided by the lace alone. -/

namespace CommitReveal

/-- The COMMIT event: genesis `g0`. -/
abbrev commit : Block := g0
/-- The honest REVEAL: `g1`, which acks the commit `g0` (so `commit ≺ reveal`). -/
abbrev honestReveal : Block := g1
/-- The honest causal-inclusion witness: the EMPTY intermediate chain — `g1` directly acks `g0`,
so the single base edge `g0 ← g1` is the whole walk. -/
def honestChain : ChainWit := []

/-- A concurrent commit `f1` and its would-be reveal `f2` (the rejected input: `f2 ∥ f1`). -/
abbrev forkCommit : Block := f1
abbrev forkReveal : Block := f2

-- The honest reveal directly acks the commit: the single-edge causal walk checks out.
#guard causallyAfterVerifier demoLace commit honestReveal honestChain        -- true (accepted)
-- The fork reveal does NOT ack the fork commit: the empty-chain walk fails (no direct edge).
#guard (causallyAfterVerifier demoLace forkCommit forkReveal [] == false)     -- true (rejected)

/-- **`commit_reveal_accepted` — the guarantee holds for an honest reveal.** The honest
reveal `g1` causally follows its commit `g0`, so the `causally_after(commit)` guard ADMITS it: the
accept bit holds, and its denotation is `CausalAfter demoLace commit honestReveal` (the reveal
observed the commit). The honest commit-reveal is admissible exactly because the causal edge exists. -/
theorem commit_reveal_accepted :
    causallyAfterVerifier demoLace commit honestReveal honestChain = true ∧
      CausalAfter demoLace commit honestReveal := by
  refine ⟨by decide, ?_⟩
  exact causallyAfter_denotes_precedes demoLace commit honestReveal honestChain (by decide)

/-- **`commit_reveal_rejected` — the rejected input: a reveal that did not follow its
commit.** The fork reveal `f2` is CONCURRENT with the fork commit `f1` (`f2 ∥ f1`), so it does NOT
causally follow it: `¬ CausalAfter demoLace forkCommit forkReveal`. Therefore NO causal-inclusion
witness can make the guard accept — for EVERY witness chain the verifier rejects. A reveal that never
observed its commit is structurally inadmissible, forced by the order, not adjudicated. -/
theorem commit_reveal_rejected :
    ¬ CausalAfter demoLace forkCommit forkReveal ∧
      ∀ chain : ChainWit, causallyAfterVerifier demoLace forkCommit forkReveal chain = false := by
  refine ⟨demo_causalAfter_fails.1, ?_⟩
  intro chain
  -- If the verifier accepted with ANY chain, the denotation would force the (false) causal-after.
  by_contra hne
  have hacc : causallyAfterVerifier demoLace forkCommit forkReveal chain = true := by
    cases hb : causallyAfterVerifier demoLace forkCommit forkReveal chain with
    | false => exact absurd hb hne
    | true  => rfl
  exact demo_causalAfter_fails.1
    (causallyAfter_denotes_precedes demoLace forkCommit forkReveal chain hacc)

/-- **`commit_reveal_unforgeable` — the rejected reveal cannot be admitted by any prover.**
Installed at a custom kind, the `causally_after(forkCommit)` guard rejects the concurrent reveal `f2`
for EVERY prover and EVERY witness chain it proposes: a reveal that did not causally follow its commit
has no admitting path through the in-TCB gate. The non-amplification statement for the causal guard —
the prover cannot manufacture a causal fact that the lace does not contain. -/
theorem commit_reveal_unforgeable (base : Registry GateStmt ChainWit) (vk : Nat)
    (chain : ChainWit) :
    let reg : Registry GateStmt ChainWit :=
      fun k => if k = .custom vk then some (causallyAfterVerifier demoLace forkCommit) else base k
    ∀ (find : GateStmt → Option ChainWit), find forkReveal = some chain →
      registryVerify reg (.custom vk) forkReveal chain = false := by
  intro reg find hfound
  exact causallyAfter_adversarial_cannot_forge base vk demoLace forkCommit forkReveal chain
    ((commit_reveal_rejected.2 chain)) find hfound

end CommitReveal

/-! ## 5. The I-CONFLUENCE boundary — WHICH guard atoms keep coordination-freedom.

`Confluence.IConfluent` is the third judgement (BEC Thm 3.1): an invariant runs tier-1 (causal-only,
coordination-free, partition-tolerant) IFF concurrent invariant-preserving merges stay safe. The two
atoms sit on OPPOSITE sides of that boundary, and the distinction is load-bearing:

  * **`monotoneOverForks(val)` KEEPS coordination-freedom.** Its content — "`val` never decreases
    along causal extension" — is a grow-only / join-semilattice property: the merge of two monotone
    branches is their pointwise max, which is still ≥ each, so monotonicity is preserved under `⊔`.
    A `monotone_over_forks` guard is I-confluent (the `top`/grow-only witness in `Confluence.lean`),
    so a cell gated only by it stays TIER-1 — no atomic commit, partition-tolerant.

  * **`causallyAfter(E)` is a CAUSAL gate, not an invariant — coordination-freedom depends on the
    GATED step.** `causally_after(E)` is precisely a happens-before constraint: it is satisfied
    *causally* (the order itself carries it, `Time/Causal` proves it needs no authority). So a step
    that ONLY requires "follow `E`" is tier-1-eligible — the causal layer enforces it for free without
    consensus. It forfeits coordination-freedom only when COMPOSED with a non-I-confluent invariant
    on the gated write (e.g. a bounded-resource `card ≤ 1` settlement), which is the invariant's
    fault, not the causal guard's. The causal modality is the coordination-free fragment's NATIVE
    deadline (the §4/§5 anti-frontrunning point: a causal type, never a global-order race).

We make the monotone side load-bearing as a theorem: a monotone-over-forks value's preservation
invariant is I-confluent, hence tier-1-eligible. -/

/-- A `Nat` high-water mark is a join-semilattice under `⊔ = max` (the grow-only join), so it is a
`Confluence.MergeState` — concurrent marks merge by `max`. -/
instance : Dregg2.Confluence.MergeState Nat := { toSemilatticeSup := inferInstance }

/-- A `Nat` high-water mark merges by `max` — the grow-only join. We expose the monotone-value
invariant "the mark is ≥ a floor `c`" as the I-confluence witness: it is preserved by `⊔ = max`, so
a `monotone_over_forks`-guarded mark runs coordination-free. -/
def aboveFloor (c : Nat) : Dregg2.Confluence.Invariant Nat := fun v => c ≤ v

/-- **`monotone_guard_is_iconfluent` — `monotoneOverForks` KEEPS coordination-freedom.** The
grow-only "high-water mark ≥ floor `c`" invariant — the invariant a `monotone_over_forks(val)` guard
maintains — is `Confluence.IConfluent` over the `max`-merge lattice: two branches each above the floor
merge (by `max`) to a value still above it. So a cell gated ONLY by a monotone-over-forks atom is
tier-1-eligible (`Confluence.Tier1Eligible`): coordination-free, partition-tolerant, no atomic commit.
This is the I-confluence side the causal-monotone guard lands on. -/
theorem monotone_guard_is_iconfluent (c : Nat) :
    Dregg2.Confluence.IConfluent (S := Nat) (aboveFloor c) := by
  intro x y hx hy
  -- merge is `⊔ = max`; `c ≤ x ≤ x ⊔ y`.
  unfold aboveFloor at *
  exact le_trans hx le_sup_left

/-- **`bounded_resource_not_iconfluent` — the CONTRAST: a coupled gated write is NOT
coordination-free.** When the gated write carries a bounded-resource invariant (`card ≤ 1`, the
`balance ≥ 0` shape), it is NOT I-confluent (`Confluence.cardLeOne_not_iconfluent`): two concurrent
in-bound branches merge to an over-the-bound state. A `causally_after(E)` guard composed with such an
invariant forfeits tier-1 — but the fault is the bounded invariant's, NOT the causal guard's. This
pins down WHICH atom keeps coordination-freedom: the monotone one always does; the causal-after one
does iff the gated invariant is itself I-confluent. -/
theorem bounded_resource_not_iconfluent :
    ¬ Dregg2.Confluence.IConfluent (S := Finset ℕ) (fun s => s.card ≤ 1) :=
  Dregg2.Confluence.cardLeOne_not_iconfluent

/-! ### `#guard` smoke — the guard atoms decide by the lace / lattice alone (no clock, no consensus). -/

-- causally_after(commit): the honest reveal's direct ack edge passes (single base step).
#guard pointedB demoLace g0 g1                                          -- true (g1 acks g0)
-- causally_after(commit): the concurrent fork reveal has no direct edge — the guard rejects.
#guard (pointedB demoLace f1 f2 == false)                              -- true (rejected)
-- monotone_over_forks: a step that does not regress the value is accepted.
#guard (monotoneStepVerifier demoLace (fun b => b.seq) g0 g1)          -- true (seq 0 ≤ 1)

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms chainOk_sound
#assert_axioms causallyAfter_denotes_precedes
#assert_axioms causallyAfter_installs
#assert_axioms causallyAfter_adversarial_cannot_forge
#assert_axioms monotoneStep_sound
#assert_axioms monotoneStep_implies_monotone
#assert_axioms monotone_preserved_on_extension
#assert_axioms CommitReveal.commit_reveal_accepted
#assert_axioms CommitReveal.commit_reveal_rejected
#assert_axioms CommitReveal.commit_reveal_unforgeable
#assert_axioms monotone_guard_is_iconfluent
#assert_axioms bounded_resource_not_iconfluent

end Dregg2.Authority.CausalGuard
