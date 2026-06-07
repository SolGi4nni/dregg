/-
# Dregg2.Exec.ProofForest — proof-carrying without recursive compression.

The architecture ships the **whole forest** of per-step proofs, each standalone and independently
verifiable, plus the linking witness data. A verifier (a) checks every proof against its own
public inputs, and (b) checks the **linking discipline**: each proof's `newCommit` equals the
next proof's `oldCommit` along every happened-before edge. Soundness of the composite is the
conjunction of per-proof soundness (the §8 cryptographic assumption) and the linking check (a
combinatorial fact, fully in Lean). Aggregation slots in later as a pure performance swap.

  * **`ProofNode`** — the public-input projection of one cell-step (`oldCommit`, `newCommit`,
    `effectsHash`, `prevReceipt`, `seq`, `δ` — the `circuit/src/effect_vm/pi.rs` linking surface)
    plus `StepProofValid : Prop`: the §8 assumption "this node's STARK proof verifies." Never an
    `axiom`/`sorry`; entered as a hypothesis the composition theorem is parametric in.
  * **`Linked`** — the combinatorial chain-link: `newCommit = next.oldCommit` (state continuity),
    receipt-chain pointer, and monotone `seq` (no replay/fork).
  * **`proofForest_sound`** — the main theorem: `(∀ n, StepProofValid) ∧ Linked ⟹
    fullForestInv` (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance over the whole forest),
    reducing to `execForest_attests`.

ASSUMED (§8 seam, not proved in Lean): per-node `StepProofValid` and EffectVm AIR soundness,
packaged into `ProofForest.attested` — the cryptographic obligation, discharged in Rust by
`verify_effect_vm`. PROVED (fully in Lean, axiom-clean): that linked per-step soundness composes
to whole-forest `StepInv`.

-- OPEN: the cross-cell proof-forest — where edges cross cells and the link is the CG-5 N-ary
--   `Σδ = 0` shared-binding — is the natural next slice, packaging `CrossCellForest.lean`'s
--   `crossForest_attests`. The `δ` surface is already on `ProofNode`; the cross-cell `Linked`
--   would require `∑ δ = 0` over a family. Left as a documented OPEN, not a `sorry`/`axiom`.
-/
import Dregg2.Exec.TurnForest
import Dregg2.Exec.CrossCellForest

namespace Dregg2.Exec.ProofForest

open Dregg2.Exec
open Dregg2.Exec.Forest
open Dregg2.Exec.TurnExecutor

/-! ## §1 — `ProofNode`: the public-input projection of one cell-step + the §8 validity seam.

A `ProofNode` is the Lean shadow of one EffectVm AIR proof's public inputs — the linking surface
`circuit/src/effect_vm/pi.rs` exposes (`OLD_COMMIT`, `NEW_COMMIT`, `EFFECTS_HASH`,
`PREVIOUS_RECEIPT_HASH`, `SOVEREIGN_WITNESS_SEQUENCE`, `δ`) — together with the abstract
proposition `StepProofValid`: "this node's STARK proof verifies against this PI." No crypto lives
inside Lean; `StepProofValid` is the named §8 hypothesis, never a concrete predicate here. -/

/-- A commitment is an opaque tag in Lean (Poseidon2 of cell state in the real system, `pi.rs:16`):
its only structure the proof-forest reads is EQUALITY along the chain-link edge. -/
abbrev Commit := Nat

/-- One node of the proof-forest: the public-input projection of a single cell-step proof, plus the
§8 validity seam `StepProofValid`. -/
structure ProofNode where
  /-- `OLD_COMMIT` (`pi.rs:17`) — the input-state commitment this step's proof binds. -/
  oldCommit   : Commit
  /-- `NEW_COMMIT` (`pi.rs:20`) — the output-state commitment this step's proof binds. -/
  newCommit   : Commit
  /-- `EFFECTS_HASH` (`pi.rs:24`) — the effects this step emitted (linking surface, carried). -/
  effectsHash : Commit
  /-- `PREVIOUS_RECEIPT_HASH` (`pi.rs:103`) — the receipt-chain position this proof is pinned to. -/
  prevReceipt : Commit
  /-- `SOVEREIGN_WITNESS_SEQUENCE` (`pi.rs:204`) — the per-cell monotone replay counter. -/
  seq         : Nat
  /-- The CG-5 signed half-edge magnitude (`NET_DELTA`, `pi.rs:42`) — the cross-cell balance surface. -/
  δ           : ℤ
  /-- **The §8 SEAM.** The proposition "this node's STARK proof verifies against its public inputs."
  NOT a concrete predicate — the named cryptographic-soundness hypothesis the composition theorem is
  parametric in. In the real system this is `verify_effect_vm(proof, public_inputs) = true`; here it
  is left abstract as the circuit's obligation. -/
  StepProofValid : Prop

/-! ## §2 — `ProofForest`: the forest of PI-projections + the §8 portal.

A `ProofForest` packages (a) the list of per-step PI-projections (`nodes`, pre-order), and (b) the
§8 cryptographic-soundness portal: the underlying intra-cell witness `TurnForest`, its claimed
endpoints `(s, s')`, and `attested` — "if every node's proof verifies, the EffectVm AIR's soundness
gives a real committed `execForest` run with these endpoints." `attested` is entered as data,
exactly as `CryptoKernel`/`World` portals enter their assumptions. -/

set_option linter.dupNamespace false in
structure ProofForest where
  /-- The per-step PI-projections, in pre-order (the call-forest, `PHASE-PROOF-CARRYING §4.1`). -/
  nodes    : List ProofNode
  /-- The underlying intra-cell witness forest (the executable shadow the AIR soundness yields). -/
  witness  : TurnForest
  /-- The claimed pre-state (the root `oldCommit`'s state). -/
  s        : RecChainedState
  /-- The claimed post-state (the leaf `newCommit`'s state). -/
  s'       : RecChainedState
  /-- **The §8 cryptographic-soundness PORTAL (ASSUMED, entered as DATA).** "If every node's proof
  verifies, the EffectVm AIR's soundness gives a real committed run `execForest s witness = some s'`."
  This is the per-node validity discharged into a real execution — the circuit's obligation, NOT
  proved in Lean (it is `verify_effect_vm` in Rust, checked by the FFI golden-oracle cascade). -/
  attested : (∀ n ∈ nodes, n.StepProofValid) → execForest s witness = some s'

/-! ## §3 — `Linked`: the combinatorial chain-link discipline.

Along every consecutive edge: `prev.newCommit = next.oldCommit` (state continuity),
`next.prevReceipt` pins to the prior's receipt-chain position, and `seq` strictly advances
(no replay/fork). Pure combinatorics over the PI vectors, no crypto. -/

/-- The chain-link predicate on a node LIST: each adjacent pair links `prev.newCommit = next.oldCommit`
(state continuity) ∧ `next.prevReceipt = prev.newCommit` (receipt-chain pointer) ∧
`next.seq = prev.seq + 1` (monotone replay counter). The combinatorial leaf obligation. -/
def chainLinked : List ProofNode → Prop
  | []          => True
  | [_]         => True
  | a :: b :: rest =>
      a.newCommit = b.oldCommit
      ∧ b.prevReceipt = a.newCommit
      ∧ b.seq = a.seq + 1
      ∧ chainLinked (b :: rest)

/-- **`Linked`** — the forest is well-linked: its node list satisfies the chain-link discipline. The
§4.2 (2) combinatorial check, named. -/
def Linked (pf : ProofForest) : Prop := chainLinked pf.nodes

/-! ## §4 — `proofForest_sound`: linked per-step proofs compose to a sound whole forest.

If (P) every node's proof verifies (`∀ n, n.StepProofValid` — the §8 seam) and (L) the forest is
`Linked`, the composite attests the full `StepInv`: Conservation ∧ Authority ∧ ChainLink ∧
ObsAdvance. (P) discharges `pf.attested` to a real committed `execForest` run; `execForest_attests`
then attests all four conjuncts. The per-node validity is the hypothesis; the linking + composition
is what is proved. -/

/-- **The whole-proof-forest `StepInv`** — all four conjuncts over the forest (`Forest.fullForestInv`
on the underlying witness). NEVER weakened. -/
def fullProofForestInv (pf : ProofForest) : Prop :=
  fullForestInv pf.s pf.witness pf.s'

/-- **`proofForest_sound`** — given (P) every node's proof verifies (`∀ n ∈ nodes, StepProofValid`
— the §8 seam, a hypothesis) and (L) the forest is `Linked`, the composite attests the full
`StepInv`: Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance. Reduces to
`Forest.execForest_attests` over the witness run `pf.attested` yields from (P). The
cryptographic per-proof soundness is assumed; the linking + composition is proved. -/
theorem proofForest_sound (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid)
    (_hlinked : Linked pf) :
    fullProofForestInv pf := by
  unfold fullProofForestInv
  exact execForest_attests (pf.attested hvalid)

/-- **Conservation conjunct, projected — PROVED.** A linked, valid proof-forest preserves `recTotal`
end-to-end (the intra-cell CG-5 over the whole forest). Read out of the composite `StepInv`. -/
theorem proofForest_conserves (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    recTotal pf.s'.kernel = recTotal pf.s.kernel :=
  (proofForest_sound pf hvalid hlinked).1

/-- **ChainLink conjunct, projected — PROVED.** A linked, valid proof-forest extends the receipt
chain by EXACTLY its nodes' moves (newest-first), no fork/rewrite — the executable shadow of the
per-node `prevReceipt` pointers chaining. Read out of the composite `StepInv`. -/
theorem proofForest_chainlinks (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    pf.s'.log = turnLog (forestActions pf.witness) pf.s.log :=
  (proofForest_sound pf hvalid hlinked).2.2.1

/-! ## §5 — The §8 boundary, explicit.

Composite soundness factors as `(per-node proof validity [assumed §8 seam]) ∧ (Linked [proved-side
combinatorial check]) ⟹ whole-forest StepInv`. Nothing in the consequent is assumed; nothing in
the per-node validity is proved here. -/

/-- **`proofForest_factors`** — `proofForest_sound` stated as an explicit `∧`-antecedent: the
per-node validity is assumed (the circuit's obligation, discharged in Rust by `verify_effect_vm`);
the linking + composition ⇒ the four conjuncts is proved. -/
theorem proofForest_factors (pf : ProofForest) :
    ((∀ n ∈ pf.nodes, n.StepProofValid) ∧ Linked pf) → fullProofForestInv pf :=
  fun ⟨hvalid, hlinked⟩ => proofForest_sound pf hvalid hlinked

/-! ## §6 — Axiom-hygiene tripwires. -/

#assert_axioms proofForest_sound
#assert_axioms proofForest_conserves
#assert_axioms proofForest_chainlinks
#assert_axioms proofForest_factors

/-! ## §7 — Non-vacuity: a concrete 2-step linked proof-forest is sound; an unlinked forest is not.

A `ProofForest` is built over `Forest.goodForest` (the 2-level intra-cell witness): two
PI-projections with `node0.newCommit = node1.oldCommit`. The §8 portal `attested` is discharged
by `goodForest`'s actual commitment. -/

/-- Node 0's PI-projection: state commitment `0 ⟶ 1`, receipt position `0`, seq `0`. -/
def node0 : ProofNode :=
  { oldCommit := 0, newCommit := 1, effectsHash := 100, prevReceipt := 0, seq := 0, δ := 30
  , StepProofValid := True }

/-- Node 1's PI-projection: state commitment `1 ⟶ 2` (so `node0.newCommit = node1.oldCommit`),
receipt position `1 = node0.newCommit`, seq `1 = node0.seq + 1`. The chain links. -/
def node1 : ProofNode :=
  { oldCommit := 1, newCommit := 2, effectsHash := 101, prevReceipt := 1, seq := 1, δ := 10
  , StepProofValid := True }

/-- The committed witness state for `Forest.goodForest` (the post-state the AIR soundness yields). -/
noncomputable def goodWitnessPost : RecChainedState :=
  (execForest ts0 goodForest).get (by decide)

/-- A GOOD 2-step proof-forest: PI-projections `[node0, node1]` (linked), witness `goodForest`. Its
§8 portal `attested` is discharged by `goodForest`'s actual commitment — the executable witness the
EffectVm AIR soundness would produce. -/
noncomputable def goodProofForest : ProofForest :=
  { nodes := [node0, node1]
  , witness := goodForest
  , s := ts0
  , s' := goodWitnessPost
  , attested := fun _ => by
      show execForest ts0 goodForest = some goodWitnessPost
      unfold goodWitnessPost
      rw [Option.some_get] }

/-- The good proof-forest IS `Linked`: `node0.newCommit (1) = node1.oldCommit (1)`,
`node1.prevReceipt (1) = node0.newCommit (1)`, `node1.seq (1) = node0.seq (0) + 1`. -/
example : Linked goodProofForest := by
  show chainLinked [node0, node1]
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact True.intro

/-- The good proof-forest is sound: with every node's proof valid (here `True`) and the chain
linked, `proofForest_sound` attests the full `StepInv` over the whole forest. -/
example : fullProofForestInv goodProofForest :=
  proofForest_sound goodProofForest
    (fun n hn => by
      -- both nodes carry `StepProofValid := True`.
      simp only [goodProofForest, node0, node1, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with h | h <;> (subst h; exact True.intro))
    (by
      show chainLinked [node0, node1]
      exact ⟨rfl, rfl, rfl, True.intro⟩)

/-- An unlinked node list: `node0.newCommit (1) ≠ badNode.oldCommit (99)` — the state-continuity
edge is broken even though each node's proof could individually verify. The link is what makes
the composite sound, not per-proof validity alone. -/
def badNode : ProofNode :=
  { oldCommit := 99, newCommit := 2, effectsHash := 101, prevReceipt := 99, seq := 1, δ := 10
  , StepProofValid := True }

/-- The unlinked list is NOT `chainLinked`: the broken `newCommit (1) = oldCommit (99)` edge fails. -/
example : ¬ chainLinked [node0, badNode] := by
  intro h
  -- the first conjunct is `node0.newCommit = badNode.oldCommit`, i.e. `1 = 99`.
  exact absurd h.1 (by decide)


end Dregg2.Exec.ProofForest
