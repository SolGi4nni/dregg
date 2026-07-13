/-
# Dregg2.Circuit.AggAirSound — the AGGREGATION AIR soundness, PROVEN per node, FRI-floor only.

**What this shrinks.** `RecursiveAggregation.EngineSound.recursive_sound`
(`RecursiveAggregation.lean:125`) is the ONE black-box recursion carrier: "the root aggregate
verifies ⟹ every wrapped child leaf verifies". §9 of `RecursiveAggregation` already refines that to a
PER-NODE local floor — `SegSound (.node c l r)` ASSUMES `Accepts node → Accepts l ∧ Accepts r ∧
CombineOk H (exposedSeg l) (exposedSeg r) c` as the LAYER-1 crypto carrier. That per-node implication
is STILL a black box: it bundles "the children verify" AND "the segment-combine is correct" into one
assumed fact.

This file OPENS that box. It models the actual aggregation AIR — the `segment_combine_expose` hook
(`circuit-prove/src/ivc_turn_chain.rs:2713`) that BOTH the serial `aggregate_tree` and the parallel
`merge_two_segment_proofs` drive — at the per-node level: the state-continuity `connect`
(`L.last_new8 == R.first_old8`), the count-additivity `add` (`count = L.count + R.count`), the
ordered multi-felt Poseidon2 digest fold (`acc = commit(L.acc ++ R.acc)`, L before R), the parent
span expose `[L.first_old, R.last_new, …]`, AND the per-child in-circuit recursion-verifier subcircuit
that pins each child's preprocessed commitment (its VK core, `batch_to_pinned_input` lever (a)) and
checks the child proof. It then proves:

  * **`agg_air_sound` (THE DISCHARGE).** A SATISFYING aggregation-node trace — gates satisfied, both
    child-verifier subcircuits satisfied at their pinned commitments exposing the children's segments —
    FORCES (a) each pinned child PI is the published commitment of a genuinely VERIFYING child proof,
    and (b) `CombineOk H L R P` (continuity + count + ordered digest). Part (b) is proven from the
    arithmetic gates with NO crypto. Part (a) reduces to a single NAMED, localized floor `FriExtract` —
    the in-circuit recursion-verifier subcircuit's soundness, the standard SNARK-of-a-fixed-verifier
    obligation `RecursiveAggregation` §2 already names — NOT a new dregg axiom.

So `recursive_sound` / the §9 per-node LAYER-1 carrier decomposes into:
  {`FriExtract`: the pinned child verifier subcircuit, satisfied, yields a verifying child}
  ⊕ {the segment-combine gate constraints, PROVEN to force `CombineOk`}.
The black box shrinks to exactly the irreducible recursion-verifier crypto floor; the combine math
moves from assumed to proven.

  * **`combine_digest_binds` (THE CR TOOTH).** Under `Poseidon2SpongeCR` (the one named hash floor,
    never an axiom), two satisfying nodes that expose the SAME parent digest were folded from children
    with the SAME ordered `(L.acc, R.acc)` — a same-endpoint reorder of the children is rejected by the
    ordered digest. This is the only result resting on the hash floor, and it rests on it alone.

Anti-ghost, witnessed BOTH ways: an honest node satisfies the segment-combine gates
(`honest_satCombine`, `honest_parent_count_is_two`); a tampered combine — broken continuity, swapped
child, wrong count, or wrong digest — does NOT satisfy the gates (`broken_continuity_unsat`,
`swapped_child_unsat`, `wrong_count_unsat`, `wrong_digest_unsat`). So the gate constraints are both
satisfiable and falsifiable; the discharge is non-vacuous.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); `FriExtract` and
`Poseidon2SpongeCR` are Prop HYPOTHESES where used, never `axiom`s. New module; not wired into
`Dregg2.lean` here.
-/
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.AggAirSound

open Dregg2.Circuit.RecursiveAggregation (Seg combineSeg CombineOk combineOk_eq)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

/-! ## 1. The ordered digest combiner the segment AIR's gate computes.

`segment_combine_expose` builds the parent `acc` as `seg_poseidon_commit(L.acc ++ R.acc)` — the
ordered multi-felt Poseidon2 sponge over the two children's digests (L absorbed before R, hence
order-sensitive). We model the multi-lane digest as a single field over a list-sponge `sponge`, so the
ordered combiner at a node is `Hsponge sponge L.acc R.acc = sponge [L.acc, R.acc]`. This is the exact
binary specialization of the sponge whose collision-resistance is `Poseidon2SpongeCR`. -/

/-- The node's ordered digest combiner: `sponge [L.acc, R.acc]`, L before R. -/
def Hsponge (sponge : List ℤ → ℤ) (a b : ℤ) : ℤ := sponge [a, b]

/-! ## 2. The per-node aggregation trace + its gate-satisfaction predicate.

A `CombineTrace` is one `segment_combine_expose` node: the two children's exposed segments `L`, `R`
(their PI projections, pinned), the parent's exposed segment `P`, and the two pinned preprocessed
commitments `lCommit`/`rCommit` (each child's VK-identity core, `batch_to_pinned_input` lever (a)). -/
structure CombineTrace where
  /-- Left child's exposed segment (its `air_public_targets` PI projection). -/
  L       : Seg
  /-- Right child's exposed segment. -/
  R       : Seg
  /-- The parent segment the node exposes (`expose_as_public_output`). -/
  P       : Seg
  /-- The pinned preprocessed commitment (VK core) of the left child. -/
  lCommit : ℤ
  /-- The pinned preprocessed commitment (VK core) of the right child. -/
  rCommit : ℤ

/-- **`SatCombine sponge t`** — the segment-combine GATE constraints of `segment_combine_expose`, as a
denotational predicate over the node's exposed columns. Each field is one gate:
  * `continuity` — the state-continuity `connect` (`L.last_new8 == R.first_old8`, the temporal tooth);
  * `firstOld`/`lastNew` — the parent-span expose (`parent.first = L.first`, `parent.last = R.last`);
  * `count` — the count-additivity `add` (`parent.count = L.count + R.count`);
  * `digest` — the ordered Poseidon2 digest fold (`parent.acc = sponge [L.acc, R.acc]`).
STRICTLY LOCAL — it speaks only of the node and its two immediate children. -/
structure SatCombine (sponge : List ℤ → ℤ) (t : CombineTrace) : Prop where
  continuity : t.L.lastNew = t.R.firstOld
  firstOld   : t.P.firstOld = t.L.firstOld
  lastNew    : t.P.lastNew = t.R.lastNew
  count      : t.P.count = t.L.count + t.R.count
  digest     : t.P.acc = Hsponge sponge t.L.acc t.R.acc

/-- **`satCombine_combineOk` (part (b) — the combine is correct, PROVEN, no crypto).** A satisfying
segment-combine trace FORCES `RecursiveAggregation.CombineOk` over `Hsponge sponge`: the parent's
endpoints/count/digest are the genuine fold of the children's, plus the seam-continuity. This is a pure
reading of the arithmetic gates — it needs NO cryptographic assumption. -/
theorem satCombine_combineOk {sponge : List ℤ → ℤ} {t : CombineTrace}
    (h : SatCombine sponge t) :
    CombineOk (Hsponge sponge) t.L t.R t.P :=
  ⟨h.firstOld, h.lastNew, h.count, h.digest, h.continuity⟩

/-- The parent of a satisfying node IS the genuine `combineSeg` of the children (reusing
`RecursiveAggregation.combineOk_eq`) — the object §9's `subtree_binding` consumes. So a verified node's
exposed parent segment is provably the ordered concatenation, not a free claim. -/
theorem parent_is_genuine_combine {sponge : List ℤ → ℤ} {t : CombineTrace}
    (h : SatCombine sponge t) :
    t.P = combineSeg (Hsponge sponge) t.L t.R ∧ t.L.lastNew = t.R.firstOld :=
  combineOk_eq (Hsponge sponge) (satCombine_combineOk h)

/-! ## 3. The pinned child-verifier subcircuit + the NAMED FRI-extraction floor.

`merge_two_segment_proofs` embeds, per child, a recursion-verifier subcircuit (`batch_to_pinned_input`
threads the child's per-table public values, lever (b)) and PINS the child's preprocessed commitment
in-circuit (lever (a)). A `Proof` is an abstract child STARK/recursion proof; `verify` is its native
verifier; `vkCommit p` is its preprocessed-commitment VK core; `exposedPI p` is the segment it exposes.
`ChildVerifierSat c s` is the satisfaction of the in-circuit child-verifier columns PINNED at
commitment `c` and claiming exposed segment `s`. -/

section Floor

variable (Proof : Type)
variable (verify : Proof → Bool)
variable (vkCommit : Proof → ℤ)
variable (exposedPI : Proof → Seg)

/-- **`FriExtract ChildVerifierSat`** — the SINGLE named, localized crypto floor: a SATISFIED in-circuit
child-verifier subcircuit (pinned at commitment `c`, claiming exposed segment `s`) yields a GENUINE
child proof `p` that verifies, whose VK core IS the pinned `c`, and whose exposed segment IS the claimed
`s`. This is the standard "SNARK of a fixed verifier circuit is sound" obligation
(`RecursiveAggregation.RecursiveVerifierSound`, §H1), localized to ONE child of ONE node — NOT a new
dregg axiom, the same FRI-extraction carrier the engine already names. Realizable; a Prop hypothesis,
never an `axiom`. -/
def FriExtract (ChildVerifierSat : ℤ → Seg → Prop) : Prop :=
  ∀ c s, ChildVerifierSat c s → ∃ p, verify p = true ∧ vkCommit p = c ∧ exposedPI p = s

/-- **`SatNode sponge ChildVerifierSat t`** — a fully satisfying aggregation node: the segment-combine
gates hold AND both pinned child-verifier subcircuits are satisfied (left at `lCommit` exposing `L`,
right at `rCommit` exposing `R`). This is what a verifying aggregation proof's in-circuit trace IS. -/
structure SatNode (sponge : List ℤ → ℤ) (ChildVerifierSat : ℤ → Seg → Prop)
    (t : CombineTrace) : Prop where
  combine : SatCombine sponge t
  leftCV  : ChildVerifierSat t.lCommit t.L
  rightCV : ChildVerifierSat t.rCommit t.R

/-- **`ChildAccepts s`** — a child proof that VERIFIES and exposes segment `s`. This is the concrete
realization of `RecursiveAggregation`'s abstract `Accepts`: a verifying recursion child. -/
def ChildAccepts (s : Seg) : Prop := ∃ p, verify p = true ∧ exposedPI p = s

/-- **`agg_air_sound` (THE DISCHARGE — the per-node `recursive_sound`/LAYER-1 carrier, OPENED).**

A satisfying aggregation-node trace, under the named `FriExtract` floor, FORCES:
  (a) each pinned child PI is the published commitment of a genuinely VERIFYING child proof exposing
      that child's segment — `∃ p, verify p ∧ vkCommit p = pin ∧ exposedPI p = childSeg`, for both
      children; and
  (b) `CombineOk (Hsponge sponge) L R P` — the segment combine is correct (continuity + count + ordered
      digest), PROVEN from the arithmetic gates with no crypto.

This is exactly the §9 per-node LAYER-1 obligation `Accepts node → Accepts l ∧ Accepts r ∧ CombineOk`,
no longer ASSUMED: the "children verify" half reduces to the single localized `FriExtract` floor; the
"combine is correct" half is proven. The recursion black box shrinks to the standard in-circuit
verifier soundness carrier. -/
theorem agg_air_sound
    {sponge : List ℤ → ℤ} {ChildVerifierSat : ℤ → Seg → Prop} {t : CombineTrace}
    (hfri : FriExtract Proof verify vkCommit exposedPI ChildVerifierSat)
    (hsat : SatNode sponge ChildVerifierSat t) :
    (∃ pl, verify pl = true ∧ vkCommit pl = t.lCommit ∧ exposedPI pl = t.L)
      ∧ (∃ pr, verify pr = true ∧ vkCommit pr = t.rCommit ∧ exposedPI pr = t.R)
      ∧ CombineOk (Hsponge sponge) t.L t.R t.P := by
  refine ⟨hfri t.lCommit t.L hsat.leftCV, hfri t.rCommit t.R hsat.rightCV, ?_⟩
  exact satCombine_combineOk hsat.combine

/-- **`segsound_node_discharged`** — the discharge, packaged in `RecursiveAggregation.SegSound`'s
node-body shape: both children ACCEPT (a verifying child exposes each child segment) AND
`CombineOk` holds. Where §9 took this implication as the assumed LAYER-1 per-node carrier, it is here
PRODUCED from gate satisfaction + the `FriExtract` floor — the abstract `Accepts` instantiated to a
genuinely verifying recursion child. -/
theorem segsound_node_discharged
    {sponge : List ℤ → ℤ} {ChildVerifierSat : ℤ → Seg → Prop} {t : CombineTrace}
    (hfri : FriExtract Proof verify vkCommit exposedPI ChildVerifierSat)
    (hsat : SatNode sponge ChildVerifierSat t) :
    ChildAccepts Proof verify exposedPI t.L
      ∧ ChildAccepts Proof verify exposedPI t.R
      ∧ CombineOk (Hsponge sponge) t.L t.R t.P := by
  obtain ⟨⟨pl, hvl, _, hel⟩, ⟨pr, hvr, _, her⟩, hcomb⟩ :=
    agg_air_sound Proof verify vkCommit exposedPI hfri hsat
  exact ⟨⟨pl, hvl, hel⟩, ⟨pr, hvr, her⟩, hcomb⟩

end Floor

/-! ## 4. THE CR TOOTH — the ordered digest binds the children (rests on `Poseidon2SpongeCR`). -/

/-- **`combine_digest_binds` (THE CR ANTI-REORDER TOOTH).** Two satisfying nodes (same sponge) that
expose the SAME parent digest `P.acc` were folded from children with the SAME ordered child digests:
`L.acc = L'.acc ∧ R.acc = R'.acc`. So a same-endpoint reorder/swap of the two children (different
`(L.acc, R.acc)`) yields a DIFFERENT parent digest and is rejected. The only crypto reliance is the
named `Poseidon2SpongeCR` floor — the ordered digest fold `sponge [L.acc, R.acc]` is order-sensitive
(L before R), so this also rejects a left/right swap. -/
theorem combine_digest_binds
    {sponge : List ℤ → ℤ} (hCR : Poseidon2SpongeCR sponge)
    {t t' : CombineTrace} (h : SatCombine sponge t) (h' : SatCombine sponge t')
    (hdig : t.P.acc = t'.P.acc) :
    t.L.acc = t'.L.acc ∧ t.R.acc = t'.R.acc := by
  have e : sponge [t.L.acc, t.R.acc] = sponge [t'.L.acc, t'.R.acc] := by
    have hl := h.digest; have hr := h'.digest
    simp only [Hsponge] at hl hr
    rw [← hl, ← hr, hdig]
  have hlist := hCR _ _ e
  -- `[a, b] = [a', b']` ⇒ `a = a' ∧ b = b'`.
  injection hlist with hacc htail
  injection htail with hr _
  exact ⟨hacc, hr⟩

/-! ## 5. NON-VACUITY — the discharge FIRES on an honest node, and tampered combines are REJECTED.

The discharge would be hollow if no node satisfied the gates, or if the gates accepted a tampered
combine. We exhibit BOTH: an honest node `[1→2] ⋆ [2→3]` that satisfies and on which `agg_air_sound`
fires (a true `CombineOk` + two verifying children), and four tampered nodes — broken continuity,
swapped child, wrong count, wrong digest — none of which satisfy. -/

section Vacuity

/-- A concrete sponge for the witness (constant-zero — the realizing instance only needs the gate
shape to typecheck; the CR floor is not invoked here). -/
def zSponge : List ℤ → ℤ := fun _ => 0

/-- The honest node: left segment `1 → 2` (count 1), right `2 → 3` (count 1), parent the genuine
`combineSeg` (`1 → 3`, count 2). Continuity holds: `L.lastNew = 2 = R.firstOld`. -/
def honestL : Seg := { firstOld := 1, lastNew := 2, count := 1, acc := 0 }
def honestR : Seg := { firstOld := 2, lastNew := 3, count := 1, acc := 0 }
def honestNode : CombineTrace :=
  { L := honestL, R := honestR
  , P := combineSeg (Hsponge zSponge) honestL honestR
  , lCommit := 10, rCommit := 20 }

/-- **`honest_satCombine` (positive non-vacuity).** The honest node satisfies the segment-combine
gates — the continuity tooth `2 = 2` holds and the parent is the genuine fold. So `SatCombine` is
inhabited with a nontrivial ordered combine. -/
theorem honest_satCombine : SatCombine zSponge honestNode where
  continuity := rfl
  firstOld   := rfl
  lastNew    := rfl
  count      := rfl
  digest     := rfl

/-- **`honest_parent_count_is_two` (the attestation is REAL).** The honest node's exposed parent count
is literally `2` — a true arithmetic fact read off the genuine combine, not a husk. -/
theorem honest_parent_count_is_two : honestNode.P.count = 2 := rfl

/-! ### The anti-ghost teeth — four tampered combines, none satisfying. -/

/-- A node with BROKEN continuity: `L.lastNew = 2 ≠ 5 = R.firstOld` (a spliced/reordered seam). -/
def brokenContNode : CombineTrace :=
  { L := { firstOld := 1, lastNew := 2, count := 1, acc := 0 }
  , R := { firstOld := 5, lastNew := 3, count := 1, acc := 0 }
  , P := { firstOld := 1, lastNew := 3, count := 2, acc := 0 }
  , lCommit := 10, rCommit := 20 }

/-- **`broken_continuity_unsat` (THE TEMPORAL TOOTH).** A node whose seam continuity is broken does NOT
satisfy the gates: the `connect` constraint forces `2 = 5`, a contradiction. -/
theorem broken_continuity_unsat (sponge : List ℤ → ℤ) : ¬ SatCombine sponge brokenContNode := by
  intro h
  have := h.continuity
  simp only [brokenContNode] at this
  exact absurd this (by norm_num)

/-- A SWAPPED-child node: the honest `[1→2] ⋆ [2→3]` with the two children exchanged to
`[2→3] ⋆ [1→2]`. The seam now demands `3 = 1` — swap is a continuity break. -/
def swappedNode : CombineTrace :=
  { L := honestR, R := honestL
  , P := { firstOld := 2, lastNew := 2, count := 2, acc := 0 }
  , lCommit := 20, rCommit := 10 }

/-- **`swapped_child_unsat` (THE LEG-SWAP TOOTH).** Exchanging the two children does NOT satisfy: the
continuity gate forces `honestR.lastNew = 3 = honestL.firstOld = 1`, false. A left/right swap is
rejected by the same continuity tooth (and, on equal endpoints, by the order-sensitive digest). -/
theorem swapped_child_unsat (sponge : List ℤ → ℤ) : ¬ SatCombine sponge swappedNode := by
  intro h
  have := h.continuity
  simp only [swappedNode, honestR, honestL] at this
  exact absurd this (by norm_num)

/-- A node with WRONG count: parent claims count `7 ≠ 1 + 1`. -/
def wrongCountNode : CombineTrace :=
  { L := honestL, R := honestR
  , P := { firstOld := 1, lastNew := 3, count := 7, acc := 0 }
  , lCommit := 10, rCommit := 20 }

/-- **`wrong_count_unsat` (THE COUNT-ADDITIVITY TOOTH).** A node whose exposed count is not the sum of
the children's does NOT satisfy: the `add` gate forces `7 = 1 + 1`, false. Dropping/inserting a turn
under the node breaks exactly this. -/
theorem wrong_count_unsat (sponge : List ℤ → ℤ) : ¬ SatCombine sponge wrongCountNode := by
  intro h
  have := h.count
  simp only [wrongCountNode, honestL, honestR] at this
  exact absurd this (by norm_num)

/-- A node with WRONG digest: parent acc claimed `99`, but the gate computes `sponge [0,0] = 0` under
`zSponge`. -/
def wrongDigestNode : CombineTrace :=
  { L := honestL, R := honestR
  , P := { firstOld := 1, lastNew := 3, count := 2, acc := 99 }
  , lCommit := 10, rCommit := 20 }

/-- **`wrong_digest_unsat` (THE ORDERED-DIGEST TOOTH).** A node whose exposed digest is not the genuine
ordered fold does NOT satisfy: the digest gate forces `99 = sponge [0,0] = 0`, false. A forged
history-digest under the node is rejected. -/
theorem wrong_digest_unsat : ¬ SatCombine zSponge wrongDigestNode := by
  intro h
  have := h.digest
  simp only [wrongDigestNode, honestL, honestR, Hsponge, zSponge] at this
  exact absurd this (by norm_num)

end Vacuity

/-! ## 6. Axiom hygiene. -/

#assert_axioms satCombine_combineOk
#assert_axioms parent_is_genuine_combine
#assert_axioms agg_air_sound
#assert_axioms segsound_node_discharged
#assert_axioms combine_digest_binds
#assert_axioms honest_satCombine
#assert_axioms honest_parent_count_is_two
#assert_axioms broken_continuity_unsat
#assert_axioms swapped_child_unsat
#assert_axioms wrong_count_unsat
#assert_axioms wrong_digest_unsat

end Dregg2.Circuit.AggAirSound
