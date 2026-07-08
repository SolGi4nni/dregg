/-
# Dregg2.Circuit.Emit.MembershipDepthGeneralRung2 — the RUNG-2 depth-GENERAL soundness of the
Poseidon2 Merkle-membership descriptor (the "named residual" from the stark-kill Gate 1.5).

## What the Rust side built and what this file closes

`circuit/src/membership_descriptor_{4ary,general}.rs` build a DEPTH-GENERAL membership descriptor
whose constraint block is depth-UNIFORM: ONE Merkle level per trace row, chained by a continuity
window gate (`next.cur == this.parent`). The depth lives in the TRACE HEIGHT and the descriptor
NAME/VK — there is NO in-circuit row-count binding. An observation surfaced during the cutover: a
nominal-depth-2 witness (a 2-row trace) VERIFIES under the nominal-depth-4 descriptor for the same
`[leaf, root]` public inputs — the two share an identical (depth-uniform) constraint system.

The informal argument that this is SOUND (not a forgery): the ROOT public input binds the ACTUAL
authentication path via Poseidon2 collision-resistance — a shallower / different proof cannot hit a
genuine committed root without a hash collision. This file FORMALIZES that argument into real
theorems, so depth-nominal is SOUND-BY-PROOF, not merely argued.

## The functional model (reused, trace-independent)

`MerkleMembershipRefine` already authored + proved the depth-general functional relation:
`foldNode4 hash leaf steps` folds a leaf up an arbitrary list of 4-ary authentication `steps`
(one `(sib,sib,sib)` triple per level), and `MembersUnderRoot4 hash leaf root steps := foldNode4 … =
root` is genuine Merkle membership along a path of `steps.length` levels. `merkleMembership_sat_refines`
(SAT ⟹ SEM, `ChipTableSound` carrier) proves the DEPLOYED depth-2 descriptor's accepting trace binds
exactly a length-2 `MembersUnderRoot4`. This file lifts soundness to EVERY depth.

## What is proved (in ascending strength)

* `foldNode4_concat` — the fold peels at the TOP (last) level: `foldNode4 leaf (steps ++ [(a,b,c)]) =
  hash [foldNode4 leaf steps, a, b, c]`. The structural handle for both inductions.

* `foldNode4_inj` (the LOAD-BEARING CR half, **theorem (B)** of the brief) — with the NAMED CR carrier
  (`hash` injective, i.e. `Poseidon2SpongeCR`), two SAME-LENGTH authentication paths that fold to the
  SAME value have IDENTICAL leaf AND identical siblings at every level. The exact 4-ary analog of
  `DfaAcceptanceAir.fold_inj` / `route_commitment_binds_trace`. This is what makes the committed root
  bind the whole path.

* `membership_root_binds` / `nonmember_rejected` — the same-depth soundness: the committed root pins
  the unique member at each depth; a `leaf' ≠ leaf` at the same depth is PROVABLY not a member.

* `foldNode4_len_lt` + `committed_root_determines_depth` + `membership_depth_general_sound`
  (**theorem (A)**, the headline) — with CR AND the NAMED leaf/node domain-separation carrier
  `LeafNodeSep` (leaves are never hash outputs — realized by Poseidon2 leaf tagging), the committed
  root binds not only the path but its DEPTH: two accepting witnesses (of ANY nominal descriptor
  depths, ANY actual heights) that expose the same committed root necessarily have the SAME leaf,
  SAME path, and SAME depth. So a nominal-depth-4 descriptor and a nominal-depth-2 descriptor cannot
  both legitimately accept the same genuine root at different depths — depth-nominal is SOUND.

## Honest scope — what the CR carrier alone does and does NOT buy

Same-depth binding (`foldNode4_inj`, `membership_root_binds`) rides CR ALONE. The CROSS-depth leg
(`foldNode4_len_lt` and everything above it) genuinely REQUIRES the extra `LeafNodeSep` carrier: CR
(hash injectivity) alone does NOT forbid a length-`m` fold and a length-`n` fold (`m ≠ n`) from
coinciding — that is the classic Merkle depth-extension / second-preimage shape (a raw leaf value
colliding with an interior node digest), which CR does not touch. It is closed exactly by
domain-separating leaves from node digests, which the deployed Poseidon2 Merkle set does (leaf
tagging). This file names that carrier precisely rather than overclaiming CR-only cross-depth
soundness. The remaining nominal↔actual distinction is carried by the descriptor NAME/VK, as designed.

## Non-vacuity (TRUE and FALSE, never a stub)

* `member_true` / `nonmember_false` — a CONCRETE depth-2 member folds to its root (a real arithmetic
  identity) and a wrong leaf under the same root is CONCRETELY rejected — via `decide`, no carrier.
* `deployed_sat_grounds_membership` — the DEPLOYED depth-2 descriptor's genuine `Satisfied2` witness
  (`MerkleMembershipRefine.witness_spec`, itself fired from a concrete `Satisfied2`) yields an
  inhabited `MembersUnderRoot4` — the membership predicate the soundness theorems govern is realized
  by an actual accepting circuit trace, not an empty antecedent.
* `cr_soundness_fires` — for ANY CR hash, the membership hypothesis is inhabited (the fold of any
  path is a genuine member) AND a wrong leaf is provably rejected by `nonmember_rejected` — the CR
  filter genuinely BITES.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; the CR carrier `Poseidon2SpongeCR` and the
leaf/node separation carrier `LeafNodeSep` ride as NAMED hypotheses, never as Lean axioms. NEW file;
all imports read-only.
-/
import Dregg2.Circuit.Emit.MerkleMembershipRefine
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.MembershipDepthGeneralRung2

open Dregg2.Circuit.Emit.MerkleMembershipRefine
  (foldNode4 MembersUnderRoot4 merkleMembers2_as_fold witness_spec)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option autoImplicit false

/-! ## §1 — the structural handle: the 4-ary fold peels at the TOP (last) level.

`foldNode4` is a left fold with the leaf as the seed, so its LAST step is the top of the tree — the
level the committed root directly pins. Peeling there is what lets CR bite on the root. -/

/-- **`foldNode4_concat`** — appending one authentication step `(a,b,c)` hashes the running fold with
that level's siblings: `foldNode4 leaf (steps ++ [(a,b,c)]) = hash [foldNode4 leaf steps, a, b, c]`. -/
theorem foldNode4_concat (hash : List ℤ → ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ × ℤ)) (a b c : ℤ) :
    foldNode4 hash leaf (steps ++ [(a, b, c)]) = hash [foldNode4 hash leaf steps, a, b, c] := by
  simp only [foldNode4, List.foldl_append, List.foldl_cons, List.foldl_nil]

/-! ## §2 — the CR carrier as hash injectivity. -/

/-- `Poseidon2SpongeCR hash` IS `hash`-injectivity (its very definition), so it hands us the injective
function the two folds are compared through. Named hypothesis, never an axiom. -/
theorem inj_of_cr {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash) : Function.Injective hash :=
  fun _ _ h => hCR _ _ h

/-! ## §3 — THE LOAD-BEARING CR HALF (theorem (B)): same-length fold injectivity. -/

/-- **`foldNode4_inj` — the depth-general analog of `DfaAcceptanceAir.fold_inj`.** Under the NAMED CR
carrier (`hash` injective), two authentication paths of the SAME length that fold to the SAME value
have identical leaves AND identical siblings at every level. Peels from the top (`foldNode4_concat`)
and reduces level-by-level through CR. This is the load-bearing content of "the committed root binds
the whole path". -/
theorem foldNode4_inj {hash : List ℤ → ℤ} (hinj : Function.Injective hash) :
    ∀ (stepsA stepsB : List (ℤ × ℤ × ℤ)) (leafA leafB : ℤ),
      stepsA.length = stepsB.length →
      foldNode4 hash leafA stepsA = foldNode4 hash leafB stepsB →
      leafA = leafB ∧ stepsA = stepsB := by
  intro stepsA
  induction stepsA using List.reverseRecOn with
  | nil =>
    intro stepsB leafA leafB hlen hfold
    cases stepsB with
    | nil => simp only [foldNode4, List.foldl_nil] at hfold; exact ⟨hfold, rfl⟩
    | cons x xs => exact absurd hlen (by simp)
  | append_singleton A' sa ih =>
    intro stepsB leafA leafB hlen hfold
    rcases List.eq_nil_or_concat' stepsB with rfl | ⟨B', sb, rfl⟩
    · exact absurd hlen (by simp)
    · obtain ⟨a, b, c⟩ := sa
      obtain ⟨a', b', c'⟩ := sb
      rw [foldNode4_concat, foldNode4_concat] at hfold
      have hlist := hinj hfold
      simp only [List.cons.injEq, and_true] at hlist
      obtain ⟨hfoldeq, ha, hb, hc⟩ := hlist
      have hlen' : A'.length = B'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen; omega
      obtain ⟨hleaf, hstep⟩ := ih B' leafA leafB hlen' hfoldeq
      exact ⟨hleaf, by rw [hstep, ha, hb, hc]⟩

/-! ## §4 — same-depth soundness: the committed root pins the unique member. -/

/-- **`membership_root_binds`** — two accepting witnesses of the SAME actual depth that expose the SAME
committed root have identical leaves and identical authentication paths. Rides CR alone. -/
theorem membership_root_binds {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {leafA leafB rootA rootB : ℤ} {stepsA stepsB : List (ℤ × ℤ × ℤ)}
    (hA : MembersUnderRoot4 hash leafA rootA stepsA)
    (hB : MembersUnderRoot4 hash leafB rootB stepsB)
    (hlen : stepsA.length = stepsB.length) (hroot : rootA = rootB) :
    leafA = leafB ∧ stepsA = stepsB := by
  refine foldNode4_inj (inj_of_cr hCR) stepsA stepsB leafA leafB hlen ?_
  have hA' : foldNode4 hash leafA stepsA = rootA := hA
  have hB' : foldNode4 hash leafB stepsB = rootB := hB
  rw [hA', hB', hroot]

/-- **`nonmember_rejected`** — given a GENUINE member at the committed root, ANY `leaf' ≠ leaf` at the
same depth is PROVABLY not a member of that root. So the descriptor cannot be fooled into accepting a
non-member at the honest depth: the target is a real filter, not `True`. -/
theorem nonmember_rejected {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    {leafG leaf' root : ℤ} {stepsG steps' : List (ℤ × ℤ × ℤ)}
    (hgen : MembersUnderRoot4 hash leafG root stepsG)
    (hlen : steps'.length = stepsG.length) (hne : leaf' ≠ leafG) :
    ¬ MembersUnderRoot4 hash leaf' root steps' := by
  intro h'
  exact hne (membership_root_binds hCR h' hgen hlen rfl).1

/-! ## §5 — the CROSS-depth leg: the committed root binds the DEPTH (theorem (A), headline).

CR alone does NOT forbid different-length folds from coinciding (the Merkle depth-extension shape: a
raw leaf value colliding with an interior node digest). That is closed by domain-separating leaves
from node digests — the NAMED `LeafNodeSep` carrier below, realized by Poseidon2 leaf tagging. -/

/-- **`LeafNodeSep hash IsLeaf`** — the leaf/node domain-separation carrier: a value tagged as a leaf
(`IsLeaf a`) is never equal to any Poseidon2 node digest (`hash l`). REALIZABLE by leaf tagging in the
deployed Poseidon2 Merkle set; carried as a NAMED Prop hypothesis, never an axiom. -/
def LeafNodeSep (hash : List ℤ → ℤ) (IsLeaf : ℤ → Prop) : Prop :=
  ∀ a, IsLeaf a → ∀ l, a ≠ hash l

/-- **`foldNode4_len_lt`** — under CR AND leaf/node separation, a SHORTER authentication path from a
genuine (tagged) leaf can NEVER fold to the same value as a strictly longer path. Peels both from the
top through CR until the shorter one bottoms out at its raw leaf, which then equals a node digest —
refuted by `LeafNodeSep`. -/
theorem foldNode4_len_lt {hash : List ℤ → ℤ} {IsLeaf : ℤ → Prop}
    (hinj : Function.Injective hash) (hsep : LeafNodeSep hash IsLeaf) :
    ∀ (stepsB stepsA : List (ℤ × ℤ × ℤ)) (leafA leafB : ℤ),
      IsLeaf leafA → stepsA.length < stepsB.length →
      foldNode4 hash leafA stepsA ≠ foldNode4 hash leafB stepsB := by
  intro stepsB
  induction stepsB using List.reverseRecOn with
  | nil => intro stepsA leafA leafB _ hlt _; simp at hlt
  | append_singleton B' sb ihB =>
    intro stepsA leafA leafB hIL hlt hfold
    rcases List.eq_nil_or_concat' stepsA with rfl | ⟨A', sa, rfl⟩
    · obtain ⟨b1, b2, b3⟩ := sb
      rw [foldNode4_concat] at hfold
      simp only [foldNode4, List.foldl_nil] at hfold
      exact hsep leafA hIL _ hfold
    · obtain ⟨a1, a2, a3⟩ := sa
      obtain ⟨b1, b2, b3⟩ := sb
      rw [foldNode4_concat, foldNode4_concat] at hfold
      have hlist := hinj hfold
      simp only [List.cons.injEq, and_true] at hlist
      have hlt' : A'.length < B'.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlt; omega
      exact ihB A' leafA leafB hIL hlt' hlist.1

/-- **`committed_root_determines_depth`** — under CR and leaf/node separation, two accepting witnesses
(from tagged leaves) that expose the SAME committed root necessarily have the SAME depth. So a nominal
depth-`d` descriptor cannot accept a genuine committed root at any height other than the one the root
was committed at. -/
theorem committed_root_determines_depth {hash : List ℤ → ℤ} {IsLeaf : ℤ → Prop}
    (hCR : Poseidon2SpongeCR hash) (hsep : LeafNodeSep hash IsLeaf)
    {leafA leafB root : ℤ} {stepsA stepsB : List (ℤ × ℤ × ℤ)}
    (hILa : IsLeaf leafA) (hILb : IsLeaf leafB)
    (hA : MembersUnderRoot4 hash leafA root stepsA)
    (hB : MembersUnderRoot4 hash leafB root stepsB) :
    stepsA.length = stepsB.length := by
  have hinj := inj_of_cr hCR
  have hAf : foldNode4 hash leafA stepsA = root := hA
  have hBf : foldNode4 hash leafB stepsB = root := hB
  rcases lt_trichotomy stepsA.length stepsB.length with h | h | h
  · exact absurd (hAf.trans hBf.symm) (foldNode4_len_lt hinj hsep stepsB stepsA leafA leafB hILa h)
  · exact h
  · exact absurd (hBf.trans hAf.symm) (foldNode4_len_lt hinj hsep stepsA stepsB leafB leafA hILb h)

/-- **`membership_depth_general_sound` — THE HEADLINE (theorem (A)).** Under the NAMED CR carrier and
the NAMED leaf/node separation carrier, the committed root binds the ENTIRE authentication path AND
its depth: two accepting witnesses (of ANY nominal descriptor depths, ANY actual heights) exposing the
SAME committed root have the SAME leaf, the SAME siblings at every level, and the SAME depth. This is
what makes depth-nominal SOUND-BY-PROOF: a shallower/deeper proof cannot hit a genuine committed root
of a different depth, so accepting under a mismatched nominal descriptor is impossible for a real
member and cannot forge a non-member. -/
theorem membership_depth_general_sound {hash : List ℤ → ℤ} {IsLeaf : ℤ → Prop}
    (hCR : Poseidon2SpongeCR hash) (hsep : LeafNodeSep hash IsLeaf)
    {leafA leafB rootA rootB : ℤ} {stepsA stepsB : List (ℤ × ℤ × ℤ)}
    (hILa : IsLeaf leafA) (hILb : IsLeaf leafB)
    (hA : MembersUnderRoot4 hash leafA rootA stepsA)
    (hB : MembersUnderRoot4 hash leafB rootB stepsB)
    (hroot : rootA = rootB) :
    leafA = leafB ∧ stepsA = stepsB := by
  have hB' : MembersUnderRoot4 hash leafB rootA stepsB := by
    show foldNode4 hash leafB stepsB = rootA; rw [hroot]; exact hB
  have hdepth := committed_root_determines_depth hCR hsep hILa hILb hA hB'
  exact membership_root_binds hCR hA hB hdepth hroot

/-! ## §6 — non-vacuity: TRUE and FALSE, concrete and carrier-fired. -/

/-- A concrete order-sensitive digit hash `[x₀,…] ↦ …·100 + xᵢ` — distinguishes levels for the finite
witnesses (its GLOBAL CR is not asserted; these are `decide`-checked concrete instances). -/
def dHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **Non-vacuity, TRUE (concrete).** Leaf `1` with level-0 siblings `2,3,4` folds to `dHash[1,2,3,4]
= 1020304`, then with level-1 siblings `5,6,7` to root `1020304050607` — a genuine length-2 member. -/
theorem member_true : MembersUnderRoot4 dHash 1 1020304050607 [(2, 3, 4), (5, 6, 7)] := by
  show foldNode4 dHash 1 [(2, 3, 4), (5, 6, 7)] = 1020304050607
  decide

/-- **Non-vacuity, FALSE (concrete).** The WRONG leaf `999` under the SAME root and siblings is NOT a
member — the fold separates. A `True`/`P → P` target could not distinguish this. -/
theorem nonmember_false : ¬ MembersUnderRoot4 dHash 999 1020304050607 [(2, 3, 4), (5, 6, 7)] := by
  show ¬ foldNode4 dHash 999 [(2, 3, 4), (5, 6, 7)] = 1020304050607
  decide

/-- **Non-vacuity, cross-depth (concrete).** A length-1 fold and a length-2 fold of concrete inputs are
distinct — depth-extension does not coincide here (a concrete instance of what `LeafNodeSep` forbids in
general). -/
theorem cross_depth_concrete :
    foldNode4 dHash 5 [(1, 1, 1)] ≠ foldNode4 dHash 1 [(2, 3, 4), (5, 6, 7)] := by decide

/-- **Non-vacuity, DEPLOYED-SAT grounded.** The genuine `Satisfied2` witness of the deployed depth-2
Merkle-membership descriptor (`MerkleMembershipRefine.witness_spec`, fired from a concrete accepting
trace) yields an inhabited `MembersUnderRoot4` of length 2 — the membership predicate the soundness
theorems govern is realized by an ACTUAL accepting circuit trace, not an empty antecedent. -/
theorem deployed_sat_grounds_membership :
    ∃ (hash : List ℤ → ℤ) (leaf root : ℤ) (steps : List (ℤ × ℤ × ℤ)),
      MembersUnderRoot4 hash leaf root steps ∧ steps.length = 2 := by
  refine ⟨_, _, _, _, (merkleMembers2_as_fold _ _ _ _ _ _ _ _ _).mp witness_spec, rfl⟩

/-- **Non-vacuity, CR-CARRIER FIRED.** For ANY hash satisfying the NAMED CR carrier, the membership
hypothesis is INHABITED (the fold of any path is a genuine member) AND a wrong leaf at the same depth
is PROVABLY rejected by `nonmember_rejected` — the CR filter genuinely bites, jointly satisfiably. -/
theorem cr_soundness_fires {hash : List ℤ → ℤ} (hCR : Poseidon2SpongeCR hash)
    (leaf leaf' : ℤ) (steps : List (ℤ × ℤ × ℤ)) (hne : leaf' ≠ leaf) :
    MembersUnderRoot4 hash leaf (foldNode4 hash leaf steps) steps
    ∧ ¬ MembersUnderRoot4 hash leaf' (foldNode4 hash leaf steps) steps :=
  ⟨rfl, nonmember_rejected hCR (leafG := leaf) (steps' := steps) (stepsG := steps) rfl rfl hne⟩

/-! ## §7 — axiom tripwires. -/

#assert_axioms foldNode4_concat
#assert_axioms foldNode4_inj
#assert_axioms membership_root_binds
#assert_axioms nonmember_rejected
#assert_axioms foldNode4_len_lt
#assert_axioms committed_root_determines_depth
#assert_axioms membership_depth_general_sound
#assert_axioms member_true
#assert_axioms nonmember_false
#assert_axioms cross_depth_concrete
#assert_axioms deployed_sat_grounds_membership
#assert_axioms cr_soundness_fires

end Dregg2.Circuit.Emit.MembershipDepthGeneralRung2
