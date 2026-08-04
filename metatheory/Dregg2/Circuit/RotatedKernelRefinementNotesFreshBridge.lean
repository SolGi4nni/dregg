/-
# Dregg2.Circuit.RotatedKernelRefinementNotesFreshBridge — the FOLDED `air_accepts ⟺ spec` bridge for
`noteSpend`'s DOUBLE-SPEND FRESHNESS: ONE named carrier bundle, ONE literal biconditional against the
literal `nf ∉ nulls`, both directions load-bearing.

## Why this file exists (the assurance-perimeter replication — the note-spend exemplar)

`RotatedKernelRefinementNotesFresh` proves the SOUNDNESS direction: a satisfying strengthened decode
FORCES `nf ∉ pre.nullifiers` in-circuit (`freshness_forced`, via the sorted-Merkle non-membership open
`nonMembership_sound`). It rides the SAME decode object non-revocation rides — the spine-faithfulness
carrier (`SpineCommits`) plus the deployed nullifier-accumulator faithfulness (`NullifierTreeEncodes`).

This file does the last mile the assurance-perimeter campaign (`docs/DESIGN-assurance-perimeter-closure.md`,
`docs/ROADMAP-assurance-perimeter.md`) asked for, copying the non-rev TEMPLATE
(`Emit/AccumulatorNonRevocationRefine.lean`, which absorbed the template that was
`Emit/NonRevocationRefineBridge` at `209d543e5`):

  * fold the residual trust into ONE named carrier bundle (`NoteFreshCarriers`);
  * state the literal `⟺` (accept-SET ↔ the human spec `nf ∉ nulls`);
  * state the `∀-soundness ∧ ∃-completeness` bridge that concludes the literal `nf ∉ nulls`.

Unlike non-rev's window-bracketed refinement (which drops below-min / above-max), the note-spend
`GapOpen` has ALL FOUR covering-gap shapes (`empty`/`below`/`inner`/`above`), so the accept-set equals
FULL non-membership and the biconditional is stated directly against the human spec `nf ∉ nulls` — no
intermediate "windowed" refinement is needed. Both directions are genuinely load-bearing.

## THE 5-STEP SCHEMA (where each step lives — same shape as the non-rev template)

  1. **Semantic relation.** `nf ∉ pre.nullifiers` (the human meaning "this nullifier was not spent
     before" — the no-double-spend freshness). Combinatorial core: `GapOpen.excludesSpine`.
  2. **SAT ⟹ SEM vs NAMED carriers.** `RotatedKernelRefinementNotesFresh.freshness_forced`: a valid gap
     open + the named carriers force `nf ∉ nulls`. Folded here behind `NoteFreshCarriers` (§2).
  3. **Construct the accepting object.** `gap_positions` (§1, pure combinatorics: a sorted spine + a fresh
     key ADMIT a covering gap) → `gapOpen_complete` (§1, wraps it with the deployed `MembersAt8`
     openings pulled from `SpineCommits.present_iff`). The forward direction `SortedTreeNonMembership`
     did not yet supply; authored here.
  4. **Construct AND compose the decode (never assume).** `noteSpendFresh_of_base_open` (§4, the inverse
     of `noteSpendFresh_to_base`): the honest prover's base set-insert decode + a realizable faithful
     nullifier tree UPGRADE to the freshness-FORCED strengthened decode with the gap CONSTRUCTED.
  5. **Round-trip / compose the `⟺`.** `noteSpendFresh_accepts_iff` (§3, the literal single biconditional
     accept-set = `nf ∉ nulls`) and `noteSpendFresh_bridge` (§4, the ∀-soundness ∧ ∃-completeness
     conjunction concluding the literal `nf ∉ nulls`, mirroring `NonRevocationRefineBridge`).

## The ONE named carrier bundle (the honest floor)

`NoteFreshCarriers S8 root nulls spine` (§2) folds EVERYTHING between an accepting non-membership open
and genuine freshness:
  * `treeEnc`  — `NullifierTreeEncodes`: the deployed sorted-Merkle nullifier accumulator's committed
                 key set EQUALS the kernel nullifier keys. This is the HONEST NAMED FLOOR — the
                 Rust-accumulator-boundary faithfulness (`commit/src/poseidon2_tree.rs` ↔ the Lean
                 accumulator). It is a DIFFERENTIAL OBLIGATION, named, NOT discharged here.
  * `spineCommits` — `SpineCommits`: the sorted-key-spine ↔ root binding. This is where the Poseidon2
                 collision-resistance (`Compress1CR` via the deployed binary-Merkle fold) enters — the
                 realizable crypto residue, at the spine↔root step ONLY.
The ordering / "range" side (`keyOf a < k < keyOf b`) is UNCONDITIONAL data carried inside the `GapOpen`
constructors themselves (the neighbor openings pin the keys; the strict comparisons are the gap gates),
not a separate trusted carrier. Nothing else is assumed.

## Mutation canary (load-bearing, machine-checked, §5)
  * `carrier_load_bearing` — the `treeEnc` carrier is load-bearing for `→` (soundness): a valid (empty)
    gap open of `nfKey nf` coexists with `nf ∈ nulls` when the tree is NOT faithful — so dropping
    `NullifierTreeEncodes` from `freshness_forced` admits a double-spend. (Contrast
    `noteSpendFresh_gapOpen_unsat_on_double`, which HAS `treeEnc` and rejects.)
  * `gap_needs_freshness` — the freshness precondition is load-bearing for `←` (completeness): a PRESENT
    key admits NO valid gap (a fake gap would exclude a member — impossible via `excludesSpine`), so
    `gapOpen_complete`'s `nf ∉ nulls` premise cannot be dropped.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. No `sorry`/`axiom`/`native_decide`. The crypto
carriers enter ONLY as the named `NoteFreshCarriers` fields (`NullifierTreeEncodes`/`SpineCommits`, both
HYPOTHESES, never axioms). NEW file; every import read-only; the committed
`RotatedKernelRefinementNotesFresh` proofs are untouched. Acceptance: correspondence to the DEPLOYED
`noteSpendFreshEncodes` descriptor (the SAME object the base file's `freshness_forced` /
`noteSpendFresh_descriptorRefines` speak of), NOT a re-authored mirror.
-/
import Dregg2.Circuit.RotatedKernelRefinementNotesFresh

namespace Dregg2.Circuit.RotatedKernelRefinementNotesFreshBridge

open Dregg2.Circuit.DeployedCapTree (CapLeaf Cap8Scheme Digest8)
open Dregg2.Circuit.SortedTreeNonMembership
  (keyOf keysOf SpineCommits GapOpen nonMembership_sound keysOf_eq_spine)
open Dregg2.Circuit.RotatedKernelRefinementNotesFresh
  (nfKey nfKey_injective NullifierTreeEncodes absent_key_absent_nullifier freshness_forced
   noteSpendFreshEncodes noteSpendFresh_freshness noteSpendFresh_descriptorRefines
   noteSpendFresh_gapOpen_unsat_on_double)
open Dregg2.Circuit.StateCommit (compressNInjective)
open Dregg2.Circuit.Spec.NoteNullifier (NoteSpendSpec)
open Dregg2.Crypto.NonMembership (Sorted Adjacent head_lt_of_sorted sorted_tail)
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the forward construction: a sorted spine + a fresh key ADMIT a covering gap.

The direction `SortedTreeNonMembership` did not supply (it proved only the SOUND direction, a valid gap
⟹ absent). `gap_positions` is the pure combinatorial core: any key absent from a sorted list falls into
exactly one of the four covering-gap positions (empty / below-min / a strict interior gap between an
adjacent pair / above-max). `gapOpen_complete` wraps it into a real `GapOpen` by pulling the neighbor
`MembersAt8` openings from the `SpineCommits` binding. This is what makes the `⟺` a full biconditional. -/

/-- **`gap_positions`** — a key `k` absent from a `Sorted` spine sits in exactly one covering-gap shape:
the empty list, below the head, strictly inside an adjacent interior gap, or above the last element. The
combinatorial converse of `GapOpen.excludesSpine`; UNCONDITIONAL (no crypto). Proved by induction. -/
theorem gap_positions (k : ℤ) : ∀ (spine : List ℤ), Sorted spine → k ∉ spine →
    spine = []
    ∨ (∃ b t', spine = b :: t' ∧ k < b)
    ∨ (∃ L R, Adjacent spine L R ∧ L < k ∧ k < R)
    ∨ (∃ pre a, spine = pre ++ [a] ∧ a < k) := by
  intro spine
  induction spine with
  | nil => intro _ _; exact Or.inl rfl
  | cons x t ih =>
    intro hs hnot
    have hst : Sorted t := sorted_tail hs
    have hkx : k ≠ x := fun h => hnot (by rw [h]; simp)
    have hkt : k ∉ t := fun h => hnot (List.mem_cons_of_mem x h)
    rcases lt_trichotomy k x with hlt | heq | hgt
    · exact Or.inr (Or.inl ⟨x, t, rfl, hlt⟩)
    · exact absurd heq hkx
    · rcases ih hst hkt with h0 | hbelow | hinner | habove
      · -- t = [] : spine = [x], k > x = last (above-max).
        subst h0
        exact Or.inr (Or.inr (Or.inr ⟨[], x, rfl, hgt⟩))
      · -- t = b :: t' with k < b : spine = x :: b :: t', x < k < b (interior gap between x and b).
        obtain ⟨b, t', hbeq, hkb⟩ := hbelow
        subst hbeq
        exact Or.inr (Or.inr (Or.inl ⟨x, b, ⟨[], t', rfl⟩, hgt, hkb⟩))
      · -- an interior gap of t is an interior gap of x :: t (prepend x to the split prefix).
        obtain ⟨L, R, ⟨pre, post, hsplit⟩, hlo, hhi⟩ := hinner
        exact Or.inr (Or.inr (Or.inl ⟨L, R, ⟨x :: pre, post, by rw [hsplit]; simp [List.cons_append]⟩, hlo, hhi⟩))
      · -- above-max of t is above-max of x :: t.
        obtain ⟨pre, a, hpre, hak⟩ := habove
        exact Or.inr (Or.inr (Or.inr ⟨x :: pre, a, by rw [hpre]; simp [List.cons_append], hak⟩))

/-- **`gapOpen_complete` — THE FORWARD CONSTRUCTION.** Given the (realizable) spine↔root binding and a
key ABSENT from the committed spine, a VALID `GapOpen` for `k` EXISTS: `gap_positions` finds the covering
position, and `SpineCommits.present_iff` supplies the deployed `MembersAt8` openings of the bracketing
neighbor leaves. The `←`/completeness engine of the `⟺`. -/
theorem gapOpen_complete (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ) (k : ℤ)
    (hc : SpineCommits S8 root spine) (hnot : k ∉ spine) :
    ∃ g : GapOpen S8 root k, g.coversSpine spine := by
  rcases gap_positions k spine hc.sorted hnot with h0 | hbelow | hinner | habove
  · exact ⟨GapOpen.empty, by show spine = []; exact h0⟩
  · obtain ⟨b, t', hbeq, hkb⟩ := hbelow
    have hmem : b ∈ spine := by rw [hbeq]; simp
    obtain ⟨leaf, hkey, hopen⟩ := (hc.present_iff b).mpr hmem
    refine ⟨GapOpen.below leaf hopen ?_, ?_⟩
    · rw [hkey]; exact hkb
    · show spine.head? = some (keyOf leaf)
      simp only [hbeq, hkey, List.head?_cons]
  · obtain ⟨L, R, ⟨pre, post, hsplit⟩, hlo, hhi⟩ := hinner
    have hmemL : L ∈ spine := by rw [hsplit]; simp
    have hmemR : R ∈ spine := by rw [hsplit]; simp
    obtain ⟨leafL, hkeyL, hopenL⟩ := (hc.present_iff L).mpr hmemL
    obtain ⟨leafR, hkeyR, hopenR⟩ := (hc.present_iff R).mpr hmemR
    refine ⟨GapOpen.inner leafL leafR hopenL hopenR ?_ ?_, ?_⟩
    · rw [hkeyL]; exact hlo
    · rw [hkeyR]; exact hhi
    · show Adjacent spine (keyOf leafL) (keyOf leafR)
      rw [hkeyL, hkeyR]; exact ⟨pre, post, hsplit⟩
  · obtain ⟨pre, a, hpre, hak⟩ := habove
    have hmem : a ∈ spine := by rw [hpre]; simp
    obtain ⟨leaf, hkey, hopen⟩ := (hc.present_iff a).mpr hmem
    refine ⟨GapOpen.above leaf hopen ?_, ?_⟩
    · rw [hkey]; exact hak
    · show spine.getLast? = some (keyOf leaf)
      rw [hkey]; exact List.getLast?_eq_some_iff.mpr ⟨pre, hpre⟩

/-! ## §2 — the ONE named carrier bundle + the accept-set object. -/

/-- **`NoteFreshCarriers S8 root nulls spine` — THE named carrier bundle.** Everything the freshness
bridge trusts between an accepting non-membership open and genuine freshness, folded into one structure:
the deployed nullifier-accumulator faithfulness (`treeEnc`, the HONEST NAMED FLOOR — the
Rust-accumulator-boundary differential obligation, NOT discharged here) and the spine↔root binding
(`spineCommits`, where the Poseidon2 collision-resistance enters). The ordering/"range" side is
unconditional data inside the `GapOpen` itself, not a trusted carrier. Nothing else is assumed. -/
structure NoteFreshCarriers (S8 : Cap8Scheme) (root : Digest8) (nulls : List Nat)
    (spine : List ℤ) : Prop where
  /-- The deployed sorted-Merkle nullifier accumulator faithfully encodes the kernel nullifier keys.
  The honest named floor: the Rust-accumulator-boundary faithfulness, a named DIFFERENTIAL OBLIGATION. -/
  treeEnc : NullifierTreeEncodes S8 root nulls
  /-- The committed key spine ↔ root binding (Poseidon2 CR via the deployed binary-Merkle fold enters
  here, at the spine↔root step only). -/
  spineCommits : SpineCommits S8 root spine

/-- **`NoteFreshAccepts S8 root nf spine`** — the descriptor's non-membership ACCEPT for `nf`: a valid
covering-gap open of `nfKey nf` exists against the committed nullifier spine (the deployed
`noteSpendFreshEncodes.gapOpen` + `gapValid` ingredients). The descriptor's freshness judgment on `nf`. -/
def NoteFreshAccepts (S8 : Cap8Scheme) (root : Digest8) (nf : Nat) (spine : List ℤ) : Prop :=
  ∃ g : GapOpen S8 root (nfKey nf), g.coversSpine spine

/-! ## §3 — the literal single biconditional: accept-set = the freshness spec. -/

/-- **`noteSpendFresh_accepts_iff` — THE LITERAL `⟺` (accept-set = spec).** Under the named carrier
bundle, the descriptor's freshness accept-set for `nf` against the committed tree is EXACTLY the genuine
non-double-spends: `NoteFreshAccepts S8 root nf spine ↔ nf ∉ nulls`. A genuine full biconditional (the
four gap shapes capture full non-membership), both directions load-bearing:

`→` : a valid gap open forces `nfKey nf` absent from the committed tree, hence `nf ∉ nulls`
      (`freshness_forced` — the `treeEnc` carrier is load-bearing, `carrier_load_bearing`).
`←` : a genuinely fresh `nf` has `nfKey nf ∉ spine`, so `gapOpen_complete` CONSTRUCTS the accepting gap
      (the freshness premise is load-bearing, `gap_needs_freshness`). -/
theorem noteSpendFresh_accepts_iff (S8 : Cap8Scheme) (root : Digest8) (nulls : List Nat)
    (nf : Nat) (spine : List ℤ) (C : NoteFreshCarriers S8 root nulls spine) :
    NoteFreshAccepts S8 root nf spine ↔ nf ∉ nulls := by
  constructor
  · rintro ⟨g, hv⟩
    exact freshness_forced S8 root nulls nf spine C.treeEnc C.spineCommits g hv
  · intro hfresh
    have hkeys : nfKey nf ∉ keysOf S8 root := by
      intro hmem
      obtain ⟨nf', hnf', hkeq⟩ := (C.treeEnc (nfKey nf)).mp hmem
      exact hfresh (nfKey_injective hkeq ▸ hnf')
    have hspine : nfKey nf ∉ spine := fun hmem =>
      hkeys ((keysOf_eq_spine S8 root spine C.spineCommits (nfKey nf)).mpr hmem)
    exact gapOpen_complete S8 root spine (nfKey nf) C.spineCommits hspine

/-- **`noteSpendFresh_accepts_fresh` — the security corollary.** The descriptor accepting `nf` PROVES the
human spec: `NoteFreshAccepts → nf ∉ nulls`. "If the circuit says `nf` is fresh, it genuinely is." -/
theorem noteSpendFresh_accepts_fresh {S8 : Cap8Scheme} {root : Digest8} {nulls : List Nat}
    {nf : Nat} {spine : List ℤ} (C : NoteFreshCarriers S8 root nulls spine)
    (h : NoteFreshAccepts S8 root nf spine) : nf ∉ nulls :=
  (noteSpendFresh_accepts_iff S8 root nulls nf spine C).mp h

/-! ## §4 — the codebase-idiom bridge: ∀-soundness ∧ ∃-completeness (concludes literal `nf ∉ nulls`). -/

/-- **`noteSpendFresh_of_base_open` — the completeness constructor** (the inverse of
`noteSpendFresh_to_base`). The honest prover's BASE set-insert decode (`noteSpendGenuineEncodes`, freshness
CARRIED) plus a realizable faithful nullifier tree + a valid gap open UPGRADE to the strengthened
`noteSpendFreshEncodes` — the freshness now FORCED by the open, not carried. Copies the base fields;
installs the open ingredients. -/
def noteSpendFresh_of_base_open (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
    (base : RotatedKernelRefinementNotes.noteSpendGenuineEncodes compressN pre post nf actor spendProof)
    (nfTreeRoot : Digest8) (spine : List ℤ)
    (treeEnc : NullifierTreeEncodes S8 nfTreeRoot pre.kernel.nullifiers)
    (spineCommits : SpineCommits S8 nfTreeRoot spine)
    (g : GapOpen S8 nfTreeRoot (nfKey nf)) (hv : g.coversSpine spine) :
    noteSpendFreshEncodes S8 compressN pre post nf actor spendProof where
  preRoot := base.preRoot
  postRoot := base.postRoot
  hroots := base.hroots
  gate := base.gate
  nfTreeRoot := nfTreeRoot
  spine := spine
  treeEnc := treeEnc
  spineCommits := spineCommits
  gapOpen := g
  gapValid := hv
  proof := base.proof
  logAdv := base.logAdv
  frAccounts := base.frAccounts
  frCell := base.frCell
  frCaps := base.frCaps
  frRevoked := base.frRevoked
  frCommitments := base.frCommitments
  frBal := base.frBal
  frSlotCaveats := base.frSlotCaveats
  frFactories := base.frFactories
  frLifecycle := base.frLifecycle
  frDeathCert := base.frDeathCert
  frDelegate := base.frDelegate
  frDelegations := base.frDelegations
  frDelegationEpoch := base.frDelegationEpoch
  frDelegationEpochAt := base.frDelegationEpochAt
  frHeaps := base.frHeaps
  frNullifierRoot := base.frNullifierRoot
  frRevokedRoot := base.frRevokedRoot
  frCommitmentsRoot := base.frCommitmentsRoot

/-- **`noteSpendFresh_bridge` — the two-direction bridge (concludes the literal `nf ∉ nulls`).**
  * SOUNDNESS (∀-decode): every strengthened decode of the DEPLOYED `noteSpendFreshEncodes` reads a
    genuine non-double-spend (`nf ∉ pre.nullifiers`), via the in-circuit open (`noteSpendFresh_freshness`
    = `freshness_forced`). The hostile-prover guarantee, quantified over all such decodes.
  * COMPLETENESS (∃-decode): any honest base set-insert decode + a realizable faithful nullifier tree
    over a genuinely-fresh `nf` yields a strengthened decode whose freshness is CONSTRUCTED-FORCED (the
    gap built by `gapOpen_complete`, not carried) — and that decode REFINES the kernel spec
    (`noteSpendFresh_descriptorRefines`) AND reads back the literal `nf ∉ pre.nullifiers`.
Together: the descriptor's accept-set (∀→) and the freshness relation (∃←) agree on the whole family. -/
theorem noteSpendFresh_bridge (S8 : Cap8Scheme)
    (compressN : List RotatedKernelRefinementNotes.FieldElem → RotatedKernelRefinementNotes.FieldElem)
    (hN : compressNInjective compressN) :
    (∀ (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
        (henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof),
        nf ∉ pre.kernel.nullifiers)
    ∧
    (∀ (pre post : RecChainedState) (nf : Nat) (actor : CellId) (spendProof : Bool)
        (base : RotatedKernelRefinementNotes.noteSpendGenuineEncodes
          compressN pre post nf actor spendProof)
        (nfTreeRoot : Digest8) (spine : List ℤ)
        (treeEnc : NullifierTreeEncodes S8 nfTreeRoot pre.kernel.nullifiers)
        (spineCommits : SpineCommits S8 nfTreeRoot spine),
        ∃ henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof,
          NoteSpendSpec pre nf actor spendProof post ∧ nf ∉ pre.kernel.nullifiers) := by
  refine ⟨?_, ?_⟩
  · intro pre post nf actor spendProof henc
    exact noteSpendFresh_freshness S8 compressN pre post nf actor spendProof henc
  · intro pre post nf actor spendProof base nfTreeRoot spine treeEnc spineCommits
    have hfresh : nf ∉ pre.kernel.nullifiers := base.freshness
    have hspine : nfKey nf ∉ spine := by
      intro hmem
      have hkeys : nfKey nf ∈ keysOf S8 nfTreeRoot :=
        (keysOf_eq_spine S8 nfTreeRoot spine spineCommits (nfKey nf)).mpr hmem
      obtain ⟨nf', hnf', hkeq⟩ := (treeEnc (nfKey nf)).mp hkeys
      exact hfresh (nfKey_injective hkeq ▸ hnf')
    obtain ⟨g, hv⟩ := gapOpen_complete S8 nfTreeRoot spine (nfKey nf) spineCommits hspine
    have henc : noteSpendFreshEncodes S8 compressN pre post nf actor spendProof :=
      noteSpendFresh_of_base_open S8 compressN pre post nf actor spendProof base
        nfTreeRoot spine treeEnc spineCommits g hv
    exact ⟨henc,
      noteSpendFresh_descriptorRefines S8 compressN hN pre post nf actor spendProof henc,
      noteSpendFresh_freshness S8 compressN pre post nf actor spendProof henc⟩

#assert_axioms gap_positions
#assert_axioms gapOpen_complete
#assert_axioms noteSpendFresh_accepts_iff
#assert_axioms noteSpendFresh_accepts_fresh
#assert_axioms noteSpendFresh_of_base_open
#assert_axioms noteSpendFresh_bridge

/-! ## §5 — the mutation canary (load-bearing witnesses) + a run-through of the `⟺`. -/

/-- **CANARY — the `treeEnc` carrier is load-bearing (the `→` of the iff).** With an UNFAITHFUL tree, a
valid non-membership open of `nfKey nf` (here the trivial empty-tree gap) COEXISTS with `nf ∈ nulls`. So a
valid gap does NOT by itself entail `nf ∉ nulls`; only `NullifierTreeEncodes` (which is FALSE for this
pairing — `keysOf ∅ ≠ {nfKey nf}`) rules it out. Deleting the `treeEnc` carrier from `freshness_forced`
would admit this double-spend. (Contrast `noteSpendFresh_gapOpen_unsat_on_double`, which HAS `treeEnc`
and REJECTS the double-spend.) -/
theorem carrier_load_bearing (S8 : Cap8Scheme) (root : Digest8) (nf : Nat) :
    ∃ (nulls : List Nat) (g : GapOpen S8 root (nfKey nf)),
      nf ∈ nulls ∧ g.coversSpine ([] : List ℤ) :=
  ⟨[nf], GapOpen.empty, by simp, rfl⟩

/-- **CANARY — the freshness premise is load-bearing (the `←` of the iff / completeness).** A PRESENT key
admits NO valid covering gap: a fake gap would have to EXCLUDE a member, impossible via
`GapOpen.excludesSpine`. So `gapOpen_complete`'s `k ∉ spine` premise cannot be dropped — a non-fresh `nf`
(one whose key is in the committed spine) has no accepting open. -/
theorem gap_needs_freshness (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ) (k : ℤ)
    (hs : Sorted spine) (hmem : k ∈ spine) (g : GapOpen S8 root k) :
    ¬ g.coversSpine spine :=
  fun hv => g.excludesSpine hs hv hmem

/-- **TEETH — the spec is TWO-VALUED, in-circuit.** A DOUBLE-SPEND (`nf ∈ nulls`) under a FAITHFUL tree
admits NO valid gap open — the freshness accept genuinely discriminates (a `True`/`P → P` bridge could
not). Reuses the committed `noteSpendFresh_gapOpen_unsat_on_double`. -/
theorem accepts_double_teeth (S8 : Cap8Scheme) (root : Digest8) (nulls : List Nat) (nf : Nat)
    (spine : List ℤ) (henc : NullifierTreeEncodes S8 root nulls) (hc : SpineCommits S8 root spine)
    (hdouble : nf ∈ nulls) (g : GapOpen S8 root (nfKey nf)) (hv : g.coversSpine spine) : False :=
  noteSpendFresh_gapOpen_unsat_on_double S8 root nulls nf spine henc hc hdouble g hv

/-- **THE `⟺` RUN END-TO-END on a concrete instance (the `→` / soundness leg).** Under the named carrier
bundle over a CONCRETE nullifier set `[10, 20, 30]`, a valid non-membership open of `nfKey 25` makes the
descriptor ACCEPT, and `noteSpendFresh_accepts_iff` turns the acceptance into the literal
`25 ∉ [10, 20, 30]` — DERIVED through the tree-absence → nullifier-absence chain, not by `decide`. Not a
hollow green. -/
theorem accepts_iff_demo (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ)
    (C : NoteFreshCarriers S8 root [10, 20, 30] spine)
    (g : GapOpen S8 root (nfKey 25)) (hv : g.coversSpine spine) :
    (25 : Nat) ∉ ([10, 20, 30] : List Nat) :=
  noteSpendFresh_accepts_fresh C ⟨g, hv⟩

/-- **THE `⟺` RUN END-TO-END on a concrete instance (the `←` / completeness leg).** Under the same bundle,
the genuinely-fresh `25 ∉ [10, 20, 30]` (decidable) drives `gapOpen_complete` to CONSTRUCT the accepting
gap open — the forward construction runs on concrete data. -/
theorem constructs_demo (S8 : Cap8Scheme) (root : Digest8) (spine : List ℤ)
    (C : NoteFreshCarriers S8 root [10, 20, 30] spine) :
    NoteFreshAccepts S8 root 25 spine :=
  (noteSpendFresh_accepts_iff S8 root [10, 20, 30] 25 spine C).mpr (by decide)

#assert_axioms carrier_load_bearing
#assert_axioms gap_needs_freshness
#assert_axioms accepts_double_teeth
#assert_axioms accepts_iff_demo
#assert_axioms constructs_demo

end Dregg2.Circuit.RotatedKernelRefinementNotesFreshBridge
