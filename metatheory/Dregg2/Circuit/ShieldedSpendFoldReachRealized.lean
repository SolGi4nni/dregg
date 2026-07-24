/-
# Dregg2.Circuit.ShieldedSpendFoldReachRealized — the `FoldReachIsMember` committed-accumulator
# REALIZATION (the §B residual of `ShieldedSpendPortResidual`, closed honestly).

**This is Lean-authored AIR discharge, downstream of the emitted objects.** No new descriptor, no
deployed-code touch: theorems over `Emit.ShieldedSpendDescriptor.shieldedSpendDesc` + the landed
accumulator modules (`SortedTreeNonMembershipHeap8` / `DeployedHeapTree`).

`ShieldedSpendPortResidual.noteAccumulatorCR_of_hashFloor` reduced the ∀-leaf `NoteAccumulatorCR`
floor to `FoldReachIsMember` — "only a genuinely-committed member folds to the committed root" —
and named its realization (a REAL committed accumulator + the standard Poseidon2 second-preimage
floor) as the residual. This module supplies that realization, and in doing so PROVES two
structural facts about the deployed fold shape that reshape the floor:

## The two findings (proved, not narrated)

1. **No leaf/node domain separation ⇒ the ∀-path floor OVERREACHES the committed set**
   (`foldReachIsMember_forces_raw_atom`, `noteAccumulatorCR_forces_raw_atom_note`). The C6
   note-commitment shape `hash [v, as, ow, rd, 0, MARK, 1]` IS the per-level fold shape
   `Hair hash v ⟨as, ow, rd, 0⟩` — one arity-5 `hash_fact` site serves both. So every committed
   chain extends DOWNWARD through the note's own (genuine, known) preimage:
   `foldPath (Hair hash) v (⟨as,ow,rd,0⟩ :: path) = root` — the raw `value` FIELD of the note
   fold-reaches the root. Any member set satisfying the unbounded `FoldReachIsMember` must
   therefore contain the raw field, and `NoteAccumulatorCR` itself forces `IsCommittedNote` of
   that raw field. The ∀-path form is NOT the crypto content; the bounded break-extraction game
   below is.

2. **The emitted fold convention is a CHAIN commitment, not a set commitment.** `Hair` absorbs
   `[current, sib0, sib1, sib2, pos]` — current-FIRST, position-asymmetric — so two DIFFERENT
   leaves opening one root is itself a fact-site collision (`fold_meet`'s break disjunct). The
   realized committed accumulator at a 1-felt root is a SINGLE fold chain (one note + its path,
   root COMPUTED from the data); the MULTI-note committed set lives where it already landed — the
   8-felt `Heap8Scheme` accumulator (`SpineCommits8`/`keysOf8`) — and the two COMPOSE
   (`emitted_accept_spends_note_in_committed_set`).

## What is proved

  * **`fold_meet`** — THE WALK (unconditional, the house or-collides form): two folds meeting at
    one value either thread through one another (one chain is a suffix-extension of the other) or
    hand back a NAMED fact-site collision (`HairBreak` — two different arity-5 absorb blocks with
    equal hash, the SAME floor family as the deployed `Compress8CR`).
  * **`CommittedChain`** — the REAL committed accumulator: the inserted note's full preimage
    `(value, asset, owner, randomness)` + its committed path; `chainRoot` is COMPUTED by folding
    the data (the realizable `compute_canonical_*_root` discipline); `chainMember` is the
    committed value set. Inhabited, computable, non-vacuous.
  * **`foldReach_trichotomy`** — UNCONDITIONAL: anything folding to `chainRoot` is a committed
    chain value, OR descends through the note's genuine preimage to the raw `value` atom (the
    finding-1 overreach, with its exact path structure), OR a `HairBreak` is in hand.
  * **`foldReachIsMember_realized`** — the residual's literal ask: `FoldReachIsMember` holds over
    the realized accumulator with member set `chainMember ∪ {raw value}`, from TWO named standard
    floors: `HairCR` (no fact-site collision — Poseidon2 CR at the deployed arity-5 site) and
    `BaseAtomPreimageFree` (the raw value field is not a fact-hash image — Poseidon2 preimage
    resistance at the accumulator's base atom). The raw-value member is IRREDUCIBLE (finding 1),
    so it is IN the set, not hidden.
  * **`noteAccumulatorCR_realized`** — `NoteAccumulatorCR` via the landed
    `noteAccumulatorCR_of_hashFloor` reduction at the realized member set; the two construction
    facts it additionally needs (`chainMember ⊆ IsCommittedNote`, raw value note-shaped) are
    carried EXPLICITLY — and `noteAccumulatorCR_forces_raw_atom_note` proves the second is FORCED
    by `NoteAccumulatorCR` itself, so carrying it is honesty, not laundering.
    `chain_members_are_notes_of_zero_pos` discharges the first for pos-0 (padding-fold-shaped)
    paths — the deployed forward-chained padding convention.
  * **`emitted_chain_is_exact_foldPath`** — THE FIELD-REDUCTION IDENTIFICATION: on a
    canonical-BabyBear-rep trace (`CanonicalCells` — every `current` cell and the committed PI in
    `[0, p)`; `CanonicalHash` — the hash lands canonical), the emitted mod-p membership chain
    (`emitted_membership_chain`'s C3-chip + C5-window content) COLLAPSES to the exact-ℤ
    `foldPath` the accumulator consumes: `foldPath (Hair hash) current₀ (emittedPath t) =
    pi[committed_root]`. The mod-p chain and the exact fold coincide on the deployed denotation.
  * **`emitted_accept_is_committed_member_or_break`** — THE CAPSTONE: a satisfying
    `shieldedSpendDesc` trace (sound chip table, canonical reps) against a real `CommittedChain`
    whose root is the committed PI spends a committed chain value, or exhibits a fact-hash
    preimage of the accumulator's base atom, or a `HairBreak` — the C6 note-shape of the accepted
    leaf (`spend_relation_row0`) converts even the degenerate descent into a NAMED preimage
    event.
  * **`emitted_accept_spends_note_in_committed_set`** — THE SET COMPOSITION: the capstone
    composed with the LANDED 8-felt accumulator: if the insert discipline recorded the committed
    note's key in the spine bound by `SpineCommits8` (the one landed Poseidon2/`Compress8CR`
    carrier), the accepted spend's leaf is the committed note AND its key sits in
    `keysOf8 S8 root8` — `NoteAccumulatorCR`'s content now rests ONLY on deployed Poseidon2 hash
    floors (fact-site CR + base-atom preimage + the landed `SpineCommits8` carrier).

## The named floors (all standard, none laundered)

`HairCR` (fact-site collision-freeness; at the deployed 1-felt ~31-bit width this is
2^15.5-collidable — the #17 width residual PRICES it, this module makes the width-dependence
explicit) · `BaseAtomPreimageFree` (preimage at the base atom, same width caveat) ·
`SpineCommits8` (the landed spine↔root carrier) · `ChipTableSound` (the chip AIR's own
faithfulness, inherited) · `CanonicalCells`/`CanonicalHash` (denotation facts of the BabyBear
trace, not crypto). Hypotheses, never axioms.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.ShieldedSpendPortResidual

namespace Dregg2.Circuit.ShieldedSpendFoldReachRealized

open Dregg2.Circuit.DescriptorIR2 (VmTrace Satisfied2 ChipTableSound TableId zeroAsg)
open Dregg2.Circuit.ShieldedMerkleRootPin (Level foldPath)
open Dregg2.Circuit.ShieldedSpendPortDischarge (Hair IsCommittedNote NoteAccumulatorCR zTf_sound)
open Dregg2.Circuit.ShieldedSpendPortResidual
  (P FoldReachIsMember curAt levelAt modp_eq_of_bounds noteAccumulatorCR_of_hashFloor
   emitted_fold_step_all_rows emitted_chain_continuity)
open Dregg2.Circuit.Emit.ShieldedSpendDescriptor
  (shieldedSpendDesc NS_FACT_MARK cCUR cVAL cASSET cOWNER cRAND cLEAF piCOMMITTED
   spend_relation_row0 root_is_pinned hzero zTrace zero_witness_satisfies)
open Dregg2.Circuit.SortedTreeNonMembershipHeap8 (SpineCommits8 keysOf8 keysOf8_eq_spine)
open Dregg2.Circuit.DeployedHeapTree (Heap8Scheme)
open Dregg2.Circuit.DeployedCapTree (Digest8)

set_option autoImplicit false

/-! ## §0 — fold plumbing. -/

/-- Peeling the TOP level off a fold: `foldPath H x (p ++ [l]) = H (foldPath H x p) l`. -/
theorem foldPath_concat (H : ℤ → Level → ℤ) (x : ℤ) (p : List Level) (l : Level) :
    foldPath H x (p ++ [l]) = H (foldPath H x p) l := by
  induction p generalizing x with
  | nil => rfl
  | cons a t ih =>
    simp only [List.cons_append, foldPath]
    exact ih (H x a)

/-! ## §1 — the named break: a genuine collision of the deployed arity-5 fact site. -/

/-- **`HairBreak hash`** — a NAMED collision of the emitted Poseidon2 `hash_fact` fold site: two
DIFFERENT `(current, level)` inputs — hence two different arity-5 absorb blocks — with equal hash.
The SAME floor family as the deployed `Compress8CR` (a collision of the deployed chip at named
blocks), at the spend fold's own site. At the deployed 1-felt (~31-bit) width this event is
2^15.5-birthday-reachable — the #17 width residual prices exactly this. -/
def HairBreak (hash : List ℤ → ℤ) : Prop :=
  ∃ x₁ l₁ x₂ l₂, ¬ (x₁ = x₂ ∧ l₁ = l₂) ∧ Hair hash x₁ l₁ = Hair hash x₂ l₂

/-- A `HairBreak` NAMES its colliding absorb blocks: two different `List ℤ` inputs with equal
hash — the concrete collision-pair data every `Coll8`-style consumer expects. -/
theorem hairBreak_names_absorb_collision (hash : List ℤ → ℤ) (hb : HairBreak hash) :
    ∃ L₁ L₂ : List ℤ, L₁ ≠ L₂ ∧ hash L₁ = hash L₂ := by
  obtain ⟨x₁, l₁, x₂, l₂, hne, heq⟩ := hb
  obtain ⟨a₁, b₁, c₁, d₁⟩ := l₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := l₂
  refine ⟨[x₁, a₁, b₁, c₁, d₁, NS_FACT_MARK, 1],
          [x₂, a₂, b₂, c₂, d₂, NS_FACT_MARK, 1], ?_, heq⟩
  intro hL
  simp only [List.cons.injEq, and_true] at hL
  obtain ⟨hx, h0, h1, h2, h3⟩ := hL
  exact hne ⟨hx, by rw [h0, h1, h2, h3]⟩

/-! ## §2 — THE WALK (`fold_meet`): two folds meeting at one value either thread through one
another or hand back a named fact-site collision. Unconditional. -/

theorem fold_meet (hash : List ℤ → ℤ) (Q : List Level) :
    ∀ (Pc : List Level) (u c : ℤ),
      foldPath (Hair hash) u Q = foldPath (Hair hash) c Pc →
      (∃ Q₀, Q = Q₀ ++ Pc ∧ foldPath (Hair hash) u Q₀ = c)
      ∨ (∃ P₀, Pc = P₀ ++ Q ∧ foldPath (Hair hash) c P₀ = u)
      ∨ HairBreak hash := by
  induction Q using List.reverseRecOn with
  | nil =>
    intro Pc u c h
    refine Or.inr (Or.inl ⟨Pc, (List.append_nil Pc).symm, ?_⟩)
    simpa [foldPath] using h.symm
  | append_singleton Qs m ih =>
    intro Pc u c h
    rcases Pc.eq_nil_or_concat' with rfl | ⟨Ps, l, rfl⟩
    · refine Or.inl ⟨Qs ++ [m], (List.append_nil _).symm, ?_⟩
      simpa [foldPath] using h
    · rw [foldPath_concat, foldPath_concat] at h
      by_cases hpair : foldPath (Hair hash) u Qs = foldPath (Hair hash) c Ps ∧ m = l
      · obtain ⟨hAB, rfl⟩ := hpair
        rcases ih Ps u c hAB with ⟨Q₀, hQ, hf⟩ | ⟨P₀, hP, hf⟩ | hbr
        · refine Or.inl ⟨Q₀, ?_, hf⟩
          rw [hQ, List.append_assoc]
        · refine Or.inr (Or.inl ⟨P₀, ?_, hf⟩)
          rw [hP, List.append_assoc]
        · exact Or.inr (Or.inr hbr)
      · exact Or.inr (Or.inr
          ⟨foldPath (Hair hash) u Qs, m, foldPath (Hair hash) c Ps, l, hpair, h⟩)

/-! ## §3 — the REAL committed accumulator: one inserted note + its committed path; the root is
COMPUTED from the data. -/

/-- **`CommittedChain`** — the committed accumulator's DATA: the inserted note's full preimage
and the committed fold path (the insert discipline's record). Pure data — the root is derived,
never assumed. -/
structure CommittedChain where
  value : ℤ
  asset : ℤ
  owner : ℤ
  randomness : ℤ
  path : List Level

/-- The note-commitment PREIMAGE level: absorbing `⟨asset, owner, randomness⟩` at position 0 is
EXACTLY the C6 note-commitment hash — the fold shape and the note shape are one site (finding 1). -/
def preLevel (a : CommittedChain) : Level := ⟨a.asset, a.owner, a.randomness, 0⟩

/-- The committed note commitment: `hash_fact(value, [asset, owner, randomness])` — BYTE-SHAPE
identical to the emitted C6a site, and definitionally a `Hair` step from the raw value atom. -/
def leafCommitOf (hash : List ℤ → ℤ) (a : CommittedChain) : ℤ :=
  Hair hash a.value (preLevel a)

/-- The C6 note shape, explicitly: `leafCommitOf = hash [v, as, ow, rd, 0, MARK, 1]`. -/
theorem leafCommitOf_eq (hash : List ℤ → ℤ) (a : CommittedChain) :
    leafCommitOf hash a
      = hash [a.value, a.asset, a.owner, a.randomness, 0, NS_FACT_MARK, 1] := rfl

/-- **`chainRoot`** — the committed root, COMPUTED by folding the committed data (the realizable
`compute_canonical_*_root` discipline; no abstract binding assumption). -/
def chainRoot (hash : List ℤ → ℤ) (a : CommittedChain) : ℤ :=
  foldPath (Hair hash) (leafCommitOf hash a) a.path

/-- **`chainMember`** — the committed value set of this root: the note commitment and its fold
ancestors along the committed path (each a prefix-fold of the committed data). -/
def chainMember (hash : List ℤ → ℤ) (a : CommittedChain) (x : ℤ) : Prop :=
  ∃ P₀ P₁, a.path = P₀ ++ P₁ ∧ foldPath (Hair hash) (leafCommitOf hash a) P₀ = x

/-- A PROPER ancestor: a committed chain value strictly above the leaf. -/
def properAncestor (hash : List ℤ → ℤ) (a : CommittedChain) (x : ℤ) : Prop :=
  ∃ P₀ P₁, P₀ ≠ [] ∧ a.path = P₀ ++ P₁ ∧ foldPath (Hair hash) (leafCommitOf hash a) P₀ = x

/-- The committed note commitment IS a member (the leaf, prefix `[]`). -/
theorem member_leaf (hash : List ℤ → ℤ) (a : CommittedChain) :
    chainMember hash a (leafCommitOf hash a) :=
  ⟨[], a.path, rfl, rfl⟩

/-- The root IS a member (the full-path fold — `foldPath x [] = x` makes this forced). -/
theorem member_root (hash : List ℤ → ℤ) (a : CommittedChain) :
    chainMember hash a (chainRoot hash a) :=
  ⟨a.path, [], (List.append_nil _).symm, rfl⟩

/-- The committed note commitment is a genuine `IsCommittedNote` (the C6 shape, witnessed by the
accumulator's own preimage record). -/
theorem leafCommitOf_isCommittedNote (hash : List ℤ → ℤ) (a : CommittedChain) :
    IsCommittedNote hash (leafCommitOf hash a) := by
  refine ⟨a.value, a.asset, a.owner, a.randomness, ?_⟩
  rw [leafCommitOf_eq]

/-! ## §4 — THE TRICHOTOMY (unconditional): fold-reaching the committed root means committed
member, or the preimage DESCENT (finding 1, with its exact structure), or a named break. -/

theorem foldReach_trichotomy (hash : List ℤ → ℤ) (a : CommittedChain) (u : ℤ)
    (Q : List Level) (h : foldPath (Hair hash) u Q = chainRoot hash a) :
    chainMember hash a u
    ∨ (∃ Q₁, Q = Q₁ ++ preLevel a :: a.path ∧ foldPath (Hair hash) u Q₁ = a.value)
    ∨ HairBreak hash := by
  rcases fold_meet hash Q a.path u (leafCommitOf hash a) h with
    ⟨Q₀, hQ, hf⟩ | ⟨P₀, hP, hf⟩ | hbr
  · -- u folds INTO the committed leaf through Q₀: peel the last step against the note preimage.
    rcases Q₀.eq_nil_or_concat' with rfl | ⟨Q₂, lst, rfl⟩
    · exact Or.inl ⟨[], a.path, rfl, hf.symm⟩
    · rw [foldPath_concat] at hf
      by_cases hpair : foldPath (Hair hash) u Q₂ = a.value ∧ lst = preLevel a
      · obtain ⟨hval, rfl⟩ := hpair
        refine Or.inr (Or.inl ⟨Q₂, ?_, hval⟩)
        rw [hQ, List.append_assoc]
        rfl
      · exact Or.inr (Or.inr
          ⟨foldPath (Hair hash) u Q₂, lst, a.value, preLevel a, hpair, hf⟩)
  · exact Or.inl ⟨P₀, Q, hP, hf⟩
  · exact Or.inr (Or.inr hbr)

/-- Non-vacuity of the DESCENT pole: the raw value atom genuinely fold-reaches the root through
the note's own preimage — definitionally. This is finding 1 as a witness, not a warning. -/
theorem descent_reaches_root (hash : List ℤ → ℤ) (a : CommittedChain) :
    foldPath (Hair hash) a.value (preLevel a :: a.path) = chainRoot hash a := rfl

/-! ## §5 — the FORCING theorems: the ∀-path floor overreaches the committed set (finding 1). -/

/-- **THE OVERREACH (`foldReachIsMember_forces_raw_atom`).** ANY member set satisfying the
unbounded `FoldReachIsMember` at a realized root must contain the note's raw `value` FIELD —
which is not a committed note, merely the first slot of its preimage. The ∀-path floor cannot
hold over "the committed notes"; the bounded break-game below is the true crypto content. -/
theorem foldReachIsMember_forces_raw_atom (hash : List ℤ → ℤ) (a : CommittedChain)
    (member : ℤ → Prop)
    (h : FoldReachIsMember hash (chainRoot hash a) member) : member a.value :=
  h a.value (preLevel a :: a.path) (descent_reaches_root hash a)

/-- **THE OVERREACH at `NoteAccumulatorCR` itself.** The discharge module's ∀-leaf floor FORCES
`IsCommittedNote` of the raw value field — so any realization carrying that fact as a hypothesis
is carrying what the floor itself demands, not smuggling strength in. -/
theorem noteAccumulatorCR_forces_raw_atom_note (hash : List ℤ → ℤ) (a : CommittedChain)
    (h : NoteAccumulatorCR hash (chainRoot hash a)) : IsCommittedNote hash a.value :=
  h a.value (preLevel a :: a.path) (descent_reaches_root hash a)

/-! ## §6 — the REALIZED floor: `FoldReachIsMember` from two named standard Poseidon2 floors. -/

/-- Fact-site collision-freeness — the standard Poseidon2 CR floor at the emitted arity-5 site
(the `Compress8CR` family shape). NAMED hypothesis; at 1-felt width it is 2^15.5-collidable. -/
def HairCR (hash : List ℤ → ℤ) : Prop := ¬ HairBreak hash

/-- Preimage-freeness at the accumulator's BASE ATOM: the committed note's raw `value` field is
not itself a fact-hash image. The standard preimage floor, localized to the one value the
descent (finding 1) bottoms at. -/
def BaseAtomPreimageFree (hash : List ℤ → ℤ) (a : CommittedChain) : Prop :=
  ∀ w l, Hair hash w l ≠ a.value

/-- **⚑ THE REALIZATION (`foldReachIsMember_realized`).** `FoldReachIsMember` over the REAL
committed accumulator, from the two named floors. The member set is the committed chain values
PLUS the raw value atom — the latter is irreducible (`foldReachIsMember_forces_raw_atom`), so it
is stated IN the set, not hidden behind it. -/
theorem foldReachIsMember_realized (hash : List ℤ → ℤ) (a : CommittedChain)
    (hCR : HairCR hash) (hPF : BaseAtomPreimageFree hash a) :
    FoldReachIsMember hash (chainRoot hash a)
      (fun x => chainMember hash a x ∨ x = a.value) := by
  intro leaf path hfold
  rcases foldReach_trichotomy hash a leaf path hfold with hm | ⟨Q₁, hQ, hg⟩ | hbr
  · exact Or.inl hm
  · rcases Q₁.eq_nil_or_concat' with rfl | ⟨Q₂, lst, rfl⟩
    · exact Or.inr (by simpa [foldPath] using hg)
    · rw [foldPath_concat] at hg
      exact absurd hg (hPF _ _)
  · exact absurd hbr hCR

/-- Pos-0 paths (the deployed forward-chained PADDING convention — every level absorbs at
position 0) make every chain value note-shaped: each fold step IS a C6-shaped image. Discharges
`noteAccumulatorCR_realized`'s chain-side construction fact for padding-shaped accumulators. -/
theorem chain_members_are_notes_of_zero_pos (hash : List ℤ → ℤ) (a : CommittedChain)
    (hpos : ∀ l ∈ a.path, l.pos = 0) :
    ∀ x, chainMember hash a x → IsCommittedNote hash x := by
  rintro x ⟨P₀, P₁, hsplit, rfl⟩
  rcases P₀.eq_nil_or_concat' with rfl | ⟨Ps, lst, rfl⟩
  · exact leafCommitOf_isCommittedNote hash a
  · rw [foldPath_concat]
    have hlst : lst.pos = 0 := hpos lst (by rw [hsplit]; simp)
    refine ⟨foldPath (Hair hash) (leafCommitOf hash a) Ps,
            lst.sib0, lst.sib1, lst.sib2, ?_⟩
    show Hair hash _ lst ≡ _ [ZMOD _]
    simp only [Hair, hlst]
    exact Int.ModEq.refl _

/-- **⚑ `NoteAccumulatorCR`, REALIZED.** Through the landed `noteAccumulatorCR_of_hashFloor`
reduction at the realized member set. The two extra construction facts are EXPLICIT — and the
second is FORCED by the conclusion itself (`noteAccumulatorCR_forces_raw_atom_note`), so this is
the honest full price of the ∀-leaf floor: two named hash floors + what the floor already
demands. -/
theorem noteAccumulatorCR_realized (hash : List ℤ → ℤ) (a : CommittedChain)
    (hCR : HairCR hash) (hPF : BaseAtomPreimageFree hash a)
    (hchain_notes : ∀ x, chainMember hash a x → IsCommittedNote hash x)
    (hatom_note : IsCommittedNote hash a.value) :
    NoteAccumulatorCR hash (chainRoot hash a) := by
  refine noteAccumulatorCR_of_hashFloor hash (chainRoot hash a)
    (fun x => chainMember hash a x ∨ x = a.value) ?_
    (foldReachIsMember_realized hash a hCR hPF)
  rintro leaf (hm | rfl)
  · exact hchain_notes leaf hm
  · exact hatom_note

/-! ## §7 — THE FIELD-REDUCTION IDENTIFICATION: the emitted mod-p membership chain IS the exact
`foldPath` on the canonical-BabyBear-rep trace. -/

/-- Canonical BabyBear representation of the fold-relevant cells: every `current` cell and the
committed-root PI lie in `[0, p)`. A DENOTATION fact of the deployed trace (BabyBear cells are
canonical), not crypto. -/
def CanonicalCells (t : VmTrace) : Prop :=
  (∀ i, i < t.rows.length → 0 ≤ curAt t i ∧ curAt t i < P)
  ∧ (0 ≤ t.pub piCOMMITTED ∧ t.pub piCOMMITTED < P)

/-- The hash lands canonical (`hash_fact` outputs a BabyBear element). Denotation, not crypto. -/
def CanonicalHash (hash : List ℤ → ℤ) : Prop := ∀ L, 0 ≤ hash L ∧ hash L < P

theorem hair_canonical {hash : List ℤ → ℤ} (hcH : CanonicalHash hash) (x : ℤ) (l : Level) :
    0 ≤ Hair hash x l ∧ Hair hash x l < P :=
  hcH [x, l.sib0, l.sib1, l.sib2, l.pos, NS_FACT_MARK, 1]

/-- The path the emitted trace carries: one `Level` per row. This is EXACTLY the path the
accumulator's fold consumes. -/
def emittedPath (t : VmTrace) : List Level :=
  (List.range t.rows.length).map (levelAt t)

/-- The prefix folds of the emitted path land ON the trace's own `current` cells — the mod-p
chain junctions (C5) collapse to exact equalities under canonical reps. -/
theorem emitted_prefix_fold (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace)
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hcT : CanonicalCells t) (hcH : CanonicalHash hash) :
    ∀ j, j < t.rows.length →
      foldPath (Hair hash) (curAt t 0) ((List.range j).map (levelAt t)) = curAt t j := by
  intro j
  induction j with
  | zero => intro _; simp [foldPath]
  | succ j ih =>
    intro hj1
    have hj : j < t.rows.length := by omega
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil]
    rw [foldPath_concat, ih hj]
    have hstep := emitted_fold_step_all_rows hash minit mfin maddrs t hsat hChip j hj
    have hcont := emitted_chain_continuity hash minit mfin maddrs t hsat j hj1
    rw [hstep] at hcont
    exact (modp_eq_of_bounds _ _ (hcT.1 (j + 1) hj1).1 (hcT.1 (j + 1) hj1).2
      (hair_canonical hcH _ _).1 (hair_canonical hcH _ _).2 hcont).symm

/-- **⚑ THE IDENTIFICATION (`emitted_chain_is_exact_foldPath`).** On the canonical-BabyBear-rep
trace the emitted mod-p membership chain IS the exact `foldPath` reaching the committed-root PI —
precisely the equation the accumulator's `FoldReachIsMember` consumes. The `≡ [ZMOD p]`
junctions of `emitted_membership_chain` and the exact fold of `ShieldedMerkleRootPin` coincide
on the deployed denotation. -/
theorem emitted_chain_is_exact_foldPath (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hcT : CanonicalCells t) (hcH : CanonicalHash hash) :
    foldPath (Hair hash) (curAt t 0) (emittedPath t) = t.pub piCOMMITTED := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons x l => simp
  have hsplit : List.range t.rows.length
      = List.range (t.rows.length - 1) ++ [t.rows.length - 1] := by
    rw [← List.range_succ]
    congr 1
    omega
  simp only [emittedPath]
  rw [hsplit, List.map_append, List.map_cons, List.map_nil, foldPath_concat,
    emitted_prefix_fold hash minit mfin maddrs t hsat hChip hcT hcH
      (t.rows.length - 1) (by omega)]
  have hstep := emitted_fold_step_all_rows hash minit mfin maddrs t hsat hChip
    (t.rows.length - 1) (by omega)
  have hpin := (root_is_pinned hash minit mfin maddrs t hne hsat).2.1
  rw [hstep] at hpin
  exact modp_eq_of_bounds _ _ (hair_canonical hcH _ _).1 (hair_canonical hcH _ _).2
    hcT.2.1 hcT.2.2 hpin

/-! ## §8 — THE CAPSTONE: the emitted accepted spend against the REAL committed accumulator. -/

/-- **⚑ THE CAPSTONE (`emitted_accept_is_committed_member_or_break`).** A satisfying
`shieldedSpendDesc` trace (sound chip table, canonical reps) whose committed-root PI is a real
`CommittedChain`'s computed root spends a COMMITTED CHAIN VALUE — or exhibits, by name, a
fact-hash preimage of the accumulator's base atom, or a fact-site collision. The C6 note shape
of the accepted leaf (`spend_relation_row0`) converts the degenerate descent (`leaf = raw atom`)
into a concrete preimage event: the leaf's own C6 opening IS the preimage. -/
theorem emitted_accept_is_committed_member_or_break (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hcT : CanonicalCells t) (hcH : CanonicalHash hash)
    (acc : CommittedChain) (hroot : chainRoot hash acc = t.pub piCOMMITTED) :
    chainMember hash acc (curAt t 0)
    ∨ (∃ w l, Hair hash w l = acc.value)
    ∨ HairBreak hash := by
  have hpos : 0 < t.rows.length := by
    cases hr : t.rows with
    | nil => exact absurd hr hne
    | cons x l => simp
  have hfold : foldPath (Hair hash) (curAt t 0) (emittedPath t) = chainRoot hash acc := by
    rw [hroot]
    exact emitted_chain_is_exact_foldPath hash minit mfin maddrs t hne hsat hChip hcT hcH
  rcases foldReach_trichotomy hash acc _ _ hfold with hm | ⟨Q₁, hQ, hg⟩ | hbr
  · exact Or.inl hm
  · refine Or.inr (Or.inl ?_)
    rcases Q₁.eq_nil_or_concat' with rfl | ⟨Q₂, lst, rfl⟩
    · -- degenerate descent: the accepted leaf IS the raw atom — its C6 opening is the preimage.
      have hg0 : curAt t 0 = acc.value := hg
      have hrel := spend_relation_row0 hash minit mfin maddrs t hne hsat hChip
      have hLEAFc : 0 ≤ (t.rows.getD 0 zeroAsg) cLEAF
          ∧ (t.rows.getD 0 zeroAsg) cLEAF < P := by
        rw [hrel.2.2.1]; exact hcH _
      have hcur : (t.rows.getD 0 zeroAsg) cCUR = (t.rows.getD 0 zeroAsg) cLEAF :=
        modp_eq_of_bounds _ _ (hcT.1 0 hpos).1 (hcT.1 0 hpos).2 hLEAFc.1 hLEAFc.2
          hrel.2.2.2.2.1
      refine ⟨(t.rows.getD 0 zeroAsg) cVAL,
              ⟨(t.rows.getD 0 zeroAsg) cASSET, (t.rows.getD 0 zeroAsg) cOWNER,
               (t.rows.getD 0 zeroAsg) cRAND, 0⟩, ?_⟩
      calc Hair hash ((t.rows.getD 0 zeroAsg) cVAL)
              ⟨(t.rows.getD 0 zeroAsg) cASSET, (t.rows.getD 0 zeroAsg) cOWNER,
               (t.rows.getD 0 zeroAsg) cRAND, 0⟩
          = (t.rows.getD 0 zeroAsg) cLEAF := (hrel.2.2.1).symm
        _ = (t.rows.getD 0 zeroAsg) cCUR := hcur.symm
        _ = acc.value := hg0
    · rw [foldPath_concat] at hg
      exact ⟨_, lst, hg⟩
  · exact Or.inr (Or.inr hbr)

/-! ## §9 — THE SET COMPOSITION: the capstone meets the LANDED 8-felt accumulator. -/

/-- **⚑ THE COMPOSITION (`emitted_accept_spends_note_in_committed_set`).** The accepted spend
against the realized chain, COMPOSED with the landed `Heap8Scheme` sorted-tree accumulator: if
the insert discipline recorded the committed note's key (`addrFold leafCommit`) in the spine
bound by `SpineCommits8` — the ONE landed Poseidon2/`Compress8CR` carrier — then the accepted
leaf IS the committed note and its key sits in the committed set `keysOf8 S8 root8`; or it is a
proper chain ancestor (named); or the base-atom preimage / fact-site break is in hand.
`NoteAccumulatorCR`'s content, resting only on deployed Poseidon2 hash floors. -/
theorem emitted_accept_spends_note_in_committed_set (hash : List ℤ → ℤ) (minit : ℤ → ℤ)
    (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hsat : Satisfied2 hash shieldedSpendDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf TableId.poseidon2))
    (hcT : CanonicalCells t) (hcH : CanonicalHash hash)
    (acc : CommittedChain) (hroot : chainRoot hash acc = t.pub piCOMMITTED)
    (S8 : Heap8Scheme) (root8 : Digest8) (spine : List ℤ)
    (hcommits : SpineCommits8 S8 root8 spine)
    (addrFold : ℤ → ℤ)
    (hins : addrFold (leafCommitOf hash acc) ∈ spine) :
    (curAt t 0 = leafCommitOf hash acc ∧ addrFold (curAt t 0) ∈ keysOf8 S8 root8)
    ∨ properAncestor hash acc (curAt t 0)
    ∨ (∃ w l, Hair hash w l = acc.value)
    ∨ HairBreak hash := by
  rcases emitted_accept_is_committed_member_or_break hash minit mfin maddrs t hne hsat hChip
    hcT hcH acc hroot with hm | hp | hb
  · obtain ⟨P₀, P₁, hsplit, hfold⟩ := hm
    by_cases hP0 : P₀ = []
    · subst hP0
      have hleaf : leafCommitOf hash acc = curAt t 0 := hfold
      refine Or.inl ⟨hleaf.symm, ?_⟩
      rw [← hleaf]
      exact (keysOf8_eq_spine S8 root8 spine hcommits _).mpr hins
    · exact Or.inr (Or.inl ⟨P₀, P₁, hP0, hsplit, hfold⟩)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hb))

/-! ## §10 — non-vacuity: both poles inhabited; the capstone FIRES on the emit module's witness. -/

/-- The break pole is REACHABLE across hashes: the constant hash breaks (so the disjunct is not
a decorative `False`). At an injective-on-blocks hash it is refutable — the two poles are both
live. -/
theorem hairBreak_hzero : HairBreak hzero :=
  ⟨0, ⟨0, 0, 0, 0⟩, 1, ⟨0, 0, 0, 0⟩, by simp, rfl⟩

/-- The realized accumulator matching the discharge module's all-zero satisfying witness. -/
def zChain : CommittedChain := ⟨0, 0, 0, 0, []⟩

/-- Its computed root IS the witness's committed-root PI (both zero) — by computation. -/
theorem zChain_root : chainRoot hzero zChain = zTrace.pub piCOMMITTED := rfl

theorem zTrace_canonical : CanonicalCells zTrace := by
  constructor
  · intro i hi
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [zTrace] using hi
      omega
    subst hi0
    exact ⟨le_refl 0, by show (0 : ℤ) < 2013265921; norm_num⟩
  · exact ⟨le_refl 0, by show (0 : ℤ) < 2013265921; norm_num⟩

theorem hzero_canonical : CanonicalHash hzero := by
  intro L
  exact ⟨le_refl 0, by norm_num [hzero]⟩

/-- **The capstone FIRES on the emit module's explicit satisfying witness** — the accepted leaf
really is the committed chain member (the member pole, witnessed directly: both are `0`). -/
theorem capstone_member_pole_fires : chainMember hzero zChain (curAt zTrace 0) := by
  have h : curAt zTrace 0 = leafCommitOf hzero zChain := rfl
  rw [h]
  exact member_leaf hzero zChain

/-- ... and the full capstone pipeline RUNS on that witness (hypotheses all inhabited on a real
trace — the theorem is about a live relation, not an empty one). -/
theorem capstone_runs_on_witness :
    chainMember hzero zChain (curAt zTrace 0)
    ∨ (∃ w l, Hair hzero w l = zChain.value)
    ∨ HairBreak hzero :=
  emitted_accept_is_committed_member_or_break hzero (fun _ => 0) (fun _ => (0, 0)) [] zTrace
    (by simp [zTrace]) zero_witness_satisfies zTf_sound zTrace_canonical hzero_canonical
    zChain zChain_root

/-! ## §11 — axiom hygiene. -/

#assert_axioms foldPath_concat
#assert_axioms hairBreak_names_absorb_collision
#assert_axioms fold_meet
#assert_axioms member_leaf
#assert_axioms member_root
#assert_axioms leafCommitOf_isCommittedNote
#assert_axioms foldReach_trichotomy
#assert_axioms descent_reaches_root
#assert_axioms foldReachIsMember_forces_raw_atom
#assert_axioms noteAccumulatorCR_forces_raw_atom_note
#assert_axioms foldReachIsMember_realized
#assert_axioms chain_members_are_notes_of_zero_pos
#assert_axioms noteAccumulatorCR_realized
#assert_axioms emitted_prefix_fold
#assert_axioms emitted_chain_is_exact_foldPath
#assert_axioms emitted_accept_is_committed_member_or_break
#assert_axioms emitted_accept_spends_note_in_committed_set
#assert_axioms hairBreak_hzero
#assert_axioms zChain_root
#assert_axioms capstone_member_pole_fires
#assert_axioms capstone_runs_on_witness

end Dregg2.Circuit.ShieldedSpendFoldReachRealized
