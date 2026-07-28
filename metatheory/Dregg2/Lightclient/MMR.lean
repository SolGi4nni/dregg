/-
# Dregg2.Lightclient.MMR — the receipt index as an append-only range structure (Merkle Mountain Range).

THE EPOCH's per-structure choice for the receipt index (.docs-history-noclaude/EPOCH-DESIGN.md): history keys are
DENSE POSITIONS, so the index does not need a sorted map — it needs an append-only structure where
completeness holds BY CONSTRUCTION. This module is the MMR theory that specializes the
`HistoryIndex`/`AttestedQuery` non-omission machinery onto exactly that structure:

  * **the forest** (§2): peaks are PERFECT Poseidon2 trees; `push` is the carry — merge while the
    youngest peak has equal height, else prepend. `peaksOf L = L.foldl appendLeaf []`, so the
    peak update IS the append algorithm (amortized O(1): each append touches one new height-0 peak
    plus carries, and `peaksOf (L ++ [v]) = push (peaksOf L) (.leaf v)` holds by `foldl` — the
    O(1) incremental form is DEFINITIONALLY the recomputation, `peaksOf_append`);
  * **the recovery keystone** `forestLeaves_peaksOf`: the forest's leaves, read oldest-first, are
    EXACTLY the appended log — no entry moves once appended (prefix stability by construction);
  * **the structure theorem** `peaksOf_mountains`: every peak is perfect and heights strictly
    increase from the youngest — the binary decomposition of the log length (so #peaks ≤ log₂ n,
    the succinct frontier the prover carries);
  * **bagging + the root** (§3, §3½): `mroot = bag (peaksOf L)`; **`mroot_binds_or_collides`** — the
    root BINDS the whole log, UNCONDITIONALLY: two logs with equal roots are equal OR the total
    extractor `mrootFind` HANDS BACK the specific pair of sponge inputs that collide. ⚑ CUTOVER
    2026-07-25, COMPLETED 2026-07-28: the headline used to be `mroot_injective` under the
    `Poseidon2SpongeCR` floor, which `Storage.DeployedFloorRefuted.deployed_floor_false` REFUTES at
    the deployed hash by `rfl` — so it said nothing about deployment. Between those two dates
    `mroot_injective` / `bag_injective` / `PTree.hashOf_injective` were RETAINED as one-line
    "strength bridges". **They are now DELETED, and the reason is that their CONCLUSIONS are false at
    the deployed hash too, not only their premises** — `mroot_not_injective_of_singleton_collision`
    (§3¼) turns ONE sponge collision at two singleton preimages into a refutation of
    `mroot_injective`'s exact conclusion, and `Storage.DeployedFloorRegrounded` instantiates it at
    `poseidon2Hash` off the `rfl` collision `deployed_collides`. A false→false theorem is not a
    bridge. What survives is the honest per-instance residual `MRootColl` at the pair `mrootFind`
    NAMES, with all three poles proved (§3¾), and `Storage.DeployedFloorRegrounded` prices that
    residual as an advantage in a real collision GAME;
  * **positional + range openings** (§4): `Opens`/`mrange`; appends preserve prior openings and
    prior ranges VERBATIM (`append_preserves_opens`, `append_preserves_range`);
  * **POSITIONAL COMPLETENESS** (§5): the range protocol needs NO gap openings — positions are
    dense, so the client checks a COUNT (pinned by the committed length) and per-slot openings;
    `range_complete` proves a verifying answer contains EVERY position in the range (positions
    cannot be skipped), `rverifies_iff_exact` the two-sided characterization, `mroot` faces
    (`server_cannot_omit_position`) pin everything to the genuine log;
  * **the bridge** (§6): `light_client_position_non_omission` restates `AttestedQuery`'s
    per-block face over the MMR index — `CommitBindsMMR` is the `CommitBindsIndex` limb
    obligation VERBATIM with `iroot := mroot`, and composes with
    `RecursiveAggregation.light_client_verifies_whole_history` identically. The obligation list
    SHRINKS on this structure: no sorted invariant (`hsorted` is gone — the log is its own
    canonical order) and no gap-opening machinery (density replaces bracketing).

## Axiom hygiene, and the ROM number this module's guarantee is actually worth
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every theorem. **`Poseidon2SpongeCR`
no longer appears in this file at all** (2026-07-28): every root/peak/commit binding is either
hypothesis-free (`*_binds_or_collides`) or carries a per-instance `¬ MRootColl` / `¬ CommitColl`
residual at a pair a TOTAL extractor names. `EngineSound`'s named fields remain hypotheses at §6.

⚑ **THE HONEST NUMBER: ~2^15.5 QUERIES, NOT ~2^123.5.** `PTree.hashOf`, `bag` and `mroot` are all
`… → ℤ` — ONE BabyBear felt — at every log length and every peak height. The MMR widens the ABSORBED
PREIMAGE (peak arity 1 vs 2, bag arity 0/2), never the DIGEST; nothing here is `Digest8`-valued. So on
`Crypto.RomQueryFloor.birthday_bound`'s honest rung the residual costs `(Q² + 1)/‖R‖` with
`‖R‖ = babyBearP ≈ 2^30.9`, i.e. **an adversary reaches probability ~1 at Q ≈ 2^15.5 — a break, not a
bound.** Every ported endpoint below (`mroot_binds_position`, `mroot_binds_range`,
`mroot_pins_rverifies`, `server_cannot_omit_position`, `commit_pins_mmr`,
`light_client_position_non_omission`) reads that same number. The residual is HONEST-BUT-WEAK, which
is exactly the point: the deleted floor read as infinitely strong and was false.

Non-vacuity §7: witnesses TRUE (a complete range answer verifies; the demo forest has the
binary-decomposition shape; **the honest opening discharges BOTH residuals for EVERY hash**) and FALSE
(a skipped position is rejected; a substituted/reordered value is rejected; tamper/truncate/extend/
reorder each MOVE the root). All §7 witnesses are UNCONDITIONAL — none is conditioned on a floor.
-/
import Dregg2.Lightclient.AttestedQuery

namespace Dregg2.Lightclient.MMR

open Dregg2.Substrate.Heap (refSponge)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR SpongeColl)

/-! ## §1 — perfect peak trees.

An MMR peak is a PERFECT binary Poseidon2 tree over a contiguous chunk of the log. The model keeps
the TREES (the implementation keeps only their hashes; `hashOf` is the projection), so leaf
recovery is a function and root injectivity reduces to hash injectivity structurally. -/

/-- A peak tree: a leaf holds one log entry (a receipt-commitment felt); a node is the Poseidon2
compression of its two children. Perfectness is the separate invariant `Perfect`. -/
inductive PTree : Type where
  | leaf (v : ℤ)
  | node (l r : PTree)
deriving Repr, BEq, DecidableEq

namespace PTree

/-- Peak height: a leaf is 0, a node is one above its LEFT child (merges are equal-height, so the
bias is immaterial on perfect trees). -/
def height : PTree → ℕ
  | .leaf _ => 0
  | .node l _ => l.height + 1

/-- The leaves, left-to-right (oldest-first within the peak's chunk). -/
def leaves : PTree → List ℤ
  | .leaf v => [v]
  | .node l r => l.leaves ++ r.leaves

/-- The perfect-tree invariant: every node joins two perfect trees of EQUAL height. -/
def Perfect : PTree → Prop
  | .leaf _ => True
  | .node l r => l.Perfect ∧ r.Perfect ∧ l.height = r.height

/-- The peak hash — what the implementation stores: `hash [v]` at a leaf, `hash [hl, hr]` at a
node. The 1-vs-2 arity separates leaf from node domains under CR; no extra tag needed. -/
def hashOf (hash : List ℤ → ℤ) : PTree → ℤ
  | .leaf v => hash [v]
  | .node l r => hash [l.hashOf hash, r.hashOf hash]

@[simp] theorem height_leaf (v : ℤ) : (PTree.leaf v).height = 0 := rfl
@[simp] theorem height_node (l r : PTree) : (PTree.node l r).height = l.height + 1 := rfl
@[simp] theorem leaves_leaf (v : ℤ) : (PTree.leaf v).leaves = [v] := rfl
@[simp] theorem leaves_node (l r : PTree) : (PTree.node l r).leaves = l.leaves ++ r.leaves := rfl
@[simp] theorem perfect_leaf (v : ℤ) : (PTree.leaf v).Perfect := trivial
@[simp] theorem hashOf_leaf (hash : List ℤ → ℤ) (v : ℤ) :
    (PTree.leaf v).hashOf hash = hash [v] := rfl
@[simp] theorem hashOf_node (hash : List ℤ → ℤ) (l r : PTree) :
    (PTree.node l r).hashOf hash = hash [l.hashOf hash, r.hashOf hash] := rfl

/-! ### §1½ — THE PEAK EXTRACTOR: the binding, with NO refuted floor.

There used to be a `hashOf_injective` here, conditioned on `Poseidon2SpongeCR`, which
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear` PROVES FALSE for every range-bounded sponge and
`Storage.DeployedFloorRefuted.deployed_floor_false` refutes at the DEPLOYED hash by `rfl`. A theorem
carrying it says nothing about the deployed system, and — see §3¼ — its CONCLUSION is false there
too, so it was not even a bridge worth keeping.

What replaces it is not a weaker hypothesis but NO hypothesis: a TOTAL extractor that, from two peaks
with equal hashes, either proves the peaks equal or HANDS BACK the specific pair of sponge inputs at
which the hash actually collides. The disjunction is UNCONDITIONAL, so it holds OF the deployed
sponge — and it is not a free pass, because the returned pair is REFUTABLE (§3¾): exhibiting it
outright refutes `Poseidon2SpongeCR`, which is what makes this a strict WEAKENING rather than a
change of subject. -/

/-- **THE PEAK-COLLISION EXTRACTOR (TOTAL).** The tree walk the deleted `hashOf_injective` performed,
written as a FUNCTION. Two peaks whose hashes agree: if their sponge preimages differ (mismatched arity, or
different child digests) those preimages ARE the collision; otherwise the child digests agree
slot-for-slot, so recurse into the first child that differs. No search, no `Classical.choice` — the
branch test is `DecidableEq PTree`. -/
def collFind (hash : List ℤ → ℤ) : PTree → PTree → List ℤ × List ℤ
  | .leaf v, .leaf v' => ([v], [v'])
  | .leaf v, .node l' r' => ([v], [l'.hashOf hash, r'.hashOf hash])
  | .node l r, .leaf v' => ([l.hashOf hash, r.hashOf hash], [v'])
  | .node l r, .node l' r' =>
      if [l.hashOf hash, r.hashOf hash] ≠ [l'.hashOf hash, r'.hashOf hash] then
        ([l.hashOf hash, r.hashOf hash], [l'.hashOf hash, r'.hashOf hash])
      else if l ≠ l' then collFind hash l l'
      else collFind hash r r'

/-- **⚑ THE PEAK BINDING, UNCONDITIONAL.** Two peaks with equal hashes are EITHER equal, OR the pair
`collFind` returns is a genuine sponge collision. No injectivity, no CR, no floor of any kind — this
holds of the DEPLOYED sponge, which the deleted `hashOf_injective` never did. -/
theorem hashOf_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ t t' : PTree, t.hashOf hash = t'.hashOf hash →
      t = t' ∨ SpongeColl hash (collFind hash t t') := by
  intro t
  induction t with
  | leaf v =>
    intro t' h
    cases t' with
    | leaf v' =>
      by_cases hv : v = v'
      · exact Or.inl (by rw [hv])
      · refine Or.inr ?_
        simp only [collFind]
        exact ⟨by simpa using hv, h⟩
    | node l' r' =>
      refine Or.inr ?_
      simp only [collFind]
      exact ⟨by simp, h⟩
  | node l r ihl ihr =>
    intro t' h
    cases t' with
    | leaf v' =>
      refine Or.inr ?_
      simp only [collFind]
      exact ⟨by simp, h⟩
    | node l' r' =>
      by_cases houter : [l.hashOf hash, r.hashOf hash] ≠ [l'.hashOf hash, r'.hashOf hash]
      · refine Or.inr ?_
        simp only [collFind, if_pos houter]
        exact ⟨houter, h⟩
      · have hcond := houter
        rw [not_not] at houter
        simp only [List.cons.injEq, and_true] at houter
        obtain ⟨hlh, hrh⟩ := houter
        by_cases hl : l = l'
        · subst hl
          simp only [collFind, if_neg hcond, if_neg (by simp : ¬ (l ≠ l))]
          rcases ihr r' hrh with hr | hcoll
          · exact Or.inl (by rw [hr])
          · exact Or.inr hcoll
        · refine Or.inr ?_
          simp only [collFind, if_neg hcond, if_pos hl]
          exact (ihl l' hlh).resolve_left hl

/-- **THE PEAK EXTRACTOR BOTTOMS OUT AT AN EQUAL PAIR.** On one and the same peak the walk never
finds a difference, so the pair it returns has EQUAL components — the DISCHARGEABLE pole, one level
down: an honest prover who commits ONE peak pays nothing, for every hash. -/
theorem collFind_self_eq (hash : List ℤ → ℤ) :
    ∀ t : PTree, (collFind hash t t).1 = (collFind hash t t).2 := by
  intro t
  induction t with
  | leaf v => rfl
  | node l r _ ihr =>
    simp only [collFind, if_neg (by simp : ¬ ([l.hashOf hash, r.hashOf hash] : List ℤ)
      ≠ [l.hashOf hash, r.hashOf hash]), if_neg (by simp : ¬ (l ≠ l))]
    exact ihr

/-- **DISCHARGEABLE (peak level).** The honest opening of ONE peak refutes its own residual, with no
cryptographic hypothesis at all. -/
theorem hashOfColl_dischargeable (hash : List ℤ → ℤ) (t : PTree) :
    ¬ SpongeColl hash (collFind hash t t) :=
  fun hc => hc.1 (collFind_self_eq hash t)

/-- **A REFUTATION, NOT A NEW FLOOR (peak level).** Two DISTINCT peaks sharing a hash REFUTE
`Poseidon2SpongeCR` outright. Stated contrapositively — it assumes no floor content — so it is the
tooth the old `hashOf_injective_of_binds_or_collides` was pretending to be: that one took the refuted
floor as a HYPOTHESIS and was therefore a carrier whatever its conclusion. -/
theorem hashOf_equivocation_refutes_poseidon2CR {hash : List ℤ → ℤ} {t t' : PTree}
    (h : t.hashOf hash = t'.hashOf hash) (hne : t ≠ t') : ¬ Poseidon2SpongeCR hash := by
  intro hCR
  rcases hashOf_binds_or_collides hash t t' h with heq | hc
  · exact hne heq
  · exact hc.1 (hCR _ _ hc.2)

/-- A perfect peak of height `h` carries exactly `2 ^ h` leaves (the chunk sizes are the binary
decomposition of the log length). -/
theorem length_leaves : ∀ t : PTree, t.Perfect → t.leaves.length = 2 ^ t.height := by
  intro t
  induction t with
  | leaf v => intro _; simp
  | node l r ihl ihr =>
    intro hp
    obtain ⟨hl, hr, hh⟩ := hp
    simp only [leaves_node, List.length_append, ihl hl, ihr hr, ← hh, height_node, pow_succ]
    omega

end PTree

#assert_axioms PTree.hashOf_binds_or_collides
#assert_axioms PTree.collFind_self_eq
#assert_axioms PTree.hashOfColl_dischargeable
#assert_axioms PTree.hashOf_equivocation_refutes_poseidon2CR
#assert_axioms PTree.length_leaves

/-! ## §2 — the forest: `push` (the carry), `peaksOf` (the fold), leaf recovery, the mountains
invariant.

Head = youngest (smallest) peak. `push` merges while heights match — the binary carry; an append
is `push f (.leaf v)`. The forest of a log is the left fold, so the incremental peak update agrees
with recomputation BY DEFINITION (`peaksOf_append` is `foldl` over a concat). -/

/-- The mountain range: peaks, youngest (lowest) first. -/
abbrev Forest := List PTree

/-- **`push`** — the carry: while the youngest peak has the SAME height as the incoming tree,
merge (older peak on the LEFT — its leaves precede); otherwise prepend. Amortized O(1) appends:
each merge retires a peak, each append mints one. -/
def push : Forest → PTree → Forest
  | [], t => [t]
  | s :: rest, t => if t.height = s.height then push rest (.node s t) else t :: s :: rest

@[simp] theorem push_nil (t : PTree) : push [] t = [t] := rfl

theorem push_cons (s : PTree) (rest : Forest) (t : PTree) :
    push (s :: rest) t =
      if t.height = s.height then push rest (.node s t) else t :: s :: rest := rfl

/-- Append one log entry: push a fresh height-0 peak. -/
def appendLeaf (f : Forest) (v : ℤ) : Forest := push f (.leaf v)

/-- **`peaksOf`** — the forest of a log: fold the appends. The implementation maintains this
incrementally; the model recomputes — `peaksOf_append` says the two agree. -/
def peaksOf (L : List ℤ) : Forest := L.foldl appendLeaf []

/-- The forest's leaves, OLDEST-FIRST (tail peaks are older; within a peak, left-to-right). -/
def forestLeaves (f : Forest) : List ℤ := f.foldr (fun t acc => acc ++ t.leaves) []

@[simp] theorem forestLeaves_nil : forestLeaves [] = [] := rfl
@[simp] theorem forestLeaves_cons (t : PTree) (f : Forest) :
    forestLeaves (t :: f) = forestLeaves f ++ t.leaves := rfl

/-- Pushing a tree appends its leaves at the YOUNG end — the leaf order is append order, through
every carry (associativity is the whole proof). -/
theorem forestLeaves_push : ∀ (f : Forest) (t : PTree),
    forestLeaves (push f t) = forestLeaves f ++ t.leaves := by
  intro f
  induction f with
  | nil => intro t; simp
  | cons s rest ih =>
    intro t
    rw [push_cons]
    by_cases h : t.height = s.height
    · rw [if_pos h, ih]
      simp [List.append_assoc]
    · rw [if_neg h]
      rfl

/-- **The O(1) peak update agrees with recomputation** (a `foldl` over a concat — definitional).
This IS "append = peak update": the implementation's incremental push computes `peaksOf`. -/
theorem peaksOf_append (L : List ℤ) (v : ℤ) :
    peaksOf (L ++ [v]) = push (peaksOf L) (.leaf v) := by
  simp [peaksOf, appendLeaf, List.foldl_append]

/-- **THE RECOVERY KEYSTONE (`forestLeaves_peaksOf`).** The forest's oldest-first leaves are
EXACTLY the appended log. Two consequences fall out by construction: the structure is its own
canonical order (no sorted invariant to maintain), and appending never moves a prior position
(prefix stability — §4 consumes it). -/
theorem forestLeaves_peaksOf (L : List ℤ) : forestLeaves (peaksOf L) = L := by
  induction L using List.reverseRecOn with
  | nil => rfl
  | append_singleton L v ih =>
    rw [peaksOf_append, forestLeaves_push, ih, PTree.leaves_leaf]

/-- **`Mountains`** — the range invariant: every peak perfect, heights STRICTLY increasing from
the youngest. (Strict increase = the binary decomposition of the log length: at most one peak per
height, so #peaks ≤ log₂(n)+1 — the succinct frontier.) -/
def Mountains (f : Forest) : Prop :=
  (∀ t ∈ f, t.Perfect) ∧ f.Pairwise (fun a b => a.height < b.height)

/-- The carry preserves the invariant: pushing a perfect tree no taller than every peak yields
mountains again, with every peak still at least the pushed height. -/
theorem push_invariant : ∀ (f : Forest) (t : PTree), Mountains f → t.Perfect →
    (∀ s ∈ f, t.height ≤ s.height) →
    Mountains (push f t) ∧ ∀ s ∈ push f t, t.height ≤ s.height := by
  intro f
  induction f with
  | nil =>
    intro t _ hp _
    simp [Mountains, hp]
  | cons s rest ih =>
    intro t hm hp hle
    obtain ⟨hperf, hpair⟩ := hm
    rw [push_cons]
    by_cases h : t.height = s.height
    · rw [if_pos h]
      have hsp : s.Perfect := hperf s List.mem_cons_self
      have hnp : (PTree.node s t).Perfect := ⟨hsp, hp, h.symm⟩
      have hrest : Mountains rest :=
        ⟨fun u hu => hperf u (List.mem_cons_of_mem _ hu), (List.pairwise_cons.mp hpair).2⟩
      have hle' : ∀ u ∈ rest, (PTree.node s t).height ≤ u.height := by
        intro u hu
        simpa using (List.pairwise_cons.mp hpair).1 u hu
      obtain ⟨hm', hge'⟩ := ih (PTree.node s t) hrest hnp hle'
      refine ⟨hm', fun u hu => le_trans ?_ (hge' u hu)⟩
      simp [h]
    · rw [if_neg h]
      have hts : t.height < s.height := lt_of_le_of_ne (hle s List.mem_cons_self) h
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hp
        · exact hperf u hu
      · rw [List.pairwise_cons]
        refine ⟨fun u hu => ?_, hpair⟩
        rcases List.mem_cons.mp hu with rfl | hu
        · exact hts
        · exact hts.trans ((List.pairwise_cons.mp hpair).1 u hu)
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact le_refl _
        · exact hle u hu

/-- **The structure theorem.** Every log's forest is mountains: perfect peaks, strictly
increasing heights — the binary-decomposition shape, for free, forever (the invariant is
maintained by the only mutation the structure has). -/
theorem peaksOf_mountains (L : List ℤ) : Mountains (peaksOf L) := by
  induction L using List.reverseRecOn with
  | nil => simp [peaksOf, Mountains]
  | append_singleton L v ih =>
    rw [peaksOf_append]
    exact (push_invariant (peaksOf L) (.leaf v) ih trivial (fun s _ => Nat.zero_le _)).1

#assert_axioms forestLeaves_push
#assert_axioms peaksOf_append
#assert_axioms forestLeaves_peaksOf
#assert_axioms push_invariant
#assert_axioms peaksOf_mountains

/-! ## §3 — bagging and THE ROOT.

`bag` folds the peaks into ONE felt (right-assoc: `hash [peakHash, bagOfRest]`, empty = `hash []`
— arities 0/2/1 keep the three hash domains apart with no tags). `mroot` is the committed
value; `mroot_binds_or_collides` (§3½) is the root-binding transfer onto the MMR. -/

/-- **`bag`** — the single root over the peaks: `hash []` for the empty range, else
`hash [peak, bag rest]` youngest-outward. -/
def bag (hash : List ℤ → ℤ) : Forest → ℤ
  | [] => hash []
  | t :: rest => hash [t.hashOf hash, bag hash rest]

@[simp] theorem bag_nil (hash : List ℤ → ℤ) : bag hash [] = hash [] := rfl
@[simp] theorem bag_cons (hash : List ℤ → ℤ) (t : PTree) (f : Forest) :
    bag hash (t :: f) = hash [t.hashOf hash, bag hash f] := rfl

/-- **`mroot`** — the committed MMR root of a receipt log: bag the forest. THE value the per-turn
commitment absorbs (§6) — `iroot` for the append-only index. -/
def mroot (hash : List ℤ → ℤ) (L : List ℤ) : ℤ := bag hash (peaksOf L)

/-! ### §3½ — THE ROOT EXTRACTOR: the anti-ghost keystone WITHOUT the refuted floor.

Same move as §1½, one level up. `bagFind` walks the two peak lists together; `mrootFind` is that walk
started at `peaksOf`. `mroot_binds_or_collides` is the UNCONDITIONAL form of the headline: two logs
with equal roots are equal OR the extractor hands back a genuine collision of the sponge. It is what
a light client can actually rely on at the deployed Poseidon2, and it is the theorem every consumer
below is migrated onto. -/

/-- **THE FOREST-COLLISION EXTRACTOR (TOTAL).** The deleted `bag_injective`'s induction as a FUNCTION: mismatched
arity (empty vs cons) IS the collision; matching arity with differing preimages IS the collision;
otherwise peel — the peak if the peaks differ, else the tail. -/
def bagFind (hash : List ℤ → ℤ) : Forest → Forest → List ℤ × List ℤ
  | [], [] => ([], [])
  | [], (t' :: rest') => ([], [t'.hashOf hash, bag hash rest'])
  | (t :: rest), [] => ([t.hashOf hash, bag hash rest], [])
  | (t :: rest), (t' :: rest') =>
      if [t.hashOf hash, bag hash rest] ≠ [t'.hashOf hash, bag hash rest'] then
        ([t.hashOf hash, bag hash rest], [t'.hashOf hash, bag hash rest'])
      else if t ≠ t' then PTree.collFind hash t t'
      else bagFind hash rest rest'

/-- **⚑ THE BAG BINDING, UNCONDITIONAL.** Equal bags force equal peak lists OR expose a genuine sponge
collision. No floor. -/
theorem bag_binds_or_collides (hash : List ℤ → ℤ) :
    ∀ f₁ f₂ : Forest, bag hash f₁ = bag hash f₂ →
      f₁ = f₂ ∨ SpongeColl hash (bagFind hash f₁ f₂) := by
  intro f₁
  induction f₁ with
  | nil =>
    intro f₂ h
    cases f₂ with
    | nil => exact Or.inl rfl
    | cons t' rest' =>
      refine Or.inr ?_
      simp only [bagFind]
      exact ⟨by simp, h⟩
  | cons t rest ih =>
    intro f₂ h
    cases f₂ with
    | nil =>
      refine Or.inr ?_
      simp only [bagFind]
      exact ⟨by simp, h⟩
    | cons t' rest' =>
      by_cases houter :
          [t.hashOf hash, bag hash rest] ≠ [t'.hashOf hash, bag hash rest']
      · refine Or.inr ?_
        simp only [bagFind, if_pos houter]
        exact ⟨houter, h⟩
      · have hcond := houter
        rw [not_not] at houter
        simp only [List.cons.injEq, and_true] at houter
        obtain ⟨hth, hbh⟩ := houter
        by_cases ht : t = t'
        · subst ht
          simp only [bagFind, if_neg hcond, if_neg (by simp : ¬ (t ≠ t))]
          rcases ih rest' hbh with hrest | hcoll
          · exact Or.inl (by rw [hrest])
          · exact Or.inr hcoll
        · refine Or.inr ?_
          simp only [bagFind, if_neg hcond, if_pos ht]
          exact (PTree.hashOf_binds_or_collides hash t t' hth).resolve_left ht

/-- **THE FOREST EXTRACTOR BOTTOMS OUT AT AN EQUAL PAIR** (the forest-level DISCHARGEABLE pole). -/
theorem bagFind_self_eq (hash : List ℤ → ℤ) :
    ∀ f : Forest, (bagFind hash f f).1 = (bagFind hash f f).2 := by
  intro f
  induction f with
  | nil => rfl
  | cons t rest ih =>
    simp only [bagFind, if_neg (by simp : ¬ ([t.hashOf hash, bag hash rest] : List ℤ)
      ≠ [t.hashOf hash, bag hash rest]), if_neg (by simp : ¬ (t ≠ t))]
    exact ih

/-- **THE ROOT-COLLISION EXTRACTOR (TOTAL).** The forest walk started at the two logs' peak lists —
what an adversary who equivocates on the published MMR root actually hands over. -/
def mrootFind (hash : List ℤ → ℤ) (L₁ L₂ : List ℤ) : List ℤ × List ℤ :=
  bagFind hash (peaksOf L₁) (peaksOf L₂)

/-- **⚑ `mroot_binds_or_collides` — THE ROOT BINDS THE WHOLE LOG, UNCONDITIONALLY.** Two logs with
equal roots are EITHER equal — a server cannot keep the published root while suppressing, forging,
REORDERING or truncating any receipt position — OR the pair `mrootFind` returns is a genuine collision
of the sponge.

This is the headline the deleted `mroot_injective` was trying to be, minus the hypothesis the deployed
sponge REFUTES — and minus a conclusion the deployed sponge also refutes (§3¼). It holds OF the
deployed Poseidon2. What it costs is honest and named: the guarantee is now
"binds, unless the server found a sponge collision", and §3¾ prices that residual as a game advantage
instead of assuming it away. -/
theorem mroot_binds_or_collides (hash : List ℤ → ℤ) {L₁ L₂ : List ℤ}
    (h : mroot hash L₁ = mroot hash L₂) :
    L₁ = L₂ ∨ SpongeColl hash (mrootFind hash L₁ L₂) := by
  rcases bag_binds_or_collides hash _ _ h with hf | hcoll
  · refine Or.inl ?_
    calc L₁ = forestLeaves (peaksOf L₁) := (forestLeaves_peaksOf L₁).symm
      _ = forestLeaves (peaksOf L₂) := by rw [hf]
      _ = L₂ := forestLeaves_peaksOf L₂
  · exact Or.inr hcoll

/-! ### §3¼ — ⚑ WHY THE THREE "STRENGTH BRIDGES" ARE DELETED, NOT KEPT.

`PTree.hashOf_injective`, `bag_injective` and `mroot_injective` survived the 2026-07-25 cutover as
one-line derivations from the unconditional forms, labelled STRENGTH BRIDGES: "whatever the old
theorem gave you, the new one still gives you, at exactly the same hypothesis". That was true and it
was beside the point. **Check the CONCLUSION, not only the hypothesis.**

Each of those three concludes an INJECTIVITY of a `… → ℤ` map — and at a range-bounded sponge that
conclusion is refuted by the SAME pigeonhole that refutes the premise. The three lemmas below make it
concrete rather than asymptotic: ONE sponge collision at two DISTINCT SINGLETON preimages (`hash [a] =
hash [b]`, `a ≠ b`) refutes all three conclusions outright, because `mroot hash [a] = hash [hash [a],
hash []]` peels straight down to it. `Storage.DeployedFloorRegrounded` instantiates them at the
DEPLOYED `poseidon2Hash` off `DeployedFloorRefuted.deployed_collides`, an `rfl` collision at
`[0]`/`[p]`. So the bridges were false → false: they carried a refuted hypothesis to a refuted
conclusion, and a reader who cited one learned nothing either way. They are gone.

None of the three names a floor at all: each ASSUMES a concrete collision at two NAMED singleton
preimages and CONCLUDES the negation of an anonymous injectivity. They are teeth, not carriers. -/

/-- One singleton collision refutes the PEAK binding's old conclusion. -/
theorem hashOf_not_injective_of_singleton_collision (hash : List ℤ → ℤ) {a b : ℤ}
    (hne : a ≠ b) (hcoll : hash [a] = hash [b]) :
    ¬ (∀ t t' : PTree, t.hashOf hash = t'.hashOf hash → t = t') := by
  intro hinj
  have := hinj (.leaf a) (.leaf b) hcoll
  exact hne (by simpa using this)

/-- The same collision refutes the FOREST binding's old conclusion. -/
theorem bag_not_injective_of_singleton_collision (hash : List ℤ → ℤ) {a b : ℤ}
    (hne : a ≠ b) (hcoll : hash [a] = hash [b]) :
    ¬ (∀ f₁ f₂ : Forest, bag hash f₁ = bag hash f₂ → f₁ = f₂) := by
  intro hinj
  have hb : bag hash [PTree.leaf a] = bag hash [PTree.leaf b] := by
    simp only [bag_cons, bag_nil, PTree.hashOf_leaf, hcoll]
  have := hinj _ _ hb
  exact hne (by simpa using this)

/-- **⚑ THE HEADLINE OF §3¼ — the same collision refutes `mroot_injective`'s exact conclusion.** The
deleted theorem said "two logs with equal roots are equal"; at any sponge that collides on two
singletons, the two ONE-ENTRY logs `[a]` and `[b]` are a counterexample. So the deployed system never
had the conclusion either, and the "bridge" bridged nothing. -/
theorem mroot_not_injective_of_singleton_collision (hash : List ℤ → ℤ) {a b : ℤ}
    (hne : a ≠ b) (hcoll : hash [a] = hash [b]) :
    ¬ (∀ L₁ L₂ : List ℤ, mroot hash L₁ = mroot hash L₂ → L₁ = L₂) := by
  intro hinj
  have hr : mroot hash [a] = mroot hash [b] := by
    simp only [mroot, peaksOf, List.foldl_cons, List.foldl_nil, appendLeaf, push_nil,
      bag_cons, bag_nil, PTree.hashOf_leaf, hcoll]
  have := hinj _ _ hr
  exact hne (by simpa using this)

/-! ### §3¾ — the RESIDUAL every migrated consumer now carries, and its three poles.

`MRootColl hash L₁ L₂` is the ONE named side condition that replaced the floor binder in
`mroot_binds_position`, `mroot_binds_range`, `mroot_pins_rverifies`, `server_cannot_omit_position`,
`commit_pins_mmr` and `light_client_position_non_omission`.

Deliberately NOT `∃ xs ys, xs ≠ ys ∧ hash xs = hash ys`: at deployed BabyBear that existence claim is
unconditionally TRUE by pigeonhole, so it would carry no more content than `True`. And deliberately
NOT `∀ xs ys, ¬ …`: that is the refuted floor wearing a disjunction. It is the collision AT THE PAIR
`mrootFind` HANDS BACK, for the two logs in play.

Three poles, because a side condition that can never fail is `True` in disguise and one that can never
be discharged is a broken keystone rather than a repaired one. -/

/-- **`MRootColl hash L₁ L₂`** — the per-instance residual: the deployed sponge genuinely collides at
the ONE pair the root extractor returns for these two logs. -/
def MRootColl (hash : List ℤ → ℤ) (L₁ L₂ : List ℤ) : Prop :=
  SpongeColl hash (mrootFind hash L₁ L₂)

/-- The residual is DECIDABLE per instance — which is exactly what a global injectivity floor never
was, and what lets the poles below be `decide`d rather than asserted. -/
instance decidableMRootColl (hash : List ℤ → ℤ) (L₁ L₂ : List ℤ) :
    Decidable (MRootColl hash L₁ L₂) := by
  unfold MRootColl; infer_instance

/-- The root extractor bottoms out at an EQUAL pair on one and the same log. -/
theorem mrootFind_self_eq (hash : List ℤ → ℤ) (L : List ℤ) :
    (mrootFind hash L L).1 = (mrootFind hash L L).2 :=
  bagFind_self_eq hash (peaksOf L)

/-- **DISCHARGEABLE.** The honest prover — who commits ONE log — discharges the residual for EVERY
hash, with no cryptographic assumption whatsoever. This is what the deleted floor could never do:
`Poseidon2SpongeCR` is unavailable at the deployed sponge even to an honest party. -/
theorem mrootColl_dischargeable (hash : List ℤ → ℤ) (L : List ℤ) : ¬ MRootColl hash L L :=
  fun hc => hc.1 (mrootFind_self_eq hash L)

/-- **REFUTABLE.** At the constant sponge the extractor really does hand back a colliding pair, so
`¬ MRootColl` is not free — the residual is not `True` in disguise. -/
theorem mrootColl_refutable : MRootColl (fun _ => (0 : ℤ)) [1] [2] := by decide

/-- **A REFUTATION, NOT A NEW FLOOR.** Exhibiting the residual REFUTES `Poseidon2SpongeCR` outright,
so every port below is a strict WEAKENING of the premise it replaces. Stated contrapositively, so it
assumes no floor content and the ratchet reads it as the tooth it is. -/
theorem mrootColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {L₁ L₂ : List ℤ}
    (hc : MRootColl hash L₁ L₂) : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hc.1 (hCR _ _ hc.2)

#assert_axioms bag_binds_or_collides
#assert_axioms bagFind_self_eq
#assert_axioms mroot_binds_or_collides
#assert_axioms hashOf_not_injective_of_singleton_collision
#assert_axioms bag_not_injective_of_singleton_collision
#assert_axioms mroot_not_injective_of_singleton_collision
#assert_axioms mrootFind_self_eq
#assert_axioms mrootColl_dischargeable
#assert_axioms mrootColl_refutable
#assert_axioms mrootColl_refutes_poseidon2CR

/-! ## §4 — positional and range openings; appends preserve them.

A positional opening certifies "position `i` holds `v`"; a range opening is the contiguous slice
`mrange`. Because the structure only ever APPENDS, every prior opening and every prior range stays
true VERBATIM after any number of later appends — prefix stability by construction, the property
the sorted map had to re-prove per insert. -/

/-- **`Opens L i v`** — the positional opening's semantic content: position `i` of the log holds
`v`. (At the wire: the Merkle path through the covering peak + the peak's bag position; at the
model the log is pinned by `mroot_binds_or_collides`.) -/
def Opens (L : List ℤ) (i : ℕ) (v : ℤ) : Prop := L[i]? = some v

instance (L : List ℤ) (i : ℕ) (v : ℤ) : Decidable (Opens L i v) := by
  unfold Opens; infer_instance

/-- **`mrange L lo hi`** — the EXACT range answer: positions `[lo, hi]` of the log, clipped to the
committed length. THE complete answer a range query must equal. -/
def mrange (L : List ℤ) (lo hi : ℕ) : List ℤ := (L.take (hi + 1)).drop lo

/-- The committed in-range position count: `|[lo, hi] ∩ [0, len)|`. Computable from the committed
length alone — the client-side count check of §5. -/
def rangeCount (len lo hi : ℕ) : ℕ := min (hi + 1) len - lo

@[simp] theorem mrange_length (L : List ℤ) (lo hi : ℕ) :
    (mrange L lo hi).length = rangeCount L.length lo hi := by
  simp [mrange, rangeCount]

/-- The range answer reads the log at dense offsets: slot `j` is position `lo + j`. -/
theorem mrange_getElem? (L : List ℤ) (lo hi j : ℕ) (hj : j < rangeCount L.length lo hi) :
    (mrange L lo hi)[j]? = L[lo + j]? := by
  have h1 : lo + j < hi + 1 := by unfold rangeCount at hj; omega
  simp [mrange, List.getElem?_drop, h1]

/-- Equal roots open identically at every position (the per-position consumable form).

⚙ PORTED 2026-07-28: the `Poseidon2SpongeCR` binder is replaced by the per-instance residual at the
pair `mrootFind` names for THESE two logs. Strictly weaker hypothesis, so nothing provable was lost —
and unlike the floor, `¬ MRootColl` is DISCHARGEABLE by the honest party (`mrootColl_dischargeable`)
and REFUTABLE (`mrootColl_refutable`). Worth ~2^15.5 queries at the deployed 1-felt root; see the
header. -/
theorem mroot_binds_position (hash : List ℤ → ℤ)
    {L L' : List ℤ} (h : mroot hash L' = mroot hash L)
    (hno : ¬ MRootColl hash L' L) (i : ℕ) : L'[i]? = L[i]? := by
  rw [(mroot_binds_or_collides hash h).resolve_right hno]

/-- **A range is fully determined by the root**: once the root is fixed there is exactly one
correct answer to every positional range query (`iroot_binds_range`, transferred). -/
theorem mroot_binds_range (hash : List ℤ → ℤ)
    {L L' : List ℤ} (h : mroot hash L' = mroot hash L)
    (hno : ¬ MRootColl hash L' L) (lo hi : ℕ) :
    mrange L' lo hi = mrange L lo hi := by
  rw [(mroot_binds_or_collides hash h).resolve_right hno]

/-- **Appends preserve prior positions** — any suffix of later appends leaves every committed
position untouched (prefix stability, by construction). -/
theorem append_preserves_get (L M : List ℤ) {i : ℕ} (hi : i < L.length) :
    (L ++ M)[i]? = L[i]? :=
  List.getElem?_append_left hi

/-- **Appends preserve prior OPENINGS**: an opening made against the old log is verbatim true of
the appended log. (The sorted map re-sorts on insert; the MMR never moves a leaf.) -/
theorem append_preserves_opens {L : List ℤ} {i : ℕ} {v : ℤ} (h : Opens L i v) (M : List ℤ) :
    Opens (L ++ M) i v := by
  have hi : i < L.length := by
    by_contra hn
    rw [Opens, List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
    simp at h
  rw [Opens, append_preserves_get L M hi]
  exact h

/-- **Appends preserve prior RANGES**: a range answer whose upper end is already committed is
verbatim the same after any number of later appends. -/
theorem append_preserves_range (L M : List ℤ) {lo hi : ℕ} (hhi : hi < L.length) :
    mrange (L ++ M) lo hi = mrange L lo hi := by
  unfold mrange
  rw [List.take_append_of_le_length (by omega)]

#assert_axioms mrange_getElem?
#assert_axioms mroot_binds_position
#assert_axioms mroot_binds_range
#assert_axioms append_preserves_get
#assert_axioms append_preserves_opens
#assert_axioms append_preserves_range

/-! ## §5 — the range protocol + POSITIONAL COMPLETENESS (non-omission WITHOUT gap openings).

The sorted map needed gap openings (bracketing absent KEYS); positions are DENSE, so absence needs
no witness at all. The client checks (1) the answer's COUNT equals the committed clip — `rangeCount`
from the committed length, which the root pins — and (2) each value opens at its dense slot
`lo + j`. A position cannot be skipped: skipping shifts every later slot and breaks the count. -/

/-- **`RVerifies L lo hi vals`** — the client-side acceptance for a positional range answer:
the count matches the committed clip, and slot `j` opens position `lo + j`. NO gap openings. -/
def RVerifies (L : List ℤ) (lo hi : ℕ) (vals : List ℤ) : Prop :=
  vals.length = rangeCount L.length lo hi
  ∧ ∀ j v, vals[j]? = some v → Opens L (lo + j) v

/-- **SOUNDNESS (`range_sound`).** Every answered value genuinely opens at its claimed position. -/
theorem range_sound {L : List ℤ} {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L lo hi vals) :
    ∀ j v, vals[j]? = some v → Opens L (lo + j) v := hv.2

/-- **THE KEYSTONE — POSITIONAL COMPLETENESS (`range_complete`): positions cannot be skipped.**
A verifying answer contains EVERY committed position in the queried range, each at its dense slot
`i - lo`, agreeing with the log. Non-omission with no gap openings: density + the count are the
whole argument. -/
theorem range_complete {L : List ℤ} {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L lo hi vals) :
    ∀ i, lo ≤ i → i ≤ hi → i < L.length →
      ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  intro i hlo hhi hlen
  have hj : i - lo < vals.length := by
    rw [hv.1]; unfold rangeCount; omega
  have hval : vals[i - lo]? = some vals[i - lo] := List.getElem?_eq_getElem hj
  have hopen := hv.2 (i - lo) _ hval
  rw [Nat.add_sub_cancel' hlo] at hopen
  exact ⟨_, hval, hopen⟩

/-- **The two-sided characterization (`rverifies_iff_exact`).** An answer verifies IFF it is
EXACTLY `mrange L lo hi` — the unique correct answer: nothing skipped, nothing forged, dense
order. (The backward direction is honest-prover totality: the exact answer ALWAYS verifies, so
completeness is achievable, not vacuous.) -/
theorem rverifies_iff_exact {L : List ℤ} {lo hi : ℕ} {vals : List ℤ} :
    RVerifies L lo hi vals ↔ vals = mrange L lo hi := by
  constructor
  · intro hv
    apply List.ext_getElem?
    intro j
    by_cases hj : j < vals.length
    · have hval : vals[j]? = some vals[j] := List.getElem?_eq_getElem hj
      rw [hval, mrange_getElem? L lo hi j (hv.1 ▸ hj)]
      exact (hv.2 j _ hval).symm
    · rw [List.getElem?_eq_none (Nat.le_of_not_lt hj),
        List.getElem?_eq_none (by rw [mrange_length, ← hv.1]; omega)]
  · rintro rfl
    refine ⟨mrange_length L lo hi, fun j v hval => ?_⟩
    have hj : j < (mrange L lo hi).length := by
      by_contra hn
      rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hval
      simp at hval
    show L[lo + j]? = some v
    rw [← mrange_getElem? L lo hi j (by rwa [mrange_length] at hj)]
    exact hval

/-- **Honest-prover totality.** The exact answer always verifies — every positional range query on
every log is answerable, completely, with no auxiliary witnesses. -/
theorem exact_range_verifies (L : List ℤ) (lo hi : ℕ) :
    RVerifies L lo hi (mrange L lo hi) :=
  rverifies_iff_exact.mpr rfl

/-- A `RVerifies` run against ANY log recomposing the published root is a run against THE log
(the root binding pins the leaves, unless the server found the named collision). -/
theorem mroot_pins_rverifies (hash : List ℤ → ℤ)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L)
    (hno : ¬ MRootColl hash L' L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) : RVerifies L lo hi vals := by
  rwa [(mroot_binds_or_collides hash hroot).resolve_right hno] at hv

/-- **`server_cannot_omit_position` — THE ROOT-FACE HEADLINE.** A client holding ONLY the committed
`mroot`: a verifying answer against ANY log recomposing that root IS the unique exact range of the
genuine log — every committed in-range position present at its dense slot (omission impossible),
every value genuine (forgery impossible). No sorted invariant, no gaps.

The only crypto is ONE named, per-instance, refutable residual — *unless the server found a sponge
collision at the specific pair `mrootFind hash L' L` returns*. That is the honest statement at the
deployed 1-felt root, and it is worth ~2^15.5 queries (header). The version of this theorem that
carried `Poseidon2SpongeCR` was worth nothing at all: the floor is refuted at the deployed hash. -/
theorem server_cannot_omit_position (hash : List ℤ → ℤ)
    {L L' : List ℤ} (hroot : mroot hash L' = mroot hash L)
    (hno : ¬ MRootColl hash L' L)
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    vals = mrange L lo hi
    ∧ ∀ i, lo ≤ i → i ≤ hi → i < L.length →
        ∃ v, vals[i - lo]? = some v ∧ Opens L i v := by
  have hv' := mroot_pins_rverifies hash hroot hno hv
  exact ⟨rverifies_iff_exact.mp hv', range_complete hv'⟩

#assert_axioms range_sound
#assert_axioms range_complete
#assert_axioms rverifies_iff_exact
#assert_axioms exact_range_verifies
#assert_axioms mroot_pins_rverifies
#assert_axioms server_cannot_omit_position

/-! ## §6 — the CHAIN face: `AttestedQuery`'s per-block obligation, restated over the MMR.

`CommitBindsMMR` is `CommitBindsIndex` VERBATIM with `iroot := mroot` — the per-turn state
commitment absorbs the receipt-index root as its LAST sponge limb (the EPOCH commitment layout
places the receipt-index root last, exactly so this discharges by construction). The composition
with `RecursiveAggregation` is identical; the obligation list SHRINKS: `hsorted` is GONE (the
append-only log is its own canonical order) and the answer carries no gap openings. -/

/-- **`CommitBindsMMR` — the rotation obligation, carried over verbatim.** The per-turn commitment
is a sponge absorbing the MMR root as a limb (`limbs` = the other absorbed fields — cells root,
registers, map roots). The EPOCH layout (receipt-index root LAST) discharges this by construction
at the flag-day. -/
def CommitBindsMMR (hash : List ℤ → ℤ) (limbs : List ℤ) (commit : ℤ)
    (L : List ℤ) : Prop :=
  commit = hash (limbs ++ [mroot hash L])

/-- **`CommitColl hash limbs limbs' L L'`** — the OUTER residual `commit_pins_mmr` carries: the
sponge collides at the two COMMITMENT PREIMAGES in play. The peel of the commitment is a second,
independent use of the hash, so it gets its own named residual rather than being smuggled into the
root one; both pairs are statement-visible, which is what makes a per-instance condition honest here
(hiding either behind an existential would force the residual back to a universal, i.e. back to the
refuted floor). -/
def CommitColl (hash : List ℤ → ℤ) (limbs limbs' : List ℤ) (L L' : List ℤ) : Prop :=
  SpongeColl hash (limbs ++ [mroot hash L], limbs' ++ [mroot hash L'])

instance decidableCommitColl (hash : List ℤ → ℤ) (limbs limbs' L L' : List ℤ) :
    Decidable (CommitColl hash limbs limbs' L L') := by
  unfold CommitColl; infer_instance

/-- **DISCHARGEABLE.** One honest opening of one commitment refutes the outer residual for EVERY
hash. -/
theorem commitColl_dischargeable (hash : List ℤ → ℤ) (limbs L : List ℤ) :
    ¬ CommitColl hash limbs limbs L L := fun hc => hc.1 rfl

/-- **REFUTABLE.** At the constant sponge two different limb vectors really do collide, so the outer
residual is not `True` in disguise either. -/
theorem commitColl_refutable : CommitColl (fun _ => (0 : ℤ)) [1] [2] [] [] := by decide

/-- **A REFUTATION, NOT A NEW FLOOR** (outer level), stated contrapositively. -/
theorem commitColl_refutes_poseidon2CR {hash : List ℤ → ℤ} {limbs limbs' L L' : List ℤ}
    (hc : CommitColl hash limbs limbs' L L') : ¬ Poseidon2SpongeCR hash :=
  fun hCR => hc.1 (hCR _ _ hc.2)

/-- A commitment binding an MMR root pins the log: two openings of the SAME commitment expose the
SAME receipt log (the sponge peel exposes the last limb regardless of the other limbs' shape, and
the root binding pins the leaves — `commit_pins_index`, transferred).

⚙ PORTED 2026-07-28: TWO per-instance residuals in place of one refuted floor — the outer commitment
peel (`CommitColl`) and the root binding (`MRootColl`). Both are dischargeable by an honest opening
with no hypothesis on the hash, and both are refutable. -/
theorem commit_pins_mmr (hash : List ℤ → ℤ)
    {limbs limbs' : List ℤ} {c : ℤ} {L L' : List ℤ}
    (hb : CommitBindsMMR hash limbs c L)
    (hb' : CommitBindsMMR hash limbs' c L')
    (hnc : ¬ CommitColl hash limbs limbs' L L')
    (hnr : ¬ MRootColl hash L' L) : L' = L := by
  have hl : limbs ++ [mroot hash L] = limbs' ++ [mroot hash L'] := by
    by_contra hne
    exact hnc ⟨hne, hb.symm.trans hb'⟩
  have h1 : (limbs ++ [mroot hash L]).getLast? = some (mroot hash L) :=
    List.getLast?_concat
  have h2 : (limbs' ++ [mroot hash L']).getLast? = some (mroot hash L') :=
    List.getLast?_concat
  rw [hl, h2] at h1
  exact (mroot_binds_or_collides hash (Option.some.inj h1)).resolve_right hnr

open Dregg2.Circuit.RecursiveAggregation
open Dregg2.Distributed.HistoryAggregation (ChainStep)
open Dregg2.Exec (RecChainedState)

/-- **`light_client_position_non_omission` — non-omission over the WHOLE history, on the MMR
index.** The per-block face of `AttestedQuery.light_client_query_non_omission`, restated: a light
client holding ONLY the aggregation root, given

  * a sound recursion engine (`EngineSound`) and `verify agg.root = true` (the ONE client check),
  * the weld — every step's folded state commitment absorbs its receipt log's MMR root
    (`CommitBindsMMR`, the `CommitBindsIndex` limb obligation verbatim, `iroot := mroot`),

concludes, for ANY step, ANY server-supplied opening of that step's attested commitment, and ANY
verifying positional range answer: the whole chain is attested (`AggregateAttests`), the answer is
EXACTLY the genuine range, and every committed in-range position is present at its dense slot.
Versus the sorted-map face, TWO obligations vanish: no per-index sorted invariant (`hsorted` is
gone — append-only is canonically ordered) and no gap openings (density replaces bracketing). The
server cannot skip a position anywhere in history. -/
theorem light_client_position_non_omission
    (Proof : Type) (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb : ℤ → ℤ → ℤ) (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hash : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (steps : List ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true)
    -- the per-turn receipt log and THE WELD (the rotation obligation, per step):
    (logOf : ChainStep → List ℤ) (limbsOf : ChainStep → List ℤ)
    (hweld : ∀ s ∈ steps, CommitBindsMMR hash (limbsOf s)
      (ChainStep.newRoot CH RH cmb compress compressN s) (logOf s))
    -- the queried step + the server's opening of its ATTESTED commitment + a verifying answer:
    {s : ChainStep} (hstep : s ∈ steps)
    {L' : List ℤ} {limbs' : List ℤ}
    (hopen : CommitBindsMMR hash limbs'
      (ChainStep.newRoot CH RH cmb compress compressN s) L')
    -- the two per-instance residuals, at the pairs the extractors NAME for this step:
    (hnc : ¬ CommitColl hash (limbsOf s) limbs' (logOf s) L')
    (hnr : ¬ MRootColl hash L' (logOf s))
    {lo hi : ℕ} {vals : List ℤ}
    (hv : RVerifies L' lo hi vals) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps
      ∧ vals = mrange (logOf s) lo hi
      ∧ (∀ i, lo ≤ i → i ≤ hi → i < (logOf s).length →
          ∃ v, vals[i - lo]? = some v ∧ Opens (logOf s) i v) := by
  have hpin : L' = logOf s := commit_pins_mmr hash (hweld s hstep) hopen hnc hnr
  rw [hpin] at hv
  exact ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN
      agg g steps es hroot,
    rverifies_iff_exact.mp hv, range_complete hv⟩

#assert_axioms commitColl_dischargeable
#assert_axioms commitColl_refutable
#assert_axioms commitColl_refutes_poseidon2CR
#assert_axioms commit_pins_mmr
#assert_axioms light_client_position_non_omission

/-! ## §7 — NON-VACUITY: witnesses TRUE and FALSE on a concrete log.

Log `[111, 222, 333]` (receipt commitments at positions 0, 1, 2), query range `[1, 2]`, on the
computable Horner toy sponge `refSponge` (`Heap` §3 — NOT real crypto; deployment = p3 Poseidon2
behind the CR floor):

  * TRUE — the forest has the binary-decomposition shape (peaks heights `[0, 1]`; appending a 4th
    leaf carries to ONE height-2 peak); the leaves read back; the exact answer `[222, 333]`
    VERIFIES; appends preserve prior ranges (executable prefix stability);
  * FALSE — a SKIPPED position is rejected (`demo_skipped_rejected` — derived from THE keystone);
    a SUBSTITUTED value and a REORDERED answer are rejected (the dense slot pins each value);
    tamper / truncate / extend / reorder each MOVE the root (the executable shadow of
    `mroot_binds_or_collides` — note REORDER is detected, which the sorted map could not even
    express). -/

/-- The demo receipt log: positions 0, 1, 2. -/
def demoLog : List ℤ := [111, 222, 333]

-- The forest is the binary decomposition of 3 = 2 + 1: peak heights [0, 1], youngest first...
#guard (peaksOf demoLog).map PTree.height == [0, 1]
-- ...the leaves read back oldest-first (the recovery keystone, executable)...
#guard forestLeaves (peaksOf demoLog) == demoLog
-- ...and the 4th append CARRIES: 4 = 2² gives ONE peak of height 2 (amortized O(1) shape).
#guard (peaksOf (demoLog ++ [444])).map PTree.height == [2]

-- Positional + range openings compute:
#guard demoLog[1]? == some 222
#guard mrange demoLog 1 2 == [222, 333]
#guard mrange demoLog 0 10 == demoLog               -- clipping at the committed length
#guard rangeCount demoLog.length 1 2 == 2
-- Prefix stability, executable: a later append leaves the prior range VERBATIM.
#guard mrange (demoLog ++ [444]) 1 2 == mrange demoLog 1 2
-- Determinism sanity: same log, same root.
#guard mroot refSponge [111, 222, 333] == mroot refSponge demoLog

-- **Witness FALSE at the root (anti-ghost):** tampering ONE position MOVES the root...
#guard mroot refSponge [111, 999, 333] != mroot refSponge demoLog
-- ...truncating the log moves it (omission is visible at the root)...
#guard mroot refSponge [111, 222] != mroot refSponge demoLog
-- ...forging an extra receipt moves it...
#guard mroot refSponge (demoLog ++ [444]) != mroot refSponge demoLog
-- ...and so does REORDERING (position is part of the commitment — the append-only tooth):
#guard mroot refSponge [222, 111, 333] != mroot refSponge demoLog

/-- The demo forest is mountains (perfect peaks, strictly increasing heights) — the structure
theorem, instantiated. -/
theorem demo_mountains : Mountains (peaksOf demoLog) := peaksOf_mountains demoLog

/-- **Witness TRUE** — the exact answer to range `[1, 2]` VERIFIES. -/
theorem demo_range_verifies : RVerifies demoLog 1 2 [222, 333] :=
  rverifies_iff_exact.mpr (by decide)

/-- **Witness FALSE #1 — a skipped position is REJECTED.** The server drops position 1 and slides
333 into its slot: position 2 then has NO slot (the count breaks). Derived from THE keystone:
a verifying answer would have to carry position 2 at slot 1. -/
theorem demo_skipped_rejected : ¬ RVerifies demoLog 1 2 [333] := by
  intro hv
  obtain ⟨v, hslot, _⟩ := range_complete hv 2 (by norm_num) (by norm_num)
    (by norm_num [demoLog])
  simp at hslot

/-- **Witness FALSE #2 — a substituted value is REJECTED.** Right count, wrong value at slot 0:
the dense opening pins slot 0 to position 1, which holds 222, not 333. -/
theorem demo_substituted_rejected : ¬ RVerifies demoLog 1 2 [333, 333] := by
  intro hv
  exact absurd (hv.2 0 333 (by decide)) (by decide)

/-- **Witness FALSE #3 — a reordered answer is REJECTED** (positions cannot be permuted: each slot
opens its own position). -/
theorem demo_reordered_rejected : ¬ RVerifies demoLog 1 2 [333, 222] := by
  intro hv
  exact absurd (hv.2 0 333 (by decide)) (by decide)

/-- **Witness TRUE #2 — THE HONEST PROVER PAYS NOTHING, FOR EVERY HASH.** The two residuals the
ported §5/§6 endpoints carry are BOTH discharged by a non-equivocating opening — one log, one limb
vector — with no hypothesis on the sponge whatsoever. This is the pole the deleted floor could not
supply: `Poseidon2SpongeCR` is unavailable at the deployed hash even to the honest party, so a
statement conditioned on it fired for nobody. Deliberately UNCONDITIONAL: a satisfiability witness
gated on the refuted floor is itself vacuous, and this campaign has found three of those. -/
theorem demo_honest_opening_discharges_residuals (hash : List ℤ → ℤ) (limbs L : List ℤ) :
    ¬ CommitColl hash limbs limbs L L ∧ ¬ MRootColl hash L L :=
  ⟨commitColl_dischargeable hash limbs L, mrootColl_dischargeable hash L⟩

/-- **Witness FALSE #4 — the residual is ABSENT at a real tamper pair, so the binding half does the
work.** On the genuine demo log against a tampered one, at the toy sponge, `¬ MRootColl` HOLDS — the
ported endpoints cannot be discharged here by taking the collision escape, which is exactly the
failure mode a bare `∃`-collision disjunct would have had (it is unconditionally true at deployed
parameters). Decided, not asserted. -/
theorem demo_residual_absent_at_refSponge :
    ¬ MRootColl refSponge demoLog [111, 999, 333] := by decide

#assert_axioms demo_mountains
#assert_axioms demo_honest_opening_discharges_residuals
#assert_axioms demo_residual_absent_at_refSponge
#assert_axioms demo_range_verifies
#assert_axioms demo_skipped_rejected
#assert_axioms demo_substituted_rejected
#assert_axioms demo_reordered_rejected

end Dregg2.Lightclient.MMR
