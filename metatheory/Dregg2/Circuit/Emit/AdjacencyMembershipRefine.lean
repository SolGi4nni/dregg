/-
# Dregg2.Circuit.Emit.AdjacencyMembershipRefine — the WHOLE-DESCRIPTOR functional-correctness
bridge for the neighbor-adjacency (sorted-set non-membership) family.

## What Rung 0 gave us (`AdjacencyMembershipEmit.lean`) and what this file adds

`AdjacencyMembershipEmit` byte-pins `adjacencyDesc` and proves per-GATE lemmas
(`consecutive_body_zero_iff`, `dir_binary_body_zero_iff`). This file proves the missing
WHOLE-DESCRIPTOR bridge: a trace SATISFYING the descriptor (`Satisfied2`) is a genuine
two-path binary-Merkle authentication transcript of two adjacent leaves under a shared root.

## The functional spec (authored here — `spec_status = NO_LEAN`)

`combine`/`foldNode`/`MembersUnderRoot`/`AdjacentLeavesUnderRoot` are the trace-independent
functional relation the circuit is meant to compute: `leaf_lower` and `leaf_upper` are the leaves
of two authentic dir-ordered Poseidon2 Merkle paths that fold to the SAME committed `root`, at
reconstructed indices that are CONSECUTIVE (`idx_upper = idx_lower + 1`) — the sound
non-membership witness (nothing can sit strictly between two adjacent leaves of a sorted tree).
`foldNode` mirrors `membership_adjacency_air.rs::walk` exactly (dir-ordered `hash_2_to_1`).

## The refinement (`SAT_IMPLIES_SEM`) — proven, with ONE precisely-named residual

`adjacency_sat_refines` : `Satisfied2 adjacencyDesc` + the named Poseidon2 chip carrier
(`ChipTableSound`) FORCE, for the whole trace:
  * each leaf folds AUTHENTICALLY (dir-ordered Poseidon2 combine per active level, index carry,
    cross-row chain) up the tree to its top spine node `*_cur[last]` — `foldNode … = *_cur[last]`;
  * both top parents `*_par[last]` are pinned to the SAME public `root`, and `root` is a genuine
    Poseidon2 hash of the (left,right) pair the last-row lookup carries;
  * the published indices are consecutive (`idx_upper = idx_lower + 1`).
The load-bearing hash binding rides the NAMED carrier `ChipTableSound hash (tf .poseidon2)`
through `chip_lookup_sound` — never assumed on `hash` structurally.

### The residual (status PARTIAL — a real DSL→IR-v2 drift, MODEL-FOUND)

The deployed DSL (`dsl_plonky3.rs:225/240`) lowers `Binary`/`Polynomial` (the child-ordering
gates) as `is_transition = false` → `builder.assert_zero` — they fire on EVERY row, so the LAST
trace row is a real Merkle level (`membership_adjacency_air.rs:77`, "the last trace row is a real
Merkle level"). But `AdjacencyMembershipEmit` maps them to IR-v2 `.base (.gate …)`, whose
`VmConstraint.holdsVm` makes a `.gate` VACUOUS on the last row (`when_transition` semantics). So
the top-level ordering `*_left[last] = dir-order(*_cur[last], *_sib[last])` is NOT forced by the
Lean `Satisfied2`, and the fold cannot be extended the final level to bind `root` to the
reconstructed spine. `adjacency_full_bridge` proves the fragment PLUS exactly this missing fact
(`TopLevelOrdered`) yields the full `AdjacentLeavesUnderRoot` — naming the gap constructively:
the residual is precisely the top-level ordering the IR-v2 `.gate` (when_transition) mapping drops.

## Axiom hygiene
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. The Poseidon2 CR carrier enters ONLY
as the NAMED hypothesis `ChipTableSound hash (tf .poseidon2)` (the chip AIR's own faithfulness),
never as an axiom. NEW file; all imports read-only.
-/
import Dregg2.Circuit.Emit.AdjacencyMembershipEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.AdjacencyMembershipRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Satisfied2 VmTrace envAt Lookup TableId
   WindowConstraint WindowExpr ChipTableSound chip_lookup_sound chipLookupTuple CHIP_RATE
   memLog mapLog)
open Dregg2.Circuit.Emit.AdjacencyMembershipEmit
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (eqToModEq gate_modEq_iff pPrimeInt)

set_option autoImplicit false

/-! ## §0 — Field-denotation glue (mod-`p`, `p` the BabyBear prime).

`holdsVm` / `WindowConstraint.holdsAt` now assert their bodies vanish `≡ 0 [ZMOD p]` (the DEPLOYED
field constraint), not `= 0` over ℤ. For a Merkle FOLD the intermediate spine digests are hashed
again, so the field reduction is LOAD-BEARING: mod-`p` congruence cannot thread through the abstract
`hash`. We recover the genuine ℤ equalities the fold needs from the DEPLOYED range-check
canonicality (`0 ≤ cell < p`, carried as `Canon`) of the stored spine columns — a canonical field
cell is determined by its residue. -/

/-- The deployed range-check invariant on a stored field cell: it is the canonical residue. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- Two canonical field cells that are congruent mod `p` are EQUAL over ℤ (the residue determines the
canonical cell — the field-faithful recovery of a genuine equality). -/
theorem eq_of_modEq_canon {a b : ℤ} (ha : Canon a) (hb : Canon b) (h : a ≡ b [ZMOD 2013265921]) :
    a = b := by
  rw [Int.modEq_iff_dvd] at h
  obtain ⟨k, hk⟩ := h
  obtain ⟨ha0, ha1⟩ := ha
  obtain ⟨hb0, hb1⟩ := hb
  omega

/-- A boolean gate `x·(x-1) ≡ 0 [ZMOD p]` on a CANONICAL cell forces `x ∈ {0,1}` genuinely
(`p` prime ⟹ `p ∣ x ∨ p ∣ (x-1)`; canonicality collapses each to `0`/`1`). -/
theorem bit_of_modEq_canon {x : ℤ} (hc : Canon x) (h : x * (x - 1) ≡ 0 [ZMOD 2013265921]) :
    x = 0 ∨ x = 1 := by
  rw [Int.modEq_zero_iff_dvd] at h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp h with hd | hd
  · left; obtain ⟨k, hk⟩ := hd; omega
  · right; obtain ⟨k, hk⟩ := hd; omega

/-! ## §1 — the functional spec (trace-independent; the twin of `membership_adjacency_air.rs::walk`). -/

/-- One dir-ordered Poseidon2 Merkle combine: `dir = 1` ⇒ the running node is the RIGHT child
(`parent = hash [sib, cur]`); else the LEFT child (`parent = hash [cur, sib]`). The exact
`(step.sibling, cur)` vs `(cur, step.sibling)` ordering of the hand AIR's `walk`. -/
def combine (hash : List ℤ → ℤ) (dir cur sib : ℤ) : ℤ :=
  if dir = 1 then hash [sib, cur] else hash [cur, sib]

/-- Fold a leaf up a list of `(dir, sibling)` path steps (level 0 first) — the reconstructed root. -/
def foldNode (hash : List ℤ → ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ)) : ℤ :=
  steps.foldl (fun acc s => combine hash s.1 acc s.2) leaf

/-- Folding over an appended final step is one more combine — the fold's recursion at the top. -/
theorem foldNode_concat (hash : List ℤ → ℤ) (leaf : ℤ) (steps : List (ℤ × ℤ)) (d s : ℤ) :
    foldNode hash leaf (steps ++ [(d, s)]) = combine hash d (foldNode hash leaf steps) s := by
  simp [foldNode, List.foldl_append]

/-- **`MembersUnderRoot hash leaf root steps`** — `leaf` authenticates to `root` along `steps`
(the dir-ordered binary-Merkle path). The membership relation the circuit is meant to certify. -/
def MembersUnderRoot (hash : List ℤ → ℤ) (leaf root : ℤ) (steps : List (ℤ × ℤ)) : Prop :=
  foldNode hash leaf steps = root

/-- **`AdjacentLeavesUnderRoot`** — THE FUNCTIONAL SPEC: `leafLo` and `leafHi` are the leaves of
two authentic Poseidon2-Merkle paths that reach the SAME `root`, at consecutive indices
(`idxHi = idxLo + 1`). Two adjacent leaves of a committed sorted tree — the sound non-membership
witness for any key strictly between `leafLo` and `leafHi`. -/
def AdjacentLeavesUnderRoot (hash : List ℤ → ℤ)
    (leafLo leafHi root idxLo idxHi : ℤ) : Prop :=
  (∃ stepsLo, MembersUnderRoot hash leafLo root stepsLo) ∧
  (∃ stepsHi, MembersUnderRoot hash leafHi root stepsHi) ∧
  idxHi = idxLo + 1

/-! ## §2 — one authentic Merkle level, forced by the row gates + the chip carrier. -/

/-- **The per-level authenticity core.** The three ordering/binary gates (`dir` binary, `left`/
`right` = dir-ordering of `(cur, sib)`) plus the chip-forced `par = hash [left, right]` collapse
to `par = combine hash dir cur sib` — the genuine dir-ordered Poseidon2 combine. Pure arithmetic
over one row; the load-bearing crypto (`par = hash [left, right]`) is supplied by the caller
through the named chip carrier. -/
theorem combine_of_gates (hash : List ℤ → ℤ) (a : Assignment)
    (cur sib dir left right par : Nat)
    (hcDir : Canon (a dir)) (hcCur : Canon (a cur)) (hcSib : Canon (a sib))
    (hcLeft : Canon (a left)) (hcRight : Canon (a right))
    (hdir : (dirBinaryBody dir).eval a ≡ 0 [ZMOD 2013265921])
    (hleft : (leftOrderBody cur sib dir left).eval a ≡ 0 [ZMOD 2013265921])
    (hright : (rightOrderBody cur sib dir right).eval a ≡ 0 [ZMOD 2013265921])
    (hpar : a par = hash [a left, a right]) :
    a par = combine hash (a dir) (a cur) (a sib) := by
  -- the direction bit is genuinely `0`/`1` (field bit + canonicality).
  have hbin : a dir = 0 ∨ a dir = 1 := by
    have key : (dirBinaryBody dir).eval a = a dir * (a dir - 1) := by
      simp only [dirBinaryBody, negE, EmittedExpr.eval]; ring
    rw [key] at hdir
    exact bit_of_modEq_canon hcDir hdir
  -- the ordering gates give the child columns mod `p`; canonicality lifts to genuine equalities.
  have hleftC : a left ≡ a cur + a dir * a sib - a dir * a cur [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [leftOrderBody, negE, EmittedExpr.eval]; ring)).mp hleft
  have hrightC : a right ≡ a sib + a dir * a cur - a dir * a sib [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [rightOrderBody, negE, EmittedExpr.eval]; ring)).mp hright
  rcases hbin with hd | hd
  · have hl : a left = a cur :=
      eq_of_modEq_canon hcLeft hcCur (by have := hleftC; rw [hd] at this; simpa using this)
    have hr : a right = a sib :=
      eq_of_modEq_canon hcRight hcSib (by have := hrightC; rw [hd] at this; simpa using this)
    rw [hpar, hl, hr]; unfold combine; rw [if_neg (by rw [hd]; decide)]
  · have hl : a left = a sib :=
      eq_of_modEq_canon hcLeft hcSib (by have := hleftC; rw [hd] at this; simpa using this)
    have hr : a right = a cur :=
      eq_of_modEq_canon hcRight hcCur (by have := hrightC; rw [hd] at this; simpa using this)
    rw [hpar, hl, hr]; unfold combine; rw [if_pos hd]

/-! ## §3 — extracting the row facts from `Satisfied2` (the descriptor's own constraints). -/

/-- The membership tactic: every constraint we name is literally in `adjacencyDesc.constraints`. -/
local macro "adj_mem" : tactic =>
  `(tactic| (show _ ∈ adjacencyConstraints;
             simp [adjacencyConstraints, adjacencyConstraintsCore, adjLastOrderFix, adjLastIdxFix,
               pathBlock]))

/-- The window's `nxt` field at row `j` IS the `loc` field at row `j+1` (`envAt` reads the same
`getD (j+1)` row). -/
theorem envAt_nxt_loc (t : VmTrace) (j : Nat) : (envAt t j).nxt = (envAt t (j + 1)).loc := rfl

/-- A declared `.gate` fires on any ACTIVE (non-last) row: its body vanishes. -/
theorem activeGateZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = false)
    (body : EmittedExpr)
    (hmem : VmConstraint2.base (.gate body) ∈ adjacencyDesc.constraints) :
    body.eval (envAt t j).loc ≡ 0 [ZMOD 2013265921] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h

/-- A declared transition `copyWindow hi lo` copies `next[hi] ≡ local[lo] [ZMOD p]` on any active
row. -/
theorem activeCopyZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (j : Nat) (hj : j < t.rows.length) (hlast : (j + 1 == t.rows.length) = false)
    (hi lo : Nat)
    (hmem : VmConstraint2.windowGate (copyWindow hi lo) ∈ adjacencyDesc.constraints) :
    (envAt t j).nxt hi ≡ (envAt t j).loc lo [ZMOD 2013265921] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, WindowConstraint.holdsAt, copyWindow, hlast,
    WindowExpr.eval, ite_true, true_implies] at h
  exact (gate_modEq_iff (by ring)).mp h

/-- A declared chip lookup, against the NAMED sound chip table, forces `par = hash [left, right]`
on ANY row (the lookup is not gated). This is where the Poseidon2 CR carrier enters. -/
theorem lookupChip {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (j : Nat) (hj : j < t.rows.length) (left right par : Nat) (lanes : List Nat)
    (hmem : VmConstraint2.lookup ⟨TableId.poseidon2,
              chipLookupTuple [.var left, .var right] par lanes⟩ ∈ adjacencyDesc.constraints) :
    (envAt t j).loc par = hash [(envAt t j).loc left, (envAt t j).loc right] := by
  have h := hsat.rowConstraints j hj _ hmem
  simp only [VmConstraint2.holdsAt, Lookup.holdsAt] at h
  have hs := chip_lookup_sound hash (t.tf .poseidon2) hChip (envAt t j).loc
    [.var left, .var right] par lanes (by show (2 : Nat) ≤ CHIP_RATE; decide) h
  simpa [EmittedExpr.eval] using hs

/-- A declared first-row PI binding pins `loc[col] = pub[k]` on row 0. -/
theorem firstPi {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.first col k) ∈ adjacencyDesc.constraints) :
    (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have h := hsat.rowConstraints 0 hlen _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm] at h
  exact h (by decide)

/-- A declared last-row PI binding pins `loc[col] = pub[k]` on the last row. -/
theorem lastPi {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (col k : Nat)
    (hmem : VmConstraint2.base (.piBinding VmRow.last col k) ∈ adjacencyDesc.constraints) :
    (envAt t (t.rows.length - 1)).loc col ≡ t.pub k [ZMOD 2013265921] := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simp [this]
  have h := hsat.rowConstraints _ hLlt _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h (by decide)

/-- A declared last-row boundary body vanishes on the last row. -/
theorem lastBoundaryZero {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hlen : 0 < t.rows.length) (body : EmittedExpr)
    (hmem : VmConstraint2.base (.boundary VmRow.last body) ∈ adjacencyDesc.constraints) :
    body.eval (envAt t (t.rows.length - 1)).loc ≡ 0 [ZMOD 2013265921] := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  have hlast : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    have : t.rows.length - 1 + 1 = t.rows.length := by omega
    simp [this]
  have h := hsat.rowConstraints _ hLlt _ hmem
  simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, hlast] at h
  exact h (by decide)

/-! ## §4 — the multi-row fold: an authentic path to the top spine node. -/

/-- The reconstructed `(dir, sib)` path steps of a single authentication path over rows `0..j-1`. -/
def pathSteps (t : VmTrace) (dir sib : Nat) (j : Nat) : List (ℤ × ℤ) :=
  (List.range j).map (fun k => ((envAt t k).loc dir, (envAt t k).loc sib))

/-- **The fold theorem (generic over one path's columns).** Given that every active level advances
`cur` by an authentic combine (`hstep`), the leaf at row 0 folds — level by level — to the value
of `cur` at every row `j`. The whole-trace Merkle recomposition, by induction on the level. -/
theorem fold_generic (hash : List ℤ → ℤ) (t : VmTrace) (cur dir sib : Nat)
    (hstep : ∀ j, j + 1 < t.rows.length →
       (envAt t (j + 1)).loc cur
         = combine hash ((envAt t j).loc dir) ((envAt t j).loc cur) ((envAt t j).loc sib)) :
    ∀ j, j < t.rows.length →
      foldNode hash ((envAt t 0).loc cur) (pathSteps t dir sib j) = (envAt t j).loc cur := by
  intro j
  induction j with
  | zero => intro _; simp [foldNode, pathSteps]
  | succ n ih =>
    intro hlt
    have hn : n < t.rows.length := by omega
    have hexpand : pathSteps t dir sib (n + 1)
        = pathSteps t dir sib n ++ [((envAt t n).loc dir, (envAt t n).loc sib)] := by
      simp [pathSteps, List.range_succ]
    rw [hexpand, foldNode_concat, ih hn, hstep n hlt]

/-- **The deployed range-check envelope for one path.** Every stored spine column of the path is a
canonical field cell (`0 ≤ · < p`, the deployed range check) on every row. This is what lets the
mod-`p` continuity / ordering constraints be lifted to the genuine ℤ equalities the hash fold needs
(the intermediate digests are re-hashed, so mod-`p` congruence cannot thread through `hash`). -/
def PathCanon (t : VmTrace) (cur sib dir left right par : Nat) : Prop :=
  ∀ j, j < t.rows.length →
    Canon ((envAt t j).loc cur) ∧ Canon ((envAt t j).loc sib) ∧ Canon ((envAt t j).loc dir)
    ∧ Canon ((envAt t j).loc left) ∧ Canon ((envAt t j).loc right) ∧ Canon ((envAt t j).loc par)

/-- The per-active-level step for ANY path block `(cur, sib, dir, left, right, par)` welded to its
chip lookup lanes — chain continuity (`cur[j+1] = par[j]`, recovered from the mod-`p` window gate via
canonicality) composed with the combine core. The `mem*` hypotheses are the six constraint-membership
facts (discharged by `adj_mem` at the call). -/
theorem step_of_sat {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
    {maddrs : List ℤ} (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (cur sib dir left right par : Nat) (lanes : List Nat)
    (hcanon : PathCanon t cur sib dir left right par)
    (memDir : VmConstraint2.base (.gate (dirBinaryBody dir)) ∈ adjacencyDesc.constraints)
    (memLeft : VmConstraint2.base (.gate (leftOrderBody cur sib dir left))
                 ∈ adjacencyDesc.constraints)
    (memRight : VmConstraint2.base (.gate (rightOrderBody cur sib dir right))
                 ∈ adjacencyDesc.constraints)
    (memLook : VmConstraint2.lookup ⟨TableId.poseidon2,
                 chipLookupTuple [.var left, .var right] par lanes⟩
                 ∈ adjacencyDesc.constraints)
    (memChain : VmConstraint2.windowGate (copyWindow cur par) ∈ adjacencyDesc.constraints) :
    ∀ j, j + 1 < t.rows.length →
      (envAt t (j + 1)).loc cur
        = combine hash ((envAt t j).loc dir) ((envAt t j).loc cur) ((envAt t j).loc sib) := by
  intro j hj1
  have hj : j < t.rows.length := by omega
  have hlast : (j + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne]; omega
  obtain ⟨hcCur, hcSib, hcDir, hcLeft, hcRight, hcPar⟩ := hcanon j hj
  have hcCurNext := (hcanon (j + 1) hj1).1
  have hchain : (envAt t (j + 1)).loc cur = (envAt t j).loc par := by
    have hc := activeCopyZero hsat j hj hlast cur par memChain
    rw [envAt_nxt_loc] at hc
    exact eq_of_modEq_canon hcCurNext hcPar hc
  have hcombine := combine_of_gates hash (envAt t j).loc cur sib dir left right par
    hcDir hcCur hcSib hcLeft hcRight
    (activeGateZero hsat j hj hlast _ memDir)
    (activeGateZero hsat j hj hlast _ memLeft)
    (activeGateZero hsat j hj hlast _ memRight)
    (lookupChip hsat hChip j hj left right par lanes memLook)
  rw [hchain]; exact hcombine

/-! ## §5 — the whole-descriptor refinement (SAT_IMPLIES_SEM), and the named residual. -/

/-- **The deployed range-check envelope for the WHOLE adjacency descriptor.** Bundles the per-path
canonicality of both spine paths, the canonicality of the published leaf/root inputs, and the
canonicality of the last-row index cells + their in-circuit reconstructions. Each field is a
DEPLOYED range-check invariant (`0 ≤ · < p`); together they lift every mod-`p` field constraint the
descriptor asserts to the genuine ℤ equalities the Merkle fold + index reconstruction need. The
concrete witness (`concrete_canon`) discharges it, so the envelope is non-vacuous. -/
structure AdjacencyCanon (t : VmTrace) : Prop where
  pathL : PathCanon t L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR
  pathU : PathCanon t U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR
  leafLo : Canon (t.pub PI_LEAF_LOWER)
  leafHi : Canon (t.pub PI_LEAF_UPPER)
  root : Canon (t.pub PI_ROOT)
  idxUp : Canon (t.pub PI_IDX_UPPER)
  idxLoSucc : Canon (t.pub PI_IDX_LOWER + 1)
  idxOutL : Canon ((envAt t (t.rows.length - 1)).loc L_IDX_OUT)
  idxOutU : Canon ((envAt t (t.rows.length - 1)).loc U_IDX_OUT)
  reconL : Canon ((envAt t (t.rows.length - 1)).loc L_IDX_IN
    + (envAt t (t.rows.length - 1)).loc L_DIR * (envAt t (t.rows.length - 1)).loc POW)
  reconU : Canon ((envAt t (t.rows.length - 1)).loc U_IDX_IN
    + (envAt t (t.rows.length - 1)).loc U_DIR * (envAt t (t.rows.length - 1)).loc POW)

/-- The proven fragment: a satisfying trace is an authentic two-path Merkle transcript of adjacent
leaves, up to (and excluding) the single top-level combine the IR-v2 `.gate` mapping drops. -/
structure AdjacencyAuthFragment (hash : List ℤ → ℤ) (t : VmTrace) : Prop where
  /-- The lower leaf folds authentically up to its top spine node `L_CUR[last]`. -/
  foldLower : ∃ steps, foldNode hash (t.pub PI_LEAF_LOWER) steps
                = (envAt t (t.rows.length - 1)).loc L_CUR
  /-- The upper leaf folds authentically up to its top spine node `U_CUR[last]`. -/
  foldUpper : ∃ steps, foldNode hash (t.pub PI_LEAF_UPPER) steps
                = (envAt t (t.rows.length - 1)).loc U_CUR
  /-- The lower top parent is pinned to the committed public root. -/
  rootLower : (envAt t (t.rows.length - 1)).loc L_PAR = t.pub PI_ROOT
  /-- The upper top parent is pinned to the SAME committed public root. -/
  rootUpper : (envAt t (t.rows.length - 1)).loc U_PAR = t.pub PI_ROOT
  /-- The root is a genuine Poseidon2 hash of the lower path's top `(left, right)` pair. -/
  rootHashedLower : t.pub PI_ROOT
    = hash [(envAt t (t.rows.length - 1)).loc L_LEFT, (envAt t (t.rows.length - 1)).loc L_RIGHT]
  /-- The root is a genuine Poseidon2 hash of the upper path's top `(left, right)` pair. -/
  rootHashedUpper : t.pub PI_ROOT
    = hash [(envAt t (t.rows.length - 1)).loc U_LEFT, (envAt t (t.rows.length - 1)).loc U_RIGHT]
  /-- The published indices are consecutive (the internalized catch tooth). -/
  consecutive : t.pub PI_IDX_UPPER = t.pub PI_IDX_LOWER + 1
  /-- The lower published index at the last row is the GENUINE in-circuit reconstruction
  `idx_in + dir*pow` (the landed `adjLastIdxFix` binding) — not a free, prover-chosen value. -/
  idxReconLower : (envAt t (t.rows.length - 1)).loc L_IDX_OUT
    = (envAt t (t.rows.length - 1)).loc L_IDX_IN
      + (envAt t (t.rows.length - 1)).loc L_DIR * (envAt t (t.rows.length - 1)).loc POW
  /-- The upper published index at the last row is the GENUINE in-circuit reconstruction (twin). -/
  idxReconUpper : (envAt t (t.rows.length - 1)).loc U_IDX_OUT
    = (envAt t (t.rows.length - 1)).loc U_IDX_IN
      + (envAt t (t.rows.length - 1)).loc U_DIR * (envAt t (t.rows.length - 1)).loc POW

/-- **`adjacency_sat_refines` — THE WHOLE-DESCRIPTOR BRIDGE (SAT_IMPLIES_SEM, sound fragment).**
A `Satisfied2` of `adjacencyDesc`, against the NAMED Poseidon2 chip carrier, is a genuine
two-path binary-Merkle authentication transcript of two consecutive-index leaves under one shared
committed root (`AdjacencyAuthFragment`). The one un-forced fact (the top-level combine ordering)
is the named residual — see `adjacency_full_bridge`. -/
theorem adjacency_sat_refines {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hc : AdjacencyCanon t) :
    AdjacencyAuthFragment hash t := by
  have hLlt : t.rows.length - 1 < t.rows.length := by omega
  -- the two authentic folds (to the top spine node), leaf pinned to its PI.
  have hstepL := step_of_sat hsat hChip L_CUR L_SIB L_DIR L_LEFT L_RIGHT L_PAR L_PAR_LANES
    hc.pathL (by adj_mem) (by adj_mem) (by adj_mem) (by adj_mem) (by adj_mem)
  have hstepU := step_of_sat hsat hChip U_CUR U_SIB U_DIR U_LEFT U_RIGHT U_PAR U_PAR_LANES
    hc.pathU (by adj_mem) (by adj_mem) (by adj_mem) (by adj_mem) (by adj_mem)
  have hfoldL := fold_generic hash t L_CUR L_DIR L_SIB hstepL _ hLlt
  have hfoldU := fold_generic hash t U_CUR U_DIR U_SIB hstepU _ hLlt
  -- the leaf pins, lifted to genuine ℤ equalities by canonicality (leaf cell + published input).
  have hleafL : (envAt t 0).loc L_CUR = t.pub PI_LEAF_LOWER :=
    eq_of_modEq_canon ((hc.pathL 0 hlen).1) hc.leafLo (firstPi hsat hlen L_CUR PI_LEAF_LOWER (by adj_mem))
  have hleafU : (envAt t 0).loc U_CUR = t.pub PI_LEAF_UPPER :=
    eq_of_modEq_canon ((hc.pathU 0 hlen).1) hc.leafHi (firstPi hsat hlen U_CUR PI_LEAF_UPPER (by adj_mem))
  rw [hleafL] at hfoldL
  rw [hleafU] at hfoldU
  -- the boundary pins, lifted to genuine ℤ equalities by canonicality.
  have hrootL : (envAt t (t.rows.length - 1)).loc L_PAR = t.pub PI_ROOT :=
    eq_of_modEq_canon ((hc.pathL _ hLlt).2.2.2.2.2) hc.root (lastPi hsat hlen L_PAR PI_ROOT (by adj_mem))
  have hrootU : (envAt t (t.rows.length - 1)).loc U_PAR = t.pub PI_ROOT :=
    eq_of_modEq_canon ((hc.pathU _ hLlt).2.2.2.2.2) hc.root (lastPi hsat hlen U_PAR PI_ROOT (by adj_mem))
  have hidxL := lastPi hsat hlen L_IDX_OUT PI_IDX_LOWER (by adj_mem)
  have hidxU := lastPi hsat hlen U_IDX_OUT PI_IDX_UPPER (by adj_mem)
  -- root is a genuine hash of the last-row (left,right) pair (the lookup fires on every row).
  have hhashL := lookupChip hsat hChip _ hLlt L_LEFT L_RIGHT L_PAR L_PAR_LANES (by adj_mem)
  have hhashU := lookupChip hsat hChip _ hLlt U_LEFT U_RIGHT U_PAR U_PAR_LANES (by adj_mem)
  -- consecutiveness: the last-row catch tooth (mod p) + the two index pins, lifted by canonicality.
  have hcons0 := lastBoundaryZero hsat hlen consecutiveBody (by adj_mem)
  have hconsC : (envAt t (t.rows.length - 1)).loc U_IDX_OUT
      ≡ (envAt t (t.rows.length - 1)).loc L_IDX_OUT + 1 [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [consecutiveBody, negE, EmittedExpr.eval]; ring)).mp hcons0
  have hcons : t.pub PI_IDX_UPPER = t.pub PI_IDX_LOWER + 1 :=
    eq_of_modEq_canon hc.idxUp hc.idxLoSucc
      ((hidxU.symm.trans hconsC).trans (hidxL.add_right 1))
  -- index reconstruction: the last-row `adjLastIdxFix` boundaries bind `idx_out ≡ idx_in+dir*pow`,
  -- lifted to genuine ℤ by canonicality of the published index and its reconstruction.
  have hidxReconL0 := lastBoundaryZero hsat hlen (idxStepBody L_DIR L_IDX_IN L_IDX_OUT) (by adj_mem)
  have hidxReconL : (envAt t (t.rows.length - 1)).loc L_IDX_OUT
      = (envAt t (t.rows.length - 1)).loc L_IDX_IN
        + (envAt t (t.rows.length - 1)).loc L_DIR * (envAt t (t.rows.length - 1)).loc POW :=
    eq_of_modEq_canon hc.idxOutL hc.reconL
      ((gate_modEq_iff (by simp only [idxStepBody, negE, EmittedExpr.eval]; ring)).mp hidxReconL0)
  have hidxReconU0 := lastBoundaryZero hsat hlen (idxStepBody U_DIR U_IDX_IN U_IDX_OUT) (by adj_mem)
  have hidxReconU : (envAt t (t.rows.length - 1)).loc U_IDX_OUT
      = (envAt t (t.rows.length - 1)).loc U_IDX_IN
        + (envAt t (t.rows.length - 1)).loc U_DIR * (envAt t (t.rows.length - 1)).loc POW :=
    eq_of_modEq_canon hc.idxOutU hc.reconU
      ((gate_modEq_iff (by simp only [idxStepBody, negE, EmittedExpr.eval]; ring)).mp hidxReconU0)
  refine ⟨⟨_, hfoldL⟩, ⟨_, hfoldU⟩, hrootL, hrootU, ?_, ?_, hcons, hidxReconL, hidxReconU⟩
  · rw [hrootL] at hhashL; exact hhashL
  · rw [hrootU] at hhashU; exact hhashU

/-- **The named residual (`TopLevelOrdered`).** The single fact `Satisfied2` does NOT force: on the
LAST trace row, each path's `par` is the authentic dir-ordered combine of its `(cur, sib)`. This is
exactly what the DSL's every-row `Binary`/`Polynomial` ordering gates enforce
(`dsl_plonky3.rs:225/240`, `is_transition = false`) but the IR-v2 `.base (.gate …)` mapping drops
on the last row (`VmConstraint.holdsVm` gives `.gate` `True` when `isLast`). -/
def TopLevelOrdered (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  (envAt t (t.rows.length - 1)).loc L_PAR
      = combine hash ((envAt t (t.rows.length - 1)).loc L_DIR)
          ((envAt t (t.rows.length - 1)).loc L_CUR) ((envAt t (t.rows.length - 1)).loc L_SIB) ∧
  (envAt t (t.rows.length - 1)).loc U_PAR
      = combine hash ((envAt t (t.rows.length - 1)).loc U_DIR)
          ((envAt t (t.rows.length - 1)).loc U_CUR) ((envAt t (t.rows.length - 1)).loc U_SIB)

/-- **`adjacency_full_bridge` — the residual made constructive (SAT + the ONE missing fact ⟹ full
spec).** The proven fragment PLUS `TopLevelOrdered` (the top-level ordering the `.gate` mapping
drops) yields the complete `AdjacentLeavesUnderRoot`: both leaves are the leaves of full authentic
Poseidon2-Merkle paths reaching the same committed root at consecutive indices. This isolates the
PARTIAL residual to exactly one named, currently-un-forced constraint — nothing else is missing. -/
theorem adjacency_full_bridge {hash : List ℤ → ℤ} {t : VmTrace} {minit : ℤ → ℤ}
    {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ}
    (hlen : 0 < t.rows.length)
    (hsat : Satisfied2 hash adjacencyDesc minit mfin maddrs t)
    (hChip : ChipTableSound hash (t.tf .poseidon2))
    (hc : AdjacencyCanon t)
    (htop : TopLevelOrdered hash t) :
    AdjacentLeavesUnderRoot hash (t.pub PI_LEAF_LOWER) (t.pub PI_LEAF_UPPER)
      (t.pub PI_ROOT) (t.pub PI_IDX_LOWER) (t.pub PI_IDX_UPPER) := by
  have frag := adjacency_sat_refines hlen hsat hChip hc
  obtain ⟨stepsL, hfoldL⟩ := frag.foldLower
  obtain ⟨stepsU, hfoldU⟩ := frag.foldUpper
  obtain ⟨htopL, htopU⟩ := htop
  refine ⟨?_, ?_, frag.consecutive⟩
  · -- extend the lower fold by the top level: fold ++ [(L_DIR[last], L_SIB[last])] = root.
    refine ⟨stepsL ++ [((envAt t (t.rows.length - 1)).loc L_DIR,
                        (envAt t (t.rows.length - 1)).loc L_SIB)], ?_⟩
    rw [MembersUnderRoot, foldNode_concat, hfoldL, ← htopL, frag.rootLower]
  · refine ⟨stepsU ++ [((envAt t (t.rows.length - 1)).loc U_DIR,
                        (envAt t (t.rows.length - 1)).loc U_SIB)], ?_⟩
    rw [MembersUnderRoot, foldNode_concat, hfoldU, ← htopU, frag.rootUpper]

/-! ## §6 — non-vacuity of the SPEC (the anti-scar: the target is TRUE and FALSE, not a stub). -/

/-- A concrete little-endian digit hash — distinguishes child order (`[a,b] ↦ 10a+b`). -/
private def demoHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- **Witness TRUE — the spec is INHABITED.** The sibling leaves `10` (index 0, left child) and
`20` (index 1, right child) are two authentic one-level paths BOTH reaching the shared parent
`root = 1020` (`combine 0 10 20 = combine 1 20 10 = demoHash [10, 20]`), at consecutive indices
`0, 1`. A concrete satisfying witness of the functional spec. -/
theorem demo_adjacent :
    AdjacentLeavesUnderRoot demoHash 10 20 1020 0 1 := by
  refine ⟨⟨[(0, 20)], ?_⟩, ⟨[(1, 10)], ?_⟩, rfl⟩
  · unfold MembersUnderRoot; decide
  · unfold MembersUnderRoot; decide

/-- **Witness FALSE — the spec CONSTRAINS.** The very same paths with a NON-consecutive index pair
(`0, 2`) are NOT accepted: the consecutiveness conjunct bites. A `True`/`P → P` bridge could not
separate this. -/
theorem demo_not_adjacent :
    ¬ AdjacentLeavesUnderRoot demoHash 10 20 1020 0 2 := by
  rintro ⟨_, _, hc⟩
  omega

-- The combine is ORDER-SENSITIVE (dir genuinely selects the child slot) — not a constant fold:
#guard decide (combine demoHash 0 1 2 ≠ combine demoHash 1 1 2)   -- 102 ≠ 201
-- foldNode genuinely recomposes a two-level path:
#guard foldNode demoHash 1 [(0, 2), (0, 3)] == 10203              -- combine 0 (combine 0 1 2) 3

/-! ## §6b — THE ANTI-SCAR: a CONCRETE trace that genuinely SATISFIES the descriptor (the `Satisfied2`
hypothesis is INHABITED — not an empty/unsatisfiable antecedent), and a concrete trace that FAILS it
(the descriptor genuinely REJECTS). A degenerate depth-1 witness: two sibling leaves `10, 20` at
indices `0, 1`, genuinely dir-ordered as the children of their shared parent (`cHash [10,20] = 1020`),
which is the committed root. (The children must be the GENUINE dir-ordering of `(cur, sib)` — the
last-row ordering fix now bites any forged top pair.) -/

private def cHash : List ℤ → ℤ := fun xs => xs.foldl (fun acc x => acc * 100 + x) 0

/-- The single satisfying row: leaves `10`/`20` as SIBLINGS, genuinely dir-ordered children
(`L_LEFT=L_CUR=10`, `L_RIGHT=L_SIB=20`, `L_DIR=0`; `U_LEFT=10=U_SIB`, `U_RIGHT=20=U_CUR`, `U_DIR=1`),
both parents = root `1020`, indices `0`/`1`, `pow = 1`. -/
private def cRow : Assignment := fun c =>
  if c = L_CUR then 10 else if c = L_SIB then 20 else if c = L_LEFT then 10
  else if c = L_RIGHT then 20 else if c = L_PAR then 1020
  else if c = U_CUR then 20 else if c = U_SIB then 10 else if c = U_DIR then 1
  else if c = U_LEFT then 10 else if c = U_RIGHT then 20 else if c = U_PAR then 1020
  else if c = U_IDX_OUT then 1 else if c = POW then 1 else 0

private def cPub : Assignment := fun k =>
  if k = PI_ROOT then 1020 else if k = PI_LEAF_LOWER then 10
  else if k = PI_LEAF_UPPER then 20 else if k = PI_IDX_UPPER then 1 else 0

private def cTbl : List (List ℤ) :=
  [Dregg2.Circuit.DescriptorIR2.chipRow cHash [10, 20] (List.replicate 7 0)]

private def cTrace : VmTrace :=
  { rows := [cRow], pub := cPub
    tf := fun tid => match tid with | .poseidon2 => cTbl | _ => [] }

/-- The concrete chip table is genuinely SOUND (every row is a real `chipRow` of `cHash`) — so the
NAMED carrier `ChipTableSound` is realizable, not just assumed. -/
theorem concrete_chipSound : ChipTableSound cHash (cTrace.tf .poseidon2) := by
  intro r hr
  simp only [cTrace, cTbl, List.mem_singleton] at hr
  exact ⟨[10, 20], List.replicate 7 0, by decide, by decide, hr⟩

/-- **The `Satisfied2` HYPOTHESIS IS INHABITED.** The concrete trace genuinely satisfies the deployed
descriptor's whole denotation — every one of the 32 constraints holds on the single row (including the
last-row ordering fix, which the genuinely dir-ordered children satisfy), and the (empty) memory/table
legs close. This refutes the vacuity scar: `adjacency_sat_refines` is NOT a theorem over an empty
antecedent. -/
theorem concrete_sat :
    Satisfied2 cHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] cTrace := by
  have hmemlog : memLog adjacencyDesc cTrace = [] := rfl
  have hmaplog : mapLog adjacencyDesc cTrace = [] := rfl
  have hF : (0 == 0) = true := rfl
  have hL : (0 + 1 == cTrace.rows.length) = true := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    rw [show cTrace.rows.length = 1 from rfl] at hi
    interval_cases i
    rw [show adjacencyDesc.constraints = adjacencyConstraints from rfl] at hc
    simp only [adjacencyConstraints, adjacencyConstraintsCore, adjLastOrderFix, adjLastIdxFix,
      pathBlock, List.cons_append, List.nil_append] at hc
    fin_cases hc <;>
      simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, WindowConstraint.holdsAt,
        copyWindow, Lookup.holdsAt, Int.ModEq, hF, hL] <;>
      decide
  · intro i _; trivial
  · intro i _ r hr; simp [adjacencyDesc] at hr
  · exact List.nodup_nil
  · intro op hop; rw [hmemlog] at hop; simp at hop
  · rw [hmemlog]; trivial
  · rw [hmemlog]; exact Dregg2.Circuit.DescriptorIR2.memCheck_nil _ _
  · rw [hmemlog]; rfl
  · rw [hmaplog]; rfl

/-- **The canonicality envelope is genuinely INHABITED** for the concrete trace — every stored spine
column, published input, and index reconstruction is a small canonical field value. So
`adjacency_sat_refines` does NOT rest on a vacuous range-check hypothesis. -/
theorem concrete_canon : AdjacencyCanon cTrace := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have hj0 : j = 0 := by have : cTrace.rows.length = 1 := rfl; omega
    subst hj0
    exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
           ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  · intro j hj
    have hj0 : j = 0 := by have : cTrace.rows.length = 1 := rfl; omega
    subst hj0
    exact ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
           ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

/-- The bridge genuinely APPLIES to the concrete inhabited instance: all FOUR hypotheses
(`Satisfied2`, `ChipTableSound`, `0 < length`, the canonicality envelope) are jointly satisfied. -/
example : AdjacencyAuthFragment cHash cTrace :=
  adjacency_sat_refines (by decide) concrete_sat concrete_chipSound concrete_canon

/-- The FAILING trace: identical, but `U_IDX_OUT = 2` breaks the internalized consecutiveness catch
tooth (`2 - 0 - 1 = 1 ≠ 0`). -/
private def cRowBad : Assignment := fun c => if c = U_IDX_OUT then 2 else cRow c

private def cTraceBad : VmTrace := { cTrace with rows := [cRowBad] }

/-- **The descriptor genuinely REJECTS.** The last-row consecutiveness boundary bites: no
`Satisfied2` exists for the non-consecutive trace. (The constraint is load-bearing, not decorative.) -/
theorem concrete_fail :
    ¬ Satisfied2 cHash adjacencyDesc (fun _ => 0) (fun _ => (0, 0)) [] cTraceBad := by
  intro h
  have hmem : VmConstraint2.base (.boundary VmRow.last consecutiveBody)
      ∈ adjacencyDesc.constraints := by adj_mem
  -- the last-row consecutiveness boundary forces its body `≡ 0 [ZMOD p]`; on the bad row the body is
  -- `2 − 0 − 1 = 1`, and `p ∤ 1`, so no satisfying assignment exists.
  have h0 := lastBoundaryZero h (by decide) consecutiveBody hmem
  rw [Int.modEq_zero_iff_dvd,
    show consecutiveBody.eval (envAt cTraceBad (cTraceBad.rows.length - 1)).loc = 1 from rfl] at h0
  omega

/-! ## §7 — axiom hygiene. -/

#assert_axioms combine_of_gates
#assert_axioms fold_generic
#assert_axioms adjacency_sat_refines
#assert_axioms adjacency_full_bridge
#assert_axioms concrete_sat
#assert_axioms concrete_fail

end Dregg2.Circuit.Emit.AdjacencyMembershipRefine
