/-
# Dregg2.Circuit.Emit.RotWideCompactE1 — DELETE the DEAD v1-FACE column bands from the WIDE
members (the second allocator flag-day: `docs/EFFICIENCY-BACKLOG-circuit-minimality.md` item E1),
by verified per-member column compaction.

## What this module is

Item E1: on every wide registry member (already S2-compacted), a per-member band of columns is
DEAD — referenced by ZERO surviving constraint, hash site, or range tooth: the retired v1 aux
band (`AUX_BASE = 90 .. 187`, including the entire 60-column v1 balance bit-decomposition band
superseded by the 15-bit-limb avail weld), the gentian refuse tail, and the appendix scratch
bands the note/heap/refusal/cap-open gadgets carry past the face. They persist only because the
wide composition is conjunctive.

`compactE1 M ks` is the value-preserving deletion for a PER-MEMBER kill-set `ks`: drop exactly
the columns in `ks`, remapping every surviving column reference through the verified index map
`dropIdxG ks`. Unlike S2 (a uniform 992-column chain stratum with a chip-lane walk), E1 kills
PURE-DEAD columns — referenced by nothing that survives — so the expansion needs NO permutation
walk and NO chip-table extension: the deleted columns are recomputed as the aliased compact
value (they constrain nothing in the original, so any value satisfies it).

## The kill-set is DERIVED, not hand-listed

A column is killable iff no surviving constraint / hash site / range references it — the SAME
refs2-completeness `compactE1Ok` checks. `deadColsE1 M floor` computes exactly the unreferenced
columns at index `≥ floor`; `floor` sits strictly above every `.transition`-referenced face
column (`sbCol`/`saCol` ≤ 89 < 90), so `dropIdxG` is the identity on the offset-encoded
transitions — the S2-proven pattern. The emit driver refuses (`compactE1Checked`) unless the
whole decidable `compactE1Ok` bundle holds; a load-bearing column fails the emit, closed.

## The soundness bridge (`compactE1_expand`)

The keystone tower (and the S2 bridge `compactS2_expand`) is stated over the pre-E1 member `M`.
`compactE1_expand` re-connects it: a `Satisfied2` witness of `compactE1 M ks` EXPANDS to a
`Satisfied2` witness of `M` itself. The expanded trace remaps every row through `dropIdxG ks`
(surviving columns land on their compact index; killed columns alias whatever compact position
`dropIdxG` sends them to — irrelevant, since no surviving constraint reads a killed column). The
auxiliary tables are UNCHANGED (no walk, no chip extension), so `memClosed` / table faithfulness
transport verbatim. Every conclusion a keystone draws about surviving columns transfers.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no new hypotheses — the bridge is
unconditional given the decidable shape checks.
-/
import Dregg2.Circuit.Emit.RotWideCompactS2

namespace Dregg2.Circuit.Emit.RotWideCompactE1

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.RotWideCompactS2

set_option linter.unusedVariables false
set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — the per-member kill-set, its membership test, and the index map. -/

/-- Membership in the kill-set (the computable form the emit-time gates and the index map run on). -/
def isKilled (ks : List Nat) (c : Nat) : Bool := ks.contains c

/-- How many killed columns sit strictly below `c`. -/
def killedBelow (ks : List Nat) (c : Nat) : Nat := (ks.filter (· < c)).length

/-- The compaction index map: a column falls by the number of killed columns below it. Strictly
monotone on survivors; the identity below the first killed column. -/
def dropIdxG (ks : List Nat) (c : Nat) : Nat := c - killedBelow ks c

/-- `dropIdxG` is the identity on any column that sits at or below every killed column (in
particular the face columns the offset-encoded `.transition` reads). -/
theorem dropIdxG_id_of_low (ks : List Nat) (c : Nat) (h : ∀ k ∈ ks, c ≤ k) :
    dropIdxG ks c = c := by
  unfold dropIdxG killedBelow
  have : ks.filter (· < c) = [] := by
    rw [List.filter_eq_nil_iff]
    intro k hk
    have := h k hk
    simp only [decide_eq_true_eq]
    omega
  rw [this]
  simp

/-! ## §2 — the decidable side-condition bundle: what makes a kill-set VALID for a member. -/

/-- One surviving constraint is compatible with the deletion: it reads no killed column, and if
it is a `.transition` (offset-encoded through the fixed face bases) both its columns sit strictly
below every killed column, so the remap is the identity there. -/
def keptOkG (ks : List Nat) (c : VmConstraint2) : Bool :=
  (refs2 c).all (fun r => !isKilled ks r)
    && (match c with
        | .base (.transition hi lo) =>
            ks.all (fun k => decide (sbCol hi < k) && decide (saCol lo < k))
        | _ => true)

/-- **The whole decidable side-condition bundle** — the emit gate AND the bridge hypothesis:
  * every constraint reads no killed column and every `.transition` sits below the kill-set (so
    the deletion is value-preserving: no surviving constraint's meaning changes);
  * every hash site / range tooth avoids the killed columns;
  * the kill-set is duplicate-free and lies inside the trace width (exact width bookkeeping). -/
def compactE1Ok (M : EffectVmDescriptor2) (ks : List Nat) : Bool :=
  M.constraints.all (keptOkG ks)
    && M.hashSites.all (fun s => (refsSite s).all (fun r => !isKilled ks r))
    && M.ranges.all (fun r => !isKilled ks r.wire)
    && ks.Nodup
    && ks.all (fun c => decide (c < M.traceWidth))

/-! ## §3 — `compactE1`: the deletion itself. -/

/-- **`compactE1 M ks`** — the kill-set-deleted member: every column reference remapped through
`dropIdxG ks`, the width and main-table arity down by the killed counts, NO constraint dropped
(the E1 kill-set is pure-dead — referenced by nothing). Name, PI count, and every published value
are UNCHANGED. -/
def compactE1 (M : EffectVmDescriptor2) (ks : List Nat) : EffectVmDescriptor2 :=
  let g := dropIdxG ks
  { name := M.name
  , traceWidth := M.traceWidth - ks.length
  , piCount := M.piCount
  , tables := M.tables.map (fun td =>
      if td.id = TableId.main then { td with arity := td.arity - killedBelow ks td.arity } else td)
  , constraints := M.constraints.map (mapC2 g)
  , hashSites := M.hashSites.map (mapSite g)
  , ranges := M.ranges.map (mapRange g) }

/-- The compaction preserves the name (byte-identity of the member key). -/
theorem compactE1_name (M : EffectVmDescriptor2) (ks : List Nat) :
    (compactE1 M ks).name = M.name := rfl

/-- The compaction preserves the PUBLIC-INPUT COUNT — the structural half of "no published value
changed": the PI vector's length is fixed, and every `.piBinding` still binds the SAME PI index
(only the column it reads falls through `dropIdxG`, and the compact trace carries the same value
at that remapped column — value preservation). -/
theorem compactE1_piCount (M : EffectVmDescriptor2) (ks : List Nat) :
    (compactE1 M ks).piCount = M.piCount := rfl

/-- Every `.piBinding` keeps its PI index across the compaction (the published SLOTS are fixed;
only the reading column is remapped). -/
theorem compactE1_piBinding_index (g : Nat → Nat) (r : VmRow) (col k : Nat) :
    mapC2 g (.base (.piBinding r col k)) = .base (.piBinding r (g col) k) := rfl

/-! ## §4 — the expansion: remap every row back through the index map (NO walk). -/

/-- The expanded OLD-geometry row of a compact row: every column reads the compact row through
the index map `g` (survivors correctly; killed columns alias `dropIdxG`'s image — unread). -/
def expandRowG (ks : List Nat) (a : Assignment) : Assignment := fun c => a (dropIdxG ks c)

/-- The expanded trace: rows remapped, PIs and every auxiliary table UNTOUCHED (no chip
extension — the E1 kill-set constrains nothing that survives). -/
def expandTraceG (ks : List Nat) (t : VmTrace) : VmTrace :=
  { rows := t.rows.map (expandRowG ks), pub := t.pub, tf := t.tf }

/-- Row agreement, at the trace level: the expanded row reads the compact row through the map,
in range and out (the off-the-end default is `zeroAsg` on both sides). -/
theorem expandTraceG_getD (ks : List Nat) (t : VmTrace) (i c : Nat) :
    (expandTraceG ks t).rows.getD i zeroAsg c = t.rows.getD i zeroAsg (dropIdxG ks c) := by
  show (t.rows.map (expandRowG ks)).getD i zeroAsg c = _
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : t.rows[i]? with
  | none => rfl
  | some a => rfl

/-! ## §5 — the mem/map-log legs commute with the deletion (constraint kinds are preserved). -/

theorem memOpsOf_compactE1 (M : EffectVmDescriptor2) (ks : List Nat) :
    memOpsOf (compactE1 M ks) = (memOpsOf M).map (mapMemF (dropIdxG ks)) := by
  show (M.constraints.map (mapC2 (dropIdxG ks))).filterMap _ = _
  unfold memOpsOf
  induction M.constraints with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [mapC2, ih]

theorem mapOpsOf_compactE1 (M : EffectVmDescriptor2) (ks : List Nat) :
    mapOpsOf (compactE1 M ks) = (mapOpsOf M).map (mapMapF (dropIdxG ks)) := by
  show (M.constraints.map (mapC2 (dropIdxG ks))).filterMap _ = _
  unfold mapOpsOf
  induction M.constraints with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [mapC2, ih]

/-- The memory log of the ORIGINAL member over the expanded trace is the compact member's log
over the compact trace: every row remaps definitionally, and the mem ops' kinds are preserved. -/
theorem memLog_expandG (M : EffectVmDescriptor2) (ks : List Nat) (t : VmTrace) :
    memLog M (expandTraceG ks t) = memLog (compactE1 M ks) t := by
  unfold memLog
  rw [memOpsOf_compactE1]
  show (t.rows.map (expandRowG ks)).flatMap _ = _
  apply flatMap_map_rows
  intro a
  apply filterMap_opAt?_map
  intro m hm r hr
  rfl

theorem mapLog_expandG (M : EffectVmDescriptor2) (ks : List Nat) (t : VmTrace) :
    mapLog M (expandTraceG ks t) = mapLog (compactE1 M ks) t := by
  unfold mapLog
  rw [mapOpsOf_compactE1]
  show (t.rows.map (expandRowG ks)).flatMap _ = _
  apply flatMap_map_rows
  intro a
  apply filterMap_rowAt_map
  intro m hm r hr
  rfl

/-! ## §6 — the MASTER BRIDGE. -/

/-- **THE MASTER BRIDGE (`compactE1_expand`).** A `Satisfied2` witness of the E1-compacted member
expands to a `Satisfied2` witness of the ORIGINAL (pre-E1) member: every row is remapped back
through the index map, and every conclusion transports. The auxiliary tables are unchanged, so
the memory / map-ops legs ride verbatim. Every keystone stated over `M` therefore speaks about
the deployed E1-compact object, through this expansion (composed with the S2 bridge upstream). -/
theorem compactE1_expand (hash : List ℤ → ℤ)
    (M : EffectVmDescriptor2) (ks : List Nat)
    (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat) (maddrs : List ℤ) (t : VmTrace)
    (hok : compactE1Ok M ks = true)
    (hsat : Satisfied2 hash (compactE1 M ks) minit mfin maddrs t) :
    Satisfied2 hash M minit mfin maddrs (expandTraceG ks t) := by
  -- unpack the decidable side-condition bundle
  unfold compactE1Ok at hok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hkeptAll, hsitesOk⟩, hrangesOk⟩, _hnodup⟩, _hwidth⟩ := hok
  set g := dropIdxG ks with hg
  set tX := expandTraceG ks t with htX
  have hlen : tX.rows.length = t.rows.length := by simp [htX, expandTraceG]
  have hlocAg : ∀ i c, (envAt tX i).loc c = (envAt t i).loc (g c) := by
    intro i c; exact expandTraceG_getD ks t i c
  have hnxtAg : ∀ i c, (envAt tX i).nxt c = (envAt t i).nxt (g c) := by
    intro i c; exact expandTraceG_getD ks t (i + 1) c
  have hpubAg : ∀ i, (envAt tX i).pub = (envAt t i).pub := fun _ => rfl
  -- the mapped constraint sits in the compact member
  have hkeptMem : ∀ c ∈ M.constraints, mapC2 g c ∈ (compactE1 M ks).constraints := by
    intro c hc
    exact List.mem_map_of_mem hc
  -- the transition side condition, per constraint
  have htransOf : ∀ c ∈ M.constraints, ∀ hi lo, c = .base (.transition hi lo) →
      g (sbCol hi) = sbCol hi ∧ g (saCol lo) = saCol lo := by
    intro c hc hi lo hceq
    have hk := hkeptAll c hc
    unfold keptOkG at hk
    subst hceq
    simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hk
    obtain ⟨-, hbelow⟩ := hk
    refine ⟨dropIdxG_id_of_low ks _ ?_, dropIdxG_id_of_low ks _ ?_⟩
    · intro k hkm; have := hbelow k hkm; omega
    · intro k hkm; have := hbelow k hkm; omega
  have htbl : ∀ tid : TableId, ∀ row ∈ t.tf tid, row ∈ tX.tf tid := by
    intro tid row hrow; simpa [htX, expandTraceG] using hrow
  have hml : memLog M tX = memLog (compactE1 M ks) t := memLog_expandG M ks t
  have hmpl : mapLog M tX = mapLog (compactE1 M ks) t := mapLog_expandG M ks t
  have htfmem : tX.tf TableId.memory = t.tf TableId.memory := by simp [htX, expandTraceG]
  have htfmap : tX.tf TableId.mapOps = t.tf TableId.mapOps := by simp [htX, expandTraceG]
  refine ⟨?_, ?_, ?_, hsat.memAddrsNodup, ?_, ?_, ?_, ?_, ?_⟩
  · -- rowConstraints: pure transport through the index map
    intro i hi c hc
    rw [hlen] at hi
    rw [hlen]
    have hcompact := hsat.rowConstraints i hi (mapC2 g c) (hkeptMem c hc)
    exact holdsAt_transport hash g t.tf tX.tf (envAt t i) (envAt tX i)
      (i == 0) (i + 1 == t.rows.length) c
      (fun r _ => hlocAg i r) (fun r _ => hnxtAg i r) (hpubAg i)
      (htransOf c hc) htbl hcompact
  · -- rowHashes
    intro i hi
    rw [hlen] at hi
    exact siteHoldsAll_transport hash (envAt t i) (envAt tX i) g M.hashSites
      (fun s _ r _ => hlocAg i r) (hsat.rowHashes i hi)
  · -- rowRanges
    intro i hi r hr
    rw [hlen] at hi
    have hcompact := hsat.rowRanges i hi (mapRange g r) (List.mem_map_of_mem hr)
    unfold VmRange.holds at hcompact ⊢
    simp only [mapRange] at hcompact
    rw [hlocAg i r.wire]
    exact hcompact
  · rw [hml]; exact hsat.memClosed
  · rw [hml]; exact hsat.memDisciplined
  · rw [hml]; exact hsat.memBalanced
  · rw [htfmem, hml]; exact hsat.memTableFaithful
  · rw [htfmap, hmpl]; exact hsat.mapTableFaithful

#assert_axioms compactE1_expand

/-! ## §7 — the DERIVED kill-set and the CHECKED emit entry point. -/

/-- Every column any constraint / hash site / range of the member references (the live surface). -/
def liveCols (M : EffectVmDescriptor2) : List Nat :=
  M.constraints.flatMap refs2
    ++ M.hashSites.flatMap refsSite
    ++ M.ranges.map (fun r => r.wire)

/-- **The DERIVED kill-set**: every column in `[floor, traceWidth)` that the live surface never
references. `floor` sits strictly above every `.transition` face column (so the deletion leaves
the offset-encoded transitions the identity). No hand-listing — the same refs-completeness the
gate checks. -/
def deadColsE1 (M : EffectVmDescriptor2) (floor : Nat) : List Nat :=
  (List.range M.traceWidth).filter (fun c => decide (floor ≤ c) && !(liveCols M).contains c)

/-- The derived kill-set is duplicate-free (a filtered `List.range`). -/
theorem deadColsE1_nodup (M : EffectVmDescriptor2) (floor : Nat) :
    (deadColsE1 M floor).Nodup :=
  (List.nodup_range).filter _

/-- A killed column is genuinely unreferenced: it is in neither the constraints', hash sites',
nor ranges' reference surface. (The structural falsifier of "this column is dead".) -/
theorem deadColsE1_unref (M : EffectVmDescriptor2) (floor : Nat) (c : Nat)
    (h : c ∈ deadColsE1 M floor) : c ∉ liveCols M := by
  unfold deadColsE1 at h
  rw [List.mem_filter] at h
  have := h.2
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at this
  exact this.2

/-- A referenced column of any constraint is in the live surface. -/
theorem refs2_mem_liveCols (M : EffectVmDescriptor2) (c : VmConstraint2) (hc : c ∈ M.constraints)
    (r : Nat) (hr : r ∈ refs2 c) : r ∈ liveCols M := by
  unfold liveCols
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, hc, hr⟩))

/-- A referenced column of any hash site is in the live surface. -/
theorem refsSite_mem_liveCols (M : EffectVmDescriptor2) (s : VmHashSite) (hs : s ∈ M.hashSites)
    (r : Nat) (hr : r ∈ refsSite s) : r ∈ liveCols M := by
  unfold liveCols
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨s, hs, hr⟩))

/-- A range tooth's wire is in the live surface. -/
theorem range_wire_mem_liveCols (M : EffectVmDescriptor2) (rg : VmRange) (hrg : rg ∈ M.ranges) :
    rg.wire ∈ liveCols M := by
  unfold liveCols
  exact List.mem_append_right _ (List.mem_map_of_mem hrg)

/-- Every killed column sits at or above the floor. -/
theorem deadColsE1_ge_floor (M : EffectVmDescriptor2) (floor : Nat) (c : Nat)
    (h : c ∈ deadColsE1 M floor) : floor ≤ c := by
  unfold deadColsE1 at h
  rw [List.mem_filter] at h
  have := h.2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1

/-- Every killed column is inside the trace width. -/
theorem deadColsE1_lt_width (M : EffectVmDescriptor2) (floor : Nat) (c : Nat)
    (h : c ∈ deadColsE1 M floor) : c < M.traceWidth := by
  unfold deadColsE1 at h
  rw [List.mem_filter] at h
  exact List.mem_range.mp h.1

/-- **The derived kill-set ALWAYS passes the gate** — GENERICALLY, given only that the floor sits
strictly above every `.transition` face column (the one cheap per-member fact). No expensive
per-constraint kernel decide: killability is unreferencedness by construction (`deadColsE1_unref`),
and the transition clause reduces to `floor` beating the (14-limb) face offsets. -/
theorem compactE1Ok_deadColsE1 (M : EffectVmDescriptor2) (floor : Nat)
    (htrans : ∀ c ∈ M.constraints, ∀ hi lo, c = .base (.transition hi lo) →
        sbCol hi < floor ∧ saCol lo < floor) :
    compactE1Ok M (deadColsE1 M floor) = true := by
  set ks := deadColsE1 M floor with hks
  have hunref : ∀ x, x ∈ ks → x ∉ liveCols M := fun x hx => deadColsE1_unref M floor x hx
  have hnotKilled : ∀ x, x ∈ liveCols M → isKilled ks x = false := by
    intro x hx
    unfold isKilled
    simp only [List.contains_eq_mem, decide_eq_false_iff_not]
    intro hmem
    exact hunref x hmem hx
  unfold compactE1Ok
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, deadColsE1_nodup M floor⟩, ?_⟩
  · -- every constraint kept-ok
    intro c hc
    unfold keptOkG
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, ?_⟩
    · intro r hr
      rw [hnotKilled r (refs2_mem_liveCols M c hc r hr)]; rfl
    · -- the transition clause
      cases c with
      | base b =>
        cases b with
        | transition hi lo =>
          simp only [List.all_eq_true, Bool.and_eq_true]
          intro k hk
          simp only [decide_eq_true_eq]
          obtain ⟨h1, h2⟩ := htrans _ hc hi lo rfl
          have hge := deadColsE1_ge_floor M floor k hk
          exact ⟨by omega, by omega⟩
        | gate _ => rfl
        | boundary _ _ => rfl
        | piBinding _ _ _ => rfl
      | lookup _ => rfl
      | memOp _ => rfl
      | mapOp _ => rfl
      | umemOp _ => rfl
      | proofBind _ => rfl
      | windowGate _ => rfl
  · -- hash sites
    intro s hs r hr
    rw [hnotKilled r (refsSite_mem_liveCols M s hs r hr)]; rfl
  · -- ranges
    intro rg hrg
    rw [hnotKilled rg.wire (range_wire_mem_liveCols M rg hrg)]; rfl
  · -- width bookkeeping
    intro c hc
    exact deadColsE1_lt_width M floor c hc

/-- The cheap per-member fact the generic gate needs: every `.transition` sits strictly below the
floor. Scans only the transitions (no kill-set cross-product), so `decide` is fast. -/
def transitionCeilingOk (M : EffectVmDescriptor2) (floor : Nat) : Bool :=
  M.constraints.all (fun c => match c with
    | .base (.transition hi lo) => decide (sbCol hi < floor) && decide (saCol lo < floor)
    | _ => true)

theorem transitionCeilingOk_sound (M : EffectVmDescriptor2) (floor : Nat)
    (h : transitionCeilingOk M floor = true) :
    ∀ c ∈ M.constraints, ∀ hi lo, c = .base (.transition hi lo) →
      sbCol hi < floor ∧ saCol lo < floor := by
  intro c hc hi lo hceq
  subst hceq
  unfold transitionCeilingOk at h
  rw [List.all_eq_true] at h
  have := h _ hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- **The gate holds from the cheap ceiling check alone** — the wrapper the emit driver and the
crown corollary use: `transitionCeilingOk` is the only member-specific obligation. -/
theorem compactE1Ok_of_ceiling (M : EffectVmDescriptor2) (floor : Nat)
    (h : transitionCeilingOk M floor = true) :
    compactE1Ok M (deadColsE1 M floor) = true :=
  compactE1Ok_deadColsE1 M floor (transitionCeilingOk_sound M floor h)

#assert_axioms compactE1Ok_deadColsE1
#assert_axioms compactE1Ok_of_ceiling

/-- **The emit-side compaction** — compact a member at its DERIVED kill-set, FAILING CLOSED
(`none`) unless the whole decidable `compactE1Ok` bundle holds. The `floor` is supplied by the
driver (the fixed face ceiling `AUX_BASE = 90` for the wide members). -/
def compactE1Checked (M : EffectVmDescriptor2) (floor : Nat) : Option EffectVmDescriptor2 :=
  let ks := deadColsE1 M floor
  if compactE1Ok M ks then some (compactE1 M ks) else none

/-- A checked compaction only ever returns `compactE1` under a TRUE `compactE1Ok` — the bridge's
hypothesis is discharged by construction for every emitted member. -/
theorem compactE1Checked_ok (M : EffectVmDescriptor2) (floor : Nat) (cm : EffectVmDescriptor2)
    (h : compactE1Checked M floor = some cm) :
    compactE1Ok M (deadColsE1 M floor) = true ∧ cm = compactE1 M (deadColsE1 M floor) := by
  unfold compactE1Checked at h
  by_cases hok : compactE1Ok M (deadColsE1 M floor)
  · rw [if_pos hok] at h
    exact ⟨hok, (Option.some_inj.mp h).symm⟩
  · rw [if_neg hok] at h; cases h

#assert_axioms compactE1Checked_ok
#assert_axioms deadColsE1_unref

end Dregg2.Circuit.Emit.RotWideCompactE1
