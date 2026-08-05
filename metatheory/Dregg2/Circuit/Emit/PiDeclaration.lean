/-
# Dregg2.Circuit.Emit.PiDeclaration — a published PI slot must SAY WHAT IT IS.

## The wound

A public input exists in **four places with no shared source**: the index constant
(`circuit/src/effect_vm/pi.rs`), the `pi_binding` in the emitter (here), the carrier column
(`circuit/src/effect_vm/trace_rotated.rs`) and the producer's fill. You can declare a slot, never
bind it, never fill it — and everything compiles, emits, proves and verifies.

MEASURED at HEAD over the emitted registries (`scripts/pi_disposition_census.py`, which parses the
committed TSV and counts `pi_binding` constraints — the ONLY constraint kind that reads a public
input, `descriptor_ir2.rs`'s sole `pv[*pi_index]` site):

| registry | members | Σ piCount | Σ with a pin | **unpinned** |
|---|---|---|---|---|
| `rotation-wide-registry-staged.tsv` (deployed) | 57 | 3,821 | 1,642 | **2,179 (57.0%)** |
| `rotation-v3-staged-registry.tsv` | 60 | 3,012 | 844 | **2,168 (72.0%)** |

Per slot across the 57 wide members: `TURN_HASH` 0/56, `EFFECTS_HASH_GLOBAL` 0/56, `NET_DELTA_*`
0/56, `CURRENT_BLOCK_HEIGHT` 0/56, `CUSTOM_EFFECT_COUNT` 0/56 — and the producer writes
`PI[TURN_HASH] = [0,0,0,0]` on every deployed rotated leg (`trace_rotated.rs`'s v1 sub-trace is
built `..Default::default()`, and `EffectVmContext::default` zeroes `turn_hash`).

⚑ **The wound is not that 2,179 are unpinned. It is that NOBODY CHOSE.** An unpinned slot is
either (a) a value a verifier must check — so it needs a binding — or (b) not a public input at
all. Nothing in the tree forces that choice, or even records which was intended.

## What this module is

The `ChipArityAdmitted` shape (`DescriptorIR2`), applied to public inputs: a descriptor routed
through [`withPiManifest`] **fails to elaborate** unless every published slot carries a
disposition, and every disposition is TRUE OF THE DESCRIPTOR.

  * **`.bound row col`** — the AIR reads this slot. Admitted only when the descriptor really
    carries `.piBinding row col k` AND `col ∈ UnforcedPiPins.forcedCols` — i.e. only when the
    pinned column is forced by something that is not the pin. A pin on a column nothing else
    reads is the wound `UnforcedPiPins` censuses (the prover picks both sides), so **`.bound`
    cannot name one**: `bound_decl_pin_survives_subtraction`.
  * **`.transcriptOnly reason`** — the slot enters Fiat–Shamir and NOTHING ELSE. Permitted, with
    a written reason at the declaration site, and admitted only when the descriptor carries **no
    pin at all** on that slot (a slot that IS pinned must be declared `.bound`, or the manifest
    is lying about the object). What the class costs is a theorem, not a hope:
    `transcriptOnly_admits_any_value` — the AIR admits *every* value there.

Totality is the tooth that makes an unbound PI unrepresentable: `piSlotsCovered` requires
**exactly one** declaration per index in `0..piCount`. A slot you forget is not silently
transcript-only; the descriptor does not elaborate.

And the fourth source dies with [`producerObligations`]: the (index, row, column) triples a
producer must fill from are DERIVED from the manifest, so a declared-and-unfilled slot is not a
thing a producer can have.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; no crypto hypothesis anywhere — every
statement here is about the constraint system's SHAPE, not about a hash.

The armed half — the refusals, which are the part that can go RED — is
`Dregg2.Circuit.PiDispositionBite`.
-/
import Dregg2.Circuit.Emit.UnforcedPiPins

namespace Dregg2.Circuit.Emit.PiDeclaration

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.UnforcedPiPins
  (isPin pinsOf forcedCols pinUnforced dropUnforcedPins evalW_congr evalChal_congr)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the declaration. -/

/-- What a published public input IS. There are exactly two honest answers, and a slot with no
answer does not elaborate. -/
inductive PiDisposition where
  /-- **The AIR reads it.** `local[col] = pi[index]` on `row`, and `col` is forced by a non-pin
  constraint / hash site / range tooth. A verifier that recomputes the slot independently and
  finds a different value is refused by the constraint system alone. -/
  | bound (row : VmRow) (col : Nat)
  /-- **The AIR does not read it, on purpose.** The slot enters the Fiat–Shamir transcript (so it
  is bound to the PROOF, not to the TRACE) and nothing else. `reason` is mandatory and must say
  why a binding is not wanted — it is the record of the choice this whole module exists to force. -/
  | transcriptOnly (reason : String)
  deriving Repr, DecidableEq

/-- One slot's declaration: which index, what it is called on the wire, and what it IS. -/
structure PiDecl where
  index : Nat
  slot  : String
  disp  : PiDisposition
  deriving Repr, DecidableEq

/-- A descriptor's full PI declaration — one entry per published slot. -/
abbrev PiManifest := List PiDecl

/-! ## §2 — admissibility: is the declaration TRUE of the descriptor? -/

/-- Does the descriptor carry exactly the pin a `.bound` declaration claims? -/
def hasPin (M : EffectVmDescriptor2) (row : VmRow) (col k : Nat) : Bool :=
  (pinsOf M).any (fun p => p.1 == row && p.2.1 == col && p.2.2 == k)

/-- Every PI slot SOME pin of the descriptor names. -/
def pinnedSlots (M : EffectVmDescriptor2) : List Nat := (pinsOf M).map (fun p => p.2.2)

/-- **One declaration's admissibility.**

* `.bound row col` — the pin must EXIST and the column must be FORCED. The second half is not
  decoration: a pin on an unforced column is satisfied by construction (the prover chooses the
  column value and publishes it), and `UnforcedPiPins.dropUnforcedPins` deletes exactly those.
  Admitting one here would let a manifest promise a binding the very next compaction pass removes.
* `.transcriptOnly reason` — the reason must be non-empty, and the slot must carry NO pin. A
  pinned slot declared transcript-only is a manifest describing a different object. -/
def declAdmitted (M : EffectVmDescriptor2) (d : PiDecl) : Bool :=
  d.index < M.piCount &&
  (match d.disp with
    | .bound row col        => hasPin M row col d.index && (forcedCols M).contains col
    | .transcriptOnly reason => !reason.isEmpty && !(pinnedSlots M).contains d.index)

/-- **Totality** — every published index carries EXACTLY ONE declaration. This is the clause that
makes an undeclared PI unrepresentable rather than tacitly transcript-only. -/
def piSlotsCovered (ds : PiManifest) (n : Nat) : Bool :=
  (List.range n).all (fun k => (ds.filter (fun d => d.index == k)).length == 1)

/-- The whole manifest is admitted: total over `0..piCount`, and every entry true of `M`. -/
def manifestAdmitted (M : EffectVmDescriptor2) (ds : PiManifest) : Bool :=
  piSlotsCovered ds M.piCount && ds.all (declAdmitted M)

/-- The `Prop` face, `abbrev` so `decide` sees through it and the failure message shows the
offending manifest against the descriptor. -/
abbrev PiManifestAdmitted (M : EffectVmDescriptor2) (ds : PiManifest) : Prop :=
  manifestAdmitted M ds = true

/-- **The side-condition discharger** (the `chip_arity_admitted` shape). Two ways an emitter can
be shown to have declared its public inputs, and no third. -/
macro "pi_manifest_admitted" : tactic =>
  `(tactic| first
      | assumption
      | exact of_decide_eq_true (Eq.refl true)
      | fail "PI DISPOSITION MISSING OR FALSE — every published public input must carry EXACTLY \
              ONE declaration, and the declaration must be TRUE of this descriptor. Either (a) a \
              slot in 0..piCount has no declaration (or two), or (b) a `.bound row col` names a \
              pin the descriptor does not carry, or names a column no NON-PIN constraint reads \
              (an unforced pin — the prover chooses both sides, and `UnforcedPiPins` deletes it), \
              or (c) a `.transcriptOnly` carries an empty reason, or was declared for a slot the \
              descriptor DOES pin. An unbound public input is either a value a verifier must \
              check — so bind it — or not a public input at all — so delete it. It is not a \
              thing you may leave unsaid."
      )

/-- **The gate.** An emitter routes its descriptor through this; the object is UNCHANGED
(`withPiManifest_eq`), so no emitted byte moves — what changes is that the emit does not
ELABORATE unless every published slot has been dispositioned. -/
def withPiManifest (M : EffectVmDescriptor2) (ds : PiManifest)
    (h : PiManifestAdmitted M ds := by pi_manifest_admitted) : EffectVmDescriptor2 := M

/-- The gate is the identity on the emitted object: adopting it changes no descriptor byte. -/
@[simp] theorem withPiManifest_eq (M : EffectVmDescriptor2) (ds : PiManifest)
    (h : PiManifestAdmitted M ds) : withPiManifest M ds h = M := rfl

/-- **The producer obligation.** The `(piIndex, row, column)` triples a producer must fill the PI
vector FROM — derived from the manifest, never re-typed. This is the fourth source of the
four-source problem: a producer that reads this cannot publish a slot it did not fill from the
column the AIR pins. -/
def producerObligations (ds : PiManifest) : List (Nat × VmRow × Nat) :=
  ds.filterMap fun d => match d.disp with
    | .bound row col        => some (d.index, row, col)
    | .transcriptOnly _     => none

/-- The transcript-only class, with its reasons — what a census must report SEPARATELY. -/
def transcriptOnlySlots (ds : PiManifest) : List (Nat × String × String) :=
  ds.filterMap fun d => match d.disp with
    | .transcriptOnly reason => some (d.index, d.slot, reason)
    | .bound _ _             => none

/-! ## §3 — the bridge to the descriptor: a `.bound` declaration IS the AIR's equation. -/

/-- A member of `pinsOf` is a genuine pin constraint of the descriptor. -/
theorem mem_constraints_of_mem_pinsOf {M : EffectVmDescriptor2} {row : VmRow} {col k : Nat}
    (h : (row, col, k) ∈ pinsOf M) :
    VmConstraint2.base (.piBinding row col k) ∈ M.constraints := by
  obtain ⟨c, hc, hval⟩ := List.mem_filterMap.mp h
  cases c with
  | base b =>
    cases b with
    | piBinding row' col' k' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hval
      obtain ⟨h1, h2, h3⟩ := hval
      subst h1; subst h2; subst h3; exact hc
    | gate _ => simp at hval
    | transition _ _ => simp at hval
    | boundary _ _ => simp at hval
  | lookup _ => simp at hval
  | memOp _ => simp at hval
  | mapOp _ => simp at hval
  | umemOp _ => simp at hval
  | proofBind _ => simp at hval
  | windowGate _ => simp at hval
  | chalGate _ => simp at hval

/-- Conversely: every pin constraint shows up in the census list. -/
theorem mem_pinsOf_of_mem_constraints {M : EffectVmDescriptor2} {row : VmRow} {col k : Nat}
    (h : VmConstraint2.base (.piBinding row col k) ∈ M.constraints) :
    (row, col, k) ∈ pinsOf M :=
  List.mem_filterMap.mpr ⟨_, h, rfl⟩

/-- `hasPin` is decided membership. -/
theorem mem_constraints_of_hasPin {M : EffectVmDescriptor2} {row : VmRow} {col k : Nat}
    (h : hasPin M row col k = true) :
    VmConstraint2.base (.piBinding row col k) ∈ M.constraints := by
  obtain ⟨p, hp, hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  obtain ⟨⟨h1, h2⟩, h3⟩ := hq
  have : p = (row, col, k) := by
    cases p with
    | mk a bc => cases bc with
      | mk b c => simp_all
  exact mem_constraints_of_mem_pinsOf (this ▸ hp)

/-- An admitted manifest's declarations are each admitted. -/
theorem declAdmitted_of_mem {M : EffectVmDescriptor2} {ds : PiManifest} {d : PiDecl}
    (hadm : PiManifestAdmitted M ds) (hd : d ∈ ds) : declAdmitted M d = true := by
  have := (Bool.and_eq_true _ _).mp hadm
  exact List.all_eq_true.mp this.2 d hd

/-- **A `.bound` declaration's pin exists.** -/
theorem bound_decl_pin_mem {M : EffectVmDescriptor2} {ds : PiManifest}
    {k : Nat} {slot : String} {row : VmRow} {col : Nat}
    (hadm : PiManifestAdmitted M ds) (hd : ⟨k, slot, .bound row col⟩ ∈ ds) :
    VmConstraint2.base (.piBinding row col k) ∈ M.constraints := by
  have h := declAdmitted_of_mem hadm hd
  simp only [declAdmitted, Bool.and_eq_true] at h
  exact mem_constraints_of_hasPin h.2.1

/-- **A `.bound` declaration's column is FORCED** — something other than the pin reads it. -/
theorem bound_decl_col_forced {M : EffectVmDescriptor2} {ds : PiManifest}
    {k : Nat} {slot : String} {row : VmRow} {col : Nat}
    (hadm : PiManifestAdmitted M ds) (hd : ⟨k, slot, .bound row col⟩ ∈ ds) :
    col ∈ forcedCols M := by
  have h := declAdmitted_of_mem hadm hd
  simp only [declAdmitted, Bool.and_eq_true] at h
  exact List.mem_of_elem_eq_true (by simpa using h.2.2)

/-- ⚑ **THE COMPOSITION WITH THE EXISTING CENSUS.** A `.bound` declaration can never name a pin
that `UnforcedPiPins.dropUnforcedPins` would delete: the pin survives the subtraction ON ITS OWN
MERITS. So the two mechanisms cannot disagree — a manifest cannot promise a binding that the
compaction pass then removes, which is precisely how the `withDfaRcPins` quartet became a
`CarrierWitness::Dsl` fold that refused every deployed leg. -/
theorem bound_decl_pin_survives_subtraction {M : EffectVmDescriptor2} {ds : PiManifest}
    {k : Nat} {slot : String} {row : VmRow} {col : Nat}
    (hadm : PiManifestAdmitted M ds) (hd : ⟨k, slot, .bound row col⟩ ∈ ds) :
    VmConstraint2.base (.piBinding row col k) ∈ (dropUnforcedPins M).constraints := by
  refine List.mem_filter.mpr ⟨bound_decl_pin_mem hadm hd, ?_⟩
  have hforced : col ∈ forcedCols M := bound_decl_col_forced hadm hd
  simp only [pinUnforced, Bool.not_not, List.contains_eq_mem, decide_eq_true_eq]
  exact hforced

/-- **A `.bound` declaration IS the AIR's equation on the row it names.** Any satisfying witness
of the descriptor publishes, at slot `k`, exactly the trace column the declaration names. This is
the promise the manifest makes, discharged against `Satisfied2`. -/
theorem bound_decl_forces_pi (hash : List ℤ → ℤ) {M : EffectVmDescriptor2} {ds : PiManifest}
    {k : Nat} {slot : String} {col : Nat}
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (hadm : PiManifestAdmitted M ds)
    (h : Satisfied2 hash M minit mfin maddrs t) :
    (⟨k, slot, .bound .first col⟩ ∈ ds → 0 < t.rows.length →
      (envAt t 0).loc col ≡ (envAt t 0).pub k [ZMOD 2013265921])
    ∧ (∀ i, ⟨k, slot, .bound .last col⟩ ∈ ds → i < t.rows.length → i + 1 = t.rows.length →
      (envAt t i).loc col ≡ (envAt t i).pub k [ZMOD 2013265921]) := by
  constructor
  · intro hd hlen
    have hmem := bound_decl_pin_mem hadm hd
    have := h.rowConstraints 0 hlen _ hmem
    exact this (by simp)
  · intro i hd hi hlast
    have hmem := bound_decl_pin_mem hadm hd
    have := h.rowConstraints i hi _ hmem
    exact this (by simp [hlast])

/-! ## §4 — THE EVIDENCE: an UNPINNED slot admits any published value.

This is what the 2,179 MEAN. The dual of a forgery tooth: a binding REFUSES an inconsistent
publication; a slot with no pin accepts every publication, so the number a verifier reads there is
the producer's word and nothing else. `UnforcedPiPins.unforced_pin_admits_any_value` is the
sibling one step in (a pin whose COLUMN is free); this is the case where there is no pin at all,
which is 57% of the deployed surface. -/

/-- Overwrite one published slot. -/
def setPubAt (a : Assignment) (k : Nat) (v : ℤ) : Assignment :=
  fun j => if j = k then v else a j

/-- A hash-site input resolves off the LOCAL row alone. -/
theorem resolve_loc_congr (e f : VmRowEnv) (hloc : e.loc = f.loc) (digs : List ℤ)
    (i : HashInput) : HashInput.resolve e digs i = HashInput.resolve f digs i := by
  cases i <;> simp [HashInput.resolve, hloc]

/-- ⚑ The hash layer never reads a public input either: `siteHoldsAll` is invariant under any
change to `pub` (it is a function of `env.loc` alone). -/
theorem siteHoldsAll_loc_congr (hash : List ℤ → ℤ) (e f : VmRowEnv) (hloc : e.loc = f.loc)
    (sites : List VmHashSite) (acc : List ℤ)
    (h : siteHoldsAll.go hash e acc sites) : siteHoldsAll.go hash f acc sites := by
  induction sites generalizing acc with
  | nil => exact h
  | cons s ss ih =>
    have hres : s.resolvedInputs e acc = s.resolvedInputs f acc := by
      simp only [VmHashSite.resolvedInputs]
      exact List.map_congr_left (fun i _ => resolve_loc_congr e f hloc acc i)
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [← hloc, ← hres]; exact h1
    · rw [← hres]; exact ih _ h2

/-- Overwriting a published slot touches ONLY the `pub` slice of every row window: the trace rows,
the next-row slice and the challenge draws are carried verbatim. -/
theorem envAt_setPubAt (t : VmTrace) (k : Nat) (v : ℤ) (i : Nat) :
    envAt { t with pub := setPubAt t.pub k v } i
      = { loc := (envAt t i).loc, nxt := (envAt t i).nxt
        , pub := setPubAt (envAt t i).pub k v, chal := (envAt t i).chal } := rfl

/-- ⚑ The whole reason this is provable: in the v2 denotation `env.pub` is projected at EXACTLY
TWO places — the two `.piBinding` arms of `VmConstraint.holdsVm`. Lookups, map/mem/umem ops,
`proofBind`, window gates, challenge gates, hash sites and range teeth all read `loc`/`nxt`/`chal`
only. (The Rust twin: `descriptor_ir2.rs`'s sole `pv[*pi_index]` site, in the `PiBinding` arm.) -/
theorem holdsAt_setPubAt (hash : List ℤ → ℤ) (tf : TraceFamily) (M : EffectVmDescriptor2)
    (k : Nat) (v : ℤ) (hk : k ∉ pinnedSlots M)
    (env : VmRowEnv) (isFirst isLast : Bool) (c : VmConstraint2) (hc : c ∈ M.constraints)
    (h : c.holdsAt hash tf env isFirst isLast) :
    c.holdsAt hash tf { env with pub := setPubAt env.pub k v } isFirst isLast := by
  cases c with
  | base b =>
    cases b with
    | piBinding row col k' =>
      have hne : k' ≠ k := by
        intro hh
        exact hk (hh ▸ List.mem_map.mpr ⟨(row, col, k'), mem_pinsOf_of_mem_constraints hc, rfl⟩)
      have hpub : setPubAt env.pub k v k' = env.pub k' := by simp [setPubAt, hne]
      cases row with
      | first => intro hf; show env.loc col ≡ setPubAt env.pub k v k' [ZMOD 2013265921]
                 rw [hpub]; exact h hf
      | last  => intro hl; show env.loc col ≡ setPubAt env.pub k v k' [ZMOD 2013265921]
                 rw [hpub]; exact h hl
    | gate _ => exact h
    | transition _ _ => exact h
    | boundary row _ => cases row <;> exact h
  | lookup _ => exact h
  | memOp _ => exact h
  | mapOp _ => exact h
  | umemOp _ => exact h
  | proofBind _ => exact h
  | windowGate w =>
    have heq : w.body.eval ({ env with pub := setPubAt env.pub k v } : VmRowEnv)
        = w.body.eval env := evalW_congr w.body _ env (fun _ _ => rfl) (fun _ _ => rfl)
    show WindowConstraint.holdsAt _ isLast w
    simp only [WindowConstraint.holdsAt, heq]
    exact h
  | chalGate w =>
    have heq : w.body.eval ({ env with pub := setPubAt env.pub k v } : VmRowEnv)
        = w.body.eval env := evalChal_congr w.body _ env (fun _ _ => rfl) (fun _ _ => rfl) rfl
    show ChalConstraint.holdsAt _ isLast w
    simp only [ChalConstraint.holdsAt, heq]
    exact h

/-- **`unpinned_pi_admits_any_value`** — a slot no pin names is PROVER-CHOSEN. Take any satisfying
witness, overwrite the published slot with an ARBITRARY `v`, and the result satisfies the SAME
descriptor. The slot refuses nothing; a light client reading it is reading the producer's word.

⚠ Read together with the census this says: **2,179 of the 3,821 published felts on the deployed
wide registry are this**. That is not, by itself, a defect — some slots genuinely only need to
enter Fiat–Shamir. It is a defect that nothing recorded which. -/
theorem unpinned_pi_admits_any_value (hash : List ℤ → ℤ) (M : EffectVmDescriptor2)
    (k : Nat) (v : ℤ) (hk : k ∉ pinnedSlots M)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash M minit mfin maddrs t) :
    Satisfied2 hash M minit mfin maddrs { t with pub := setPubAt t.pub k v } := by
  refine
    { rowConstraints := ?_, rowHashes := ?_, rowRanges := ?_
    , memAddrsNodup := h.memAddrsNodup, memClosed := h.memClosed
    , memDisciplined := h.memDisciplined, memBalanced := h.memBalanced
    , memTableFaithful := h.memTableFaithful, mapTableFaithful := h.mapTableFaithful }
  · intro i hi c hc
    rw [envAt_setPubAt]
    exact holdsAt_setPubAt hash t.tf M k v hk (envAt t i) (i == 0) (i + 1 == t.rows.length) c hc
      (h.rowConstraints i hi c hc)
  · intro i hi
    rw [envAt_setPubAt]
    exact siteHoldsAll_loc_congr hash (envAt t i)
      { loc := (envAt t i).loc, nxt := (envAt t i).nxt
      , pub := setPubAt (envAt t i).pub k v, chal := (envAt t i).chal }
      rfl M.hashSites [] (h.rowHashes i hi)
  · intro i hi r hr; rw [envAt_setPubAt]; exact h.rowRanges i hi r hr

/-- **`transcriptOnly_admits_any_value`** — declaring a slot transcript-only is declaring THIS,
and the declaration is checked: `declAdmitted` refuses `.transcriptOnly` on a slot the descriptor
pins, so the class cannot quietly absorb a real binding, and every member of the class carries
this consequence. -/
theorem transcriptOnly_admits_any_value (hash : List ℤ → ℤ) {M : EffectVmDescriptor2}
    {ds : PiManifest} {k : Nat} {slot reason : String} (v : ℤ)
    (hadm : PiManifestAdmitted M ds) (hd : ⟨k, slot, .transcriptOnly reason⟩ ∈ ds)
    {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
    (h : Satisfied2 hash M minit mfin maddrs t) :
    Satisfied2 hash M minit mfin maddrs { t with pub := setPubAt t.pub k v } := by
  have hda := declAdmitted_of_mem hadm hd
  simp only [declAdmitted, Bool.and_eq_true] at hda
  have hnp := hda.2.2
  have hk : k ∉ pinnedSlots M := by
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hnp
    exact hnp
  exact unpinned_pi_admits_any_value hash M k v hk h

/-! ## §5 — totality: no slot escapes the choice. -/

/-- Every published index carries a declaration. This is the clause that makes an unbound PI
UNREPRESENTABLE: forgetting a slot is not "tacitly transcript-only", it is a descriptor that does
not elaborate. -/
theorem decl_of_lt_piCount {M : EffectVmDescriptor2} {ds : PiManifest}
    (hadm : PiManifestAdmitted M ds) {k : Nat} (hk : k < M.piCount) :
    ∃ d ∈ ds, d.index = k := by
  have hcov := (Bool.and_eq_true _ _).mp hadm |>.1
  have := List.all_eq_true.mp hcov k (List.mem_range.mpr hk)
  simp only [beq_iff_eq] at this
  have hlen : (ds.filter (fun d => d.index == k)).length = 1 := by simpa using this
  have hne : ds.filter (fun d => d.index == k) ≠ [] := by
    intro hnil; rw [hnil] at hlen; simp at hlen
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
  exact ⟨d, List.mem_of_mem_filter hd, by
    have := (List.mem_filter.mp hd).2
    simpa using this⟩

/-- The two classes PARTITION the published surface: every slot is bound or transcript-only, and
the census can therefore report them separately without a residual. -/
theorem bound_or_transcriptOnly {M : EffectVmDescriptor2} {ds : PiManifest}
    (hadm : PiManifestAdmitted M ds) {k : Nat} (hk : k < M.piCount) :
    (∃ d ∈ ds, d.index = k ∧ ∃ row col, d.disp = .bound row col)
    ∨ (∃ d ∈ ds, d.index = k ∧ ∃ reason, d.disp = .transcriptOnly reason) := by
  obtain ⟨d, hd, hidx⟩ := decl_of_lt_piCount hadm hk
  cases hdisp : d.disp with
  | bound row col => exact .inl ⟨d, hd, hidx, row, col, hdisp⟩
  | transcriptOnly reason => exact .inr ⟨d, hd, hidx, reason, hdisp⟩

#assert_axioms mem_constraints_of_mem_pinsOf
#assert_axioms mem_constraints_of_hasPin
#assert_axioms bound_decl_pin_mem
#assert_axioms bound_decl_col_forced
#assert_axioms bound_decl_pin_survives_subtraction
#assert_axioms bound_decl_forces_pi
#assert_axioms holdsAt_setPubAt
#assert_axioms unpinned_pi_admits_any_value
#assert_axioms transcriptOnly_admits_any_value
#assert_axioms decl_of_lt_piCount
#assert_axioms bound_or_transcriptOnly

end Dregg2.Circuit.Emit.PiDeclaration
