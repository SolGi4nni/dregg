/-
# Dregg2.Crypto.BindingSurvivesSimulation — COMMITMENT-LAYER SIMULATION-EXTRACTABILITY:
# binding survives the simulator.

## The insight (a re-quantification, not a new extractor)

The deployed binding extractors are TRANSCRIPT-FREE:

  * `GuardedHidingSpanWideBlindRefine.guardedHidingSpanWideBlind_two_openings_collide`
    (`Dregg2/Circuit/Emit/GuardedHidingSpanWideBlindRefine.lean`) takes two ACCEPTING OPENINGS
    (two `Satisfied2` witnesses over sound wide chip tables) of one published `hole_commit`
    and returns a `Coll8` collision AS DATA;
  * `BlindedMembershipWideEmit.interior_forge_narrow_admits_wide_refuses`
    (`Dregg2/Circuit/Emit/BlindedMembershipWideEmit.lean:665`) does the same at the fold layer.

(The commit descriptor here is the WIDE-BLIND `guardedHidingSpanWideBlindDesc` — the sole
emitted hidden-span descriptor since the felt-width cutover of 2026-07-23; the opened blinding
is the full 5-lane vector, so binding-as-extraction is STRONGER than the deleted narrow M0
form: distinctness in ANY blinding lane forces the collision.)

Their hypotheses are the two OPENINGS — never a proof transcript, never a verifier view. So the
extraction goes through UNCHANGED against an adversary who has seen arbitrarily many SIMULATED
proofs (the `Metatheory.Open.PerfectZK` simulator outputs): a maul that reuses a published commit
with a new opening still hands back a genuine wide Poseidon2-chip collision. That is
commitment-layer simulation-extractability, and this file STATES it as such:
`binding_survives_simulation` quantifies over an arbitrary `PerfectZK` simulator, an arbitrary
set of its simulated views, and an adversary that chooses a FAMILY of published commits and two
accepting openings AS A FUNCTION of those views — and concludes a `Coll8` collision whose term is
built by `collOfHidden` from the two openings' opened data ALONE. The simulator views feed
nothing: `collOfHidden`'s TYPE cannot mention them, and
`collision_independent_of_simulation` exhibits two different simulators/views extracting the
IDENTICAL collision term.

## HONEST SCOPE — what this is and is NOT

  * This is the COMMITMENT-layer property: binding-as-extraction is unconditional on (and
    structurally independent of) simulated views, because the extractor consumes openings, not
    transcripts. The openings carry their own `ChipTableSoundN` floors (the wide-chip
    faithfulness parameter, exactly as in the parent extractor) — those are floors about the
    CHIP TABLE, not about any simulator.
  * It is NOT STARK-layer (proof-level) simulation-extractability. That property — extract a
    witness from any accepting PROOF produced after seeing simulated PROOFS — needs a FRI
    knowledge extractor plus an HVZK simulator for the deployed STARK, is the Tier-3 frontier,
    and is NOT claimed anywhere here. It also inherits the undischarged FRI/STARK soundness
    floor ([[project-fri-soundness-reality]]); nothing in this file touches that.
  * `PerfectZK` here supplies the repo's honest simulator OBJECT (`sim : S → V`, perfect-ZK law
    `view s w = sim s`); we quantify over ANY such instance and ANY set of its outputs. The
    theorem is deliberately INSENSITIVE to which one — that insensitivity is the content.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound} on every load-bearing theorem.
Imports read-only. No `sorry`, no fresh `axiom`, no `native_decide`.
-/
import Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine
import Metatheory.Open.PerfectZK

namespace Dregg2.Crypto.BindingSurvivesSimulation

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.DeployedCapTree (Digest8 Coll8)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)
open Dregg2.Circuit.Emit.EffectVmEmit (holdsVm_piFirst_true)
open Dregg2.Circuit.Emit.BlindedMembershipWideEmit (wCols wVal wStageIns wPermOut)
open Dregg2.Circuit.Emit.GuardedHidingSpanEmit (wideFoldPair piCT piHOLE piGUARD)
open Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindEmit
open Dregg2.Circuit.Emit.GuardedHidingSpanRefine (hash0 wZeroAbsorb)
open Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine
open Metatheory.Open.PerfectZK

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

/-! ## §1 — an ACCEPTING OPENING, as one object.

The parent extractor's hypotheses for ONE side, bundled: a trace that `Satisfied2`s the emitted
`guardedHidingSpanWideBlindDesc` over a SOUND wide chip table. Note what is NOT here: no proof
transcript, no verifier view, no simulator anything. An opening is a witness, full stop. -/

/-- One accepting opening of the wide-blind hidden-hole-commitment descriptor: a `Satisfied2`
witness over a sound WIDE chip table (`ChipTableSoundN` — the same wide-chip faithfulness floor
the parent binding theorem carries). -/
structure AcceptingOpening (absorb : List ℤ → Digest8) where
  /-- The abstract v1 hash the denotation threads (unused by this descriptor). -/
  hash : List ℤ → ℤ
  /-- The declared initial memory image (this descriptor has no memory ops). -/
  minit : ℤ → ℤ
  /-- The declared final memory image. -/
  mfin : ℤ → ℤ × Nat
  /-- The declared memory address boundary. -/
  maddrs : List ℤ
  /-- The witness trace. -/
  trace : VmTrace
  /-- The wide chip table is SOUND for `absorb` (the wide-chip faithfulness floor). -/
  chipSound : ChipTableSoundN (wPermOut absorb) (trace.tf .poseidon2)
  /-- The trace satisfies the emitted descriptor. -/
  sat : Satisfied2 hash guardedHidingSpanWideBlindDesc minit mfin maddrs trace
  /-- The trace is nonempty (row 0 exists). -/
  rowsNonempty : trace.rows ≠ []

namespace AcceptingOpening

variable {absorb : List ℤ → Digest8}

/-- The row-0 assignment of the opening's trace. -/
def row0 (o : AcceptingOpening absorb) : Assignment := (envAt o.trace 0).loc

/-- The published 8-felt `hole_commit` this opening opens. -/
def commit (o : AcceptingOpening absorb) : Digest8 := wVal o.row0 gHOLE

/-- The opened hidden span digest (8 felts). -/
def spanDigest (o : AcceptingOpening absorb) : Digest8 := wVal o.row0 gDIGEST

/-- The opened context commitment `C_T` (8 felts). -/
def ctx (o : AcceptingOpening absorb) : Digest8 := wVal o.row0 gCT

/-- The opened blinding VECTOR (all 5 lanes). -/
def blinding (o : AcceptingOpening absorb) : Blind5 := bVal o.row0

/-- The full opened hidden data `(span_digest8, C_T, blinding-vector)` — what "two DISTINCT
openings" quantifies over, exactly as in the parent theorem. -/
def hidden (o : AcceptingOpening absorb) : Digest8 × Digest8 × Blind5 :=
  (o.spanDigest, o.ctx, o.blinding)

end AcceptingOpening

/-! ## §2 — the DETERMINISTIC collision extractor, a function of the two openings' opened data
ALONE.

`collOfHidden`'s type is the structural independence claim: it takes two hidden triples and
`absorb` — a simulator view CANNOT be an input, because the type has no slot for one. -/

/-- The collision extractor: from the two opened hidden triples, the specific colliding preimage
pair — the arity-16 stage-1 pair when the stage-2 preimages agree, else the arity-14 stage-2
pair. TOTAL and decidable-branching; consumes NOTHING but the two openings' opened data. -/
def collOfHidden (absorb : List ℤ → Digest8) :
    Digest8 × Digest8 × Blind5 → Digest8 × Digest8 × Blind5 → List ℤ × List ℤ
  | (d₁, ct₁, r₁), (d₂, ct₂, r₂) =>
    if packCommitW (wideFoldPair absorb d₁ ct₁) r₁ = packCommitW (wideFoldPair absorb d₂ ct₂) r₂
    then (pack8 d₁ ct₁, pack8 d₂ ct₂)
    else (packCommitW (wideFoldPair absorb d₁ ct₁) r₁, packCommitW (wideFoldPair absorb d₂ ct₂) r₂)

/-- The extractor on two openings: `collOfHidden` fed exactly their opened data. -/
def collFind (absorb : List ℤ → Digest8) (o₁ o₂ : AcceptingOpening absorb) : List ℤ × List ℤ :=
  collOfHidden absorb o₁.hidden o₂.hidden

/-- **The pure extraction core.** If the two stage-2 blinded images agree (equal published
commit, routed through `guardedHidingSpanWideBlind_commit_binds`) but the hidden triples differ,
the extractor's pair is a genuine `Coll8` collision — a single named pair, not a bare `∃`. -/
theorem collOfHidden_collides (absorb : List ℤ → Digest8)
    (d₁ ct₁ : Digest8) (r₁ : Blind5) (d₂ ct₂ : Digest8) (r₂ : Blind5)
    (himg : absorb (packCommitW (wideFoldPair absorb d₁ ct₁) r₁)
          = absorb (packCommitW (wideFoldPair absorb d₂ ct₂) r₂))
    (hdistinct : (d₁, ct₁, r₁) ≠ (d₂, ct₂, r₂)) :
    Coll8 absorb (collOfHidden absorb (d₁, ct₁, r₁) (d₂, ct₂, r₂)) := by
  simp only [collOfHidden]
  by_cases hpc : packCommitW (wideFoldPair absorb d₁ ct₁) r₁
      = packCommitW (wideFoldPair absorb d₂ ct₂) r₂
  · -- stage-2 preimages agree ⇒ mid and blinding agree ⇒ the stage-1 pair collides
    rw [if_pos hpc]
    obtain ⟨hmid, hr⟩ := packCommitW_inj hpc
    have himg1 : absorb (pack8 d₁ ct₁) = absorb (pack8 d₂ ct₂) := by
      simpa only [wideFoldPair] using hmid
    refine ⟨fun hp8 => ?_, himg1⟩
    obtain ⟨hd, hct⟩ := pack8_inj hp8
    exact hdistinct (by rw [hd, hct, hr])
  · -- stage-2 preimages differ but their images agree: the stage-2 pair IS the collision
    rw [if_neg hpc]
    exact ⟨hpc, himg⟩

/-- **Two accepting openings of one published commit yield the extractor's collision.** The
deterministic single-pair repackaging of the parent disjunction
(`guardedHidingSpanWideBlind_two_openings_collide`), routed through the same
`guardedHidingSpanWideBlind_commit_binds`. Hypotheses: the two OPENINGS, their equal published
commit, their distinct opened data. Nothing else. -/
theorem two_openings_collide (absorb : List ℤ → Digest8)
    (o₁ o₂ : AcceptingOpening absorb)
    (hcommit : o₁.commit = o₂.commit)
    (hdistinct : o₁.hidden ≠ o₂.hidden) :
    Coll8 absorb (collFind absorb o₁ o₂) := by
  have hb₁ : o₁.commit = holeCommitWideOf absorb o₁.spanDigest o₁.ctx o₁.blinding :=
    (guardedHidingSpanWideBlind_commit_binds absorb o₁.chipSound o₁.sat o₁.rowsNonempty).2
  have hb₂ : o₂.commit = holeCommitWideOf absorb o₂.spanDigest o₂.ctx o₂.blinding :=
    (guardedHidingSpanWideBlind_commit_binds absorb o₂.chipSound o₂.sat o₂.rowsNonempty).2
  have himg : absorb (packCommitW (wideFoldPair absorb o₁.spanDigest o₁.ctx) o₁.blinding)
      = absorb (packCommitW (wideFoldPair absorb o₂.spanDigest o₂.ctx) o₂.blinding) := by
    have h := hb₁.symm.trans (hcommit.trans hb₂)
    simpa only [holeCommitWideOf] using h
  exact collOfHidden_collides absorb o₁.spanDigest o₁.ctx o₁.blinding
    o₂.spanDigest o₂.ctx o₂.blinding himg hdistinct

/-! ## §3 — THE KEYSTONE: binding survives the simulator. -/

/-- **`binding_survives_simulation` — commitment-layer simulation-extractability.**

Quantify over:

  * ANY perfect-ZK simulator object `Z : PerfectZK` (the repo's simulator carrier —
    `Metatheory.Open.PerfectZK`), and ANY set `views` of its simulated outputs (each certified a
    genuine witness-free `Z.sim` output by `hsimulated` — the adversary has seen arbitrarily many
    simulated proofs);
  * an ADVERSARY that, AS A FUNCTION OF those views, publishes a family of commits
    (`commitsOf views : ι → Digest8`, index set of its choosing) and produces two accepting
    openings (`openingsOf views`);

and suppose the two openings both open ONE commit of the family (`hopen₁`, `hopen₂` — e.g. a
maul that REUSES a published commit with a new opening) with distinct opened data.

CONCLUSION: the extractor's pair is a genuine `Coll8 absorb` collision, AS DATA — and the
collision term `collOfHidden absorb (…).hidden (…).hidden` is built from the two openings' opened
data ALONE. `views`, `hsimulated`, `Z`, and `commitsOf` appear in NO position the extraction
consumes: the proof is word-for-word the transcript-free binding extraction, which is precisely
why binding survives the simulator. (Commitment layer ONLY — see the header for what the
STARK-layer Tier-3 frontier would additionally need.) -/
theorem binding_survives_simulation (absorb : List ℤ → Digest8)
    (Z : PerfectZK.{u}) (views : Set Z.V)
    (hsimulated : ∀ v ∈ views, ∃ s : Z.S, v = Z.sim s)
    {ι : Type} (commitsOf : Set Z.V → ι → Digest8)
    (openingsOf : Set Z.V → AcceptingOpening absorb × AcceptingOpening absorb)
    (i : ι)
    (hopen₁ : (openingsOf views).1.commit = commitsOf views i)
    (hopen₂ : (openingsOf views).2.commit = commitsOf views i)
    (hdistinct : (openingsOf views).1.hidden ≠ (openingsOf views).2.hidden) :
    Coll8 absorb (collOfHidden absorb (openingsOf views).1.hidden (openingsOf views).2.hidden) :=
  two_openings_collide absorb (openingsOf views).1 (openingsOf views).2
    (hopen₁.trans hopen₂.symm) hdistinct

/-- **The maul special case, named.** An adversary who has seen the simulated views and REUSES
one published commit `c` with a second, different opening hands back the collision. (The family
is the singleton `c`.) -/
theorem maul_reusing_commit_collides (absorb : List ℤ → Digest8)
    (Z : PerfectZK.{u}) (views : Set Z.V)
    (hsimulated : ∀ v ∈ views, ∃ s : Z.S, v = Z.sim s)
    (c : Digest8) (o₁ o₂ : AcceptingOpening absorb)
    (h₁ : o₁.commit = c) (h₂ : o₂.commit = c)
    (hdistinct : o₁.hidden ≠ o₂.hidden) :
    Coll8 absorb (collOfHidden absorb o₁.hidden o₂.hidden) :=
  two_openings_collide absorb o₁ o₂ (h₁.trans h₂.symm) hdistinct

/-- **STRUCTURAL INDEPENDENCE, exhibited.** Two DIFFERENT simulators over DIFFERENT view sets,
two DIFFERENT adversary procedures — whenever the opened data agree, the extracted collision is
the IDENTICAL term. The simulation context is not merely unused in the hypotheses; it cannot
reach the collision at all, because `collOfHidden` factors through the opened data. -/
theorem collision_independent_of_simulation (absorb : List ℤ → Digest8)
    (Z : PerfectZK.{u}) (Z' : PerfectZK.{u})
    (views : Set Z.V) (views' : Set Z'.V)
    (openingsOf : Set Z.V → AcceptingOpening absorb × AcceptingOpening absorb)
    (openingsOf' : Set Z'.V → AcceptingOpening absorb × AcceptingOpening absorb)
    (hagree₁ : (openingsOf views).1.hidden = (openingsOf' views').1.hidden)
    (hagree₂ : (openingsOf views).2.hidden = (openingsOf' views').2.hidden) :
    collOfHidden absorb (openingsOf views).1.hidden (openingsOf views).2.hidden
      = collOfHidden absorb (openingsOf' views').1.hidden (openingsOf' views').2.hidden := by
  rw [hagree₁, hagree₂]

/-! ## §4 — NON-VACUITY: a concrete instance FIRES the keystone.

Opening 1 is the wide-blind refine's all-zero witness (`witTraceW`, `witTraceW_satisfies`,
`witTfW_chip_sound` — reused, not re-authored). Opening 2 is the MAUL: the SAME published
`hole_commit` (all lanes `0`) opened with a DIFFERENT blinding vector (first blinding lane
`gBLIND 0 = 1`, the wide-blind refine's `mutBlind0Row`) over its OWN sound chip table. Note the
contrast with the refine's canary `mutBlind0_not_satisfied`: there the mauled row was presented
against the HONEST table and was REFUSED; here the maul brings a sound table of its own, so it
genuinely ACCEPTS — and the keystone converts that acceptance into a collision of `wZeroAbsorb`,
as data. -/

section NonVacuity

/-- The maul's chip rows: the three lookup tuples evaluated on `mutBlind0Row` (`gBLIND 0 = 1`). -/
def spanRow₂ : List ℤ := (chipLookupTupleN spanIns (wCols gDIGEST)).map (·.eval mutBlind0Row)
def stage1Row₂ : List ℤ :=
  (chipLookupTupleN (wStageIns gDIGEST gCT) (wCols gMID)).map (·.eval mutBlind0Row)
def stage2Row₂ : List ℤ :=
  (chipLookupTupleN commitStage2WideIns (wCols gHOLE)).map (·.eval mutBlind0Row)

/-- The maul's chip table: exactly its three evaluated rows. -/
def wTf₂ : TraceFamily := fun id =>
  match id with
  | .poseidon2 => [spanRow₂, stage1Row₂, stage2Row₂]
  | _ => []

/-- The maul's single-row trace: `mutBlind0Row` (`gBLIND 0 = 1`, all else `0`), public inputs all
`0` — the SAME published commit as the honest witness. -/
def witTrace₂ : VmTrace := { rows := [mutBlind0Row], pub := fun _ => 0, tf := wTf₂ }

/-- Every column other than `gBLIND 0` in `mutBlind0Row` is `0`, so every boundary pin holds
against the all-zero public inputs. -/
private theorem mutBlind0Row_pin (col pin : Nat) (hcol : col ≠ gBLIND 0) :
    (envAt witTrace₂ 0).loc col ≡ (envAt witTrace₂ 0).pub pin [ZMOD 2013265921] := by
  show mutBlind0Row col ≡ (0 : ℤ) [ZMOD 2013265921]
  unfold Dregg2.Circuit.Emit.GuardedHidingSpanWideBlindRefine.mutBlind0Row
  rw [if_neg hcol]

/-- **The maul PROVABLY satisfies the emitted descriptor** — over its own chip table. -/
theorem witTrace₂_satisfies :
    Satisfied2 hash0 guardedHidingSpanWideBlindDesc (fun _ => 0) (fun _ => (0, 0)) [] witTrace₂ where
  rowConstraints := by
    intro i hi c hc
    have hi0 : i = 0 := by
      have : i < 1 := by simpa [witTrace₂] using hi
      omega
    subst hi0
    have hfst : ((0 : Nat) == 0) = true := rfl
    have hlst : ((0 : Nat) + 1 == witTrace₂.rows.length) = true := rfl
    rw [hfst, hlst]
    simp only [guardedHidingSpanWideBlindDesc, ctPins, holePins, guardPins, List.append_assoc,
      List.mem_append, List.mem_cons, List.mem_map, List.mem_finRange, List.not_mem_nil,
      or_false, true_and, or_assoc] at hc
    rcases hc with rfl | rfl | rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    · exact (holdsVm_piFirst_true (envAt witTrace₂ 0) true (gCT k) (piCT k)).mpr
        (mutBlind0Row_pin (gCT k) (piCT k)
          (by simp only [gCT, gBLIND, Fin.val_zero]; have := k.isLt; omega))
    · exact (holdsVm_piFirst_true (envAt witTrace₂ 0) true (gHOLE k) (piHOLE k)).mpr
        (mutBlind0Row_pin (gHOLE k) (piHOLE k)
          (by simp only [gHOLE, gBLIND, Fin.val_zero]; have := k.isLt; omega))
    · exact (holdsVm_piFirst_true (envAt witTrace₂ 0) true (gGUARD k) (piGUARD k)).mpr
        (mutBlind0Row_pin (gGUARD k) (piGUARD k)
          (by simp only [gGUARD, gBLIND, Fin.val_zero]; have := k.isLt; omega))
  rowHashes := by intro i _; trivial
  rowRanges := by
    intro i _ r hr
    simp only [guardedHidingSpanWideBlindDesc, List.not_mem_nil] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_ghsw]; simp
  memDisciplined := by rw [memLog_ghsw]; trivial
  memBalanced := by rw [memLog_ghsw]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_ghsw]; rfl
  mapTableFaithful := by rw [mapLog_ghsw]; rfl

/-- **The maul's chip table is SOUND for `wZeroAbsorb`** — each row is a genuine `chipRowN` of
its inputs (which now carry `gBLIND 0 = 1`). -/
theorem wTf₂_chip_sound : ChipTableSoundN (wPermOut wZeroAbsorb) (witTrace₂.tf .poseidon2) := by
  intro r hr
  simp only [witTrace₂, wTf₂, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨spanIns.map (·.eval mutBlind0Row), by decide, by decide⟩
  · exact ⟨(wStageIns gDIGEST gCT).map (·.eval mutBlind0Row), by decide, by decide⟩
  · exact ⟨commitStage2WideIns.map (·.eval mutBlind0Row), by decide, by decide⟩

/-- The HONEST accepting opening — the wide-blind refine's all-zero witness, reused verbatim. -/
def openHonest : AcceptingOpening wZeroAbsorb where
  hash := hash0
  minit := fun _ => 0
  mfin := fun _ => (0, 0)
  maddrs := []
  trace := witTraceW
  chipSound := witTfW_chip_sound
  sat := witTraceW_satisfies
  rowsNonempty := List.cons_ne_nil _ _

/-- The MAULED accepting opening — same published commit, different blinding vector, its own
sound table. -/
def openMauled : AcceptingOpening wZeroAbsorb where
  hash := hash0
  minit := fun _ => 0
  mfin := fun _ => (0, 0)
  maddrs := []
  trace := witTrace₂
  chipSound := wTf₂_chip_sound
  sat := witTrace₂_satisfies
  rowsNonempty := List.cons_ne_nil _ _

/-- **THE KEYSTONE FIRES.** The simulator is the repo's own `PerfectZK` teeth instance
(`Teeth.otp`); the view set is its ENTIRE simulator image (the adversary has seen every simulated
view there is); the adversary's commit family and openings are functions of that set; the two
openings open the one published commit with distinct hidden data — and the collision comes back
as data. -/
theorem demo_binding_survives_simulation :
    Coll8 wZeroAbsorb
      (collOfHidden wZeroAbsorb openHonest.hidden openMauled.hidden) :=
  binding_survives_simulation wZeroAbsorb Teeth.otp
    {v | ∃ s, v = Teeth.otp.sim s}
    (fun _ hv => hv)
    (commitsOf := fun _ (_ : Unit) => openHonest.commit)
    (openingsOf := fun _ => (openHonest, openMauled))
    ()
    rfl
    (by decide)
    (by decide)

-- CANARIES (computed, kernel-checked): the maul really does reuse the published commit; the two
-- openings really are distinct; the extracted pair really is a genuine collision of the stand-in
-- absorb (two DISTINCT preimages, EQUAL images); and on IDENTICAL openings the extractor's pair
-- is NOT a collision — `Coll8` is refutable, no free pass.
#guard decide (openMauled.commit = openHonest.commit)
#guard decide (openHonest.hidden ≠ openMauled.hidden)
#guard decide ((collOfHidden wZeroAbsorb openHonest.hidden openMauled.hidden).1
                 ≠ (collOfHidden wZeroAbsorb openHonest.hidden openMauled.hidden).2)
#guard decide (Coll8 wZeroAbsorb (collOfHidden wZeroAbsorb openHonest.hidden openMauled.hidden))
#guard decide (¬ Coll8 wZeroAbsorb (collOfHidden wZeroAbsorb openHonest.hidden openHonest.hidden))

end NonVacuity

/-! ## §5 — axiom tripwires. -/

#assert_axioms collOfHidden_collides
#assert_axioms two_openings_collide
#assert_axioms binding_survives_simulation
#assert_axioms maul_reusing_commit_collides
#assert_axioms collision_independent_of_simulation
#assert_axioms witTrace₂_satisfies
#assert_axioms wTf₂_chip_sound
#assert_axioms demo_binding_survives_simulation

end Dregg2.Crypto.BindingSurvivesSimulation
