/-
# Dregg2.Circuit.StateCommitReduceRaw — the RAW (surface-free) half of the state-commit reduction.

`StateCommit`/`CircuitSoundness` bind the full-state root under carried INJECTIVITY hypotheses
(`compressInjective`, `compressNInjective`, `cellLeafInjective`) — each FALSE at real params
(`HashFloorHonesty.*_false_of_finite_range`: a bounded-range hash cannot be injective). This module
de-vacuates the chain: every binding theorem is restated in REDUCTION FORM — the SAME good conclusion
holds, OR the proof hands back a CONCRETE collision of one of the four commitment primitives (a
`StateBreakP`). No injectivity hypothesis appears anywhere in the `_orBreak` twins; they are valid at
the real hash.

⚑⚑ **AND THAT IS NOT ENOUGH — READ §4c BEFORE CONSUMING ANY `_orBreak` TWIN.** `StateBreakP`'s first
disjunct is a GLOBAL collision existential over `compressN`, which pigeonhole SUPPLIES at every
BabyBear-bounded sponge. So at deployed parameters the break branch holds unconditionally, every
`OrBreak (StateBreakP …) P` is literally `True`, and the twins are vacuous — by free disjunct instead
of by false hypothesis. §4c PROVES that (`orBreak_stateBreakP_iff_True`, over an arbitrary good
branch). §5 is the replacement the apex path consumes: an UNCONDITIONAL binding whose residual is
`StateCommitLeafRegrounded.RecStateCommitColl` — the same four commitment primitives, but stated at
the SPECIFIC argument pairs the extraction visits. §1–§4 are kept because three out-of-scope modules
(`HistoryAggregation`, `RecursiveAggregation`, `CommitFaithfulRegrounded`) still thread them; each of
those threadings is vacuous at deployed parameters by §4c and is named, unported work.

⚑ **WHY THIS MODULE EXISTS SEPARATELY FROM `StateCommitReduce` (2026-08-01).** These layers are
parametric in the BARE primitives (`CH cmb compress compressN RH`) and need nothing from
`CircuitSoundness` — verified by inspection of every declaration below: the only imports they touch
are `StateCommit` (`recStateCommit`/`cellDigest`/`frameDigest`/`movedDigest`/`AccountsWF`),
`RestFrameFin` (`RestHashIffFrameFin`/`FiniteRepresentable`) and `CollisionReduce` (the `OrBreak`
monad + the per-hash collision leaves). Sitting BELOW `CircuitSoundness` is what lets
`CircuitSoundness` itself state its bindings in reduction form: `CommitSurface.commit_binds` (the
injective original) used the four refuted `CommitSurface` injectivity fields, and its in-module
consumers (`stateDecode_*_faithful`, `stateDecodeChain_frame_continuous`) could not be repointed at a
twin that lived ABOVE them. Same manoeuvre `RestFrameFin.lean` made on 2026-07-31 for
`RestHashIffFrameFin`, and for the same reason: an obligation the apex path must consume has to be
DEFINED below the apex path.

The chain, bottom-up (each mirrors its injective original step for step, swapping every injectivity
appeal for the matching `CollisionReduce` leaf and threading with `OrBreak.bind`/`map₂`):

  1. `movedDigestBindsCells_orBreak`  — twin of `StateCommit.MovedDigestBindsCells` (:260).
  2. `frameDigestBindsCells_orBreak`  — twin of `StateCommit.FrameDigestBindsCells` (:275).
  3. `recStateCommit_binds_orBreak`   — twin of `StateCommit.recStateCommit_binds` (:554).
  4. `cellDigest_binds_cells_orBreak` — twin of `StateCommit.cellDigest_binds_cells` (:574).
  5. `recStateCommit_binds_kernel_orBreak` — twin of `StateCommit.recStateCommit_binds_kernel` (:620).

The `CommitSurface` view of the same reduction (`CommitSurface.StateBreak`,
`CommitSurface.commit_binds_of_noColl`) is in `CircuitSoundness` — it needs the surface, so it cannot
live here; the decode-level twins (`stateDecode_*_faithful_of_noColl`) are in `StateCommitReduce`.

Non-vacuity, both directions:
  * `resolve` recovery — `recStateCommit_binds_kernel_of_no_break` recovers the injective original's
    conclusion verbatim from `¬ StateBreakP`. ⚠ That is a RECOVERY LEMMA, not a licence: at deployed
    BabyBear width `¬ StateBreakP` is itself FALSE (a bounded-range hash HAS collisions), so
    hypothesising it is the same vacuity the four injectivity fields were. Consumers carry the
    `OrBreak`; they do not assume the break away.
  * FIRE — `fire_break_caught`: instantiate layer 1 at the LOSSY `+` node hash with a concrete
    colliding pair (100+5 = 99+6). The good branch is impossible (the values differ), so the twin is
    FORCED to hand back a concrete `StateBreakP` — the machinery catches the fake hash instead of
    silently binding.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.RestFrameFin
import Dregg2.Circuit.StateCommitLeafRegrounded
import Dregg2.Circuit.SpongeCollisionShirk

namespace Dregg2.Circuit.StateCommitReduce

open Dregg2.Circuit
open Dregg2.Exec
open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)

/-! ## §0 — the break event (raw).

`StateBreakP` is the raw four-way apex break over bare primitives (usable at a REAL hash). The
`CommitSurface` view `CommitSurface.StateBreak` is `CircuitSoundness`'s, defined as exactly this
disjunction at the surface's carriers. -/

section Raw

variable (CH : CellId → Value → ℤ)
variable (cmb compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)
variable (RH : RecordKernelState → ℤ)

/-- **The raw state-commit apex break**: a concrete collision of the sponge, the root combiner, the
node hash, or the cell-leaf hash — the four commitment primitives `recStateCommit` runs over. -/
def StateBreakP : Prop :=
  SpongeCollision compressN ∨ CompressCollision cmb ∨ CompressCollision compress
    ∨ CellCollision CH

/-- Inject a sponge collision into the apex break. -/
theorem StateBreakP.ofSponge (h : SpongeCollision compressN) :
    StateBreakP CH cmb compress compressN := Or.inl h

/-- Inject a root-combiner collision into the apex break. -/
theorem StateBreakP.ofCmb (h : CompressCollision cmb) :
    StateBreakP CH cmb compress compressN := Or.inr (Or.inl h)

/-- Inject a node-hash collision into the apex break. -/
theorem StateBreakP.ofCompress (h : CompressCollision compress) :
    StateBreakP CH cmb compress compressN := Or.inr (Or.inr (Or.inl h))

/-- Inject a cell-leaf collision into the apex break. -/
theorem StateBreakP.ofCell (h : CellCollision CH) :
    StateBreakP CH cmb compress compressN := Or.inr (Or.inr (Or.inr h))

/-! ## §1 — layer 1: the digest-binding twins (of `MovedDigestBindsCells`/`FrameDigestBindsCells`).

Each mirrors its original: the original's `hC _ _ _ _ h` / `hN _ _ h` / `hL c _ _ h` injectivity
appeals become `compress_orBreak` / `spongeN_orBreak` / `cellLeaf_orBreak` leaves weakened into the
apex break, threaded by `bind`/`map₂`. NO injectivity hypothesis. -/

/-- **Twin of `MovedDigestBindsCells` (StateCommit.lean:260).** Equal moved (2-leaf) node hashes
force WHOLE-`Value` equality of BOTH `src` and `dst` leaves — or a concrete node-hash / leaf-hash
collision. The original's `hC`/`hL` hypotheses are GONE. -/
theorem movedDigestBindsCells_orBreak
    (f g : CellId → Value) (src dst : CellId)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    OrBreak (StateBreakP CH cmb compress compressN) (f src = g src ∧ f dst = g dst) := by
  unfold movedDigest at h
  -- original: `obtain ⟨hs, hd⟩ := hC _ _ _ _ h` — the compress-injectivity appeal, now a leaf.
  refine OrBreak.bind
    (OrBreak.weaken (StateBreakP.ofCompress CH cmb compress compressN)
      (compress_orBreak compress h)) ?_
  rintro ⟨hs, hd⟩
  -- original: `⟨hL src _ _ hs, hL dst _ _ hd⟩` — the two leaf-injectivity appeals, now leaves.
  exact OrBreak.map₂ And.intro
    (OrBreak.weaken (StateBreakP.ofCell CH cmb compress compressN) (cellLeaf_orBreak CH hs))
    (OrBreak.weaken (StateBreakP.ofCell CH cmb compress compressN) (cellLeaf_orBreak CH hd))

/-- **Twin of `FrameDigestBindsCells` (StateCommit.lean:275).** Equal frame digests over a carrier
`Sc` force per-cell WHOLE-`Value` equality on `Sc` — or a concrete sponge / leaf-hash collision. The
∀-over-`OrBreak` commute is classical: either every cell agrees (good), or some disagreeing cell
with an equal leaf hash IS a concrete `CellCollision`. -/
theorem frameDigestBindsCells_orBreak
    (k k' : RecordKernelState) (Sc : Finset CellId)
    (h : frameDigest CH compressN k Sc = frameDigest CH compressN k' Sc) :
    OrBreak (StateBreakP CH cmb compress compressN) (∀ c ∈ Sc, k.cell c = k'.cell c) := by
  unfold frameDigest at h
  -- original: `hN _ _ h` — the sponge-injectivity appeal, now a leaf.
  refine OrBreak.bind
    (OrBreak.weaken (StateBreakP.ofSponge CH cmb compress compressN)
      (spongeN_orBreak compressN h)) ?_
  intro hmap
  have hpt : ∀ c ∈ Sc.sort (· ≤ ·), CH c (k.cell c) = CH c (k'.cell c) :=
    List.map_inj_left.mp hmap
  by_cases hall : ∀ c ∈ Sc, k.cell c = k'.cell c
  · exact OrBreak.ok hall
  · -- some cell disagrees while its leaf hash agrees: a CONCRETE leaf collision.
    push Not at hall
    obtain ⟨c, hc, hne⟩ := hall
    exact OrBreak.broke (StateBreakP.ofCell CH cmb compress compressN
      ⟨c, k.cell c, k'.cell c, hne, hpt c ((Finset.mem_sort (· ≤ ·)).mpr hc)⟩)

/-! ## §2 — layer 2: the root-split twin (of `recStateCommit_binds`). -/

/-- **Twin of `recStateCommit_binds` (StateCommit.lean:554).** Equal full-state roots (same turn)
force equal cell-digest AND equal rest-hash children — or a concrete root-combiner collision. The
original's `hCmb : compressInjective cmb` hypothesis is GONE. -/
theorem recStateCommit_binds_orBreak
    (k k' : RecordKernelState) (t : Turn)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    OrBreak (StateBreakP CH cmb compress compressN)
      (cellDigest CH compress compressN k t = cellDigest CH compress compressN k' t
        ∧ RH k = RH k') := by
  unfold recStateCommit at hroot
  -- original: `CombineInjective cmb hCmb _ _ _ _ hroot` — the cmb-injectivity appeal, now a leaf.
  exact OrBreak.weaken (StateBreakP.ofCmb CH cmb compress compressN)
    (compress_orBreak cmb hroot)

/-! ## §3 — layer 3: the cell-map recovery twin (of `cellDigest_binds_cells`). -/

/-- **Twin of `cellDigest_binds_cells` (StateCommit.lean:574).** Equal cell digests (same turn,
equal `accounts`, both `AccountsWF`) force the WHOLE `cell` map equal — or a concrete collision.
Mirrors the original's exhaustive `funext` partition (src / dst / untouched-live / dead) with the
three injectivity appeals replaced by layers 1–2's twins, threaded by `bind`/`imp`. -/
theorem cellDigest_binds_cells_orBreak
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hAcc : k.accounts = k'.accounts)
    (hcd : cellDigest CH compress compressN k t = cellDigest CH compress compressN k' t) :
    OrBreak (StateBreakP CH cmb compress compressN) (k.cell = k'.cell) := by
  unfold cellDigest at hcd
  rw [← hAcc] at hcd
  -- original: `obtain ⟨hframeEq, hmovedEq⟩ := hCompress _ _ _ _ hcd` — now a compress leaf.
  refine OrBreak.bind
    (OrBreak.weaken (StateBreakP.ofCompress CH cmb compress compressN)
      (compress_orBreak compress hcd)) ?_
  rintro ⟨hframeEq, hmovedEq⟩
  -- original: `FrameDigestBindsCells … hCompressN hLeaf …` — now layer 1's frame twin.
  refine OrBreak.bind
    (frameDigestBindsCells_orBreak CH cmb compress compressN k k'
      (k.accounts \ {t.src, t.dst}) hframeEq) ?_
  intro hcellframe
  -- original: `MovedDigestBindsCells … hCompress hLeaf …` — now layer 1's moved twin.
  refine OrBreak.imp ?_
    (movedDigestBindsCells_orBreak CH cmb compress compressN k.cell k'.cell t.src t.dst hmovedEq)
  rintro ⟨hmsrc, hmdst⟩
  -- reconstruct the whole cell map by funext over the exhaustive partition (verbatim original).
  funext c
  by_cases hcsrc : c = t.src
  · subst hcsrc; exact hmsrc
  · by_cases hcdst : c = t.dst
    · subst hcdst; exact hmdst
    · by_cases hcacc : c ∈ k.accounts
      · have hmem : c ∈ k.accounts \ {t.src, t.dst} := by
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hcacc, hcsrc, hcdst⟩
        exact hcellframe c hmem
      · have hk'acc : c ∉ k'.accounts := by rw [← hAcc]; exact hcacc
        rw [hwf c hcacc, hwf' c hk'acc]

/-! ## §4 — layer 4: the whole-kernel recovery twin (of `recStateCommit_binds_kernel`).

The rest-hash frame iff (`RestHashIffFrameFin RH`) is NOT a hash-collision event (it is the modeling
premise that `RH` transports the 18 non-cell components), so it stays an explicit hypothesis here —
exactly as the `CommitSurface` carries it as `restFrame`. All four HASH injectivity hypotheses of the
original are gone. -/

/-- **Twin of `recStateCommit_binds_kernel` (StateCommit.lean:620).** Equal full-state roots (same
turn, both `AccountsWF`) force the WHOLE `RecordKernelState` equal — or a concrete collision of one
of the four commitment primitives. The original's `hCmb/hCompress/hCompressN/hLeaf` are GONE; only
the non-hash `RestHashIffFrame` premise remains. -/
theorem recStateCommit_binds_kernel_orBreak
    (hRest : RestHashIffFrameFin RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    OrBreak (StateBreakP CH cmb compress compressN) (k = k') := by
  refine OrBreak.bind (recStateCommit_binds_orBreak CH cmb compress compressN RH k k' t hroot) ?_
  rintro ⟨hcd, hRHeq⟩
  -- the 18 non-cell fields from RH (verbatim original — RestHashIffFrame is not a collision event).
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA,
    hHeaps, hNR, hRR, hCR⟩ := (hRest k k' hfin hfin').mp hRHeq
  -- the cell map from layer 3's twin.
  refine OrBreak.imp ?_
    (cellDigest_binds_cells_orBreak CH cmb compress compressN k k' t hwf hwf' hAcc.symm hcd)
  intro hcell
  cases k; cases k'
  simp_all

/-! ## §4b — `resolve` recovery (raw): the twin strictly subsumes the injective original. -/

/-- **Non-vacuity (resolve, raw):** if no collision of any of the four primitives is possible, layer
4's twin yields the injective original's conclusion verbatim — `recStateCommit_binds_kernel` without
its four injectivity hypotheses, from `¬ StateBreakP` instead.

⚠ A RECOVERY LEMMA, NOT A LICENCE. `¬ StateBreakP` is false at deployed BabyBear width for the same
pigeonhole reason the four injectivity fields are, so a theorem that HYPOTHESISES it is exactly as
vacuous as one that hypothesises them. Nothing on the apex path may consume this; it exists to show
the twin subsumes the original. -/
theorem recStateCommit_binds_kernel_of_no_break
    (hNo : ¬ StateBreakP CH cmb compress compressN)
    (hRest : RestHashIffFrameFin RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) : k = k' :=
  OrBreak.resolve hNo
    (recStateCommit_binds_kernel_orBreak CH cmb compress compressN RH hRest k k' t hwf hwf'
      hfin hfin' hroot)

/-! ## §4c — ⚑⚑ THE BREAK DISJUNCT IS FREE AT DEPLOYED PARAMETERS.

`StateBreakP`'s first disjunct is `SpongeCollision compressN`, a GLOBAL existential ("there EXIST two
colliding lists"). `SpongeCollisionShirk.spongeCollision_of_fieldBounded` supplies it at ANY sponge
whose outputs land in a BabyBear felt — which every deployed sponge does. So at deployed parameters
the break branch of every `OrBreak (StateBreakP …) P` in §1–§4 holds UNCONDITIONALLY, the dichotomy is
literally `True`, and the good branch carries NO information: the same pigeonhole that REFUTES the four
injectivity floors ESTABLISHES the break. The `_orBreak` twins traded vacuous-by-false-hypothesis for
vacuous-by-free-disjunct.

This is `SpongeCollisionShirk.orBreak_spongeCollision_iff_True` at THIS family's break event, stated
over an ARBITRARY good branch `P`, so it refutes every `OrBreak (StateBreakP …) _` in the tree at once
— §1–§4 here, `CommitSurface.StateBreak`'s view of them (definitionally the same `Prop`), and the
`HistoryAggregation`/`RecursiveAggregation`/`CommitFaithfulRegrounded` threadings.

§5 is the replacement, in the shape the landed cutovers use (`MapPathCutoverCheck`,
`MapOpsColumnLayout` §2, `AggregationAirSound`): a per-instance residual at a NAMED pair. -/

/-- **⚑⚑ THE SHIRK, AT THIS FAMILY'S BREAK EVENT.** At any field-bounded (= deployed-shaped) sponge,
`OrBreak (StateBreakP …) P` holds for EVERY proposition `P`, by the break branch alone. Cite this, not
a doc-comment, when a lane offers a `StateBreakP` disjunct as a vacuity fix. -/
theorem orBreak_stateBreakP_trivial
    (hb : SpongeCollisionShirk.FieldBounded compressN) (P : Prop) :
    OrBreak (StateBreakP CH cmb compress compressN) P :=
  OrBreak.broke (StateBreakP.ofSponge CH cmb compress compressN
    (SpongeCollisionShirk.spongeCollision_of_fieldBounded hb))

/-- **The shirk at its worst branch**: the dichotomy holds with the good branch `False`. Nothing
survives — a theorem of this shape is satisfied without its conclusion being satisfiable at all. -/
theorem orBreak_stateBreakP_False
    (hb : SpongeCollisionShirk.FieldBounded compressN) :
    OrBreak (StateBreakP CH cmb compress compressN) False :=
  orBreak_stateBreakP_trivial CH cmb compress compressN hb False

/-- **The shirk, as an equivalence** — the crisp form of the refusal. -/
theorem orBreak_stateBreakP_iff_True
    (hb : SpongeCollisionShirk.FieldBounded compressN) (P : Prop) :
    OrBreak (StateBreakP CH cmb compress compressN) P ↔ True :=
  ⟨fun _ => trivial, fun _ => orBreak_stateBreakP_trivial CH cmb compress compressN hb P⟩

/-! ## §5 — THE EXTRACTOR-SHAPED PORT: a per-instance residual at a NAMED pair.

The sound shape already exists for THIS chain and is landed:
`StateCommitLeafRegrounded.RecStateCommitColl CH RH cmb compress compressN k k' t` is the four-way
apex residual with every disjunct stated at the SPECIFIC argument pair the extraction visits
(`CompressColl cmb (cellDigest k t) (RH k) (cellDigest k' t) (RH k')`, then `CellDigestColl`'s node /
frame / moved pairs), never as `∃ two colliding inputs`. It carries all three teeth already
(`noRecStateCommitColl_diag` — SATISFIABLE at every hash on the diagonal;
`recStateCommitColl_refutable` — it FIRES at a constant hash; `noRecStateCommitColl_not_provable`).

What was missing is the FINITE-SUPPORT rest-frame variant: `StateCommitLeafRegrounded`'s whole-kernel
port takes the predecessor `RestHashIffFrame RH`, which
`RestFrameCardinalityFloor.restHashIffFrame_false_by_cardinality` refutes at EVERY `RH`; the deployed
obligation is `RestFrameFin.RestHashIffFrameFin` on finitely-representable states, which IS
satisfiable and is what `CommitSurface.restFrame` carries. These two theorems are that variant, and
they are what `CommitSurface.commit_binds_of_noColl` is. NO new floor binder: `RestHashIffFrameFin` is
the satisfiable successor, `AccountsWF`/`FiniteRepresentable` are structural, and the residual is
per-instance. -/

/-- **⚑ THE EXTRACTOR-SHAPED WHOLE-KERNEL BINDING (finite-support rest frame), UNCONDITIONAL.**
Equal full-state roots (same turn, both `AccountsWF`, both `FiniteRepresentable`) force the WHOLE
kernel equal, OR the NAMED four-way residual `RecStateCommitColl` holds at the exact argument pairs
the extraction visits. No injectivity hypothesis, no global collision existential, no floor.

This is `StateCommitLeafRegrounded.recStateCommit_binds_kernel_or_collides` with `RestHashIffFrame`
(refuted at every `RH`) replaced by the finite-support successor the deployed surface carries. -/
theorem recStateCommit_binds_kernel_or_collidesFin
    (hRest : RestHashIffFrameFin RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    k = k' ∨ StateCommitLeafRegrounded.RecStateCommitColl CH RH cmb compress compressN k k' t := by
  unfold recStateCommit at hroot
  rcases StateCommitLeafRegrounded.compress_binds_or_collides cmb _ _ _ _ hroot with
    ⟨hcd, hRHeq⟩ | hrootColl
  · obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA,
      hHeaps, hNR, hRR, hCR⟩ := (hRest k k' hfin hfin').mp hRHeq
    rcases StateCommitLeafRegrounded.cellDigest_binds_cells_or_collides CH compress compressN
        k k' t hwf hwf' hAcc.symm hcd with hcell | hcoll
    · refine Or.inl ?_
      cases k; cases k'
      simp_all
    · exact Or.inr (Or.inr hcoll)
  · exact Or.inr (Or.inl hrootColl)

/-- **⚑ THE S3 FORM** — the SAME conclusion the injective original drew (`k = k'`), from the
PER-INSTANCE side condition instead of a refuted floor or a free disjunct. The side condition is
SATISFIABLE (`noRecStateCommitColl_diag` holds at every hash on the diagonal), REFUTABLE
(`recStateCommitColl_refutable` fires at a constant hash), and NOT PROVABLE
(`noRecStateCommitColl_not_provable`) — the three-way separation that
`orBreak_stateBreakP_iff_True` proves the disjunctive form cannot make. -/
theorem recStateCommit_binds_kernel_of_noCollFin
    (hRest : RestHashIffFrameFin RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (hno : ¬ StateCommitLeafRegrounded.RecStateCommitColl CH RH cmb compress compressN k k' t)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    k = k' :=
  (recStateCommit_binds_kernel_or_collidesFin CH cmb compress compressN RH hRest k k' t hwf hwf'
    hfin hfin' hroot).resolve_right hno

/-- **⚑⚑ THE SEPARATION — the port is NOT a relabeling.** At one and the same deployed-shaped sponge:
the `StateBreakP` dichotomy holds with the good branch `False` (it says nothing), while the
per-instance residual is genuinely REFUTED at the honest (diagonal) pair (it says something). A
theorem re-grounded on `¬ RecStateCommitColl` at the pair in play therefore carries content that no
`OrBreak (StateBreakP …)` form can carry at deployed parameters. This is the acceptance test for the
port: the replacement survives here, the disjunctive twin provably does not. -/
theorem perInstance_sharper_than_stateBreakP
    (hb : SpongeCollisionShirk.FieldBounded compressN) (k : RecordKernelState) (t : Turn) :
    OrBreak (StateBreakP CH cmb compress compressN) False
      ∧ ¬ StateCommitLeafRegrounded.RecStateCommitColl CH RH cmb compress compressN k k t :=
  ⟨orBreak_stateBreakP_False CH cmb compress compressN hb,
    StateCommitLeafRegrounded.noRecStateCommitColl_diag CH RH cmb compress compressN k t⟩

end Raw

/-! ## §7 — non-vacuity, direction 2 (FIRE): the break branch actually fires on a lossy hash.

The injective originals cannot even be STATED at a lossy hash (their hypotheses are false). The
twins can — and on a concrete colliding pair they are FORCED into the break branch, handing back a
concrete collision. `+` as the node hash, `100+5 = 99+6`: the moved digests agree while the moved
values differ, so the good branch is refuted and the twin yields a `StateBreakP`. -/

/-- FIRE leaf hash: read the `ℤ` out of an `.int` cell (lossless on the fire domain). -/
def chFire : CellId → Value → ℤ := fun _ v => match v with | .int n => n | _ => 0
/-- FIRE lossy 2-to-1 hash: the `+`-fold the whole campaign exists to catch. -/
def plusFire : ℤ → ℤ → ℤ := fun a b => a + b
/-- FIRE sponge (placeholder carrier for the apex break's sponge slot). -/
def sumFire : List ℤ → ℤ := fun xs => xs.sum
/-- FIRE pre cell map: balances (100, 5). -/
def fFire : CellId → Value := fun c => if c = 0 then .int 100 else .int 5
/-- FIRE forged cell map: balances (99, 6) — different cells, same `+`-digest. -/
def gFire : CellId → Value := fun c => if c = 0 then .int 99 else .int 6

/-- The concrete collision the lossy node hash admits: `100 + 5 = 99 + 6`. -/
theorem fire_movedDigest_eq :
    movedDigest chFire plusFire fFire 0 1 = movedDigest chFire plusFire gFire 0 1 := by
  simp [movedDigest, chFire, plusFire, fFire, gFire]

/-- **FIRE.** On the lossy `+` node hash, layer 1's twin composes on the concrete colliding pair and
its good branch is IMPOSSIBLE (`fFire 0 ≠ gFire 0`), so the twin HANDS BACK a concrete
`StateBreakP` — the reduction form catches the fake hash instead of silently binding. (The injective
original is unusable here: its `compressInjective plusFire` hypothesis is false.) -/
theorem fire_break_caught : StateBreakP chFire plusFire plusFire sumFire := by
  have tw := movedDigestBindsCells_orBreak chFire plusFire plusFire sumFire fFire gFire 0 1
    fire_movedDigest_eq
  rcases tw with ⟨h0, _⟩ | hbrk
  · -- the good branch would say `.int 100 = .int 99` — refuted.
    exact absurd h0 (by simp [fFire, gFire])
  · exact hbrk

/-- The fire break really is inhabited by the expected node-hash collision (sanity: the break we
caught is realizable independently, so `fire_break_caught` is not a vacuous disjunct). -/
theorem fire_break_is_plus_collision : CompressCollision plusFire :=
  ⟨(100, 5), (99, 6), by simp, by norm_num [plusFire]⟩

/-! ## §7b — ⚑ THE PER-INSTANCE SIDE CONDITION IS LOAD-BEARING.

The tooth the disjunctive form provably could not carry: DELETE `hno` from
`recStateCommit_binds_kernel_of_noCollFin` and the statement is FALSE — not "weaker", FALSE — for
EVERY rest hash, honest or not. So `hno` is carrying the argument. (`orBreak_stateBreakP_iff_True`
is the dual reading: delete nothing from the `_orBreak` form and it is still `True`.)

The two witness kernels differ ONLY in `nullifiers`, so both are `AccountsWF` (identical `cell`,
`accounts = ∅`) and both are `FiniteRepresentable` (both are `denote` images); at a constant root
combiner their full-state roots agree by `rfl` while the kernels differ. -/

/-- The second witness: `finInit` with one spent nullifier. Same `cell`/`accounts`, so it inherits
`finInit`'s `AccountsWF`; distinct as a `RecordKernelState`. -/
def finNul : Dregg2.Circuit.FinKernelState.FinKernelState :=
  { Dregg2.Circuit.FinKernelState.finInit with nullifiers := [0] }

/-- `denote finInit` is `AccountsWF`: `accounts = ∅` and every cell reads the kernel default
(`(default : Value) = .int 0`, the alignment `FinKernelState.cell`'s default was chosen for). -/
theorem accountsWF_denote_finInit :
    AccountsWF (Dregg2.Circuit.FinKernelState.denote Dregg2.Circuit.FinKernelState.finInit) := by
  intro c _
  rw [Dregg2.Circuit.FinKernelState.denote_finInit]
  exact rfl

/-- `denote finNul` is `AccountsWF` — same `cell`/`accounts` fields as `finInit`, so this is the
previous theorem at a definitionally equal statement. -/
theorem accountsWF_denote_finNul :
    AccountsWF (Dregg2.Circuit.FinKernelState.denote finNul) :=
  accountsWF_denote_finInit

/-- The two witnesses are DISTINCT kernels — they disagree on `nullifiers`. -/
theorem denote_finInit_ne_finNul :
    Dregg2.Circuit.FinKernelState.denote Dregg2.Circuit.FinKernelState.finInit
      ≠ Dregg2.Circuit.FinKernelState.denote finNul := by
  intro h
  have hn := congrArg RecordKernelState.nullifiers h
  simp only [Dregg2.Circuit.FinKernelState.denote, finNul,
    Dregg2.Circuit.FinKernelState.finInit] at hn
  exact absurd hn (by decide)

/-- **⚑⚑ LOAD-BEARING.** For EVERY rest hash `RH` — including every honest one satisfying
`RestHashIffFrameFin` — the whole-kernel binding with the per-instance side condition DELETED is
FALSE. At a constant root combiner two `AccountsWF`, `FiniteRepresentable` kernels that differ only in
`nullifiers` commit to the same root. This is the mutation canary for the whole port: a version that
dropped `hno` would not be a port, it would be refuted. -/
theorem recStateCommit_binds_kernel_unconditional_false (RH : RecordKernelState → ℤ) :
    ¬ (∀ (CH : CellId → Value → ℤ) (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
        (k k' : RecordKernelState) (t : Turn),
        AccountsWF k → AccountsWF k' → FiniteRepresentable k → FiniteRepresentable k' →
        recStateCommit CH RH cmb compress compressN k t
          = recStateCommit CH RH cmb compress compressN k' t →
        k = k') := by
  intro hall
  exact denote_finInit_ne_finNul
    (hall (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ => 0) _ _
      goodTurnS
      accountsWF_denote_finInit accountsWF_denote_finNul
      (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
      (Dregg2.Circuit.RestFrameFin.finiteRepresentable_of_denote _)
      rfl)

/-! ## §8 — axiom hygiene: every raw twin pinned kernel-clean. -/

#assert_axioms StateBreakP.ofSponge
#assert_axioms StateBreakP.ofCmb
#assert_axioms StateBreakP.ofCompress
#assert_axioms StateBreakP.ofCell
#assert_axioms movedDigestBindsCells_orBreak
#assert_axioms frameDigestBindsCells_orBreak
#assert_axioms recStateCommit_binds_orBreak
#assert_axioms cellDigest_binds_cells_orBreak
#assert_axioms recStateCommit_binds_kernel_orBreak
#assert_axioms recStateCommit_binds_kernel_of_no_break
#assert_axioms fire_movedDigest_eq
#assert_axioms fire_break_caught
#assert_axioms fire_break_is_plus_collision
#assert_axioms orBreak_stateBreakP_trivial
#assert_axioms orBreak_stateBreakP_iff_True
#assert_axioms recStateCommit_binds_kernel_or_collidesFin
#assert_axioms recStateCommit_binds_kernel_of_noCollFin
#assert_axioms perInstance_sharper_than_stateBreakP
#assert_axioms accountsWF_denote_finInit
#assert_axioms denote_finInit_ne_finNul
#assert_axioms recStateCommit_binds_kernel_unconditional_false
-- The port must not secretly route back through the floors the campaign is draining.
#assert_not_depends_on Dregg2.Circuit.StateCommitReduce.recStateCommit_binds_kernel_or_collidesFin
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR, Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.compressInjective, Dregg2.Circuit.StateCommit.compressNInjective]
#assert_not_depends_on Dregg2.Circuit.StateCommitReduce.recStateCommit_binds_kernel_of_noCollFin
  [Dregg2.Circuit.Poseidon2Binding.Poseidon2SpongeCR, Dregg2.Circuit.StateCommit.cellLeafInjective,
   Dregg2.Circuit.StateCommit.compressInjective, Dregg2.Circuit.StateCommit.compressNInjective]

end Dregg2.Circuit.StateCommitReduce
