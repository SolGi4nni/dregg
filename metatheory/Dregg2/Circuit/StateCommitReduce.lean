/-
# Dregg2.Circuit.StateCommitReduce — the REDUCTION-FORM twin of the state-commitment binding chain.

`StateCommit`/`CircuitSoundness` bind the full-state root under carried INJECTIVITY hypotheses
(`compressInjective`, `compressNInjective`, `cellLeafInjective`) — each FALSE at real params
(`HashFloorHonesty.*_false_of_finite_range`: a bounded-range hash cannot be injective). This module
de-vacuates the chain: every binding theorem is restated in REDUCTION FORM — the SAME good conclusion
holds, OR the proof hands back a CONCRETE collision of one of the four commitment primitives (a
`StateBreak`). No injectivity hypothesis appears anywhere in the `_orBreak` twins; they are valid at
the real hash.

The chain, bottom-up (each mirrors its injective original step for step, swapping every injectivity
appeal for the matching `CollisionReduce` leaf and threading with `OrBreak.bind`/`map₂`):

  1. `movedDigestBindsCells_orBreak`  — twin of `StateCommit.MovedDigestBindsCells` (:260).
  2. `frameDigestBindsCells_orBreak`  — twin of `StateCommit.FrameDigestBindsCells` (:275).
  3. `recStateCommit_binds_orBreak`   — twin of `StateCommit.recStateCommit_binds` (:554).
  4. `cellDigest_binds_cells_orBreak` — twin of `StateCommit.cellDigest_binds_cells` (:574).
  5. `recStateCommit_binds_kernel_orBreak` — twin of `StateCommit.recStateCommit_binds_kernel` (:620).
  6. `commit_binds_orBreak`           — twin of `CircuitSoundness.CommitSurface.commit_binds` (:145).
  7. `stateDecode_pre/post_faithful_orBreak` — twins of `CircuitSoundness.stateDecode_*_faithful`
     (:202/:211): two decodes of the same published commitment have equal kernels, or a StateBreak.

The raw layers (1–5) are parametric in the bare primitives, so they can be INSTANTIATED AT A REAL
(non-injective) HASH — that is the whole point. The `CommitSurface` layers (6–7) take the surface `S`
only for its five primitive CARRIERS + `restFrame` (the rest-hash frame iff, which is not a hash-
collision event); none of the twins consults `S.cmbInj/compInj/compNInj/leafInj`.

Non-vacuity, both directions:
  * `resolve` recovery — `commit_binds_of_no_stateBreak` / `recStateCommit_binds_kernel_of_no_break`
    recover the injective originals' conclusions verbatim from `¬ StateBreak` (and
    `surface_no_stateBreak` shows a `CommitSurface`'s bundled injectivity refutes its own break, so
    the twin strictly subsumes the original).
  * FIRE — `fire_break_caught`: instantiate layer 1 at the LOSSY `+` node hash with a concrete
    colliding pair (100+5 = 99+6). The good branch is impossible (the values differ), so the twin is
    FORCED to hand back a concrete `StateBreak` — the machinery catches the fake hash instead of
    silently binding.
-/
import Dregg2.Circuit.CollisionReduce
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.StateCommitReduce

open Dregg2.Circuit
open Dregg2.Exec
open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.CircuitSoundness (CommitSurface PublishedCommit StateDecode)

/-! ## §0 — the break events.

`StateBreakP` is the raw four-way apex break over bare primitives (usable at a REAL hash);
`StateBreak S` is the mandated `CommitSurface` view — definitionally the same disjunction over `S`'s
carriers. -/

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

The rest-hash frame iff (`RestHashIffFrame RH`) is NOT a hash-collision event (it is the modeling
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
its four injectivity hypotheses, from `¬ StateBreakP` instead. -/
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

end Raw

/-! ## §5 — the `CommitSurface` view: `StateBreak S` + the top-layer twins.

The surface `S` is consulted ONLY for its five primitive carriers and the non-collision `restFrame`
premise. None of the twins touches `S.cmbInj/compInj/compNInj/leafInj` — the bundled injectivity is
used exactly once below, in `surface_no_stateBreak`, to show it REFUTES the break (so `resolve`
recovers the originals and the twins strictly subsume them). -/

/-- **The state-commit apex break over a `CommitSurface`**: a concrete collision of the surface's
sponge, root combiner, node hash, or cell-leaf hash. -/
def StateBreak (S : CommitSurface) : Prop :=
  SpongeCollision S.compressN ∨ CompressCollision S.cmb ∨ CompressCollision S.compress
    ∨ CellCollision S.CH

/-- `StateBreak` is the raw break at the surface's carriers (definitional). -/
theorem stateBreak_eq_raw (S : CommitSurface) :
    StateBreak S = StateBreakP S.CH S.cmb S.compress S.compressN := rfl

/-- **Twin of `CommitSurface.commit_binds` (CircuitSoundness.lean:145).** Two kernels whose surface
commitments agree (same turn, both `AccountsWF`) are EQUAL — or the adversary produced a concrete
collision of one of `S`'s four hash carriers. Uses NO `S.*Inj` field (only the carriers +
`S.restFrame`). -/
theorem commit_binds_orBreak (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : S.commit k t = S.commit k' t) :
    OrBreak (StateBreak S) (k = k') :=
  recStateCommit_binds_kernel_orBreak S.CH S.cmb S.compress S.compressN S.RH S.restFrame
    k k' t hwf hwf' hfin hfin' h

/-- **Twin of `stateDecode_pre_faithful` (CircuitSoundness.lean:202).** Two pre-states decoding the
SAME published commitment have EQUAL kernels — or a concrete `StateBreak`. Pure commitment binding,
no admissibility, NO injectivity. -/
theorem stateDecode_pre_faithful_orBreak (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable pre.kernel) (hfin' : FiniteRepresentable pre'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    OrBreak (StateBreak S) (pre.kernel = pre'.kernel) :=
  commit_binds_orBreak S pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hfin hfin'
    (h.preBinds ▸ h'.preBinds ▸ rfl)

/-- **Twin of `stateDecode_post_faithful` (CircuitSoundness.lean:211).** Two post-states decoding
the SAME published commitment have EQUAL kernels — or a concrete `StateBreak`. -/
theorem stateDecode_post_faithful_orBreak (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable post.kernel) (hfin' : FiniteRepresentable post'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    OrBreak (StateBreak S) (post.kernel = post'.kernel) :=
  commit_binds_orBreak S post.kernel post'.kernel pc.turn h.postWF h'.postWF hfin hfin'
    (h.postBinds ▸ h'.postBinds ▸ rfl)

/-! ## §6 — non-vacuity, direction 1: `resolve` recovers the injective originals. -/

/-- A `CommitSurface`'s bundled injectivity fields refute its own break: under `S.*Inj`, no
collision of any carrier exists. (This is exactly where the original layer's hypotheses were
consumed — the twins moved them from EVERY theorem to this ONE refutation.) -/
theorem surface_no_stateBreak (S : CommitSurface) : ¬ StateBreak S := by
  rintro (⟨xs, ys, hne, heq⟩ | ⟨p, q, hne, heq⟩ | ⟨p, q, hne, heq⟩ | ⟨c, v, w, hne, heq⟩)
  · exact hne (S.compNInj xs ys heq)
  · obtain ⟨h1, h2⟩ := S.cmbInj p.1 p.2 q.1 q.2 heq
    exact hne (by cases p; cases q; simp_all)
  · obtain ⟨h1, h2⟩ := S.compInj p.1 p.2 q.1 q.2 heq
    exact hne (by cases p; cases q; simp_all)
  · exact hne (S.leafInj c v w heq)

/-- **Non-vacuity (resolve):** from `¬ StateBreak S`, the twin recovers the injective original's
conclusion verbatim — the `_of_no_stateBreak` form of `CommitSurface.commit_binds`. -/
theorem commit_binds_of_no_stateBreak (S : CommitSurface) (hNo : ¬ StateBreak S)
    (k k' : RecordKernelState) (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : S.commit k t = S.commit k' t) : k = k' :=
  OrBreak.resolve hNo (commit_binds_orBreak S k k' t hwf hwf' hfin hfin' h)

/-- **The originals are strictly subsumed:** `CommitSurface.commit_binds` re-derived from the twin
alone (the surface's own injectivity refutes the break, `resolve` hands back the good branch). -/
theorem commit_binds_recovered (S : CommitSurface) (k k' : RecordKernelState)
    (t : Dregg2.Exec.Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : FiniteRepresentable k) (hfin' : FiniteRepresentable k')
    (h : S.commit k t = S.commit k' t) : k = k' :=
  commit_binds_of_no_stateBreak S (surface_no_stateBreak S) k k' t hwf hwf' hfin hfin' h

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

/-! ## §8 — axiom hygiene: every twin pinned kernel-clean. -/

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
#assert_axioms stateBreak_eq_raw
#assert_axioms commit_binds_orBreak
#assert_axioms stateDecode_pre_faithful_orBreak
#assert_axioms stateDecode_post_faithful_orBreak
#assert_axioms surface_no_stateBreak
#assert_axioms commit_binds_of_no_stateBreak
#assert_axioms commit_binds_recovered
#assert_axioms fire_movedDigest_eq
#assert_axioms fire_break_caught
#assert_axioms fire_break_is_plus_collision

end Dregg2.Circuit.StateCommitReduce
