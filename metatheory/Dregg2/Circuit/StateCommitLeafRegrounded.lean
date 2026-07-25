/-
# Dregg2.Circuit.StateCommitLeafRegrounded — the `compressInjective` / `cellLeafInjective` endpoints,
re-grounded.

`StateCommit.MovedDigestBindsCells` and `StateCommit.FrameDigestBindsCells` conclude per-cell
`Value` equality from TWO carried ∀-injectivities each — `compressInjective compress` /
`compressNInjective compressN` at the node/sponge layer, and `cellLeafInjective CH` at the leaf.
Both leaf-side floors are FALSE at deployed BabyBear parameters:

  * `cellLeafInjective` — `StateCommitFloorRegrounded.cellLeafInjective_false_babyBear`: `Value` is
    INFINITE (`Value.int` injects `ℤ`) and a real Poseidon2 leaf lands in ONE field element.
  * `compressInjective` — `HashFloorHonesty.compressInjective_false_of_finite_range`: two field
    elements do not fit in one.

So every theorem threading those binders is conditional on a refuted premise. This module is the
S2/S3 port of that pair of endpoints, in the `Circuit/ListCommitRegrounded` shape:

  * **S2 (`*_binds_or_collides`)** — HYPOTHESIS-FREE: equal digests force equal cells OR a NAMED
    collision whose witness pair is carried in the conclusion. The extractors are TOTAL: on an
    equivocation they RETURN the specific colliding pair (`CompressColl.extracts` /
    `CellLeafColl.extracts` / `MovedColl.extracts` / `FrameColl.extracts`), which is exactly what
    the old proofs never built — injectivity DISCARDS a case, a reduction must PRODUCE the witness.
  * **S3 (`*_binds_of_no*Coll`)** — the SAME conclusions as the old endpoints, with the refuted
    universal replaced by a per-instance, refutable side condition about ONE named pair. These are
    what the mechanical cone port (`Tools/ConePort`) re-points threaders onto. HONEST-BUT-
    CONDITIONAL: at 1-felt widths the side condition is a ~2^15.5-breakable claim about the
    deployed hash at these named points — visible, refutable, never universal.
  * **No strength lost** (`*_of_carriers`): each old endpoint's exact statement is the injective
    special case of its port (the old ∀-hypothesis IMPLIES every per-instance side condition, via
    the `no*Coll_of_inj` bridges). What is given up is only the pretence that the deployed hash
    satisfies the injectivity.

⚑ **The 8-felt rule, stated out loud.** Nothing here instantiates a digest width. The refutations
above are about the deployed ~31-bit BabyBear felt (birthday ≈ 2^15.5), which is a WOUND under
repair, not a spec: the TARGET is the 8-felt digest (`card R = p^8 ≈ 2^247`, birthday ≈ 2^123.5).
The per-instance side conditions get STRONGER, not weaker, as the width is repaired — they are
claims about named points of whatever hash is deployed.

Teeth (§5): `compressColl_refutable` / `cellLeafColl_refutable` (the predicates FIRE at a constant
hash — they are not vacuously false), `noCompressColl_satisfiable` (they are satisfiable at a
deployed-shaped instance — `¬ Coll` is not vacuously false either), `movedDigest_unconditional_false`
/ `compress_binds_unconditional_false` (the side condition is LOAD-BEARING: the S3 statements with
`hno` DELETED are REFUTED), and `canary_moved_tamper_moves_digest_or_collides` (the left disjunct
BITES — at named points with no collision available, S2 genuinely forces the digests apart, with no
injectivity floor anywhere in the argument).

No `sorry`, no `axiom`, no `native_decide`; `decide` only on concrete closed instances.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Tactics

namespace Dregg2.Circuit.StateCommitLeafRegrounded

open Dregg2.Exec
open Dregg2.Circuit.StateCommit
  (compressInjective compressNInjective cellLeafInjective movedDigest frameDigest cellDigest
   recStateCommit recStateCommit_binds AccountsWF RestHashIffFrame)

set_option autoImplicit false

/-! ## §1 — the NAMED collision events (the S2 raw material).

Distinctness is INSIDE each predicate, so a side condition `¬ Coll` is never satisfied vacuously by
an equal pair, and never trivially true on a genuine equivocation. -/

/-- **`CompressColl h a b c d`** — the two argument PAIRS are a GENUINE collision of the 2-to-1 node
hash `h`: the pairs differ, the node hashes agree. The extractor is the identity — the colliding
pair IS `((a,b), (c,d))`, named in the predicate. -/
def CompressColl (h : ℤ → ℤ → ℤ) (a b c d : ℤ) : Prop :=
  ¬ (a = c ∧ b = d) ∧ h a b = h c d

/-- **`CellLeafColl CH c v w`** — the two `Value`s are a GENUINE collision of the leaf hash at the
FIXED cell `c`: distinct values, equal leaves. (Per-cell, matching `cellLeafInjective`'s own
diagonal shape — `StateCommitFloorRegrounded` §8 already records that this floor never covered the
family's cross-cell collisions.) -/
def CellLeafColl (CH : CellId → Value → ℤ) (c : CellId) (v w : Value) : Prop :=
  v ≠ w ∧ CH c v = CH c w

/-- The `CompressColl` pair is a genuine `h` collision (distinctness is intrinsic). -/
theorem CompressColl.extracts {h : ℤ → ℤ → ℤ} {a b c d : ℤ} (hc : CompressColl h a b c d) :
    ∃ p q : ℤ × ℤ, p ≠ q ∧ h p.1 p.2 = h q.1 q.2 :=
  ⟨(a, b), (c, d), fun hpq => hc.1 ⟨congrArg Prod.fst hpq, congrArg Prod.snd hpq⟩, hc.2⟩

/-- The `CellLeafColl` event yields a NAMED `Value`-level collision of the leaf hash at `c`. -/
theorem CellLeafColl.extracts {CH : CellId → Value → ℤ} {c : CellId} {v w : Value}
    (hc : CellLeafColl CH c v w) : ∃ x y : Value, x ≠ y ∧ CH c x = CH c y :=
  ⟨v, w, hc.1, hc.2⟩

/-! ## §2 — S2 at the PRIMITIVE layer: the unconditional dichotomies. NO floor hypothesis. -/

/-- **⚑ HYPOTHESIS-FREE node binding.** Equal node hashes force equal argument pairs OR a named
`CompressColl`. This replaces `compressInjective`'s refuted universal with a conclusion-carried
reduction: the collision disjunct names the exact pair the old proof would have fed to the
injectivity. -/
theorem compress_binds_or_collides (h : ℤ → ℤ → ℤ) (a b c d : ℤ) (heq : h a b = h c d) :
    (a = c ∧ b = d) ∨ CompressColl h a b c d := by
  by_cases hp : a = c ∧ b = d
  · exact Or.inl hp
  · exact Or.inr ⟨hp, heq⟩

/-- **⚑ HYPOTHESIS-FREE leaf binding.** Equal leaves at a fixed cell force equal `Value`s OR a named
`CellLeafColl`. -/
theorem cellLeaf_binds_or_collides (CH : CellId → Value → ℤ) (c : CellId) (v w : Value)
    (heq : CH c v = CH c w) : v = w ∨ CellLeafColl CH c v w := by
  by_cases hp : v = w
  · exact Or.inl hp
  · exact Or.inr ⟨hp, heq⟩

/-- **S3, node layer** — `compressInjective h` at ONE named argument quadruple. This is the exact
statement `CombineInjective` / the `cellDigest` split need. -/
theorem compress_binds_of_noColl (h : ℤ → ℤ → ℤ) (a b c d : ℤ)
    (hno : ¬ CompressColl h a b c d) (heq : h a b = h c d) : a = c ∧ b = d :=
  (compress_binds_or_collides h a b c d heq).resolve_right hno

/-- **S3, leaf layer** — `cellLeafInjective CH` at ONE named `(c, v, w)`. -/
theorem cellLeaf_binds_of_noColl (CH : CellId → Value → ℤ) (c : CellId) (v w : Value)
    (hno : ¬ CellLeafColl CH c v w) (heq : CH c v = CH c w) : v = w :=
  (cellLeaf_binds_or_collides CH c v w heq).resolve_right hno

/-! ## §3 — S2/S3 at the DIGEST layer: `movedDigest` (the 2-leaf node) and `frameDigest` (the
ordered sponge over the untouched carrier). These are the ports of `StateCommit`'s two endpoints. -/

/-- **`MovedLeafColl CH f g src dst`** — the moved pair equivocates at the LEAF layer: one of the
two moved cells has distinct `Value`s with equal leaves. -/
def MovedLeafColl (CH : CellId → Value → ℤ) (f g : CellId → Value) (src dst : CellId) : Prop :=
  CellLeafColl CH src (f src) (g src) ∨ CellLeafColl CH dst (f dst) (g dst)

/-- **`MovedColl CH compress f g src dst`** — a `movedDigest` equivocation at `(f, g)` broke ONE of
the two deployed objects: the node hash at the named leaf quadruple, or the leaf hash at `src`/`dst`. -/
def MovedColl (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (f g : CellId → Value) (src dst : CellId) : Prop :=
  CompressColl compress (CH src (f src)) (CH dst (f dst)) (CH src (g src)) (CH dst (g dst))
    ∨ MovedLeafColl CH f g src dst

/-- The umbrella extraction: a `MovedColl` is a genuine collision of ONE of the two deployed
objects — the node hash on a named `ℤ × ℤ` pair, or the leaf hash on a named `Value` pair. -/
theorem MovedColl.extracts {CH : CellId → Value → ℤ} {compress : ℤ → ℤ → ℤ}
    {f g : CellId → Value} {src dst : CellId} (hc : MovedColl CH compress f g src dst) :
    (∃ p q : ℤ × ℤ, p ≠ q ∧ compress p.1 p.2 = compress q.1 q.2)
      ∨ (∃ c : CellId, ∃ x y : Value, x ≠ y ∧ CH c x = CH c y) :=
  match hc with
  | .inl hn => Or.inl hn.extracts
  | .inr (.inl hl) => Or.inr ⟨src, hl.extracts⟩
  | .inr (.inr hl) => Or.inr ⟨dst, hl.extracts⟩

/-- **⚑ THE HYPOTHESIS-FREE MOVED BINDING (`_or_collides`).** Equal moved (2-leaf) node hashes force
BOTH moved cells' whole `Value`s equal, OR a named collision. This is the S2 of
`StateCommit.MovedDigestBindsCells` — its two refuted premises (`compressInjective compress`,
`cellLeafInjective CH`) replaced by a conclusion-carried reduction. Formally weaker than the old
endpoint, but it HOLDS of the deployed hash, which the old one did not. -/
theorem movedDigest_binds_or_collides (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (f g : CellId → Value) (src dst : CellId)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    (f src = g src ∧ f dst = g dst) ∨ MovedColl CH compress f g src dst := by
  unfold movedDigest at h
  by_cases hleaf : CH src (f src) = CH src (g src) ∧ CH dst (f dst) = CH dst (g dst)
  · by_cases hs : f src = g src
    · by_cases hd : f dst = g dst
      · exact Or.inl ⟨hs, hd⟩
      · exact Or.inr (Or.inr (Or.inr ⟨hd, hleaf.2⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hs, hleaf.1⟩))
  · exact Or.inr (Or.inl ⟨hleaf, h⟩)

/-- **S3, both carriers floor-borne** — the exact conclusion of `MovedDigestBindsCells` with BOTH
refuted binders replaced by one refutable side condition. -/
theorem movedDigest_binds_of_noColl (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (f g : CellId → Value) (src dst : CellId)
    (hno : ¬ MovedColl CH compress f g src dst)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    f src = g src ∧ f dst = g dst :=
  (movedDigest_binds_or_collides CH compress f g src dst h).resolve_right hno

/-- **S3, node-side only** — for a site whose leaf injectivity is genuinely proved (an injective
encoder, not a hash), only the node floor is replaced. -/
theorem movedDigest_binds_of_noCompressColl (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (hL : cellLeafInjective CH) (f g : CellId → Value) (src dst : CellId)
    (hno : ¬ CompressColl compress (CH src (f src)) (CH dst (f dst))
      (CH src (g src)) (CH dst (g dst)))
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    f src = g src ∧ f dst = g dst := by
  rcases movedDigest_binds_or_collides CH compress f g src dst h with hok | hcn | hl | hl
  · exact hok
  · exact absurd hcn hno
  · exact absurd (hL src _ _ hl.2) hl.1
  · exact absurd (hL dst _ _ hl.2) hl.1

/-- **S3, leaf-side only** — the dual, for a site with a genuinely proved node injectivity but a
floor-borne leaf hash. This is the variant the `cellLeafInjective` cone uses most. -/
theorem movedDigest_binds_of_noLeafColl (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (hC : compressInjective compress) (f g : CellId → Value) (src dst : CellId)
    (hno : ¬ MovedLeafColl CH f g src dst)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    f src = g src ∧ f dst = g dst := by
  rcases movedDigest_binds_or_collides CH compress f g src dst h with hok | hcn | hl
  · exact hok
  · exact absurd (hC _ _ _ _ hcn.2) hcn.1
  · exact absurd hl hno

/-! ### the frame sponge. -/

/-- The ORDERED leaf list the frame sponge absorbs — `frameDigest`'s argument, named so the
collision events can talk about it. -/
def frameLeaves (CH : CellId → Value → ℤ) (k : RecordKernelState) (S : Finset CellId) : List ℤ :=
  (S.sort (· ≤ ·)).map (fun c => CH c (k.cell c))

/-- `frameDigest` IS the sponge of `frameLeaves` (definitional). -/
theorem frameDigest_eq (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k : RecordKernelState) (S : Finset CellId) :
    frameDigest CH compressN k S = compressN (frameLeaves CH k S) := rfl

/-- **`FrameCNColl`** — the two ordered leaf lists are a GENUINE collision of the sponge. -/
def FrameCNColl (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k k' : RecordKernelState) (S : Finset CellId) : Prop :=
  frameLeaves CH k S ≠ frameLeaves CH k' S
    ∧ compressN (frameLeaves CH k S) = compressN (frameLeaves CH k' S)

/-- **`FrameLeafColl`** — some cell of the carrier `S` has distinct `Value`s with equal leaves: a
NAMED leaf collision, at a cell the predicate itself exhibits. -/
def FrameLeafColl (CH : CellId → Value → ℤ) (k k' : RecordKernelState) (S : Finset CellId) : Prop :=
  ∃ c ∈ S, CellLeafColl CH c (k.cell c) (k'.cell c)

/-- **`FrameColl`** — a `frameDigest` equivocation over `S` broke the sponge or the leaf hash. -/
def FrameColl (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k k' : RecordKernelState) (S : Finset CellId) : Prop :=
  FrameCNColl CH compressN k k' S ∨ FrameLeafColl CH k k' S

/-- The umbrella extraction for the frame side. -/
theorem FrameColl.extracts {CH : CellId → Value → ℤ} {compressN : List ℤ → ℤ}
    {k k' : RecordKernelState} {S : Finset CellId} (hc : FrameColl CH compressN k k' S) :
    (∃ xs ys : List ℤ, xs ≠ ys ∧ compressN xs = compressN ys)
      ∨ (∃ c : CellId, ∃ x y : Value, x ≠ y ∧ CH c x = CH c y) := by
  rcases hc with ⟨hne, heq⟩ | ⟨c, _, hl⟩
  · exact Or.inl ⟨_, _, hne, heq⟩
  · exact Or.inr ⟨c, hl.extracts⟩

/-- **⚑ THE HYPOTHESIS-FREE FRAME BINDING (`_or_collides`).** Equal frame digests over the SAME
sorted carrier force per-cell whole-`Value` equality on `S`, OR a named collision. This is the S2 of
`StateCommit.FrameDigestBindsCells`. -/
theorem frameDigest_binds_or_collides (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k k' : RecordKernelState) (S : Finset CellId)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    (∀ c ∈ S, k.cell c = k'.cell c) ∨ FrameColl CH compressN k k' S := by
  rw [frameDigest_eq, frameDigest_eq] at h
  by_cases hmap : frameLeaves CH k S = frameLeaves CH k' S
  · have hpt : ∀ c ∈ S.sort (· ≤ ·), CH c (k.cell c) = CH c (k'.cell c) :=
      List.map_inj_left.mp hmap
    by_cases hall : ∀ c ∈ S, k.cell c = k'.cell c
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨c, hc, hne⟩ := hall
      exact Or.inr (Or.inr ⟨c, hc, hne, hpt c ((Finset.mem_sort (· ≤ ·)).mpr hc)⟩)
  · exact Or.inr (Or.inl ⟨hmap, h⟩)

/-- **S3, both carriers floor-borne** — `FrameDigestBindsCells`'s conclusion with BOTH refuted
binders replaced by one refutable side condition. -/
theorem frameDigest_binds_of_noColl (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (k k' : RecordKernelState) (S : Finset CellId)
    (hno : ¬ FrameColl CH compressN k k' S)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c :=
  (frameDigest_binds_or_collides CH compressN k k' S h).resolve_right hno

/-- **S3, leaf-side only** — the variant the `cellLeafInjective` cutover uses: the sponge carrier
`compressNInjective` is RETAINED (it is a sibling floor with its own cone, ported separately), and
only the refuted LEAF universal is replaced by the per-instance `¬ FrameLeafColl`. -/
theorem frameDigest_binds_of_noLeafColl (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (hN : compressNInjective compressN) (k k' : RecordKernelState) (S : Finset CellId)
    (hno : ¬ FrameLeafColl CH k k' S)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c := by
  rcases frameDigest_binds_or_collides CH compressN k k' S h with hok | hcn | hl
  · exact hok
  · exact absurd (hN _ _ hcn.2) hcn.1
  · exact absurd hl hno

/-- **S3, sponge-side only** — the dual, for a site with a genuinely injective leaf encoder. -/
theorem frameDigest_binds_of_noCNColl (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (hL : cellLeafInjective CH) (k k' : RecordKernelState) (S : Finset CellId)
    (hno : ¬ FrameCNColl CH compressN k k' S)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c := by
  rcases frameDigest_binds_or_collides CH compressN k k' S h with hok | hcn | ⟨c, hc, hl⟩
  · exact hok
  · exact absurd hcn hno
  · exact absurd (hL c _ _ hl.2) hl.1

/-! ## §3b — THE WHOLE-CELL-MAP and WHOLE-KERNEL ports (the next cone level, unblocked).

`StateCommit.cellDigest_binds_cells` and `recStateCommit_binds_kernel` are the two endpoints the
`CommitSurface`/`S_live` bundle and the whole `Closure*` cluster stand on. They are ported here at
the LEAF floor: `compressInjective`/`compressNInjective` are RETAINED (sibling floors with their own
cones), and only the refuted `cellLeafInjective` universal is replaced by ONE per-instance side
condition naming both leaf points the proof actually visits. -/

/-- **`CellDigestLeafColl`** — a `cellDigest` equivocation broke the LEAF hash somewhere: at an
untouched frame cell, or at one of the two moved cells. Exactly the two leaf points
`cellDigest_binds_cells` feeds to `cellLeafInjective`. -/
def CellDigestLeafColl (CH : CellId → Value → ℤ) (k k' : RecordKernelState) (t : Turn) : Prop :=
  FrameLeafColl CH k k' (k.accounts \ {t.src, t.dst})
    ∨ MovedLeafColl CH k.cell k'.cell t.src t.dst

/-- **S3 of `StateCommit.cellDigest_binds_cells`.** Equal cell-digests (same turn, equal accounts,
both `AccountsWF`) force the WHOLE cell map equal, with the refuted leaf universal replaced by the
per-instance `¬ CellDigestLeafColl`. Conclusion byte-identical; the exhaustive
`{src} ∪ {dst} ∪ (accounts\{src,dst}) ∪ dead` partition is unchanged. -/
theorem cellDigest_binds_cells_of_noLeafColl (CH : CellId → Value → ℤ)
    (compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCompress : compressInjective compress) (hCompressN : compressNInjective compressN)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hAcc : k.accounts = k'.accounts)
    (hno : ¬ CellDigestLeafColl CH k k' t)
    (hcd : cellDigest CH compress compressN k t = cellDigest CH compress compressN k' t) :
    k.cell = k'.cell := by
  unfold cellDigest at hcd
  rw [← hAcc] at hcd
  obtain ⟨hframeEq, hmovedEq⟩ := hCompress _ _ _ _ hcd
  have hcellframe : ∀ c ∈ (k.accounts \ {t.src, t.dst}), k.cell c = k'.cell c :=
    frameDigest_binds_of_noLeafColl CH compressN hCompressN k k' (k.accounts \ {t.src, t.dst})
      (fun hc => hno (Or.inl hc)) hframeEq
  obtain ⟨hmsrc, hmdst⟩ :=
    movedDigest_binds_of_noLeafColl CH compress hCompress k.cell k'.cell t.src t.dst
      (fun hc => hno (Or.inr hc)) hmovedEq
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

/-- **S3 of `StateCommit.recStateCommit_binds_kernel`** — the WHOLE-KERNEL recovery, leaf floor
removed. This is the binding `CircuitSoundness.CommitSurface.commit_binds` repackages; porting the
`leafInj` FIELD of that bundle (⚑ the bundle is uninhabitable at deployed parameters — its four
injectivity fields are all refuted) is the next structural move, and this is the theorem it needs. -/
theorem recStateCommit_binds_kernel_of_noLeafColl (CH : CellId → Value → ℤ)
    (RH : RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hRest : RestHashIffFrame RH)
    (k k' : RecordKernelState) (t : Turn)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hno : ¬ CellDigestLeafColl CH k k' t)
    (hroot : recStateCommit CH RH cmb compress compressN k t
      = recStateCommit CH RH cmb compress compressN k' t) :
    k = k' := by
  obtain ⟨hcd, hRHeq⟩ := recStateCommit_binds CH RH cmb compress compressN hCmb k k' t hroot
  obtain ⟨hAcc, hCaps, hBal, hNul, hRev, hCom, hSC, hFac, hLif, hDC, hDel, hDgs, hDE, hDEA, hHeaps,
    hNR, hRR, hCR⟩ := (hRest k k').mp hRHeq
  have hcell : k.cell = k'.cell :=
    cellDigest_binds_cells_of_noLeafColl CH compress compressN hCompress hCompressN k k' t
      hwf hwf' hAcc.symm hno hcd
  cases k; cases k'
  simp_all

/-! ## §4 — NO STRENGTH LOST: each old endpoint is the injective special case of its port, and the
CUTOVER BRIDGES that make the remaining floor use UNIFORM.

After the in-place cutover a threader that STILL carries a refuted floor binder discharges its
callee's per-instance side condition through exactly one of these. That makes every not-yet-ported
consumer's floor flow into ONE bridge application, so the NEXT cone level is portable by ConePort
with a single bridge `AppRule` per bridge (`orig := no*Coll_of_inj`, `repl := no*Coll_self`), never
a per-theorem rule table. -/

/-- Node-side bridge: the (refuted) universal injectivity kills every per-instance `CompressColl`.
Instance args implicit so a rewired call site is exactly `(noCompressColl_of_inj hC)`. -/
theorem noCompressColl_of_inj {h : ℤ → ℤ → ℤ} (hC : compressInjective h) {a b c d : ℤ} :
    ¬ CompressColl h a b c d := fun hc => hc.1 (hC a b c d hc.2)

/-- Leaf-side bridge. -/
theorem noCellLeafColl_of_inj {CH : CellId → Value → ℤ} (hL : cellLeafInjective CH)
    {c : CellId} {v w : Value} : ¬ CellLeafColl CH c v w := fun hc => hc.1 (hL c v w hc.2)

/-- Moved-leaf bridge. -/
theorem noMovedLeafColl_of_inj {CH : CellId → Value → ℤ} (hL : cellLeafInjective CH)
    {f g : CellId → Value} {src dst : CellId} : ¬ MovedLeafColl CH f g src dst := by
  rintro (hl | hl)
  · exact hl.1 (hL src _ _ hl.2)
  · exact hl.1 (hL dst _ _ hl.2)

/-- Frame-leaf bridge. -/
theorem noFrameLeafColl_of_inj {CH : CellId → Value → ℤ} (hL : cellLeafInjective CH)
    {k k' : RecordKernelState} {S : Finset CellId} : ¬ FrameLeafColl CH k k' S := by
  rintro ⟨c, _, hl⟩
  exact hl.1 (hL c _ _ hl.2)

/-- Both moved carriers kill every `MovedColl` disjunct. -/
theorem noMovedColl_of_carriers {CH : CellId → Value → ℤ} {compress : ℤ → ℤ → ℤ}
    (hC : compressInjective compress) (hL : cellLeafInjective CH)
    {f g : CellId → Value} {src dst : CellId} : ¬ MovedColl CH compress f g src dst := by
  rintro (hn | hl)
  · exact hn.1 (hC _ _ _ _ hn.2)
  · exact noMovedLeafColl_of_inj hL hl

/-- Both frame carriers kill every `FrameColl` disjunct. -/
theorem noFrameColl_of_carriers {CH : CellId → Value → ℤ} {compressN : List ℤ → ℤ}
    (hN : compressNInjective compressN) (hL : cellLeafInjective CH)
    {k k' : RecordKernelState} {S : Finset CellId} : ¬ FrameColl CH compressN k k' S := by
  rintro (hn | hl)
  · exact hn.1 (hN _ _ hn.2)
  · exact noFrameLeafColl_of_inj hL hl

/-- **The deleted-shape bridge for the moved endpoint**: `MovedDigestBindsCells`'s exact statement,
re-derived THROUGH the port. Nothing genuinely proved was given up — only the pretence that the
deployed hash satisfies the injectivities. Deliberately a standalone bridge, never a hypothesis on
a keystone. -/
theorem movedDigest_binds_of_carriers (CH : CellId → Value → ℤ) (compress : ℤ → ℤ → ℤ)
    (hC : compressInjective compress) (hL : cellLeafInjective CH)
    (f g : CellId → Value) (src dst : CellId)
    (h : movedDigest CH compress f src dst = movedDigest CH compress g src dst) :
    f src = g src ∧ f dst = g dst :=
  movedDigest_binds_of_noColl CH compress f g src dst (noMovedColl_of_carriers hC hL) h

/-- The frame twin of `movedDigest_binds_of_carriers`. -/
theorem frameDigest_binds_of_carriers (CH : CellId → Value → ℤ) (compressN : List ℤ → ℤ)
    (hN : compressNInjective compressN) (hL : cellLeafInjective CH)
    (k k' : RecordKernelState) (S : Finset CellId)
    (h : frameDigest CH compressN k S = frameDigest CH compressN k' S) :
    ∀ c ∈ S, k.cell c = k'.cell c :=
  frameDigest_binds_of_noColl CH compressN k k' S (noFrameColl_of_carriers hN hL) h

/-- Both leaf points of a `cellDigest` equivocation die under the (refuted) leaf universal. -/
theorem noCellDigestLeafColl_of_inj {CH : CellId → Value → ℤ} (hL : cellLeafInjective CH)
    {k k' : RecordKernelState} {t : Turn} : ¬ CellDigestLeafColl CH k k' t := by
  rintro (hf | hm)
  · exact noFrameLeafColl_of_inj hL hf
  · exact noMovedLeafColl_of_inj hL hm

/-- The identity carrier for `CellDigestLeafColl`'s bridge. -/
theorem noCellDigestLeafColl_self {CH : CellId → Value → ℤ} {k k' : RecordKernelState} {t : Turn}
    (hno : ¬ CellDigestLeafColl CH k k' t) : ¬ CellDigestLeafColl CH k k' t := hno

/-- The identity carriers for the bridges' side conditions — the constant-headed replacements the
ConePort `AppRule` shape needs so a level-2 threader's `no*Coll_of_inj h` application can be
mechanically rewritten into a passed-through `hno` binder. -/
theorem noCompressColl_self {h : ℤ → ℤ → ℤ} {a b c d : ℤ}
    (hno : ¬ CompressColl h a b c d) : ¬ CompressColl h a b c d := hno

theorem noCellLeafColl_self {CH : CellId → Value → ℤ} {c : CellId} {v w : Value}
    (hno : ¬ CellLeafColl CH c v w) : ¬ CellLeafColl CH c v w := hno

theorem noMovedLeafColl_self {CH : CellId → Value → ℤ} {f g : CellId → Value} {src dst : CellId}
    (hno : ¬ MovedLeafColl CH f g src dst) : ¬ MovedLeafColl CH f g src dst := hno

theorem noMovedColl_self {CH : CellId → Value → ℤ} {compress : ℤ → ℤ → ℤ}
    {f g : CellId → Value} {src dst : CellId}
    (hno : ¬ MovedColl CH compress f g src dst) : ¬ MovedColl CH compress f g src dst := hno

theorem noFrameLeafColl_self {CH : CellId → Value → ℤ} {k k' : RecordKernelState}
    {S : Finset CellId} (hno : ¬ FrameLeafColl CH k k' S) : ¬ FrameLeafColl CH k k' S := hno

theorem noFrameColl_self {CH : CellId → Value → ℤ} {compressN : List ℤ → ℤ}
    {k k' : RecordKernelState} {S : Finset CellId}
    (hno : ¬ FrameColl CH compressN k k' S) : ¬ FrameColl CH compressN k k' S := hno

/-! ## §5 — TEETH: the ports are not vacuous, the side conditions are load-bearing, refutable, and
satisfiable. Concrete carriers: a positional 2-to-1 pairing (the deployed-shaped injective node) and
a CONSTANT hash as the refuted pole. -/

/-- A deployed-SHAPED node hash: positional, so distinct pairs land apart on small inputs. -/
private def demoNode : ℤ → ℤ → ℤ := fun a b => a * 1000000 + b

/-- The refuted pole: a constant node hash — every pair collides. -/
private def constNode : ℤ → ℤ → ℤ := fun _ _ => 0

/-- The refuted pole at the leaf: a constant leaf hash. -/
private def constLeaf : CellId → Value → ℤ := fun _ _ => 0

/-- **The node side condition is SATISFIABLE** at a deployed-shaped instance: no collision at these
two named argument pairs. (`¬ CompressColl` is not vacuously false.) -/
theorem noCompressColl_satisfiable : ¬ CompressColl demoNode 1 2 3 4 := by
  rintro ⟨-, heq⟩
  exact absurd heq (by decide)

/-- **The node collision predicate is REFUTABLE** — at a constant node hash the event FIRES. The new
predicate commits to something a bad instantiation genuinely violates. -/
theorem compressColl_refutable : CompressColl constNode 0 0 1 1 :=
  ⟨by decide, rfl⟩

/-- **The leaf collision predicate is REFUTABLE** — at a constant leaf hash two distinct `Value`s
collide at every cell. -/
theorem cellLeafColl_refutable : CellLeafColl constLeaf 0 (Value.int 0) (Value.int 1) :=
  ⟨by intro h; injection h with h; exact absurd h (by decide), rfl⟩

/-- **The moved collision predicate FIRES at the constant node hash** — the umbrella event is
reachable, so `¬ MovedColl` is a real commitment. -/
theorem movedColl_refutable :
    MovedColl constLeaf constNode (fun _ => Value.int 0) (fun _ => Value.int 1) 0 1 :=
  Or.inr (Or.inl ⟨by intro h; injection h with h; exact absurd h (by decide), rfl⟩)

/-- **⚑ THE NODE SIDE CONDITION IS LOAD-BEARING** — the S3 node statement with `hno` DELETED is
FALSE (at a constant node hash every pair collides). A port that dropped the side condition would
not be a port; it would be refuted. This is the mutation canary for the whole `CompressColl`
family. -/
theorem compress_binds_unconditional_false :
    ¬ ∀ a b c d : ℤ, constNode a b = constNode c d → a = c ∧ b = d := by
  intro hall
  exact absurd (hall 0 0 1 1 rfl).1 (by decide)

/-- **⚑ THE MOVED SIDE CONDITION IS LOAD-BEARING** — `movedDigest_binds_of_noColl` with `hno`
DELETED is FALSE at the constant leaf/node pair: the digests agree while the cells differ. The
mutation canary for the `MovedColl` family. -/
theorem movedDigest_unconditional_false :
    ¬ ∀ (f g : CellId → Value) (src dst : CellId),
        movedDigest constLeaf constNode f src dst = movedDigest constLeaf constNode g src dst →
        f src = g src ∧ f dst = g dst := by
  intro hall
  have h := (hall (fun _ => Value.int 0) (fun _ => Value.int 1) 0 1 rfl).1
  injection h with h
  exact absurd h (by decide)

/-- **⚑ THE LEFT DISJUNCT BITES.** At named points where no collision is available, S2 forces the
moved digests APART — the gate genuinely rejects a tampered cell, with no injectivity floor anywhere
in the argument. (The leaf hash here is the deployed-shaped `Value.int`-projection; the node hash is
the positional pairing.) -/
private def demoLeaf : CellId → Value → ℤ := fun _ v => match v with
  | .int n => n
  | .dig n => (n : ℤ) + 1000
  | .sym n => (n : ℤ) + 2000
  | .record _ => 3000

theorem canary_moved_tamper_moves_digest_or_collides :
    movedDigest demoLeaf demoNode (fun _ => Value.int 0) 0 1
      ≠ movedDigest demoLeaf demoNode (fun _ => Value.int 1) 0 1 := by
  intro h
  rcases movedDigest_binds_or_collides demoLeaf demoNode _ _ 0 1 h with ⟨hs, -⟩ | hcoll
  · injection hs with hs; exact absurd hs (by decide)
  · rcases hcoll with ⟨-, heq⟩ | (⟨-, heq⟩ | ⟨-, heq⟩) <;>
      exact absurd heq (by decide)

/-! ## §6 — kernel pins. -/

#assert_all_clean [compress_binds_or_collides, cellLeaf_binds_or_collides,
  compress_binds_of_noColl, cellLeaf_binds_of_noColl,
  movedDigest_binds_or_collides, movedDigest_binds_of_noColl,
  movedDigest_binds_of_noCompressColl, movedDigest_binds_of_noLeafColl,
  frameDigest_binds_or_collides, frameDigest_binds_of_noColl,
  frameDigest_binds_of_noLeafColl, frameDigest_binds_of_noCNColl,
  movedDigest_binds_of_carriers, frameDigest_binds_of_carriers,
  cellDigest_binds_cells_of_noLeafColl, recStateCommit_binds_kernel_of_noLeafColl,
  noCompressColl_of_inj, noCellLeafColl_of_inj, noMovedLeafColl_of_inj, noFrameLeafColl_of_inj,
  noMovedColl_of_carriers, noFrameColl_of_carriers, noCellDigestLeafColl_of_inj,
  CompressColl.extracts, CellLeafColl.extracts, MovedColl.extracts, FrameColl.extracts,
  noCompressColl_satisfiable, compressColl_refutable, cellLeafColl_refutable, movedColl_refutable,
  compress_binds_unconditional_false, movedDigest_unconditional_false,
  canary_moved_tamper_moves_digest_or_collides]

end Dregg2.Circuit.StateCommitLeafRegrounded
