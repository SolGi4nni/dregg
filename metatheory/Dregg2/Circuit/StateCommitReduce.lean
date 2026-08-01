/-
# Dregg2.Circuit.StateCommitReduce — the DECODE-level twins of the state-commitment binding chain.

The raw (surface-free) layers of this reduction moved to `Dregg2.Circuit.StateCommitReduceRaw` on
2026-08-01 so they sit BELOW `CircuitSoundness` and the apex path can consume them; the
`CommitSurface` view (`CommitSurface.CommitColl`, `CommitSurface.commit_binds_of_noColl`) is in
`CircuitSoundness` beside the surface it is about. Read `StateCommitReduceRaw`'s header for the
campaign and the bottom-up chain (layers 1–5); this module carries only what needs BOTH the raw
chain and `StateDecode`:

  7. `stateDecode_pre/post_faithful_or_collides` (UNCONDITIONAL) and
     `stateDecode_pre/post_faithful_of_noColl` (the S3 form) — twins of the (now deleted) injective
     `CircuitSoundness.stateDecode_*_faithful`: two decodes of the same published commitment have
     equal kernels, or the NAMED residual `S.CommitColl` holds at exactly those two kernels.

⚑ **PORTED 2026-08-01 (second pass).** These were `stateDecode_*_faithful_orBreak`, concluding
`OrBreak S.StateBreak (…)`. `S.StateBreak`'s sponge disjunct is a GLOBAL collision existential, which
pigeonhole supplies at every BabyBear-bounded sponge, so that dichotomy is literally `True` at
deployed parameters (`CommitSurface.orBreak_stateBreak_iff_True`) and the good branch carried nothing.
The per-instance residual names a PAIR and therefore discriminates.

The twins take the surface `S` only for its five primitive CARRIERS + `restFrame` (the rest-hash
frame iff, which is not a hash-collision event). No injectivity hypothesis appears anywhere.
-/
import Dregg2.Circuit.StateCommitReduceRaw
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.StateCommitReduce

open Dregg2.Circuit
open Dregg2.Exec
open Dregg2.Circuit.CollisionReduce
open Dregg2.Circuit.StateCommit
open Dregg2.Circuit.RestFrameFin (FiniteRepresentable RestHashIffFrameFin)
open Dregg2.Circuit.CircuitSoundness (CommitSurface PublishedCommit StateDecode)

/-! ## §5 — the decode-level twins.

`CommitSurface.CommitColl` and `CommitSurface.commit_binds_of_noColl` are defined in
`CircuitSoundness` (they are about the surface, and its own in-module bindings consume them). These
two lift that binding through `StateDecode`. -/

/-- **⚑ UNCONDITIONAL** — two pre-states decoding the SAME published commitment have EQUAL kernels, OR
the NAMED residual `S.CommitColl` holds at exactly those two kernels. No hypothesis on `S`'s hashes. -/
theorem stateDecode_pre_faithful_or_collides (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable pre.kernel) (hfin' : FiniteRepresentable pre'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    pre.kernel = pre'.kernel ∨ S.CommitColl pre.kernel pre'.kernel pc.turn :=
  S.commit_binds_or_collides pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hfin hfin'
    (h.preBinds ▸ h'.preBinds ▸ rfl)

/-- **Twin of the deleted `stateDecode_pre_faithful`.** Two pre-states decoding the SAME published
commitment have EQUAL kernels. Pure commitment binding, no admissibility, NO injectivity — the crypto
reliance is the per-instance `hno` at the two named kernels.

⚑ Was `stateDecode_pre_faithful_orBreak`, whose `OrBreak S.StateBreak` disjunct is FREE at every
deployed-shaped surface (`CommitSurface.orBreak_stateBreak_iff_True`), so it asserted nothing. -/
theorem stateDecode_pre_faithful_of_noColl (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable pre.kernel) (hfin' : FiniteRepresentable pre'.kernel)
    (hno : ¬ S.CommitColl pre.kernel pre'.kernel pc.turn)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    pre.kernel = pre'.kernel :=
  (stateDecode_pre_faithful_or_collides S pc hfin hfin' h h').resolve_right hno

/-- **⚑ UNCONDITIONAL**, post twin. -/
theorem stateDecode_post_faithful_or_collides (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable post.kernel) (hfin' : FiniteRepresentable post'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    post.kernel = post'.kernel ∨ S.CommitColl post.kernel post'.kernel pc.turn :=
  S.commit_binds_or_collides post.kernel post'.kernel pc.turn h.postWF h'.postWF hfin hfin'
    (h.postBinds ▸ h'.postBinds ▸ rfl)

/-- **Twin of the deleted `stateDecode_post_faithful`.** -/
theorem stateDecode_post_faithful_of_noColl (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable post.kernel) (hfin' : FiniteRepresentable post'.kernel)
    (hno : ¬ S.CommitColl post.kernel post'.kernel pc.turn)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    post.kernel = post'.kernel :=
  (stateDecode_post_faithful_or_collides S pc hfin hfin' h h').resolve_right hno

/-! ## §6 — ⚰ TOMBSTONE: the `resolve`-recovery layer (DELETED 2026-08-01).

Three declarations lived here and are gone:

  * `surface_no_stateBreak (S : CommitSurface) : ¬ StateBreak S` — proved the surface's own bundled
    injectivity refutes its own break, by consuming `S.compNInj`/`S.cmbInj`/`S.compInj`/`S.leafInj`.
    It was the ONLY place in the tree those four fields were used AS INJECTIVITY, and all four are
    FALSE at deployed parameters (`Verify/ApexPremiseVacuity.lean:177` — injectivity of a
    compressing map into one BabyBear felt is refuted by pigeonhole). So the theorem was not a
    non-vacuity argument, it was the vacuity: it "refuted" the break using premises no deployed
    surface satisfies. The four fields are DELETED from `CommitSurface` as of the same commit.
  * `commit_binds_of_no_stateBreak` — `¬ StateBreak S → (equal commits ⟹ equal kernels)`.
    `¬ StateBreak S` is FALSE at deployed width for the same pigeonhole reason, so hypothesising it
    re-introduces exactly the vacuity these twins exist to remove. Consume
    `CommitSurface.commit_binds_of_noColl` and discharge the per-instance residual.
  * `commit_binds_recovered` — the composition of the two, re-deriving the deleted
    `CommitSurface.commit_binds` from its own refuted fields.

The RAW recovery lemma `StateCommitReduceRaw.recStateCommit_binds_kernel_of_no_break` survives with
the same warning attached: it demonstrates the twin subsumes the original, and nothing on the apex
path may consume it.

The FIRE direction (`fire_break_caught` — the twin forced into the break branch at the lossy `+`
hash) moved to `StateCommitReduceRaw` §7 with the raw layers it instantiates. -/

/-! ## §8 — axiom hygiene. -/

#assert_axioms stateDecode_pre_faithful_or_collides
#assert_axioms stateDecode_post_faithful_or_collides
#assert_axioms stateDecode_pre_faithful_of_noColl
#assert_axioms stateDecode_post_faithful_of_noColl

end Dregg2.Circuit.StateCommitReduce
