/-
# Dregg2.Circuit.StateCommitReduce — the DECODE-level twins of the state-commitment binding chain.

The raw (surface-free) layers of this reduction moved to `Dregg2.Circuit.StateCommitReduceRaw` on
2026-08-01 so they sit BELOW `CircuitSoundness` and the apex path can consume them; the
`CommitSurface` view (`CommitSurface.StateBreak`, `CommitSurface.commit_binds_orBreak`) is in
`CircuitSoundness` beside the surface it is about. Read `StateCommitReduceRaw`'s header for the
campaign and the bottom-up chain (layers 1–5); this module carries only what needs BOTH the raw
chain and `StateDecode`:

  7. `stateDecode_pre/post_faithful_orBreak` — twins of the (now deleted) injective
     `CircuitSoundness.stateDecode_*_faithful`: two decodes of the same published commitment have
     equal kernels, or a concrete `StateBreak`.

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

`CommitSurface.StateBreak` and `CommitSurface.commit_binds_orBreak` are defined in
`CircuitSoundness` (they are about the surface, and its own in-module bindings consume them). These
two lift that binding through `StateDecode`. -/

/-- **Twin of the deleted `stateDecode_pre_faithful`.** Two pre-states decoding the SAME published
commitment have EQUAL kernels — or a concrete `StateBreak`. Pure commitment binding, no
admissibility, NO injectivity. -/
theorem stateDecode_pre_faithful_orBreak (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable pre.kernel) (hfin' : FiniteRepresentable pre'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    OrBreak S.StateBreak (pre.kernel = pre'.kernel) :=
  S.commit_binds_orBreak pre.kernel pre'.kernel pc.turn h.preWF h'.preWF hfin hfin'
    (h.preBinds ▸ h'.preBinds ▸ rfl)

/-- **Twin of the deleted `stateDecode_post_faithful`.** Two post-states decoding the SAME published
commitment have EQUAL kernels — or a concrete `StateBreak`. -/
theorem stateDecode_post_faithful_orBreak (S : CommitSurface) (pc : PublishedCommit)
    {pre post pre' post' : RecChainedState}
    (hfin : FiniteRepresentable post.kernel) (hfin' : FiniteRepresentable post'.kernel)
    (h : StateDecode S pc pre post) (h' : StateDecode S pc pre' post') :
    OrBreak S.StateBreak (post.kernel = post'.kernel) :=
  S.commit_binds_orBreak post.kernel post'.kernel pc.turn h.postWF h'.postWF hfin hfin'
    (h.postBinds ▸ h'.postBinds ▸ rfl)

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
    re-introduces exactly the vacuity the `_orBreak` twins exist to remove. Consume
    `CommitSurface.commit_binds_orBreak` and handle the break disjunct.
  * `commit_binds_recovered` — the composition of the two, re-deriving the deleted
    `CommitSurface.commit_binds` from its own refuted fields.

The RAW recovery lemma `StateCommitReduceRaw.recStateCommit_binds_kernel_of_no_break` survives with
the same warning attached: it demonstrates the twin subsumes the original, and nothing on the apex
path may consume it.

The FIRE direction (`fire_break_caught` — the twin forced into the break branch at the lossy `+`
hash) moved to `StateCommitReduceRaw` §7 with the raw layers it instantiates. -/

/-! ## §8 — axiom hygiene. -/

#assert_axioms stateDecode_pre_faithful_orBreak
#assert_axioms stateDecode_post_faithful_orBreak

end Dregg2.Circuit.StateCommitReduce
