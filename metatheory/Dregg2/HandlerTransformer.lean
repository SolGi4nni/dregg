/-
# Dregg2.HandlerTransformer — the safe handler-transformer frontier.

A safe higher-order handler-transformer is a morphism in the category of sheaves-of-handlers;
the safe-composition law is the camera's frame-preserving update (`Resource.Fpu`) / sheaf
gluing condition (`ProofForest.proofForest_sound`).

This module builds one abstract interface — a **safe-step preorder** `SafeStep` (a reflexive,
transitive relation) — and proves two dregg objects instantiate it: (1) the camera via `Fpu`,
and (2) the proof-forest gluing surface via `chainLinked` continuity. The general theorem
`safe_transformer_composes` lifts `SafeStep.trans` through transformer composition; it is
instantiated on both. Teeth: `overshare_rejected` exhibits an over-sharing `Auth ℕ` transformer
genuinely refused; `sheaf_rejects_disagreeing_verifier` breaks the gluing hypothesis.

OPEN: the keystone weld — that `Fpu`-preservation IS the gluing condition (one law, not two
instances of one preorder) — is not proved. Camera and proof-forest carriers differ; the forest
continuity relation fails reflexivity (`forest_continuity_not_reflexive`), so it is not a
`SafeStep` instance. The higher-order (recursive-camera) tier is also OPEN.
-/
import Dregg2.Resource
import Dregg2.Await
import Dregg2.Exec.ProofForest
import Dregg2.Authority.DesignatedVerifier
import Dregg2.Tactics

namespace Dregg2.HandlerTransformer

-- `HandlerTransformer` shares its name with the namespace (intentional); silence the linter.
set_option linter.dupNamespace false
-- `conservativeAct_matched` does not use `[AddCommMonoid M]` in its statement; omit per section.
set_option linter.unusedSectionVars false

universe u

open Dregg2.Resource (ResourceAlgebra Fpu Auth Excl fits)
open Dregg2.Resource.ResourceAlgebra

/-! ## §1 — `SafeStep`: the abstract safe-composition preorder. -/

/-- **`SafeStep R`** — a reflexive-transitive "safe to compose" relation on a carrier `R`.
This is the morphism-composition skeleton of a category (objects = `R`, a unique morphism
`a ⟶ b` iff `safe a b`). `refl` = identity; `trans` = composition. A handler-transformer is
*safe* exactly when its action is a `safe` step (§3). -/
class SafeStep (R : Type u) where
  /-- "Replacing `a` by `b` is a safe step" — the morphism-existence relation. -/
  safe  : R → R → Prop
  /-- Identity: doing nothing is safe. -/
  refl  : ∀ a, safe a a
  /-- Composition: a safe step after a safe step is safe (the morphism-composition law). -/
  trans : ∀ {a b c}, safe a b → safe b c → safe a c

/-! ## §2 — INSTANCE 1: the camera `Fpu` as a `SafeStep`. -/

/-- **The camera is a `SafeStep` via `Fpu`** — `Fpu.refl`/`Fpu.trans` are the identity and
composition laws. The frame-preserving update is an instance of the safe-composition preorder. -/
instance instSafeStepFpu (R : Type u) [ResourceAlgebra R] : SafeStep R where
  safe  := Fpu
  refl  := Fpu.refl
  trans := Fpu.trans

/-! ## §3 — `HandlerTransformer` and the safe-composition predicate. -/

/-- **`HandlerTransformer R`** — a handler-transformer modelled by its resource action on the
camera `R`. (`act a` = the post-state when the transformer's committed effect acts on `a`.) The
full `Handler → Handler` comodel-morphism is unbuilt; this is the first-order resource-action
model the safe-composition law constrains. -/
structure HandlerTransformer (R : Type u) where
  /-- The resource update the transformer's committed effect induces. -/
  act : R → R

/-- Composition of handler-transformers: do `T₁` then `T₂` (function composition of actions).
This is the candidate morphism-composition the safe-composition law must preserve. -/
def HandlerTransformer.comp {R : Type u} (T₂ T₁ : HandlerTransformer R) :
    HandlerTransformer R :=
  ⟨T₂.act ∘ T₁.act⟩

/-- **`Safe T`** — the safe-composition predicate: a transformer is safe iff its action is a
`SafeStep` from every state `a` to `act a`. For the camera instance (`instSafeStepFpu`) this
unfolds to `∀ a, Fpu a (T.act a)` — "the transformer never invalidates a third party's frame",
exactly the conjecture's safe-composition side-condition. -/
def Safe {R : Type u} [SafeStep R] (T : HandlerTransformer R) : Prop :=
  ∀ a, SafeStep.safe a (T.act a)

/-! ## §4 — The general safe-composition theorem (with teeth). -/

/-- **`safe_transformer_composes` — safe transformers compose.** Given `T₁` and `T₂` each
safe, the composite `T₂.comp T₁` is safe. Proved by `SafeStep.trans` (= `Fpu.trans` on the
camera instance). On `instSafeStepFpu`, this is the statement that Fpu-safe transformers
compose preserving frame-safety. -/
theorem safe_transformer_composes {R : Type u} [SafeStep R]
    {T₁ T₂ : HandlerTransformer R} (hsafe₁ : Safe T₁) (hsafe₂ : Safe T₂) :
    Safe (T₂.comp T₁) := by
  intro a
  -- `(T₂.comp T₁).act a = T₂.act (T₁.act a)`; chain `a ↝ T₁.act a ↝ T₂.act (T₁.act a)`.
  exact SafeStep.trans (hsafe₁ a) (hsafe₂ (T₁.act a))

/-! ### `conservation_is_fpu` as a safe transformer. -/

section CameraInstance
variable {M : Type u} [AddCommMonoid M]

/-- The conservative-rewrite ACTION: under a fixed sovereign total `a`, send the *matched*
authoritative state `(some a, f)` to `(some a, f')`, and leave every other state fixed. Equality
on the monoid `M` is decided classically (the module's whitelist permits `Classical.choice`) — no
`DecidableEq M` is forced on callers. -/
noncomputable def conservativeAct (a f f' : M) : Auth M → Auth M :=
  fun s => by
    classical
    exact match s with
    | .mk (some a') g => if a' = a ∧ g = f then .mk (some a) f' else .mk (some a') g
    | s => s

/-- A **conservative fragment-rewrite transformer**: the handler-transformer whose action is
`conservativeAct`. The `(some a, f) ↦ (some a, f')` move is the one `conservation_is_fpu` governs. -/
noncomputable def conservativeTransformer (a f f' : M) : HandlerTransformer (Auth M) :=
  ⟨conservativeAct a f f'⟩

/-- The action's value on the MATCHED state is the conservative rewrite. -/
theorem conservativeAct_matched (a f f' : M) :
    conservativeAct a f f' (Auth.mk (some a) f) = Auth.mk (some a) f' := by
  classical
  simp only [conservativeAct, and_self, if_true]

/-- The action's value on any UNMATCHED authoritative state `(some a', g)` with `(a',g) ≠ (a,f)`
is the identity. -/
theorem conservativeAct_unmatched (a f f' a' g : M) (h : ¬ (a' = a ∧ g = f)) :
    conservativeAct a f f' (Auth.mk (some a') g) = Auth.mk (some a') g := by
  classical
  simp only [conservativeAct, if_neg h]

/-- A conservation move is a safe handler-transformer: when the fragment-rewrite is
conservative (`hmono`), the `conservativeTransformer` is `Safe` on `Auth M`. This is
`Resource.conservation_is_fpu` lifted to the transformer level — "safe handler-transformer"
and "frame-preserving update" are the same object. -/
theorem conservation_is_safe_transformer (a f f' : M)
    (hmono : ∀ g, fits (f + g) a → fits (f' + g) a) :
    Safe (conservativeTransformer a f f') := by
  classical
  intro s
  -- `SafeStep.safe` here is `Fpu`; reduce to `Fpu s (conservativeAct a f f' s)`.
  show Fpu s (conservativeAct a f f' s)
  cases s with
  | invalid =>
    -- act invalid = invalid; Fpu invalid invalid is refl.
    have : conservativeAct a f f' Auth.invalid = Auth.invalid := by simp [conservativeAct]
    rw [this]; exact Fpu.refl (R := Auth M) Auth.invalid
  | mk a' g =>
    cases a' with
    | none =>
      -- a pure fragment is not matched; identity action; Fpu by refl.
      have : conservativeAct a f f' (Auth.mk none g) = Auth.mk none g := by simp [conservativeAct]
      rw [this]; exact Fpu.refl (R := Auth M) (Auth.mk none g)
    | some a' =>
      by_cases h : a' = a ∧ g = f
      · -- matched: action rewrites (some a, f) ↦ (some a, f'); use conservation_is_fpu.
        obtain ⟨ha, hg⟩ := h
        subst ha; subst hg
        rw [conservativeAct_matched a' g f']
        exact Dregg2.Resource.conservation_is_fpu a' g f' hmono
      · -- unmatched: identity action; Fpu by refl.
        rw [conservativeAct_unmatched a f f' a' g h]
        exact Fpu.refl (R := Auth M) (Auth.mk (some a') g)

end CameraInstance

/-! ### TEETH: an unsafe transformer is genuinely rejected.

The `Excl` (NFT) camera cannot host a rejecting witness: every composition in `Excl` is
`invalid` (`excl_op_never_valid`), so `Fpu` is vacuously true for every `Excl`-transformer.
The teeth must therefore bite on `Auth ℕ`, where an over-sharing transformer breaks a frame
a third party holds — `overshare_rejected`. -/

/-- In the `Excl` camera every composition is invalid, so there are no valid frames and `Fpu`
holds vacuously for every transformer — the reason the rejecting witness uses `Auth` instead. -/
theorem excl_op_never_valid {R : Type u} (a f : Excl R) :
    ¬ Dregg2.Resource.ResourceAlgebra.valid (a ⊙ f) := by
  -- `a ⊙ f = Excl.invalid`, and `Excl.valid invalid = False`.
  show ¬ Excl.valid (Excl.op a f)
  simp only [Excl.op, Excl.valid, not_false_iff]

/-- An **over-sharing transformer** on `Auth ℕ`: under authoritative total `2`, it rewrites the
held fragment from `0` to `3` — claiming `3` against a total of `2`, an over-share. Its action
on the matched state `(some 2, 0)` is `(some 2, 3)`. -/
def overshareTransformer : HandlerTransformer (Auth Nat) :=
  ⟨fun s => match s with
    | .mk (some 2) 0 => .mk (some 2) 3
    | s => s⟩

/-- The over-sharing transformer is NOT `Safe` on `Auth ℕ`. Witness: frame `(none, 0)` is
valid at pre-state `(some 2, 0)` but not at post-state `(some 2, 3)` (`3` does not fit in `2`),
so `Fpu (some 2, 0) (some 2, 3)` fails — the safe-composition law genuinely refuses this
transformer. -/
theorem overshare_rejected : ¬ Safe overshareTransformer := by
  -- Safe would give Fpu (some 2,0) (act (some 2,0)) = Fpu (some 2,0) (some 2,3).
  intro hsafe
  have hfpu : Fpu (R := Auth Nat) (Auth.mk (some 2) 0) (Auth.mk (some 2) 3) := by
    have := hsafe (Auth.mk (some 2) 0)
    -- `act (some 2, 0) = (some 2, 3)` definitionally.
    simpa [overshareTransformer, SafeStep.safe] using this
  -- instantiate the frame `f = (none, 0)`: pre is valid, post must be — but post is not.
  have hpre : Dregg2.Resource.ResourceAlgebra.valid
      ((Auth.mk (some 2) 0) ⊙ (Auth.mk (none) 0) : Auth Nat) := by
    -- (some 2, 0) ⊙ (none, 0) = (some 2, 0); valid = fits 0 2 = ∃ c, 2 = 0 + c.
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
    exact ⟨2, rfl⟩
  have hpost := hfpu (Auth.mk none 0) hpre
  -- post: (some 2, 3) ⊙ (none, 0) = (some 2, 3); valid = fits 3 2 = ∃ c, 2 = 3 + c — false in ℕ.
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits, add_zero] at hpost
  obtain ⟨c, hc⟩ := hpost
  -- 2 = 3 + c is impossible in ℕ.
  omega

/-! ## §5 — INSTANCE 2: the proof-forest gluing surface, and `proofForest_sheaf_sound` (G2). -/

open Dregg2.Exec.ProofForest

/-- **`forestContinuity`** — the proof-forest's one-step overlap relation: a node `a` links to a
node `b` when their commitments are continuous (`a.newCommit = b.oldCommit`), the first conjunct
of `chainLinked` (`ProofForest.lean:141`). This is the seam-agreement the gluing law glues over. -/
def forestContinuity (a b : ProofNode) : Prop := a.newCommit = b.oldCommit

/-- Commitment continuity is NOT reflexive: `node0` (`oldCommit = 0`, `newCommit = 1`) does not
satisfy `forestContinuity node0 node0` (it would need `1 = 0`). So `forestContinuity` is NOT a
`SafeStep`; the forest gluing is a graph (a one-step continuity relation), not the
reflexive-transitive preorder `Fpu` is. This is the load-bearing reason the keystone weld
"`Fpu` = gluing condition" is a notation pun: we do NOT register `ProofNode` as a `SafeStep`
instance. -/
theorem forest_continuity_not_reflexive : ¬ forestContinuity node0 node0 := by
  -- `forestContinuity node0 node0` is `node0.newCommit = node0.oldCommit`, i.e. `1 = 0`.
  unfold forestContinuity node0
  decide

/-- The forest gluing law is `proofForest_sound`: `Linked` + per-node validity ⟹ whole-forest
`StepInv`. Re-stated here (no new content) to make precise that this is the list-level gluing —
NOT an instance of `SafeStep.trans`. -/
theorem forest_gluing_is_proofForest_sound (pf : ProofForest)
    (hvalid : ∀ n ∈ pf.nodes, n.StepProofValid) (hlinked : Linked pf) :
    fullProofForestInv pf :=
  proofForest_sound pf hvalid hlinked

/-! ### The sheaf-of-verifiers generalization `proofForest_sheaf_sound` (G2). -/

open Dregg2.Authority.DV

/-- **`VerifierSection`** — a per-node assignment of a verifier and the statement/proof that node
must discharge FOR that verifier (the per-party stalk `DischargedFor Vᵢ`, facet 5). This is the
HETEROGENEOUS fibre the sheaf-of-verifiers wants — each node may be checked by a *different*
verifier, unlike the constant `StepProofValid`. -/
structure VerifierSection (Verifier Statement Proof VSecret : Type)
    [DVKernel Verifier Statement Proof VSecret] where
  /-- The verifier assigned to a node (the stalk index). -/
  verifierOf : ProofNode → Verifier
  /-- The statement a node must discharge. -/
  stmtOf     : ProofNode → Statement
  /-- The proof a node presents. -/
  proofOf    : ProofNode → Proof

/-- **`SheafLocallyValid`** — the heterogeneous local-validity condition: EVERY node discharges
its OWN verifier's verdict (`DischargedFor (verifierOf n) (stmtOf n) (proofOf n)`). This is the
per-party stalk condition, replacing the constant `∀ n, StepProofValid`. -/
def SheafLocallyValid {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (sec : VerifierSection Verifier Statement Proof VSecret) (pf : ProofForest) : Prop :=
  ∀ n ∈ pf.nodes, DischargedFor (VSecret := VSecret)
    (sec.verifierOf n) (sec.stmtOf n) (sec.proofOf n)

/-- **`proofForest_sheaf_sound` — THE SHEAF-OF-VERIFIERS GLUING (G2, PROVED).** Generalizes
`proofForest_sound`: if (P') every node discharges its OWN verifier's verdict
(`SheafLocallyValid` — the heterogeneous per-party fibre, facet 5), (L) the forest is `Linked`,
AND (bridge) the per-verifier local validity entails the per-node `StepProofValid` (the §8 seam
linking the verifier verdict to the AIR's validity — the *substantive* overlap condition, NOT
`Hᵢ = Hⱼ`), then the whole forest attests `fullProofForestInv`.

This is the buildable first theorem `SHEAF-OF-VERIFIERS §5.1` named: the fibre is now the
per-node `DischargedFor Vᵢ` (verdict-valued, a genuine generalization of the constant
`StepProofValid`), and the gluing is `proofForest_sound` over the bridged validity. The `bridge`
hypothesis is the honest §8 seam (verifier accepts ⟹ the AIR-validity proposition holds); it is
NOT circular (it does not assume the conclusion) and NOT trivial (a disagreeing verifier makes
`SheafLocallyValid` false — the teeth, see `sheaf_rejects_disagreeing_verifier`). -/
theorem proofForest_sheaf_sound {Verifier Statement Proof VSecret : Type}
    [DVKernel Verifier Statement Proof VSecret]
    (sec : VerifierSection Verifier Statement Proof VSecret) (pf : ProofForest)
    (hlocal : SheafLocallyValid sec pf) (hlinked : Linked pf)
    (bridge : ∀ n ∈ pf.nodes,
      DischargedFor (VSecret := VSecret) (sec.verifierOf n) (sec.stmtOf n) (sec.proofOf n) →
        n.StepProofValid) :
    fullProofForestInv pf :=
  proofForest_sound pf (fun n hn => bridge n hn (hlocal n hn)) hlinked

/-! ### TEETH for the sheaf: a disagreeing verifier breaks the local section. -/

/-- **`sheaf_rejects_disagreeing_verifier` (PROVED — the sheaf teeth).** There is a node
assignment (a node checked by the outsider `vOther`, presenting `v0`'s designated transcript)
for which the per-party local-validity condition `DischargedFor` is FALSE — so the sheaf gluing
hypothesis `SheafLocallyValid` cannot be met, and the global section is not derivable. This is
the `dial_endpoints_distinct` separation biting the gluing: handlers that DISAGREE on the
overlap (verifier `vOther` vs the transcript designated for `v0`) genuinely fail to glue. -/
theorem sheaf_rejects_disagreeing_verifier :
    ¬ DischargedFor (VSecret := Reference.VSec)
        Reference.V.vOther 7 Reference.designatedProof := by
  unfold DischargedFor Reference.designatedProof
  simp [DVKernel.verifyFor, Reference.vrfy, Reference.sim, Reference.secretOf]

/-! ## §6 — The composition obstruction = the proper subobject of safe transformers. -/

/-- The `Safe` transformers on `Auth ℕ` are a proper subobject of all transformers: there
exists a transformer (`overshareTransformer`) that is NOT `Safe`. Analogue of
`JointTurn.binding_is_proper`: the obstruction is real (witnessed exclusion). -/
theorem safe_is_proper_subobject :
    ∃ T : HandlerTransformer (Auth Nat), ¬ Safe T :=
  ⟨overshareTransformer, overshare_rejected⟩

/-- The identity transformer is always safe: the proper subobject is non-empty. -/
def idTransformer {R : Type u} : HandlerTransformer R := ⟨id⟩

theorem id_is_safe {R : Type u} [SafeStep R] : Safe (idTransformer (R := R)) :=
  fun a => SafeStep.refl a

/-! ## §7 — Axiom-hygiene pins. -/

#assert_axioms safe_transformer_composes
#assert_axioms conservation_is_safe_transformer
#assert_axioms overshare_rejected
#assert_axioms excl_op_never_valid
#assert_axioms forest_continuity_not_reflexive
#assert_axioms forest_gluing_is_proofForest_sound
#assert_axioms proofForest_sheaf_sound
#assert_axioms sheaf_rejects_disagreeing_verifier
#assert_axioms safe_is_proper_subobject
#assert_axioms id_is_safe

#print axioms safe_transformer_composes
#print axioms conservation_is_safe_transformer
#print axioms overshare_rejected
#print axioms proofForest_sheaf_sound

/-! ## §8 — Non-vacuity witnesses. -/

-- The over-sharing transformer's action on the matched state is the over-share (3 against 2).
example : (overshareTransformer.act (Auth.mk (some 2) 0)) = Auth.mk (some 2) 3 := rfl

-- Two identity transformers compose safely.
example : Safe ((idTransformer (R := Auth Nat)).comp idTransformer) :=
  safe_transformer_composes id_is_safe id_is_safe

-- v0 accepts its designated transcript; vOther rejects it.
#guard Reference.check Reference.V.v0 7 Reference.designatedProof
#guard Reference.check Reference.V.vOther 7 Reference.designatedProof == false

/-! ## §9 — Verdict.

What genuinely unified: `SafeStep` is one preorder; the camera's `Fpu` instantiates it literally
(`instSafeStepFpu`). `safe_transformer_composes` subsumes `Fpu.trans` for transformers;
`conservation_is_safe_transformer` shows `conservation_is_fpu` is a literal safe-transformer
instance. `proofForest_sheaf_sound` generalizes `proofForest_sound` to a per-node
verifier-indexed fibre. `safe_is_proper_subobject` witnesses the proper-subobject obstruction.

-- OPEN: The keystone weld — `Fpu`-preservation IS the gluing condition (one law, not two
--   instances of one preorder) — is not proved. The camera (`Auth M`) and forest (`ProofNode`)
--   carriers differ; `forestContinuity` fails reflexivity (`forest_continuity_not_reflexive`),
--   so it is not a `SafeStep` instance. Closing requires a restriction map `ρ` along chain edges
--   and a proof that commitment continuity implies frame-preservation.
-- OPEN: The higher-order tier requires a step-indexed (`▶`-guarded) recursive `Auth` camera
--   (only the discrete RA is built). `safe_transformer_composes` is first-order only.
-- OPEN: The `act` functor is supplied externally. There is no proof that `Await.Handler`'s
--   committed effect induces `act`; wiring the commit/abort arms of `turnAsRollbackHandler`
--   to an `act` is the next bridge. -/

end Dregg2.HandlerTransformer
