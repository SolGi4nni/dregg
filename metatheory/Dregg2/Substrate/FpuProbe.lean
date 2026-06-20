/-
# Dregg2.Substrate.FpuProbe — S0: the decisive falsification probe for DREGG3 §6 R1.

THE CLAIM UNDER TEST (DREGG3 §2.1, "the one gate"): *every kernel verb is a
frame-preserving update (`Fpu`) in the product of four substance-cameras*
(value = linear, authority = affine, evidence = monotone, state = guarded-heap),
so that conservation + non-amplification + monotonicity collapse into ONE theorem
schema. This module exists to find out whether that is TRUE, PARTIAL, or FALSE —
an honest negative is as valuable as a positive. Every escape hatch is counted in
§LEDGER at the bottom; nothing is rescued by a vacuous trick (each vacuous
formulation that was TRIED is kept as a THEOREM exhibiting its vacuity).

Method: instantiate the EXISTING theorems (the conservation spine
`recTransferBal_sum_conserve_moved`/`recCexecAsset_iff_spec`, the attenuation gate
`attenuate_confRights_le`/`recKDelegateAtten_non_amplifying`, the guarded write
`stateStepGuarded_eq`/`stateStep_factors`, the in-tree camera `Resource.lean`'s
`Auth`/`conservation_is_fpu`/`fpu_of_total`/`Excl`) — NOT re-prove from scratch.

Layout:
  §1  the product of resource algebras (the product RA is an RA; `fpu_prod`)
  §2  generic Auth-camera Fpu lemmas + the two NEGATIVE space-probes
      (ℤ trivializes validity; ℕ admits coordinated mint — Fpu ⊉ Σδ=0!)
  §3  `USet` — Finset-∪ as an AddCommMonoid, so the IN-TREE `Auth` camera serves
      authority AND evidence (fits = ⊆): one camera shape, two substances
  §4  `SAuth` — the supply-validity camera (valid ● := the measure equals the
      constituted constant): conservation AS validity, parametricity counted
  §5  VALUE     — `move` is Fpu in `SAuth` (from the conservation spine); a mint
      is provably NOT Fpu (non-vacuity)
  §6  AUTHORITY — the attenuated `grant` is Fpu via the IN-TREE
      `conservation_is_fpu` (the "one law" of Resource.lean:319, made concrete);
      an amplifying grant is provably NOT Fpu
  §7  EVIDENCE  — nullifier spend = authoritative growth = Fpu; FORGETTING a
      nullifier is provably NOT Fpu; the valid=True formulation exhibited vacuous
  §8  STATE     — the Excl-heap camera: the points-to write is Fpu (the frame
      rule AS a camera), writing an unowned slot is NOT Fpu; the caveat/authority
      GUARD is provably INVISIBLE to the camera (the kernel is strictly stricter)
  §9  THE PRODUCT APEX — `move_is_fpu` / `grant_is_fpu` / `write_is_fpu` (+
      `spend_is_fpu`) in the 4-substance product, untouched legs by `Fpu.refl`
      off the existing frame lemmas
  §LEDGER — the honest escape-hatch census + the verdict.
-/
import Dregg2.Resource
import Dregg2.Exec.TurnExecutorFull
import Dregg2.Circuit.Spec.balancemovement
import Dregg2.Tactics

namespace Dregg2.Substrate.FpuProbe

open Dregg2.Resource
open scoped Dregg2.Resource.ResourceAlgebra
open Dregg2.Exec
open Dregg2.Exec.TurnExecutorFull
open Dregg2.Circuit.Spec.BalanceMovement
open Dregg2.Exec.EffectsState (stateStepGuarded stateStepGuarded_eq stateStep_factors
  caveatsAdmit stateStepGuarded_caveat_violation_fails writeField setField fieldOf)

/-- The rights enumeration (qualified: `Resource.Auth` is the camera, `Authority.Auth`
the rights enum — the name collision itself is a small census datum). -/
abbrev Rights := Dregg2.Authority.Auth

/-! ## §1 — The product of resource algebras IS a resource algebra.

Componentwise `op`/`valid`; the core exists iff both components' cores exist (the Iris
product-camera `pcore`). This is what "the product of the four substance-cameras"
formally means; `fpu_prod` is the schema's glue: componentwise Fpu ⇒ product Fpu. -/

open ResourceAlgebra in
instance instProdRA {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B] :
    ResourceAlgebra (A × B) where
  op a b    := (a.1 ⊙ b.1, a.2 ⊙ b.2)
  valid a   := valid a.1 ∧ valid a.2
  core a    :=
    match core a.1, core a.2 with
    | some c1, some c2 => some (c1, c2)
    | _, _ => none
  op_comm a b := by
    show (a.1 ⊙ b.1, a.2 ⊙ b.2) = (b.1 ⊙ a.1, b.2 ⊙ a.2)
    rw [op_comm a.1 b.1, op_comm a.2 b.2]
  op_assoc a b c := by
    show ((a.1 ⊙ b.1) ⊙ c.1, (a.2 ⊙ b.2) ⊙ c.2) = (a.1 ⊙ (b.1 ⊙ c.1), a.2 ⊙ (b.2 ⊙ c.2))
    rw [op_assoc a.1 b.1 c.1, op_assoc a.2 b.2 c.2]
  valid_op_left a b h := ⟨valid_op_left a.1 b.1 h.1, valid_op_left a.2 b.2 h.2⟩
  core_id a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (c1 ⊙ a.1, c2 ⊙ a.2) = a
        rw [core_id a.1 c1 h1, core_id a.2 c2 h2]
  core_idem a ca h := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        show (match core c1, core c2 with
              | some d1, some d2 => some (d1, d2)
              | _, _ => none) = some (c1, c2)
        rw [core_idem a.1 c1 h1, core_idem a.2 c2 h2]
  core_mono a b ca h hext := by
    cases h1 : core a.1 with
    | none => simp [h1] at h
    | some c1 =>
      cases h2 : core a.2 with
      | none => simp [h1, h2] at h
      | some c2 =>
        simp only [h1, h2, Option.some.injEq] at h
        subst h
        obtain ⟨e, he⟩ := hext
        have hb1 : ∃ z, b.1 = a.1 ⊙ z := ⟨e.1, by rw [he]⟩
        have hb2 : ∃ z, b.2 = a.2 ⊙ z := ⟨e.2, by rw [he]⟩
        obtain ⟨d1, hd1, w1, hw1⟩ := core_mono a.1 b.1 c1 h1 hb1
        obtain ⟨d2, hd2, w2, hw2⟩ := core_mono a.2 b.2 c2 h2 hb2
        refine ⟨(d1, d2), by rw [hd1, hd2], (w1, w2), ?_⟩
        show (d1, d2) = (c1 ⊙ w1, c2 ⊙ w2)
        rw [hw1, hw2]

/-- **The product glue.** Componentwise Fpu lifts to the product — the formal content of
"one theorem schema over the product of the substances". -/
theorem fpu_prod {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (h1 : Fpu a b) (h2 : Fpu c d) : Fpu (a, c) (b, d) :=
  fun f hv => ⟨h1 f.1 hv.1, h2 f.2 hv.2⟩

/-- **The product tooth.** If ONE component update is not Fpu (witnessed by a frame that
the other components can accompany validly), the PRODUCT update is not Fpu — a violation
in any single substance kills the whole verb. -/
theorem not_fpu_prod_left {A : Type u} {B : Type v} [ResourceAlgebra A] [ResourceAlgebra B]
    {a b : A} {c d : B} (f1 : A)
    (hpre : ResourceAlgebra.valid (a ⊙ f1)) (hpost : ¬ ResourceAlgebra.valid (b ⊙ f1))
    (f2 : B) (hc : ResourceAlgebra.valid (c ⊙ f2)) : ¬ Fpu (a, c) (b, d) :=
  fun h => hpost (h (f1, f2) ⟨hpre, hc⟩).1

/-! ## §2 — Generic Auth-camera Fpu lemmas + the two NEGATIVE space-probes.

These two negative results are the probe's first real finding (the "does a natural
`valid` exist WITHOUT begging the question?" test for VALUE):

  * over a **group** (the kernel's debt-capable `ℤ` ledger), `fits` is TOTAL, so EVERY
    `●`-update — including the most violent mint — is Fpu (`int_auth_fpu_vacuous`):
    camera validity carries NOTHING;
  * over the **ordered cancellative `ℕ`**, the order bites
    (`nat_frag_mint_not_fpu`) — but a COORDINATED mint (authority and fragment grown
    together; Iris's `auth_update_alloc`) is STILL Fpu (`nat_auth_coordinated_mint_fpu`).

Conclusion: **Fpu expresses frame-consistency, NOT Σδ=0.** Conservation enters the
camera only if `valid` itself carries the supply constant — §4's `SAuth`. -/

/-- **The local-update lemma** (Iris `auth_update`): if replacing `(● a, ◦ f)` by
`(● a', ◦ f')` preserves every exact complement (`∀ d, a = f + d → a' = f' + d`), the
replacement is frame-preserving. The general engine behind every `●`+`◦` move. -/
theorem auth_local_update_fpu {M : Type u} [AddCommMonoid M] {a a' f f' : M}
    (h : ∀ d, a = f + d → a' = f' + d) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some a') f') := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv ⊢
      obtain ⟨c, hc⟩ := hv
      have := h (g + c) (by rw [hc, add_assoc])
      exact ⟨c, by rw [this, add_assoc]⟩
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **Authoritative growth is Fpu** (Iris `auth_update_auth`): enlarging `● a` to
`● (a + t)` while fragments stand still never invalidates a frame — every fragment that
fit within `a` fits within `a + t`. THIS is the monotone-substance law (evidence). -/
theorem auth_grow_fpu {M : Type u} [AddCommMonoid M] (a t f : M) :
    Fpu (R := Auth M) (.mk (some a) f) (.mk (some (a + t)) f) := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hv ⊢
      obtain ⟨c, hc⟩ := hv
      exact ⟨c + t, by rw [hc, add_assoc]⟩
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **NEGATIVE SPACE-PROBE 1 (ℤ trivializes the camera).** Over a GROUP-valued carrier —
the kernel's actual debt-capable `bal : CellId → AssetId → ℤ` — `fits` is total
(`c := a - f` always exists), so EVERY `●`-to-`●` update is "frame-preserving",
including any mint or burn. Conservation-as-Fpu over the raw ℤ ledger is VACUOUS:
this theorem proves the vacuity rather than hiding it. -/
theorem int_auth_fpu_vacuous (a a' f f' : ℤ) :
    Fpu (R := Auth ℤ) (.mk (some a) f) (.mk (some a') f') := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
      exact ⟨a' - (f' + g), by ring⟩
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid])

/-- **NEGATIVE SPACE-PROBE 2 (even ℕ's order does not give Σδ=0).** Over the ordered,
cancellative `ℕ` the camera order bites (`nat_frag_mint_not_fpu` below) — but a
COORDINATED mint, growing the authority and one's own fragment together, is STILL a
frame-preserving update (it is exactly Iris's `auth_update_alloc`). So `Fpu` in the
order-validity camera does NOT imply conservation; it implies only frame-consistency.
The Σδ=0 content must live in `valid` itself (§4) — this is the probe's central
discovery for VALUE. -/
theorem nat_auth_coordinated_mint_fpu (a f amt : ℕ) :
    Fpu (R := Auth ℕ) (.mk (some a) f) (.mk (some (a + amt)) (f + amt)) :=
  auth_local_update_fpu (fun d hd => by omega)

/-- The ℕ camera's order DOES bite (it is not vacuous like ℤ): growing a fragment
WITHOUT the authority's growth is NOT Fpu — the frame `◦ 0` against `● 1` is invalidated
when the fragment claims `2 > 1`. (So the ℕ camera enforces *no uncovered claims*; what
it does not enforce is *no consented mint* — see `nat_auth_coordinated_mint_fpu`.) -/
theorem nat_frag_mint_not_fpu : ¬ Fpu (R := Auth ℕ) (.mk (some 1) 1) (.mk (some 1) 2) := by
  intro h
  have hv : ResourceAlgebra.valid ((Auth.mk (some 1) 1 : Auth ℕ) ⊙ .mk none 0) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits]
    exact ⟨0, by omega⟩
  have hpost := h (.mk none 0) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid, fits] at hpost
  obtain ⟨c, hc⟩ := hpost
  omega

/-! ## §3 — `USet`: Finset-∪ as an `AddCommMonoid`, so the IN-TREE `Auth` camera serves
authority AND evidence.

`Finset α` under `∪` is an (idempotent) commutative monoid; packaging it as an
`AddCommMonoid` lets the existing `Resource.Auth M` camera and the existing
`conservation_is_fpu` apply verbatim, with the extension order `fits` literally `⊆`
(`USet.fits_iff`). One camera shape now carries TWO substances:

  * **authority** (affine): `● held-rights` with `◦ granted` fragments — minting a
    fragment within the bound is Fpu (= non-amplification); amplification is NOT Fpu;
  * **evidence** (monotone): `● the-known-set` growing — growth is Fpu
    (`auth_grow_fpu`), FORGETTING is NOT Fpu.

That two of the four substances are the SAME camera at different carriers is itself a
probe finding (the unification is better than R1 hoped, for these two). -/

/-- `Finset α` wearing its `∪`-monoid hat (a one-field structure, so the `AddCommMonoid`
instance cannot leak onto bare `Finset`s and rewriting stays syntactic: `+` is `∪` of
`.set`, `0` is `⟨∅⟩`). -/
structure USet (α : Type u) [DecidableEq α] : Type u where
  set : Finset α

namespace USet

variable {α : Type u} [DecidableEq α]

instance : Zero (USet α) := ⟨⟨∅⟩⟩
instance : Add (USet α) := ⟨fun a b => ⟨a.set ∪ b.set⟩⟩

instance : AddCommMonoid (USet α) where
  add a b    := a + b
  zero       := 0
  nsmul      := nsmulRec
  add_assoc a b c := congrArg USet.mk (Finset.union_assoc a.set b.set c.set)
  add_comm a b    := congrArg USet.mk (Finset.union_comm a.set b.set)
  zero_add a      := congrArg USet.mk (Finset.empty_union a.set)
  add_zero a      := congrArg USet.mk (Finset.union_empty a.set)

@[simp] theorem add_set (a b : USet α) : (a + b).set = a.set ∪ b.set := rfl
@[simp] theorem zero_set : (0 : USet α).set = (∅ : Finset α) := rfl
@[simp] theorem mk_set (s : Finset α) : (USet.mk s).set = s := rfl

/-- Equality through the wrapper. -/
theorem set_inj {a b : USet α} : a = b ↔ a.set = b.set :=
  ⟨congrArg USet.set, fun h => by cases a; cases b; simpa using h⟩

/-- The monoid extension order on `USet` is LITERALLY `⊆`: the camera's `fits` is the
rights/knowledge inclusion. This is the bridge that lets `attenuate_confRights_le`
(granted `⊆` held) feed `conservation_is_fpu` directly. -/
theorem fits_iff (f a : USet α) : fits f a ↔ f.set ⊆ a.set := by
  constructor
  · rintro ⟨c, hc⟩
    have hs : a.set = f.set ∪ c.set := by
      have := congrArg USet.set hc
      simpa using this
    rw [hs]
    exact Finset.subset_union_left
  · intro h
    refine ⟨⟨a.set⟩, set_inj.mpr ?_⟩
    show a.set = f.set ∪ a.set
    exact (Finset.union_eq_right.mpr h).symm

end USet

/-! ## §4 — `SAuth`: the supply-validity camera.

§2 proved that no order-shaped `valid` makes Fpu ⟺ conservation. The remaining
candidate (the task's hint, and DREGG3 R2's shadow): put the SUPPLY ITSELF into
validity — `valid (● L) := μ L = s₀` where `μ` is the conserved measure and `s₀` the
constituted constant. Then a supply-preserving move IS Fpu and a mint is provably NOT.

THE COST, counted (LEDGER E1): the camera is PARAMETRIC in `(μ, s₀)` — the
measure quantifies over the live-account set, and the constant is constituted at some
genesis. Under R2 (`AssetId := issuer cell`, the issuer carries `−supply`) the constant
becomes canonically `0` and the parameter dissolves; TODAY it is an escape hatch.

(`SAuth` generalizes the in-tree `Auth` by replacing `fits`-validity with an arbitrary
predicate `P` on the authoritative element; the fragment bookkeeping is retained so the
product/`op` shape matches Iris's auth.) -/

/-- The supply-validity carrier: `Auth`'s shape with validity = a predicate `P` on the
authoritative element (for us: "the conserved measure equals the constituted supply"). -/
inductive SAuth (M : Type u) (P : M → Prop) : Type u where
  | mk (auth : Option M) (frag : M)
  | invalid

namespace SAuth

variable {M : Type u} {P : M → Prop}

/-- Composition: fragments add; at most one authoritative; `invalid` absorbs. -/
def op [AddCommMonoid M] : SAuth M P → SAuth M P → SAuth M P
  | .invalid, _ => .invalid
  | _, .invalid => .invalid
  | .mk a1 f1, .mk a2 f2 =>
      match a1, a2 with
      | none,   a      => .mk a (f1 + f2)
      | a,      none   => .mk a (f1 + f2)
      | some _, some _ => .invalid

/-- Validity: the authoritative element satisfies `P` (pure fragments are valid;
`invalid` is not). -/
def valid : SAuth M P → Prop
  | .invalid       => False
  | .mk none _     => True
  | .mk (some a) _ => P a

instance [AddCommMonoid M] : ResourceAlgebra (SAuth M P) where
  op    := SAuth.op
  valid := SAuth.valid
  core  := fun _ => some (.mk none 0)
  op_comm := by
    intro a b
    cases a with
    | invalid => cases b <;> rfl
    | mk a1 f1 =>
      cases b with
      | invalid => rfl
      | mk a2 f2 => cases a1 <;> cases a2 <;> simp [SAuth.op, add_comm]
  op_assoc := by
    intro a b c
    cases a with
    | invalid => rfl
    | mk a1 f1 =>
      cases b with
      | invalid => cases c <;> rfl
      | mk a2 f2 =>
        cases c with
        | invalid => cases a1 <;> cases a2 <;> rfl
        | mk a3 f3 => cases a1 <;> cases a2 <;> cases a3 <;> simp [SAuth.op, add_assoc]
  valid_op_left := by
    intro a b h
    cases a with
    | invalid => exact absurd h (by cases b <;> simp [SAuth.op, SAuth.valid])
    | mk a1 f1 =>
      cases b with
      | invalid => exact absurd h (by simp [SAuth.op, SAuth.valid])
      | mk a2 f2 =>
        cases a1 with
        | none => simp [SAuth.valid]
        | some a1 =>
          cases a2 with
          | none => simpa [SAuth.op, SAuth.valid] using h
          | some a2 => exact absurd h (by simp [SAuth.op, SAuth.valid])
  core_id := by
    intro a ca h
    rw [Option.some.injEq] at h; subst h
    cases a with
    | invalid => rfl
    | mk a1 f1 => cases a1 <;> simp [SAuth.op, zero_add]
  core_idem := by intro a ca h; rw [Option.some.injEq] at h; subst h; rfl
  core_mono := by
    intro a b ca h _
    rw [Option.some.injEq] at h; subst h
    exact ⟨.mk none 0, rfl, .mk none 0, by simp [SAuth.op, add_zero]⟩

/-- **Measure preservation ⇒ Fpu** in the supply camera: if the update keeps the
authoritative element inside `P` (for us: the conserved measure unchanged), it is
frame-preserving. -/
theorem preserve_fpu [AddCommMonoid M] {a a' f f' : M} (h : P a → P a') :
    Fpu (R := SAuth M P) (.mk (some a) f) (.mk (some a') f') := by
  intro fr hv
  cases fr with
  | invalid =>
    exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid])
  | mk a2 g =>
    cases a2 with
    | none =>
      simp only [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid] at hv ⊢
      exact h hv
    | some a2 =>
      exact absurd hv (by simp [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid])

/-- **Measure violation ⇒ NOT Fpu** (the camera's tooth): if the pre-state satisfies `P`
and the post-state breaks it, the update is not frame-preserving (the empty frame
witnesses). For us: a supply-changing move is rejected by the camera. -/
theorem break_not_fpu [AddCommMonoid M] {a a' f f' : M} (ha : P a) (ha' : ¬ P a') :
    ¬ Fpu (R := SAuth M P) (.mk (some a) f) (.mk (some a') f') := by
  intro hF
  have hv : ResourceAlgebra.valid ((SAuth.mk (some a) f : SAuth M P) ⊙ .mk none 0) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid]
    exact ha
  have hpost := hF (.mk none 0) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid] at hpost
  exact ha' hpost

end SAuth

/-! ## §5 — VALUE: `move` is Fpu in the supply camera (from the conservation spine).

The substance carrier is the genuine per-asset ledger `CellId → AssetId → ℤ`; the
conserved measure is `supply acc L : AssetId → ℤ` (the per-asset column sums over the
live accounts — the vector `recTotalAsset`, NOT one collapsed scalar). The camera is
`SAuth Ledger (fun L => supply acc L = s₀)`. `move_value_fpu` instantiates the EXISTING
spine: `recCexecAsset_iff_spec` (the full-state triangle) +
`recTransferBal_sum_conserve_moved` (moved column) + `recTransferBal_untouched`
(every other column). The mint counterexample uses the same `sum_indicator` the spine
itself is built on. -/

/-- The value-substance carrier: the genuine per-asset ledger. -/
abbrev Ledger := CellId → AssetId → ℤ

/-- The conserved measure: per-asset supply over the live accounts (the
`recTotalAsset` vector as a function of the ledger). -/
def supply (acc : Finset CellId) (L : Ledger) : AssetId → ℤ :=
  fun a => ∑ c ∈ acc, L c a

/-- The VALUE camera: the supply-validity camera at live-account set `acc` and
constituted supply `s₀`. (E1: the `(acc, s₀)` parametricity is counted in the LEDGER —
it dissolves under R2, where `s₀ = 0` canonically.) -/
abbrev ValueCam (acc : Finset CellId) (s0 : AssetId → ℤ) : Type :=
  SAuth Ledger (fun L => supply acc L = s0)

/-- **`move_value_fpu` — the VALUE corner, derived from the conservation spine.**
A committed per-asset transfer (`recCexecAsset`, the arm `execFullA` dispatches
`.balanceA` to) is a frame-preserving update in the supply camera, FOR EVERY constituted
supply `s₀`. Instantiates `recCexecAsset_iff_spec` + `recTransferBal_sum_conserve_moved`
+ `recTransferBal_untouched` — no fresh conservation proof. -/
theorem move_value_fpu (st st' : RecChainedState) (t : Turn) (a : AssetId)
    (h : recCexecAsset st t a = some st') (s0 : AssetId → ℤ) :
    Fpu (R := ValueCam st.kernel.accounts s0)
      (.mk (some st.kernel.bal) 0) (.mk (some st'.kernel.bal) 0) := by
  obtain ⟨hguard, hbal, _⟩ := (recCexecAsset_iff_spec st t a st').mp h
  obtain ⟨_, _, _, hne, hsrc, hdst, _⟩ := hguard
  have hsup : supply st.kernel.accounts st'.kernel.bal = supply st.kernel.accounts st.kernel.bal := by
    funext b
    show (∑ c ∈ st.kernel.accounts, st'.kernel.bal c b) = ∑ c ∈ st.kernel.accounts, st.kernel.bal c b
    rw [hbal]
    rcases eq_or_ne b a with rfl | hb
    · exact recTransferBal_sum_conserve_moved st.kernel.accounts st.kernel.bal
        t.src t.dst b t.amt hsrc hdst hne
    · exact Finset.sum_congr rfl
        (fun c _ => recTransferBal_untouched st.kernel.bal t.src t.dst a b t.amt hb c)
  exact SAuth.preserve_fpu (fun h0 => by rw [hsup]; exact h0)

/-- A bare mint: credit `dst` with `amt` of asset `a`, debiting nobody. -/
def mintBal (L : Ledger) (dst : CellId) (a : AssetId) (amt : ℤ) : Ledger :=
  fun c b => if c = dst ∧ b = a then L c b + amt else L c b

/-- A mint changes the minted asset's supply by exactly `amt` (via the spine's own
`sum_indicator`). -/
theorem mintBal_supply (acc : Finset CellId) (L : Ledger) (dst : CellId) (a : AssetId)
    (amt : ℤ) (hdst : dst ∈ acc) :
    supply acc (mintBal L dst a amt) a = supply acc L a + amt := by
  show (∑ c ∈ acc, mintBal L dst a amt c a) = (∑ c ∈ acc, L c a) + amt
  have hsplit : ∀ c ∈ acc,
      mintBal L dst a amt c a = L c a + (if c = dst then amt else 0) := by
    intro c _
    unfold mintBal
    by_cases hc : c = dst
    · simp [hc]
    · simp [hc]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, sum_indicator acc dst amt hdst]

/-- **VALUE NON-VACUITY: a conservation-violating move is provably NOT Fpu.** Minting
`amt ≠ 0` of asset `a` breaks the supply-camera's validity, so the camera rejects it —
the schema has teeth exactly where the spine does. -/
theorem mint_not_value_fpu (acc : Finset CellId) (L : Ledger) (dst : CellId) (a : AssetId)
    (amt : ℤ) (hdst : dst ∈ acc) (hamt : amt ≠ 0) :
    ¬ Fpu (R := ValueCam acc (supply acc L))
        (.mk (some L) 0) (.mk (some (mintBal L dst a amt)) 0) := by
  refine SAuth.break_not_fpu (P := fun L' => supply acc L' = supply acc L) rfl ?_
  intro hP
  have := congrFun hP a
  rw [mintBal_supply acc L dst a amt hdst] at this
  omega

/-! ## §6 — AUTHORITY: the attenuated grant is Fpu via the IN-TREE `conservation_is_fpu`.

`Resource.lean:319` DEFINED `ConfinesAuthority := Fpu` and promised "conservation and
confinement are one law". Here the promise is cashed concretely: the carrier is the REAL
rights lattice `ExecAuth = Finset Auth` (as the ∪-monoid `USet Rights`), the camera is
the in-tree `Auth (USet Rights)`, the bound `●` is the delegator's held rights
(`heldCapTo`), the granted fragment is `attenuate keep`'s conferred rights, and the
inclusion feeding `conservation_is_fpu`'s `hmono` is EXACTLY the existing
`recKDelegateAtten_non_amplifying` (= `attenuate_confRights_le`). Zero new authority
mathematics — the existing attenuation gate IS the Fpu instance. -/

/-- **`grant_authority_fpu` — the AUTHORITY corner, an instance of the in-tree
`conservation_is_fpu`.** Minting the attenuated-grant fragment under the delegator's held
bound is a frame-preserving update in `Auth (USet Rights)`; the `hmono` obligation is
discharged by `recKDelegateAtten_non_amplifying` (granted ⊆ held). -/
theorem grant_authority_fpu (caps : Dregg2.Authority.Caps) (delegator t : CellId)
    (keep : List Rights) :
    Fpu (R := Auth (USet Rights))
      (.mk (some ⟨confRights (heldCapTo caps delegator t)⟩) 0)
      (.mk (some ⟨confRights (heldCapTo caps delegator t)⟩)
           ⟨confRights (attenuate keep (heldCapTo caps delegator t))⟩) := by
  apply conservation_is_fpu
  intro g hg
  rw [zero_add] at hg
  rw [USet.fits_iff] at hg ⊢
  rw [USet.add_set, USet.mk_set]
  refine Finset.union_subset ?_ hg
  show confRights (attenuate keep (heldCapTo caps delegator t)) ⊆ _
  rw [← Finset.le_iff_subset]
  exact recKDelegateAtten_non_amplifying caps delegator t keep

/-- The unification cashed: the grant's Fpu IS `ConfinesAuthority` (definitionally —
`Resource.lean:319`'s "one law", now inhabited by the real executable attenuation). -/
theorem grant_confines (caps : Dregg2.Authority.Caps) (delegator t : CellId)
    (keep : List Rights) :
    ConfinesAuthority (C := Auth (USet Rights))
      (Auth.mk (some ⟨confRights (heldCapTo caps delegator t)⟩) 0)
      (Auth.mk (some ⟨confRights (heldCapTo caps delegator t)⟩)
           ⟨confRights (attenuate keep (heldCapTo caps delegator t))⟩) :=
  grant_authority_fpu caps delegator t keep

/-- **AUTHORITY NON-VACUITY: an AMPLIFYING grant is provably NOT Fpu.** Granting `write`
under a bound of only `read` is rejected by the camera (the empty frame already
witnesses the amplification). -/
theorem amplifying_grant_not_fpu :
    ¬ Fpu (R := Auth (USet Rights))
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0)
        (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩) := by
  intro hF
  have hv : ResourceAlgebra.valid
      ((Auth.mk (some (⟨{Dregg2.Authority.Auth.read}⟩ : USet Rights)) 0 : Auth (USet Rights))
        ⊙ .mk none 0) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid]
    rw [add_zero, USet.fits_iff]
    simp
  have hpost := hF (.mk none 0) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at hpost
  rw [add_zero, USet.fits_iff] at hpost
  have hmem := hpost (Finset.mem_singleton_self Dregg2.Authority.Auth.write)
  exact absurd hmem (by decide)

/-! ## §7 — EVIDENCE: the monotone substance is the SAME camera growing its `●`.

The discovery here: evidence does NOT need a new algebra. The grow-only law is
`auth_grow_fpu` in `Auth (USet ℕ)` — the authoritative set (the spent-nullifier ledger)
grows, every snapshot fragment a third party holds stays within it. FORGETTING a
nullifier is NOT Fpu (a frame holding the full snapshot is invalidated) — that is the
monotone tooth. And the lazy formulation (`valid := True`) is exhibited VACUOUS rather
than used: under it even deletion is "Fpu" (`fpu_of_total`, in-tree), so it cannot carry
the law. -/

/-- **`spend_evidence_fpu` — the EVIDENCE corner.** A committed `noteSpendNullifier`
grows the authoritative spent-set by `{nf}`: an instance of `auth_grow_fpu` (the
authoritative-growth law) in `Auth (USet ℕ)`. -/
theorem spend_evidence_fpu (k k' : RecordKernelState) (nf : Nat)
    (h : noteSpendNullifier k nf = some k') :
    Fpu (R := Auth (USet Nat))
      (.mk (some ⟨k.nullifiers.toFinset⟩) 0)
      (.mk (some ⟨k'.nullifiers.toFinset⟩) 0) := by
  have hnl : k'.nullifiers = nf :: k.nullifiers := by
    unfold noteSpendNullifier at h
    by_cases hin : nf ∈ k.nullifiers
    · rw [if_pos hin] at h; exact absurd h (by simp)
    · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h; rfl
  have hset : (⟨k'.nullifiers.toFinset⟩ : USet Nat)
      = (⟨k.nullifiers.toFinset⟩ : USet Nat) + ⟨{nf}⟩ := by
    refine USet.set_inj.mpr ?_
    show k'.nullifiers.toFinset = k.nullifiers.toFinset ∪ {nf}
    rw [hnl, List.toFinset_cons, Finset.insert_eq, Finset.union_comm]
  rw [hset]
  exact auth_grow_fpu _ _ _

/-- **EVIDENCE NON-VACUITY: forgetting is provably NOT Fpu.** Erasing a known nullifier
invalidates the frame that holds the full snapshot — once known, never unknown, as a
camera fact. (THIS is what makes the evidence camera non-vacuous where `valid := True`
fails, next theorem.) -/
theorem forget_evidence_not_fpu (s : Finset Nat) (nf : Nat) (hmem : nf ∈ s) :
    ¬ Fpu (R := Auth (USet Nat))
        (.mk (some ⟨s⟩) 0) (.mk (some ⟨s.erase nf⟩) 0) := by
  intro hF
  have hv : ResourceAlgebra.valid
      ((Auth.mk (some (⟨s⟩ : USet Nat)) 0 : Auth (USet Nat)) ⊙ .mk none ⟨s⟩) := by
    simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid]
    rw [zero_add, USet.fits_iff]
  have hpost := hF (.mk none ⟨s⟩) hv
  simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid] at hpost
  rw [zero_add, USet.fits_iff] at hpost
  exact Finset.notMem_erase nf s (hpost hmem)

/-- The lazy grow-only camera (`op = ∪, valid = True`): everything is duplicable, nothing
is ever invalid. Kept ONLY to exhibit its vacuity (next theorem) — it is NOT used as a
substance. -/
instance trivialGrowRA : ResourceAlgebra (Finset Nat) where
  op a b   := a ∪ b
  valid _  := True
  core a   := some a
  op_comm  := Finset.union_comm
  op_assoc := Finset.union_assoc
  valid_op_left := fun _ _ _ => trivial
  core_id := by
    intro a ca h; rw [Option.some.injEq] at h; subst h; exact Finset.union_self a
  core_idem := fun _ _ _ => rfl
  core_mono := by
    intro a b ca h hext; rw [Option.some.injEq] at h; subst h
    obtain ⟨c, hc⟩ := hext
    exact ⟨b, rfl, c, hc⟩

/-- **The vacuity of `valid := True`, exhibited (not laundered).** Under the trivial
validity even FORGETTING evidence is "frame-preserving" (the in-tree `fpu_of_total`),
so that formulation cannot carry the monotone law: `Fpu` only ever bites through
`valid`. The honest evidence camera is `Auth (USet ℕ)` above. -/
theorem trivial_valid_forgets_monotonicity (s : Finset Nat) (nf : Nat) :
    Fpu (R := Finset Nat) s (s.erase nf) :=
  fpu_of_total (fun _ => trivial) s (s.erase nf)

/-! ## §8 — STATE: the guarded heap, half a camera.

The heap of slots IS a camera — the points-to camera `Loc → Option (Excl V)` (Iris's
`gmap_view`/heap RA, built from the in-tree `Excl`): exclusively-owned locations, with
`valid` = no location doubly owned. In it, the frame rule IS Fpu: rewriting an owned slot
preserves every frame (a frame cannot own the same slot — composition would be invalid),
and writing an UNOWNED slot is NOT Fpu (non-vacuity).

But the kernel's write is `stateStepGuarded` — caveat-gated, authority-gated, and
lifecycle-gated. **None of those gates appear in camera validity** — and this is proved,
not glossed: `camera_blind_to_caveats` exhibits a write the kernel REJECTS fail-closed
while the camera blesses it as a perfectly good Fpu. The GUARD half of "guarded heap" is
an admission precondition OUTSIDE the algebra (Iris keeps it in the Hoare triple, not the
RA) — counted as LEDGER E2. -/

/-- A heap fragment: each location is unowned (`none`) or exclusively held. Built on the
in-tree `Excl` camera. -/
def Heap (L : Type u) (V : Type v) : Type (max u v) := L → Option (Excl V)

namespace Heap

variable {L : Type u} {V : Type v}

/-- Disjoint composition: `none` is the unit; two owners of one location collapse to the
invalid exclusive (the in-tree `Excl.op`). -/
def hop (h1 h2 : Heap L V) : Heap L V := fun l =>
  match h1 l, h2 l with
  | none,   x      => x
  | x,      none   => x
  | some _, some _ => some Excl.invalid

/-- Validity: no location holds the invalid exclusive — i.e. no location is doubly
owned. -/
def hvalid (h : Heap L V) : Prop := ∀ l e, h l = some e → Excl.valid e

/-- The empty heap (the duplicable core: owning nothing). -/
def emp : Heap L V := fun _ => none

instance : ResourceAlgebra (Heap L V) where
  op    := hop
  valid := hvalid
  core  := fun _ => some emp
  op_comm := by
    intro a b; funext l
    show hop a b l = hop b a l
    unfold hop
    cases a l <;> cases b l <;> rfl
  op_assoc := by
    intro a b c; funext l
    show hop (hop a b) c l = hop a (hop b c) l
    unfold hop
    cases a l <;> cases b l <;> cases c l <;> rfl
  valid_op_left := by
    intro a b h l e hae
    cases hbl : b l with
    | none =>
      have : hop a b l = some e := by unfold hop; rw [hae, hbl]
      exact h l e this
    | some eb =>
      have : hop a b l = some Excl.invalid := by unfold hop; rw [hae, hbl]
      exact absurd (h l Excl.invalid this) (by simp [Excl.valid])
  core_id := by
    intro a ca h; rw [Option.some.injEq] at h; subst h
    funext l
    show hop emp a l = a l
    unfold hop emp
    rfl
  core_idem := by intro a ca h; rw [Option.some.injEq] at h; subst h; rfl
  core_mono := by
    intro a b ca h _
    rw [Option.some.injEq] at h; subst h
    refine ⟨emp, rfl, emp, ?_⟩
    funext l
    show emp l = hop emp emp l
    rfl

/-- The singleton heap: exclusive ownership of one slot. -/
def single [DecidableEq L] (l : L) (e : Excl V) : Heap L V :=
  fun l' => if l' = l then some e else none

/-- **The frame rule AS a camera Fpu** (the points-to update): rewriting an exclusively
owned slot to ANY new value is frame-preserving — no valid frame can own the same slot,
and every other slot is untouched. -/
theorem write_fpu [DecidableEq L] (l : L) (v v' : V) :
    Fpu (R := Heap L V) (single l (.ex v)) (single l (.ex v')) := by
  intro fr hv
  have hv' : hvalid (hop (single l (Excl.ex v)) fr) := hv
  intro l' e he
  have he' : hop (single l (Excl.ex v')) fr l' = some e := he
  by_cases hl : l' = l
  · subst hl
    cases hfr : fr l' with
    | none =>
      have hcomp : hop (single l' (Excl.ex v')) fr l' = some (Excl.ex v') := by
        unfold hop single
        rw [if_pos rfl, hfr]
      rw [hcomp] at he'
      rw [Option.some.injEq] at he'
      subst he'
      trivial
    | some efr =>
      have hbad : hop (single l' (Excl.ex v)) fr l' = some Excl.invalid := by
        unfold hop single
        rw [if_pos rfl, hfr]
      exact absurd (hv' l' Excl.invalid hbad) (by simp [Excl.valid])
  · have hpre : hop (single l (Excl.ex v)) fr l' = fr l' := by
      unfold hop single
      rw [if_neg hl]
    have hpost : hop (single l (Excl.ex v')) fr l' = fr l' := by
      unfold hop single
      rw [if_neg hl]
    rw [hpost] at he'
    exact hv' l' e (by rw [hpre]; exact he')

/-- **STATE NON-VACUITY: writing an UNOWNED slot is NOT Fpu.** Claiming a slot out of
thin air invalidates the frame that owns it — sovereignty as a camera fact
(the anti-ghost tooth at the substrate tier). -/
theorem alloc_unowned_not_fpu [DecidableEq L] (l : L) (v w : V) :
    ¬ Fpu (R := Heap L V) emp (single l (.ex v)) := by
  intro hF
  have hv : ResourceAlgebra.valid ((emp : Heap L V) ⊙ single l (.ex w)) := by
    show hvalid (hop emp (single l (Excl.ex w)))
    intro l' e he
    have he' : single l (Excl.ex w) l' = some e := he
    unfold single at he'
    by_cases hl : l' = l
    · rw [if_pos hl, Option.some.injEq] at he'; subst he'; trivial
    · rw [if_neg hl] at he'; exact absurd he' (by simp)
  have hpost := hF (single l (.ex w)) hv
  have hpost' : hvalid (hop (single l (Excl.ex v)) (single l (Excl.ex w))) := hpost
  have hbad : hop (single l (Excl.ex v)) (single l (Excl.ex w)) l = some Excl.invalid := by
    unfold hop single
    rw [if_pos rfl, if_pos rfl]
  exact absurd (hpost' l Excl.invalid hbad) (by simp [Excl.valid])

end Heap

/-- A slot location: (cell, field). -/
abbrev Loc : Type := CellId × FieldName

/-- The committed scalar at a slot (dregg1's `FIELD_ZERO` default, via the executor's
own `fieldOf`). -/
def slotVal (k : RecordKernelState) (c : CellId) (f : FieldName) : Int :=
  fieldOf f (k.cell c)

/-- **`write_state_fpu` — the STATE corner.** A committed caveat-gated write
(`stateStepGuarded`, the arm `execFullA` dispatches `.setFieldA` to) is, on its
footprint, the points-to Fpu: the owned slot `(target, f)` moves from its old committed
scalar to `n`. NOTE (E2, proved below): the commit hypothesis is NOT needed for the
Fpu — the camera blesses ANY owned-slot rewrite; the caveat/authority/lifecycle gates
live OUTSIDE the camera. -/
theorem write_state_fpu (s s' : RecChainedState) (f : FieldName) (actor target : CellId)
    (n : Int) (_h : stateStepGuarded s f actor target n = some s') :
    Fpu (R := Heap Loc Int)
      (Heap.single (target, f) (.ex (slotVal s.kernel target f)))
      (Heap.single (target, f) (.ex (slotVal s'.kernel target f))) :=
  Heap.write_fpu (target, f) _ _

/-- The kernel-side frame behind the heap leg: a committed guarded write touches NO other
cell's record (read off `stateStep_factors` + `writeField`). (The slot-level frame within
the SAME cell is the codec fact `setField`-other-field — carried by the executor's §
field lemmas; here we pin the cross-cell frame the camera's `single` footprint needs.) -/
theorem write_state_frame (s s' : RecChainedState) (f : FieldName) (actor target : CellId)
    (n : Int) (h : stateStepGuarded s f actor target n = some s')
    (c : CellId) (hc : c ≠ target) :
    s'.kernel.cell c = s.kernel.cell c := by
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  rw [hs']
  show (if c = target then _ else s.kernel.cell c) = s.kernel.cell c
  rw [if_neg hc]

/-- **E2, PROVED (the camera is BLIND to the guard).** A write that EVERY caveat
rejects — which the kernel therefore fails CLOSED (`none`) — is nonetheless a perfectly
frame-preserving update in the heap camera. The "guarded" half of the guarded-heap
substance is NOT camera validity; it is an admission precondition outside the algebra
(in Iris: the Hoare triple's precondition, never the RA). This is the probe's sharpest
honest negative: the Fpu schema does NOT subsume the guard-theorem family. -/
theorem camera_blind_to_caveats (s : RecChainedState) (f : FieldName)
    (actor target : CellId) (n : Int)
    (hbad : caveatsAdmit s.kernel f actor target n = false) :
    stateStepGuarded s f actor target n = none
    ∧ Fpu (R := Heap Loc Int)
        (Heap.single (target, f) (.ex (slotVal s.kernel target f)))
        (Heap.single (target, f) (.ex n)) :=
  ⟨stateStepGuarded_caveat_violation_fails s f actor target n hbad,
   Heap.write_fpu (target, f) _ _⟩

/-! ## §9 — THE PRODUCT APEX: the three verbs as Fpu in the 4-substance product.

`Sub4` is the product camera (value × authority × evidence × state). Each verb theorem
gives the verb's FOOTPRINT elements explicitly (which substances it owns and moves) and
proves the product Fpu: the moving leg by the §5–§8 corner theorems, every untouched leg
by `Fpu.refl` after rewriting with the EXISTING frame facts (`recCexecAsset_iff_spec`'s
frame clauses, the delegate/write factorings). The footprint-indexing of the elements is
itself a census finding (LEDGER F3). -/

/-- The 4-substance product camera. Order: VALUE × AUTHORITY × EVIDENCE × STATE. -/
abbrev Sub4 (acc : Finset CellId) (s0 : AssetId → ℤ) : Type :=
  ValueCam acc s0 × Auth (USet Rights) × Auth (USet Nat) × Heap Loc Int

/-- **`move_is_fpu` — the verb `move` in the product.** The VALUE leg moves (the supply
camera, §5); the AUTHORITY leg is `Fpu.refl` off the spec's `caps`-frame; the EVIDENCE
leg is `Fpu.refl` off the `nullifiers`-frame; the STATE leg owns nothing (`emp`). All
frame clauses come from `recCexecAsset_iff_spec` — the existing triangle, instantiated. -/
theorem move_is_fpu (st st' : RecChainedState) (t : Turn) (a : AssetId)
    (h : recCexecAsset st t a = some st') (s0 : AssetId → ℤ) :
    Fpu (R := Sub4 st.kernel.accounts s0)
      ((.mk (some st.kernel.bal) 0),
       (.mk (some ⟨confRights (heldCapTo st.kernel.caps t.actor t.src)⟩) 0),
       (.mk (some ⟨st.kernel.nullifiers.toFinset⟩) 0),
       Heap.emp)
      ((.mk (some st'.kernel.bal) 0),
       (.mk (some ⟨confRights (heldCapTo st'.kernel.caps t.actor t.src)⟩) 0),
       (.mk (some ⟨st'.kernel.nullifiers.toFinset⟩) 0),
       Heap.emp) := by
  obtain ⟨_, _, _, _, _, hcaps, hnul, _⟩ := (recCexecAsset_iff_spec st t a st').mp h
  refine fpu_prod (move_value_fpu st st' t a h s0) (fpu_prod ?_ (fpu_prod ?_ (Fpu.refl _)))
  · rw [hcaps]; exact Fpu.refl _
  · rw [hnul]; exact Fpu.refl _

/-- The substrate frame of the attenuated delegation: it edits ONLY `caps` (the in-tree
`recKDelegateAtten_frame` pins `recTotal`/`accounts`/`cell` but NOT `bal`/`nullifiers` —
an instantiation gap filled here by the same one-step unfold; see LEDGER F4). -/
theorem recKDelegateAtten_substrate_frame (k k' : RecordKernelState)
    (d r t : CellId) (keep : List Rights)
    (h : recKDelegateAtten k d r t keep = some k') :
    k'.bal = k.bal ∧ k'.nullifiers = k.nullifiers ∧ k'.accounts = k.accounts := by
  unfold recKDelegateAtten at h
  by_cases hg : (k.caps d).any (fun cap => confersEdgeTo t cap) = true
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`grant_is_fpu` — the verb `grant` in the product.** The AUTHORITY leg mints the
attenuated fragment under the held bound (§6 — the in-tree `conservation_is_fpu` fed by
`recKDelegateAtten_non_amplifying`); VALUE and EVIDENCE legs are `Fpu.refl` off the
substrate frame; the STATE leg owns nothing. -/
theorem grant_is_fpu (k k' : RecordKernelState) (d r t : CellId) (keep : List Rights)
    (h : recKDelegateAtten k d r t keep = some k') (s0 : AssetId → ℤ) :
    Fpu (R := Sub4 k.accounts s0)
      ((.mk (some k.bal) 0),
       (.mk (some ⟨confRights (heldCapTo k.caps d t)⟩) 0),
       (.mk (some ⟨k.nullifiers.toFinset⟩) 0),
       Heap.emp)
      ((.mk (some k'.bal) 0),
       (.mk (some ⟨confRights (heldCapTo k.caps d t)⟩)
            ⟨confRights (attenuate keep (heldCapTo k.caps d t))⟩),
       (.mk (some ⟨k'.nullifiers.toFinset⟩) 0),
       Heap.emp) := by
  obtain ⟨hbal, hnul, _⟩ := recKDelegateAtten_substrate_frame k k' d r t keep h
  refine fpu_prod ?_ (fpu_prod (grant_authority_fpu k.caps d t keep) (fpu_prod ?_ (Fpu.refl _)))
  · rw [hbal]; exact Fpu.refl _
  · rw [hnul]; exact Fpu.refl _

/-- **`write_is_fpu` — the verb `write` in the product.** The STATE leg is the points-to
Fpu on the written slot (§8); VALUE/AUTHORITY/EVIDENCE legs are `Fpu.refl` off the
`writeField` factoring (`stateStep_factors`): the guarded write edits ONLY `cell`. -/
theorem write_is_fpu (s s' : RecChainedState) (f : FieldName) (actor target : CellId)
    (n : Int) (h : stateStepGuarded s f actor target n = some s') (s0 : AssetId → ℤ) :
    Fpu (R := Sub4 s.kernel.accounts s0)
      ((.mk (some s.kernel.bal) 0),
       (.mk (some ⟨confRights (heldCapTo s.kernel.caps actor target)⟩) 0),
       (.mk (some ⟨s.kernel.nullifiers.toFinset⟩) 0),
       Heap.single (target, f) (.ex (slotVal s.kernel target f)))
      ((.mk (some s'.kernel.bal) 0),
       (.mk (some ⟨confRights (heldCapTo s'.kernel.caps actor target)⟩) 0),
       (.mk (some ⟨s'.kernel.nullifiers.toFinset⟩) 0),
       Heap.single (target, f) (.ex (slotVal s'.kernel target f))) := by
  obtain ⟨_, hs'⟩ := stateStep_factors (stateStepGuarded_eq h)
  have hbal : s'.kernel.bal = s.kernel.bal := by rw [hs']; rfl
  have hcaps : s'.kernel.caps = s.kernel.caps := by rw [hs']; rfl
  have hnul : s'.kernel.nullifiers = s.kernel.nullifiers := by rw [hs']; rfl
  refine fpu_prod ?_ (fpu_prod ?_ (fpu_prod ?_ (Heap.write_fpu _ _ _)))
  · rw [hbal]; exact Fpu.refl _
  · rw [hcaps]; exact Fpu.refl _
  · rw [hnul]; exact Fpu.refl _

/-- **`spend_is_fpu` — bonus: the evidence verb (`shield`'s ledger half) in the
product.** The EVIDENCE leg grows (§7); everything else is `Fpu.refl` off
`noteSpendNullifier`'s record-update frame. -/
theorem spend_is_fpu (k k' : RecordKernelState) (nf : Nat)
    (h : noteSpendNullifier k nf = some k') (s0 : AssetId → ℤ) :
    Fpu (R := Sub4 k.accounts s0)
      ((.mk (some k.bal) 0),
       (.mk (some ⟨confRights (heldCapTo k.caps 0 0)⟩) 0),
       (.mk (some ⟨k.nullifiers.toFinset⟩) 0),
       Heap.emp)
      ((.mk (some k'.bal) 0),
       (.mk (some ⟨confRights (heldCapTo k'.caps 0 0)⟩) 0),
       (.mk (some ⟨k'.nullifiers.toFinset⟩) 0),
       Heap.emp) := by
  have hframe : k'.bal = k.bal ∧ k'.caps = k.caps := by
    unfold noteSpendNullifier at h
    by_cases hin : nf ∈ k.nullifiers
    · rw [if_pos hin] at h; exact absurd h (by simp)
    · rw [if_neg hin] at h; simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩
  obtain ⟨hbal, hcaps⟩ := hframe
  refine fpu_prod ?_ (fpu_prod ?_ (fpu_prod (spend_evidence_fpu k k' nf h) (Fpu.refl _)))
  · rw [hbal]; exact Fpu.refl _
  · rw [hcaps]; exact Fpu.refl _

/-- **PRODUCT NON-VACUITY.** A single bad substance kills the whole product verb: an
amplifying authority leg embedded among perfectly idle legs is NOT a product Fpu.
(The product schema inherits every corner's tooth — `not_fpu_prod_left` composed with
§6's witness.) -/
theorem amplified_product_not_fpu (acc : Finset CellId) (L : Ledger) :
    ¬ Fpu (R := Sub4 acc (supply acc L))
        ((.mk (some L) 0),
         (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) 0),
         (.mk (some ⟨(∅ : Finset Nat)⟩) 0),
         Heap.emp)
        ((.mk (some L) 0),
         (.mk (some ⟨{Dregg2.Authority.Auth.read}⟩) ⟨{Dregg2.Authority.Auth.write}⟩),
         (.mk (some ⟨(∅ : Finset Nat)⟩) 0),
         Heap.emp) := by
  intro hF
  apply amplifying_grant_not_fpu
  intro fr hv
  have := hF ((.mk none 0), fr, (.mk none 0), Heap.emp)
    ⟨by simp only [ResourceAlgebra.op, ResourceAlgebra.valid, SAuth.op, SAuth.valid],
     hv,
     by
       simp only [ResourceAlgebra.op, ResourceAlgebra.valid, Auth.op, Auth.valid]
       rw [add_zero, USet.fits_iff]
       simp,
     fun l e he => by
       have he' : (none : Option (Excl Int)) = some e := he
       simp at he'⟩
  exact this.2.1

/-! ## §LEDGER — the honest escape-hatch census + verdict.

### Escape hatches (formulation needs that are NOT camera-validity), counted:

**E1 — VALUE: the supply constant is PARAMETRIC.** Conservation enters the camera only
through `valid (● L) := supply acc L = s₀`, and BOTH parameters are constituted outside
the algebra: `acc` (the live-account index set — the ℤ ledger is not finitely supported,
so the measure must be told where to sum) and `s₀` (the genesis supply). The probe's
§2 negative theorems prove this is FORCED, not lazy: over the kernel's actual ℤ carrier
the order-validity is VACUOUS (`int_auth_fpu_vacuous`), and even over ℕ the order admits
the coordinated mint (`nat_auth_coordinated_mint_fpu` — Iris's `auth_update_alloc`), so
NO order-shaped `valid` yields Fpu ⇒ Σδ=0. DREGG3 R2 (AssetId := issuer cell, issuer
carries −supply) makes `s₀ = 0` canonical and the issuer the authoritative element —
exactly the Iris-bank shape — dissolving this hatch. **Verdict-relevant: value unifies
CONDITIONALLY on R2.**

**E2 — STATE: the GUARD is invisible to the camera (proved, `camera_blind_to_caveats`).**
The heap camera carries the frame rule (ownership-exclusivity: `write_fpu` /
`alloc_unowned_not_fpu`), and that half is genuine. But `caveatsAdmit` + `stateAuthB` +
lifecycle — the "guarded" half of the guarded-heap substance — are admission
preconditions OUTSIDE camera validity: the kernel fails closed where the camera blesses.
Iris concurs (guards live in Hoare preconditions, not the RA). **The Fpu schema does NOT
subsume the guard-theorem family** (`stateStepGuarded_caveat_violation_fails`,
`*_rejects_*`, `authorizedB`-gating stay their own family).

### Findings that are NOT counted as escapes (with reasons):

**F3 — footprint-indexing.** The product elements are the VERB'S FOOTPRINT (the
fragment/bound the actor owns: src/dst rows, the delegator's held cap, the written
slot), not a verb-independent projection of the global state. Not counted: this is the
universal Fpu usage pattern (one updates what one owns) — but it does mean R1's slogan
must be read as "every verb is an Fpu *of its footprint*", not "of a uniform state
image".

**F4 — instantiation gaps in the existing frame lemmas.** `recKDelegateAtten_frame`
pins `recTotal/accounts/cell` but not `bal`/`nullifiers`; filled here by a one-step
unfold (`recKDelegateAtten_substrate_frame`). A missing lemma, not a semantic hatch.

**F5 — the nonce question (the task's hint), answered.** This kernel's `move`
(`recKExecAsset`) ticks NO nonce — its footprint is purely VALUE; the anticipated
value×state interaction term does not arise. The analog that DOES arise is the receipt
log (`st'.log = t :: st.log`), and it is EVIDENCE-shaped (grow-only) — a monotone leg,
not an interaction term. So the hint's conjecture holds in spirit: the would-be hatch
dissolves into the monotone substance.

**F6 — two substances, ONE camera.** Authority and evidence are the SAME in-tree `Auth`
camera over `∪`-monoids (`USet`), with non-amplification = fragment-mint-within-bound
(via the IN-TREE `conservation_is_fpu` — Resource.lean:319's "one law" promise, cashed)
and monotonicity = authoritative growth (`auth_grow_fpu`). Better unification than R1
hoped for these two.

**F7 — step-indexing did NOT leak in.** The discrete RA tier (`Resource.lean`) sufficed
for all of S0; `StepCamera.lean` was not needed (no higher-order/recursive resources
appear in the three verbs).

### Non-vacuity witnesses (every camera bites):
  value     — `mint_not_value_fpu` (a conservation-violating move is NOT Fpu)
  authority — `amplifying_grant_not_fpu` (granting `write` under a `read` bound)
  evidence  — `forget_evidence_not_fpu` (erasing a known nullifier)
  state     — `Heap.alloc_unowned_not_fpu` (writing a slot one does not own)
  product   — `amplified_product_not_fpu` (one bad leg kills the verb)
  and the deliberately-exhibited vacuities: `int_auth_fpu_vacuous`,
  `trivial_valid_forgets_monotonicity`, `nat_auth_coordinated_mint_fpu`.

### VERDICT (DREGG3 §6 R1): **PARTIAL — 2 escape hatches (E1, E2), strongly positive.**

All four substances admit real, non-vacuous camera formulations, and the three verb
instances + spend ARE one product-Fpu schema instantiated from the EXISTING theorems
(conservation spine, attenuation gate, write factoring). But the claim as worded does
not pass clean:
  * conservation collapses into Fpu-validity only with the supply constant inside
    `valid` — parametric TODAY, canonical only after R2 (E1). Sequence R2 before
    declaring the one-gate.
  * the guard family (caveats/authority/lifecycle admission) provably CANNOT collapse
    into the schema (E2) — it remains its own theorem family, which DREGG3 §2.2's `Pred`
    (preconditions, Hoare-style) already anticipates structurally.
So: keep the Fpu schema as the FRAME/no-amplification/monotonicity gate (it
unifies those three — one theorem shape, four carriers, two of them literally one
camera), and keep admission-guards as the second, separate gate. The DREGG3 §2 skeleton
should say "two gates" (Fpu + admission), not one. -/

/-! ## §WITNESS — executable shadows of the non-vacuity facts (`#guard`, they run). -/

-- A transfer leaves the supply FIXED (the executable shadow of `move_value_fpu`):
#guard supply {0, 1} (recTransferBal (fun _ _ => (5 : ℤ)) 0 1 0 3) 0 == 10
-- ... and every other asset column is untouched:
#guard supply {0, 1} (recTransferBal (fun _ _ => (5 : ℤ)) 0 1 0 3) 7 == 10
-- A mint RAISES it — the camera-invalidating event of `mint_not_value_fpu`:
#guard supply {0, 1} (mintBal (fun _ _ => (5 : ℤ)) 1 0 3) 0 == 13
-- The attenuated grant's rights sit INSIDE the held bound (`grant_authority_fpu`'s hmono):
#guard decide (confRights (attenuate [Dregg2.Authority.Auth.read]
    (Dregg2.Authority.Cap.endpoint 7 [Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write]))
  ⊆ confRights (Dregg2.Authority.Cap.endpoint 7
      [Dregg2.Authority.Auth.read, Dregg2.Authority.Auth.write]))
-- ... and the AMPLIFYING pair of `amplifying_grant_not_fpu` does NOT:
#guard decide (¬ ({Dregg2.Authority.Auth.write} : Finset Rights) ⊆ {Dregg2.Authority.Auth.read})

/-! ## §AXIOMS — hygiene tripwires (whitelist: propext, Classical.choice, Quot.sound). -/

#assert_axioms fpu_prod
#assert_axioms not_fpu_prod_left
#assert_axioms auth_local_update_fpu
#assert_axioms auth_grow_fpu
#assert_axioms int_auth_fpu_vacuous
#assert_axioms nat_auth_coordinated_mint_fpu
#assert_axioms nat_frag_mint_not_fpu
#assert_axioms USet.fits_iff
#assert_axioms SAuth.preserve_fpu
#assert_axioms SAuth.break_not_fpu
#assert_axioms move_value_fpu
#assert_axioms mintBal_supply
#assert_axioms mint_not_value_fpu
#assert_axioms grant_authority_fpu
#assert_axioms grant_confines
#assert_axioms amplifying_grant_not_fpu
#assert_axioms spend_evidence_fpu
#assert_axioms forget_evidence_not_fpu
#assert_axioms trivial_valid_forgets_monotonicity
#assert_axioms Heap.write_fpu
#assert_axioms Heap.alloc_unowned_not_fpu
#assert_axioms write_state_fpu
#assert_axioms write_state_frame
#assert_axioms camera_blind_to_caveats
#assert_axioms move_is_fpu
#assert_axioms recKDelegateAtten_substrate_frame
#assert_axioms grant_is_fpu
#assert_axioms write_is_fpu
#assert_axioms spend_is_fpu
#assert_axioms amplified_product_not_fpu

end Dregg2.Substrate.FpuProbe
