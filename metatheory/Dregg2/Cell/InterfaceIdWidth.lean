/-
# Dregg2.Cell.InterfaceIdWidth — the felt-width binding of a cell's `interface_id`.

**What this proves, and why it was missing.** `cell/src/interface.rs::compute_interface_id` is the
content-address of a typed interface: the sorted-Poseidon2 fold over the per-method 8-felt leaf
digests. At HEAD it is a FULL eight-felt fold end-to-end (`hash_many_8` at every step, arity-seeded,
`digest8_to_bytes32` tail) — the Rust widening ALREADY LANDED. But there was NO Lean model and NO
formal proof: that the pre-widening ONE-felt encoding was genuinely forgeable, that the deployed wide
fold closes it, or that the "widen only the final squeeze" launder the wide primitive warns against is
really broken. `docs/WOUND-felt-width-boundaries-2026-07-19.md` #12 flagged it "NO Lean model and NO
wide twin"; the "no wide twin" half is now STALE (the wide fold exists), and this module supplies the
missing formal content.

The shared object is the SORTED list of per-method eight-felt leaf digests (`MethodSig::leaf_digest8`,
faithful to `[BabyBear; 8]`). It is modeled at felt resolution (`Digest8 := Fin 8 → Felt`, `Felt := ℤ`
as in `Dregg2.Distributed.FinalityCertWidth`), with the wide hash `hash8 : List Felt → Digest8`
standing for `dregg_circuit::poseidon2::hash_many_8`. The deployed fold is

  * seed `acc8 = hash8 [domainTag, len]`   (the `0x1FACE` domain tag + the leaf count),
  * step `acc8 = hash8 (acc8 ‖ leaf8)`      (16 felts in, per SORTED leaf),
  * tail `digest8_to_bytes32 acc8`          (injective packing — kept as the wide `Digest8` here).

and we prove, as theorems over ALL inputs:

  * **THE FALSIFIER (`narrow_conflates`, `narrow_colliding_interfaces_share_vk`).** The pre-widening
    encoding squeezed each leaf to its lane-0 felt (`~31 bits`). Modeled as `narrowLeaf d = d 0`, ANY
    such one-felt scheme `nid` gives the SAME id to two DISTINCT leaf sets that agree only on lane 0 —
    and since a service-factory VK is `derive_service_factory_vk(interface_id, mode)` (a function of
    the id), those two distinct interfaces SHARE a factory VK. This is the wound's stated harm.
  * **THE FIX, sound (`wideId_injective`, `wide_separates`).** Under the wide hash's collision-
    resistance floor (`Function.Injective hash8`, the honest named hypothesis, NOT an axiom), the
    deployed eight-felt fold is INJECTIVE in the leaf list: distinct method sets get distinct ids, so
    the lane-0 collision closes. It SEPARATES exactly the two sets the narrow scheme conflated.
  * **THE ANTI-LAUNDER (`finalSqueezeOnly_still_conflates`).** Widening ONLY the final squeeze over
    the narrow (lane-0) leaves — `hash8 (leaves.map narrowLeaf)` — STILL conflates them. The fold must
    be eight-felt END TO END (`hash_many_8` at every step), not merely at the tail; the launder the
    wide primitive names is proved broken.
  * **THE ARITY TOOTH (`seed_arity_injective`).** The `len`-seed binds the leaf count, so `{a}` and
    `{a, a}` get distinct seeds under the floor.

**Byte-safe / posture.** The deployed `compute_interface_id` is NOT touched; this is the machine-
checked proof that the (landed) widening is correct and the narrow encoding it replaced was genuinely
broken. The wide-hash collision-resistance floor is a NAMED hypothesis (the same posture
`Market.WideCommitBoundary` takes for its `Poseidon2SpongeCR` receipt sponge), inheriting the deployed
Poseidon2 collision floor — not discharged here.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Cell.InterfaceIdWidth`.
-/
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic
import Dregg2.Tactics

set_option autoImplicit false

namespace Dregg2.Cell.InterfaceIdWidth

/-! ## 1. The wide leaf digest — felt resolution. -/

/-- One field lane, modeled by its canonical `as_u32()` value (as in `FinalityCertWidth`). The
BabyBear range prices the offline grind (~2^15.5 birthday on one felt) but is irrelevant to the fold's
injectivity, so a lane stays an integer. -/
abbrev Felt : Type := ℤ

/-- A per-method leaf digest — faithful to `MethodSig::leaf_digest8 : [BabyBear; 8]`. -/
abbrev Digest8 : Type := Fin 8 → Felt

/-- The `0x1FACE` domain tag `compute_interface_id` seeds the fold with. -/
def domainTag : Felt := 0x1FACE

/-! ## 2. The deployed eight-felt fold (`compute_interface_id`). -/

/-- One fold step — `acc8 = hash_many_8(acc8 ‖ leaf8)`, sixteen felts in. -/
def stepOf (hash8 : List Felt → Digest8) (acc leaf : Digest8) : Digest8 :=
  hash8 (List.ofFn acc ++ List.ofFn leaf)

/-- The fold seed — `hash_many_8([0x1FACE, len])`, the domain tag plus the leaf count. -/
def seedOf (hash8 : List Felt → Digest8) (n : ℕ) : Digest8 :=
  hash8 [domainTag, (n : Felt)]

/-- The deployed interface-id fold (kept as the wide `Digest8`; the `digest8_to_bytes32` tail is an
injective packing, so it carries the same collision floor). -/
def wideId (hash8 : List Felt → Digest8) (leaves : List Digest8) : Digest8 :=
  List.foldl (stepOf hash8) (seedOf hash8 leaves.length) leaves

/-! ## 3. Step-level facts under the wide hash's collision-resistance floor. -/

/-- Each fold step is JOINTLY injective in `(acc, leaf)` — under `hash8` injective, equal steps force
equal accumulators AND equal leaves (both preimage halves are exactly eight felts, so the append
splits uniquely). -/
theorem stepOf_inj (hash8 : List Felt → Digest8) (hInj : Function.Injective hash8)
    {a b x y : Digest8} (h : stepOf hash8 a x = stepOf hash8 b y) : a = b ∧ x = y := by
  have h' : hash8 (List.ofFn a ++ List.ofFn x) = hash8 (List.ofFn b ++ List.ofFn y) := h
  have h2 : List.ofFn a ++ List.ofFn x = List.ofFn b ++ List.ofFn y := hInj h'
  have hlen : (List.ofFn a).length = (List.ofFn b).length := by
    rw [List.length_ofFn, List.length_ofFn]
  obtain ⟨hab, hxy⟩ := List.append_inj h2 hlen
  exact ⟨List.ofFn_inj.mp hab, List.ofFn_inj.mp hxy⟩

/-- The seed is NEVER in the range of a step — its preimage is two felts, a step's is sixteen, so under
`hash8` injective they cannot collide. This is the arity separation the `len`-seed buys at the fold
boundary. -/
theorem seedOf_ne_stepOf (hash8 : List Felt → Digest8) (hInj : Function.Injective hash8)
    (n : ℕ) (a x : Digest8) : seedOf hash8 n ≠ stepOf hash8 a x := by
  intro h
  have h' : hash8 [domainTag, (n : Felt)] = hash8 (List.ofFn a ++ List.ofFn x) := h
  have h2 : [domainTag, (n : Felt)] = List.ofFn a ++ List.ofFn x := hInj h'
  have hcontra := congrArg List.length h2
  simp only [List.length_cons, List.length_nil, List.length_append, List.length_ofFn] at hcontra
  omega

/-! ## 4. The generic fold-injectivity engine. -/

/-- A `foldl` whose step is jointly injective and whose seed is never a step output is injective in the
LIST — even across different lengths (the empty-vs-nonempty gap is exactly where `seed ≠ step` bites).
The `seed`-domain hypotheses keep the base accumulator a seed through the whole right-to-left peel. -/
theorem foldl_step_inj {D L : Type*} (step : D → L → D) (seed : ℕ → D)
    (hstep : ∀ {a b : D} {x y : L}, step a x = step b y → a = b ∧ x = y)
    (hns : ∀ (n : ℕ) (a : D) (x : L), seed n ≠ step a x) :
    ∀ (xs ys : List L) (n m : ℕ),
      List.foldl step (seed n) xs = List.foldl step (seed m) ys → xs = ys := by
  intro xs
  induction xs using List.reverseRecOn with
  | nil =>
      intro ys n m h
      cases ys using List.reverseRecOn with
      | nil => rfl
      | append_singleton ys y =>
          rw [List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
          exact absurd h (hns n _ _)
  | append_singleton xs x ih =>
      intro ys n m h
      cases ys using List.reverseRecOn with
      | nil =>
          rw [List.foldl_nil, List.foldl_append, List.foldl_cons, List.foldl_nil] at h
          exact absurd h.symm (hns m _ _)
      | append_singleton ys y =>
          rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
              List.foldl_append, List.foldl_cons, List.foldl_nil] at h
          obtain ⟨hacc, hxy⟩ := hstep h
          rw [ih ys n m hacc, hxy]

/-- **THE FIX, sound (WIDENED-BINDING SOUNDNESS).** Under the wide hash's collision-resistance floor,
the deployed eight-felt interface-id fold is INJECTIVE in the leaf list: two method sets with the same
`interface_id` have the same sorted leaf list. The ~31-bit lane-0 collision the narrow encoding admitted
is gone. -/
theorem wideId_injective (hash8 : List Felt → Digest8) (hInj : Function.Injective hash8) :
    Function.Injective (wideId hash8) := by
  intro l l' h
  exact foldl_step_inj (stepOf hash8) (seedOf hash8)
    (fun hh => stepOf_inj hash8 hInj hh) (seedOf_ne_stepOf hash8 hInj) l l' l.length l'.length h

/-- The seed binds the leaf COUNT: distinct arities get distinct seeds under the floor, so `{a}` and
`{a, a}` cannot alias via the seed (the domain-tagged `len` word). -/
theorem seed_arity_injective (hash8 : List Felt → Digest8) (hInj : Function.Injective hash8)
    {n m : ℕ} (h : seedOf hash8 n = seedOf hash8 m) : n = m := by
  have h' : hash8 [domainTag, (n : Felt)] = hash8 [domainTag, (m : Felt)] := h
  have h2 : [domainTag, (n : Felt)] = [domainTag, (m : Felt)] := hInj h'
  have hn : (n : Felt) = (m : Felt) := (List.cons.inj (List.cons.inj h2).2).1
  exact_mod_cast hn

/-! ## 5. THE FALSIFIER — the pre-widening one-felt leaf conflates distinct method sets.

The pre-widening leaf was ONE ~31-bit felt (`MethodSig::leaf_digest8`'s docstring: "the pre-widening
leaf was ONE ~31-bit felt, birthday-collidable at ~2^15.5 by grinding method names"). Modeled as the
lane-0 projection `narrowLeaf d = d 0`, ANY one-felt scheme over `leaves.map narrowLeaf` is BLIND to
lanes 1..7 — so two leaf lists agreeing only on lane 0 collide. -/

/-- The pre-widening leaf squeeze — one felt (lane 0) of the eight-felt digest. -/
def narrowLeaf (d : Digest8) : Felt := d 0

/-- A concrete leaf (all lanes zero). -/
def leafZero : Digest8 := fun _ => 0

/-- A concrete leaf that agrees with `leafZero` on lane 0 but differs on lane 1 — the shape a ~2^15.5
grind buys. -/
def leafBumped : Digest8 := fun i => if i = 1 then 1 else 0

theorem narrowLeaf_leafBumped : narrowLeaf leafBumped = 0 := by
  simp only [narrowLeaf, leafBumped, if_neg (show (0 : Fin 8) ≠ 1 by decide)]

/-- The two leaves have the SAME lane-0 narrow squeeze (the pre-widening leaf conflates them): both
reduce to `[0]` — `leafBumped 0 = 0` because `(0 : Fin 8) ≠ 1`. -/
theorem leaves_narrow_collide :
    List.map narrowLeaf [leafZero] = List.map narrowLeaf [leafBumped] := rfl

/-- The two leaves are GENUINELY distinct (they differ at lane 1), so the method sets differ:
`leafZero 1 = 0` while `leafBumped 1 = 1`. -/
theorem leafZero_ne_leafBumped : leafZero ≠ leafBumped := by
  intro h
  have h1 : (0 : Felt) = 1 := congrFun h 1
  exact absurd h1 (by decide)

/-- Hence the two singleton method sets are distinct lists. -/
theorem lists_distinct : ([leafZero] : List Digest8) ≠ [leafBumped] := by
  intro h
  exact leafZero_ne_leafBumped (List.cons.inj h).1

/-- **THE FALSIFIER.** ANY pre-widening one-felt (lane-0) interface-id scheme `nid` gives the SAME id
to two DISTINCT method-leaf sets — the ~31-bit conflation, over all inputs. -/
theorem narrow_conflates {α : Type*} (nid : List Felt → α) :
    ∃ l l' : List Digest8, l ≠ l' ∧ nid (l.map narrowLeaf) = nid (l'.map narrowLeaf) :=
  ⟨[leafZero], [leafBumped], lists_distinct, by rw [leaves_narrow_collide]⟩

/-- The whole-set narrow interface id: a one-felt scheme applied to the squeezed leaves. -/
def narrowId {α : Type*} (nid : List Felt → α) (leaves : List Digest8) : α :=
  nid (leaves.map narrowLeaf)

/-- **THE DOWNSTREAM HARM (`derive_service_factory_vk`).** A factory VK is
`derive_service_factory_vk(interface_id, mode)` — a function of the id — so two interfaces sharing a
(narrow) id share a factory VK. Composed with `narrow_conflates`: the pre-widening scheme lets two
DISTINCT method sets share ONE service-factory VK (the wound's "colliding interfaces share a VK"). -/
theorem narrow_colliding_interfaces_share_vk {α M V : Type*}
    (nid : List Felt → α) (deriveVK : α → M → V) (mode : M) :
    ∃ l l' : List Digest8, l ≠ l' ∧
      deriveVK (narrowId nid l) mode = deriveVK (narrowId nid l') mode := by
  obtain ⟨l, l', hne, hid⟩ := narrow_conflates nid
  exact ⟨l, l', hne, by rw [narrowId, narrowId, hid]⟩

/-- **THE FIX bites the specific pair.** The deployed eight-felt fold SEPARATES exactly the two leaf
sets the narrow scheme conflated (distinct lists → distinct ids, under the floor). -/
theorem wide_separates (hash8 : List Felt → Digest8) (hInj : Function.Injective hash8) :
    wideId hash8 [leafZero] ≠ wideId hash8 [leafBumped] :=
  fun h => lists_distinct (wideId_injective hash8 hInj h)

/-! ## 6. THE ANTI-LAUNDER — final-squeeze-only widening is still broken. -/

/-- **ANTI-LAUNDER.** Widening ONLY the final squeeze over the narrow (lane-0) leaves —
`hash8 (leaves.map narrowLeaf)` — STILL conflates the two distinct sets: the wide tail cannot recover
information the leaves already dropped. The fold must be eight-felt END TO END (`hash_many_8` at every
step, the deployed discipline), not merely at the tail. This is the launder `MethodSig::leaf_digest8`
and the `WideCommitBoundary` warn against, proved broken. -/
theorem finalSqueezeOnly_still_conflates (hash8 : List Felt → Digest8) :
    ∃ l l' : List Digest8, l ≠ l' ∧
      hash8 (l.map narrowLeaf) = hash8 (l'.map narrowLeaf) :=
  ⟨[leafZero], [leafBumped], lists_distinct, by rw [leaves_narrow_collide]⟩

/-! ## 7. NON-VACUITY — the collision and the distinctness FIRE on concrete leaves. -/

-- The two leaves have byte-identical lane-0 narrow squeezes (the pre-widening conflation) …
#guard narrowLeaf leafZero == narrowLeaf leafBumped
-- … while being genuinely distinct digests (so the method sets differ) …
#guard decide (leafZero = leafBumped) == false
-- … and the squeezed leaf lists collide …
#guard decide (List.map narrowLeaf [leafZero] = List.map narrowLeaf [leafBumped])
-- … but the underlying singleton method sets do not.
#guard decide (([leafZero] : List Digest8) = [leafBumped]) == false

/-! ## 8. Axiom hygiene. -/

#assert_axioms stepOf_inj
#assert_axioms seedOf_ne_stepOf
#assert_axioms foldl_step_inj
#assert_axioms wideId_injective
#assert_axioms seed_arity_injective
#assert_axioms narrow_conflates
#assert_axioms narrow_colliding_interfaces_share_vk
#assert_axioms wide_separates
#assert_axioms finalSqueezeOnly_still_conflates

end Dregg2.Cell.InterfaceIdWidth
