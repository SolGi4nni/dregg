/-
# Dregg2.Crypto.HandlebarsGuardedUniqueness — the INVERSE, guard-PARAMETRIC.

`HandlebarsGuarded.lean` proves GENERATION SOUNDNESS guard-parametrically (`guarded_render_mem_language`
— per-hole data satisfying its OWN guard renders into the induced language) and names, in its §7
residual, the guard-parametric INVERSE as the next slice: *unique data recovery* — recover WHICH
per-hole data produced a given output. This module lands that inverse, as a STRUCTURAL PROPERTY OF THE
GUARDS.

## The honest restriction (stated plainly — general-guard uniqueness is FALSE)

`HandlebarsUniqueness.lean` chipped the inverse for a hardcoded *delimiter-guarded* class over the
2-symbol `Tok` alphabet: holes carrying the `NoBrace` (brace-free) guard, separated by single-`{`
literals. That class is ONE point of a general phenomenon. The inverse **cannot** hold for arbitrary
guards: two abutting `star any` holes split `[x, y]` many ways (`abutting_ambiguous`, §7), so render is
genuinely NOT injective there. The reachable, honest home of the inverse is a **structural condition on
the guards**, not a global content ban.

## The separation condition (`Excludes` / `Separated`)

A guard `g` **EXCLUDES** a symbol `c` (`Excludes g c`) when NO `g`-satisfying word contains `c`
(`∀ w, derives w g = true → Absent c w`, decided by the VERIFIED matcher). A `GuardedTemplate` is a
**SEPARATED-guards spine** (`SepSpine` / `Separated`) when it is an alternation

    hole g₀ · lit[c₀] · hole g₁ · lit[c₁] · … · lit[cₙ₋₁] · hole gₙ

of holes and SINGLE-symbol delimiter literals, where each non-final hole's guard `gᵢ` **excludes its
following delimiter symbol** `cᵢ`. Then a hole's data can never bleed into the delimiter that follows
it: the first `cᵢ` in the output sits exactly at the hole boundary, so the split — and hence each
hole's data — is FORCED. This is the guard-structure generalization of `HandlebarsUniqueness`'s
`brace_split_unique`.

## What is proven (no `sorry`; the general wall stays honest)

* `split_unique` — the core: a `c`-free prefix before the first `c` is unique (generic `c : Value`).
* `guarded_render_injective` — THE KEY THEOREM: for a `SeparatedTemplate T`, `guardedSafe T d`,
  `guardedSafe T d'`, `render T d = render T d'` forces `d h = d' h` on every hole `h` of `T`.
  Unique data recovery, guard-parametric — generalizing `HandlebarsUniqueness.delim_render_injective`
  from the hardcoded `{brace,data}` / `NoBrace` class to an ARBITRARY separated-guard class. The
  existence half rides `HandlebarsGuarded.guarded_render_mem_language`.
* `noBraceRE_excludes` + `braceSpine_render_injective` — SUBSUMPTION: the brace-free guard `noBraceRE`
  excludes `braceVal`, so a spine of brace-free holes `{`-separated is a `SeparatedTemplate`. The old
  delimiter-guarded class is the COARSEST instance. (`noDoubleBraceRE` is NOT separated — it permits a
  lone brace — which is exactly why `HandlebarsUniqueness` strengthened to `NoBrace`; §5.)
* `Demo` — a separated spine with TWO DIFFERENT guards (`noBraceRE` and `star any`); distinct data →
  distinct outputs (`demo_distinct`). `abutting_ambiguous` (§7) exhibits the honest wall: two abutting
  permissive holes, distinct data, SAME output — WHY the side-condition is needed.
-/
import Dregg2.Crypto.HandlebarsGuarded
import Dregg2.Crypto.Deriv.Correctness
import Dregg2.Crypto.Segmentation
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsGuardedUniqueness

open Dregg2.Exec
open Dregg2.Exec.PredAlgebra
open Dregg2.Crypto
open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE
open Dregg2.Crypto.HandlebarsGuarded

/-! ## §1 `Absent` and the split-uniqueness core — a `c`-free prefix before the first `c` is unique.

`Absent c w` — `w` contains no symbol equal to `c` (structural, decidable). `split_unique` is the
guard-parametric generalization of `HandlebarsUniqueness.brace_split_unique`: the delimiter `c` cannot
occur inside a `c`-free prefix, so it is located identically in both decompositions. -/

/-- **`Absent c w`** — the symbol `c` does not occur in `w` (a `c`-free word). The delimiter-role
condition: a hole whose data is `Absent c` cannot emit the delimiter `c`. -/
def Absent (c : Value) : List Value → Prop
  | []       => True
  | a :: rest => a ≠ c ∧ Absent c rest

/-- **`guarded_absent_iff`** — the guard bridge: this module's `Absent c w` is propositionally
`Segmentation.Absent c w` (distinct equation-compiler fixpoints, so NOT `rfl`; by induction on the
word). -/
theorem guarded_absent_iff (c : Value) : ∀ w, Absent c w ↔ Segmentation.Absent c w
  | [] => Iff.rfl
  | _ :: rest => and_congr Iff.rfl (guarded_absent_iff c rest)

/-- **`split_unique`** — if `x ++ c :: s = y ++ c :: t` with `x`, `y` both `c`-free (`Absent c`), then
`x = y` and `s = t`. The load-bearing uniqueness step, generic in the delimiter symbol `c`: the
delimiter `c` cannot occur inside a `c`-free prefix, so it is located identically in both
decompositions. Generalizes `HandlebarsUniqueness.brace_split_unique` (`c := Tok.brace`). Instance of
`Segmentation.split_unique_generic` at `α := Value` via the `guarded_absent_iff` bridge. -/
theorem split_unique (c : Value) :
    ∀ (x y s t : List Value), Absent c x → Absent c y →
      x ++ c :: s = y ++ c :: t → x = y ∧ s = t :=
  fun x y s t hx hy h =>
    Segmentation.split_unique_generic c x y s t
      ((guarded_absent_iff c x).mp hx) ((guarded_absent_iff c y).mp hy) h

/-! ## §2 The separation primitive — a guard `EXCLUDES` a symbol. -/

/-- **`Excludes g c`** — no `g`-satisfying word contains the symbol `c`, decided by the VERIFIED
matcher `derives`. This is the guard-structure content the inverse needs: a hole guarded by `g` can
never emit `c`, so a following `c`-delimiter marks an unambiguous boundary. -/
def Excludes (g : PredRE) (c : Value) : Prop :=
  ∀ w, derives w g = true → Absent c w

/-! ## §3 The separated-guards spine — holes interleaved with single-symbol delimiters. -/

/-- **`SepSpine`** — a separated-guards normal form: a non-empty chain of holes, each (but the last)
carrying a guard and a SINGLE-symbol delimiter to the next. `cons id g c rest` reads
`hole id (guard g) · lit[c] · <rest>`. -/
inductive SepSpine where
  /-- The final hole. -/
  | last (id : Nat) (g : PredRE)
  /-- A hole `id` guarded by `g`, then a single-symbol delimiter `c`, then the rest of the spine. -/
  | cons (id : Nat) (g : PredRE) (c : Value) (rest : SepSpine)

/-- The spine's segments (the `GuardedTemplate` shape): holes separated by single-symbol literals. -/
def spineSegs : SepSpine → List GSeg
  | .last id g      => [GSeg.hole id g]
  | .cons id g c rest => GSeg.hole id g :: GSeg.lit [c] :: spineSegs rest

/-- **`spineTemplate s`** — the spine as a `GuardedTemplate` (what `render`/`guardedSafe` act on). -/
def spineTemplate (s : SepSpine) : GuardedTemplate := ⟨spineSegs s⟩

/-- The hole-ids named by the spine, in order. -/
def spineHoles : SepSpine → List Nat
  | .last id _      => [id]
  | .cons id _ _ rest => id :: spineHoles rest

/-- **`Separated s`** — the SEPARATED-GUARDS side-condition: every non-final hole's guard EXCLUDES the
delimiter symbol that follows it. Under this condition the parse is unique (§4). -/
def Separated : SepSpine → Prop
  | .last _ _       => True
  | .cons _ g c rest => Excludes g c ∧ Separated rest

/-! ### `holesOf` for a `GuardedTemplate` (the hole-ids of its segments). -/

/-- The hole-ids of a segment list (literals filtered out). -/
def holeIds : List GSeg → List Nat
  | []                => []
  | GSeg.lit _ :: rest  => holeIds rest
  | GSeg.hole id _ :: rest => id :: holeIds rest

/-- **`holesOf T`** — the hole-ids `T` names, in order. -/
def holesOf (T : GuardedTemplate) : List Nat := holeIds T.segments

/-- `holesOf` of a spine recovers exactly its hole-id list (the delimiters are filtered out). -/
theorem holesOf_spine : ∀ s : SepSpine, holesOf (spineTemplate s) = spineHoles s
  | .last id g => rfl
  | .cons id g c rest => by
      have ih := holesOf_spine rest
      simp only [holesOf, spineTemplate, spineSegs, holeIds, spineHoles] at ih ⊢
      rw [ih]

/-! ### Render shape — a spine renders as its hole data joined by the delimiters. -/

/-- Single-hole render: `render (spineTemplate (last id g)) d = d id`. -/
theorem render_spine_last (d : Nat → List Value) (id : Nat) (g : PredRE) :
    render (spineTemplate (.last id g)) d = d id := by
  simp only [render, spineTemplate, spineSegs, List.flatMap_cons, List.flatMap_nil,
    renderSeg, List.append_nil]

/-- Cons render: the first hole's data, the delimiter `c`, then the tail render. -/
theorem render_spine_cons (d : Nat → List Value) (id : Nat) (g : PredRE) (c : Value)
    (rest : SepSpine) :
    render (spineTemplate (.cons id g c rest)) d
      = d id ++ c :: render (spineTemplate rest) d := by
  simp only [render, spineTemplate, spineSegs, List.flatMap_cons, renderSeg,
    List.singleton_append]

/-! ## §4 THE KEY THEOREM — render injectivity / unique data recovery, guard-parametric.

The induction lives alphabet-generically in `Segmentation.spine_segment_unique`; the lemmas below
erase the guards to reach its `Spine` (`eraseGuards`), turn `Separated` + `guardedSafe` into
`Segmented` (via `Excludes` and the `guarded_absent_iff` bridge), and instantiate. -/

/-- The spine with its guards ERASED — the pure word-combinatorics skeleton that
`Segmentation.spine_segment_unique` acts on (guards enter only through `Segmented`, via
`Excludes`). -/
def eraseGuards : SepSpine → Segmentation.Spine Value
  | .last id _        => .last id
  | .cons id _ c rest => .cons id c (eraseGuards rest)

/-- Guard erasure preserves the named hole-ids. -/
theorem eraseGuards_holes : ∀ s : SepSpine,
    Segmentation.spineHoles (eraseGuards s) = spineHoles s
  | .last _ _ => rfl
  | .cons _ _ _ rest => by
      simp only [eraseGuards, Segmentation.spineHoles, spineHoles, eraseGuards_holes rest]

/-- Guard erasure preserves the render (guards do not print). -/
theorem eraseGuards_render (d : Nat → List Value) : ∀ s : SepSpine,
    Segmentation.spineRender d (eraseGuards s) = render (spineTemplate s) d
  | .last _ _ => by rw [render_spine_last]; rfl
  | .cons _ _ _ rest => by
      rw [render_spine_cons]
      simp only [eraseGuards, Segmentation.spineRender, eraseGuards_render d rest]

/-- `Separated` + `guardedSafe` make the erased spine `Segmented`: each non-final hole's guard
EXCLUDES its delimiter, and its data satisfies the guard, so the data is `Absent` the delimiter
(via the `guarded_absent_iff` bridge). -/
theorem eraseGuards_segmented (d : Nat → List Value) : ∀ s : SepSpine,
    Separated s → guardedSafe (spineTemplate s) d →
    Segmentation.Segmented d (eraseGuards s)
  | .last _ _, _, _ => trivial
  | .cons id g c rest, hsep, hsafe =>
      ⟨(guarded_absent_iff c _).mp
         (hsep.1 _ (hsafe id g (by simp [spineTemplate, spineSegs]))),
       eraseGuards_segmented d rest hsep.2 fun id' g' hm =>
         hsafe id' g' (by
           simp only [spineTemplate, spineSegs]
           exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))⟩

/-- The spine-form injectivity: for a `Separated` spine whose holes are guard-satisfied on both `d`,
`d'`, equal output forces equal data on every named hole. Instance of
`Segmentation.spine_segment_unique` on the guard-erased spine. Generalizes
`HandlebarsUniqueness.delim_render_injective_holes`. -/
theorem spine_render_injective_aux :
    ∀ (s : SepSpine), Separated s → ∀ (d d' : Nat → List Value),
      guardedSafe (spineTemplate s) d → guardedSafe (spineTemplate s) d' →
      render (spineTemplate s) d = render (spineTemplate s) d' →
      ∀ id ∈ spineHoles s, d id = d' id :=
  fun s hsep d d' hsafe hsafe' heq id hmem =>
    Segmentation.spine_segment_unique (eraseGuards s) d d'
      (eraseGuards_segmented d s hsep hsafe) (eraseGuards_segmented d' s hsep hsafe')
      (by rw [eraseGuards_render, eraseGuards_render]; exact heq)
      id (by rw [eraseGuards_holes]; exact hmem)

/-- **`SeparatedTemplate T`** — `T` is (equal to) a separated-guards spine. The precise home of the
inverse: an alternation of holes and single-symbol delimiter literals in which every non-final hole's
guard EXCLUDES its following delimiter. -/
def SeparatedTemplate (T : GuardedTemplate) : Prop :=
  ∃ s : SepSpine, T = spineTemplate s ∧ Separated s

/-- **`guarded_render_injective`** — THE KEY THEOREM: unique data recovery, guard-parametric. For a
`SeparatedTemplate T` whose holes carry guard-satisfied data on both `d` and `d'`, `render T d =
render T d'` forces `d h = d' h` for every hole `h` of `T`. This is the round-trip INVERSE,
load-bearing half; the existence half rides `HandlebarsGuarded.guarded_render_mem_language`. It
generalizes `HandlebarsUniqueness.delim_render_injective` from the hardcoded `{brace,data}` / `NoBrace`
class to an ARBITRARY separated-guard class — the honest home of the old delimiter ban is now a
STRUCTURAL PROPERTY OF THE GUARDS (`Excludes`), not a global content restriction. -/
theorem guarded_render_injective (T : GuardedTemplate) (hsep : SeparatedTemplate T)
    (d d' : Nat → List Value)
    (hsafe : guardedSafe T d) (hsafe' : guardedSafe T d')
    (heq : render T d = render T d') :
    ∀ h ∈ holesOf T, d h = d' h := by
  obtain ⟨s, rfl, hs⟩ := hsep
  rw [holesOf_spine]
  exact spine_render_injective_aux s hs d d' hsafe hsafe' heq

/-! ## §5 SUBSUMPTION — the old delimiter-guarded class is the COARSEST instance.

The brace-free guard `noBraceRE = neg (any* ⬝ brace ⬝ any*)` EXCLUDES `braceVal`, so a spine of
brace-free holes `{`-separated satisfies `Separated`. That is exactly `HandlebarsUniqueness`'s
delimiter-guarded class (holes `NoBrace`, single-`{` separators), now recognized as one instance of
`Excludes`. Note `HandlebarsGuarded.noDoubleBraceRE` is NOT separated — it permits a LONE brace
(`derives [braceVal] noDoubleBraceRE = true`), so it does not exclude `braceVal`; that is precisely why
`HandlebarsUniqueness` strengthened `NoDoubleBrace` to the brace-free `NoBrace`. -/

/-- `any* ⬝ brace ⬝ any*` — the "contains a brace frame" regex (`braceP` = the `HandlebarsGuarded`
brace-tag leaf). -/
def containsB : PredRE :=
  .cat (.star PredRE.any) (.cat (.sym braceP) (.star PredRE.any))

/-- **`noBraceRE`** — the brace-free guard `neg (any* ⬝ brace ⬝ any*)`: matches a word iff it holds
NO brace frame. This is the `PredRE` witness of `HandlebarsUniqueness.NoBrace`. -/
def noBraceRE : PredRE := .neg containsB

/-- `u` contains a frame firing `braceP`. -/
def hasB (u : List Value) : Prop :=
  ∃ p b s, u = p ++ b :: s ∧ leaf braceP b = true

/-- **`derives_containsB`** — the matcher decides `containsB` exactly as "contains a brace frame". -/
theorem derives_containsB (u : List Value) : derives u containsB = true ↔ hasB u := by
  unfold containsB
  rw [derives_cat]
  constructor
  · rintro ⟨w1, w2, hsplit, _, h2⟩
    rw [derives_cat] at h2
    obtain ⟨x1, x2, hs2, hb, _⟩ := h2
    rw [derives_sym] at hb
    obtain ⟨b, rfl, hlb⟩ := hb
    subst hs2
    exact ⟨w1, b, x2, hsplit.symm, hlb⟩
  · rintro ⟨p, b, s, hu, hlb⟩
    refine ⟨p, b :: s, hu.symm, derives_star_any p, ?_⟩
    rw [derives_cat]
    refine ⟨[b], s, rfl, ?_, derives_star_any s⟩
    rw [derives_sym]; exact ⟨b, rfl, hlb⟩

/-- The matcher decides `noBraceRE` as "no brace frame". -/
theorem noBraceRE_no_brace (u : List Value) :
    derives u noBraceRE = true ↔ ¬ hasB u := by
  simp only [noBraceRE, derives_neg]
  rw [← derives_containsB]
  cases derives u containsB <;> simp

/-- A word with no brace-firing frame does not contain a brace frame. -/
theorem nofire_no_hasB (w : List Value) (hf : ∀ b ∈ w, leaf braceP b = false) : ¬ hasB w := by
  rintro ⟨p, b, s, hs, hlb⟩
  have hb : b ∈ w := by rw [hs]; simp
  rw [hf b hb] at hlb
  simp at hlb

/-- `¬ hasB u → Absent braceVal u`: `braceVal` fires `braceP` (`leaf_braceP_brace`), so if `braceVal`
occurred in `u` it would witness `hasB u`. -/
theorem not_hasB_absent : ∀ (u : List Value), ¬ hasB u → Absent braceVal u
  | [],      _   => trivial
  | a :: as, hnb => by
      refine ⟨fun hEq => hnb ⟨[], a, as, rfl, ?_⟩, not_hasB_absent as (fun h => hnb ?_)⟩
      · rw [hEq]; exact leaf_braceP_brace
      · obtain ⟨p, b, s, hs, hlb⟩ := h
        exact ⟨a :: p, b, s, by simp [hs], hlb⟩

/-- **`noBraceRE_excludes`** — the brace-free guard EXCLUDES `braceVal`. The `PredRE` content of
`HandlebarsUniqueness.NoBrace`, lifted into the guard-structure condition `Excludes`. -/
theorem noBraceRE_excludes : Excludes noBraceRE braceVal :=
  fun w hw => not_hasB_absent w ((noBraceRE_no_brace w).mp hw)

/-- Convenience: a word with no brace-firing frame satisfies `noBraceRE` (the GENERATE-side check the
`guardedSafe` obligation needs on brace-free data). -/
theorem derives_noBraceRE_of_nofire (w : List Value)
    (hf : ∀ b ∈ w, leaf braceP b = false) : derives w noBraceRE = true :=
  (noBraceRE_no_brace w).mpr (nofire_no_hasB w hf)

/-- **`braceSpine id rest`** — the brace-free / `{`-separated spine over the hole-ids `id :: rest`:
every hole carries `noBraceRE`, every delimiter is `braceVal`. This is exactly the
`HandlebarsUniqueness` delimiter-guarded class, rebuilt in the guarded framework. -/
def braceSpine : Nat → List Nat → SepSpine
  | id, []     => .last id noBraceRE
  | id, h :: t => .cons id noBraceRE braceVal (braceSpine h t)

/-- Every brace-free `{`-separated spine is `Separated` (each non-final hole's `noBraceRE` guard
excludes the `braceVal` delimiter). So the old delimiter-guarded class IS an instance. -/
theorem braceSpine_separated : ∀ (id : Nat) (rest : List Nat), Separated (braceSpine id rest)
  | _, []     => trivial
  | _, _ :: t => ⟨noBraceRE_excludes, braceSpine_separated _ t⟩

/-- **`braceSpine_render_injective`** — `guarded_render_injective` on the old delimiter-guarded class:
brace-free holes, `{`-separated, equal output forces equal data. This is the guard-parametric
generalization of `HandlebarsUniqueness.delim_render_injective`, obtained by exhibiting the class as a
`SeparatedTemplate`. The tie to `HandlebarsUniqueness` itself (its `Tok`/`NoBrace` machinery) is a
NAMED residual (§6) — this module recovers the SAME theorem shape natively over `noBraceRE`/`braceVal`,
without importing the committed 2-symbol formulation. -/
theorem braceSpine_render_injective (id : Nat) (rest : List Nat)
    (d d' : Nat → List Value)
    (hsafe  : guardedSafe (spineTemplate (braceSpine id rest)) d)
    (hsafe' : guardedSafe (spineTemplate (braceSpine id rest)) d')
    (heq : render (spineTemplate (braceSpine id rest)) d
             = render (spineTemplate (braceSpine id rest)) d') :
    ∀ h ∈ holesOf (spineTemplate (braceSpine id rest)), d h = d' h :=
  guarded_render_injective _ ⟨braceSpine id rest, rfl, braceSpine_separated id rest⟩ d d' hsafe hsafe' heq

-- `noDoubleBraceRE` is NOT a separated guard: it permits a LONE brace, so it does NOT exclude
-- `braceVal`. `noBraceRE` (fully brace-free) does. THIS is why the inverse needs `NoBrace`, not
-- `NoDoubleBrace` — the separation condition names the difference precisely.
#guard derives [braceVal] noDoubleBraceRE            -- permissive guard admits a lone `{`
#guard ! derives [braceVal] noBraceRE                -- separated guard forbids it

/-! ## §6 Demo — a separated spine with TWO DIFFERENT guards; distinct data → distinct output. -/

namespace Demo

/-- `hole 0 (noBraceRE) · lit[{] · hole 1 (star any)`. TWO DIFFERENT guards: hole 0 is brace-free
(the delimiter-excluding guard that makes the parse unique), hole 1 is fully permissive (`star any`) —
its position is pinned by the preceding delimiter, so the spine stays separated. -/
def demoSpine : SepSpine := .cons 0 noBraceRE braceVal (.last 1 (PredRE.star PredRE.any))

/-- The spine is separated: hole 0's `noBraceRE` excludes the `braceVal` delimiter; the final hole is
unconstrained. -/
theorem demoSpine_separated : Separated demoSpine := ⟨noBraceRE_excludes, trivial⟩

/-- Assignment A: both holes a single `data` byte. -/
def demoDA : Nat → List Value
  | 0 => [dataVal]
  | 1 => [dataVal]
  | _ => []

/-- Assignment B: hole 0 is TWO `data` bytes — distinct data. -/
def demoDB : Nat → List Value
  | 0 => [dataVal, dataVal]
  | 1 => [dataVal]
  | _ => []

/-- Assignment A satisfies both guards (hole 0 brace-free, hole 1 permissive). -/
theorem demoDA_safe : guardedSafe (spineTemplate demoSpine) demoDA := by
  intro id g hmem
  simp only [spineTemplate, demoSpine, spineSegs, List.mem_cons, List.not_mem_nil, or_false,
    GSeg.hole.injEq, reduceCtorEq, false_or] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply derives_noBraceRE_of_nofire
    intro b hb; simp only [demoDA, List.mem_singleton] at hb; subst hb; exact leaf_braceP_data
  · exact derives_star_any _

/-- Assignment B satisfies both guards. -/
theorem demoDB_safe : guardedSafe (spineTemplate demoSpine) demoDB := by
  intro id g hmem
  simp only [spineTemplate, demoSpine, spineSegs, List.mem_cons, List.not_mem_nil, or_false,
    GSeg.hole.injEq, reduceCtorEq, false_or] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · apply derives_noBraceRE_of_nofire
    intro b hb
    simp only [demoDB, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact leaf_braceP_data
  · exact derives_star_any _

/-- **Non-vacuity — the separated guards SEPARATE.** Distinct guarded data render to DISTINCT outputs
(`data { data` vs `data data { data`), so render is not collapsing: injectivity (§4) has real content
on this class. Proved by lengths (no `DecidableEq Value` in-tree). -/
theorem demo_distinct :
    render (spineTemplate demoSpine) demoDA ≠ render (spineTemplate demoSpine) demoDB := by
  intro h
  simp only [demoSpine, render_spine_cons, render_spine_last] at h
  have hlen := congrArg List.length h
  simp only [demoDA, demoDB, List.length_append, List.length_cons, List.length_nil] at hlen
  omega

/-- The key theorem instantiated on the demo: equal output would force equal per-hole data. -/
theorem demo_injective (d d' : Nat → List Value)
    (hs  : guardedSafe (spineTemplate demoSpine) d) (hs' : guardedSafe (spineTemplate demoSpine) d')
    (heq : render (spineTemplate demoSpine) d = render (spineTemplate demoSpine) d') :
    ∀ h ∈ holesOf (spineTemplate demoSpine), d h = d' h :=
  guarded_render_injective _ ⟨demoSpine, rfl, demoSpine_separated⟩ d d' hs hs' heq

-- The render lengths pin the split (3 = `data { data`, 4 = `data data { data`); the guards decide
-- each hole's data via the VERIFIED matcher.
#guard (render (spineTemplate demoSpine) demoDA).length = 3
#guard (render (spineTemplate demoSpine) demoDB).length = 4
#guard derives [dataVal] noBraceRE                    -- hole 0: brace-free data admitted
#guard derives [dataVal, dataVal] noBraceRE           -- hole 0: still brace-free
#guard ! derives [braceVal] noBraceRE                 -- hole 0: a `{` would be rejected
#guard derives [dataVal] (PredRE.star PredRE.any)     -- hole 1: permissive guard admits anything

end Demo

/-! ## §7 THE HONEST WALL — general-guard uniqueness is FALSE (why the side-condition is needed). -/

namespace Ambiguous

/-- Two abutting `star any` holes — NO separating delimiter. This is NOT a `SeparatedTemplate`. -/
def ambT : GuardedTemplate :=
  ⟨[GSeg.hole 0 (PredRE.star PredRE.any), GSeg.hole 1 (PredRE.star PredRE.any)]⟩

/-- `hole 0 := [data]`, `hole 1 := [brace]`. -/
def ambD : Nat → List Value
  | 0 => [dataVal]
  | 1 => [braceVal]
  | _ => []

/-- `hole 0 := [data, brace]`, `hole 1 := []` — the SAME concatenation, split differently. -/
def ambD' : Nat → List Value
  | 0 => [dataVal, braceVal]
  | 1 => []
  | _ => []

/-- **`abutting_ambiguous`** — the general inverse is FALSE without the separation side-condition. Two
abutting permissive (`star any`) holes admit two DISTINCT data assignments producing the SAME output
`[data, brace]`; both are `guardedSafe` (the permissive guard accepts everything). So `render` is
genuinely NOT injective for general guards — the honest wall that `Separated` (§3) climbs. -/
theorem abutting_ambiguous :
    ∃ (T : GuardedTemplate) (d d' : Nat → List Value),
      guardedSafe T d ∧ guardedSafe T d' ∧ render T d = render T d' ∧ d 0 ≠ d' 0 := by
  refine ⟨ambT, ambD, ambD', ?_, ?_, ?_, ?_⟩
  · intro id g hmem
    have hg : g = PredRE.star PredRE.any := by
      simp only [ambT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq] at hmem
      rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    subst hg; exact derives_star_any _
  · intro id g hmem
    have hg : g = PredRE.star PredRE.any := by
      simp only [ambT, List.mem_cons, List.not_mem_nil, or_false, GSeg.hole.injEq] at hmem
      rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    subst hg; exact derives_star_any _
  · rfl
  · intro h
    have hlen := congrArg List.length h
    simp only [ambD, ambD', List.length_cons, List.length_nil] at hlen
    omega

end Ambiguous

/-! ## §8 Axiom hygiene. -/

#assert_axioms split_unique
#assert_axioms guarded_render_injective
#assert_axioms noBraceRE_excludes
#assert_axioms braceSpine_render_injective
#assert_axioms Demo.demo_injective
#assert_axioms Ambiguous.abutting_ambiguous

/-! ## §9 RESIDUALS — named follow-ons (stated, not `sorry`-ed).

  -- RESIDUAL (HandlebarsUniqueness tie): `braceSpine_render_injective` recovers the SAME theorem shape
  -- as `HandlebarsUniqueness.delim_render_injective` natively over `noBraceRE`/`braceVal`, but the
  -- EXACT identification (`spineTemplate (braceSpine …)` ↔ the committed `delimTemplate` under the
  -- `Tok ↪ Value` embedding `tokVal`, `NoBrace w ↔ Absent braceVal (w.map tokVal)`) is stated, not
  -- proved — it needs importing the 2-symbol formulation, deliberately kept out of this module's deps.

  -- RESIDUAL (predicate ↔ constructor): a DECIDABLE structural recognizer `SeparatedFormB : List GSeg →
  -- Bool` for the spine shape (alternating hole / single-symbol literal), with `SeparatedFormB T.segments
  -- ↔ ∃ s, T = spineTemplate s` — the analog of `HandlebarsUniqueness.DelimGuarded` — would let
  -- `guarded_render_injective` apply to ANY recognizer-accepted template. `Separated` itself is NOT
  -- decidable (`Excludes` is a `∀`-language statement), so the recognizer decides only the SHAPE; the
  -- per-hole `Excludes` obligations remain matcher facts, discharged as in §5.

  -- RESIDUAL (multi-symbol delimiters): `split_unique` and `Separated` use a SINGLE-symbol delimiter
  -- `c`. A multi-symbol delimiter word `δ` needs `Excludes` strengthened to "no `g`-word contains `δ`
  -- as a factor AND `δ` is not a proper prefix-overlap of itself" (border-free), so the first
  -- occurrence of `δ` still marks a unique boundary — the Knuth–Morris–Pratt border condition.

  -- RESIDUAL (junction breakout, inherited from HandlebarsGuarded §7): `Excludes` closes the seam FOR
  -- THIS CLASS (a hole cannot emit the following delimiter symbol), but a guard ending in a frame that
  -- abuts a NON-delimiter literal can still form a cross-junction structure; the general byte-level
  -- junction guarantee needs junction-aware guards.
-/

end Dregg2.Crypto.HandlebarsGuardedUniqueness
