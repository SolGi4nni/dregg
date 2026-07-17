/-
# Dregg2.Crypto.HandlebarsUniqueness — the INVERSE direction, chipped at a delimiter-guarded class.

`Handlebars.lean` proves GENERATION SOUNDNESS (safe rendering ⇒ language member) and names the
INVERSE / round-trip as a residual (§9): recover WHICH per-hole data produced a given output. The
inverse needs CFG parse-uniqueness (unambiguity); mathlib has no unambiguity API and GENERAL
unambiguity is real automata-theory work. This module CHIPS that wall on the reachable slice — it
proves the load-bearing half of the round-trip (RENDER INJECTIVITY / unique data recovery) for a
DELIMITER-GUARDED restricted template class, and names the general case honestly.

## THE RESTRICTION (stated plainly — NOT general unambiguity)

The class is **delimiter-normal-form** templates `delimTemplate [h₀, …, hₙ]`:

    hole h₀ · `{` · hole h₁ · `{` · … · `{` · hole hₙ

holes interleaved with SINGLE-`brace` (`{`) delimiter literals, PLUS the data-side guard that every
hole's data is **brace-free** (`NoBrace`, a strengthening of `Handlebars.NoDoubleBrace`).

Why THIS class and not the general one. The terminal alphabet is two symbols `{brace, data}`
(`Handlebars.Tok`). On a two-symbol alphabet there is no token a hole can freely carry yet a
delimiter can exclude — a hole may legitimately contain a lone `brace` (that is exactly what
`NoDoubleBrace` permits). So a delimiter that guarded holes provably cannot bleed into requires
demoting the one structural token, `brace`, to the delimiter role and forbidding it INSIDE holes.
That is the honest, minimal delimiter on this alphabet (option (ii) of the residual: holes are pure
data-runs; the separator is the one excluded token). With that guard the parse is UNIQUE: the
`brace`s in the output sit exactly at the delimiter positions, so the hole/literal split — and hence
each hole's data — is forced. General unambiguity (arbitrary literals, `NoDoubleBrace`-only holes,
seam-abutting braces) stays the NAMED WALL; see §6.

## WHAT IS PROVED (no `sorry`; the general wall stays a commented residual)

  * `brace_split_unique` — the core: a `brace`-free prefix before the first `brace` is unique.
  * `delim_render_injective` — RENDER INJECTIVITY: for a delimiter-guarded template, equal output
    forces equal per-hole data on every hole of the template (`∀ h ∈ holesOf T, d h = d' h`). This is
    the unique-data-recovery / round-trip-inverse half; the existence half rides
    `Handlebars.render_mem_language`.
  * `DelimGuarded` — a DECIDABLE structural recognizer for the class (a `Bool` function), with a
    concrete Demo showing it accepts the guarded form and rejects adjacent-hole ambiguity.
  * Demo — a guarded template with two DISTINCT data assignments producing DISTINCT outputs
    (non-vacuity: the guard genuinely separates), with `#guard`s.
-/
import Dregg2.Crypto.Handlebars
import Dregg2.Crypto.Segmentation
import Dregg2.Tactics

namespace Dregg2.Crypto.HandlebarsUniqueness

open Dregg2.Crypto.Handlebars

/-! ## §1 The data-side guard — `NoBrace` (pure data-runs; the delimiter token excluded).

`Handlebars.NoDoubleBrace` permits a lone interior `{`; the round-trip cannot, because a lone `{`
inside a hole is indistinguishable from a delimiter `{`. `NoBrace` is the strengthening that makes
holes pure data-runs, so every `{` in the output is a genuine delimiter. -/

/-- **`NoBrace w`** — `w` contains no `brace` token at all (a pure `data`-run). Strengthens
`Handlebars.NoDoubleBrace`: it forbids the lone `{` that `NoDoubleBrace` allows, because the
round-trip needs each `{` in the output to be an unambiguous delimiter, not possibly hole data. -/
def NoBrace : List Tok → Prop
  | [] => True
  | a :: rest => a ≠ Tok.brace ∧ NoBrace rest

instance decNoBrace : (w : List Tok) → Decidable (NoBrace w)
  | [] => isTrue trivial
  | a :: rest =>
      have _ : Decidable (NoBrace rest) := decNoBrace rest
      inferInstanceAs (Decidable (a ≠ Tok.brace ∧ NoBrace rest))

/-! ## §2 The core lemma — a `brace`-free prefix before the first `brace` is UNIQUE.

This is the parse-uniqueness content, at the granularity the guarded class needs: because both
prefixes are `brace`-free, the first `brace` in a shared output falls at the same index in each, so
the split point — and thus the prefix and suffix — are forced. The combinatorics lives
alphabet-generically in `Segmentation.split_unique_generic`; `noBrace_iff_absent` is the bridge
(`NoBrace` and `Segmentation.Absent Tok.brace` are distinct equation-compiler fixpoints, so the
equivalence is propositional, NOT `rfl`). -/

/-- **`noBrace_iff_absent`** — the guard bridge: `NoBrace w ↔ Segmentation.Absent Tok.brace w`.
Propositional (by induction on the word), not definitional — the two `def`s are distinct
equation-compiler fixpoints. -/
theorem noBrace_iff_absent : ∀ w, NoBrace w ↔ Segmentation.Absent Tok.brace w
  | [] => Iff.rfl
  | _ :: rest => and_congr Iff.rfl (noBrace_iff_absent rest)

/-- **`brace_split_unique`** — if `x ++ {` ` :: s = y ++ {` ` :: t` with `x`, `y` both `brace`-free,
then `x = y` and `s = t`. The load-bearing uniqueness step: the delimiter `{` cannot occur inside a
`brace`-free prefix, so it is located identically in both decompositions. Instance of
`Segmentation.split_unique_generic` at `⟨Tok, Tok.brace⟩` via the `noBrace_iff_absent` bridge. -/
theorem brace_split_unique :
    ∀ (x y s t : List Tok), NoBrace x → NoBrace y →
      x ++ Tok.brace :: s = y ++ Tok.brace :: t → x = y ∧ s = t :=
  fun x y s t hx hy h =>
    Segmentation.split_unique_generic Tok.brace x y s t
      ((noBrace_iff_absent x).mp hx) ((noBrace_iff_absent y).mp hy) h

/-! ## §3 The delimiter-normal-form template class. -/

/-- Segments of a delimiter-normal-form template over a hole-id list: holes separated by single-`{`
delimiter literals. `[h₀, h₁, …, hₙ] ↦ hole h₀ · lit[{] · hole h₁ · lit[{] · … · hole hₙ`. -/
def delimSegs : List HoleId → List Segment
  | [] => []
  | [h] => [Segment.hole h]
  | h :: h2 :: rest =>
      Segment.hole h :: Segment.lit [Tok.brace] :: delimSegs (h2 :: rest)

/-- **`delimTemplate holes`** — the delimiter-guarded template naming `holes` in order, each hole
separated from the next by a single-`{` delimiter. THIS is the restricted class this module unlocks
the round-trip for. -/
def delimTemplate (holes : List HoleId) : HandlebarsTemplate :=
  ⟨delimSegs holes⟩

/-- `holesOf` recovers exactly the hole-id list (the `{` delimiters are filtered out). -/
theorem holesOf_delimTemplate :
    ∀ holes, holesOf (delimTemplate holes) = holes
  | [] => rfl
  | [_] => rfl
  | h0 :: h1 :: rest => by
      have ih := holesOf_delimTemplate (h1 :: rest)
      simp only [holesOf, delimTemplate, delimSegs, List.filterMap_cons] at ih ⊢
      rw [ih]

/-! ## §4 Render shape — a delimiter-normal-form template renders as `{`-joined hole data. -/

/-- Single-hole render: `render (delimTemplate [h₀]) d = d h₀`. -/
theorem render_delim_single (d : HoleId → List Tok) (h0 : HoleId) :
    render (delimTemplate [h0]) d = d h0 := by
  simp only [render, delimTemplate, delimSegs, List.flatMap_cons, List.flatMap_nil,
    renderSeg, List.append_nil]

/-- Cons render: the first hole's data, then a delimiter `{`, then the render of the tail template. -/
theorem render_delim_cons (d : HoleId → List Tok) (h0 h1 : HoleId) (rest : List HoleId) :
    render (delimTemplate (h0 :: h1 :: rest)) d
      = d h0 ++ Tok.brace :: render (delimTemplate (h1 :: rest)) d := by
  simp only [render, delimTemplate, delimSegs, List.flatMap_cons, renderSeg,
    List.singleton_append]

/-! ## §5 THE KEY THEOREM — render injectivity / unique data recovery.

The induction lives alphabet-generically in `Segmentation.spine_segment_unique`; the lemmas below
exhibit `delimTemplate` as a brace-delimited `Segmentation.Spine Tok` (`toSpine`), transport the
guard via `noBrace_iff_absent`, and instantiate. -/

/-- The hole-id list as a brace-delimited `Segmentation.Spine` (delimiter `Tok.brace` throughout). -/
def toSpine : HoleId → List HoleId → Segmentation.Spine Tok
  | h, []         => .last h
  | h, h1 :: rest => .cons h Tok.brace (toSpine h1 rest)

/-- `toSpine` names exactly the hole-id list. -/
theorem toSpine_holes : ∀ (h0 : HoleId) (rest : List HoleId),
    Segmentation.spineHoles (toSpine h0 rest) = h0 :: rest
  | _, [] => rfl
  | h0, h1 :: rest => by
      simp only [toSpine, Segmentation.spineHoles, toSpine_holes h1 rest]

/-- `toSpine` renders as the delimiter-normal-form template. -/
theorem toSpine_render (d : HoleId → List Tok) : ∀ (h0 : HoleId) (rest : List HoleId),
    Segmentation.spineRender d (toSpine h0 rest) = render (delimTemplate (h0 :: rest)) d
  | h0, [] => by rw [render_delim_single]; rfl
  | h0, h1 :: rest => by
      rw [render_delim_cons]
      simp only [toSpine, Segmentation.spineRender, toSpine_render d h1 rest]

/-- `brace`-free hole data makes the spine `Segmented` (via the `noBrace_iff_absent` bridge). -/
theorem toSpine_segmented (d : HoleId → List Tok) :
    ∀ (h0 : HoleId) (rest : List HoleId), (∀ h ∈ h0 :: rest, NoBrace (d h)) →
      Segmentation.Segmented d (toSpine h0 rest)
  | _, [], _ => trivial
  | h0, h1 :: rest, hnb =>
      ⟨(noBrace_iff_absent _).mp (hnb h0 (by simp)),
       toSpine_segmented d h1 rest fun h hm => hnb h (List.mem_cons_of_mem _ hm)⟩

/-- Injectivity in the hole-id-list form: for a delimiter-guarded template with every hole's data
`brace`-free on both sides, equal output forces equal data on every named hole. Instance of
`Segmentation.spine_segment_unique` on `toSpine` (the hole data is `Absent` each following `{`, so
each split is forced). -/
theorem delim_render_injective_holes :
    ∀ (holes : List HoleId) (d d' : HoleId → List Tok),
      (∀ h ∈ holes, NoBrace (d h)) → (∀ h ∈ holes, NoBrace (d' h)) →
      render (delimTemplate holes) d = render (delimTemplate holes) d' →
      ∀ h ∈ holes, d h = d' h
  | [], _, _, _, _, _ => by intro h hmem; simp at hmem
  | h0 :: rest, d, d', hnd, hnd', heq => fun h hmem =>
      Segmentation.spine_segment_unique (toSpine h0 rest) d d'
        (toSpine_segmented d h0 rest hnd) (toSpine_segmented d' h0 rest hnd')
        (by rw [toSpine_render, toSpine_render]; exact heq)
        h (by rw [toSpine_holes]; exact hmem)

/-- **`delim_render_injective`** — RENDER INJECTIVITY on `holesOf`. For a delimiter-guarded template
`delimTemplate holes` whose holes carry `brace`-free data on both assignments, `render T d = render T
d'` forces `d h = d' h` for every hole `h` of `T`. This is the unique-data-recovery / round-trip
INVERSE, load-bearing half: an output determines the data that produced it. The existence half
(some safe `d` renders to a given language member) rides `Handlebars.render_mem_language`; together
they give the exists-UNIQUE the round-trip needs, on this class. -/
theorem delim_render_injective (holes : List HoleId) (d d' : HoleId → List Tok)
    (hnd : ∀ h ∈ holes, NoBrace (d h)) (hnd' : ∀ h ∈ holes, NoBrace (d' h))
    (heq : render (delimTemplate holes) d = render (delimTemplate holes) d') :
    ∀ h ∈ holesOf (delimTemplate holes), d h = d' h := by
  rw [holesOf_delimTemplate]
  exact delim_render_injective_holes holes d d' hnd hnd' heq

#assert_axioms brace_split_unique
#assert_axioms delim_render_injective_holes
#assert_axioms delim_render_injective

/-! ## §6 RESIDUAL — the GENERAL unambiguity wall (stated, not proved, not `sorry`-ed).

Injectivity above is proved for the delimiter-normal-form class ONLY. The general inverse stays the
named wall — mathlib has no CFG unambiguity API and general unambiguity is real automata-theory work.

  -- RESIDUAL (general_round_trip): for an arbitrary UNAMBIGUOUS handlebars template `T`,
  --   injectionFree T output → ∃! (d on holesOf T), render T d = output.
  -- FALSE without an unambiguity side-condition: e.g. ⟨hole 0, lit [data], hole 1⟩ splits
  -- `data data data` many ways. The delimiter-normal-form class here is the sub-slice where the
  -- side-condition is discharged structurally (brace-free holes + single-`{` separators); the
  -- general parse-uniqueness theorem (arbitrary literals, `NoDoubleBrace`-only holes) is unproved.

  -- RESIDUAL (predicate ↔ constructor): `DelimGuarded` (§7) DECIDES the delimiter-normal form, and
  -- `delimTemplate holes` inhabits it (Demo §7 confirms concretely). The exact characterization
  -- `DelimGuarded T ↔ ∃ holes, T = delimTemplate holes` — which would let `delim_render_injective`
  -- apply to ANY `DelimGuarded` template rather than the constructor image — is stated, not proved
  -- (a reconstruction induction over the stuck-`delimSegs` head; deferred).

  -- RESIDUAL (junction breakout, inherited from Handlebars §9): `∈ language` captures IN-SLOT
  -- confinement, not byte-level no-`{{` across hole/literal seams. The `brace`-free guard here
  -- closes the seam FOR THIS CLASS (no hole can emit a `{` to abut a delimiter `{`), but the general
  -- junction question is unchanged.
-/

/-! ## §7 `DelimGuarded` — a DECIDABLE structural recognizer for the class. -/

/-- **`delimFormB segs`** — decides delimiter-normal form structurally: `ε`, a lone hole, or
`hole · lit[{] · <hole-led delimiter form>`. Any other shape (adjacent holes, a non-`{` or multi-tok
literal, a dangling delimiter) is rejected. Boolean-valued, hence `DelimGuarded` is decidable. -/
def delimFormB : List Segment → Bool
  | [] => true
  | [Segment.hole _] => true
  | Segment.hole _ :: Segment.lit [Tok.brace] :: Segment.hole h :: more =>
      delimFormB (Segment.hole h :: more)
  | _ => false

/-- **`DelimGuarded T`** — decidable structural predicate: `T` is in delimiter-normal form. -/
def DelimGuarded (T : HandlebarsTemplate) : Prop := delimFormB T.segments = true

instance (T : HandlebarsTemplate) : Decidable (DelimGuarded T) :=
  inferInstanceAs (Decidable (delimFormB T.segments = true))

/-! ## §8 Demo — the recognizer, and the guard genuinely separating distinct data. -/

namespace Demo

/-- A three-hole delimiter-guarded template: `{{0}} { {{1}} { {{2}}` (holes 0,1,2, `{`-separated). -/
def t3 : HandlebarsTemplate := delimTemplate [0, 1, 2]

/-- The recognizer ACCEPTS the guarded form … -/
example : DelimGuarded t3 := by decide
#guard delimFormB t3.segments                                    -- true  (delimiter-normal form)

/-- … and REJECTS adjacent holes (the genuinely-ambiguous shape the guard exists to exclude). -/
def ambiguous : HandlebarsTemplate := ⟨[Segment.hole 0, Segment.hole 1]⟩
example : ¬ DelimGuarded ambiguous := by decide
#guard ! delimFormB ambiguous.segments                            -- false (adjacent holes rejected)

/-- Two-hole guarded template `{{0}} { {{1}}`. -/
def t2 : HandlebarsTemplate := delimTemplate [0, 1]

/-- Assignment A: both holes a single `data` byte. -/
def dA : HoleId → List Tok
  | 0 => [Tok.data]
  | 1 => [Tok.data]
  | _ => []

/-- Assignment B: hole 0 is TWO `data` bytes — distinct data. -/
def dB : HoleId → List Tok
  | 0 => [Tok.data, Tok.data]
  | 1 => [Tok.data]
  | _ => []

/-- Both assignments are `brace`-free on the template's holes (the guard is satisfied). -/
theorem dA_brace_free : ∀ h ∈ [0, 1], NoBrace (dA h) := by decide
theorem dB_brace_free : ∀ h ∈ [0, 1], NoBrace (dB h) := by decide

-- **Non-vacuity — the guard SEPARATES.** Distinct guarded data render to DISTINCT outputs:
-- `{{0}}={data}` gives `data { data`, `{{0}}={data,data}` gives `data data { data`. So the map from
-- guarded data to output is not collapsing — injectivity (§5) has real content on this class.
#guard render t2 dA = [Tok.data, Tok.brace, Tok.data]
#guard render t2 dB = [Tok.data, Tok.data, Tok.brace, Tok.data]
#guard decide (render t2 dA ≠ render t2 dB)

/-- The injectivity theorem instantiated on `t2`: equal output would force equal per-hole data. -/
theorem t2_injective (d d' : HoleId → List Tok)
    (hd : ∀ h ∈ [0, 1], NoBrace (d h)) (hd' : ∀ h ∈ [0, 1], NoBrace (d' h))
    (heq : render t2 d = render t2 d') :
    ∀ h ∈ holesOf t2, d h = d' h :=
  delim_render_injective [0, 1] d d' hd hd' heq

#assert_axioms t2_injective

end Demo

end Dregg2.Crypto.HandlebarsUniqueness
