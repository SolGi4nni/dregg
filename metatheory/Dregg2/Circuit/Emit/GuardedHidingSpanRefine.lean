/-
# Dregg2.Circuit.Emit.GuardedHidingSpanRefine — the PARSE COMPOSITION of the hidden-span family
(the weld to the untouched parse theorem), plus the family's shared witness scaffolding.

The hidden-span family's EMITTED descriptor is
`GuardedHidingSpanWideBlindEmit.guardedHidingSpanWideBlindDesc` (the 5-blinding-lane
guard-constrained descriptor); its whole-descriptor refinement (`Satisfied2 ⟹ spec`,
commit-binds + binding-as-extraction) lives in `GuardedHidingSpanWideBlindRefine`, and the
grounded guard weld (no `hGuard`) in `GuardedHidingSpanGuardWeld`. The original single-felt-
blinding M0 descriptor this file used to refine was DELETED in the felt-width cutover of
2026-07-23 (see the `GuardedHidingSpanEmit` header); every one of its theorems exists
STRENGTHENED over the wide-blind descriptor.

What REMAINS here is the descriptor-INDEPENDENT half those files reuse verbatim:

## The WELD to the parse theorem (hiding lives strictly BELOW `mem_language_iff_spans`)

The M0 skeleton is `lit₀ · ⟨hole 0 : guard g⟩ · lit₁`. Given the hole span's guard obligation
(`derives span guard = true` — either the plainly-named `hGuard`, or DERIVED by the guard weld),
the skeleton is a member of the induced language and the untouched
`HandlebarsGuardedParse.parse_exists_distinct_holes` fires on the recovered span. The
load-bearing framing: hiding lives BELOW `mem_language_iff_spans`, so the parse/∃! direction
carries for free once the recovered span guard-fires. `m0Template`/`m0_holes_nodup`/`m0_spanOk`/
`m0_mem` are consumed by `GuardedHidingSpanWideBlindRefine` and `GuardedHidingSpanGuardWeld`
unchanged.

Also here: the guard-violation canary (`badSpan_rejected` — a brace-holding span fails `SpanOk`,
so the guard clause is genuinely load-bearing), the concrete `Demo` span whose guard obligation
is DISCHARGED by the verified matcher (`s_guard` — the concrete `hGuard` the welds instantiate),
and the shared witness scaffolding (`hash0`, `wZeroAbsorb`, `wRow`) the wide-blind non-vacuity
witnesses are built from.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only (edits nothing in
`GuardedSpans` / `HandlebarsGuardedParse` / `HandlebarsGuarded`).
-/
import Dregg2.Circuit.Emit.GuardedHidingSpanEmit
import Dregg2.Crypto.HandlebarsGuardedParse

namespace Dregg2.Circuit.Emit.GuardedHidingSpanRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DeployedCapTree (Digest8)

set_option autoImplicit false

/-! ## §1 — the WELD to the untouched parse theorem.

The M0 skeleton is `lit₀ · ⟨hole 0 : g⟩ · lit₁`. Given the hole span's guard obligation, the
skeleton is a member of the induced language and `parse_exists_distinct_holes` fires unchanged —
hiding lives strictly BELOW `mem_language_iff_spans`. -/

open Dregg2.Exec (Value)
open Dregg2.Crypto.Deriv (PredRE)
open Dregg2.Crypto.Deriv.PredRE (derives)
open Dregg2.Crypto.HandlebarsGuarded
  (GSeg GuardedTemplate guardedToGrammar render guardedSafe)
open Dregg2.Crypto.GuardedSpans (SpanOk mem_language_iff_spans)
open Dregg2.Crypto.HandlebarsGuardedUniqueness (holesOf holeIds)
open Dregg2.Crypto.HandlebarsGuardedParse (parse_exists_distinct_holes)

/-- The M0 fixed skeleton as a guarded template: `lit₀ · ⟨hole 0 : g⟩ · lit₁`. -/
def m0Template (lit0 lit1 : List Value) (g : PredRE) : GuardedTemplate :=
  ⟨[.lit lit0, .hole 0 g, .lit lit1]⟩

/-- The template names exactly hole 0 — trivially distinct. -/
theorem m0_holes_nodup (lit0 lit1 : List Value) (g : PredRE) :
    (holesOf (m0Template lit0 lit1 g)).Nodup := by
  simp only [holesOf, m0Template, holeIds]
  exact List.nodup_singleton 0

/-- `SpanOk` for the M0 skeleton with the hidden span `s`: literals are pinned to the template text,
the hole span guard-fires (`hGuard`). -/
theorem m0_spanOk (lit0 lit1 s : List Value) (g : PredRE) (hGuard : derives s g = true) :
    SpanOk (m0Template lit0 lit1 g).segments [lit0, s, lit1] :=
  ⟨rfl, hGuard, rfl, trivial⟩

/-- The rendered skeleton `lit₀ ++ s ++ lit₁` is a member of the induced language — via the untouched
`mem_language_iff_spans` and the guard-firing span. -/
theorem m0_mem (lit0 lit1 s : List Value) (g : PredRE) (hGuard : derives s g = true) :
    (lit0 ++ s ++ lit1) ∈ (guardedToGrammar (m0Template lit0 lit1 g)).language :=
  (mem_language_iff_spans (m0Template lit0 lit1 g) _).mpr
    ⟨[lit0, s, lit1], m0_spanOk lit0 lit1 s g hGuard, by simp [List.append_assoc]⟩

/-! ## §2 — the shared witness scaffolding (consumed by the wide-blind non-vacuity witnesses). -/

/-- The abstract hash never enters the family's descriptors' denotations (no hash sites / map
ops), so any value serves. -/
def hash0 : List ℤ → ℤ := fun _ => 0

/-- A decidable stand-in absorb: the constant all-zero 8-felt digest (NOT Poseidon2). -/
def wZeroAbsorb : List ℤ → Digest8 := fun _ => fun _ => 0

/-- The all-zero witness row (every column `0`; consistent with `wZeroAbsorb`). -/
def wRow : Assignment := fun _ => 0

/-! ## §3 — TAMPER CANARY: a guard-violating hidden span is REFUSED (the hole clause bites).

This is the composition-side canary: a span that does NOT satisfy its guard fails `SpanOk`, so the
recovered word is not admitted as an expansion — the `derives span guard = true` obligation is
genuinely load-bearing (model `GuardedSpans.demoSpans_bad_rejected`). -/

open Dregg2.Crypto.HandlebarsGuarded (braceVal dataVal braceP leaf_braceP_data)
open Dregg2.Crypto.Deriv.PredRE (leaf)
open Dregg2.Crypto.HandlebarsGuardedUniqueness (noBraceRE derives_noBraceRE_of_nofire)

/-- A span holding a brace violates the `noBraceRE` guard. -/
theorem badSpan_rejected (lit0 lit1 : List Value) :
    ¬ SpanOk (m0Template lit0 lit1 noBraceRE).segments [lit0, [braceVal], lit1] := by
  rintro ⟨-, hbad, -⟩
  have hbrace : derives [braceVal] noBraceRE = false := by
    simp only [derives, noBraceRE]
    decide
  rw [hbrace] at hbad
  exact absurd hbad (by decide)

/-! ## §4 — the parse theorem FIRES on a concrete recovered span (matcher re-run). -/

namespace Demo

/-- The M0 template under test: `lit[data] · ⟨hole 0 : noBraceRE⟩ · lit[data]`. -/
def T : GuardedTemplate := m0Template [dataVal] [dataVal] noBraceRE

/-- The hidden hole span (brace-free — satisfies `noBraceRE`). -/
def s : List Value := [dataVal]

/-- The hole span's guard obligation, DISCHARGED by the verified matcher (not assumed): a brace-free
span satisfies `noBraceRE`. This is the `hGuard` the weld consumes, made concrete. -/
theorem s_guard : derives s noBraceRE = true :=
  derives_noBraceRE_of_nofire s (by
    intro b hb
    simp only [s, List.mem_singleton] at hb
    subst hb
    exact leaf_braceP_data)

/-- The presented output `data · data · data` — a language member of the M0 skeleton, reached with NO
assignment in hand (through `m0_mem`). -/
def out : List Value := [dataVal] ++ s ++ [dataVal]

theorem out_mem : out ∈ (guardedToGrammar T).language :=
  m0_mem [dataVal] [dataVal] s noBraceRE s_guard

/-- **The parse theorem FIRES** on the recovered span: from `out_mem` alone, guard-satisfying per-hole
data rendering to `out` EXISTS — the untouched `parse_exists_distinct_holes`, welded below
`mem_language_iff_spans`, carries through the hiding. -/
theorem out_parses : ∃ d : Nat → List Value, guardedSafe T d ∧ render T d = out :=
  parse_exists_distinct_holes T (m0_holes_nodup [dataVal] [dataVal] noBraceRE) out out_mem

-- Non-vacuity `#guard`s: the recovered hole-0 data is the brace-free span, and the verified matcher
-- RE-RUN on it accepts (the guard obligation) while the strict guard would reject a brace.
#guard derives s noBraceRE
#guard (s.map (leaf braceP)) == [false]
#guard ! derives [braceVal] noBraceRE

end Demo

/-! ## §5 — axiom tripwires (the composition keystones). -/

#assert_axioms m0_mem
#assert_axioms badSpan_rejected
#assert_axioms Demo.out_parses

end Dregg2.Circuit.Emit.GuardedHidingSpanRefine
