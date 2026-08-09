/-
# SeedDraw — a CONSUMING uniform draw over a byte stream

Substrate note: this is Lean-authored game semantics.  Nothing here is an AIR, a
constraint system or a gadget; Rust and TypeScript only dispatch the tables the
Lean emitter writes.

## The wound this module closes

`SalvageCrate.unbiasedIndex?` is

    bytes.find? (· < ceiling)  |>.map (· % count)

— one index, no offset, no remainder.  It is unbiased for *one* draw and it is
unusable for a second: calling it three times on the same 32 bytes returns the
same byte three times, because there is no cursor to advance.  Any instance that
needs more than one number out of a seed — three Signal bands, a shuffle, a
board — cannot be built from it, and a construction that appears to do so is one
draw wearing three hats.

`drawBelow?` returns the drawn value **and the bytes it did not consume**, so a
caller threads a stream instead of re-reading a prefix.  `drawBelow?_consumes`
is the theorem that says the stream really shrinks, and
`consuming_draw_is_not_a_repeat` is the concrete refutation of the "just call it
again" reading.

## What is proved about the bias

Rejection sampling, not `% bound`: byte values in the incomplete high block are
discarded rather than folded, and `rejected_is_exactly_the_incomplete_block`
identifies that block as `256 % bound` for **every** bound (an ordinary proof,
no enumeration).  `draw_is_uniform_on_every_bound` then states that every
residue has exactly `256 / bound` preimages, quantified over the whole domain a
byte stream can serve (bounds `1..256`) — the complete finite domain of the
function, not a sampled instance of it.
-/
import Dregg2.Games.PathOfAngels.Core
import Dregg2.Tactics

namespace Dregg2.Games.PathOfAngels.SeedDraw

/-- The largest multiple of `bound` that fits in a byte.  Byte values at or above
it form the incomplete high block; the draw discards them rather than folding
them with `%`, which is what would favour the low residues. -/
def ceilingFor (bound : Nat) : Nat := 256 - 256 % bound

/-- One rejection-sampled draw below `bound`, returning the value **and the
bytes that remain**.  Every byte the draw inspects is consumed, rejected ones
included, so successive draws are independent reads of one stream.

`none` means the stream ran out before an acceptable byte appeared.  There is no
fallback: an exhausted stream refuses rather than folding a biased byte. -/
def drawBelow? (bound : Nat) (hb : 0 < bound) :
    List (Fin 256) → Option (Fin bound × List (Fin 256))
  | [] => none
  | b :: rest =>
      if b.val < ceilingFor bound then
        some (⟨b.val % bound, Nat.mod_lt _ hb⟩, rest)
      else
        drawBelow? bound hb rest

/-- The property `unbiasedIndex?` cannot have: the stream a draw hands back is
strictly shorter than the one it was given.  A sequence of draws therefore reads
disjoint prefixes, and a caller cannot accidentally draw the same byte twice. -/
theorem drawBelow?_consumes (bound : Nat) (hb : 0 < bound) (bs : List (Fin 256)) :
    ∀ (v : Fin bound) (rest : List (Fin 256)),
      drawBelow? bound hb bs = some (v, rest) → rest.length < bs.length := by
  induction bs with
  | nil =>
      intro v rest h
      simp [drawBelow?] at h
  | cons b bs ih =>
      intro v rest h
      simp only [drawBelow?] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        have hr : bs = rest := h.2
        subst hr
        simp only [List.length_cons]
        omega
      · have hlt := ih v rest h
        simp only [List.length_cons]
        omega

/-- A draw only ever accepts a byte below the ceiling; the high block never
reaches the `%`. -/
theorem drawBelow?_accepts_below_ceiling (bound : Nat) (hb : 0 < bound)
    (bs : List (Fin 256)) :
    ∀ (v : Fin bound) (rest : List (Fin 256)),
      drawBelow? bound hb bs = some (v, rest) →
        ∃ b : Fin 256, b.val < ceilingFor bound ∧ v.val = b.val % bound := by
  induction bs with
  | nil =>
      intro v rest h
      simp [drawBelow?] at h
  | cons b bs ih =>
      intro v rest h
      simp only [drawBelow?] at h
      split at h
      · rename_i hlt
        refine ⟨b, hlt, ?_⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact congrArg Fin.val h.1.symm
      · exact ih v rest h

/-- How many byte values the draw discards for a given bound: exactly the
incomplete high block, and nothing when `bound` divides 256.  Proved for every
bound, not enumerated. -/
def rejectedCount (bound : Nat) : Nat := 256 - ceilingFor bound

theorem rejected_is_exactly_the_incomplete_block (bound : Nat) :
    rejectedCount bound = 256 % bound := by
  have h : 256 % bound ≤ 256 := Nat.mod_le _ _
  simp only [rejectedCount, ceilingFor]
  revert h
  generalize 256 % bound = remainder
  omega

/-- The byte values a draw below `bound` accepts. -/
def acceptedBytes (bound : Nat) : List Nat :=
  (List.range 256).filter fun b => decide (b < ceilingFor bound)

/-- Preimage sizes: how many accepted byte values land on each residue. -/
def fibreSizes (bound : Nat) : List Nat :=
  (List.range bound).map fun r =>
    ((acceptedBytes bound).filter fun b => b % bound == r).length

/-- Uniformity over the WHOLE domain a byte stream can serve.  For every bound
in `1..256`, every residue below it has exactly `256 / bound` accepted preimages,
so no residue is favoured — this is the complete finite domain of `drawBelow?`,
not a sample of it. -/
def drawUniformB : Bool :=
  (List.range 257).all fun bound =>
    bound == 0 || (fibreSizes bound).all (fun n => n == 256 / bound)

/-! ⚑ **THE UNIFORMITY PIN NO LONGER EVALUATES IN THIS MODULE (2026-08-08).**  This module
is in the `Dregg2.FFI` closure — the crypto archive's build — and a `native_decide` here
made a game-fixture regression a hard failure of every Rust proving target.  The
STATEMENT stays here as an evaluation-free `check_* : Bool` (a `def` body elaborates
without running); the EVALUATION lives in `SeedDrawFixtures.lean`, rooted in the
`PathOfAngelsGuards` library, so a plain `lake build` still runs it.

Named residue: NONE.  `drawUniformB` is a closed Bool over `List.range 257`, so nothing
here needs a draw to elaborate. -/

/-- Uniformity over the WHOLE domain a byte stream can serve: for every bound in
`1..256`, every residue below it has exactly `256 / bound` accepted preimages.
(Pinned `= true` in `SeedDrawFixtures`.) -/
def check_draw_is_uniform_on_every_bound : Bool := drawUniformB

/-- Three bytes whose values differ, to exhibit the contrast below. -/
def probeBytes : List (Fin 256) := [1, 2, 0]

/-- The concrete refutation of "call the non-consuming draw again".  Off the same
three bytes the first draw yields 1 and the second yields 2; a draw with no
cursor — `bytes.find? (· < ceiling)` — yields 1 both times, because it re-reads
the same byte.  A multi-draw built on that shape is one draw repeated. -/
theorem consuming_draw_is_not_a_repeat :
    ((drawBelow? 6 (by decide) probeBytes).map Prod.fst = some 1) ∧
    (((drawBelow? 6 (by decide) probeBytes).bind
        fun r => drawBelow? 6 (by decide) r.2).map Prod.fst = some 2) ∧
    (probeBytes.find? (fun b => decide (b.val < ceilingFor 6)) = some 1) := by
  decide

#assert_axioms drawBelow?_consumes
#assert_axioms drawBelow?_accepts_below_ceiling
#assert_axioms rejected_is_exactly_the_incomplete_block
#assert_axioms consuming_draw_is_not_a_repeat

-- `draw_is_uniform_on_every_bound` (`native_decide` + `#assert_compiled`) lives in
-- `SeedDrawFixtures.lean`, rooted in `PathOfAngelsGuards` — see the note above.

end Dregg2.Games.PathOfAngels.SeedDraw
