/-
  Pancake/RealStages/HeaderStamp.lean — REAL STAGE #1: a fixed-header STAMP.

  A response-phase stamp that unconditionally appends one fixed header line to the
  output — the serializer's `headerLine (name, value) ++ crlf` for a gateway
  self-identification field (`Via: 1.1 edge`). Unlike the pivot witness (a single
  8-byte word) this header line is 15 bytes = TWO machine words, so its byte-effect
  is a `Seq` of two packed-word `Store`s the translator compiles by composition
  (`emit` over `Stage.seq`), proven byte-for-byte through the panSem byte model.

  * `stampWords`      — the two big-endian packed words the line lowers to.
  * `stampBytes`      — the 16-byte output region (the 15-byte header line + one
                        zero pad); bytes 0..14 are `Via: 1.1 edge\r\n`.
  * `stamp_byte_effect` — the translator-emitted `Seq` runs to a state whose whole
                        output region reads back as the getByte-decomposition of
                        the stored words (symbolic byte-view via the substrate).
  * `stamp_ascii`     — the CONCRETE non-vacuity: every one of the 16 output bytes
                        reads back as EXACTLY `stampBytes[i]` (`Via: 1.1 edge\r\n`
                        then a zero), decided in-kernel — real lowering, real bytes.

  ASSURANCE: `#print axioms` ⊆ {propext, Quot.sound, Classical.choice}; 0 `sorry`,
  no `native_decide`/`ofReduceBool`. Stack L (the Lean model). No machine claim.
-/
import Pancake.RealStages.MultiWord

namespace Pancake.RealStages.HeaderStamp

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.RealStageDemo
open Pancake.RealStages.MultiWord

variable {σ : Type}

/-- The two big-endian packed words the header line `Via: 1.1 edge\r\n` lowers to:
slot 0 = `"Via: 1."`, slot 1 = `" edge"` + CRLF + one zero pad. -/
def stampWords : List Word :=
  [ packBE [86, 105, 97, 58, 32, 49, 46, 49],
    packBE [32, 101, 100, 103, 101, 13, 10, 0] ]

/-- The 16-byte output region: the 15-byte header line `Via: 1.1 edge\r\n`
(`V`,`i`,`a`,`:`,SP,`1`,`.`,`1`,SP,`e`,`d`,`g`,`e`,CR,LF) followed by one zero
pad. This is exactly `headerLine ("Via","1.1 edge") ++ crlf` (colon=58, space=32,
CR=13, LF=10) padded to the two-word region. -/
def stampBytes : List (BitVec 8) :=
  [86, 105, 97, 58, 32, 49, 46, 49, 32, 101, 100, 103, 101, 13, 10, 0]

/-- **The byte-effect (symbolic).** The translator-emitted `Seq` for the two-word
stamp stage runs to a state whose every output byte, read back through the panSem
byte model, is the getByte-decomposition of the word stored in its slot. A
byte-ADDRESSED statement over the endianness substrate, for a TWO-word line. -/
theorem stamp_byte_effect (o : Oracle σ) (s : PancakeState σ)
    (hmap : ∀ k, k < 2 → s.memaddrs (BitVec.ofNat 64 (8 * k)) = true) :
    ∃ s', PancakeSem o (emit (storeWordsFrom (σ := σ) 0 stampWords)) s = (none, s') ∧
      ∀ k, k < 2 → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs true
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (getByte (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) stampWords[k]! true) := by
  obtain ⟨s', hrun, hbytes⟩ :=
    store_words_byte_effect o stampWords true s (by decide) hmap
      (by intro k j hk hj
          have hk2 : k < 2 := hk
          rcases (show k = 0 ∨ k = 1 from by omega) with rfl | rfl <;>
            (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                       from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide))
  exact ⟨s', hrun, hbytes⟩

/-- **The concrete non-vacuity.** After the translator-emitted `Seq`, EVERY byte of
the 16-byte output region reads back as exactly `stampBytes[8·k+j]` — the ASCII of
`Via: 1.1 edge\r\n` (then a zero pad), decided in-kernel. Real bytes-lowering →
real memory bytes; not a `P → P`. -/
theorem stamp_ascii (o : Oracle σ) (s : PancakeState σ)
    (hmap : ∀ k, k < 2 → s.memaddrs (BitVec.ofNat 64 (8 * k)) = true) :
    ∃ s', PancakeSem o (emit (storeWordsFrom (σ := σ) 0 stampWords)) s = (none, s') ∧
      ∀ k, k < 2 → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs true
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (stampBytes[8 * k + j]!) := by
  obtain ⟨s', hrun, hbytes⟩ := stamp_byte_effect o s hmap
  refine ⟨s', hrun, ?_⟩
  intro k hk j hj
  rw [hbytes k hk j hj]
  rcases (show k = 0 ∨ k = 1 from by omega) with rfl | rfl <;>
    (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
               from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      decide)

end Pancake.RealStages.HeaderStamp
