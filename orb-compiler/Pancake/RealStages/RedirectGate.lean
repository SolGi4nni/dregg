/-
  Pancake/RealStages/RedirectGate.lean — REAL STAGE #2: a status-rewrite GATE that
  writes a `Location` header.

  A request-phase gate: when the request matches a redirect rule (a decision word
  held in local `"match"`) the stage short-circuits and writes the redirect's
  `Location` header line into the output; otherwise it writes nothing and the
  response is untouched. This is the CONDITIONAL shape — a `cond` stage-kind whose
  branch the translator compiles to a panSem `If` (`emit` over `Stage.cond`) — so
  the byte-effect is guarded, and BOTH branches are certified:

  * `redirect_match_ascii` — a matched request: the emitted `If` takes the write
    branch and the whole 40-byte output region reads back byte-for-byte as the
    `Location` header line `Location: https://new.example/old\r\n` (five packed
    words, 35 meaningful bytes + zero pad), decided in-kernel.
  * `redirect_nomatch_noop` — an unmatched request: the emitted `If` takes the
    skip branch and the machine state is returned UNCHANGED — no `Location`, no
    byte written. The no-rewrite boundary, stated as full-state identity.

  The `Location` line is exactly `headerLine ("Location", "https://new.example/old")
  ++ crlf` (colon=58, space=32, CR=13, LF=10).

  ASSURANCE: `#print axioms` ⊆ {propext, Quot.sound, Classical.choice}; 0 `sorry`,
  no `native_decide`/`ofReduceBool`. Stack L (the Lean model). No machine claim.
-/
import Pancake.RealStages.MultiWord

namespace Pancake.RealStages.RedirectGate

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.RealStageDemo
open Pancake.RealStages.MultiWord

variable {σ : Type}

/-- The five big-endian packed words the `Location` line lowers to. -/
def locWords : List Word :=
  [ packBE [76, 111, 99, 97, 116, 105, 111, 110],      -- "Location"
    packBE [58, 32, 104, 116, 116, 112, 115, 58],      -- ": https:"
    packBE [47, 47, 110, 101, 119, 46, 101, 120],      -- "//new.ex"
    packBE [97, 109, 112, 108, 101, 47, 111, 108],     -- "ample/ol"
    packBE [100, 13, 10, 0, 0, 0, 0, 0] ]              -- "d" CRLF pad

/-- The 40-byte output region: the 35-byte `Location: https://new.example/old\r\n`
followed by five zero pad bytes. -/
def locBytes : List (BitVec 8) :=
  [76, 111, 99, 97, 116, 105, 111, 110, 58, 32, 104, 116, 116, 112, 115, 58,
   47, 47, 110, 101, 119, 46, 101, 120, 97, 109, 112, 108, 101, 47, 111, 108,
   100, 13, 10, 0, 0, 0, 0, 0]

/-- The gate guard expression: the request-match decision word in local `"match"`
equals `1`. -/
def guardExp : PancakeExp := .cmp .equal (.var "match") (.const 1)

/-- **The redirect gate stage.** `cond` on the match word: the write branch stores
the `Location` line, the skip branch does nothing. The translator compiles this to
a panSem `If`. -/
def redirectStage : Stage σ :=
  .cond guardExp (fun s => decide (s.locals "match" = some 1))
    (storeWordsFrom 0 locWords) (.prim skipPrim)

/-- The guard evaluates to `1` (take the write branch) when the match word is `1`. -/
theorem guard_match (s : PancakeState σ) (h : s.locals "match" = some 1) :
    eval s guardExp = some 1 := by
  simp only [guardExp, eval, h]; decide

/-- The guard evaluates to `0` (take the skip branch) when the match word is `0`. -/
theorem guard_nomatch (s : PancakeState σ) (h : s.locals "match" = some 0) :
    eval s guardExp = some 0 := by
  simp only [guardExp, eval, h]; decide

/-- **Matched request → the `Location` line is written, byte-for-byte.** The
translator-emitted `If` takes the write branch and every byte of the 40-byte
output region reads back as exactly `locBytes[8·k+j]` — the ASCII of
`Location: https://new.example/old\r\n` (then zero pad), decided in-kernel. -/
theorem redirect_match_ascii (o : Oracle σ) (s : PancakeState σ)
    (hmatch : s.locals "match" = some 1)
    (hmap : ∀ k, k < 5 → s.memaddrs (BitVec.ofNat 64 (8 * k)) = true) :
    ∃ s', PancakeSem o (emit (redirectStage (σ := σ))) s = (none, s') ∧
      ∀ k, k < 5 → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs true
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (locBytes[8 * k + j]!) := by
  obtain ⟨s', hrun, hbytes⟩ :=
    store_words_byte_effect o locWords true s (by decide) hmap
      (by intro k j hk hj
          have hk5 : k < 5 := hk
          rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 from by omega)
            with rfl | rfl | rfl | rfl | rfl <;>
            (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                       from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide))
  refine ⟨s', ?_, ?_⟩
  · -- the emitted If takes the write branch
    show PancakeSem o (.cond guardExp (emit (storeWordsFrom (σ := σ) 0 locWords)) .skip) s
          = (none, s')
    rw [sem_cond o (guard_match s hmatch), if_pos (show (1 : Word) ≠ 0 from by decide)]
    exact hrun
  · intro k hk j hj
    rw [hbytes k hk j hj]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 from by omega)
      with rfl | rfl | rfl | rfl | rfl <;>
      (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                 from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide)

/-- **Unmatched request → nothing written.** The translator-emitted `If` takes the
skip branch and the machine state is returned UNCHANGED: no `Location`, no byte
added. The no-rewrite boundary, as full-state identity. -/
theorem redirect_nomatch_noop (o : Oracle σ) (s : PancakeState σ)
    (hmatch : s.locals "match" = some 0) :
    PancakeSem o (emit (redirectStage (σ := σ))) s = (none, s) := by
  show PancakeSem o (.cond guardExp (emit (storeWordsFrom (σ := σ) 0 locWords)) .skip) s
        = (none, s)
  rw [sem_cond o (guard_nomatch s hmatch), if_neg (show ¬((0 : Word) ≠ 0) from by decide),
      PancakeSem]

end Pancake.RealStages.RedirectGate
