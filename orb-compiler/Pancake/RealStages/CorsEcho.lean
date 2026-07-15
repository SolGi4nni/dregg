/-
  Pancake/RealStages/CorsEcho.lean — REAL STAGE #3: a conditional CORS header with
  a NO-LEAK boundary.

  A response-phase transform that stamps `Access-Control-Allow-Origin` onto the
  output ONLY when the request's origin is permitted (a decision word held in local
  `"allowed"`); a forbidden origin gets NOTHING added. This is the conditional
  security boundary: a disallowed origin never receives the header. Expressed as a
  `cond` stage-kind (translator-compiled to a panSem `If`), both branches certified:

  * `cors_allow_ascii` — a permitted origin: the emitted `If` takes the write
    branch and the whole 56-byte output region reads back byte-for-byte as the
    header line `Access-Control-Allow-Origin: https://app.example.com\r\n` (seven
    packed words, 54 meaningful bytes + zero pad), decided in-kernel.
  * `cors_deny_noleak` — a forbidden origin: the emitted `If` takes the skip branch
    and the machine state is returned UNCHANGED — no ACAO, no byte added. The
    byte-level no-leak boundary, stated as full-state identity.

  The header line is exactly `headerLine ("Access-Control-Allow-Origin",
  "https://app.example.com") ++ crlf` (colon=58, space=32, CR=13, LF=10).

  ASSURANCE: `#print axioms` ⊆ {propext, Quot.sound, Classical.choice}; 0 `sorry`,
  no `native_decide`/`ofReduceBool`. Stack L (the Lean model). No machine claim.
-/
import Pancake.RealStages.MultiWord

namespace Pancake.RealStages.CorsEcho

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.RealStageDemo
open Pancake.RealStages.MultiWord

variable {σ : Type}

/-- The seven big-endian packed words the ACAO line lowers to. -/
def acaoWords : List Word :=
  [ packBE [65, 99, 99, 101, 115, 115, 45, 67],       -- "Access-C"
    packBE [111, 110, 116, 114, 111, 108, 45, 65],    -- "ontrol-A"
    packBE [108, 108, 111, 119, 45, 79, 114, 105],    -- "llow-Ori"
    packBE [103, 105, 110, 58, 32, 104, 116, 116],    -- "gin: htt"
    packBE [112, 115, 58, 47, 47, 97, 112, 112],      -- "ps://app"
    packBE [46, 101, 120, 97, 109, 112, 108, 101],    -- ".example"
    packBE [46, 99, 111, 109, 13, 10, 0, 0] ]         -- ".com" CRLF pad

/-- The 56-byte output region: the 54-byte
`Access-Control-Allow-Origin: https://app.example.com\r\n` followed by two zero
pad bytes. -/
def acaoBytes : List (BitVec 8) :=
  [65, 99, 99, 101, 115, 115, 45, 67, 111, 110, 116, 114, 111, 108, 45, 65,
   108, 108, 111, 119, 45, 79, 114, 105, 103, 105, 110, 58, 32, 104, 116, 116,
   112, 115, 58, 47, 47, 97, 112, 112, 46, 101, 120, 97, 109, 112, 108, 101,
   46, 99, 111, 109, 13, 10, 0, 0]

/-- The guard expression: the origin-allow decision word in local `"allowed"`
equals `1`. -/
def guardExp : PancakeExp := .cmp .equal (.var "allowed") (.const 1)

/-- **The CORS ACAO stage.** `cond` on the allow word: the write branch stores the
ACAO line, the skip branch does nothing (no leak). The translator compiles this to
a panSem `If`. -/
def corsStage : Stage σ :=
  .cond guardExp (fun s => decide (s.locals "allowed" = some 1))
    (storeWordsFrom 0 acaoWords) (.prim skipPrim)

/-- The guard evaluates to `1` (write branch) when the allow word is `1`. -/
theorem guard_allow (s : PancakeState σ) (h : s.locals "allowed" = some 1) :
    eval s guardExp = some 1 := by
  simp only [guardExp, eval, h]; decide

/-- The guard evaluates to `0` (skip branch) when the allow word is `0`. -/
theorem guard_deny (s : PancakeState σ) (h : s.locals "allowed" = some 0) :
    eval s guardExp = some 0 := by
  simp only [guardExp, eval, h]; decide

/-- **Permitted origin → the ACAO line is written, byte-for-byte.** The
translator-emitted `If` takes the write branch and every byte of the 56-byte output
region reads back as exactly `acaoBytes[8·k+j]` — the ASCII of
`Access-Control-Allow-Origin: https://app.example.com\r\n` (then zero pad), decided
in-kernel. -/
theorem cors_allow_ascii (o : Oracle σ) (s : PancakeState σ)
    (hallow : s.locals "allowed" = some 1)
    (hmap : ∀ k, k < 7 → s.memaddrs (BitVec.ofNat 64 (8 * k)) = true) :
    ∃ s', PancakeSem o (emit (corsStage (σ := σ))) s = (none, s') ∧
      ∀ k, k < 7 → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs true
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (acaoBytes[8 * k + j]!) := by
  obtain ⟨s', hrun, hbytes⟩ :=
    store_words_byte_effect o acaoWords true s (by decide) hmap
      (by intro k j hk hj
          have hk7 : k < 7 := hk
          rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 from by omega)
            with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                       from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide))
  refine ⟨s', ?_, ?_⟩
  · show PancakeSem o (.cond guardExp (emit (storeWordsFrom (σ := σ) 0 acaoWords)) .skip) s
          = (none, s')
    rw [sem_cond o (guard_allow s hallow), if_pos (show (1 : Word) ≠ 0 from by decide)]
    exact hrun
  · intro k hk j hj
    rw [hbytes k hk j hj]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                 from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        decide)

/-- **Forbidden origin → nothing written (no leak).** The translator-emitted `If`
takes the skip branch and the machine state is returned UNCHANGED: no
`Access-Control-Allow-Origin`, no byte added. The byte-level no-leak boundary, as
full-state identity. -/
theorem cors_deny_noleak (o : Oracle σ) (s : PancakeState σ)
    (hdeny : s.locals "allowed" = some 0) :
    PancakeSem o (emit (corsStage (σ := σ))) s = (none, s) := by
  show PancakeSem o (.cond guardExp (emit (storeWordsFrom (σ := σ) 0 acaoWords)) .skip) s
        = (none, s)
  rw [sem_cond o (guard_deny s hdeny), if_neg (show ¬((0 : Word) ≠ 0) from by decide),
      PancakeSem]

end Pancake.RealStages.CorsEcho
