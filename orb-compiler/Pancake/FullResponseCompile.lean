/-
  Pancake/FullResponseCompile.lean — AXIS 1: the FULL HTTP response compiled to a
  proven Pancake program, ENTIRELY in the faithful byte-addressed model.

  WHAT THIS CLOSES. `ModelUnify` put the response HEAD (literal frame + runtime
  decimal render) into the byte-addressed `putByte`/`memLoadByte` model;
  `ByteCopy` reproved the runtime body COPY there. This file COMPOSES them: the
  head materializer (`ModelUnify.byteLit`) followed by the byte-addressed body copy
  (`ByteCopy.copySeg`) is a single Pancake program whose EXECUTION lands exactly
  `serialize resp` at consecutive BYTE addresses. Everything — head and body — now
  lives in ONE faithful packed-byte memory image; the word-slot shortcut is gone.

  WHAT IS PROVEN:

   * `membytesB_glue` — the byte-region append law: a head block at `base` plus a
     body block at `base + |head|` assemble the concatenation `head ++ body`,
     byte-addressed.

   * `fullRespLit` / `fullRespLit_correct` — THE FULL RESPONSE PROGRAM and its
     OPERATIONAL correctness. For ALL `resp`, running
        byteLit obase (headBytes resp) ; copySeg (obase+|head|) src |body|
     from a state whose source region holds `resp.body` (byte-addressed) leaves the
     model memory holding `serialize resp` at `obase`, byte for byte, read back by
     the faithful `mem_load_byte`. This is `behavior(program) = serialize(resp)`,
     not a definitional identity: the head bytes are materialized by literal
     `StoreByte`s and the body bytes are COPIED at runtime by the `copyByteWhile`
     loop; the theorem names the real `serialize` and its conclusion is a genuine
     memory post-state.

   * `fullResp_fires_on_404` — NON-VACUITY: a concrete `HTTP/1.1 404 Not Found`
     with body `"nope"` compiles FULLY (status line, `Content-Length: 4`, framing
     CRLFs, body), every hypothesis discharged against a witness state (output
     region at 0, body source at 1024, all-zero output). `witness_pre_not_full`
     pins non-vacuity: the pre-state does NOT already hold the response.

  THE HONEST RESIDUAL (named, not hidden). The head here is materialized as
  EMIT-TIME LITERAL bytes (`byteLit`), so the status decimal and Content-Length are
  baked when the program is generated — exactly as the word-slot `StructEmit.respEmit`
  did, now byte-addressed. The RUNTIME decimal render of the status (`natToDecProg`)
  is separately proven byte-addressed and COMPOSED into the status-line head in
  `ModelUnify.statusHead_landsB`; splicing THAT runtime render into this longer
  program needs a frame-exposing restatement of `statusHead_landsB` (its published
  conclusion drops the `memaddrs`/frame facts a following program rides on). That
  restatement is the remaining step for a single program with BOTH a runtime status
  render AND a runtime body copy; the pieces are each proven byte-addressed.

  Stack L (the Lean model of Pancake). `#print axioms` at the foot
  (⊆ {propext, Classical.choice, Quot.sound}).
-/
import Pancake.ByteCopy
import Pancake.ModelUnify
import Pancake.StructEmit

namespace Pancake.FullResponseCompile

open Pancake Pancake.BytesModel Pancake.SerializeCompile Pancake.SerializeStruct
open Pancake.ModelUnify Pancake.ByteCopy Pancake.StructEmit Pancake.NatToDecFull

variable {σ : Type}

/-! ## 1. The byte-region append law. -/

/-- **`MemBytesB` GLUE.** A head block at `base` and a body block at `base + |head|`
(each read back by `mem_load_byte`) assemble the concatenation `head ++ body`
byte-addressed at `base`. -/
theorem membytesB_glue (m : Word → Word) (dm : Word → Bool) (be : Bool) (base : Word)
    (head body : Bytes)
    (hh : ∀ i, i < head.length →
      memLoadByte m dm be (base + BitVec.ofNat 64 i) = some head[i]!)
    (hb : ∀ j, j < body.length →
      memLoadByte m dm be (base + BitVec.ofNat 64 (head.length + j)) = some body[j]!) :
    MemBytesB m dm be base (head ++ body) := by
  intro i hi
  rw [List.length_append] at hi
  by_cases hh' : i < head.length
  · rw [get!_append_left head body i hh']
    exact hh i hh'
  · have hji : head.length ≤ i := Nat.not_lt.mp hh'
    have hjb : i - head.length < body.length := by omega
    rw [get!_append_right head body i hji hi]
    have := hb (i - head.length) hjb
    rwa [show head.length + (i - head.length) = i from by omega] at this

/-! ## 2. THE FULL RESPONSE PROGRAM: literal head, runtime body copy. -/

/-- **The full response program.** Phase A materializes the head block (status line,
header block, blank-line separator — `headBytes resp`, byte-addressed literals);
phase B copies `|resp.body|` bytes from `src` to `obase + |head|` with the genuine
byte-addressed `copyByteWhile` loop. -/
def fullRespLit (resp : Response) (obase src : Word) : PancakeProg :=
  .seq (byteLit obase (headBytes resp))
       (copySeg (obase + BitVec.ofNat 64 (headBytes resp).length) src resp.body.length)

/-- **THE FULL RESPONSE COMPILES — OPERATIONAL.** For ALL `resp`: running
`fullRespLit resp obase src` from a state whose output region is addressable and
non-aliasing and whose source region holds `resp.body` (byte-addressed) terminates
normally with the model memory at `obase` equal, byte for byte, to `serialize resp`
(read back by `mem_load_byte`). The head bytes are laid by literal `StoreByte`s; the
body bytes are COPIED at runtime by `copyByteWhile`. The conclusion names the real
`serialize` and is a genuine packed-byte memory post-state. -/
theorem fullRespLit_correct (o : Oracle σ) (resp : Response) (obase src : Word)
    (s : PancakeState σ)
    (h63 : (serialize resp).length < 2 ^ 63)
    (hinj : ∀ p q, p < (serialize resp).length → q < (serialize resp).length → p ≠ q →
      obase + BitVec.ofNat 64 p ≠ obase + BitVec.ofNat 64 q)
    (hdisj : ∀ p q, p < (serialize resp).length → q < resp.body.length →
      obase + BitVec.ofNat 64 p ≠ src + BitVec.ofNat 64 q)
    (hoA : ∀ p, p < (serialize resp).length →
      s.memaddrs (byteAlign (obase + BitVec.ofNat 64 p)) = true)
    (hsrcR : ∀ j, j < resp.body.length →
      memLoadByte s.memory s.memaddrs s.be (src + BitVec.ofNat 64 j) = some resp.body[j]!)
    (hclock : resp.body.length ≤ s.clock) :
    ∃ s', PancakeSem o (fullRespLit resp obase src) s = (none, s')
      ∧ MemBytesB s'.memory s.memaddrs s.be obase (serialize resp) := by
  have hsplit : (serialize resp).length = (headBytes resp).length + resp.body.length := by
    rw [serialize_head_body, List.length_append]
  -- ===== Phase A: literal head =====
  have hinjH : ∀ p q, p < (headBytes resp).length → q < (headBytes resp).length → p ≠ q →
      obase + BitVec.ofNat 64 p ≠ obase + BitVec.ofNat 64 q :=
    fun p q hp hq hpq => hinj p q (by omega) (by omega) hpq
  obtain ⟨s1, hrunA, hmbA, hframeA, hma1, hbe1, _hloc1, hclk1⟩ :=
    byteLit_landsB o obase (headBytes resp) s hinjH (fun j hj => hoA j (by omega))
  -- ===== Phase B: runtime byte copy of the body =====
  have hlenB63 : resp.body.length < 2 ^ 63 := by omega
  have hdisjB : ∀ i j, i < resp.body.length → j < resp.body.length →
      (obase + BitVec.ofNat 64 (headBytes resp).length) + BitVec.ofNat 64 i
        ≠ src + BitVec.ofNat 64 j := by
    intro i j hi hj
    rw [addr_join]
    exact hdisj _ j (by omega) hj
  have hinjB : ∀ i j, i < resp.body.length → j < resp.body.length → i ≠ j →
      (obase + BitVec.ofNat 64 (headBytes resp).length) + BitVec.ofNat 64 i
        ≠ (obase + BitVec.ofNat 64 (headBytes resp).length) + BitVec.ofNat 64 j := by
    intro i j hi hj hij
    rw [addr_join, addr_join]
    exact hinj _ _ (by omega) (by omega) (by omega)
  have hsrcB : ∀ j, j < resp.body.length →
      memLoadByte s1.memory s1.memaddrs s1.be (src + BitVec.ofNat 64 j)
        = some resp.body[j]! := by
    intro j hj
    rw [hma1, hbe1]
    rw [hframeA (src + BitVec.ofNat 64 j)
        (fun i hi => (hdisj i j (by omega) hj).symm)]
    exact hsrcR j hj
  have hdstAB : ∀ j, j < resp.body.length →
      s1.memaddrs (byteAlign ((obase + BitVec.ofNat 64 (headBytes resp).length)
        + BitVec.ofNat 64 j)) = true := by
    intro j hj
    rw [addr_join, hma1]
    exact hoA _ (by omega)
  obtain ⟨s', hrunB, hlandB, hframeB, hma', hbe'⟩ :=
    copySeg_landsB o (obase + BitVec.ofNat 64 (headBytes resp).length) src
      (fun j => resp.body[j]!) resp.body.length hlenB63 hdisjB hinjB s1
      (by rw [hclk1]; exact hclock) hsrcB hdstAB
  -- ===== assemble the run =====
  refine ⟨s', ?_, ?_⟩
  · show PancakeSem o (fullRespLit resp obase src) s = (none, s')
    rw [fullRespLit, seq_step o hrunA (Nat.le_of_eq hclk1)]
    exact hrunB
  -- ===== assemble the bytes: head ++ body = serialize resp =====
  · rw [serialize_head_body]
    refine membytesB_glue s'.memory s.memaddrs s.be obase (headBytes resp) resp.body ?_ ?_
    · -- head survived the body copy (its addresses are outside the body window)
      intro i hi
      have hne : ∀ j, j < resp.body.length → obase + BitVec.ofNat 64 i
          ≠ (obase + BitVec.ofNat 64 (headBytes resp).length) + BitVec.ofNat 64 j := by
        intro j hj
        rw [addr_join]
        exact hinj i _ (by omega) (by omega) (by omega)
      have e := hframeB (obase + BitVec.ofNat 64 i) hne
      rw [hma1, hbe1] at e
      rw [e]
      exact hmbA i hi
    · -- body landed at offset |head|
      intro j hj
      have e := hlandB j hj
      rw [hma1, hbe1, addr_join] at e
      exact e

/-! ## 3. NON-VACUITY — a concrete 404 with body, compiled FULLY.

`resp404 = HTTP/1.1 404 Not Found, Content-Length: 4, body "nope"` (StructEmit).
The witness: output region at address `0`, body source at `1024` (holding `"nope"`,
byte-addressed via `write_bytearray`), all addresses mapped, 100-tick budget, output
region all-zero. Every hypothesis of `fullRespLit_correct` is discharged, so the
result is a FACT: the emitted program lands the 49 bytes of `serialize resp404`
byte-addressed at address `0`. -/

/-- The witness memory: `resp404`'s body `"nope"` written byte-addressed at `1024`,
zero elsewhere. -/
def wmemFR : Word → Word :=
  writeByteArray (fun _ => true) false 1024 resp404.body (fun _ => 0)

/-- The witness state: every address mapped, 100 ticks, body loaded at `1024`,
output region (address `0`) all-zero. -/
def wstateFR (f : σ) : PancakeState σ :=
  { locals := fun _ => none, memory := wmemFR, memaddrs := fun _ => true, be := false,
    clock := 100, ffi := f, baseAddr := 0 }

/-- The source region genuinely holds `resp404`'s body, byte-addressed. -/
theorem wmemFR_body (j : Nat) (hj : j < resp404.body.length) :
    memLoadByte wmemFR (fun _ => true) false (1024 + BitVec.ofNat 64 j)
      = some resp404.body[j]! := by
  have h := writeByteArray_memBytes (fun _ => true) false resp404.body 1024 (fun _ => 0)
    (by decide) (fun k _ => rfl) j hj
  rw [getElem!_pos resp404.body j hj]
  exact h

/-- **THE FULL RESPONSE FIRES ON A REAL 404.** Not an implication — every side
condition is discharged against `wstateFR`. Running `fullRespLit resp404 0 1024`
terminates normally and leaves the 49 bytes of `serialize resp404` at address `0`,
byte-addressed. The status line `HTTP/1.1 404 Not Found`, the `Content-Length: 4`
header and the framing CRLFs are materialized by the program's literal `StoreByte`s;
the body `"nope"` is COPIED at runtime from `1024` by `copyByteWhile`. -/
theorem fullResp_fires_on_404 (o : Oracle σ) (f : σ) :
    ∃ s', PancakeSem o (fullRespLit resp404 0 1024) (wstateFR f) = (none, s')
      ∧ MemBytesB s'.memory (wstateFR f).memaddrs (wstateFR f).be 0 (serialize resp404) := by
  refine fullRespLit_correct o resp404 0 1024 (wstateFR f) (by decide) ?_ ?_
    (fun p _ => rfl) ?_ (by show (4 : Nat) ≤ 100; omega)
  · -- hinj: the 49-byte output region does not alias itself
    intro p q hp hq hpq
    rw [serialize_resp404_len] at hp hq
    exact fun hEq => hpq (zero_addr_inj (by omega) (by omega) hEq)
  · -- hdisj: output region [0,49) disjoint from source region [1024,1028)
    intro p q hp hq hEq
    rw [serialize_resp404_len] at hp
    rw [show resp404.body.length = 4 from rfl] at hq
    have hL : ((0 : Word) + BitVec.ofNat 64 p).toNat = p := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show ((0 : Word)).toNat = 0 from rfl,
        Nat.mod_eq_of_lt (show p < 2 ^ 64 by omega), Nat.zero_add]
    have hR : ((1024 : Word) + BitVec.ofNat 64 q).toNat = 1024 + q := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
        show ((1024 : Word)).toNat = 1024 from rfl,
        Nat.mod_eq_of_lt (show q < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 1024 + q < 2 ^ 64 by omega)]
    have h1 := congrArg BitVec.toNat hEq
    rw [hL, hR] at h1
    omega
  · -- hsrcR: the source genuinely holds resp404's body -- DISCHARGED, not assumed
    intro j hj
    exact wmemFR_body j hj

/-- **THE PRE-STATE IS NOT THE RESPONSE.** `wstateFR`'s output region (address `0`)
is all-zero, so it does NOT already hold `serialize resp404` (byte 0 is `0`, not
`'H' = 72`). With `fullResp_fires_on_404` this pins the result: the program
TRANSPORTS a state where the conclusion is false to one where it is true — the
response bytes are manufactured by the compiled program, not laundered from the
hypotheses. -/
theorem witness_pre_not_full (f : σ) :
    ¬ MemBytesB (wstateFR f).memory (wstateFR f).memaddrs (wstateFR f).be 0
        (serialize resp404) := by
  intro h
  have h0 : memLoadByte wmemFR (fun _ => true) false ((0 : Word) + BitVec.ofNat 64 0)
      = some (serialize resp404)[0]! := h 0 (by rw [serialize_resp404_len]; omega)
  have hpre : memLoadByte wmemFR (fun _ => true) false ((0 : Word) + BitVec.ofNat 64 0)
      = memLoadByte (fun _ => (0 : Word)) (fun _ => true) false ((0 : Word) + BitVec.ofNat 64 0) := by
    apply writeByteArray_preserves
    intro j hj
    rw [show resp404.body.length = 4 from rfl] at hj
    match j, hj with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
  rw [hpre] at h0
  revert h0
  decide

/-! ## 4. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms membytesB_glue
#print axioms fullRespLit_correct
#print axioms fullResp_fires_on_404
#print axioms witness_pre_not_full

end Pancake.FullResponseCompile
