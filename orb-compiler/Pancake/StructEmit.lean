/-
  Pancake/StructEmit.lean — THE FULL STRUCTURED RESPONSE EMIT, for a response whose
  head is known at emit time. The piece that closes the last "assumed" hypothesis.

  WHAT WAS MISSING. Every prior result in the serialize chain establishes a memory
  post-state *given that the bytes are already somewhere in memory*:

   * `serialize_write_correct` (SerializeCompile) copies `serialize resp` — from a
     source region ASSUMED to already hold `serialize resp` (`hsrcR`). The answer is
     assumed into the question; it proves a memcpy, not a serializer.
   * `writeSegs_correct` / `serialize_structured_correct` (SerializeFull) write a
     segment list — from segment sources ASSUMED loaded (`SourcesOK`).
   * `segWhile_membytes` (SerializeHeaders) and `full_response_membytes`
     (SerializeStruct §3) run the genuine per-header outer loop — from a record array
     and per-segment sources ASSUMED materialized (`hrec`, `hsrc`).

  So the chain proved: *if the response bytes are in memory, a loop can move them*.
  NOTHING in it ever PUT them there. `Pancake/ServeEmit.lean` does materialize bytes
  (`storesInto` emits `st8 out+i, b` per byte) but is UNPROVEN emission glue — no
  theorem relates its stores to `serialize`.

  THIS FILE MATERIALIZES THE BYTES AND PROVES IT. `storeLit base bs` is a
  straight-line sequence of literal word-slot stores, one per byte, and
  `storeLit_membytes` proves — for ALL `bs`, by induction on the byte list — that
  running it lands `MemBytesAt s' base bs`. That is the first result in the chain
  whose source-region hypothesis is NOT "the bytes are already there".

  THE COMPOSITION (`respEmit`, `respEmit_correct`). The full structured response is
  emitted in two phases:

      respEmit resp obase src
        = storeLit obase (headBytes resp)              -- phase A: head, as literals
        ; writeSeg obase |headBytes resp| src |body|   -- phase B: body, by copyWhile

  Phase A materializes the HEAD block — status line, header block, blank-line
  separator (`headBytes`, SerializeStruct §5) — as emit-time literal bytes. Phase B
  copies the BODY at runtime out of a source region with the GENUINE `copyWhile`
  write loop (`writeSeg_correct`, SerializeFull §2). The two regions abut at offset
  `|headBytes resp|` and are glued by `full_response_glue` (SerializeStruct §5) into
  the whole wire response:

      ∃ s', PancakeSem o (respEmit resp obase src) s = (none, s')
            ∧ MemBytesAt s' obase (serialize resp)

  — byte-correct against the `serialize` spec, for ALL `resp`, with the ONLY memory
  hypothesis on the source being that it holds `resp.body` (the body genuinely IS an
  input; the head is not).

  WHY THIS NEEDS NO Div/Mod, AND EXACTLY WHAT DOES. The modelled expression language
  `PancakeExp` has NO division or remainder: `Binop` is `Add`/`And`/`Sub`, plus
  `Mul`. There is no expression that can turn a runtime status word into ASCII
  decimal digits — which is precisely why `natToDec` has no compilation in this
  subset. `respEmit` sidesteps it by CONSTRUCTION rather than by luck: the program is
  generated FROM `resp`, so Lean's kernel evaluates `natToDec resp.status` and
  `natToDec resp.body.length` at emit time and the digits enter the program as
  `.const` literals. `#guard`s in §5 exhibit the baked-in `200` / `404` digits.

  WHAT THIS BUYS AND WHAT IT COSTS (stated plainly, not hidden). The head is
  emit-time constant, so the status, the reason phrase, the caller headers and the
  Content-Length — hence the BODY LENGTH — are fixed when the program is generated.
  The body CONTENT is runtime (copied from `src`). A response whose status or body
  length is only known at runtime cannot be emitted this way: its decimal render is a
  runtime `natToDec`, and THAT is the standing Div/Mod residual. This file is the
  concrete-status case the residual generalizes from, not a claim to have removed it.

  This is Stack L (the Lean model of Pancake) + a memory post-state claim; the same
  word-addressed output model (one byte per word slot) and residuals as
  SerializeStruct / SerializeHeaders / SerializeFull.
-/
import Pancake.SerializeStruct

namespace Pancake.StructEmit

open Pancake Pancake.SerializeCompile Pancake.SerializeFull Pancake.SerializeHeaders
open Pancake.SerializeStruct

variable {σ : Type}

/-! ## 1. Sequencing a normal-terminating, clock-neutral prefix

`Seq c1 c2` clamps the clock between the two halves. When `c1` is clock-neutral (as
every straight-line store is — a store touches memory only), the clamp is the
identity and the sequence is just "run `c1`, then `c2` on its output state". -/

/-- **Forward `Seq` composition** for a clock-neutral, normally-terminating first
half. (`seq_none_inv` in SerializeHeaders is the inversion; this is the introduction
rule, which is what a program CONSTRUCTION needs.) -/
theorem sem_seq_none (o : Oracle σ) {c1 c2 : PancakeProg} {s s1 s' : PancakeState σ}
    (h1 : PancakeSem o c1 s = (none, s1)) (hclk : s1.clock = s.clock)
    (h2 : PancakeSem o c2 s1 = (none, s')) :
    PancakeSem o (.seq c1 c2) s = (none, s') := by
  have hcl : ({ s1 with clock := min s.clock s1.clock } : PancakeState σ) = s1 := by
    rw [hclk, Nat.min_self, ← hclk]
  rw [PancakeSem]
  simp only [h1, clampClock]
  rw [hcl]
  exact h2

/-! ## 2. LITERAL MATERIALIZATION — putting bytes in memory, provably

`storeLit base bs` writes the byte string `bs` into the output region at `base`, one
literal word-slot store per byte, at statically-known addresses. Both operands of
every store are `.const`: no loads, no source region, no loop, no clock. This is the
program a serializer emits for the part of the response it KNOWS. -/

/-- One literal byte store: `store (base + off) (const (wordOfByte b))`. Both operands
are constants — the byte is baked into the program text. -/
def storeLitByte (base : Word) (off : Nat) (b : BitVec 8) : PancakeProg :=
  .store (.const (base + BitVec.ofNat 64 off)) (.const (wordOfByte b))

/-- Straight-line literal materialization of `bs` at `base + off`, in wire order.
Structural on the byte list. -/
def storeLitFrom (base : Word) (off : Nat) : Bytes → PancakeProg
  | []      => .skip
  | b :: bs => .seq (storeLitByte base off b) (storeLitFrom base (off + 1) bs)

/-- **The literal materializer**: lay the byte string `bs` into the region at `base`. -/
def storeLit (base : Word) (bs : Bytes) : PancakeProg := storeLitFrom base 0 bs

/-- **THE MATERIALIZATION IS CORRECT.** For ALL byte strings `bs` and ALL offsets, the
straight-line literal stores land every byte in its slot, preserve every address
outside the written window, and preserve `memaddrs`, the locals, and the clock.
Induction on the byte list: the head store writes `base + off`, and the tail's frame
condition carries it through because `base + off` is distinct from every later slot
(`hinj`).

The window is bounded by `N` and injectivity is assumed on `[0, N)` — the standard
"the output region does not alias itself" side condition, the same one
`serialize_write_correct` carries. NOTE what is NOT assumed: nothing whatsoever about
the CONTENT of memory. The bytes come from the program, not from a region the theorem
quietly hands itself. -/
theorem storeLitFrom_correct (o : Oracle σ) (base : Word) (N : Nat)
    (hinj : ∀ p q, p < N → q < N → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q) :
    ∀ (bs : Bytes) (off : Nat) (s : PancakeState σ), off + bs.length ≤ N →
      (∀ j, j < bs.length → s.memaddrs (base + BitVec.ofNat 64 (off + j)) = true) →
      ∃ s', PancakeSem o (storeLitFrom base off bs) s = (none, s')
        ∧ (∀ j, j < bs.length →
            s'.memory (base + BitVec.ofNat 64 (off + j)) = wordOfByte bs[j]!)
        ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + j)) →
            s'.memory a = s.memory a)
        ∧ (∀ a, s'.memaddrs a = s.memaddrs a)
        ∧ s'.locals = s.locals
        ∧ s'.clock = s.clock := by
  intro bs
  induction bs with
  | nil =>
    intro off s _ _
    refine ⟨s, ?_, by intro j hj; simp at hj, fun _ _ => rfl, fun _ => rfl, rfl, rfl⟩
    show PancakeSem o PancakeProg.skip s = (none, s)
    rw [PancakeSem]
  | cons b bs ih =>
    intro off s hle haddr
    have hlen : off + bs.length + 1 ≤ N := by simp only [List.length_cons] at hle; omega
    have hoff : off < N := by omega
    have haddr0 : s.memaddrs (base + BitVec.ofNat 64 off) = true := by
      have := haddr 0 (by simp); simpa using this
    -- the head store: `base + off := wordOfByte b`
    have h1 := sem_store (o := o) (dst := .const (base + BitVec.ofNat 64 off))
      (src := .const (wordOfByte b)) (a := base + BitVec.ofNat 64 off) (v := wordOfByte b)
      (s := s) rfl rfl haddr0
    obtain ⟨s1, hs1def⟩ : ∃ s1 : PancakeState σ, s1 =
        ({ s with memory := fun k => if k = base + BitVec.ofNat 64 off then wordOfByte b
                                     else s.memory k } : PancakeState σ) := ⟨_, rfl⟩
    rw [← hs1def] at h1
    have hma1 : ∀ a, s1.memaddrs a = s.memaddrs a := by intro a; rw [hs1def]
    have hclk1 : s1.clock = s.clock := by rw [hs1def]
    have hloc1 : s1.locals = s.locals := by rw [hs1def]
    have hmem1 : ∀ a, s1.memory a
        = if a = base + BitVec.ofNat 64 off then wordOfByte b else s.memory a := by
      intro a; rw [hs1def]
    -- the tail, from the post-store state
    have haddr' : ∀ j, j < bs.length →
        s1.memaddrs (base + BitVec.ofNat 64 (off + 1 + j)) = true := by
      intro j hj
      rw [hma1]
      have := haddr (j + 1) (by simp only [List.length_cons]; omega)
      have he : off + (j + 1) = off + 1 + j := by omega
      rw [he] at this; exact this
    obtain ⟨s', hrun, hval, hframe, hma, hloc, hclk⟩ :=
      ih (off + 1) s1 (by omega) haddr'
    refine ⟨s', sem_seq_none o h1 hclk1 hrun, ?_, ?_, ?_, ?_, ?_⟩
    · -- every byte landed
      intro j hj
      cases j with
      | zero =>
        -- the head slot survives the tail's writes (it is distinct from all of them)
        have hne : ∀ k, k < bs.length →
            base + BitVec.ofNat 64 off ≠ base + BitVec.ofNat 64 (off + 1 + k) := by
          intro k hk
          exact hinj off (off + 1 + k) hoff (by omega) (by omega)
        have hfr := hframe (base + BitVec.ofNat 64 off) hne
        simp only [Nat.add_zero]
        rw [hfr, hmem1]
        simp
      | succ j' =>
        have hj' : j' < bs.length := by simp only [List.length_cons] at hj; omega
        have he : off + (j' + 1) = off + 1 + j' := by omega
        rw [he, hval j' hj']
        simp
    · -- frame: outside the whole `b :: bs` window, memory is untouched
      intro a ha
      have haTail : ∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 (off + 1 + j) := by
        intro j hj
        have := ha (j + 1) (by simp only [List.length_cons]; omega)
        have he : off + (j + 1) = off + 1 + j := by omega
        rw [he] at this; exact this
      have hHead : a ≠ base + BitVec.ofNat 64 off := by
        have := ha 0 (by simp); simpa using this
      rw [hframe a haTail, hmem1]
      simp only [hHead, if_false]
    · intro a; rw [hma a, hma1]
    · rw [hloc, hloc1]
    · rw [hclk, hclk1]

/-- **`storeLit` lands the byte string.** For ALL `bs`: running the literal
materializer from a state whose output region is addressable and non-aliasing leaves
`MemBytesAt s' base bs` — the region at `base` holds `bs`, byte for byte. The bytes
came from the program text. -/
theorem storeLit_membytes (o : Oracle σ) (base : Word) (bs : Bytes) (s : PancakeState σ)
    (hinj : ∀ p q, p < bs.length → q < bs.length → p ≠ q →
      base + BitVec.ofNat 64 p ≠ base + BitVec.ofNat 64 q)
    (haddr : ∀ j, j < bs.length → s.memaddrs (base + BitVec.ofNat 64 j) = true) :
    ∃ s', PancakeSem o (storeLit base bs) s = (none, s')
      ∧ MemBytesAt s' base bs
      ∧ (∀ a, (∀ j, j < bs.length → a ≠ base + BitVec.ofNat 64 j) → s'.memory a = s.memory a)
      ∧ (∀ a, s'.memaddrs a = s.memaddrs a)
      ∧ s'.locals = s.locals
      ∧ s'.clock = s.clock := by
  obtain ⟨s', hrun, hval, hframe, hma, hloc, hclk⟩ :=
    storeLitFrom_correct o base bs.length hinj bs 0 s (by omega)
      (by intro j hj; simpa using haddr j hj)
  refine ⟨s', hrun, ?_, ?_, hma, hloc, hclk⟩
  · intro i hi; have := hval i hi; simpa using this
  · intro a ha; exact hframe a (by intro j hj; simpa using ha j hj)

/-! ### 2.1 The emitted straight line is exactly one store per byte

`storeCount` counts the `Store` nodes of a program. `storeCount_storeLit` proves the
materializer emits `|bs|` of them — the emit is genuinely per-byte program text, not a
loop and not a stub. -/

/-- Count the `Store` nodes of a program. -/
def storeCount : PancakeProg → Nat
  | .skip        => 0
  | .store _ _   => 1
  | .seq c1 c2   => storeCount c1 + storeCount c2
  | _            => 0

/-- **The materializer is `|bs|` literal stores**, for ALL `bs`. -/
theorem storeCount_storeLitFrom (base : Word) :
    ∀ (bs : Bytes) (off : Nat), storeCount (storeLitFrom base off bs) = bs.length := by
  intro bs
  induction bs with
  | nil => intro off; rfl
  | cons b bs ih =>
    intro off
    show storeCount (storeLitByte base off b) + storeCount (storeLitFrom base (off + 1) bs)
        = (b :: bs).length
    rw [ih (off + 1)]
    simp only [storeLitByte, storeCount, List.length_cons]
    omega

/-- **`storeLit base bs` is exactly `|bs|` stores.** -/
theorem storeCount_storeLit (base : Word) (bs : Bytes) :
    storeCount (storeLit base bs) = bs.length := storeCount_storeLitFrom base bs 0

/-! ## 3. THE FULL STRUCTURED RESPONSE EMIT

Head as emit-time literals, body by the genuine runtime copy loop, glued at the
blank-line boundary. -/

/-- **The full structured response emitter.** Phase A lays the head block (status
line + header block + blank-line separator) into `obase` as literal byte stores;
phase B copies `|resp.body|` bytes from `src` to `obase + |head|` with the genuine
`copyWhile` write loop (`writeSeg` sets its own `dst/src/i/len` frame). -/
def respEmit (resp : Response) (obase src : Word) : PancakeProg :=
  .seq (storeLit obase (headBytes resp))
       (writeSeg obase (headBytes resp).length src resp.body.length)

/-- The wire response splits by length at the body boundary. -/
theorem serialize_len_split (resp : Response) :
    (serialize resp).length = (headBytes resp).length + resp.body.length := by
  rw [serialize_head_body, List.length_append]

/-- **THE MY-HAND CHECK — THE EMITTED PROGRAM PRODUCES THE SERIALIZED RESPONSE.**
For ALL `resp`: running `respEmit resp obase src` from a state whose output region is
addressable and non-aliasing, and whose source region holds `resp.body`, terminates
normally with the output region at `obase` equal, byte for byte, to `serialize resp`.

Contrast with `serialize_write_correct`, whose hypothesis `hsrcR` assumes the source
already holds `serialize resp` — the conclusion, handed to itself. Here the ONLY
content hypothesis is that `src` holds `resp.body`, an actual runtime input. The
status line, every header, the derived `Content-Length` and the framing CRLFs are
PRODUCED by the program, from literals it carries.

Side conditions are a memcpy's, over the output region: it fits the signed range
(`h63`), does not alias itself (`hinj`), is disjoint from the source (`hdisj`), is
addressable (`hoA`); plus the body-copy iteration budget (`hclock`). -/
theorem respEmit_correct (o : Oracle σ) (resp : Response) (obase src : Word)
    (s : PancakeState σ)
    (h63 : (serialize resp).length < 2 ^ 63)
    (hinj : ∀ p q, p < (serialize resp).length → q < (serialize resp).length → p ≠ q →
      obase + BitVec.ofNat 64 p ≠ obase + BitVec.ofNat 64 q)
    (hdisj : ∀ p q, p < (serialize resp).length → q < resp.body.length →
      obase + BitVec.ofNat 64 p ≠ src + BitVec.ofNat 64 q)
    (hoA : ∀ p, p < (serialize resp).length → s.memaddrs (obase + BitVec.ofNat 64 p) = true)
    (hsrcR : ∀ j, j < resp.body.length →
      s.memaddrs (src + BitVec.ofNat 64 j) = true ∧
      s.memory (src + BitVec.ofNat 64 j) = wordOfByte resp.body[j]!)
    (hclock : resp.body.length ≤ s.clock) :
    ∃ s', PancakeSem o (respEmit resp obase src) s = (none, s')
      ∧ MemBytesAt s' obase (serialize resp) := by
  have hsplit := serialize_len_split resp
  -- ---- phase A: the head, as literals
  have hinjH : ∀ p q, p < (headBytes resp).length → q < (headBytes resp).length → p ≠ q →
      obase + BitVec.ofNat 64 p ≠ obase + BitVec.ofNat 64 q := by
    intro p q hp hq hpq; exact hinj p q (by omega) (by omega) hpq
  obtain ⟨s1, hrunA, hheadA, hframeA, hmaA, hlocA, hclkA⟩ :=
    storeLit_membytes o obase (headBytes resp) s hinjH
      (by intro j hj; exact hoA j (by omega))
  -- ---- phase B: the body, by the genuine copy loop
  have hsrcB : ∀ j, j < resp.body.length →
      s1.memaddrs (src + BitVec.ofNat 64 j) = true ∧
      s1.memory (src + BitVec.ofNat 64 j) = wordOfByte resp.body[j]! := by
    intro j hj
    refine ⟨by rw [hmaA]; exact (hsrcR j hj).1, ?_⟩
    rw [hframeA (src + BitVec.ofNat 64 j) ?_]
    · exact (hsrcR j hj).2
    · intro k hk
      exact fun hEq => hdisj k j (by omega) hj hEq.symm
  have hdstAB : ∀ j, j < resp.body.length →
      s1.memaddrs (obase + BitVec.ofNat 64 ((headBytes resp).length + j)) = true := by
    intro j hj; rw [hmaA]; exact hoA _ (by omega)
  have hinjB : ∀ j j', j < resp.body.length → j' < resp.body.length → j ≠ j' →
      obase + BitVec.ofNat 64 ((headBytes resp).length + j)
        ≠ obase + BitVec.ofNat 64 ((headBytes resp).length + j') := by
    intro j j' hj hj' hne
    exact hinj _ _ (by omega) (by omega) (by omega)
  have hdisjB : ∀ j j', j < resp.body.length → j' < resp.body.length →
      obase + BitVec.ofNat 64 ((headBytes resp).length + j) ≠ src + BitVec.ofNat 64 j' := by
    intro j j' hj hj'
    exact hdisj _ j' (by omega) hj'
  obtain ⟨s', hrunB, hvalB, hframeB, hmaB, hclkB⟩ :=
    writeSeg_correct o obase (headBytes resp).length src
      (fun j => wordOfByte resp.body[j]!) resp.body.length s1
      (by omega) hsrcB hdstAB hinjB hdisjB (by omega)
  refine ⟨s', sem_seq_none o hrunA hclkA hrunB, ?_⟩
  -- ---- the glue: head at obase, body at obase + |head| ⟹ the whole response
  have hlen64 : (serialize resp).length < 2 ^ 64 := lt_pow64_of_lt_pow63 h63
  refine full_response_glue s' obase resp hlen64 ?_ ?_
  · -- the head survived phase B (its slots are disjoint from the body window)
    intro i hi
    rw [hframeB (obase + BitVec.ofNat 64 i) ?_]
    · exact hheadA i hi
    · intro j hj
      exact hinj i _ (by omega) (by omega) (by omega)
  · -- the body landed at offset |head|
    intro j hj
    rw [seg_addr obase (headBytes resp).length j (by omega)]
    exact hvalB j hj

/-! ## 4. The head is program text, not data

`respEmit` performs no arithmetic on the response and no load outside the body copy:
`storeLit` is `.const`-to-`.const` stores. The head bytes are Lean-evaluated at emit
time, so the emitted program is determined by `resp` alone — there is nowhere in the
definition for a runtime dependency to enter. -/

/-- **The emitted program is determined by the head block and the body LENGTH.** Two
responses agreeing on those emit literally the same program — so the body CONTENT is
`respEmit`'s only runtime data dependency. -/
theorem respEmit_determined (resp resp' : Response) (obase src : Word)
    (hh : headBytes resp = headBytes resp')
    (hb : resp.body.length = resp'.body.length) :
    respEmit resp obase src = respEmit resp' obase src := by
  rw [respEmit, respEmit, hh, hb]

/-- **The emit is exactly `|head|` literal stores followed by the body copy.** -/
theorem respEmit_storeCount (resp : Response) (obase src : Word) :
    storeCount (respEmit resp obase src)
      = (headBytes resp).length + storeCount (writeSeg obase (headBytes resp).length
          src resp.body.length) := by
  show storeCount (storeLit obase (headBytes resp))
      + storeCount (writeSeg obase (headBytes resp).length src resp.body.length) = _
  rw [storeCount_storeLit]

/-! ## 5. Non-vacuity on REAL responses — a 200 and a 404

The emit-time decimal render is exhibited: `natToDec 200` and `natToDec 404` are
evaluated by Lean's kernel into the head literals, so the emitted program carries the
digit bytes `50 48 48` ("200") and `52 48 52` ("404") with no runtime `Div`/`Mod` —
which the expression language could not express anyway. -/

/-- A real `404 Not Found` with a body — the second concrete-status case. -/
def resp404 : Response :=
  { status := 404, reason := [78, 111, 116, 32, 70, 111, 117, 110, 100],  -- "Not Found"
    headers := [], body := [110, 111, 112, 101] }                          -- "nope"

-- the two concrete-status heads are genuinely distinct, non-trivial byte strings:
#guard (headBytes sampleResp).length = 46
#guard (headBytes resp404).length = 45
#guard headBytes sampleResp ≠ headBytes resp404

-- THE STATUS DECIMAL IS BAKED IN AT EMIT TIME (`natToDec 200 = "200"`, `404 = "404"`):
#guard natToDec 200 = [50, 48, 48]
#guard natToDec 404 = [52, 48, 52]
#guard (headBytes sampleResp).take 15
       = [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75]  -- "HTTP/1.1 200 OK"
#guard (headBytes resp404).take 22
       = [72, 84, 84, 80, 47, 49, 46, 49, 32, 52, 48, 52, 32,           -- "HTTP/1.1 404 "
          78, 111, 116, 32, 70, 111, 117, 110, 100]                     -- "Not Found"
-- the DERIVED Content-Length decimal is a literal too (body "nope" ⟹ 4):
#guard (headBytes resp404).drop 22
       = [13, 10,                                                        -- CRLF
          67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32,
          52,                                                            -- "4"
          13, 10, 13, 10]                                                -- CRLF CRLF

-- head ++ body IS the wire response, for both — so the emit's two phases tile it:
#guard headBytes resp404 ++ resp404.body = serialize resp404
#guard (serialize resp404).length = 49
#guard headBytes sampleResp ++ sampleResp.body = serialize sampleResp
#guard (serialize sampleResp).length = 48

-- the emitted phase-A straight line is a genuine per-byte store sequence (45 / 46
-- literal stores), not a stub and not a loop:
#guard storeCount (storeLit 0 (headBytes resp404)) = 45
#guard storeCount (storeLit 0 (headBytes sampleResp)) = 46
#guard storeCount (storeLit 0 (headBytes resp404)) = (headBytes resp404).length
-- the body phase adds NO straight-line store — it is the `copyWhile` LOOP, whose store
-- is inside the `While` body (`storeCount` does not descend into loops). So the whole
-- emit is 45 literal head stores + a loop, exactly the two-phase shape claimed:
#guard storeCount (respEmit resp404 0 64) = 45
#guard storeCount (writeSeg 0 45 64 4) = 0

/-! ### 5.1 THE HYPOTHESES FIRE — a concrete witness state for the 404

A theorem with unsatisfiable hypotheses is green and worthless. `respEmit_correct`'s
side conditions are discharged here against a REAL state — output region at address
`0`, body source at `1024`, all addresses mapped, a 100-tick budget, `resp404`'s body
`"nope"` loaded at the source — with NOTHING assumed about the output region's
contents. The conclusion is then a fact, not an implication: running the emitted
program on `witnessState` lands the 49 bytes of `serialize resp404` at address `0`.

(Note the contrast: `ServeSlice.lean:249` consumes `serialize_write_correct` by
passing its `hsrcR` along as an assumption — the "source already holds the serialized
response" obligation is never discharged, only forwarded. Here it is discharged.) -/

/-- Address injectivity at base `0`, on the word range. -/
theorem zero_addr_inj {p q : Nat} (hp : p < 2 ^ 64) (hq : q < 2 ^ 64)
    (h : (0 : Word) + BitVec.ofNat 64 p = (0 : Word) + BitVec.ofNat 64 q) : p = q := by
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt hq] at h1
  omega

/-- The witness memory: `resp404`'s body `"nope"` at `1024`, zero elsewhere. Note the
output region (address `0`) holds ZERO — the response bytes are not hiding here. -/
def wmem : Word → Word := fun a =>
  if a = 1024 then wordOfByte 110 else
  if a = 1025 then wordOfByte 111 else
  if a = 1026 then wordOfByte 112 else
  if a = 1027 then wordOfByte 101 else 0

/-- The witness state: every address mapped, 100 ticks, body loaded at `1024`. -/
def witnessState (f : σ) : PancakeState σ :=
  { locals := fun _ => none, memory := wmem, memaddrs := fun _ => true,
    be := false, clock := 100, ffi := f, baseAddr := 0 }

theorem serialize_resp404_len : (serialize resp404).length = 49 := by rfl

/-- **THE THEOREM FIRES ON A REAL 404.** Not an implication — every side condition is
discharged against `witnessState`. Running the emitted `respEmit resp404 0 1024`
terminates normally and leaves the 49 bytes of `serialize resp404` at address `0`,
having read only the 4-byte body from `1024`. The status line `HTTP/1.1 404 Not
Found`, the `Content-Length: 4` header and the framing CRLFs were produced by the
program from its own literals. -/
theorem respEmit_fires_on_404 (o : Oracle σ) (f : σ) :
    ∃ s', PancakeSem o (respEmit resp404 0 1024) (witnessState f) = (none, s')
      ∧ MemBytesAt s' 0 (serialize resp404) := by
  refine respEmit_correct o resp404 0 1024 (witnessState f) (by decide) ?_ ?_ ?_ ?_
    (by show (4 : Nat) ≤ 100; omega)
  · -- hinj: the 49-byte output region does not alias itself
    intro p q hp hq hpq
    rw [serialize_resp404_len] at hp hq
    exact fun hEq => hpq (zero_addr_inj (by omega) (by omega) hEq)
  · -- hdisj: the output region [0,49) is disjoint from the source region [1024,1028)
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
  · -- hoA: every address is mapped
    intro p _; rfl
  · -- hsrcR: the source region genuinely holds resp404 body bytes -- DISCHARGED, not assumed
    intro j hj
    rw [show resp404.body.length = 4 from rfl] at hj
    refine ⟨rfl, ?_⟩
    show wmem (1024 + BitVec.ofNat 64 j) = wordOfByte resp404.body[j]!
    match j, hj with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide

/-- **THE PRE-STATE IS NOT THE POST-STATE.** `witnessState` does NOT already hold the
serialized response at the output region (its byte 0 is `0`, not `'H'` = 72). Together
with `respEmit_fires_on_404` this pins the result down completely: the emitted program
transports a state where the conclusion is FALSE to one where it is TRUE. The response
bytes are manufactured by the program, not laundered from the hypotheses. -/
theorem witness_pre_not_response (f : σ) :
    ¬ MemBytesAt (witnessState f) 0 (serialize resp404) := by
  intro h
  have h0 := h 0 (by rw [serialize_resp404_len]; omega)
  revert h0
  show wmem ((0 : Word) + BitVec.ofNat 64 0) ≠ wordOfByte (serialize resp404)[0]!
  decide

/-! ## 6. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms sem_seq_none
#print axioms storeLitFrom_correct
#print axioms storeLit_membytes
#print axioms storeCount_storeLit
#print axioms serialize_len_split
#print axioms respEmit_correct
#print axioms respEmit_determined
#print axioms respEmit_storeCount
#print axioms zero_addr_inj
#print axioms respEmit_fires_on_404
#print axioms witness_pre_not_response

end Pancake.StructEmit
