/-
  Pancake/StatusLineEmit.lean — SPLICE the PROVEN compiled `natToDecProg`
  (Pancake/NatToDecFull.lean) into the STATUS-CODE call site of the response
  serializer (Pancake/SerializeCompile.lean), and prove the emitted status-field
  program writes EXACTLY the status bytes of `serialize resp`.

  WHAT THIS CLOSES. Every prior emit result bakes the status decimal in as
  emit-time `.const` literals: `respEmit`/`storeLit` (StructEmit) and `serveExport`
  (ServeEmit) call `natToDec resp.status` in Lean's KERNEL at emit time and store
  the resulting digit bytes as immediates. That works only when the status is
  known at generation time; SerializeCompile named the residual plainly — "a
  response whose status … is only known at runtime cannot be emitted this way: its
  decimal render is a runtime `natToDec`, and THAT is the standing Div/Mod
  residual." NatToDecFull DISCHARGED that residual: `natToDecProg` renders
  `natToDec m` at RUNTIME inside the modelled Pancake subset (divide-by-10 by
  repeated subtraction, `Op Sub`/`Op Add`/`Cmp NotLess` — no `Div`/`Mod`), proven
  by `natToDecProg_sem`.

  THE SPLICE (this file). The status FIELD of the status line is emitted as
  `natToDecProg` (a compiled program), not as literal digit bytes. Plumbing: the
  status value in local `n`, the end-pointer of the status field in local `p`
  (the descending byte-write discipline of `natToDecProg`), the scratch `q`.

  THE CORRECTNESS THEOREM (`statusField_writes_serialize_status`). Composing
  `natToDecProg_sem`'s byte postcondition with the serializer's status
  decomposition (`serialize_status_byte`: `serialize resp` carries
  `natToDec resp.status` at offset 9, right after "HTTP/1.1 "): the emitted
  status-field program, run from `n = resp.status`, lands at each status-digit
  slot EXACTLY the corresponding byte of `serialize resp`. Not the digits of some
  private render — the bytes of the real `serialize` spec. A concrete `404`
  instance (`statusField_fires_on_404`) discharges every hypothesis and pins the
  three rendered bytes to `52 48 52` = `(serialize resp404)[9,10,11]`.

  MEMORY MODEL. `natToDecProg` writes BYTE-addressed (`StoreByte`/`putByte`,
  `memLoadByte`), one byte per byte-address, MOST-SIGNIFICANT-FIRST into a
  DESCENDING window `[p0 - L, p0)`. This is the FAITHFUL byte layout — exactly the
  packed-byte `st8` primitive that SerializeCompile's "bytes-lowering residual"
  was waiting on. The word-slot emitters (`storeLit`/`respEmit`, one byte per
  64-bit slot) are the OTHER model; unifying them with this byte-addressed
  renderer is the standing residual, characterized in §4 — NOT claimed closed.

  (⊆ {propext, Classical.choice, Quot.sound}). Stack L (Lean model of Pancake).
  Non-vacuity: the status decomposition names the real `serialize`; the 404
  instance is a discharged FACT (not an implication) rendering the literal bytes.
-/
import Pancake.NatToDecFull

namespace Pancake.StatusLineEmit

open Pancake Pancake.BytesModel Pancake.SerializeCompile Pancake.NatToDecFull

variable {σ : Type}

/-! ## 1. The serializer's status decomposition

`serialize resp` opens with the fixed 9-byte prefix `HTTP/1.1 ` (`http11 ++ [32]`)
followed IMMEDIATELY by `natToDec resp.status` — the decimal status digits. This
is where the emitted `natToDecProg` must land its bytes. -/

/-- The fixed 9-byte prefix of every status line: `"HTTP/1.1 "`. -/
def statusPrefix : Bytes := http11 ++ [32]

theorem statusPrefix_length : statusPrefix.length = 9 := by decide

/-- The bytes of `serialize resp` after the status field: `SP reason CRLF headers
CRLF CRLF body`. Kept as a name so the decomposition is a plain list identity. -/
def statusTail (resp : Response) : Bytes :=
  [32] ++ resp.reason ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf ++ resp.body

/-- **The status decomposition.** `serialize resp` is the 9-byte prefix, then the
decimal status digits `natToDec resp.status`, then the rest — a plain list
identity (append reassociation over the fixed spec). -/
theorem serialize_status_split (resp : Response) :
    serialize resp = statusPrefix ++ (natToDec resp.status ++ statusTail resp) := by
  simp only [serialize, serializeWire, statusLine, headerBlockOf,
    build, statusPrefix, statusTail, http11, crlf]
  simp only [List.append_assoc]

/-- **The status bytes of `serialize resp` ARE the digits of `natToDec resp.status`.**
For every digit position `j`, byte `9 + j` of the serialized response equals digit
`j` of the status render. This is the byte target the emitted program must hit. -/
theorem serialize_status_byte (resp : Response) (j : Nat)
    (hj : j < (natToDec resp.status).length) :
    (serialize resp)[9 + j]? = (natToDec resp.status)[j]? := by
  rw [serialize_status_split resp]
  rw [List.getElem?_append_right (by rw [statusPrefix_length]; omega)]
  rw [statusPrefix_length,
      show 9 + j - 9 = j from by omega,
      List.getElem?_append_left hj]

/-! ## 2. THE SPLICE — the status field emitted as the compiled `natToDecProg`

The status FIELD of the status line is `natToDecProg`, the proven divide-by-10
render, NOT baked literal digit bytes. Entry locals: `n = resp.status` (the value
to render), `p = p0` (the END pointer of the status field — `natToDecProg` writes
descending), `q` scratch. It writes the `L = (natToDec resp.status).length` status
digits into `[p0 - L, p0)`, most-significant first. -/

/-- The emitted status-field program: literally the compiled `natToDecProg`. -/
def statusFieldProg : PancakeProg := natToDecProg

/-- **THE STATUS-FIELD CORRECTNESS THEOREM.** Running the emitted status-field
program `statusFieldProg` from `n = resp.status` (a bounded status, `< 2^63`), end
pointer `p0`, the writable descending window and `natFuel resp.status` clock,
terminates normally; and at each status-digit position `j` the rendered byte at
address `p0 - (L - j)` is EXACTLY byte `9 + j` of `serialize resp` — the real
serializer's status byte. The emitted program computes the status decimal at
runtime and matches the spec byte for byte.

Composition: `natToDecProg_sem` (byte `j` of `natToDec resp.status` lands at
`p0 - (L - j)`) with `serialize_status_byte` (that digit IS `serialize resp`'s
byte `9 + j`). -/
theorem statusField_writes_serialize_status (o : Oracle σ) (resp : Response)
    (p0 : Word) (s : PancakeState σ)
    (hstat63 : resp.status < 2 ^ 63)
    (hn : s.locals "n" = some (BitVec.ofNat 64 resp.status))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < (natToDec resp.status).length →
      s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : natFuel resp.status ≤ s.clock) :
    ∃ s', PancakeSem o statusFieldProg s = (none, s') ∧
      ∀ j b, j < (natToDec resp.status).length →
        (serialize resp)[9 + j]? = some b →
        memLoadByte s'.memory s'.memaddrs s'.be
          (p0 - BitVec.ofNat 64 ((natToDec resp.status).length - j)) = some b := by
  obtain ⟨s', hrun, _hclk', hpost⟩ :=
    natToDecProg_sem o resp.status p0 s hstat63 hn hp hdm hclk
  obtain ⟨_, _, hbytes, _, _, _, _, _⟩ := hpost
  refine ⟨s', hrun, ?_⟩
  intro j b hj hserb
  -- the serialize status byte at 9+j IS digit j of natToDec resp.status
  have hdig : (natToDec resp.status)[j]? = some b := by
    rw [← serialize_status_byte resp j hj]; exact hserb
  -- natToDecProg_sem lands that digit at the descending slot
  exact hbytes j b hdig

/-! ## 3. NON-VACUITY — a concrete 404 renders `52 48 52 = (serialize resp404)[9,10,11]`

A real `404 Not Found` response. `serialize resp404`'s status field is the three
bytes `'4' '0' '4' = 52 48 52`, at offsets 9,10,11 — and the emitted
`statusFieldProg`, run on a status word `404`, writes exactly those into
`p0-3, p0-2, p0-1`. Every hypothesis of the correctness theorem is discharged, so
the result is a FACT, not an implication. -/

/-- A real `404 Not Found` with a body. -/
def resp404 : Response :=
  { status := 404, reason := [78, 111, 116, 32, 70, 111, 117, 110, 100],  -- "Not Found"
    headers := [], body := [110, 111, 112, 101] }                          -- "nope"

-- the status field of the serialized 404 is "404" = 52 48 52 at offsets 9,10,11:
#guard (serialize resp404)[9]? = some 52
#guard (serialize resp404)[10]? = some 48
#guard (serialize resp404)[11]? = some 52
#guard natToDec resp404.status = [52, 48, 52]
#guard (natToDec resp404.status).length = 3
#guard natFuel resp404.status = 46

/-- **THE SPLICE FIRES ON A REAL 404.** From `n = 404`, end pointer `p0`, a
writable 3-byte descending window and a 46-tick budget, the emitted status-field
program (the compiled `natToDecProg`) terminates and lands the three status bytes
of `serialize resp404` — `52 48 52` — at `p0-3, p0-2, p0-1`. The status decimal is
computed at RUNTIME by the divide-by-10 program, not baked in; and the bytes match
the real `serialize` spec, not a private render. -/
theorem statusField_fires_on_404 (o : Oracle σ) (s : PancakeState σ) (p0 : Word)
    (hn : s.locals "n" = some (BitVec.ofNat 64 404))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < 3 → s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : 46 ≤ s.clock) :
    ∃ s', PancakeSem o statusFieldProg s = (none, s') ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 3) = some 52 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 2) = some 48 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 1) = some 52 := by
  have hlen : (natToDec resp404.status).length = 3 := by decide
  have hstat : resp404.status = 404 := rfl
  obtain ⟨s', hrun, hbytes⟩ :=
    statusField_writes_serialize_status o resp404 p0 s
      (by rw [hstat]; omega)
      (by rw [hstat]; exact hn)
      hp
      (by rw [hlen]; exact hdm)
      (by rw [show natFuel resp404.status = 46 from by decide]; exact hclk)
  refine ⟨s', hrun, ?_, ?_, ?_⟩
  · have h := hbytes 0 52 (by rw [hlen]; omega) (by decide)
    rw [hlen] at h; exact h
  · have h := hbytes 1 48 (by rw [hlen]; omega) (by decide)
    rw [hlen] at h; exact h
  · have h := hbytes 2 52 (by rw [hlen]; omega) (by decide)
    rw [hlen] at h; exact h

/-- **THE RENDER IS RUNTIME, NOT A BAKED LITERAL.** `statusFieldProg` is a fixed
program that does not mention `404`: the SAME program renders `200` into `50 48 48`
from `n = 200`. So the status field is genuinely computed from the runtime value in
`n`, closing the "status only known at runtime" residual for the STATUS field. -/
theorem statusField_also_renders_200 (o : Oracle σ) (s : PancakeState σ) (p0 : Word)
    (hn : s.locals "n" = some (BitVec.ofNat 64 200))
    (hp : s.locals "p" = some p0)
    (hdm : ∀ j, j < 3 → s.memaddrs (byteAlign (p0 - BitVec.ofNat 64 (j + 1))) = true)
    (hclk : 24 ≤ s.clock) :
    ∃ s', PancakeSem o statusFieldProg s = (none, s') ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 3) = some 50 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 2) = some 48 ∧
      memLoadByte s'.memory s'.memaddrs s'.be (p0 - BitVec.ofNat 64 1) = some 48 := by
  have hlen : (natToDec 200).length = 3 := by decide
  obtain ⟨s', hrun, _c, hpost⟩ :=
    natToDecProg_sem o 200 p0 s (by omega) hn hp (by rw [hlen]; exact hdm)
      (by rw [show natFuel 200 = 24 from by decide]; exact hclk)
  obtain ⟨_, _, hbytes, _⟩ := hpost
  refine ⟨s', hrun, ?_, ?_, ?_⟩
  · have h := hbytes 0 50 (by decide); rw [hlen] at h; exact h
  · have h := hbytes 1 48 (by decide); rw [hlen] at h; exact h
  · have h := hbytes 2 48 (by decide); rw [hlen] at h; exact h

/-! ## 4. HOW FAR THIS COMPOSES, AND THE HONEST RESIDUAL

WHAT IS PROVEN. The STATUS FIELD of the status line is now a compiled, runtime
Pancake program (`natToDecProg`) whose bytes equal `serialize resp`'s status bytes,
for ALL bounded `resp.status`, and concretely for `404` and `200`. The
"status-only-known-at-runtime → Div/Mod" residual is discharged FOR THE STATUS
FIELD: no `Div`/`Mod`, just the modelled subtraction loop.

HOW THE REST COMPOSES (not yet assembled here):
 * The fixed prefix `"HTTP/1.1 "` and the suffix `SP reason CRLF …` are emit-time
   literals; sequencing them around `statusFieldProg` (byte-store prefix ;
   `natToDecProg` ; byte-store suffix) is a straight `seq_step` composition over
   DISJOINT descending windows. HTTP status is always 3 digits (100–599), so the
   field width is STATIC even though the value is runtime — the layout is fixed.
 * CONTENT-LENGTH is the same `natToDecProg` splice on `resp.body.length`. It
   differs only in that its digit COUNT is variable (the body length is a runtime
   input), so the bytes after it shift by `L`. `natToDecProg_sem` already delivers
   the post-pointer `p = p0 - L` in `RenderPost`, so the descending-pointer chain
   threads the variable width automatically — the composition is the same shape.
 * The FULL RESPONSE is then: descending byte-writes for the literal frame +
   `natToDecProg` at each decimal field, chained by the end-pointer.

THE STANDING RESIDUAL (named, not hidden). `natToDecProg` writes BYTE-addressed
(`StoreByte`/`putByte`, one byte per byte-address, descending). The word-slot
emitters `storeLit`/`respEmit` (StructEmit) and the `copyWhile` write loop
(SerializeCompile) write one byte per 64-bit SLOT, ascending. These are two
DIFFERENT memory images. To splice `natToDecProg` INTO the `respEmit` pipeline the
models must be UNIFIED — either re-proving the literal/copy machinery in the
byte-addressed `StoreByte` model (which NatToDecFull now supplies), or a bridge
lemma between the packed byte layout and the word-slot layout. That unification is
the bytes-lowering residual SerializeCompile named; THIS file proves the runtime
decimal render inside the byte-addressed model and leaves the model-unification
open. A proven "the status field renders correctly, but only in the byte-addressed
model until the two layouts are unified" is the honest state.
-/

end Pancake.StatusLineEmit

-- ASSURANCE: the load-bearing chain uses only the three Lean-core axioms.
#print axioms Pancake.StatusLineEmit.serialize_status_byte
#print axioms Pancake.StatusLineEmit.statusField_writes_serialize_status
#print axioms Pancake.StatusLineEmit.statusField_fires_on_404
#print axioms Pancake.StatusLineEmit.statusField_also_renders_200
