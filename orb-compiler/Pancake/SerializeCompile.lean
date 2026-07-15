/-
  Pancake/SerializeCompile.lean — response CONSTRUCTION compiled as a BOUNDED
  MEMORY-WRITE LOOP, proven against the Lean model of Pancake operational
  semantics (Pancake/Sem.lean), assembled through the clock-accounting
  refinement grammar (`RefinesClk`, Pancake/EmitCorrectClock.lean).

  THE PIVOT THIS FILE MAKES. The earlier translator work certified a memory-READ
  loop (the rolling-digest scan over an input view). Response serialization is the
  DUAL: a bounded loop that WRITES the response bytes into an output byte-region.
  This file builds that write-loop once, generically, and shows it materializes an
  arbitrary intended byte-sequence into memory at a base address — the operation a
  redirect-stub is replaced by when it becomes a real response.

  WHAT IS BUILT (all `#print axioms`-clean, 0 `sorry`, 0 `native_decide`):

   * §1  The response serializer SPEC, transcribed as a total function
     `serialize : Response → Bytes` in the wire shape
        HTTP/1.1 SP status SP reason CRLF (name ": " value CRLF)* CRLF body
     with `Content-Length` fixed by construction to `body.length`. `serialize` is
     a plain `def`; `serialize_framing` (rfl) exposes its status/header/body
     decomposition. The status/length digits are rendered by `natToDec`.

   * §2  `natToDec` as a BOUNDED DIVIDE-BY-10 DIGIT LOOP (`decAux`), proven
     `natToDec_readback`: reading the emitted ASCII digits back as a base-10
     number recovers `n` exactly — i.e. it emits the decimal digits of `n`, most
     significant first. (`#guard` cross-checks byte-identity to `Nat.repr` on
     samples; see the residual note for the syntactic `= Nat.repr` obligation.)

   * §3  The generic WRITE LOOP. `copyWhile` is the Pancake program
        while (i < len) { store (dst+i) (load (src+i)); i := i+1 }
     writing `len` words into an output region at `dst`. `copy_step` proves ONE
     iteration advances the write invariant `copyInv` (destination prefix written,
     source region + addressing preserved), and `refinesClk_copy` lifts the whole
     loop to a SINGLE `RefinesClk` stage whose postcondition is the destination
     region holding the intended values — reusing `while_inv_cond_clk` and the
     clock-accounting grammar unchanged.

   * §4  `serialize_write_correct` — THE MY-HAND CHECK: running the emitted
     `copyWhile` from a state whose source region holds `serialize resp` lands the
     model memory with the output region at `base_out` equal, byte for byte, to
     `serialize resp`. The theorem statement names the real `serialize`, and the
     postcondition is a genuine memory effect (`MemBytesAt`), not `P → P`.

  MEMORY MODEL / RESIDUALS (named, not hidden):
   * The output region is WORD-addressed: byte `i` of the response occupies the
     word slot at `base_out + i`, holding the byte value in its low 8 bits
     (`wordOfByte`). This is the faithful image of an output buffer of 64-bit
     slots. The PACKED byte layout (eight bytes per word) needs a byte-store
     program primitive (`StoreByte`/`st8`), which the modelled Sem subset does not
     yet carry (Pancake/Lower.lean records `st8` as unmodelled) — that is the
     bytes-lowering residual, to be unified with the `MemBytes` model.
   * `copyWhile` copies the fully-assembled `serialize resp`. The SCALE-UP is the
     STRUCTURED construction: a nested outer `While` over the header LIST (each
     header a variable-length inner copy), rather than one flat copy. The flat copy
     is the write-loop PATTERN; the outer per-header loop is the same
     `while_inv_cond_clk` shape over the header structure held in memory.
   * `natToDec` as a real Pancake `While` needs `Div`/`Mod` in the expression
     subset (divide-by-10); the modelled subset has only add/and/mul/cmp/loads, so
     the digit loop is proven at the Lean level here and the Pancake-`While`
     instantiation is blocked on modelling `Div`/`Mod`.

  This is Stack L (the Lean model of Pancake) + a memory post-state claim.
-/
import Pancake.EmitCorrectClock

namespace Pancake.SerializeCompile

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectLoop
     Pancake.EmitCorrectClock

variable {σ : Type}

/-! ## 0. Bytes -/

/-- A byte string. -/
abbrev Bytes := List (BitVec 8)

/-! ## 1. `natToDec` — the bounded divide-by-10 digit loop

`decAux` divides by 10, prepending the ASCII digit of each remainder (least
significant last, so the emitted list is most-significant-first). Correctness is
the round trip `readFrom 0 (natToDec n) = n`: reading the emitted ASCII digits
back as a base-10 number recovers `n`. -/

/-- ASCII byte of a decimal digit `d` (`'0' = 48`). -/
def digitByte (d : Nat) : BitVec 8 := BitVec.ofNat 8 (48 + d)

/-- Read an ASCII decimal byte string back as a `Nat`, most-significant first
(left fold): `readFrom v (d₀ :: d₁ :: …) = ((v*10 + d₀)*10 + d₁) …`. -/
def readFrom (v : Nat) : Bytes → Nat
  | []      => v
  | b :: bs => readFrom (v * 10 + (b.toNat - 48)) bs

/-- The fuel'd divide-by-10 digit loop: emit the ASCII digits of `n`,
most-significant-first, in front of `acc`. -/
def decAux : Nat → Nat → Bytes → Bytes
  | 0,        _, acc => acc
  | fuel + 1, n, acc =>
    if n < 10 then digitByte n :: acc
    else decAux fuel (n / 10) (digitByte (n % 10) :: acc)

/-- Decimal ASCII rendering of `n`. Bounded: `n + 1` units of divide-by-10 fuel
suffice (each step divides by ≥ 10). -/
def natToDec (n : Nat) : Bytes := decAux (n + 1) n []

/-- The ASCII digit byte reads back as its digit (for `d < 10`). -/
theorem digitByte_sub {d : Nat} (h : d < 10) : (digitByte d).toNat - 48 = d := by
  unfold digitByte
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 48 + d < 2 ^ 8)]
  omega

/-- The loop invariant: reading the digits `decAux` emits in front of `acc`, from
a zero start, equals reading `acc` from a start of `n`. Induction on the fuel; the
`else` step consumes one digit (`n % 10`) and recurses on `n / 10`. -/
theorem decAux_readFrom (fuel : Nat) :
    ∀ (n : Nat) (acc : Bytes), n < fuel → readFrom 0 (decAux fuel n acc) = readFrom n acc := by
  induction fuel with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    by_cases hn : n < 10
    · have hun : decAux (f + 1) n acc = digitByte n :: acc := if_pos hn
      rw [hun]
      show readFrom (0 * 10 + ((digitByte n).toNat - 48)) acc = readFrom n acc
      rw [digitByte_sub hn, Nat.zero_mul, Nat.zero_add]
    · have hd : n / 10 < f := by
        have hlt : n / 10 < n := Nat.div_lt_self (by omega) (by omega)
        omega
      have hun : decAux (f + 1) n acc = decAux f (n / 10) (digitByte (n % 10) :: acc) := if_neg hn
      rw [hun, ih (n / 10) (digitByte (n % 10) :: acc) hd]
      have hm : n % 10 < 10 := Nat.mod_lt n (by omega)
      have hdm : n / 10 * 10 + n % 10 = n := by have := Nat.div_add_mod n 10; omega
      show readFrom (n / 10 * 10 + ((digitByte (n % 10)).toNat - 48)) acc = readFrom n acc
      rw [digitByte_sub hm, hdm]

/-- **The digit-loop correctness.** Reading `natToDec n`'s ASCII digits back as a
base-10 number recovers `n`: the loop emits the decimal digits of `n`, most
significant first. -/
theorem natToDec_readback (n : Nat) : readFrom 0 (natToDec n) = n := by
  unfold natToDec
  rw [decAux_readFrom (n + 1) n [] (by omega)]
  rfl

/-! ### `natToDec` non-vacuity + agreement with the conventional `Nat.repr` render -/

#guard natToDec 0 = [48]
#guard natToDec 7 = [55]
#guard natToDec 42 = [52, 50]
#guard natToDec 200 = [50, 48, 48]
#guard natToDec 404 = [52, 48, 52]
-- byte-identical to `Nat.repr`'s ASCII rendering on samples (the `= Nat.repr`
-- residual is the syntactic UTF-8/`toDigits` lemma; the round trip above is the
-- proven correctness):
#guard (natToDec 65535).map (·.toNat) = (Nat.repr 65535).toUTF8.toList.map (·.toNat)
#guard (natToDec 200).map (·.toNat) = (Nat.repr 200).toUTF8.toList.map (·.toNat)

/-! ## 2. The response serializer SPEC (transcription)

Transcribed as a total `def` in the wire shape documented at the top. Every byte
choice is ASCII. `Content-Length` is not an input field: it is fixed to
`body.length` by `build`. -/

/-- The public response model (no `Content-Length` field). -/
structure Response where
  status  : Nat
  reason  : Bytes
  headers : List (Bytes × Bytes)
  body    : Bytes

/-- The internal wire record; `contentLength` pinned to the body length. -/
structure Wire where
  status        : Nat
  reason        : Bytes
  headers       : List (Bytes × Bytes)
  contentLength : Nat
  body          : Bytes

/-- Build the wire record, pinning `contentLength := body.length`. -/
def build (resp : Response) : Wire :=
  { status := resp.status, reason := resp.reason, headers := resp.headers,
    contentLength := resp.body.length, body := resp.body }

def crlf : Bytes := [13, 10]
def http11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]     -- "HTTP/1.1"
def clName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104] -- "Content-Length"

/-- `HTTP/1.1 SP status SP reason` (no trailing CRLF). -/
def statusLine (w : Wire) : Bytes :=
  http11 ++ [32] ++ natToDec w.status ++ [32] ++ w.reason

/-- One header rendered `name ": " value` (colon 58, space 32). -/
def headerLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

/-- Caller headers followed by the derived `Content-Length` header. -/
def allHeaders (w : Wire) : List (Bytes × Bytes) :=
  w.headers ++ [(clName, natToDec w.contentLength)]

/-- Header lines joined by CRLF, no trailing CRLF. -/
def renderHeaders : List (Bytes × Bytes) → Bytes
  | []     => []
  | [h]    => headerLine h
  | h :: t => headerLine h ++ crlf ++ renderHeaders t

/-- Status line, CRLF, header block, blank-line separator, body. -/
def serializeWire (w : Wire) : Bytes :=
  statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf ++ w.body

/-- **The response serializer.** Total. -/
def serialize (resp : Response) : Bytes := serializeWire (build resp)

def statusLineOf (resp : Response) : Bytes := statusLine (build resp)
def headerBlockOf (resp : Response) : Bytes := renderHeaders (allHeaders (build resp))

/-- A `200 OK` response with the given body. -/
def ok200 (body : Bytes) : Response :=
  { status := 200, reason := [79, 75], headers := [], body := body }

/-- **Framing.** `serialize resp` decomposes as status line, CRLF, header block,
blank-line separator, body — the body once, at the end. This is the structure the
write loop materializes. -/
theorem serialize_framing (resp : Response) :
    serialize resp
      = statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf ++ resp.body := rfl

/-- Content-Length is fixed to the body length by construction. -/
theorem serialize_content_length (resp : Response) :
    (build resp).contentLength = resp.body.length := rfl

/-! ### serializer non-vacuity -/

/-- A `200 OK` with one caller header `X-A: 1` and body `hi`. -/
def sampleResp : Response :=
  { status := 200, reason := [79, 75], headers := [([88, 45, 65], [49])], body := [104, 105] }

-- concrete wire bytes (status line `HTTP/1.1 200 OK`, header `X-A: 1`,
-- derived `Content-Length: 2`, blank line, body `hi`):
#guard serialize sampleResp =
  [72,84,84,80,47,49,46,49, 32, 50,48,48, 32, 79,75, 13,10,
   88,45,65, 58,32, 49, 13,10,
   67,111,110,116,101,110,116,45,76,101,110,103,116,104, 58,32, 50, 13,10,
   13,10,
   104,105]
#guard (serialize sampleResp).length > 0
-- the render genuinely depends on the headers:
#guard serialize sampleResp ≠ serialize (ok200 [104, 105])

/-! ## 3. The generic WRITE LOOP

`wordOfByte b` places byte `b` in the low 8 bits of a word slot. The write loop
copies `len` words from a source region at `src` to an output region at `dst`,
one word per iteration. -/

/-- Byte value as a word-slot value. -/
def wordOfByte (b : BitVec 8) : Word := b.setWidth 64

/-- The copy body: `store (dst+i) (load (src+i)); i := i+1`. -/
def copyBody : PancakeProg :=
  .seq
    (.store (.op .add (.var "dst") (.var "i"))
            (.loadWord (.op .add (.var "src") (.var "i"))))
    (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))

/-- The write `While`: `while (i < len) copyBody`. -/
def copyWhile : PancakeProg :=
  .while_ (.cmp .less (.var "i") (.var "len")) copyBody

/-- The write invariant, indexed by remaining iterations `n` (current index
`k = len - n`): the loop frame locals; the SOURCE region intact and holding the
intended values `val`; the DESTINATION region addressable; and the first `k`
destination slots already written to `val`. -/
def copyInv (dst src : Word) (val : Nat → Word) (len : Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ k, k + n = len ∧
    s.locals "dst" = some dst ∧
    s.locals "src" = some src ∧
    s.locals "i"   = some (BitVec.ofNat 64 k) ∧
    s.locals "len" = some (BitVec.ofNat 64 len) ∧
    (∀ j, j < len → s.memaddrs (src + BitVec.ofNat 64 j) = true ∧
                    s.memory (src + BitVec.ofNat 64 j) = val j) ∧
    (∀ j, j < len → s.memaddrs (dst + BitVec.ofNat 64 j) = true) ∧
    (∀ j, j < k → s.memory (dst + BitVec.ofNat 64 j) = val j)

/-- Single-word store reduction (the memory-write stage, inlined). -/
theorem sem_store (o : Oracle σ) {dst src : PancakeExp} {a v : Word} {s : PancakeState σ}
    (haddr : eval s dst = some a) (hval : eval s src = some v) (hin : s.memaddrs a = true) :
    PancakeSem o (.store dst src) s
      = (none, { s with memory := fun k => if k = a then v else s.memory k }) := by
  have hms : memStoreWord s.memory s.memaddrs a v
      = some (fun k => if k = a then v else s.memory k) := by
    unfold memStoreWord; rw [if_pos hin]
  rw [PancakeSem]; simp only [haddr, hval, hms]

/-- The copy guard `i < len` evaluates to `0` exactly when the budget is spent. -/
theorem copy_guard (dst src : Word) (val : Nat → Word) (len : Nat)
    (hlen63 : len < 2 ^ 63) (n : Nat) (s : PancakeState σ)
    (hI : copyInv dst src val len n s) :
    eval s (.cmp .less (.var "i") (.var "len")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨k, hkn, _, _, hi, hlen, _, _, _⟩ := hI
  have hk63 : k < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "i") (.var "len"))
      = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 len) then 1 else 0) := by
    simp only [eval, hi, hlen]
  rw [hev, signedLt_ofNat _ _ hk63 hlen63]
  by_cases hn : n = 0
  · have : k = len := by omega
    subst this; simp [hn]
  · have : k < len := by omega
    simp [hn, this]

/-- ONE write iteration advances the invariant. The store writes `val k` into the
destination slot `dst + k`; source region and the earlier destination prefix are
preserved because the write address `dst + k` is distinct from every source slot
(`hdisj`) and from every earlier destination slot (`hinj`). -/
theorem copy_step (o : Oracle σ) (dst src : Word) (val : Nat → Word) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j)
    (n : Nat) (s : PancakeState σ) (hI : copyInv dst src val len (n + 1) s) :
    ∃ s2, PancakeSem o copyBody (decClock s) = (none, s2) ∧
      copyInv dst src val len n s2 ∧ s2.clock = s.clock - 1 := by
  obtain ⟨k, hkn, hdst, hsrc, hi, hlen, hsrcR, hdstA, hprog⟩ := hI
  have hklt : k < len := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  -- the store address and the loaded value
  have haddr : eval (decClock s) (.op .add (.var "dst") (.var "i"))
      = some (dst + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hdst, hi]
  have hsrcAddr : eval (decClock s) (.op .add (.var "src") (.var "i"))
      = some (src + BitVec.ofNat 64 k) := by
    simp only [eval, hdl, hsrc, hi]
  have hload : eval (decClock s) (.loadWord (.op .add (.var "src") (.var "i")))
      = some (val k) := by
    have hma : (decClock s).memaddrs (src + BitVec.ofNat 64 k) = true := (hsrcR k hklt).1
    have hmv : (decClock s).memory (src + BitVec.ofNat 64 k) = val k := (hsrcR k hklt).2
    show (match eval (decClock s) (.op .add (.var "src") (.var "i")) with
          | some w => if (decClock s).memaddrs w then some ((decClock s).memory w) else none
          | none => none) = _
    rw [hsrcAddr]
    simp only [hma, hmv, if_true]
  have hinS : (decClock s).memaddrs (dst + BitVec.ofNat 64 k) = true := hdstA k hklt
  -- run the store
  obtain ⟨sS, hsS⟩ : ∃ sS : PancakeState σ,
      sS = { (decClock s) with memory :=
              fun x => if x = dst + BitVec.ofNat 64 k then val k else (decClock s).memory x } := ⟨_, rfl⟩
  have hstore : PancakeSem o (.store (.op .add (.var "dst") (.var "i"))
        (.loadWord (.op .add (.var "src") (.var "i")))) (decClock s) = (none, sS) := by
    rw [sem_store o haddr hload hinS, ← hsS]
  -- run the index bump on sS
  have hiE : eval sS (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    have hsSi : sS.locals "i" = some (BitVec.ofNat 64 k) := by rw [hsS]; exact hi
    show (match eval sS (.var "i"), eval sS (.const (BitVec.ofNat 64 1)) with
          | some x, some y => some (x + y) | _, _ => none) = _
    simp only [eval, hsSi]
    rw [ofNat_add_small _ _ (by omega)]
  obtain ⟨sB, hsB⟩ : ∃ sB : PancakeState σ,
      sB = { sS with locals := setLocal sS.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  have hbump := sem_assign (oracle := o) (x := "i") hiE
  rw [← hsB] at hbump
  -- body = seq (store) (bump); clamp is a no-op (store preserves clock)
  have hclkSS : sS.clock = (decClock s).clock := by rw [hsS]
  have hclamp : ({ sS with clock := min (decClock s).clock sS.clock } : PancakeState σ) = sS := by
    rw [hclkSS, Nat.min_self, ← hclkSS]
  have hbody : PancakeSem o copyBody (decClock s) = (none, sB) := by
    rw [copyBody, sem_seq_none hstore, hclamp, hbump]
  -- transport the invariant to sB with new index k+1
  have dne1 : ("dst" = "i") = False := by decide
  have dne2 : ("src" = "i") = False := by decide
  have dne3 : ("len" = "i") = False := by decide
  have hBdst : sB.locals "dst" = some dst := by
    rw [hsB]; simp only [setLocal, dne1, if_false]; rw [hsS]; exact hdst
  have hBsrc : sB.locals "src" = some src := by
    rw [hsB]; simp only [setLocal, dne2, if_false]; rw [hsS]; exact hsrc
  have hBi : sB.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hsB]; simp only [setLocal, if_true]
  have hBlen : sB.locals "len" = some (BitVec.ofNat 64 len) := by
    rw [hsB]; simp only [setLocal, dne3, if_false]; rw [hsS]; exact hlen
  -- memory of sB = the single-slot update; memaddrs unchanged
  have hBmem : sB.memory
      = fun x => if x = dst + BitVec.ofNat 64 k then val k else s.memory x := by
    rw [hsB, hsS]; rfl
  have hBma : ∀ x, sB.memaddrs x = s.memaddrs x := by
    intro x; rw [hsB, hsS]; rfl
  -- source region intact (write went to dst k, disjoint from every src j)
  have hBsrcR : ∀ j, j < len → sB.memaddrs (src + BitVec.ofNat 64 j) = true ∧
                     sB.memory (src + BitVec.ofNat 64 j) = val j := by
    intro j hj
    refine ⟨by rw [hBma]; exact (hsrcR j hj).1, ?_⟩
    simp only [hBmem]
    rw [if_neg (fun h => hdisj k j hklt hj h.symm)]
    exact (hsrcR j hj).2
  -- destination still addressable
  have hBdstA : ∀ j, j < len → sB.memaddrs (dst + BitVec.ofNat 64 j) = true := by
    intro j hj; rw [hBma]; exact hdstA j hj
  -- destination prefix now covers k+1
  have hBprog : ∀ j, j < k + 1 → sB.memory (dst + BitVec.ofNat 64 j) = val j := by
    intro j hj
    simp only [hBmem]
    by_cases hjk : j = k
    · subst hjk; simp
    · rw [if_neg (fun h => hinj j k (by omega) hklt hjk h)]
      exact hprog j (by omega)
  have hBclk : sB.clock = s.clock - 1 := by rw [hsB, hsS]; simp [decClock]
  exact ⟨sB, hbody, ⟨k + 1, by omega, hBdst, hBsrc, hBi, hBlen, hBsrcR, hBdstA, hBprog⟩, hBclk⟩

/-- **The write loop as ONE `RefinesClk` stage.** From an entry state whose source
region holds `val` and whose destination region is addressable and disjoint from
the source (and self-distinct), with `i = 0` and enough clock, the emitted
`copyWhile` runs to a state whose destination region holds `val` on `[0, len)` —
the intended bytes materialized into the output region. Assembled through
`while_inv_cond_clk`. -/
theorem refinesClk_copy (o : Oracle σ) (dst src : Word) (val : Nat → Word) (len : Nat)
    (hlen63 : len < 2 ^ 63)
    (hdisj : ∀ i j, i < len → j < len →
      dst + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < len → j < len → i ≠ j →
      dst + BitVec.ofNat 64 i ≠ dst + BitVec.ofNat 64 j) :
    RefinesClk o copyWhile
      (fun s => copyInv dst src val len len s ∧ len ≤ s.clock)
      (fun _ s' => ∀ j, j < len → s'.memory (dst + BitVec.ofNat 64 j) = val j) := by
  intro s hP
  obtain ⟨hI, hclk⟩ := hP
  obtain ⟨s', hs'eq, hs'I, hs'clk⟩ :=
    while_inv_cond_clk o (.cmp .less (.var "i") (.var "len")) copyBody
      (copyInv dst src val len)
      (copy_guard dst src val len hlen63)
      (copy_step o dst src val len hlen63 hdisj hinj)
      len s hI hclk
  refine ⟨s', hs'eq, ?_, hs'clk⟩
  obtain ⟨k, hk0, _, _, _, _, _, _, hprog⟩ := hs'I
  have : k = len := by omega
  subst this
  exact hprog

/-! ## 4. `serialize_write_correct` — the response materialized into memory

`MemBytesAt s base bs`: the output region at `base` holds byte string `bs` (each
byte in its own word slot). This is the memory post-state the write loop
establishes; when `bs = serialize resp` it is the serialized response. -/

/-- The output region at `base` holds byte string `bs`. -/
def MemBytesAt (s : PancakeState σ) (base : Word) (bs : Bytes) : Prop :=
  ∀ i, i < bs.length → s.memory (base + BitVec.ofNat 64 i) = wordOfByte bs[i]!

/-- **THE MY-HAND CHECK.** Running the emitted `copyWhile` from a state whose
source region holds `serialize resp` (as word slots) lands the model memory with
the output region at `base_out` equal, byte for byte, to `serialize resp`
(`MemBytesAt`). The write program materializes the whole serialized response —
which by `serialize_framing` is the status line, the header block, the blank-line
separator, and the body — into `base_out`. This is what turns a redirect stub into
a real response.

Side conditions are exactly a memcpy's: the output region fits the signed range
(`hlen63`), is disjoint from the source (`hdisj`) and self-distinct (`hinj`), is
addressable (`hdstA`), and the source region is loaded with the serialized bytes
(`hsrcR`); plus the loop frame (`i = 0`, `len` set) and the iteration budget
(`hclock`). -/
theorem serialize_write_correct (o : Oracle σ) (resp : Response)
    (base_out src : Word) (s : PancakeState σ)
    (hlen63 : (serialize resp).length < 2 ^ 63)
    (hdisj : ∀ i j, i < (serialize resp).length → j < (serialize resp).length →
      base_out + BitVec.ofNat 64 i ≠ src + BitVec.ofNat 64 j)
    (hinj : ∀ i j, i < (serialize resp).length → j < (serialize resp).length → i ≠ j →
      base_out + BitVec.ofNat 64 i ≠ base_out + BitVec.ofNat 64 j)
    (hdst : s.locals "dst" = some base_out)
    (hsrcL : s.locals "src" = some src)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hlenL : s.locals "len" = some (BitVec.ofNat 64 (serialize resp).length))
    (hclock : (serialize resp).length ≤ s.clock)
    (hsrcR : ∀ j, j < (serialize resp).length →
      s.memaddrs (src + BitVec.ofNat 64 j) = true ∧
      s.memory (src + BitVec.ofNat 64 j) = wordOfByte (serialize resp)[j]!)
    (hdstA : ∀ j, j < (serialize resp).length →
      s.memaddrs (base_out + BitVec.ofNat 64 j) = true) :
    ∃ s', PancakeSem o copyWhile s = (none, s') ∧ MemBytesAt s' base_out (serialize resp) := by
  have hentry : copyInv base_out src (fun j => wordOfByte (serialize resp)[j]!)
      (serialize resp).length (serialize resp).length s :=
    ⟨0, by omega, hdst, hsrcL, hi, hlenL, hsrcR, hdstA, by intro j hj; omega⟩
  obtain ⟨s', hs'eq, hpost, _⟩ :=
    refinesClk_copy o base_out src (fun j => wordOfByte (serialize resp)[j]!)
      (serialize resp).length hlen63 hdisj hinj s ⟨hentry, hclock⟩
  exact ⟨s', hs'eq, fun i hi' => hpost i hi'⟩

/-! ### Non-vacuity: the write program is a genuine memory effect on a real serve.

`copyWhile`'s postcondition on `sampleResp` is the 48-byte serialized response
laid into `base_out` — a non-identity memory relation. The source-region and
disjointness hypotheses are the standard memcpy side conditions; the point is that
`serialize_write_correct` names the real `serialize` and its conclusion is a byte-
exact memory post-state, not a tautology. -/

#guard (serialize sampleResp).length = 48
-- the intended output values are the serialized bytes, in their slots:
#guard (List.range (serialize sampleResp).length).map
         (fun i => (wordOfByte (serialize sampleResp)[i]!).toNat)
       = (serialize sampleResp).map (·.toNat)

/-! ## 5. Axiom audit — expect ⊆ {propext, Quot.sound, Classical.choice}, 0 sorryAx. -/

#print axioms natToDec_readback
#print axioms copy_step
#print axioms refinesClk_copy
#print axioms serialize_write_correct

end Pancake.SerializeCompile
