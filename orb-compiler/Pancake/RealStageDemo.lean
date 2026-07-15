/-
  Pancake/RealStageDemo.lean — THE PIVOT WITNESS: a REAL serve stage with a
  BYTE-EFFECT (not a word-decision) compiled by the EXTENDED translator
  (bytes-lowering + STORE + bounded write-loop) and proven byte-for-byte, additive
  over Pancake/EmitCorrectClock.lean (nothing there is modified or re-proven).

  WHY THIS FILE. The six translator stages proven so far are WORD-DECISIONS: each
  computes a single word (a flag, a digest) and its correctness statement is a
  word equality. A real serve response is BYTES: appending a header line writes the
  byte sequence `name ": " value CRLF` into the output buffer (the serve
  serializer's `headerLine h ++ crlf`). To show the data-lowering unlocks REAL
  stages we take exactly that stage — the header-append — express it in the
  translator's `Stage` grammar, run the translator (`emit`), and prove the effect
  at the BYTE level: reading the output buffer back through the panSem byte-read
  model (`memLoadByte`/`byteAlign`/`getByte`) yields the intended header bytes.

  This is a genuine byte-effect: the correctness statement is byte-ADDRESSED and
  goes through the endianness-bearing byte substrate (§1 of Pancake/Sem.lean, the
  faithfulness hot-spot), not a single-word equality. Two theorems:

   * `hdrStore_byte_effect`  — the STRAIGHT-LINE header-append stage: the
     translator-emitted `Store` writes the packed header word, and every byte of
     the output region reads back as the getByte-decomposition of that word (the
     data-lowering). SYMBOLIC in the output address.
   * `hdrStore_ascii`        — the CONCRETE non-vacuity witness: a literal header
     line "X: 1" CRLF stored at the base, whose six output bytes read back as the
     exact ASCII codes [88,58,32,49,13,10] = `X`,`:`,` `,`1`,CR,LF. Real lowering →
     real memory bytes, decided in-kernel (no `native_decide`/`ofReduceBool`).
   * `hdrFill_loop_byte_effect` — the WRITE-LOOP stage: a bounded `While` that
     appends the header word to `n` consecutive output slots, certified through the
     reusable loop rule `while_inv_cond_clk`, with the byte-effect over the whole
     `8·n`-byte region. This exercises the loop machinery (emitLoopSchema shape /
     RefinesClk / while_inv_cond) on a BYTE-writing body, not a word-decision.

  BYTES-LOWERING INTERFACE. The header→word packing (`packBE`) and the byte
  read-back (`viewByte`) are the data-model lowering. They are REAL definitions
  over `Pancake.Sem`'s byte substrate (`getByte`, `memLoadByte`, `byteAlign`) — NOT
  axioms — so the theorems are non-vacuous. A sibling bytes/serialize model may
  later own a richer packer (variable-length, multi-word `write_bytearray`); this
  file's `packBE` is the ≤8-byte-per-word stub of that interface, noted in §1.

  ASSURANCE: `#print axioms` on each theorem (see Pancake/build_realstage.sh);
  0 `sorry`, no `native_decide`/`decide`-of-`ofReduceBool`, axioms ⊆
  {propext, Quot.sound, Classical.choice}.

  This is Stack L (the Lean model of Pancake). NO machine-code claims here.
-/
import Pancake.EmitCorrectClock

namespace Pancake.RealStageDemo

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.EmitCorrectClock

variable {σ : Type}

/-! ## 1. The bytes-lowering: header line → packed word, and the byte view

`packBE bs` packs up to 8 bytes big-endian into a 64-bit word: byte `j` of the
list lands at byte position `j` of the word under the big-endian `byteIndex`
(`byteIndex j true = 8·(7-j)`), so `getByte (a) (packBE bs) true = bs[a mod 8]`.
This is the ≤8-byte-per-word STUB of the general `write_bytearray` lowering (a
sibling model may generalise to arbitrary length / multi-word). -/
def packBE (bs : List (BitVec 8)) : Word :=
  (List.range bs.length).foldl
    (fun w j => w ||| ((bs[j]!.setWidth 64) <<< (8 * (7 - j)))) 0

/-- The serve serializer's rendered header line: `name ": " value CRLF`
(colon=58, space=32, CR=13, LF=10), the exact bytes `headerLine h ++ crlf`
appends to the output. -/
def headerLineBytes (name value : List (BitVec 8)) : List (BitVec 8) :=
  name ++ [58, 32] ++ value ++ [13, 10]

/-! ## 2. The straight-line header-append stage, in the translator grammar

The stage stores the packed header word at the output cursor held in local
`"out"`. It is a `Prim` leaf of the `Stage` grammar (Pancake/EmitCorrectCompose),
so `emit` compiles it and `refines_store` discharges its refinement — no bespoke
`.pnk`. -/

/-- The header-append primitive leaf: `Store (Var "out") (Const hdr)` with its
memory-write denotation. -/
def hdrStorePrim (hdr : Word) : Prim σ :=
  { prog := .store (.var "out") (.const hdr)
    den  := fun s => { s with memory := fun k =>
              if k = (s.locals "out").getD 0 then hdr else s.memory k } }

/-- The header-append stage. -/
def hdrStage (hdr : Word) : Stage σ := .prim (hdrStorePrim hdr)

/-- THE BYTE-EFFECT (symbolic address). The translator-emitted program for the
header-append stage runs to a state whose output region, read back through the
panSem byte model, is EXACTLY the getByte-decomposition of the stored header
word. `haln` is the alignment side-condition (`out` is word-aligned, so
`byteAlign (out+j) = out` for `j < 8`); `hin` says the slot is mapped. This is a
byte-ADDRESSED statement over the endianness substrate, not a word equality. -/
theorem hdrStore_byte_effect (o : Oracle σ) (hdr outAddr : Word)
    (s : PancakeState σ)
    (hout : s.locals "out" = some outAddr)
    (hin : s.memaddrs outAddr = true)
    (haln : ∀ j, j < 8 → byteAlign (outAddr + BitVec.ofNat 64 j) = outAddr) :
    ∃ s', PancakeSem o (emit (hdrStage (σ := σ) hdr)) s = (none, s') ∧
      s'.memaddrs = s.memaddrs ∧
      ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs s.be (outAddr + BitVec.ofNat 64 j)
          = some (getByte (outAddr + BitVec.ofNat 64 j) hdr s.be) := by
  -- the emitted program is the STORE
  have hemit : emit (hdrStage (σ := σ) hdr) = .store (.var "out") (.const hdr) := rfl
  -- reduce the store
  have hms : memStoreWord s.memory s.memaddrs outAddr hdr
      = some (fun k => if k = outAddr then hdr else s.memory k) := by
    unfold memStoreWord; rw [if_pos hin]
  refine ⟨{ s with memory := fun k => if k = outAddr then hdr else s.memory k }, ?_, rfl, ?_⟩
  · rw [hemit, PancakeSem]
    simp only [eval, hout, hms]
  · intro j hj
    have hba : byteAlign (outAddr + BitVec.ofNat 64 j) = outAddr := haln j hj
    have hmem : (fun k => if k = outAddr then hdr else s.memory k) outAddr = hdr := by simp
    show memLoadByte (fun k => if k = outAddr then hdr else s.memory k) s.memaddrs s.be
          (outAddr + BitVec.ofNat 64 j)
        = some (getByte (outAddr + BitVec.ofNat 64 j) hdr s.be)
    unfold memLoadByte
    rw [hba, if_pos hin, hmem]

/-! ### Concrete non-vacuity: a literal header line lands as ASCII bytes

The header `name="X"`, `value="1"` renders to `"X: 1" CRLF` = the six bytes
`[88,58,32,49,13,10]`. Stored at the (aligned) base address `0` with big-endian
byte order, each output byte reads back as the exact ASCII code — decided
in-kernel. This is the "real lowering → real memory effect" witness. -/

/-- The concrete header word for `"X: 1" CRLF`. -/
def demoHdr : Word := packBE (headerLineBytes [88] [49])

theorem hdrStore_ascii (o : Oracle σ) (s : PancakeState σ)
    (hbe : s.be = true)
    (hout : s.locals "out" = some 0)
    (hin : s.memaddrs 0 = true) :
    ∃ s', PancakeSem o (emit (hdrStage (σ := σ) demoHdr)) s = (none, s') ∧
      [ memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 0),
        memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 1),
        memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 2),
        memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 3),
        memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 4),
        memLoadByte s'.memory s'.memaddrs true ((0 : Word) + BitVec.ofNat 64 5) ]
        = [some 88, some 58, some 32, some 49, some 13, some 10] := by
  obtain ⟨s', hrun, _, hbytes⟩ :=
    hdrStore_byte_effect o demoHdr 0 s hout hin
      (by
        intro j hj
        have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
        rcases this with h|h|h|h|h|h|h|h <;> subst h <;> decide)
  refine ⟨s', hrun, ?_⟩
  -- each byte: symbolic byte-effect (rewriting s.be to true), then in-kernel decision
  have e0 := hbytes 0 (by decide); rw [hbe] at e0
  have e1 := hbytes 1 (by decide); rw [hbe] at e1
  have e2 := hbytes 2 (by decide); rw [hbe] at e2
  have e3 := hbytes 3 (by decide); rw [hbe] at e3
  have e4 := hbytes 4 (by decide); rw [hbe] at e4
  have e5 := hbytes 5 (by decide); rw [hbe] at e5
  rw [e0, e1, e2, e3, e4, e5]
  decide

/-! ## 3. The WRITE-LOOP header-append stage

A bounded `While` that appends the header word to `n` consecutive output slots
(slot `k` at byte address `8·k` from the buffer base `0`). This is a BYTE-writing
loop body (`Store` into flat byte-memory), certified through the SAME reusable
loop rule the byte-READING scan uses (`while_inv_cond_clk`, Pancake/
EmitCorrectClock) — the pivot's loop machinery on a write, not a word-decision.
The loop maintains a cursor local `"cur"` bumped by 8 each iteration; the store
target is the cursor. -/

/-- One `Store`-reduction: a `Store dst src` whose address/value evaluate and
whose address is mapped runs to the single-word memory update. -/
theorem sem_store_ok (o : Oracle σ) (dst src : PancakeExp) (s : PancakeState σ)
    (addr val : Word) (hd : eval s dst = some addr) (hv : eval s src = some val)
    (hin : s.memaddrs addr = true) :
    PancakeSem o (.store dst src) s
      = (none, { s with memory := fun k => if k = addr then val else s.memory k }) := by
  have hms : memStoreWord s.memory s.memaddrs addr val
      = some (fun k => if k = addr then val else s.memory k) := by
    unfold memStoreWord; rw [if_pos hin]
  rw [PancakeSem]; simp only [hd, hv, hms]

/-- The write-loop body: store the header word at the cursor, bump the cursor by
8, bump the index. -/
def fillBody (hdr : Word) : PancakeProg :=
  .seq
    (.seq (.store (.var "cur") (.const hdr))
          (.assign "cur" (.op .add (.var "cur") (.const (BitVec.ofNat 64 8)))))
    (.assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))))

/-- The write-loop: `while i < n` do the fill body. -/
def fillWhile (hdr : Word) : PancakeProg :=
  .while_ (.cmp .less (.var "i") (.var "n")) (fillBody hdr)

/-- The write-loop, as a translator `Stage`-emitted `While` over a two-leaf body
`Stage` (`emit fillBodyStage = fillBody`). The leaves' `den` are irrelevant to the
loop certificate (the loop contract is carried by `fillInv`, not a total
`Refines`), so they are identity placeholders. -/
def fillBodyStage (hdr : Word) : Stage σ :=
  .seq (.seq (.prim { prog := .store (.var "cur") (.const hdr), den := fun s => s })
             (.prim { prog := .assign "cur" (.op .add (.var "cur") (.const (BitVec.ofNat 64 8))),
                      den := fun s => s }))
       (.prim { prog := .assign "i" (.op .add (.var "i") (.const (BitVec.ofNat 64 1))),
                den := fun s => s })

theorem emit_fillBody (hdr : Word) :
    emit (fillBodyStage (σ := σ) hdr) = fillBody hdr := rfl

/-- The write-loop invariant with `m` slots still to fill: the index/cursor track
`k = n - m`, every already-filled slot `< k` holds the header word, and every
slot `< n` is mapped. -/
def fillInv (hdr : Word) (n : Nat) (m : Nat) (s : PancakeState σ) : Prop :=
  ∃ k, k + m = n ∧
    s.locals "i"   = some (BitVec.ofNat 64 k) ∧
    s.locals "cur" = some (BitVec.ofNat 64 (8 * k)) ∧
    s.locals "n"   = some (BitVec.ofNat 64 n) ∧
    (∀ j, j < k → s.memory (BitVec.ofNat 64 (8 * j)) = hdr) ∧
    (∀ j, j < n → s.memaddrs (BitVec.ofNat 64 (8 * j)) = true)

/-- Distinct slot addresses: `8·j ≠ 8·k` (as words) for `j ≠ k` in range. The one
BitVec fact the memory frame needs. -/
theorem slot_ne (n j k : Nat) (hj : j < n) (hk : k < n) (h8n : 8 * n < 2 ^ 64)
    (hjk : j ≠ k) : BitVec.ofNat 64 (8 * j) ≠ BitVec.ofNat 64 (8 * k) := by
  intro hc
  apply hjk
  have := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat] at this
  omega

/-- The write-loop guard `i < n` = `0` exactly when the budget is spent. -/
theorem fill_guard (hdr : Word) (n : Nat) (hn63 : n < 2 ^ 63)
    (m : Nat) (s : PancakeState σ) (hI : fillInv hdr n m s) :
    eval s (.cmp .less (.var "i") (.var "n")) = some (if m = 0 then (0 : Word) else 1) := by
  obtain ⟨k, hkm, hi, _, hn, _, _⟩ := hI
  have hk63 : k < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "i") (.var "n"))
      = some (if signedLt (BitVec.ofNat 64 k) (BitVec.ofNat 64 n) then 1 else 0) := by
    simp only [eval, hi, hn]
  rw [hev, signedLt_ofNat _ _ hk63 hn63]
  by_cases hm : m = 0
  · have : k = n := by omega
    subst this; simp [hm]
  · have : k < n := by omega
    simp [hm, this]

/-- ONE write-loop iteration advances the invariant, consuming one clock tick: the
store fills slot `k`, and the cursor/index bump to `k+1`, with every earlier slot
preserved by `slot_ne`. -/
theorem fill_step (o : Oracle σ) (hdr : Word) (n : Nat) (h8n : 8 * n < 2 ^ 64)
    (m : Nat) (s : PancakeState σ) (hI : fillInv hdr n (m + 1) s) :
    ∃ s2, PancakeSem o (fillBody hdr) (decClock s) = (none, s2) ∧
      fillInv hdr n m s2 ∧ s2.clock = s.clock - 1 := by
  obtain ⟨k, hkm, hi, hcur, hn, hmem, haddr⟩ := hI
  have hkn : k < n := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  -- (1) the store at cur = ofNat (8k)
  have hcurE : eval (decClock s) (.var "cur") = some (BitVec.ofNat 64 (8 * k)) := by
    show (decClock s).locals "cur" = _; rw [hdl]; exact hcur
  have hinK : (decClock s).memaddrs (BitVec.ofNat 64 (8 * k)) = true := haddr k hkn
  have hstore := sem_store_ok o (.var "cur") (.const hdr) (decClock s)
                   (BitVec.ofNat 64 (8 * k)) hdr hcurE rfl hinK
  obtain ⟨s0, hs0⟩ : ∃ s0 : PancakeState σ, s0 = { decClock s with
      memory := fun key => if key = BitVec.ofNat 64 (8 * k) then hdr
                           else (decClock s).memory key } := ⟨_, rfl⟩
  rw [← hs0] at hstore
  -- (2) the cursor bump on s0
  have hs0cur : s0.locals "cur" = some (BitVec.ofNat 64 (8 * k)) := by rw [hs0]; exact hcur
  have hcurE2 : eval s0 (.op .add (.var "cur") (.const (BitVec.ofNat 64 8)))
      = some (BitVec.ofNat 64 (8 * (k + 1))) := by
    show (match eval s0 (.var "cur"), eval s0 (.const (BitVec.ofNat 64 8)) with
          | some a, some b => some (a + b) | _, _ => none) = _
    simp only [eval, hs0cur]
    rw [ofNat_add_small _ _ (by omega : 8 * k + 8 < 2 ^ 64), Nat.mul_succ]
  have hcurA := sem_assign (oracle := o) (x := "cur") hcurE2
  obtain ⟨s1, hs1⟩ : ∃ s1 : PancakeState σ,
      s1 = { s0 with locals := setLocal s0.locals "cur" (BitVec.ofNat 64 (8 * (k + 1))) } := ⟨_, rfl⟩
  rw [← hs1] at hcurA
  -- (3) the index bump on s1
  have h0i : s0.locals "i" = some (BitVec.ofNat 64 k) := by rw [hs0]; exact hi
  have hs1i : s1.locals "i" = some (BitVec.ofNat 64 k) := by
    rw [hs1]; simp only [setLocal]; rw [if_neg (by decide)]; exact h0i
  have hiE : eval s1 (.op .add (.var "i") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (k + 1)) := by
    show (match eval s1 (.var "i"), eval s1 (.const (BitVec.ofNat 64 1)) with
          | some a, some b => some (a + b) | _, _ => none) = _
    simp only [eval, hs1i]
    rw [ofNat_add_small _ _ (by omega : k + 1 < 2 ^ 64)]
  have hiA := sem_assign (oracle := o) (x := "i") hiE
  obtain ⟨s2, hs2⟩ : ∃ s2 : PancakeState σ,
      s2 = { s1 with locals := setLocal s1.locals "i" (BitVec.ofNat 64 (k + 1)) } := ⟨_, rfl⟩
  rw [← hs2] at hiA
  -- (4) assemble the body (nested Seq); the clamps are no-ops (store/assign keep clock)
  have hclk0 : s0.clock = (decClock s).clock := by rw [hs0]
  have hclk1 : s1.clock = (decClock s).clock := by rw [hs1, hclk0]
  have hclamp0 : ({ s0 with clock := min (decClock s).clock s0.clock } : PancakeState σ) = s0 := by
    rw [hclk0, Nat.min_self, ← hclk0]
  have hclamp1 : ({ s1 with clock := min (decClock s).clock s1.clock } : PancakeState σ) = s1 := by
    rw [hclk1, Nat.min_self, ← hclk1]
  have h_inner : PancakeSem o (.seq (.store (.var "cur") (.const hdr))
      (.assign "cur" (.op .add (.var "cur") (.const (BitVec.ofNat 64 8))))) (decClock s)
      = (none, s1) := by
    rw [sem_seq_none (oracle := o) hstore, hclamp0, hcurA]
  have hbody : PancakeSem o (fillBody hdr) (decClock s) = (none, s2) := by
    rw [fillBody, sem_seq_none (oracle := o) h_inner, hclamp1, hiA]
  -- (5) the advanced invariant at index k+1
  have dne : ("cur" = "i") = False := by decide
  have hs2i : s2.locals "i" = some (BitVec.ofNat 64 (k + 1)) := by
    rw [hs2]; simp only [setLocal, if_true]
  have hs2cur : s2.locals "cur" = some (BitVec.ofNat 64 (8 * (k + 1))) := by
    rw [hs2, hs1]; simp only [setLocal, dne, if_false, if_true]
  have hs2n : s2.locals "n" = some (BitVec.ofNat 64 n) := by
    rw [hs2, hs1, hs0]
    simp only [setLocal, decClock, show ("n" = "i") = False from by decide,
               show ("n" = "cur") = False from by decide, if_false]
    exact hn
  have hs2mem : ∀ key, s2.memory key
      = (if key = BitVec.ofNat 64 (8 * k) then hdr else s.memory key) := by
    intro key; simp only [hs2, hs1, hs0, decClock]
  have hs2addr : s2.memaddrs = s.memaddrs := by simp only [hs2, hs1, hs0, decClock]
  have hs2clk : s2.clock = s.clock - 1 := by simp only [hs2, hs1, hs0, decClock]
  refine ⟨s2, hbody, ⟨k + 1, by omega, hs2i, hs2cur, hs2n, ?_, ?_⟩, hs2clk⟩
  · -- every slot < k+1 holds hdr
    intro j hjk1
    rw [hs2mem]
    by_cases hjeq : j = k
    · subst hjeq; rw [if_pos rfl]
    · have hjk : j < k := by omega
      rw [if_neg (slot_ne n j k (by omega) hkn h8n hjeq)]
      exact hmem j hjk
  · -- memaddrs preserved
    intro j hjn; rw [hs2addr]; exact haddr j hjn

/-- THE WRITE-LOOP, certified: from the entry invariant (`i=0`, `cur=0`, all `n`
slots mapped) with iteration budget `n ≤ clock`, the translator-emitted `While`
(`fillWhile = .while_ guard (emit (fillBodyStage hdr))`, see `emit_fillBody`) runs
to a state where EVERY slot `< n` holds the header word, and every slot stays
mapped. Obtained by instantiating the reusable `while_inv_cond_clk` at the fill
guard/body — the same rule the byte-READING scan loop uses, here on a byte-WRITING
body. -/
theorem fill_loop_slots (o : Oracle σ) (hdr : Word) (n : Nat) (h8n : 8 * n < 2 ^ 64)
    (hn63 : n < 2 ^ 63)
    (s : PancakeState σ)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hcur : s.locals "cur" = some (BitVec.ofNat 64 0))
    (hn : s.locals "n" = some (BitVec.ofNat 64 n))
    (hclock : n ≤ s.clock)
    (haddr : ∀ j, j < n → s.memaddrs (BitVec.ofNat 64 (8 * j)) = true) :
    ∃ s', PancakeSem o (fillWhile hdr) s = (none, s') ∧
      (∀ j, j < n → s'.memory (BitVec.ofNat 64 (8 * j)) = hdr) ∧
      (∀ j, j < n → s'.memaddrs (BitVec.ofNat 64 (8 * j)) = true) := by
  have hI0 : fillInv hdr n n s :=
    ⟨0, by omega, by simpa using hi, by simpa using hcur, hn,
      (by intro j hj; omega), haddr⟩
  obtain ⟨s', hs'eq, hs'I, _⟩ :=
    while_inv_cond_clk o (.cmp .less (.var "i") (.var "n")) (fillBody hdr)
      (fillInv hdr n)
      (fill_guard hdr n hn63)
      (fill_step o hdr n h8n)
      n s hI0 hclock
  obtain ⟨k, hk0, _, _, _, hmem, hmaddr⟩ := hs'I
  refine ⟨s', hs'eq, ?_, ?_⟩
  · intro j hj; exact hmem j (by omega)
  · intro j hj; exact hmaddr j hj

/-- A single filled slot, read back through the byte model: given the slot holds
`hdr` and is aligned, each of its 8 bytes reads back as the getByte-decomposition
of `hdr` (the alignment side-condition `haln`, dischargeable concretely). -/
theorem slot_byte (m : Word → Word) (dm : Word → Bool) (be : Bool) (hdr : Word) (k : Nat)
    (hmemk : m (BitVec.ofNat 64 (8 * k)) = hdr)
    (hin : dm (BitVec.ofNat 64 (8 * k)) = true)
    (j : Nat) (hj : j < 8)
    (haln : byteAlign (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) = BitVec.ofNat 64 (8 * k)) :
    memLoadByte m dm be (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
      = some (getByte (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) hdr be) := by
  unfold memLoadByte
  rw [haln, if_pos hin, hmemk]

/-- THE WRITE-LOOP BYTE-EFFECT (symbolic): after the emitted `While`, every byte of
the whole `8·n`-byte output region reads back through the panSem byte model as the
getByte-decomposition of the header word. `haln` is the per-slot alignment
side-condition. Combines `fill_loop_slots` (the loop certificate) with `slot_byte`
(the byte read-back). -/
theorem fill_byte_effect (o : Oracle σ) (hdr : Word) (be : Bool) (n : Nat)
    (h8n : 8 * n < 2 ^ 64) (hn63 : n < 2 ^ 63)
    (s : PancakeState σ)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hcur : s.locals "cur" = some (BitVec.ofNat 64 0))
    (hn : s.locals "n" = some (BitVec.ofNat 64 n))
    (hclock : n ≤ s.clock)
    (haddr : ∀ j, j < n → s.memaddrs (BitVec.ofNat 64 (8 * j)) = true)
    (haln : ∀ k j, k < n → j < 8 →
      byteAlign (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) = BitVec.ofNat 64 (8 * k)) :
    ∃ s', PancakeSem o (fillWhile hdr) s = (none, s') ∧
      ∀ k, k < n → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs be
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (getByte (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) hdr be) := by
  obtain ⟨s', hrun, hslots, hmaddr⟩ :=
    fill_loop_slots o hdr n h8n hn63 s hi hcur hn hclock haddr
  refine ⟨s', hrun, ?_⟩
  intro k hk j hj
  exact slot_byte s'.memory s'.memaddrs be hdr k (hslots k hk) (hmaddr k hk) j hj (haln k j hk hj)

/-- CONCRETE write-loop byte-effect: append the literal header word `demoHdr`
(= `"X: 1" CRLF`) to `n = 3` output slots, then EVERY byte of the whole 24-byte
output region reads back as the header ASCII bytes `[88,58,32,49,13,10,0,0]`
(byte `j` of slot `k`). The alignment side-conditions and the ASCII byte values are
decided in-kernel. A byte-WRITING loop compiled by the translator, proven
byte-for-byte. -/
theorem fillDemo_ascii (o : Oracle σ) (s : PancakeState σ)
    (hi : s.locals "i" = some (BitVec.ofNat 64 0))
    (hcur : s.locals "cur" = some (BitVec.ofNat 64 0))
    (hn : s.locals "n" = some (BitVec.ofNat 64 3))
    (hclock : 3 ≤ s.clock)
    (haddr : ∀ j, j < 3 → s.memaddrs (BitVec.ofNat 64 (8 * j)) = true) :
    ∃ s', PancakeSem o (fillWhile demoHdr) s = (none, s') ∧
      ∀ k, k < 3 → ∀ j, j < 6 →
        memLoadByte s'.memory s'.memaddrs true
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (([88, 58, 32, 49, 13, 10] : List (BitVec 8))[j]!) := by
  obtain ⟨s', hrun, hbytes⟩ :=
    fill_byte_effect o demoHdr true 3 (by decide) (by decide) s hi hcur hn hclock haddr
      (by intro k j hk hj
          rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl <;>
            (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7
                       from by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
              decide))
  refine ⟨s', hrun, ?_⟩
  intro k hk j hj
  rw [hbytes k hk j (by omega)]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 from by omega) with rfl | rfl | rfl <;>
    (rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 from by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide)

end Pancake.RealStageDemo
