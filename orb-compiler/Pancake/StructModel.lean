/-
  Pancake/StructModel.lean — the DATA-MODEL lowering of the pivot: lower the
  serve's first-order data (a `Response` record + a `List (Bytes × Bytes)` of
  headers) into FLAT Pancake byte/word memory, with proven field-access and a
  proven BOUNDED iteration over the list. Additive over
  Pancake/EmitCorrectClock.lean (nothing there is modified or re-proven).

  WHY. The certified translator so far lowers WORD-valued stages (the region
  digest). The real serve returns `Response` structs and `List (Bytes × Bytes)`
  header lists. Those lower to flat memory the STANDARD way:

    * a `Bytes` value (`List (BitVec 8)`) lowers to a contiguous byte region —
      `memBytes s b base` says the `b.length` bytes of `b` sit at `base + i` in
      the model memory. This is the BYTES-LOWERING seam (`memBytes`). Byte
      payloads are threaded as an EXPLICIT relation, exactly as
      `EmitCorrectRegion.ViewBytes` (the load_vec FFI postcondition A0) is —
      never a `sorry`.
    * a WORD field (a status, a length, a pointer, a count) lowers to one word
      of word-addressed memory — `wordAt s a v`. A word field ROUND-TRIPS
      constructively (store then load, `put_eq`/`put_ne`), with NO byte-aliasing
      theory, so the struct/list SKELETON (status, count, per-record base/len
      words) is constructive; only the leaf byte payloads use the `memBytes` seam.
    * a `Response` lowers to a fixed word header (status | headers-ptr |
      body-ptr | body-len) followed by the two lowered regions (`RespLayout`).
    * a `List (Bytes × Bytes)` lowers to a LENGTH-PREFIXED array of 4-word
      records `(keyBase, keyLen, valBase, valLen)` (`ListLayout`), walked by a
      BOUNDED `While` over the list length — proven through the SAME loop
      machinery as the region scan (`while_inv_cond_clk`, `RefinesClk`).

  WHAT IS PROVEN (all `#print axioms`-clean, 0 `sorry`, non-vacuous):
   * word round-trip:  `put_eq` / `put_ne` / `eval_loadWord_of_wordAt` — a
     stored word is read back by the model `Load One`.
   * struct field-access: `resp_load_status`, `resp_load_bodyLen`,
     `resp_load_bodyByte` — the model `eval` of the `.pnk` field load retrieves
     the SPEC field value (the byte case via the `memBytes` seam).
   * list field-access: `list_load_count`, `list_load_keyLen`,
     `list_load_keyBase` — the count word and per-record words are retrieved.
   * BOUNDED LIST ITERATION: `sumLen_loop` — a `While (j < count)` that walks the
     record array by a pointer, summing every record's key-length word, runs to
     `sum = ∑_{k<count} keyLen k` (the SPEC fold), proven by instantiating
     `while_inv_cond_clk`; `refinesClk_sumLoop` packages it as ONE `RefinesClk`
     stage, so the list walk composes in the uniform clock-accounting grammar.
   * SATISFIABILITY (non-vacuity witnesses): `resp_layout_witness` /
     `list_iter_witness` exhibit a CONCRETE `putWord`-built memory for which the
     layout holds and the loop computes the expected sum — the layouts are
     inhabited, so the field-access / iteration theorems are not vacuous.

  This is Stack L (the Lean model of Pancake). NO byte/machine claims here.
-/
import Pancake.EmitCorrectClock

namespace Pancake.StructModel

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectClock

variable {σ : Type}

/-- A first-order byte string (the serve's `Bytes`). -/
abbrev Bytes := List (BitVec 8)

/-- Fixed word offsets of a 4-word record / struct header. -/
def w8  : Word := BitVec.ofNat 64 8
def w16 : Word := BitVec.ofNat 64 16
def w24 : Word := BitVec.ofNat 64 24
def w32 : Word := BitVec.ofNat 64 32

/-! ## 0. Byte- and word-level memory relations (the lowering primitives) -/

/-- THE BYTES-LOWERING SEAM. `memBytes s b base`: the `b.length` bytes of the
Lean value `b` sit contiguously in the model byte memory starting at `base`,
`b[i]` at `base + i`. Same shape as `EmitCorrectRegion.ViewBytes`; threaded as an
explicit relation (A0-style) wherever a leaf byte payload appears. -/
def memBytes (s : PancakeState σ) (b : Bytes) (base : Word) : Prop :=
  ∀ i, i < b.length →
    memLoadByte s.memory s.memaddrs s.be (base + BitVec.ofNat 64 i) = some (b[i]!)

/-- A single word of word-addressed memory: address `a` is mapped and holds `v`. -/
def wordAt (s : PancakeState σ) (a v : Word) : Prop :=
  s.memaddrs a = true ∧ s.memory a = v

/-- The `mem_store`-success update at one word address (`memStoreWord`'s hit
branch): overwrite `a` with `v`, keep the rest. -/
def putWord (m : Word → Word) (a v : Word) : Word → Word :=
  fun k => if k = a then v else m k

/-- Round-trip: the just-stored word is there. -/
theorem put_eq (m : Word → Word) (a v : Word) : putWord m a v a = v := by
  simp [putWord]

/-- Non-interference: a store at `a` leaves a distinct address `k` untouched. -/
theorem put_ne (m : Word → Word) {a v k : Word} (h : k ≠ a) :
    putWord m a v k = m k := by
  simp [putWord, h]

/-! ## 1. Model `eval` of a flat field load -/

/-- The model `eval` of `Load One ea` retrieves `v` when `ea` addresses a mapped
word holding `v` (`wordAt`). This is the field-access reduction the struct/list
lemmas run on. -/
theorem eval_loadWord_of_wordAt {s : PancakeState σ} {ea : PancakeExp} {a v : Word}
    (haddr : eval s ea = some a) (h : wordAt s a v) :
    eval s (.loadWord ea) = some v := by
  obtain ⟨hdm, hmem⟩ := h
  simp only [eval, haddr, hdm, if_true, hmem]

/-- `eval` of a base-plus-constant-offset address (`Op Add (Var name) (Const off)`). -/
theorem eval_addr_off {s : PancakeState σ} {name : String} {p off : Word}
    (h : s.locals name = some p) :
    eval s (.op .add (.var name) (.const off)) = some (p + off) := by
  simp only [eval, h]

/-- `eval` of a bare `Var name` field pointer. -/
theorem eval_var {s : PancakeState σ} {name : String} {p : Word}
    (h : s.locals name = some p) : eval s (.var name) = some p := h

/-- `eval` of an `Op Add` from its two sub-evaluations. -/
theorem eval_op_add {s : PancakeState σ} {l r : PancakeExp} {a b : Word}
    (hl : eval s l = some a) (hr : eval s r = some b) :
    eval s (.op .add l r) = some (a + b) := by
  simp only [eval, hl, hr]

/-- `eval` of `LoadByte ea` from its address evaluation and a `memLoadByte` fact
(the byte is `w2w`-widened to a word). -/
theorem eval_loadByte_of {s : PancakeState σ} {ea : PancakeExp} {a : Word} {b : BitVec 8}
    (haddr : eval s ea = some a)
    (hb : memLoadByte s.memory s.memaddrs s.be a = some b) :
    eval s (.loadByte ea) = some (b.setWidth 64) := by
  simp only [eval, haddr, hb]

/-! ## 2. The `Response` struct lowering -/

/-- The serve's response record: a status word, a header list, a body byte
string. -/
structure Response where
  status  : Nat
  headers : List (Bytes × Bytes)
  body    : Bytes

/-- The record layout of one header entry `(key, val)` at word address `r`:
`(keyBase, keyLen, valBase, valLen)` in four consecutive words, plus the key/val
bytes present at their bases (`memBytes` seam). -/
def RecordAt (s : PancakeState σ) (r kb : Word) (kBytes : Bytes) (vb : Word)
    (vBytes : Bytes) : Prop :=
  wordAt s r kb ∧ wordAt s (r + w8) (BitVec.ofNat 64 kBytes.length) ∧
  wordAt s (r + w16) vb ∧ wordAt s (r + w24) (BitVec.ofNat 64 vBytes.length) ∧
  memBytes s kBytes kb ∧ memBytes s vBytes vb

/-- THE LIST LOWERING. `List (Bytes × Bytes)` → a length-prefixed array of 4-word
records. `arr` holds the length; record `k` sits at `recPtr k`; `kb`/`vb` give
each entry's key/value byte bases. -/
def ListLayout (s : PancakeState σ) (l : List (Bytes × Bytes)) (arr : Word)
    (recPtr kb vb : Nat → Word) : Prop :=
  wordAt s arr (BitVec.ofNat 64 l.length) ∧
  ∀ k, (hk : k < l.length) →
    RecordAt s (recPtr k) (kb k) (l[k].1) (vb k) (l[k].2)

/-- THE STRUCT LOWERING. `Response` → a 4-word header (status | headers-array-ptr
| body-ptr | body-len) followed by the lowered headers array and body region. -/
def RespLayout (s : PancakeState σ) (resp : Response) (base harr bodyBase : Word)
    (recPtr kb vb : Nat → Word) : Prop :=
  wordAt s base (BitVec.ofNat 64 resp.status) ∧
  wordAt s (base + w8) harr ∧
  wordAt s (base + w16) bodyBase ∧
  wordAt s (base + w24) (BitVec.ofNat 64 resp.body.length) ∧
  ListLayout s resp.headers harr recPtr kb vb ∧
  memBytes s resp.body bodyBase

/-! ### Struct field-access -/

/-- Field-access: `Load One (Var "resp")` retrieves the status word. -/
theorem resp_load_status {s : PancakeState σ} {resp : Response}
    {base harr bodyBase : Word} {recPtr kb vb : Nat → Word}
    (hlay : RespLayout s resp base harr bodyBase recPtr kb vb)
    (hb : s.locals "resp" = some base) :
    eval s (.loadWord (.var "resp")) = some (BitVec.ofNat 64 resp.status) :=
  eval_loadWord_of_wordAt (eval_var hb) hlay.1

/-- Field-access: `Load One (Var "resp" + 24)` retrieves the body length. -/
theorem resp_load_bodyLen {s : PancakeState σ} {resp : Response}
    {base harr bodyBase : Word} {recPtr kb vb : Nat → Word}
    (hlay : RespLayout s resp base harr bodyBase recPtr kb vb)
    (hb : s.locals "resp" = some base) :
    eval s (.loadWord (.op .add (.var "resp") (.const w24)))
      = some (BitVec.ofNat 64 resp.body.length) :=
  eval_loadWord_of_wordAt (eval_addr_off hb) hlay.2.2.2.1

/-- Byte field-access: `LoadByte (Var "bp" + i)` retrieves body byte `i` (through
the `memBytes` seam), zero-extended to a word (`w2w`). -/
theorem resp_load_bodyByte {s : PancakeState σ} {resp : Response}
    {base harr bodyBase : Word} {recPtr kb vb : Nat → Word}
    (hlay : RespLayout s resp base harr bodyBase recPtr kb vb)
    (hbp : s.locals "bp" = some bodyBase) (i : Nat) (hi : i < resp.body.length) :
    eval s (.loadByte (.op .add (.var "bp") (.const (BitVec.ofNat 64 i))))
      = some ((resp.body[i]!).setWidth 64) := by
  exact eval_loadByte_of (eval_addr_off hbp) (hlay.2.2.2.2.2 i hi)

/-! ### List field-access -/

/-- Field-access: `Load One (Var "arr")` retrieves the header COUNT. -/
theorem list_load_count {s : PancakeState σ} {l : List (Bytes × Bytes)}
    {arr : Word} {recPtr kb vb : Nat → Word}
    (hlay : ListLayout s l arr recPtr kb vb) (ha : s.locals "arr" = some arr) :
    eval s (.loadWord (.var "arr")) = some (BitVec.ofNat 64 l.length) :=
  eval_loadWord_of_wordAt (eval_var ha) hlay.1

/-- Field-access: `Load One (Var "p" + 8)` retrieves record `k`'s key-length. -/
theorem list_load_keyLen {s : PancakeState σ} {l : List (Bytes × Bytes)}
    {arr : Word} {recPtr kb vb : Nat → Word}
    (hlay : ListLayout s l arr recPtr kb vb) {k : Nat} (hk : k < l.length)
    (hp : s.locals "p" = some (recPtr k)) :
    eval s (.loadWord (.op .add (.var "p") (.const w8)))
      = some (BitVec.ofNat 64 (l[k].1).length) :=
  eval_loadWord_of_wordAt (eval_addr_off hp) (hlay.2 k hk).2.1

/-- Field-access: `Load One (Var "p")` retrieves record `k`'s key BASE pointer. -/
theorem list_load_keyBase {s : PancakeState σ} {l : List (Bytes × Bytes)}
    {arr : Word} {recPtr kb vb : Nat → Word}
    (hlay : ListLayout s l arr recPtr kb vb) {k : Nat} (hk : k < l.length)
    (hp : s.locals "p" = some (recPtr k)) :
    eval s (.loadWord (.var "p")) = some (kb k) :=
  eval_loadWord_of_wordAt (eval_var hp) (hlay.2 k hk).1

/-! ## 3. The BOUNDED list iteration — sum every record's key-length word

The list walk the serve needs (total serialized length, per-record dispatch, …)
is a `While (j < count)` over the record array, walking a pointer `p := p + 32`
per step. We certify the canonical instance — accumulate the sum of every
record's key-length word — through the SAME rule the region scan uses
(`while_inv_cond_clk`), so a list iteration is a `RefinesClk` stage. -/

/-- The SPEC fold: `sumLen f n = f 0 + f 1 + … + f (n-1)`. -/
def sumLen (f : Nat → Nat) : Nat → Nat
  | 0     => 0
  | n + 1 => sumLen f n + f n

theorem sumLen_le (f : Nat → Nat) : ∀ {a b : Nat}, a ≤ b → sumLen f a ≤ sumLen f b := by
  intro a b h
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => exact Nat.le_trans ih (Nat.le_add_right _ _)

/-- The list-walk loop body: `sum += mem[p+8]; p += 32; j += 1`. -/
def sumBody : PancakeProg :=
  .seq (.assign "sum" (.op .add (.var "sum") (.loadWord (.op .add (.var "p") (.const w8)))))
    (.seq (.assign "p" (.op .add (.var "p") (.const w32)))
          (.assign "j" (.op .add (.var "j") (.const (BitVec.ofNat 64 1)))))

/-- The list-walk `While (j < count)`. -/
def sumWhile : PancakeProg :=
  .while_ (.cmp .less (.var "j") (.var "count")) sumBody

/-- The list-iteration invariant with `n` records still to walk: `j = count - n`
records processed, `sum` holds the fold over them, `p` points at record `j`, and
every record's key-length word is in memory (read-only across the loop). -/
def sumInv (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (n : Nat) (s : PancakeState σ) : Prop :=
  ∃ j, j + n = count ∧
    s.locals "j"     = some (BitVec.ofNat 64 j) ∧
    s.locals "count" = some (BitVec.ofNat 64 count) ∧
    s.locals "sum"   = some (BitVec.ofNat 64 (sumLen klen j)) ∧
    s.locals "p"     = some (recPtr j) ∧
    (∀ k, k < count → wordAt s (recPtr k + w8) (BitVec.ofNat 64 (klen k)))

/-- The guard `j < count` evaluates to `0` exactly when the walk is done (`n = 0`,
`j = count`), else `1`. -/
theorem sum_guard (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (hcount63 : count < 2 ^ 63) (n : Nat) (s : PancakeState σ)
    (hI : sumInv count recPtr klen n s) :
    eval s (.cmp .less (.var "j") (.var "count")) = some (if n = 0 then (0 : Word) else 1) := by
  obtain ⟨j, hjn, hj, hcount, _, _, _⟩ := hI
  have hj63 : j < 2 ^ 63 := by omega
  have hev : eval s (.cmp .less (.var "j") (.var "count"))
      = some (if signedLt (BitVec.ofNat 64 j) (BitVec.ofNat 64 count) then 1 else 0) := by
    simp only [eval, hj, hcount]
  rw [hev, signedLt_ofNat j count hj63 hcount63]
  by_cases hn : n = 0
  · have : j = count := by omega
    subst this; simp [hn]
  · have : j < count := by omega
    simp [hn, this]

/-- ONE walk step advances the invariant: from `sumInv (n+1) s`, running `sumBody`
on `decClock s` lands in a normal state satisfying `sumInv n`, one clock tick
consumed. All three assigns preserve memory, so the key-length facts transfer. -/
theorem sum_step (o : Oracle σ) (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (hcount63 : count < 2 ^ 63) (htot : sumLen klen count < 2 ^ 64)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32)
    (n : Nat) (s : PancakeState σ) (hI : sumInv count recPtr klen (n + 1) s) :
    ∃ s2, PancakeSem o sumBody (decClock s) = (none, s2) ∧
      sumInv count recPtr klen n s2 ∧ s2.clock = s.clock - 1 := by
  obtain ⟨j, hjn, hj, hcount, hsum, hp, hKL⟩ := hI
  have hjc : j < count := by omega
  have hdl : (decClock s).locals = s.locals := rfl
  -- bound: sumLen klen j + klen j = sumLen klen (j+1) ≤ sumLen klen count < 2^64
  have hbnd : sumLen klen j + klen j < 2 ^ 64 := by
    have hle : sumLen klen (j + 1) ≤ sumLen klen count := sumLen_le klen (by omega)
    simp only [sumLen] at hle; omega
  -- (A) the sum += mem[p+8] update
  have hloadA : eval (decClock s) (.loadWord (.op .add (.var "p") (.const w8)))
      = some (BitVec.ofNat 64 (klen j)) :=
    eval_loadWord_of_wordAt (eval_addr_off (by rw [hdl]; exact hp)) (hKL j hjc)
  have hl : eval (decClock s) (.var "sum") = some (BitVec.ofNat 64 (sumLen klen j)) := hsum
  have haccE : eval (decClock s)
      (.op .add (.var "sum") (.loadWord (.op .add (.var "p") (.const w8))))
      = some (BitVec.ofNat 64 (sumLen klen (j + 1))) := by
    have hsucc : sumLen klen (j + 1) = sumLen klen j + klen j := rfl
    rw [hsucc, eval_op_add hl hloadA, ofNat_add_small _ _ hbnd]
  obtain ⟨sA, hsA⟩ : ∃ sA : PancakeState σ, sA = { decClock s with
      locals := setLocal (decClock s).locals "sum" (BitVec.ofNat 64 (sumLen klen (j + 1))) } := ⟨_, rfl⟩
  have hA := sem_assign (oracle := o) (x := "sum") haccE
  rw [← hsA] at hA
  -- (B) the p += 32 update
  have hpE : eval sA (.op .add (.var "p") (.const w32)) = some (recPtr (j + 1)) := by
    have hsAp : sA.locals "p" = some (recPtr j) := by
      rw [hsA]; simp only [setLocal, decClock]; rw [if_neg (by decide)]; exact hp
    rw [eval_addr_off hsAp, hstep]
  obtain ⟨sB, hsB⟩ : ∃ sB : PancakeState σ,
      sB = { sA with locals := setLocal sA.locals "p" (recPtr (j + 1)) } := ⟨_, rfl⟩
  have hB := sem_assign (oracle := o) (x := "p") hpE
  rw [← hsB] at hB
  -- (C) the j += 1 update
  have hjE : eval sB (.op .add (.var "j") (.const (BitVec.ofNat 64 1)))
      = some (BitVec.ofNat 64 (j + 1)) := by
    have hsBj : sB.locals "j" = some (BitVec.ofNat 64 j) := by
      rw [hsB, hsA]; simp only [setLocal, decClock]
      rw [if_neg (by decide), if_neg (by decide)]; exact hj
    rw [eval_addr_off hsBj, ofNat_add_small _ _ (by omega)]
  obtain ⟨sC, hsC⟩ : ∃ sC : PancakeState σ,
      sC = { sB with locals := setLocal sB.locals "j" (BitVec.ofNat 64 (j + 1)) } := ⟨_, rfl⟩
  have hC := sem_assign (oracle := o) (x := "j") hjE
  rw [← hsC] at hC
  -- (whole body = Seq A (Seq B C); clamps are no-ops, assigns keep the clock)
  have hclkA : sA.clock = (decClock s).clock := by rw [hsA]
  have hclampA : ({ sA with clock := min (decClock s).clock sA.clock } : PancakeState σ) = sA := by
    rw [hclkA, Nat.min_self, ← hclkA]
  have hclkB : sB.clock = sA.clock := by rw [hsB]
  have hclampB : ({ sB with clock := min sA.clock sB.clock } : PancakeState σ) = sB := by
    rw [hclkB, Nat.min_self, ← hclkB]
  have hbody : PancakeSem o sumBody (decClock s) = (none, sC) := by
    rw [sumBody, sem_seq_none (oracle := o) hA, hclampA,
        sem_seq_none (oracle := o) hB, hclampB, hC]
  -- transport the invariant to sC (index j+1)
  have hCsum : sC.locals "sum" = some (BitVec.ofNat 64 (sumLen klen (j + 1))) := by
    rw [hsC, hsB, hsA]
    simp only [setLocal, decClock, show ("sum" = "j") = False from by decide,
               show ("sum" = "p") = False from by decide, if_false, if_true]
  have hCp : sC.locals "p" = some (recPtr (j + 1)) := by
    rw [hsC, hsB]
    simp only [setLocal, show ("p" = "j") = False from by decide, if_false, if_true]
  have hCj : sC.locals "j" = some (BitVec.ofNat 64 (j + 1)) := by
    rw [hsC]; simp only [setLocal, if_true]
  have hCcount : sC.locals "count" = some (BitVec.ofNat 64 count) := by
    rw [hsC, hsB, hsA]
    simp only [setLocal, decClock, show ("count" = "j") = False from by decide,
               show ("count" = "p") = False from by decide,
               show ("count" = "sum") = False from by decide, if_false]
    exact hcount
  have hCKL : ∀ k, k < count → wordAt sC (recPtr k + w8) (BitVec.ofNat 64 (klen k)) := by
    intro k hk
    have hkfact := hKL k hk
    rw [hsC, hsB, hsA]; exact hkfact
  have hCclk : sC.clock = s.clock - 1 := by simp only [hsC, hsB, hsA, decClock]
  exact ⟨sC, hbody, ⟨j + 1, by omega, hCj, hCcount, hCsum, hCp, hCKL⟩, hCclk⟩

/-- THE BOUNDED LIST ITERATION. From `sumInv rem s` with budget `rem ≤ s.clock`,
the emitted `sumWhile` runs to a state satisfying `sumInv 0` — i.e. `sum` holds
the FULL fold `sumLen klen count` and `j = count`, clock monotonically consumed.
Obtained by instantiating `while_inv_cond_clk` (the region-scan rule) at the
list-walk guard/body — a genuine list iteration through the SAME machinery. -/
theorem sumLen_loop (o : Oracle σ) (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (hcount63 : count < 2 ^ 63) (htot : sumLen klen count < 2 ^ 64)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32) :
    ∀ (rem : Nat) (s : PancakeState σ), sumInv count recPtr klen rem s → rem ≤ s.clock →
      ∃ s', PancakeSem o sumWhile s = (none, s') ∧ sumInv count recPtr klen 0 s'
        ∧ s'.clock ≤ s.clock :=
  while_inv_cond_clk o (.cmp .less (.var "j") (.var "count")) sumBody
    (sumInv count recPtr klen)
    (sum_guard count recPtr klen hcount63)
    (sum_step o count recPtr klen hcount63 htot hstep)

/-- The list walk as ONE `RefinesClk` stage: precondition = the entry invariant
(`j = 0`, `sum = 0`, pointer at record 0, records loaded) + the iteration budget
`count ≤ s.clock`; postcondition = the full fold landed in `sum` (`j = count`).
So a list iteration composes in the uniform clock-accounting grammar. -/
theorem refinesClk_sumLoop (o : Oracle σ) (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (hcount63 : count < 2 ^ 63) (htot : sumLen klen count < 2 ^ 64)
    (hstep : ∀ k, recPtr (k + 1) = recPtr k + w32) :
    RefinesClk o sumWhile
      (fun s => sumInv count recPtr klen count s ∧ count ≤ s.clock)
      (fun _ s' => s'.locals "sum" = some (BitVec.ofNat 64 (sumLen klen count))
        ∧ s'.locals "j" = some (BitVec.ofNat 64 count)) := by
  intro s hP
  obtain ⟨hI, hclk⟩ := hP
  obtain ⟨s', hs'eq, hs'I, hs'clk⟩ :=
    sumLen_loop o count recPtr klen hcount63 htot hstep count s hI hclk
  obtain ⟨j, hj0, hs'j, _, hs'sum, _, _⟩ := hs'I
  have hjc : j = count := by omega
  subst hjc
  exact ⟨s', hs'eq, ⟨hs'sum, hs'j⟩, hs'clk⟩

/-- The entry invariant is established from `j = 0, sum = 0, p = recPtr 0`, count
bound, and the loaded record key-length words — the canonical loop start. -/
theorem sumInv_entry (count : Nat) (recPtr : Nat → Word) (klen : Nat → Nat)
    (s : PancakeState σ)
    (hj : s.locals "j" = some (BitVec.ofNat 64 0))
    (hcount : s.locals "count" = some (BitVec.ofNat 64 count))
    (hsum : s.locals "sum" = some (BitVec.ofNat 64 0))
    (hp : s.locals "p" = some (recPtr 0))
    (hKL : ∀ k, k < count → wordAt s (recPtr k + w8) (BitVec.ofNat 64 (klen k))) :
    sumInv count recPtr klen count s :=
  ⟨0, by omega, hj, hcount, by simpa [sumLen] using hsum, hp, hKL⟩

/-! ## 4. Satisfiability — the layouts are inhabited (non-vacuity witnesses)

The field-access / iteration theorems are implications from a layout; a witness
that a CONCRETELY-BUILT memory satisfies a layout shows they are not vacuously
true. `putWord` builds the word skeleton with no byte-aliasing theory; empty
byte payloads (`[]`) discharge `memBytes` vacuously, isolating the word content.

`ptrChain` is the pointer-walked record base (`recPtr (k+1) = recPtr k + 32` by
definition, so `hstep` is `rfl`). -/

def ptrChain (r0 : Word) : Nat → Word
  | 0     => r0
  | k + 1 => ptrChain r0 k + w32

def klen2 (k0 k1 : Nat) : Nat → Nat := fun k => if k = 0 then k0 else k1

/-- The `Response {status, [], []}` word skeleton: status | headers-ptr |
body-ptr | body-len(0) at `base+{0,8,16,24}`, count(0) at `harr`. -/
def respMem (base harr bodyBase : Word) (status : Nat) : Word → Word :=
  putWord (putWord (putWord (putWord (putWord (fun _ => (0 : Word))
    base (BitVec.ofNat 64 status)) (base + w8) harr) (base + w16) bodyBase)
    (base + w24) (BitVec.ofNat 64 0)) harr (BitVec.ofNat 64 0)

/-- A two-record key-length skeleton: `k0` at `r0+8`, `k1` at `r0+32+8`. -/
def listMem2 (r0 : Word) (k0 k1 : Nat) : Word → Word :=
  putWord (putWord (fun _ => (0 : Word)) (r0 + w8) (BitVec.ofNat 64 k0))
    (r0 + w32 + w8) (BitVec.ofNat 64 k1)

/-- WITNESS 1 (struct). A `Response {status, [], []}` lowered to four distinct
word slots is satisfied by the `respMem`-built memory: the layout HOLDS, so
`resp_load_status`/`resp_load_bodyLen` are non-vacuous. Distinctness of the four
slot addresses + the header/count word is the real precondition. -/
theorem resp_layout_witness (status : Nat) (base harr bodyBase : Word)
    (recPtr kb vb : Nat → Word)
    (hab : (base + w8) ≠ base) (hac : (base + w16) ≠ base) (had : (base + w24) ≠ base)
    (hcb : (base + w16) ≠ (base + w8)) (hcd : (base + w24) ≠ (base + w8))
    (hdd : (base + w24) ≠ (base + w16))
    (hh1 : harr ≠ base) (hh2 : harr ≠ (base + w8)) (hh3 : harr ≠ (base + w16))
    (hh4 : harr ≠ (base + w24)) :
    ∃ s : PancakeState Unit,
      RespLayout s { status := status, headers := [], body := [] }
        base harr bodyBase recPtr kb vb := by
  refine ⟨{ locals := fun _ => none, memory := respMem base harr bodyBase status,
            memaddrs := fun _ => true, be := false, clock := 0, ffi := (), baseAddr := 0 },
          ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨⟨rfl, ?_⟩, ?_⟩, ?_⟩
  · show respMem base harr bodyBase status base = _
    simp only [respMem]
    rw [put_ne _ (Ne.symm hh1), put_ne _ (Ne.symm had), put_ne _ (Ne.symm hac),
        put_ne _ (Ne.symm hab), put_eq]
  · show respMem base harr bodyBase status (base + w8) = _
    simp only [respMem]
    rw [put_ne _ (Ne.symm hh2), put_ne _ (Ne.symm hcd), put_ne _ (Ne.symm hcb), put_eq]
  · show respMem base harr bodyBase status (base + w16) = _
    simp only [respMem]
    rw [put_ne _ (Ne.symm hh3), put_ne _ (Ne.symm hdd), put_eq]
  · show respMem base harr bodyBase status (base + w24) = _
    simp only [respMem]
    rw [put_ne _ (Ne.symm hh4), put_eq]; rfl
  · show respMem base harr bodyBase status harr = _
    simp only [respMem]; rw [put_eq]; rfl
  · intro k hk; exact absurd hk (Nat.not_lt_zero k)
  · intro i hi; exact absurd hi (Nat.not_lt_zero i)

/-- WITNESS 2 (iteration). A two-record array with key-length words `k0`, `k1`
built by `putWord` runs `sumWhile` to `sum = k0 + k1`: the loop actually WALKS
memory (`p := p + 32` twice) and computes the SPEC fold — the iteration theorem
is non-vacuous. Distinctness of the two key-length slots is the real
precondition. -/
theorem list_iter_witness (k0 k1 : Nat) (r0 : Word)
    (hk : k0 + k1 < 2 ^ 64)
    (hslot : (r0 + w32 + w8) ≠ (r0 + w8)) :
    ∃ s' : PancakeState Unit,
      PancakeSem { call := fun _ _ _ _ => FFIResult.final ⟨""⟩ } sumWhile
        { locals := fun n =>
            if n = "j" then some (BitVec.ofNat 64 0)
            else if n = "count" then some (BitVec.ofNat 64 2)
            else if n = "sum" then some (BitVec.ofNat 64 0)
            else if n = "p" then some r0 else none,
          memory := listMem2 r0 k0 k1, memaddrs := fun _ => true, be := false,
          clock := 2, ffi := (), baseAddr := 0 } = (none, s')
      ∧ s'.locals "sum" = some (BitVec.ofNat 64 (k0 + k1)) := by
  let s : PancakeState Unit :=
    { locals := fun n =>
        if n = "j" then some (BitVec.ofNat 64 0)
        else if n = "count" then some (BitVec.ofNat 64 2)
        else if n = "sum" then some (BitVec.ofNat 64 0)
        else if n = "p" then some r0 else none,
      memory := listMem2 r0 k0 k1, memaddrs := fun _ => true, be := false,
      clock := 2, ffi := (), baseAddr := 0 }
  have hsum2 : sumLen (klen2 k0 k1) 2 = k0 + k1 := by simp [sumLen, klen2]
  have hstep : ∀ k, ptrChain r0 (k + 1) = ptrChain r0 k + w32 := fun _ => rfl
  have hKL : ∀ k, k < 2 → wordAt s (ptrChain r0 k + w8) (BitVec.ofNat 64 (klen2 k0 k1 k)) := by
    intro k hk2
    have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl
    · refine ⟨rfl, ?_⟩
      show listMem2 r0 k0 k1 (ptrChain r0 0 + w8) = _
      rw [show ptrChain r0 0 = r0 from rfl]
      simp only [listMem2]
      rw [put_ne _ (Ne.symm hslot), put_eq, klen2]; simp
    · refine ⟨rfl, ?_⟩
      show listMem2 r0 k0 k1 (ptrChain r0 1 + w8) = _
      rw [show ptrChain r0 1 = r0 + w32 from rfl]
      simp only [listMem2]
      rw [put_eq, klen2]; simp
  have hI : sumInv (σ := Unit) 2 (ptrChain r0) (klen2 k0 k1) 2 s :=
    sumInv_entry 2 (ptrChain r0) (klen2 k0 k1) s rfl rfl rfl rfl hKL
  have htot : sumLen (klen2 k0 k1) 2 < 2 ^ 64 := by rw [hsum2]; exact hk
  obtain ⟨s', hs'eq, hs'I, _⟩ :=
    sumLen_loop { call := fun _ _ _ _ => FFIResult.final ⟨""⟩ } 2 (ptrChain r0) (klen2 k0 k1)
      (by decide) htot hstep 2 s hI (Nat.le_refl 2)
  obtain ⟨j, hj0, _, _, hs'sum, _, _⟩ := hs'I
  have hj2 : j = 2 := by omega
  subst hj2
  rw [hsum2] at hs'sum
  exact ⟨s', hs'eq, hs'sum⟩

end Pancake.StructModel
