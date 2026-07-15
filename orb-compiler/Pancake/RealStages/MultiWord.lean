/-
  Pancake/RealStages/MultiWord.lean — the MULTI-WORD bytes-lowering: a real serve
  header line is longer than one machine word, so its byte-effect is a SEQUENCE of
  packed-word stores, not the single store the pivot witness compiled. This file
  generalises the pivot (one word, one `Store`) to a header line of ARBITRARY
  length: chunk the line into 8-byte big-endian words, emit a straight-line
  `Seq` of `Store`s through the translator, and prove — byte-for-byte through the
  panSem byte substrate — that the whole output region reads back as the intended
  bytes.

  This is the shared engine the three real-stage witnesses instantiate; each of
  those files supplies its own concrete header line (the exact `name ": " value
  CRLF` the serializer appends) and discharges the concrete ASCII in-kernel.

  * `storeWordsFrom` — the translator `Stage` for a word list: `Seq` of one
    `Store <const 8·slot> <const wordₖ>` per word (a `prim` leaf each), so the
    generic `emit` compiles it with no bespoke `.pnk`.
  * `store_words_sem` — the emitted `Seq` runs to a state whose slot `k` holds
    `wordₖ` (every slot distinct, earlier stores framed through later ones), the
    address set is untouched, and untouched keys are preserved.
  * `store_words_byte_effect` — the whole `8·|ws|`-byte output region, read back
    through `memLoadByte`/`byteAlign`/`getByte`, is the getByte-decomposition of
    the stored words: a byte-ADDRESSED statement over the endianness substrate.

  ASSURANCE: `#print axioms` ⊆ {propext, Quot.sound, Classical.choice}; 0 `sorry`,
  no `native_decide`/`ofReduceBool`. This is Stack L (the Lean model). No
  machine-code claim here.
-/
import Pancake.RealStageDemo

namespace Pancake.RealStages.MultiWord

open Pancake Pancake.EmitCorrect Pancake.EmitCorrectCompose Pancake.RealStageDemo

variable {σ : Type}

/-! ## 1. The multi-word store stage -/

/-- The identity leaf (the empty word list emits `Skip`). -/
def skipPrim : Prim σ := { prog := .skip, den := fun s => s }

/-- One slot store: write `w` at the flat byte address `8·k` (word-aligned slot
`k`). A `Prim` leaf of the translator grammar. -/
def storeAt (k : Nat) (w : Word) : Prim σ :=
  { prog := .store (.const (BitVec.ofNat 64 (8 * k))) (.const w)
    den  := fun s => { s with memory := fun key =>
              if key = BitVec.ofNat 64 (8 * k) then w else s.memory key } }

/-- The straight-line multi-word stage: store `ws[0]` at slot `start`, `ws[1]` at
`start+1`, … as a right-nested `Seq` of `prim` leaves. -/
def storeWordsFrom (start : Nat) : List Word → Stage σ
  | []      => .prim skipPrim
  | w :: ws => .seq (.prim (storeAt start w)) (storeWordsFrom (start + 1) ws)

/-- Distinct slot addresses: `8·a ≠ 8·b` (as 64-bit words) for `a ≠ b` in range. -/
theorem slot_ne' (a b : Nat) (ha : 8 * a < 2 ^ 64) (hb : 8 * b < 2 ^ 64)
    (hab : a ≠ b) : BitVec.ofNat 64 (8 * a) ≠ BitVec.ofNat 64 (8 * b) := by
  intro hc
  apply hab
  have := congrArg BitVec.toNat hc
  simp only [BitVec.toNat_ofNat] at this
  omega

/-! ## 2. The emitted `Seq` runs to the intended memory -/

/-- **The multi-word store, executed.** The translator-emitted `Seq` for
`storeWordsFrom start ws` runs to a state `s'` with: every slot `start+k` holding
`ws[k]`, the address set unchanged, and every key outside the written slots
preserved. Proven by induction on `ws`, framing each earlier store through the
later ones via `slot_ne'`. -/
theorem store_words_sem (o : Oracle σ) (start : Nat) (ws : List Word) (s : PancakeState σ)
    (hb : 8 * (start + ws.length) < 2 ^ 64)
    (hmap : ∀ k, k < ws.length → s.memaddrs (BitVec.ofNat 64 (8 * (start + k))) = true) :
    ∃ s', PancakeSem o (emit (storeWordsFrom (σ := σ) start ws)) s = (none, s') ∧
      s'.memaddrs = s.memaddrs ∧
      (∀ k, k < ws.length → s'.memory (BitVec.ofNat 64 (8 * (start + k))) = ws[k]!) ∧
      (∀ key, (∀ k, k < ws.length → key ≠ BitVec.ofNat 64 (8 * (start + k))) →
          s'.memory key = s.memory key) := by
  induction ws generalizing start s with
  | nil =>
    refine ⟨s, ?_, rfl, ?_, ?_⟩
    · show PancakeSem o .skip s = (none, s); rw [PancakeSem]
    · intro k hk; simp only [List.length_nil] at hk; omega
    · intro key _; rfl
  | cons w ws ih =>
    -- (1) the first store lands `w` at slot `start`
    have hin0 : s.memaddrs (BitVec.ofNat 64 (8 * start)) = true := by
      have := hmap 0 (Nat.zero_lt_succ _)
      simpa using this
    have hstore := sem_store_ok o (.const (BitVec.ofNat 64 (8 * start))) (.const w) s
                     (BitVec.ofNat 64 (8 * start)) w rfl rfl hin0
    -- the post-store state, bound explicitly (no Mathlib `set`)
    obtain ⟨s0, hs0def⟩ : ∃ s0 : PancakeState σ, s0 =
        { s with memory := fun key =>
            if key = BitVec.ofNat 64 (8 * start) then w else s.memory key } := ⟨_, rfl⟩
    rw [← hs0def] at hstore
    -- (2) the recursive call on the tail from `start+1`
    have hb' : 8 * ((start + 1) + ws.length) < 2 ^ 64 := by
      simp only [List.length_cons] at hb; omega
    have hmap' : ∀ k, k < ws.length →
        s0.memaddrs (BitVec.ofNat 64 (8 * ((start + 1) + k))) = true := by
      intro k hk
      have heq : (start + 1) + k = start + (k + 1) := by omega
      rw [hs0def, heq]
      exact hmap (k + 1) (by simp only [List.length_cons]; omega)
    obtain ⟨s', hrun', hmaddr', hmem', hframe'⟩ := ih (start + 1) s0 hb' hmap'
    -- (3) assemble the Seq
    have hclk0 : s0.clock = s.clock := by rw [hs0def]
    have hclamp : ({ s0 with clock := min s.clock s0.clock } : PancakeState σ) = s0 := by
      rw [hclk0, Nat.min_self, ← hclk0]
    refine ⟨s', ?_, ?_, ?_, ?_⟩
    · -- emit (seq ...) = seq (store ...) (emit tail)
      show PancakeSem o (.seq (.store (.const (BitVec.ofNat 64 (8 * start))) (.const w))
                              (emit (storeWordsFrom (σ := σ) (start + 1) ws))) s = (none, s')
      rw [sem_seq_none (oracle := o) hstore, hclamp]
      exact hrun'
    · -- memaddrs: s' = s0 = s
      rw [hmaddr', hs0def]
    · -- memory at each slot
      intro k hk
      cases k with
      | zero =>
        -- slot start holds w; the tail never writes slot start
        have hne : ∀ t, t < ws.length →
            BitVec.ofNat 64 (8 * start) ≠ BitVec.ofNat 64 (8 * ((start + 1) + t)) := by
          intro t ht
          apply slot_ne' start ((start + 1) + t)
          · simp only [List.length_cons] at hb; omega
          · simp only [List.length_cons] at hb; omega
          · omega
        have hfr := hframe' (BitVec.ofNat 64 (8 * start)) hne
        rw [Nat.add_zero, hfr, hs0def]
        show (if BitVec.ofNat 64 (8 * start) = BitVec.ofNat 64 (8 * start) then w
                else s.memory (BitVec.ofNat 64 (8 * start))) = (w :: ws)[0]!
        rw [if_pos rfl]; rfl
      | succ k =>
        have hk' : k < ws.length := by simp only [List.length_cons] at hk; omega
        have heq : start + (k + 1) = (start + 1) + k := by omega
        rw [heq, hmem' k hk']
        simp
    · -- frame: keys outside all slots preserved
      intro key hkey
      have hkey' : ∀ t, t < ws.length →
          key ≠ BitVec.ofNat 64 (8 * ((start + 1) + t)) := by
        intro t ht
        have heq : (start + 1) + t = start + (t + 1) := by omega
        rw [heq]
        exact hkey (t + 1) (by simp only [List.length_cons]; omega)
      have hkey0 : key ≠ BitVec.ofNat 64 (8 * start) := by
        have := hkey 0 (Nat.zero_lt_succ _)
        simpa using this
      rw [hframe' key hkey', hs0def]
      simp only [if_neg hkey0]

/-! ## 3. The byte-effect over the whole region -/

/-- **The multi-word byte-effect.** After the translator-emitted `Seq` (base slot
`0`), every byte of the whole `8·|ws|`-byte output region reads back through the
panSem byte model as the getByte-decomposition of the word stored in its slot.
`haln` is the per-slot alignment side-condition (dischargeable concretely). -/
theorem store_words_byte_effect (o : Oracle σ) (ws : List Word) (be : Bool)
    (s : PancakeState σ)
    (hb : 8 * ws.length < 2 ^ 64)
    (hmap : ∀ k, k < ws.length → s.memaddrs (BitVec.ofNat 64 (8 * k)) = true)
    (haln : ∀ k j, k < ws.length → j < 8 →
      byteAlign (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) = BitVec.ofNat 64 (8 * k)) :
    ∃ s', PancakeSem o (emit (storeWordsFrom (σ := σ) 0 ws)) s = (none, s') ∧
      ∀ k, k < ws.length → ∀ j, j < 8 →
        memLoadByte s'.memory s'.memaddrs be
          (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j)
          = some (getByte (BitVec.ofNat 64 (8 * k) + BitVec.ofNat 64 j) ws[k]! be) := by
  obtain ⟨s', hrun, hmaddr, hmem, _⟩ :=
    store_words_sem o 0 ws s (by simpa using hb) (by simpa using hmap)
  refine ⟨s', hrun, ?_⟩
  intro k hk j hj
  have hmk : s'.memory (BitVec.ofNat 64 (8 * k)) = ws[k]! := by
    have := hmem k hk; simpa using this
  have hin : s'.memaddrs (BitVec.ofNat 64 (8 * k)) = true := by
    rw [hmaddr]; exact hmap k hk
  exact slot_byte s'.memory s'.memaddrs be ws[k]! k hmk hin j hj (haln k j hk hj)

end Pancake.RealStages.MultiWord
