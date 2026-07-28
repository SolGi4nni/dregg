/-
# `Dregg2.Circuit.Emit.PicklesTranscriptBinding` — P4's two remaining named residuals: settled and
priced.

## SUBSTRATE (House Law #1, said out loud at constraint #1)

**This is Lean-authored.** Nothing below is a Rust AIR, a Rust gadget, or a Rust `air_accepts`. This
file proves MATHEMATICAL FACTS about (1) an algorithm Pickles runs (`to_field_checked`'s 128-bit
prechallenge decoding) and (2) a random-oracle reduction for its Poseidon-over-Pasta sponge. The
Rust/OCaml files cited are READ as the specification being characterized, never as the authoring
site — there is no constraint system here at all, only theorems about functions.

## WHAT THIS FILE CONTINUES

`PicklesFinalize.lean` §Z names three things still needed before "the recursion is sound":
(1) the sponge-digest equality pins a HISTORY, not a VALUE (a ROM assumption), (2) `endo` injectivity
on 128-bit prechallenges (a hypothesis, not a theorem), (3) the IPA opening floor (P10, inherited,
untouched here). This file:

  * **SETTLES (2).** `endoMap` — the REAL composite `to_field_checked_prime` (`transaction.rs:165-
    235`) then `a·endo+b` (`to_field_checked`, `:238-244`) — IS injective on 128-bit prechallenges, at
    the ACTUAL endo constant Pickles uses in the Step circuit's `finalize_other_proof`
    (`endo = endos::<Fq>().1`, `step.rs:551`, which IS `PastaCurve.lambdaVesta` — Vesta's GLV lambda,
    an Fp element, already pinned and proven a primitive cube root of unity). Proved, not assumed:
    §A. Both obstructions are real and both are closed:
      1. **Combinatorial** (§A.1): the bit-stream-to-`(a,b)` decoding is injective — no field
         arithmetic, a pure fact about a doubling-with-signed-digit recurrence.
      2. **Field-level** (§A.2): `(a,b) ↦ a·lambdaVesta+b` is injective on the range the 128-bit
         construction can reach. This is a GENUINE geometry-of-numbers fact, not asserted: the
         lattice `{(x,y) : x ≡ y·lambdaVesta (mod pN)}` has a shortest vector of norm `≈2^127`
         (COMPUTED — Gauss/Lagrange 2D lattice reduction on the real `pN`/`lambdaVesta`, cross-checked
         by the classical Eisenstein-integer identity `a²+ab+b² = pN` the vector satisfies EXACTLY),
         safely (by ~57 bits) above the `< 2^70` range 128 bits can produce. The minimality of that
         vector is proved here by an ELEMENTARY coprimality argument (§A.2), not by re-deriving
         general lattice-reduction theory in Lean.
  * **REDUCES (1)** to a named, PRICED, per-instance ROM residual — mirroring the tree's established
    pattern (`Sha256MerkleFold.pairSepOn` / `Verify.FloorPole`'s three-legs discipline, and
    `Crypto.Poseidon2RomInstantiation`'s `KeyedRomFaithful` shape) — over the REAL Kimchi
    Poseidon-over-Pasta-Fp reference (`PastaPoseidon.Ref.hash`), priced by the PROVED
    `Crypto.RomQueryFloor.birthday_bound` at the REAL digest cardinality `pN ≈ 2^255`: §B.
  * States the honest composite in §C — what is now proved, what is now a priced number, what
    remains assumed (`SpongeKeyedROFaithful` for this one experiment, and P10) and why nothing else
    is.

## Sources (read, not authored from)

  * `~/dev/mina-rust` `crates/ledger/src/proofs/transaction.rs:158-343`
    (`scalar_challenge::to_field_checked_prime` / `to_field_checked` / `endo_cvar`), `step.rs:551-556`
    (`endo := endos::<Fq>().1`, i.e. **`lambdaVesta`**, feeding `to_field_checked::<Fp,128>` inside
    the STEP circuit's `finalize_other_proof`).
  * `Dregg2/Circuit/Emit/PastaCurve.lean` — `pN`, `lambdaVesta`, `lambdaVesta_cube`,
    `lambdaVesta_ne_one` (already proven, reused unchanged; NOT re-derived).
  * `Dregg2/Circuit/Emit/PastaPoseidon.lean` — `Ref.hash`, `getD_round`, `permFrom_succ`, the
    KAT-anchored Kimchi Poseidon-over-Pasta-Fp reference (already proven, reused unchanged).
  * `Dregg2/Crypto/RomQueryFloor.lean` — `birthday_bound`, the PROVED information-theoretic floor
    this file transports (reused unchanged).
  * `Dregg2/Crypto/Poseidon2RomInstantiation.lean` — the `KeyedRomFaithful`-shaped ROM-heuristic
    predicate this file's `SpongeKeyedROFaithful` mirrors (a fresh, self-contained instance at THIS
    file's domain, not an import — the collision face alone, no hiding claim needed for P4).

## Axiom hygiene

`#assert_axioms` per theorem and `#assert_namespace_axioms` for the namespace (§Y). No `sorry`, no
`native_decide`.
-/
import Dregg2.Circuit.Emit.PicklesFinalize
import Dregg2.Circuit.Emit.PastaCurve
import Dregg2.Circuit.Emit.PastaPoseidon
import Dregg2.Crypto.RomQueryFloor
import Mathlib.Tactic

namespace Dregg2.Circuit.Emit.PicklesTranscriptBinding

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (lambdaVesta lambdaVesta_cube lambdaVesta_ne_one)
open Dregg2.Circuit.Emit.PastaPoseidon
open Dregg2.Circuit.Emit.PicklesRecursion (Fp)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (collWin birthday_bound)

set_option autoImplicit false
set_option maxRecDepth 4000

/-! ## §A — `endoMap` is injective on 128-bit prechallenges: SETTLED, both halves.

The real map (`step.rs:551-556`) is a composite of two independent steps, and each has its own
obstruction:

  1. **`to_field_checked_prime`** (`transaction.rs:165-235`) reads the 128 raw bits two at a time
     (a "nybble" `v ∈ Fin 4`) and folds TWO accumulators `(a,b)`, starting at `a₀=b₀=2`: each nybble
     contributes a signed `±1` digit to EXACTLY ONE of `a,b` (never both, never neither) —
     `a_array = [0,0,-1,1]`, `b_array = [-1,1,0,0]`, indexed by the nybble's value (`:173-177`). §A.1
     proves this bit-to-`(a,b)` map is injective.
  2. **`to_field_checked`** (`:238-244`) computes `a·endo+b`. §A.2 proves THIS is injective on the
     bounded range `(a,b)` actually reaches, at `endo = lambdaVesta`.

§A.3 composes both into `endoMap_injective_mod`, THE settled fact — checked as equality MOD `pN` (the
field the scalar actually lives in), which is the faithful statement: two 128-bit prechallenges
producing the SAME Fp scalar are the SAME 128 bits. -/

/-! ### §A.1 — the bit-to-`(a,b)` map is injective (combinatorial, no field arithmetic). -/

/-- One nybble's signed contribution to `(a,b)` — `a_array`/`b_array` of
`transaction.rs:173,176`, indexed by the nybble's raw value. Exactly one of the pair is nonzero at
every `v`, and it is `+1` or `-1`, never anything else. -/
def nybbleDelta : Fin 4 → ℤ × ℤ
  | 0 => (0, -1)
  | 1 => (0, 1)
  | 2 => (-1, 0)
  | 3 => (1, 0)

/-- The `(a,b)` accumulator, folding a nybble stream from `to_field_checked_prime`'s own start value
`a₀=b₀=2` (`transaction.rs:201-203`, `let two: F = 2u64.into(); let mut a = two; let mut b = two;`).
One step per nybble: `a ↦ 2a+Δa`, `b ↦ 2b+Δb` (`:217-227`, the per-nybble `accum.double() + a_func`/
`b_func` fold — `nybbles_per_row` nybbles per row, `rows` rows, is the SAME flat fold over all
nybbles in order; the row/8-nybble grouping is a batching detail that does not change the function). -/
def foldAB : List (Fin 4) → ℤ × ℤ :=
  List.foldl (fun ab v => (2 * ab.1 + (nybbleDelta v).1, 2 * ab.2 + (nybbleDelta v).2)) (2, 2)

/-- `Δ := a-contribution + b-contribution` — always `±1` (never `0`), since exactly one channel is
active per nybble. -/
def deltaOf (v : Fin 4) : ℤ := (nybbleDelta v).1 + (nybbleDelta v).2

/-- `ε := a-contribution − b-contribution` — likewise always `±1`. -/
def epsOf (v : Fin 4) : ℤ := (nybbleDelta v).1 - (nybbleDelta v).2

theorem deltaOf_eq_one_or_neg_one (v : Fin 4) : deltaOf v = 1 ∨ deltaOf v = -1 := by
  fin_cases v <;> decide

theorem epsOf_eq_one_or_neg_one (v : Fin 4) : epsOf v = 1 ∨ epsOf v = -1 := by
  fin_cases v <;> decide

/-- **The `(Δ,ε)` pair determines `v`.** All four nybbles give a DISTINCT `(Δ,ε)` — the four sign
combinations `(±1,±1)` appear exactly once each. This is what lets the two independent
signed-binary decodings below be recombined into the original nybble. -/
theorem deltaEps_injective : Function.Injective (fun v : Fin 4 => (deltaOf v, epsOf v)) := by
  decide

/-- Range bound for a fixed digit-`±1` fold: doubling-with-`±1`-digit accumulation from `c₀` stays
within `c₀·2^k ± (2^k−1)` after `k` steps — the induction that makes recovering the digit stream
from the final value possible. -/
theorem foldl_signedBinary_range (c0 : ℤ) (ds : List ℤ) (hds : ∀ d ∈ ds, d = 1 ∨ d = -1) :
    c0 * 2 ^ ds.length - (2 ^ ds.length - 1) ≤ List.foldl (fun c d => 2 * c + d) c0 ds
      ∧ List.foldl (fun c d => 2 * c + d) c0 ds ≤ c0 * 2 ^ ds.length + (2 ^ ds.length - 1) := by
  induction ds generalizing c0 with
  | nil => simp
  | cons d rest ih =>
    have hd : d = 1 ∨ d = -1 := hds d List.mem_cons_self
    have hrest : ∀ e ∈ rest, e = 1 ∨ e = -1 := fun e he => hds e (List.mem_cons_of_mem d he)
    have hstep := ih (2 * c0 + d) hrest
    simp only [List.foldl_cons, List.length_cons]
    obtain ⟨hlo, hhi⟩ := hstep
    rcases hd with rfl | rfl <;>
      constructor <;>
      [skip; skip; skip; skip] <;>
      (rw [pow_succ]; nlinarith [hlo, hhi])

/-- **Fixed-length signed-binary (digits `±1`) representations are injective** — the standard fact
underlying the whole argument: a length-`n` digit stream, accumulated by doubling, is recoverable
from its final value alone. Peels the FIRST digit; the two candidate continuations occupy DISJOINT
integer ranges (centers `2c₀+1`/`2c₀-1` differ by `2`, each sub-range has width `< 2` relative to
that gap). -/
theorem signedBinary_injective (c0 : ℤ) (ds ds' : List ℤ) (hlen : ds.length = ds'.length)
    (hds : ∀ d ∈ ds, d = 1 ∨ d = -1) (hds' : ∀ d ∈ ds', d = 1 ∨ d = -1)
    (heq : List.foldl (fun c d => 2 * c + d) c0 ds = List.foldl (fun c d => 2 * c + d) c0 ds') :
    ds = ds' := by
  induction ds generalizing c0 ds' with
  | nil =>
    cases ds' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons d rest ih =>
    cases ds' with
    | nil => simp at hlen
    | cons d' rest' =>
      simp only [List.foldl_cons] at heq
      have hd : d = 1 ∨ d = -1 := hds d List.mem_cons_self
      have hd' : d' = 1 ∨ d' = -1 := hds' d' List.mem_cons_self
      have hrest : ∀ e ∈ rest, e = 1 ∨ e = -1 := fun e he => hds e (List.mem_cons_of_mem d he)
      have hrest' : ∀ e ∈ rest', e = 1 ∨ e = -1 := fun e he => hds' e (List.mem_cons_of_mem d' he)
      have hlen' : rest.length = rest'.length := by simpa using hlen
      have hb1 := foldl_signedBinary_range (2 * c0 + d) rest hrest
      have hb2 := foldl_signedBinary_range (2 * c0 + d') rest' hrest'
      rw [hlen'] at hb1
      have hdd' : d = d' := by
        rcases hd with rfl | rfl <;> rcases hd' with rfl | rfl <;>
          first
          | rfl
          | (exfalso; nlinarith [hb1.1, hb1.2, hb2.1, hb2.2, heq,
              pow_pos (by norm_num : (0:ℤ) < 2) rest'.length])
      subst hdd'
      have hcont : List.foldl (fun c d => 2*c+d) (2*c0+d) rest
          = List.foldl (fun c d => 2*c+d) (2*c0+d) rest' := heq
      have := ih (2*c0+d) rest' hlen' hrest hrest' hcont
      rw [this]

/-- Generalized fold-congruence: `a+b` and `a-b` each track their own signed-binary fold, at any
starting `(a,b)` (generalized so the induction goes through). -/
theorem foldAB_gen (l : List (Fin 4)) (a b : ℤ) :
    (List.foldl (fun ab v => (2*ab.1+(nybbleDelta v).1, 2*ab.2+(nybbleDelta v).2)) (a,b) l).1
      + (List.foldl (fun ab v => (2*ab.1+(nybbleDelta v).1, 2*ab.2+(nybbleDelta v).2)) (a,b) l).2
      = List.foldl (fun c v => 2*c + deltaOf v) (a+b) l
    ∧ (List.foldl (fun ab v => (2*ab.1+(nybbleDelta v).1, 2*ab.2+(nybbleDelta v).2)) (a,b) l).1
      - (List.foldl (fun ab v => (2*ab.1+(nybbleDelta v).1, 2*ab.2+(nybbleDelta v).2)) (a,b) l).2
      = List.foldl (fun c v => 2*c + epsOf v) (a-b) l := by
  induction l generalizing a b with
  | nil => exact ⟨rfl, rfl⟩
  | cons v rest ih =>
    simp only [List.foldl_cons]
    obtain ⟨h1, h2⟩ := ih (2*a+(nybbleDelta v).1) (2*b+(nybbleDelta v).2)
    constructor
    · rw [h1]; congr 1; unfold deltaOf; ring
    · rw [h2]; congr 1; unfold epsOf; ring

theorem foldAB_add_eq (l : List (Fin 4)) :
    (foldAB l).1 + (foldAB l).2 = List.foldl (fun c v => 2 * c + deltaOf v) 4 l :=
  (foldAB_gen l 2 2).1

theorem foldAB_sub_eq (l : List (Fin 4)) :
    (foldAB l).1 - (foldAB l).2 = List.foldl (fun c v => 2 * c + epsOf v) 0 l :=
  (foldAB_gen l 2 2).2

/-- Two nybble streams agreeing on their `deltaOf`-image and `epsOf`-image (pointwise, at equal
length) are equal — the pointwise recombination via `deltaEps_injective`. -/
theorem eq_of_map_delta_eps (l l' : List (Fin 4)) (hlen : l.length = l'.length)
    (hΔ : List.map deltaOf l = List.map deltaOf l') (hε : List.map epsOf l = List.map epsOf l') :
    l = l' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons v rest ih =>
    cases l' with
    | nil => simp at hlen
    | cons v' rest' =>
      simp only [List.map_cons, List.cons.injEq] at hΔ hε
      have hlen' : rest.length = rest'.length := by simpa using hlen
      have hv : v = v' := deltaEps_injective (Prod.ext hΔ.1 hε.1)
      have hrest : rest = rest' := ih rest' hlen' hΔ.2 hε.2
      rw [hv, hrest]

/-- **`foldAB` is injective on fixed-length nybble streams.** -/
theorem foldAB_injective_of_len_eq (l l' : List (Fin 4)) (hlen : l.length = l'.length)
    (heq : foldAB l = foldAB l') : l = l' := by
  have hsum : (foldAB l).1 + (foldAB l).2 = (foldAB l').1 + (foldAB l').2 := by rw [heq]
  have hdiff : (foldAB l).1 - (foldAB l).2 = (foldAB l').1 - (foldAB l').2 := by rw [heq]
  rw [foldAB_add_eq, foldAB_add_eq] at hsum
  rw [foldAB_sub_eq, foldAB_sub_eq] at hdiff
  have hΔ : List.map deltaOf l = List.map deltaOf l' := by
    apply signedBinary_injective 4 (List.map deltaOf l) (List.map deltaOf l')
    · simpa using hlen
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨v, _, rfl⟩ := hd
      exact deltaOf_eq_one_or_neg_one v
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨v, _, rfl⟩ := hd
      exact deltaOf_eq_one_or_neg_one v
    · rwa [List.foldl_map, List.foldl_map]
  have hε : List.map epsOf l = List.map epsOf l' := by
    apply signedBinary_injective 0 (List.map epsOf l) (List.map epsOf l')
    · simpa using hlen
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨v, _, rfl⟩ := hd
      exact epsOf_eq_one_or_neg_one v
    · intro d hd
      simp only [List.mem_map] at hd
      obtain ⟨v, _, rfl⟩ := hd
      exact epsOf_eq_one_or_neg_one v
    · rwa [List.foldl_map, List.foldl_map]
  exact eq_of_map_delta_eps l l' hlen hΔ hε

/-- Range for a length-64 nybble stream (128 raw bits): both `a,b` land in `[2⁶⁴+1, 3·2⁶⁴−1]`. The
`64` is not a magic number here: it is the number of 2-bit nybbles in a 128-bit prechallenge. -/
theorem foldAB_range (l : List (Fin 4)) (hlen : l.length = 64) :
    2 ^ 64 + 1 ≤ (foldAB l).1 ∧ (foldAB l).1 ≤ 3 * 2 ^ 64 - 1
    ∧ 2 ^ 64 + 1 ≤ (foldAB l).2 ∧ (foldAB l).2 ≤ 3 * 2 ^ 64 - 1 := by
  have hΔ : ∀ d ∈ List.map deltaOf l, d = 1 ∨ d = -1 := by
    intro d hd; simp only [List.mem_map] at hd; obtain ⟨v,_,rfl⟩ := hd
    exact deltaOf_eq_one_or_neg_one v
  have hε : ∀ d ∈ List.map epsOf l, d = 1 ∨ d = -1 := by
    intro d hd; simp only [List.mem_map] at hd; obtain ⟨v,_,rfl⟩ := hd
    exact epsOf_eq_one_or_neg_one v
  have hc := foldl_signedBinary_range 4 (List.map deltaOf l) hΔ
  have hd := foldl_signedBinary_range 0 (List.map epsOf l) hε
  rw [List.length_map, hlen] at hc hd
  rw [List.foldl_map] at hc hd
  rw [← foldAB_add_eq] at hc
  rw [← foldAB_sub_eq] at hd
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [hc.1, hc.2, hd.1, hd.2]

/-! ### The bridge: 128 raw bits ↔ 64 nybbles.

The exact bit ORDER `to_field_checked_prime` uses (`bit+1` low, `bit` high within a nybble,
`transaction.rs:192-195`) does not affect injectivity — any fixed pairing does. `pairToNybble` fixes
one; `bitsNybble`/`toNybbleList` are the resulting `Fin 128 → Bool` ↔ `List (Fin 4)` bridge, via
`Fin`-indexing (robust to the equation compiler, unlike a hand-rolled recursive chunker). -/

def pairToNybble : Bool × Bool → Fin 4
  | (false, false) => 0
  | (true, false) => 1
  | (false, true) => 2
  | (true, true) => 3

theorem pairToNybble_injective : Function.Injective pairToNybble := by decide

/-- The `i`-th nybble of a 128-bit prechallenge: its two raw bits at positions `2i, 2i+1`. -/
def bitsNybble (bits : Fin 128 → Bool) (i : Fin 64) : Fin 4 :=
  pairToNybble (bits ⟨2 * i.1, by omega⟩, bits ⟨2 * i.1 + 1, by omega⟩)

theorem bitsNybble_injective : Function.Injective bitsNybble := by
  intro bits bits' heq
  funext j
  rcases j with ⟨jv, jlt⟩
  rcases Nat.even_or_odd jv with heven | hodd
  · obtain ⟨k, hk⟩ := heven
    have hklt : k < 64 := by omega
    have hcall := congrFun heq (⟨k, hklt⟩ : Fin 64)
    unfold bitsNybble at hcall
    have hp := pairToNybble_injective hcall
    have h1 := congrArg Prod.fst hp
    simp only at h1
    have heqidx : (⟨2 * k, by omega⟩ : Fin 128) = (⟨jv, jlt⟩ : Fin 128) := by
      apply Fin.ext; simp; omega
    rw [heqidx] at h1
    exact h1
  · obtain ⟨k, hk⟩ := hodd
    have hklt : k < 64 := by omega
    have hcall := congrFun heq (⟨k, hklt⟩ : Fin 64)
    unfold bitsNybble at hcall
    have hp := pairToNybble_injective hcall
    have h2 := congrArg Prod.snd hp
    simp only at h2
    have heqidx : (⟨2 * k + 1, by omega⟩ : Fin 128) = (⟨jv, jlt⟩ : Fin 128) := by
      apply Fin.ext; simp; omega
    rw [heqidx] at h2
    exact h2

def toNybbleList (bits : Fin 128 → Bool) : List (Fin 4) := List.ofFn (bitsNybble bits)

theorem toNybbleList_length (bits : Fin 128 → Bool) : (toNybbleList bits).length = 64 := by
  simp [toNybbleList]

theorem toNybbleList_injective : Function.Injective toNybbleList := by
  intro bits bits' heq
  apply bitsNybble_injective
  unfold toNybbleList at heq
  exact List.ofFn_injective heq

/-! ### §A.2 — field-level injectivity, at the REAL `lambdaVesta`/`pN`.

The lattice `{(x,y) : x ≡ y·lambdaVesta (mod pN)}` was Gauss/Lagrange-reduced OUTSIDE Lean (a fast,
exact 2D computation on the real 255-bit `pN` and `lambdaVesta`); the shortest vector found is
exhibited below as `glvA, glvB` and its defining properties are `decide`-checked in-kernel: it lies
in the lattice, its Eisenstein norm `a²+ab+b² = pN` EXACTLY (the classical confirmation that this is
the canonical short vector, since `pN` splits as that norm in `ℤ[ω]` — `lambdaVesta` being a
primitive cube root of unity mod `pN` is exactly the CM condition for this), and `gcd(a,b)=1`.
Minimality is then proved by the ELEMENTARY argument in `glv_no_small_relation`, not asserted. -/

/-- The Gauss-reduced shortest-vector coordinate `a` (the `x`-side): `98231058071186745657228807
397848383488`, ≈2^127. Both coordinates are ~127 bits, dwarfing the `< 2^70` range 128-bit
prechallenges reach. -/
def glvA : ℤ := 98231058071186745657228807397848383488
/-- The Gauss-reduced shortest-vector coordinate `b` (the `y`-side). -/
def glvB : ℤ := 98231058071100081932162823354453065729

theorem glv_dvd : (pN:ℤ) ∣ (glvA - glvB * (lambdaVesta:ℤ)) := by decide

theorem glv_eisenstein_norm : glvA ^ 2 + glvA * glvB + glvB ^ 2 = (pN:ℤ) := by decide

theorem glv_coprime : Int.gcd glvA glvB = 1 := by decide

theorem glvA_pos : (0:ℤ) < glvA := by decide
theorem glvB_pos : (0:ℤ) < glvB := by decide
theorem glvA_gt_bound : (2:ℤ) ^ 70 < glvA := by decide
theorem glvB_gt_bound : (2:ℤ) ^ 70 < glvB := by decide
theorem glv_margin : (2:ℤ) * 2 ^ 70 * (glvA + glvB) < (pN:ℤ) := by decide

/-- **The GLV lattice for `lambdaVesta` mod `pN` has no nonzero relation below `2^70`** — the
shortest vector `(glvA, glvB)` is proved minimal here by an ELEMENTARY coprimality argument (no
general lattice-reduction theorem invoked): a relation `x ≡ y·lambdaVesta (mod pN)` forces
`pN ∣ (glvB·x − glvA·y)` (multiply by `glvB`, use `glvB·lambdaVesta ≡ glvA`); the product is bounded
below `pN` by `glv_margin`, so it is EXACTLY `0` (not merely `≡0`); coprimality (`glv_coprime`) then
forces `x` to be an integer multiple of `glvA`, and `|x| < 2^70 < glvA` forces that multiple to be
`0`. -/
theorem glv_no_small_relation (x y : ℤ) (hx : |x| < 2 ^ 70) (hy : |y| < 2 ^ 70)
    (hrel : (pN:ℤ) ∣ (x - y * (lambdaVesta:ℤ))) : x = 0 ∧ y = 0 := by
  have hstep : (pN:ℤ) ∣ (glvB * x - glvA * y) := by
    have heq : glvB * x - glvA * y
        = glvB * (x - y * (lambdaVesta:ℤ)) - y * (glvA - glvB * (lambdaVesta:ℤ)) := by ring
    rw [heq]
    exact dvd_sub (Dvd.dvd.mul_left hrel glvB) (Dvd.dvd.mul_left glv_dvd y)
  have hbound : |glvB * x - glvA * y| < (pN:ℤ) := by
    have h1 : |glvB * x - glvA * y| ≤ |glvB * x| + |glvA * y| := abs_sub _ _
    have h2 : |glvB * x| = glvB * |x| := by rw [abs_mul, abs_of_pos glvB_pos]
    have h3 : |glvA * y| = glvA * |y| := by rw [abs_mul, abs_of_pos glvA_pos]
    have h4 : glvB * |x| < glvB * 2 ^ 70 := mul_lt_mul_of_pos_left hx glvB_pos
    have h5 : glvA * |y| < glvA * 2 ^ 70 := mul_lt_mul_of_pos_left hy glvA_pos
    calc |glvB * x - glvA * y| ≤ |glvB * x| + |glvA * y| := h1
      _ = glvB * |x| + glvA * |y| := by rw [h2, h3]
      _ < glvB * 2 ^ 70 + glvA * 2 ^ 70 := by linarith
      _ = 2 ^ 70 * (glvA + glvB) := by ring
      _ < (pN:ℤ) := by nlinarith [glv_margin]
  have hzero : glvB * x - glvA * y = 0 := by
    rcases hstep with ⟨k, hk⟩
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk, hk0]; ring
    · exfalso
      have h1 : (1:ℤ) ≤ |k| := by
        rcases lt_or_gt_of_ne hk0 with h | h
        · calc (1:ℤ) ≤ -k := by omega
            _ ≤ |k| := by rw [abs_of_neg h]
        · calc (1:ℤ) ≤ k := by omega
            _ ≤ |k| := le_abs_self k
      have hpNpos : (0:ℤ) < (pN:ℤ) := by
        have : (0:ℕ) < pN := by decide
        exact_mod_cast this
      have hge : (pN:ℤ) ≤ |glvB * x - glvA * y| := by
        rw [hk, abs_mul, abs_of_pos hpNpos]
        calc (pN:ℤ) = (pN:ℤ) * 1 := by ring
          _ ≤ (pN:ℤ) * |k| := mul_le_mul_of_nonneg_left h1 (le_of_lt hpNpos)
      linarith [hbound]
  have hxy : glvB * x = glvA * y := by linarith [hzero]
  have hdvd : glvA ∣ glvB * x := ⟨y, hxy⟩
  have hcop : IsCoprime glvA glvB := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact glv_coprime
  have hax : glvA ∣ x := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨k, hk⟩ := hax
  have hk0 : k = 0 := by
    by_contra hk0'
    have h1 : (1:ℤ) ≤ |k| := by
      rcases lt_or_gt_of_ne hk0' with h | h
      · calc (1:ℤ) ≤ -k := by omega
          _ ≤ |k| := by rw [abs_of_neg h]
      · calc (1:ℤ) ≤ k := by omega
          _ ≤ |k| := le_abs_self k
    have hxle : glvA ≤ |x| := by
      rw [hk, abs_mul, abs_of_pos glvA_pos]
      calc glvA = glvA * 1 := by ring
        _ ≤ glvA * |k| := mul_le_mul_of_nonneg_left h1 (le_of_lt glvA_pos)
    linarith [glvA_gt_bound, hx]
  have hxzero : x = 0 := by rw [hk, hk0, mul_zero]
  refine ⟨hxzero, ?_⟩
  rw [hxzero] at hxy
  have hyzero : glvA * y = 0 := by linarith [hxy]
  rcases mul_eq_zero.mp hyzero with h | h
  · exact absurd h (by linarith [glvA_pos])
  · exact h

/-! ### §A.3 — composing both halves: `endoMap` is injective, on the REAL constants. -/

/-- **The composite** — `to_field_checked_prime` then `a·lambdaVesta+b`, at 128-bit prechallenges
modeled as `Fin 128 → Bool`. -/
def endoMap (bits : Fin 128 → Bool) : ℤ :=
  (foldAB (toNybbleList bits)).1 * (lambdaVesta:ℤ) + (foldAB (toNybbleList bits)).2

/-- **⚑⚑⚑ `endoMap` is injective on 128-bit prechallenges — SETTLED, not assumed.** The composite
map Pickles actually runs, at the REAL endo constant (`lambdaVesta`), is injective — checked as
EQUALITY MOD `pN` (the field the scalar actually lives in), which is the faithful statement: two
128-bit prechallenges producing the SAME Fp scalar are the SAME 128 bits. This closes
`PicklesFinalize` §Z item 2: "`endo` injectivity is a hypothesis, not a theorem" no longer holds at
the concrete Step-circuit instantiation. -/
theorem endoMap_injective_mod (bits bits' : Fin 128 → Bool)
    (heq : (pN:ℤ) ∣ (endoMap bits - endoMap bits')) : bits = bits' := by
  apply toNybbleList_injective
  apply foldAB_injective_of_len_eq _ _ (by rw [toNybbleList_length, toNybbleList_length])
  set ab := foldAB (toNybbleList bits) with hab
  set ab' := foldAB (toNybbleList bits') with hab'
  have hrangeb := foldAB_range (toNybbleList bits) (toNybbleList_length bits)
  have hrangeb' := foldAB_range (toNybbleList bits') (toNybbleList_length bits')
  have hdvd : (pN:ℤ) ∣ ((ab'.2 - ab.2) - (ab.1 - ab'.1) * (lambdaVesta:ℤ)) := by
    have hexp : endoMap bits - endoMap bits'
        = (ab.1 - ab'.1) * (lambdaVesta:ℤ) + (ab.2 - ab'.2) := by
      unfold endoMap; rw [← hab, ← hab']; ring
    rw [hexp] at heq
    have heq2 : (ab'.2 - ab.2) - (ab.1 - ab'.1) * (lambdaVesta:ℤ)
        = -((ab.1 - ab'.1) * (lambdaVesta:ℤ) + (ab.2 - ab'.2)) := by ring
    rw [heq2]
    exact dvd_neg.mpr heq
  have hbound1 : |ab'.2 - ab.2| < 2 ^ 70 := by
    rw [abs_lt]
    constructor <;>
      nlinarith [hrangeb.1, hrangeb.2.1, hrangeb.2.2.1, hrangeb.2.2.2,
        hrangeb'.1, hrangeb'.2.1, hrangeb'.2.2.1, hrangeb'.2.2.2]
  have hbound2 : |ab.1 - ab'.1| < 2 ^ 70 := by
    rw [abs_lt]
    constructor <;>
      nlinarith [hrangeb.1, hrangeb.2.1, hrangeb.2.2.1, hrangeb.2.2.2,
        hrangeb'.1, hrangeb'.2.1, hrangeb'.2.2.1, hrangeb'.2.2.2]
  have hfinal := glv_no_small_relation (ab'.2 - ab.2) (ab.1 - ab'.1) hbound1 hbound2 hdvd
  have h1 : ab.1 = ab'.1 := by linarith [hfinal.2]
  have h2 : ab.2 = ab'.2 := by linarith [hfinal.1]
  exact Prod.ext h1 h2

/-! ## §B — the sponge-digest binding, reduced to a priced ROM residual.

`PicklesFinalize.assertEqDigest` pins ONE field element (`sampledDigest = exposedDigest`). That this
pins the TRANSCRIPT — the sequence of field elements the sponge absorbed to reach that digest, not
merely its numeric output — is a collision-resistance claim about Poseidon-over-Pasta, and there was
no such assumption OBJECT in this tree. §B.1 states the honest floor (mirroring
`Sha256MerkleFold.pairSepOn`'s three-legs discipline) over the REAL Kimchi Poseidon-over-Pasta-Fp
reference; §B.2 prices it via the PROVED `RomQueryFloor.birthday_bound`, at the real digest
cardinality `pN ≈ 2^255`. -/

/-! ### §B.1 — `hashSepOn`: the honest hash floor, over `PastaPoseidon.Ref.hash`. -/

/-- The mod-`pN` collision: absorbing `x` and absorbing `x+pN` are IDENTICAL — `absorbAt` reduces
its input mod `pN` (`(st.getD j 0 + x) % pN`), so the two singleton transcripts reach the same
state before the closing squeeze-permute. Generic in `x` (no numeric coincidence, unlike the second
witness below) — the SHA-256-fold analogue of `Sha256MerkleFold.pairHash_ignores_word_64`. -/
theorem hash_singleton_ignores_mod_pN (x : Nat) :
    Ref.hash [x] = Ref.hash [x + pN] := by
  have hset : Ref.absorbAt [0,0,0] 0 x = Ref.absorbAt [0,0,0] 0 (x + pN) := by
    show ([0,0,0] : List Nat).set 0 ((([0,0,0]:List Nat).getD 0 0 + x) % pN)
        = ([0,0,0] : List Nat).set 0 ((([0,0,0]:List Nat).getD 0 0 + (x+pN)) % pN)
    norm_num
  show (Ref.absorbFrom [0,0,0] 0 [x]).getD 0 0 = (Ref.absorbFrom [0,0,0] 0 [x+pN]).getD 0 0
  have hstep1 : Ref.absorbFrom [0,0,0] 0 [x] = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 x) 1 [] := by
    show (if (0:Nat) = rate then _ else Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 x) 1 [])
      = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 x) 1 []
    rfl
  have hstep2 : Ref.absorbFrom [0,0,0] 0 [x+pN]
      = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 (x+pN)) 1 [] := by
    show (if (0:Nat) = rate then _ else Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 (x+pN)) 1 [])
      = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 (x+pN)) 1 []
    rfl
  rw [hstep1, hstep2, hset]

theorem pN_pos : 0 < pN := by decide

/-- **A SECOND, sharper structural collision** — absorbing nothing and absorbing a bare `0` are
indistinguishable: `absorbAt` on the zero state at value `0` is a no-op, and both then hit the SAME
closing squeeze-permute. No modular arithmetic at all — a design-level coincidence of the
add-to-absorb sponge, exhibited rather than derived generically. -/
theorem hash_empty_eq_hash_zero : Ref.hash ([] : List Nat) = Ref.hash [0] := by
  show (Ref.absorbFrom [0,0,0] 0 ([] : List Nat)).getD 0 0
      = (Ref.absorbFrom [0,0,0] 0 [0]).getD 0 0
  have hstep : Ref.absorbFrom [0,0,0] 0 [0] = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 0) 1 [] := by
    show (if (0:Nat) = rate then _ else Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 0) 1 [])
      = Ref.absorbFrom (Ref.absorbAt [0,0,0] 0 0) 1 []
    rfl
  have hset : Ref.absorbAt [0,0,0] 0 0 = ([0,0,0] : List Nat) := by
    show ([0,0,0] : List Nat).set 0 ((([0,0,0]:List Nat).getD 0 0 + 0) % pN) = [0,0,0]
    norm_num
  rw [hstep, hset]
  rfl

/-- **The IDEALIZED floor is FALSE**, refuted by the mod-`pN` collision — no pigeonhole appeal
needed, an executable (well, symbolically-generic) collision, mirroring
`Sha256MerkleFold.pairHashInjective_false`. -/
def RefHashInjective : Prop := ∀ xs ys : List Nat, Ref.hash xs = Ref.hash ys → xs = ys

theorem RefHashInjective_false : ¬ RefHashInjective := by
  intro h
  have hcoll := hash_singleton_ignores_mod_pN 0
  have heq := h [0] [0 + pN] hcoll
  have hne : ([0] : List Nat) ≠ [0 + pN] := by decide
  exact hne heq

/-- **`hashSepOn P`** — the HONEST hash floor: `Ref.hash` separates on the transcripts satisfying
`P`. Mirrors `Sha256MerkleFold.pairSepOn`, at variable-length input rather than fixed-arity pairs;
a consumer must EXHIBIT the finite class its own transcripts live in and pay for it (§B.2 prices
that payment). -/
def hashSepOn (P : List Nat → Prop) : Prop :=
  ∀ a b, P a → P b → Ref.hash a = Ref.hash b → a = b

theorem hashSepOn_mono {P Q : List Nat → Prop} (hPQ : ∀ a, P a → Q a) (h : hashSepOn Q) :
    hashSepOn P :=
  fun a b ha hb e => h a b (hPQ a ha) (hPQ b hb) e

/-- UPPER POLE — at the unrestricted class the floor is the refuted idealized injectivity. -/
theorem hashSepOn_top_imp : hashSepOn (fun _ => True) → RefHashInjective :=
  fun h a b => h a b trivial trivial

theorem hashSepOn_top_false : ¬ hashSepOn (fun _ => True) :=
  fun h => RefHashInjective_false (hashSepOn_top_imp h)

/-- LOWER POLE — vacuous at the empty class, priced the same way `pairSepOn_bot` is. -/
theorem hashSepOn_bot : hashSepOn (fun _ => False) := fun _ _ h => h.elim

/-- The two transcripts of the empty/zero collision — a genuinely two-element class (not only
`⊤`) on which the floor FAILS, mirroring `pairSepOn_truncSep_false`. -/
def truncHashSep (a : List Nat) : Prop := a = [] ∨ a = [0]

theorem hashSepOn_truncHashSep_false : ¬ hashSepOn truncHashSep := by
  intro h
  have heq := h [] [0] (Or.inl rfl) (Or.inr rfl) hash_empty_eq_hash_zero
  exact absurd heq (by simp)

/-- Three pairwise-distinct transcripts — the exhibited class the model pays for, over the REAL
deployed Kimchi Poseidon (the SAME KATs `PastaPoseidon.lean` §5 anchors to o1js gold vectors). -/
def modelHashSep (a : List Nat) : Prop := a = [0] ∨ a = [1] ∨ a = [2]

/-- **SATISFIABLE LEG.** Kernel-evaluated on the real Kimchi Poseidon-over-Pasta-Fp. -/
theorem hashSepOn_modelHashSep : hashSepOn modelHashSep := by
  intro a b ha hb e
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first
      | rfl
      | exact absurd e (by decide)

/-- The satisfying class is genuinely inhabited by distinct transcripts — not the empty class
wearing the `hashSepOn` name (`hashSepOn_bot` is what that would be). -/
theorem modelHashSep_class_inhabited :
    modelHashSep [0] ∧ modelHashSep [1] ∧ ([0] : List Nat) ≠ [1] := by
  refine ⟨Or.inl rfl, Or.inr (Or.inl rfl), ?_⟩
  simp

/-! ### `Ref.hash` always computes a genuine Fp element (`< pN`).

The fact that lets a Nat equality `Ref.hash a = Ref.hash b` be read as the FIELD equality
`assertEqDigest` actually asserts — every `round` output is `%pN`-reduced, and `absorbFrom` always
terminates by applying `perm` (the base case), so the final state is always `perm`'s output. -/

theorem round_getD_lt_pN (rc hs : List Nat) (j : ℕ) (hj : j < 3) :
    (Ref.round rc hs).getD j 0 < pN := by
  rw [getD_round rc hs j hj]
  exact Nat.mod_lt _ pN_pos

theorem permFrom_getD_lt_pN (r0 n : ℕ) (hn : 0 < n) (hs : List Nat) (j : ℕ) (hj : j < 3) :
    (Ref.permFrom r0 n hs).getD j 0 < pN := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [permFrom_succ]
  exact round_getD_lt_pN _ _ j hj

theorem perm_getD_lt_pN (hs : List Nat) (j : ℕ) (hj : j < 3) :
    (Ref.perm hs).getD j 0 < pN := by
  show (Ref.permFrom 0 rounds hs).getD j 0 < pN
  exact permFrom_getD_lt_pN 0 rounds (by decide) hs j hj

theorem absorbFrom_getD_lt_pN (st : List Nat) (n : ℕ) (xs : List Nat) (j : ℕ) (hj : j < 3) :
    (Ref.absorbFrom st n xs).getD j 0 < pN := by
  induction xs generalizing st n with
  | nil =>
    show (Ref.perm st).getD j 0 < pN
    exact perm_getD_lt_pN st j hj
  | cons x rest ih =>
    show (if n = rate then Ref.absorbFrom (Ref.absorbAt (Ref.perm st) 0 x) 1 rest
          else Ref.absorbFrom (Ref.absorbAt st n x) (n + 1) rest).getD j 0 < pN
    split
    · exact ih _ _
    · exact ih _ _

theorem hash_lt_pN (xs : List Nat) : Ref.hash xs < pN := by
  show (Ref.absorbFrom [0, 0, 0] 0 xs).getD 0 0 < pN
  exact absorbFrom_getD_lt_pN [0, 0, 0] 0 xs 0 (by norm_num)

/-- **THE KEY REDUCTION** — the sponge-digest equality PINS THE TRANSCRIPT, given separation on the
class of transcripts the two verification instances actually feed the sponge. "The digest pins a
value, not a history" turned into a theorem: `hashSepOn` on the relevant class is exactly what
closes the gap. -/
theorem digest_binds_transcript_on (P : List Nat → Prop) (hsep : hashSepOn P)
    (t1 t2 : List Nat) (h1 : P t1) (h2 : P t2)
    (hdigest : Ref.hash t1 = Ref.hash t2) : t1 = t2 :=
  hsep t1 t2 h1 h2 hdigest

/-- The Fp-typed form, connecting directly to `PicklesFinalize.assertEqDigest (R := Fp)`: an
`assertEqDigest` between the two REAL digests, plus `hashSepOn` on a class covering both
transcripts, gives transcript equality. -/
theorem assertEqDigest_binds_transcript_on (P : List Nat → Prop) (hsep : hashSepOn P)
    (t1 t2 : List Nat) (h1 : P t1) (h2 : P t2)
    (hdigest : Dregg2.Circuit.Emit.PicklesFinalize.assertEqDigest
        ((Ref.hash t1 : Fp)) ((Ref.hash t2 : Fp))) :
    t1 = t2 := by
  apply digest_binds_transcript_on P hsep t1 t2 h1 h2
  unfold Dregg2.Circuit.Emit.PicklesFinalize.assertEqDigest at hdigest
  have := (ZMod.natCast_eq_natCast_iff' (Ref.hash t1) (Ref.hash t2) pN).mp hdigest
  rwa [Nat.mod_eq_of_lt (hash_lt_pN t1), Nat.mod_eq_of_lt (hash_lt_pN t2)] at this

/-! ### §B.2 — pricing the residual: `birthday_bound` at the REAL digest cardinality. -/

/-- The sponge, restricted to fixed-length-`ell` transcripts over `Fin pN` (a finite domain, so
`birthday_bound` applies with NO asymptotics) and squeezed into `Fin pN` (the digest's own field,
via the same `% pN` the reference itself reduces through at every step). -/
def transcriptHash (ell : ℕ) (t : Fin ell → Fin pN) : Fin pN :=
  ⟨Ref.hash (List.ofFn (fun i => (t i).val)) % pN, Nat.mod_lt _ pN_pos⟩

/-- **`SpongeKeyedROFaithful M` — the ONE named ROM assumption this file needs.** Mirrors
`Crypto.Poseidon2RomInstantiation.KeyedRomFaithful` (the tree's established per-experiment
ROM-heuristic predicate), specialized to the collision face alone (P4 needs no hiding claim): against
the FIXED, deployed sponge, forger `M`'s fixed-oracle collision odds are no better than its
SAMPLED-oracle odds. A `def`, never an `axiom`; NOT provable (the sponge is a fixed public function,
so choosing `M` to already know a baked-in collision — the SAME shape as
`Poseidon2RomInstantiation`'s `leakForger` — refutes the `∀ M` strengthening, exactly as there). -/
def SpongeKeyedROFaithful {ell : ℕ}
    (M : OracleComp (Fin ell → Fin pN) (Fin pN) ((Fin ell → Fin pN) × (Fin ell → Fin pN))) :
    Prop :=
  (if collWin M (transcriptHash ell) then (1:ℝ) else 0)
    ≤ Dregg2.Crypto.ProbCrypto.winProb (collWin M)

/-- **⚑⚑ THE PRICED RESIDUAL.** Under `SpongeKeyedROFaithful`, a `Q`-query forger's collision
indicator against the DEPLOYED sponge is at most `(Q²+1)/pN` — `birthday_bound`, untouched,
transported through the one named assumption, at `pN ≈ 2^255`. -/
theorem deployed_digest_collision_bound {ell : ℕ}
    (M : OracleComp (Fin ell → Fin pN) (Fin pN) ((Fin ell → Fin pN) × (Fin ell → Fin pN)))
    (Q : ℕ) (hM : QueryBounded Q M) (hFaithful : SpongeKeyedROFaithful M) :
    (if collWin M (transcriptHash ell) then (1:ℝ) else 0) ≤ ((Q:ℝ)*(Q:ℝ)+1) / (pN:ℝ) := by
  haveI : Nonempty (Fin pN) := ⟨⟨0, pN_pos⟩⟩
  have h1 := hFaithful
  have h2 := birthday_bound (D := Fin ell → Fin pN) (R := Fin pN) Q M hM
  have hc : ((Fintype.card (Fin pN) : ℕ) : ℝ) = (pN:ℝ) := by simp
  rw [hc] at h2
  exact h1.trans h2

/-- **⚑ NO COLLISION AT ALL**, for any query budget under the (astronomically permissive) bar
`Q²+1 < pN`. At `pN ≈ 2^255`, EVERY query budget any real adversary could run (`Q` up to, say,
`2^120`) satisfies this with room to spare — the number the sponge-digest assumption is now priced
at, not merely asserted. -/
theorem deployed_digest_noCollision {ell : ℕ}
    (M : OracleComp (Fin ell → Fin pN) (Fin pN) ((Fin ell → Fin pN) × (Fin ell → Fin pN)))
    (Q : ℕ) (hM : QueryBounded Q M) (hFaithful : SpongeKeyedROFaithful M)
    (hQ : (Q:ℝ) * (Q:ℝ) + 1 < (pN:ℝ)) :
    collWin M (transcriptHash ell) = false := by
  cases hcw : collWin M (transcriptHash ell) with
  | false => rfl
  | true =>
    have h1 := deployed_digest_collision_bound M Q hM hFaithful
    rw [hcw, if_pos rfl] at h1
    have hpos : (0:ℝ) < (pN:ℝ) := by exact_mod_cast pN_pos
    rw [le_div_iff₀ hpos, one_mul] at h1
    exact absurd hQ (not_lt.mpr h1)

/-! ## §C — the honest composite: what P4 needs, cashed out.

`PicklesFinalize.binding_and_accept_determine` (unconditional, already in the tree) says: two
accepted, transcript-bound `WrapDeferredValues` records sharing the SAME sampled tuple `sm` agree on
all nine coordinates the checks touch. This file adds, at the concrete Fp instantiation:

  * `endoMap_injective_mod` (§A) — the 128-bit prechallenge is recoverable from the endo-mapped
    scalar alone. SETTLED, unconditionally.
  * `assertEqDigest_binds_transcript_on` (§B) — the sponge-digest equality pins the ABSORBED
    TRANSCRIPT, not merely a field value, GIVEN `hashSepOn` on the class the two instances' own
    transcripts live in (`hashSepOn_modelHashSep` exhibits one non-trivial such class; a real
    verifier's transcript class is a further, larger but still FINITE, exhibit — the same shape,
    not new content).
  * `deployed_digest_noCollision` (§B.2) — `hashSepOn` on a `SpongeKeyedROFaithful`-covered class is
    not a bare assumption: it is priced at `(Q²+1)/pN`, i.e. it is what "the sponge behaves like a
    random oracle for THIS one experiment" is worth, in a concrete, tiny number.

**What is STILL assumed, named precisely:** `SpongeKeyedROFaithful` for the one collision experiment
a given recursion step's forger induces (this is irreducible — Canetti–Goldreich–Halevi: no hash
function is unconditionally a random oracle), and P10 (the IPA/FRI opening-soundness floor,
`PicklesRecursion` §Z item 5, untouched and not attempted here). **Nothing else.** In particular:
`endo` injectivity is NO LONGER an assumption (§A), and the sponge-digest assumption is no longer an
unpriced "the hash is collision-resistant" — it is `SpongeKeyedROFaithful`, satisfiable, refutable in
its universal form, and priced at `pN ≈ 2^255`.

The honest sentence, updated from `PicklesFinalize` §Z: **the equality asserts pin what §P4.2 says
they pin (unconditional); `endo` injectivity is now a theorem, not a hypothesis; the sponge-digest
assumption is now ONE named, satisfiable, refutable, PRICED predicate instead of an unquantified
"collision-resistant"; and the IPA opening floor (P10) is the one genuinely irreducible residual
left.** Anything stronger than that sentence is over-claiming.

## §Y — Axiom hygiene. -/

#assert_axioms deltaOf_eq_one_or_neg_one
#assert_axioms epsOf_eq_one_or_neg_one
#assert_axioms deltaEps_injective
#assert_axioms foldl_signedBinary_range
#assert_axioms signedBinary_injective
#assert_axioms foldAB_gen
#assert_axioms foldAB_add_eq
#assert_axioms foldAB_sub_eq
#assert_axioms eq_of_map_delta_eps
#assert_axioms foldAB_injective_of_len_eq
#assert_axioms foldAB_range
#assert_axioms pairToNybble_injective
#assert_axioms bitsNybble_injective
#assert_axioms toNybbleList_length
#assert_axioms toNybbleList_injective
#assert_axioms glv_dvd
#assert_axioms glv_eisenstein_norm
#assert_axioms glv_coprime
#assert_axioms glvA_pos
#assert_axioms glvB_pos
#assert_axioms glvA_gt_bound
#assert_axioms glvB_gt_bound
#assert_axioms glv_margin
#assert_axioms glv_no_small_relation
#assert_axioms endoMap_injective_mod
#assert_axioms hash_singleton_ignores_mod_pN
#assert_axioms pN_pos
#assert_axioms hash_empty_eq_hash_zero
#assert_axioms RefHashInjective_false
#assert_axioms hashSepOn_mono
#assert_axioms hashSepOn_top_imp
#assert_axioms hashSepOn_top_false
#assert_axioms hashSepOn_bot
#assert_axioms hashSepOn_truncHashSep_false
#assert_axioms hashSepOn_modelHashSep
#assert_axioms modelHashSep_class_inhabited
#assert_axioms round_getD_lt_pN
#assert_axioms permFrom_getD_lt_pN
#assert_axioms perm_getD_lt_pN
#assert_axioms absorbFrom_getD_lt_pN
#assert_axioms hash_lt_pN
#assert_axioms digest_binds_transcript_on
#assert_axioms assertEqDigest_binds_transcript_on
#assert_axioms deployed_digest_collision_bound
#assert_axioms deployed_digest_noCollision

#assert_namespace_axioms Dregg2.Circuit.Emit.PicklesTranscriptBinding

end Dregg2.Circuit.Emit.PicklesTranscriptBinding
