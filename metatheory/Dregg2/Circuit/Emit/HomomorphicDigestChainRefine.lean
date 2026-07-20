/-
# Dregg2.Circuit.Emit.HomomorphicDigestChainRefine — whole-trace fold ⟹ the MODEL digest

THIS IS LEAN-AUTHORED METATHEORY over the Lean-emitted `dregg-homomorphic-digest-step-n4`
descriptor (`HomomorphicDigestEmit`). No Rust constraint is touched or mirrored here.

## What it closes

`HomomorphicDigestEmit.step_refines` is ONE fold step: a two-row window's constraints vanish
mod `p` IFF `dig' ≡ dig + A·enc` (field-faithful, `p = q = BabyBear`). The model
(`Dregg2.Crypto.HomomorphicDigest`) is the WHOLE history: `digest A encode S = A (∑ i ∈ S,
encode i)`. This file proves the missing middle — the CHAIN:

* `stepChain_final` — **the load-bearing induction.** For any row list whose every adjacent
  pair satisfies the per-step fold bundle (`foldStepHolds`, via `step_refines`), the FINAL
  row's digest ≡ the seed digest + `∑_t A·enc_t`, coordinate-wise mod `p`. A single wrong
  step severs the congruence chain (§6 teeth).
* `chain_refines` — **the descriptor-level keystone.** Any `VmTrace` satisfying the
  descriptor's row denotation (the `rowConstraints` leg of `Satisfied2`, which for THIS
  descriptor is the ENTIRE content: it declares no tables, hash sites, ranges, or mem/map
  ops) has `PI(final k) ≡ PI(initial k) + ∑_{t ∈ tail} A·enc_t [ZMOD p]` — the emitted
  fold's public final digest IS the accumulated history sum. The proof CONSUMES the
  last-row repair (`lastRepair`) exactly where the design predicted: the final folded row's
  `contrib` is pinned by the `.boundary .last` twin, not by the transition-guarded `.gate`.
* `satisfied2_chain_refines` — the same, from the full `Satisfied2` multi-table denotation.
* `chain_refines_model` — **the model keystone.** Casting into `ZMod q` (legitimate because
  `q` IS the AIR modulus), the final public digest vector EQUALS the initial one plus
  `HomomorphicDigest.digest Amod (histEncode tail) Finset.univ` — the model digest of the
  folded history, landed via `digest_eq_sum` with `A` as a genuine `→ₗ[ZMod q]` linear map.
  History is POSITION-INDEXED: `ι = Fin n` (the folded rows of this trace), `S = univ`.

## Honest scope (what this does NOT claim)

* **Turn identity.** `encode` here is "row `t`'s enc columns"; nothing identifies those
  witness columns with `encode(turn)` of real turns. That identification — and the binding
  story (`SumInjective` / `HomomorphicDigestPositioned`, the MSIS floor) — is the model
  files' and the producer's perimeter, per the witness-gen assurance perimeter: this file
  proves the TRACE relation, not the witness generator.
* `A` is the parent's POC placeholder matrix; `n = 4` POC width. Nothing cryptographic is
  claimed for it, and the `ShortNorm` instance below is a LOCAL zero-norm type-class shim
  (`digest_eq_sum` carries `[ShortNorm M]` as an unused section variable) — NO shortness or
  binding claim is made in this file.
* The bridge from deployed Rust prover bytes to `Satisfied2` (assembly binding, the
  FRI/STARK floor) is the standing perimeter, unchanged by this file.
* The trace-level COMPLETENESS face (an honest whole trace satisfies the row denotation) is
  not proved here; the window-level face is the parent's `step_accepts_correct`. This file's
  §6 proves the CHAIN-level completeness face concretely (a two-step honest chain).

## Axiom hygiene

`#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}` on every keystone. NEW file;
imports read-only.
-/
import Dregg2.Circuit.Emit.HomomorphicDigestEmit
import Dregg2.Crypto.HomomorphicDigest
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi

namespace Dregg2.Circuit.Emit.HomomorphicDigestChainRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.Emit.HomomorphicDigestEmit

set_option autoImplicit false

/-! ## §0 — The whole-trace step chain. -/

/-- The two-row window of an adjacent pair of main rows (`pub` rides along unchanged). -/
def windowOf (pub a b : Assignment) : VmRowEnv := { loc := a, nxt := b, pub := pub }

/-- The whole-trace fold chain, structurally: starting from accumulator row `prev`, every
adjacent row pair satisfies the per-step fold bundle `foldStepHolds` (the §3 bundle of
`HomomorphicDigestEmit`, i.e. exactly what `step_refines` characterizes). -/
def StepChain (pub : Assignment) : Assignment → List Assignment → Prop
  | _,    []      => True
  | prev, b :: bs => foldStepHolds (windowOf pub prev b) ∧ StepChain pub b bs

/-- The final accumulator row of a chain (`seed` if no rows were folded). -/
def lastRow (seed : Assignment) : List Assignment → Assignment
  | []      => seed
  | b :: bs => lastRow b bs

@[simp] theorem lastRow_nil (seed : Assignment) : lastRow seed [] = seed := rfl
@[simp] theorem lastRow_cons (seed b : Assignment) (bs : List Assignment) :
    lastRow seed (b :: bs) = lastRow b bs := rfl

/-! ## §1 — THE ARITHMETIC CHAIN: the load-bearing induction.

Per-step `dig' ≡ dig + A·enc` composes: the final digest is the seed digest plus the SUM of
per-row contributions. The induction consumes `step_refines` once per step; without the
per-step relation the congruence chain severs (§6 exhibits the severance concretely). -/

/-- **The arithmetic chain.** If every adjacent pair of `seed :: rest` satisfies the fold
step, the final digest coordinate ≡ seed coordinate + `∑_{r ∈ rest} (A·enc)(r)` mod `p`.
Induction over the folded rows, `step_refines` discharging each link. -/
theorem stepChain_final (pub : Assignment) :
    ∀ (rest : List Assignment) (seed : Assignment), StepChain pub seed rest →
      ∀ k, k < 4 →
        lastRow seed rest (digCol k)
          ≡ seed (digCol k) + (rest.map (dotRow k)).sum [ZMOD 2013265921]
  | [], seed, _, k, _ => by simp
  | b :: bs, seed, h, k, hk => by
      obtain ⟨hstep, hchain⟩ := h
      have hb : b (digCol k) ≡ seed (digCol k) + dotRow k b [ZMOD 2013265921] :=
        ((step_refines (windowOf pub seed b)).mp hstep k hk).2
      calc lastRow seed (b :: bs) (digCol k)
          = lastRow b bs (digCol k) := rfl
        _ ≡ b (digCol k) + (bs.map (dotRow k)).sum [ZMOD 2013265921] :=
            stepChain_final pub bs b hchain k hk
        _ ≡ (seed (digCol k) + dotRow k b) + (bs.map (dotRow k)).sum [ZMOD 2013265921] :=
            Int.ModEq.add_right _ hb
        _ = seed (digCol k) + ((b :: bs).map (dotRow k)).sum := by
            rw [List.map_cons, List.sum_cons]; ring

/-! ## §2 — Indexed windows ⟹ the chain (the shape the trace denotation hands us). -/

/-- Adjacent-window facts, indexed as the trace denotation indexes them (`getD`, total —
matching `envAt`), assemble into the structural chain. -/
theorem stepChain_of_windows (pub : Assignment) :
    ∀ (rest : List Assignment) (seed : Assignment),
      (∀ i, i + 1 < rest.length + 1 →
        foldStepHolds (windowOf pub ((seed :: rest).getD i zeroAsg)
          ((seed :: rest).getD (i + 1) zeroAsg))) →
      StepChain pub seed rest
  | [], _, _ => trivial
  | b :: bs, seed, h => by
      refine ⟨?_, stepChain_of_windows pub bs b fun i hi => ?_⟩
      · exact h 0 (by simp only [List.length_cons]; omega)
      · exact h (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)

/-- The final accumulator row, as the trace denotation indexes it. -/
theorem lastRow_eq_getD :
    ∀ (rest : List Assignment) (seed : Assignment),
      lastRow seed rest = (seed :: rest).getD rest.length zeroAsg
  | [], _ => rfl
  | b :: bs, seed => by
      simpa using lastRow_eq_getD bs b

/-! ## §3 — Descriptor membership + extraction from the row denotation. -/

/-- The row-constraints leg of `Satisfied2` for the fold-step descriptor — for THIS
descriptor the ENTIRE denotational content (it declares no tables, hash sites, ranges, or
mem/map ops, so every other `Satisfied2` leg is degenerate). -/
def RowSat (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ c ∈ homDigestStepDesc.constraints,
    c.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)

/-- `envAt` IS the adjacent-pair window (both read the same total `getD` slices). -/
theorem envAt_eq_windowOf (t : VmTrace) (i : Nat) :
    envAt t i = windowOf t.pub (t.rows.getD i zeroAsg) (t.rows.getD (i + 1) zeroAsg) := rfl

/-- The `A·enc` witness gate for coordinate `k < 4` is IN the descriptor. -/
theorem contribGate_mem (k : Nat) (hk : k < 4) :
    contribGate k ∈ homDigestStepDesc.constraints := by
  show contribGate k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hmem : contribGate k ∈ contribGates := by
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [contribGates]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ hmem)))

/-- The last-row repair for coordinate `k < 4` is IN the descriptor. -/
theorem lastRepair_mem (k : Nat) (hk : k < 4) :
    lastRepair k ∈ homDigestStepDesc.constraints := by
  show lastRepair k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hmem : lastRepair k ∈ lastRepairs := by
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [lastRepairs]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hmem))

/-- The initial-digest PI pin for coordinate `k < 4` is IN the descriptor. -/
theorem initialPin_mem (k : Nat) (hk : k < 4) :
    initialPin k ∈ homDigestStepDesc.constraints := by
  show initialPin k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hmem : initialPin k ∈ initialPins := by
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [initialPins]
  exact List.mem_append_left _ (List.mem_append_right _ hmem)

/-- The final-digest PI pin for coordinate `k < 4` is IN the descriptor. -/
theorem finalPin_mem (k : Nat) (hk : k < 4) :
    finalPin k ∈ homDigestStepDesc.constraints := by
  show finalPin k ∈ contribGates ++ accumGates ++ lastRepairs ++ initialPins ++ finalPins
  have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  have hmem : finalPin k ∈ finalPins := by
    rcases h4 with rfl | rfl | rfl | rfl <;> simp [finalPins]
  exact List.mem_append_right _ hmem

/-- A satisfying trace's accumulate bodies vanish on every TRANSITION window. -/
theorem rowSat_accumBody (hash : List ℤ → ℤ) (t : VmTrace) (hR : RowSat hash t)
    {i : Nat} (hi : i + 1 < t.rows.length) (k : Nat) (hk : k < 4) :
    (accumBody k).eval (envAt t i) ≡ 0 [ZMOD 2013265921] := by
  have hc := hR i (by omega) _ (accumGate_mem k hk)
  have hfl : (i + 1 == t.rows.length) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; omega
  rw [hfl] at hc
  simp only [accumGate, VmConstraint2.holdsAt, WindowConstraint.holdsAt] at hc
  exact hc trivial

/-- A satisfying trace's `A·enc` witness bodies vanish on EVERY row: on non-last rows via
the transition-guarded `.gate`, on the last row via the `.boundary .last` REPAIR — the
chain proof consumes the repair exactly where the parent's design note predicted. -/
theorem rowSat_contribBody (hash : List ℤ → ℤ) (t : VmTrace) (hR : RowSat hash t)
    {j : Nat} (hj : j < t.rows.length) (k : Nat) (hk : k < 4) :
    (contribBody k).eval (t.rows.getD j zeroAsg) ≡ 0 [ZMOD 2013265921] := by
  by_cases hlast : j + 1 = t.rows.length
  · have hc := hR j hj _ (lastRepair_mem k hk)
    have hfl : (j + 1 == t.rows.length) = true := by
      simp only [beq_iff_eq]; exact hlast
    rw [hfl] at hc
    simp only [lastRepair, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
    exact hc trivial
  · have hc := hR j hj _ (contribGate_mem k hk)
    have hfl : (j + 1 == t.rows.length) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; exact hlast
    rw [hfl] at hc
    simp only [contribGate, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
    exact hc

/-- A satisfying trace's FIRST-row digest is PI-pinned to the initial public digest. -/
theorem rowSat_initialPI (hash : List ℤ → ℤ) (t : VmTrace) (hR : RowSat hash t)
    (hne : t.rows ≠ []) (k : Nat) (hk : k < 4) :
    (t.rows.getD 0 zeroAsg) (digCol k) ≡ t.pub k [ZMOD 2013265921] := by
  have hlen : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hc := hR 0 hlen _ (initialPin_mem k hk)
  simp only [initialPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hc rfl

/-- A satisfying trace's LAST-row digest is PI-pinned to the final public digest. -/
theorem rowSat_finalPI (hash : List ℤ → ℤ) (t : VmTrace) (hR : RowSat hash t)
    (hne : t.rows ≠ []) (k : Nat) (hk : k < 4) :
    (t.rows.getD (t.rows.length - 1) zeroAsg) (digCol k) ≡ t.pub (4 + k) [ZMOD 2013265921] := by
  have hlen : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hc := hR (t.rows.length - 1) (by omega) _ (finalPin_mem k hk)
  have hfl : (t.rows.length - 1 + 1 == t.rows.length) = true := by
    simp only [beq_iff_eq]; omega
  rw [hfl] at hc
  simp only [finalPin, VmConstraint2.holdsAt, VmConstraint.holdsVm] at hc
  exact hc trivial

/-- The row denotation assembles into the structural step chain: every transition window
carries the four accumulate bodies (its own `windowGate`s) AND the folded row's four
`A·enc` bodies (that row's `.gate`, or the `.boundary .last` repair on the final row). -/
theorem rowSat_stepChain (hash : List ℤ → ℤ) (t : VmTrace) (hR : RowSat hash t)
    (seed : Assignment) (rest : List Assignment) (hrows : t.rows = seed :: rest) :
    StepChain t.pub seed rest := by
  apply stepChain_of_windows
  intro i hi
  have hi' : i + 1 < t.rows.length := by
    rw [hrows]; simp only [List.length_cons]; omega
  constructor
  · intro k hk
    have ha := rowSat_accumBody hash t hR hi' k hk
    rw [envAt_eq_windowOf, hrows] at ha
    exact ha
  · intro k hk
    have hcB := rowSat_contribBody hash t hR hi' k hk
    rw [hrows] at hcB
    exact hcB

/-! ## §4 — THE KEYSTONE: descriptor satisfaction ⟹ the accumulated-history digest. -/

/-- **THE CHAIN REFINEMENT (descriptor-level).** Any trace satisfying the fold-step
descriptor's row denotation has, coordinate-wise mod `p` (`p = q = BabyBear`, so this IS
the spec-level statement):

    PI(final k)  ≡  PI(initial k) + ∑_{r ∈ rows.tail} (A·enc)(r)

— the emitted fold's public FINAL digest is the public INITIAL digest plus the model sum
over the whole folded history (row 0 is the seed; each subsequent row folds one turn). -/
theorem chain_refines (hash : List ℤ → ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hR : RowSat hash t) (k : Nat) (hk : k < 4) :
    t.pub (4 + k) ≡ t.pub k + (t.rows.tail.map (dotRow k)).sum [ZMOD 2013265921] := by
  obtain ⟨seed, rest, hrows⟩ := List.exists_cons_of_ne_nil hne
  have harith := stepChain_final t.pub rest seed
    (rowSat_stepChain hash t hR seed rest hrows) k hk
  have hinit := rowSat_initialPI hash t hR hne k hk
  have hfin := rowSat_finalPI hash t hR hne k hk
  rw [hrows] at hinit hfin ⊢
  have hlast : (seed :: rest).getD ((seed :: rest).length - 1) zeroAsg = lastRow seed rest := by
    simpa using (lastRow_eq_getD rest seed).symm
  rw [hlast] at hfin
  show t.pub (4 + k) ≡ t.pub k + (rest.map (dotRow k)).sum [ZMOD 2013265921]
  calc t.pub (4 + k)
      ≡ lastRow seed rest (digCol k) [ZMOD 2013265921] := hfin.symm
    _ ≡ seed (digCol k) + (rest.map (dotRow k)).sum [ZMOD 2013265921] := harith
    _ ≡ t.pub k + (rest.map (dotRow k)).sum [ZMOD 2013265921] :=
        Int.ModEq.add_right _ hinit

/-- The keystone from the FULL `Satisfied2` multi-table denotation (its row leg is `RowSat`;
its remaining legs are degenerate for this descriptor — no tables/hash sites/ranges/mem/map
ops are declared). -/
theorem satisfied2_chain_refines (hash : List ℤ → ℤ) (minit : ℤ → ℤ) (mfin : ℤ → ℤ × Nat)
    (maddrs : List ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hs : Satisfied2 hash homDigestStepDesc minit mfin maddrs t) (k : Nat) (hk : k < 4) :
    t.pub (4 + k) ≡ t.pub k + (t.rows.tail.map (dotRow k)).sum [ZMOD 2013265921] :=
  chain_refines hash t hne hs.rowConstraints k hk

/-! ## §5 — The MODEL bridge: the chain's RHS IS `HomomorphicDigest.digest` over `ZMod q`.

`q = BabyBear` is the AIR's field modulus, so casting the mod-`p` congruence into `ZMod q`
is the faithful reading, not a weakening. The history is POSITION-INDEXED: `ι = Fin n`
(the folded rows of this trace), `S = Finset.univ`, `encode i` = row `i`'s enc columns. -/

/-- The deployed modulus, as the model field's characteristic. -/
abbrev Qb : ℕ := 2013265921

/-- LOCAL type-class shim: `digest_eq_sum` carries `[ShortNorm M]` as an (unused) section
variable, so instantiating it needs SOME instance. The zero norm satisfies the axioms; the
norm plays NO role in the fold algebra, and NO shortness/binding claim is made in this
file (the real norms live with the binding story in `HomomorphicDigestPositioned`). -/
local instance : Dregg2.Crypto.Lattice.ShortNorm (Fin 4 → ZMod Qb) :=
  ⟨fun _ => 0, rfl, fun _ => rfl, fun _ _ => Nat.le_refl 0⟩

/-- The POC matrix entry, cast into the model field. -/
noncomputable def aZ (k : Fin 4) (j : Nat) : ZMod Qb := ((A k.val j : ℤ) : ZMod Qb)

/-- The POC matrix `A` as a genuine LINEAR MAP on the model's message module — the model's
`A : M →ₗ[Rq] N` for this descriptor (`M = N = Fin 4 → ZMod q`, `Rq = ZMod q`). -/
noncomputable def Amod : (Fin 4 → ZMod Qb) →ₗ[ZMod Qb] (Fin 4 → ZMod Qb) where
  toFun := fun v k => aZ k 0 * v 0 + aZ k 1 * v 1 + aZ k 2 * v 2 + aZ k 3 * v 3
  map_add' := by
    intro x y; funext k; simp only [Pi.add_apply]; ring
  map_smul' := by
    intro c v; funext k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- A row's enc columns as a model message-module element. -/
noncomputable def encVec (r : Assignment) : Fin 4 → ZMod Qb :=
  fun j => ((r (encCol j.val) : ℤ) : ZMod Qb)

/-- The linear map agrees with the emitted dot product, coordinate-wise: `Amod (encVec r) k`
IS the cast of `dotRow k r`. This is the join pin between the AIR's `Σ_j A k j · enc[j]`
and the model's `A (encode i)`. -/
theorem Amod_encVec (r : Assignment) (k : Fin 4) :
    Amod (encVec r) k = ((dotRow k.val r : ℤ) : ZMod Qb) := by
  simp only [Amod, LinearMap.coe_mk, AddHom.coe_mk, encVec, dotRow, aZ]
  push_cast
  norm_num

/-- Casting a list sum into the field distributes (self-contained; no name drift). -/
theorem cast_listSum (l : List ℤ) :
    ((l.sum : ℤ) : ZMod Qb) = (l.map (fun z : ℤ => (z : ZMod Qb))).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- A `Fin`-indexed sum over a list's rows IS the list sum of the mapped rows. -/
theorem sum_fin_getD {M : Type} [AddCommMonoid M] (f : Assignment → M) :
    ∀ (rows : List Assignment),
      (∑ i : Fin rows.length, f (rows.getD i.val zeroAsg)) = (rows.map f).sum
  | [] => by simp
  | b :: bs => by
      show (∑ i : Fin (bs.length + 1), f ((b :: bs).getD i.val zeroAsg))
        = ((b :: bs).map f).sum
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
        sum_fin_getD f bs, List.map_cons, List.sum_cons]

/-- The folded history of a row list, position-indexed for the model: position `i`'s
encode vector is row `i`'s enc columns. -/
noncomputable def histEncode (rows : List Assignment) : Fin rows.length → (Fin 4 → ZMod Qb) :=
  fun i => encVec (rows.getD i.val zeroAsg)

/-- **The model digest IS the chain's sum.** `HomomorphicDigest.digest` of the position-
indexed history (via the model's own `digest_eq_sum`) equals the cast of
`∑_{r ∈ rows} dotRow k r` — the exact RHS `chain_refines` produces. -/
theorem digest_hist (rows : List Assignment) (k : Fin 4) :
    Dregg2.Crypto.HomomorphicDigest.digest Amod (histEncode rows) Finset.univ k
      = (((rows.map (dotRow k.val)).sum : ℤ) : ZMod Qb) := by
  rw [Dregg2.Crypto.HomomorphicDigest.digest_eq_sum, Finset.sum_apply, cast_listSum,
    List.map_map, ← sum_fin_getD]
  exact Finset.sum_congr rfl fun i _ => Amod_encVec _ k

/-- **THE MODEL KEYSTONE.** For any trace satisfying the fold-step descriptor's row
denotation: over the deployed field `ZMod q`, the FINAL public digest vector equals the
INITIAL public digest vector plus the MODEL `digest` of the folded history — the emitted
fold's final digest IS `HomomorphicDigest.digest` accumulated over the history. -/
theorem chain_refines_model (hash : List ℤ → ℤ) (t : VmTrace) (hne : t.rows ≠ [])
    (hR : RowSat hash t) :
    (fun k : Fin 4 => ((t.pub (4 + k.val) : ℤ) : ZMod Qb))
      = (fun k : Fin 4 => ((t.pub k.val : ℤ) : ZMod Qb))
        + Dregg2.Crypto.HomomorphicDigest.digest Amod (histEncode t.rows.tail)
            Finset.univ := by
  funext k
  have h := chain_refines hash t hne hR k.val k.isLt
  have hcast : ((t.pub (4 + k.val) : ℤ) : ZMod Qb)
      = (((t.pub k.val + (t.rows.tail.map (dotRow k.val)).sum : ℤ)) : ZMod Qb) := by
    rw [ZMod.intCast_eq_intCast_iff]
    simpa using h
  simp only [Pi.add_apply, digest_hist]
  rw [hcast]
  push_cast
  ring

/-! ## §6 — TEETH: the per-step relation is load-bearing, in both directions.

The tampered pair (`badNxt` forges `dig'₀: 110 → 111`, the parent's §5 witness) breaks the
chain HYPOTHESIS *and* the chain CONCLUSION — the induction genuinely rides on
`step_refines`, and an honest two-step trace chains through. -/

/-- A single tampered step SEVERS the chain: the forged window fails `StepChain`. -/
theorem tampered_pair_breaks_chain :
    ¬ StepChain (fun _ => 0) okLoc [badNxt] := by
  rintro ⟨hstep, -⟩
  exact absurd (hstep.1 0 (by omega)) (by decide)

/-- ...and the tampered trace's final digest genuinely DISAGREES with the model sum in the
field — the chain conclusion is false for it, not merely unproven. -/
theorem tampered_final_breaks_equation :
    ¬ (badNxt (digCol 0) ≡ okLoc (digCol 0) + dotRow 0 badNxt [ZMOD 2013265921]) := by
  decide

/-- Third honest row: digest `(120, 252, 384, 516)` (the §5 honest step applied AGAIN:
`enc = (1,1,1,1)`, contributions `(10,26,42,58)`). -/
def okThird : Assignment := fun i =>
  if i = 0 then 120 else if i = 1 then 252 else if i = 2 then 384 else if i = 3 then 516
  else if i = 4 then 1 else if i = 5 then 1 else if i = 6 then 1 else if i = 7 then 1
  else if i = 8 then 10 else if i = 9 then 26 else if i = 10 then 42 else if i = 11 then 58
  else 0

/-- COMPLETENESS face at chain level: the honest TWO-step trace chains — the multi-step
induction is exercised on a concrete trace, not only on single windows. -/
theorem honest_two_step_chain :
    StepChain (fun _ => 0) okLoc [okNxt, okThird] := by
  refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩, trivial⟩
  all_goals
    have h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases h4 with rfl | rfl | rfl | rfl <;> decide

/-- Non-vacuity of the chain theorem ITSELF: instantiated on the honest two-step trace, the
final digest is the seed plus the two-turn history sum (`120 = 100 + 10 + 10` at k = 0). -/
example : okThird (digCol 0) ≡ okLoc (digCol 0)
    + ([okNxt, okThird].map (dotRow 0)).sum [ZMOD 2013265921] :=
  stepChain_final (fun _ => 0) [okNxt, okThird] okLoc honest_two_step_chain 0 (by omega)

-- Concrete field-level pins (parent-style `#guard`, both coordinates of the story).
#guard decide (okThird (digCol 0)
  ≡ okLoc (digCol 0) + dotRow 0 okNxt + dotRow 0 okThird [ZMOD 2013265921])
#guard decide (okThird (digCol 3)
  ≡ okLoc (digCol 3) + dotRow 3 okNxt + dotRow 3 okThird [ZMOD 2013265921])
#guard decide (¬ (badNxt (digCol 0) ≡ okLoc (digCol 0) + dotRow 0 badNxt [ZMOD 2013265921]))

/-! ## §7 — Axiom hygiene. -/

#assert_axioms stepChain_final
#assert_axioms stepChain_of_windows
#assert_axioms lastRow_eq_getD
#assert_axioms contribGate_mem
#assert_axioms lastRepair_mem
#assert_axioms initialPin_mem
#assert_axioms finalPin_mem
#assert_axioms rowSat_accumBody
#assert_axioms rowSat_contribBody
#assert_axioms rowSat_initialPI
#assert_axioms rowSat_finalPI
#assert_axioms rowSat_stepChain
#assert_axioms chain_refines
#assert_axioms satisfied2_chain_refines
#assert_axioms Amod_encVec
#assert_axioms digest_hist
#assert_axioms chain_refines_model
#assert_axioms tampered_pair_breaks_chain
#assert_axioms tampered_final_breaks_equation
#assert_axioms honest_two_step_chain

end Dregg2.Circuit.Emit.HomomorphicDigestChainRefine
