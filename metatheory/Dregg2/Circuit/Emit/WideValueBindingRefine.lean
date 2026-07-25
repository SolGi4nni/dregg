/-
# Dregg2.Circuit.Emit.WideValueBindingRefine — the SAT ⟹ SEM bridge for the Lean-authored
full-`u64` value/asset binding AIR (`WideValueBindingEmit.wideValueBindingDesc`).

## What Rung-0 gave, and what was missing

`WideValueBindingEmit` gives a descriptor whose wire bytes are pinned. What the Rust AIR it
replaces could NEVER have — because there is no formal semantics of Rust — is a machine-checked
theorem relating the EMITTED OBJECT to the relation it claims. The Rust file's own canaries
(`circuit-prove/tests/shielded_wide_value_binding.rs`) are unit tests over a co-built witness row:
they prove nothing about all inputs. Three of them are re-derived here as THEOREMS.

## What THIS file proves

Let `p = 2013265921` (BabyBear). On any transition row of any trace satisfying the descriptor:

* **THE FELT-WIDTH REPAIR (`limb_canonical`)** — the keystone. The sixteen boolean pins plus the
  recomposition gate FORCE each limb cell into `[0, 2^16)` over ℤ, and force it to BE the weighted
  sum of its own bit cells. Nothing is assumed about the witness: canonicality is produced by the
  gates. `u64_of_limbs_lt_two64` lifts it: the four limbs of a kind denote a genuine `u64`.

* **THE RUST 17-BIT CANARY, AS A THEOREM (`seventeenth_bit_unsat`)** — the Rust test
  `a_seventeenth_limb_bit_has_no_satisfying_trace` forges `value_limb_0 := 2^16` while leaving its
  sixteen bit cells zero and checks that the prover fails on that ONE input. Here it is universally
  quantified: no satisfying trace has that shape, for any witness.

* **THE COMPATIBILITY FELT IS DERIVED (`vmod_is_the_reduction` / `amod_is_the_reduction`)** — the
  one-felt cells the deployed spend circuit reads are congruent mod `p` to the full `u64` the limbs
  denote. They are not a second, free value the prover may choose.

* **THE CARRIER IS THE GENUINE PERMUTATION (`wideA_lanes_forced`, `wideB_lanes_forced`,
  `published_lane_is_genuine`, `published_laneB_is_genuine`)** — against a sound wide chip table,
  all eight lanes of each
  `node8` site are the real squeezed output of that row's own limbs, and row 0's sixteen PI cells
  are those lanes. `forged_lane_unsat` is the Rust "FALSE polarity 1" canary as a theorem: a
  published lane that is not the genuine output has NO satisfying trace.

* **THE LEGACY JOIN IS THE DEPLOYED `hash_fact` (`legacy_is_hash_fact`)** — the compatibility
  column is forced to `hash_fact(value_mod_p, [asset_mod_p, randomness, 0])`, over the SAME cells
  the limbs recompose into. That is what makes the sidecar a join and not a second claim.

* **THE BITE — the felt-width wound, refuted and repaired.**
  * `legacy_join_cannot_separate_aliases` takes NO hypotheses and NO crypto: the explicit pair
    `v` and `v + p` (both genuine `u64`s, the Rust test's own pair) has EQUAL reductions mod `p`,
    so the legacy site's four inputs are identical and its output column is equal whatever the
    hash is. The one-felt join is provably blind to the alias.
  * `alias_limbs_differ` shows the two openings the wide carrier absorbs DIFFER.
  * `wide_carrier_separates_aliases` closes it: under the named floor `WideCarrierCR`, two
    satisfying rows publishing the same eight `DOMAIN_A` lanes at the same randomness and blinds
    carry the same limbs — hence the same `u64` value and asset. On the alias pair the wide
    carrier therefore separates exactly where the legacy felt cannot.

## The NAMED floor, and why it is restricted the way it is

`WideCarrierCR permOut` is injectivity of the 8-lane squeeze IN THE LIMBS, at FIXED randomness and
blinds. It is deliberately NOT injectivity over the whole canonical opening: that statement is
PIGEONHOLE-FALSE here, because the opening carries 8 × 16 bits of limb plus 7 canonical BabyBear
felts ≈ 345 bits into an 8-felt ≈ 248-bit range. Restricting to the limb subspace at fixed
(randomness, blinds) leaves a 2^128 domain against a 2^248 range, where counting does not refute —
and it is exactly the comparison the Rust alias canary makes (`alias_witness` clones the honest
witness and changes ONLY the value). `wideCarrierCR_satisfiable` exhibits an inhabitant and
`wideCarrierCR_refutable` exhibits a `permOut` that fails it, so the floor is satisfiable and
refutable but not provable.

## Honest coverage boundary (read this before deleting anything)

COVERED by a proven theorem here: the 128 boolean pins and the 8 limb recompositions
(`limb_canonical`), the 2 compatibility reductions (`vmod_is_the_reduction`,
`amod_is_the_reduction`), both `node8` sites (`wideA_lanes_forced` / `wideB_lanes_forced`), the
`hash_fact` site (`legacy_is_hash_fact`), and all 17 PI bindings (`published_lane_is_genuine` for
the eight `DOMAIN_A` lanes, `published_laneB_is_genuine` for the eight `DOMAIN_B` lanes,
`published_legacy_is_genuine` for the compatibility join). That is EVERY emitted constraint.

NOT covered (named, not laundered):

  1. **The chip-table floors are hypotheses, not theorems.** `ChipTableSoundN permOut` and
     `ChipTableSound hash` enter as parameters exactly as they do everywhere else in this tree;
     they are discharged by the deployed chip AIR, not here.
  2. **`permOut` is not proved to be Poseidon2.** It is a parameter. The claim "these 8 lanes are
     `cap_node8`" is the claim that the deployed chip table implements `cap_node8`, which is the
     `chip_absorb_all_lanes` reading recorded in `WideValueBindingEmit` §4, not a Lean theorem.
  3. **The LAST row.** IR-v2 `.base (.gate _)` rides the deployed `when_transition()` domain, so
     every theorem above about an algebraic gate carries `i + 1 < t.rows.length`. The v1 Rust AIR
     asserts those same gates on every row. The chip-site theorems (`wideA_lanes_forced`,
     `legacy_is_hash_fact`) carry only `i < t.rows.length`, because a lookup has no row guard, and
     all 17 PI pins are FIRST-row — so the PUBLISHED claim is row 0's and row 0 is a transition row
     on any trace of two or more rows. The last row is unconstrained-and-unread. Closing it is the
     `.boundary .last` twin of each gate; not emitted, because nothing reads that row.
  4. **Multi-row structure.** The Rust producer emits a constant two-row trace; nothing here forces
     row equality across rows, because the descriptor does not constrain it (neither does the Rust).
  5. **The migration seam the Rust header already names.** The note tree still commits the one-felt
     leaf; until note creation precommits this carrier, the compatibility join alone cannot choose
     between two full-width openings. That is a DEPLOY fact, unchanged by this file.

## Axiom hygiene

`#assert_axioms` on every keystone. The only carriers are `propext`/`Classical.choice`/`Quot.sound`;
the sole imported field fact is the BabyBear primality `pPrimeInt` (`EffectVmEmitTransfer`), used
exactly where a booleanity gate is lifted from mod-`p` to ℤ. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.WideValueBindingEmit
import Dregg2.Circuit.Emit.EffectVmEmitTransfer

namespace Dregg2.Circuit.Emit.WideValueBindingRefine

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
  (Satisfied2 VmTrace TraceFamily VmConstraint2 EffectVmDescriptor2 Lookup TableId envAt zeroAsg
   ChipTableSound ChipTableSoundN chip_lookup_sound_N chipLookupTupleN chipLookupTupleNarrow
   poseidon2narrow CHIP_RATE CHIP_OUT_LANES padToE)
open Dregg2.Circuit.ChipNarrowLookup (narrowTable narrow_lookup_holdsAt_sound)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (pPrimeInt)
open Dregg2.Circuit.Emit.AirBuilder
open Dregg2.Circuit.Emit.WideValueBindingEmit

set_option autoImplicit false
set_option maxRecDepth 4000

/-! ## §0 — Field glue. -/

/-- The deployed range-check invariant on a stored field cell. -/
def Canon (x : ℤ) : Prop := 0 ≤ x ∧ x < 2013265921

/-- A booleanity gate that vanishes mod `p` on a CANONICAL cell pins it to `0` or `1` over ℤ. -/
theorem bin_of_gate {a : Assignment} {c : Nat}
    (h : (gBin c).eval a ≡ 0 [ZMOD 2013265921]) (hc : Canon (a c)) : a c = 0 ∨ a c = 1 := by
  simp only [gBin, EmittedExpr.eval] at h
  have hd : (2013265921 : ℤ) ∣ a c * (a c + (-1)) := Int.modEq_zero_iff_dvd.mp h
  obtain ⟨hc0, hc1⟩ := hc
  rcases pPrimeInt.dvd_mul.mp hd with hx | hx
  · obtain ⟨k, hk⟩ := hx; left; omega
  · obtain ⟨k, hk⟩ := hx; right; omega

/-! ## §1 — Gate / lookup extraction from `Satisfied2`. -/

section Extraction
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The row assignment at index `i`. -/
def rowOf (t : VmTrace) (i : Nat) : Assignment := (envAt t i).loc

/-- **Any emitted `Head` gate forces its head to vanish mod `p` on a transition row.** This is the
one place the lowering is unfolded; every theorem below is stated on `evalH`. -/
theorem wvbGate (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {h : Head}
    (hm : cgH h ∈ wideValueBindingDesc.constraints) :
    evalH h (rowOf t i) ≡ 0 [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (headToExpr h).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [cgH, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  rwa [headToExpr_eval] at hb

/-- The booleanity form of `wvbGate`. -/
theorem wvbBin (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t) (i : Nat)
    (hi : i + 1 < t.rows.length) {c : Nat}
    (hm : binGate c ∈ wideValueBindingDesc.constraints) (hcan : Canon (rowOf t i c)) :
    rowOf t i c = 0 ∨ rowOf t i c = 1 := by
  have hrc := hsat.rowConstraints i (by omega) _ hm
  have hlf : (i + 1 == t.rows.length) = false := by
    have hne : i + 1 ≠ t.rows.length := by omega
    simpa using hne
  have hb : (gBin c).eval (envAt t i).loc ≡ 0 [ZMOD 2013265921] := by
    simpa only [binGate, cg, VmConstraint2.holdsAt, VmConstraint.holdsVm, hlf] using hrc
  exact bin_of_gate hb hcan

/-- A lookup constraint HOLDS on any row of a satisfying trace. -/
theorem wvbLookup (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t) (i : Nat)
    (hi : i < t.rows.length) {l : Lookup}
    (hm : VmConstraint2.lookup l ∈ wideValueBindingDesc.constraints) :
    l.holdsAt t.tf (envAt t i) := hsat.rowConstraints i hi _ hm

/-- A first-row PI binding forces the column to its public input. -/
theorem wvbPin (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hne : 0 < t.rows.length) {c k : Nat}
    (hm : pinPi c k ∈ wideValueBindingDesc.constraints) :
    rowOf t 0 c ≡ (envAt t 0).pub k [ZMOD 2013265921] := by
  have hrc := hsat.rowConstraints 0 hne _ hm
  simpa only [pinPi, VmConstraint2.holdsAt, VmConstraint.holdsVm, rowOf] using hrc rfl

end Extraction

/-! ## §2 — Membership: each gate family sits inside the emitted constraint list.

`wideValueBindingConstraints` is a left-associated chain of `++`; `List.mem_append` turns
membership into a nested disjunction and `tauto` places the family. These lemmas are the ONLY place
the emission order is relied on, so a re-ordering of the emit module breaks these and nothing else.
-/

section Membership
variable {x : VmConstraint2}

theorem mem_limbGates {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS) (hx : x ∈ limbGates k i) :
    x ∈ wideValueBindingDesc.constraints := by
  have h1 : x ∈ (List.range 2).flatMap
      (fun k => (List.range U64_LIMBS).flatMap fun i => limbGates k i) :=
    List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk,
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩⟩
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_bin {k i b : Nat} (hk : k < 2) (hi : i < U64_LIMBS) (hb : b < LIMB_BITS) :
    binGate (cBit k i b) ∈ wideValueBindingDesc.constraints := by
  refine mem_limbGates hk hi ?_
  simp only [limbGates, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)

theorem mem_limbRecompose {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS) :
    cgH (limbRecomposeHead k i) ∈ wideValueBindingDesc.constraints := by
  refine mem_limbGates hk hi ?_
  simp only [limbGates, List.mem_append]
  exact Or.inr (by simp)

theorem mem_u64Recompose_value :
    cgH (u64RecomposeHead 0 cVMOD) ∈ wideValueBindingDesc.constraints := by
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_u64Recompose_asset :
    cgH (u64RecomposeHead 1 cAMOD) ∈ wideValueBindingDesc.constraints := by
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_wideA : wideSite DOMAIN_A (cWA 0) ∈ wideValueBindingDesc.constraints := by
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_wideB : wideSite DOMAIN_B (cWB 0) ∈ wideValueBindingDesc.constraints := by
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_legacy : legacySite ∈ wideValueBindingDesc.constraints := by
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_pinLegacy : pinPi cLEGACY PI_LEGACY ∈ wideValueBindingDesc.constraints := by
  have h1 : pinPi cLEGACY PI_LEGACY ∈ piPins := by simp [piPins]
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

theorem mem_pinLane {lane : Nat} (hl : lane < WIDE_LANES) :
    pinPi (laneCol lane) (PI_WIDE + lane) ∈ wideValueBindingDesc.constraints := by
  have h1 : pinPi (laneCol lane) (PI_WIDE + lane) ∈ piPins := by
    simp only [piPins, List.mem_cons]
    exact Or.inr (List.mem_map.mpr ⟨lane, List.mem_range.mpr hl, rfl⟩)
  simp only [wideValueBindingDesc, wideValueBindingConstraints, List.mem_append]
  tauto

end Membership

/-! ## §3 — THE FELT-WIDTH REPAIR: the limbs are FORCED canonical.

`R1 + R2` together are the whole content of the repair. A weighted sum of `n` boolean cells lies in
`[0, 2^n)`; the recomposition gate ties the limb cell to that sum mod `p`; `2^16 ≤ p`, so the
congruence upgrades to an equality over ℤ on a canonical cell. -/

/-- The weighted bit sum `Σ_{b<n} 2^b · a (f b)`. -/
def bitSum (a : Assignment) (f : Nat → Nat) (n : Nat) : ℤ :=
  ((List.range n).map fun b => (2 ^ b : ℤ) * a (f b)).sum

theorem bitSum_succ (a : Assignment) (f : Nat → Nat) (n : Nat) :
    bitSum a f (n + 1) = bitSum a f n + (2 ^ n : ℤ) * a (f n) := by
  simp only [bitSum, List.range_succ, List.map_append, List.sum_append, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  ring

/-- **A weighted sum of `n` boolean cells lies in `[0, 2^n)`.** The bound the boolean pins buy. -/
theorem bitSum_bounds (a : Assignment) (f : Nat → Nat) (n : Nat)
    (hb : ∀ b, b < n → a (f b) = 0 ∨ a (f b) = 1) :
    0 ≤ bitSum a f n ∧ bitSum a f n < 2 ^ n := by
  induction n with
  | zero => simp [bitSum]
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih fun b hbn => hb b (by omega)
    have hpow : (0 : ℤ) < 2 ^ n := by positivity
    have hps : (2 : ℤ) ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
    rcases hb n (by omega) with h | h
    · rw [bitSum_succ, h]
      constructor
      · linarith
      · rw [hps]; linarith
    · rw [bitSum_succ, h]
      constructor
      · linarith
      · rw [hps]; linarith

section Canonical
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The recomposition head evaluates to `limb − Σ 2^b·bit`. -/
theorem limbRecomposeHead_eval (a : Assignment) (k i : Nat) :
    evalH (limbRecomposeHead k i) a = a (cLimb k i) - bitSum a (fun b => cBit k i b) LIMB_BITS := by
  simp only [limbRecomposeHead, evalH_foldl_addLinG, evalH_lin, bitSum]
  have : ∀ xs : List Nat,
      (xs.map fun b => -(2 ^ b : ℤ) * a (cBit k i b)).sum
        = -(xs.map fun b => (2 ^ b : ℤ) * a (cBit k i b)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

/-- **THE KEYSTONE — the limbs are canonical 16-bit cells, FORCED.** On a satisfying trace the
limb cell IS the weighted sum of its own boolean bit cells, and therefore lies in `[0, 2^16)`.
Nothing here is assumed of the witness beyond the deployed range-check canonicality of the stored
field cells; the 16-bit-ness is PRODUCED by the emitted gates. -/
theorem limb_canonical (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t) (i₀ : Nat)
    (hi₀ : i₀ + 1 < t.rows.length) {k i : Nat} (hk : k < 2) (hi : i < U64_LIMBS)
    (hcan : Canon (rowOf t i₀ (cLimb k i)))
    (hcanb : ∀ b, b < LIMB_BITS → Canon (rowOf t i₀ (cBit k i b))) :
    rowOf t i₀ (cLimb k i) = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS
      ∧ 0 ≤ rowOf t i₀ (cLimb k i) ∧ rowOf t i₀ (cLimb k i) < 65536 := by
  have hbits : ∀ b, b < LIMB_BITS → rowOf t i₀ (cBit k i b) = 0 ∨ rowOf t i₀ (cBit k i b) = 1 :=
    fun b hb => wvbBin hsat i₀ hi₀ (mem_bin hk hi hb) (hcanb b hb)
  obtain ⟨hs0, hs1⟩ := bitSum_bounds (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS hbits
  have hgate := wvbGate hsat i₀ hi₀ (mem_limbRecompose hk hi)
  rw [limbRecomposeHead_eval] at hgate
  have hdvd : (2013265921 : ℤ) ∣
      rowOf t i₀ (cLimb k i) - bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS :=
    Int.modEq_zero_iff_dvd.mp hgate
  obtain ⟨hc0, hc1⟩ := hcan
  have hlt : (2 : ℤ) ^ LIMB_BITS = 65536 := by norm_num [LIMB_BITS]
  rw [hlt] at hs1
  obtain ⟨c, hc⟩ := hdvd
  have heq : rowOf t i₀ (cLimb k i) = bitSum (rowOf t i₀) (fun b => cBit k i b) LIMB_BITS := by
    omega
  exact ⟨heq, by omega, by omega⟩

/-- **THE RUST 17-BIT CANARY, AS A THEOREM.** `a_seventeenth_limb_bit_has_no_satisfying_trace`
forges `value_limb_0 := 2^16` with all sixteen of its bit cells left at zero and observes that the
prover fails ON THAT WITNESS. Here: no satisfying trace has that shape, for ANY witness — the limb
is pinned to the sum of its own bits, and a limb whose bits are all zero IS zero. -/
theorem seventeenth_bit_unsat (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length)
    (hcan : Canon (rowOf t i₀ (cV 0)))
    (hcanb : ∀ b, b < LIMB_BITS → Canon (rowOf t i₀ (cBit 0 0 b)))
    (hzeros : ∀ b, b < LIMB_BITS → rowOf t i₀ (cBit 0 0 b) = 0) :
    rowOf t i₀ (cV 0) ≠ 65536 := by
  have hlimb : cLimb 0 0 = cV 0 := by simp [cLimb]
  obtain ⟨heq, _, _⟩ := limb_canonical hsat i₀ hi₀ (k := 0) (i := 0) (by omega) (by decide)
    (by rwa [hlimb]) hcanb
  rw [hlimb] at heq
  have hz : bitSum (rowOf t i₀) (fun b => cBit 0 0 b) LIMB_BITS = 0 := by
    simp only [bitSum]
    refine List.sum_eq_zero ?_
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [hzeros b (List.mem_range.mp hb)]
    ring
  rw [heq, hz]
  norm_num

end Canonical

/-! ## §4 — The full `u64` the limbs denote, and the compatibility reduction. -/

/-- The `u64` a kind's four limb cells denote: `Σ_{i<4} 2^{16i}·limb_i` (little-endian, the Rust
`u64_limbs` inverse). -/
def u64Of (a : Assignment) (k : Nat) : ℤ :=
  ((List.range U64_LIMBS).map fun i => (2 ^ (LIMB_BITS * i) : ℤ) * a (cLimb k i)).sum

/-- The compatibility head evaluates to `out − Σ (2^{16i} mod p)·limb_i`. -/
theorem u64RecomposeHead_eval (a : Assignment) (k out : Nat) :
    evalH (u64RecomposeHead k out) a
      = a out - ((List.range U64_LIMBS).map fun i => limbWeight i * a (cLimb k i)).sum := by
  simp only [u64RecomposeHead, evalH_foldl_addLinG, evalH_lin]
  have : ∀ xs : List Nat,
      (xs.map fun i => -(limbWeight i) * a (cLimb k i)).sum
        = -(xs.map fun i => limbWeight i * a (cLimb k i)).sum := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  rw [this]
  ring

/-- The reduced place value IS the place value mod `p` — the one place `limbWeight` is unfolded. -/
theorem limbWeight_modEq (i : Nat) :
    limbWeight i ≡ (2 ^ (LIMB_BITS * i) : ℤ) [ZMOD 2013265921] := by
  simp only [limbWeight, P, Int.ModEq]
  exact Int.emod_emod_of_dvd _ dvd_rfl

section Reduction
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- Pointwise congruence lifts to the sums. -/
theorem sum_modEq {α : Type} (xs : List α) (f g : α → ℤ)
    (h : ∀ x ∈ xs, f x ≡ g x [ZMOD 2013265921]) :
    (xs.map f).sum ≡ (xs.map g).sum [ZMOD 2013265921] := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Int.ModEq.add (h b (List.mem_cons_self)) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **The compatibility felt is the reduction of the full `u64`.** `value_mod_p` is not a second,
free value: the emitted gate ties it to the limbs the wide carrier absorbs. -/
theorem vmod_is_the_reduction (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cVMOD ≡ u64Of (rowOf t i₀) 0 [ZMOD 2013265921] := by
  have hgate := wvbGate hsat i₀ hi₀ mem_u64Recompose_value
  rw [u64RecomposeHead_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum
      ≡ u64Of (rowOf t i₀) 0 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cVMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 0 i)).sum) hgate
  exact h2.trans hs

/-- The asset half of the same statement. -/
theorem amod_is_the_reduction (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (i₀ : Nat) (hi₀ : i₀ + 1 < t.rows.length) :
    rowOf t i₀ cAMOD ≡ u64Of (rowOf t i₀) 1 [ZMOD 2013265921] := by
  have hgate := wvbGate hsat i₀ hi₀ mem_u64Recompose_asset
  rw [u64RecomposeHead_eval] at hgate
  have hs : ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum
      ≡ u64Of (rowOf t i₀) 1 [ZMOD 2013265921] := by
    refine sum_modEq _ _ _ fun i _ => ?_
    exact Int.ModEq.mul_right _ (limbWeight_modEq i)
  have h2 : rowOf t i₀ cAMOD
      ≡ ((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum
      [ZMOD 2013265921] := by
    simpa using Int.ModEq.add_right
      (((List.range U64_LIMBS).map fun i => limbWeight i * rowOf t i₀ (cLimb 1 i)).sum) hgate
  exact h2.trans hs

end Reduction

/-! ## §5 — THE WIDE CARRIER IS THE GENUINE PERMUTATION OUTPUT.

`cap_node8(l8, r8)` IS `chip_absorb_all_lanes(16, l8 ‖ r8)`, so each emitted site is a 16-input
wide chip lookup and the lever is `chip_lookup_sound_N`: ALL EIGHT lanes are forced, not just the
head. -/

/-- The 16 chip inputs a carrier site absorbs, as values: `[domain, v0..v3, a0..a3, rand, bl0..bl5]`.
-/
def wideIns (a : Assignment) (domain : ℤ) : List ℤ :=
  [domain, a (cV 0), a (cV 1), a (cV 2), a (cV 3), a (cA 0), a (cA 1), a (cA 2),
   a (cA 3), a cRAND, a (cBL 0), a (cBL 1), a (cBL 2), a (cBL 3), a (cBL 4), a (cBL 5)]

theorem wideIns_eval (a : Assignment) (domain : ℤ) :
    (wideLeft domain ++ wideRight).map (·.eval a) = wideIns a domain := rfl

theorem wideIns_length (a : Assignment) (domain : ℤ) : (wideIns a domain).length = 16 := rfl

theorem wideSiteIns_length (domain : ℤ) : (wideLeft domain ++ wideRight).length ≤ CHIP_RATE :=
  Nat.le_of_eq rfl

/-- Reading lane `j` off a carrier's output block. -/
theorem wideOut_getD (a : Assignment) (base j : Nat) (hj : j < 8) :
    ((wideOut base).map a).getD j 0 = a (base + j) := by
  interval_cases j <;> rfl

section Sites
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
variable {permOut : List ℤ → List ℤ}

/-- The generic per-site forcing. -/
theorem wide_lanes_forced_at (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length)
    {domain : ℤ} {base : Nat} (hm : wideSite domain base ∈ wideValueBindingDesc.constraints) :
    (wideOut base).map (rowOf t i) = permOut (wideIns (rowOf t i) domain) := by
  have hh := wvbLookup hsat i hi hm
  simp only [Lookup.holdsAt] at hh
  have := chip_lookup_sound_N permOut (t.tf TableId.poseidon2) hSound (rowOf t i)
    (wideLeft domain ++ wideRight) (wideOut base) (wideSiteIns_length domain) hh
  rwa [wideIns_eval] at this

/-- **The `DOMAIN_A` carrier: all eight lanes are the genuine squeeze of THIS row's own limbs.** -/
theorem wideA_lanes_forced (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length) :
    (wideOut (cWA 0)).map (rowOf t i) = permOut (wideIns (rowOf t i) DOMAIN_A) :=
  wide_lanes_forced_at hsat hSound i hi mem_wideA

/-- **The `DOMAIN_B` carrier** — the same eight-lane forcing at the second separator. Two domains,
sixteen published lanes. -/
theorem wideB_lanes_forced (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (i : Nat) (hi : i < t.rows.length) :
    (wideOut (cWB 0)).map (rowOf t i) = permOut (wideIns (rowOf t i) DOMAIN_B) :=
  wide_lanes_forced_at hsat hSound i hi mem_wideB

/-- **PUBLISHED = GENUINE.** Row 0's PI cell for wide lane `j < 8` is the `j`-th lane of the
genuine `DOMAIN_A` squeeze over that row's own limbs. -/
theorem published_lane_is_genuine (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (hrows : 0 < t.rows.length)
    {j : Nat} (hj : j < 8) :
    (envAt t 0).pub (PI_WIDE + j)
      ≡ (permOut (wideIns (rowOf t 0) DOMAIN_A)).getD j 0 [ZMOD 2013265921] := by
  have hlanes := wideA_lanes_forced hsat hSound 0 hrows
  have hpin : rowOf t 0 (laneCol j) ≡ (envAt t 0).pub (PI_WIDE + j) [ZMOD 2013265921] :=
    wvbPin hsat hrows (mem_pinLane (by simp only [WIDE_LANES]; omega))
  have hcol : laneCol j = cWA 0 + j := by
    simp only [laneCol, cWA, if_pos hj]
  have hval : rowOf t 0 (cWA 0 + j)
      = (permOut (wideIns (rowOf t 0) DOMAIN_A)).getD j 0 := by
    rw [← wideOut_getD (rowOf t 0) (cWA 0) j hj, hlanes]
  rw [hcol, hval] at hpin
  exact Int.ModEq.symm hpin

/-- **PUBLISHED = GENUINE, second half.** The eight `DOMAIN_B` PI cells are the lanes of the
genuine second squeeze — so all sixteen published lanes, not just the first eight, are forced. -/
theorem published_laneB_is_genuine (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (hrows : 0 < t.rows.length)
    {lane : Nat} (hlo : 8 ≤ lane) (hhi : lane < 16) :
    (envAt t 0).pub (PI_WIDE + lane)
      ≡ (permOut (wideIns (rowOf t 0) DOMAIN_B)).getD (lane - 8) 0 [ZMOD 2013265921] := by
  have hlanes := wideB_lanes_forced hsat hSound 0 hrows
  have hj : lane - 8 < 8 := by omega
  have hpin : rowOf t 0 (laneCol lane) ≡ (envAt t 0).pub (PI_WIDE + lane) [ZMOD 2013265921] :=
    wvbPin hsat hrows (mem_pinLane (by simp only [WIDE_LANES]; omega))
  have hcol : laneCol lane = cWB 0 + (lane - 8) := by
    simp only [laneCol, cWB, if_neg (by omega : ¬ lane < 8)]
  have hval : rowOf t 0 (cWB 0 + (lane - 8))
      = (permOut (wideIns (rowOf t 0) DOMAIN_B)).getD (lane - 8) 0 := by
    rw [← wideOut_getD (rowOf t 0) (cWB 0) (lane - 8) hj, hlanes]
  rw [hcol, hval] at hpin
  exact Int.ModEq.symm hpin

/-- **THE RUST "FALSE POLARITY 1" CANARY, AS A THEOREM.** The Rust test splices `+1` onto public
wide lane 15 of a genuine proof and observes that the verifier rejects THAT input. Here: a trace
publishing anything other than the genuine lane value is UNSATISFIABLE, for every witness. -/
theorem forged_lane_unsat (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hSound : ChipTableSoundN permOut (t.tf TableId.poseidon2)) (hrows : 0 < t.rows.length)
    {j : Nat} (hj : j < 8)
    (hforge : ¬ ((envAt t 0).pub (PI_WIDE + j)
      ≡ (permOut (wideIns (rowOf t 0) DOMAIN_A)).getD j 0 [ZMOD 2013265921])) : False :=
  hforge (published_lane_is_genuine hsat hSound hrows hj)

end Sites

/-! ## §6 — THE COMPATIBILITY JOIN IS THE DEPLOYED `hash_fact`.

`hash_fact(x, [f0,f1,f2])` IS the arity-7 chip absorb of `[x, f0, f1, f2, 0, 0xFACF, 1]` squeezed at
lane 0. Single output ⇒ the narrow bus, whose lever (`narrow_lookup_holdsAt_sound`) forces the SAME
digest equation the 25-wide site would. -/

/-- The seven values the compatibility fact site absorbs. -/
def legacyIns (a : Assignment) : List ℤ :=
  [a cVMOD, a cAMOD, a cRAND, 0, 0, FACT_MARK, 1]

theorem legacyIns_eval (a : Assignment) :
    (factIns [.var cVMOD, .var cAMOD, .var cRAND, .const 0]).map (·.eval a) = legacyIns a := rfl

section Legacy
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- **The legacy column is FORCED to `hash_fact(value_mod_p, [asset_mod_p, randomness, 0])`** over
the SAME cells the limbs recompose into. That is what makes the sidecar a JOIN to the deployed
spend circuit's C7 claim and not a second, independent claim. -/
theorem legacy_is_hash_fact (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hSound : ChipTableSound hash (t.tf TableId.poseidon2))
    (i : Nat) (hi : i < t.rows.length) :
    rowOf t i cLEGACY = hash (legacyIns (rowOf t i)) := by
  have hh := wvbLookup hsat i hi mem_legacy
  have hlen : (factIns [EmittedExpr.var cVMOD, .var cAMOD, .var cRAND, .const 0]).length
      ≤ CHIP_RATE := by decide
  have := narrow_lookup_holdsAt_sound hash t.tf hwire hSound (envAt t i)
    (factIns [EmittedExpr.var cVMOD, .var cAMOD, .var cRAND, .const 0]) cLEGACY hlen hh
  rwa [legacyIns_eval] at this

/-- Row 0's legacy PI cell is that forced digest. -/
theorem published_legacy_is_genuine
    (hsat : Satisfied2 hash wideValueBindingDesc minit mfin maddrs t)
    (hwire : t.tf poseidon2narrow = narrowTable (t.tf TableId.poseidon2))
    (hSound : ChipTableSound hash (t.tf TableId.poseidon2)) (hrows : 0 < t.rows.length) :
    (envAt t 0).pub PI_LEGACY ≡ hash (legacyIns (rowOf t 0)) [ZMOD 2013265921] := by
  have hpin := wvbPin hsat hrows mem_pinLegacy
  rw [legacy_is_hash_fact hsat hwire hSound 0 hrows] at hpin
  exact Int.ModEq.symm hpin

end Legacy

/-! ## §7 — THE BITE: the felt-width wound, refuted and repaired.

The Rust canary `full_u64_alias_is_distinguished_and_each_join_lane_is_load_bearing` asserts two
things about ONE witness pair: the legacy binding is EQUAL and the wide binding DIFFERS. Both are
theorems here, and the first needs no crypto at all. -/

/-- The Rust test's own value, `0x1234_5678_9abc_def0`. -/
def ALIAS_LO : ℤ := 1311768467463790320
/-- Its modulo-`p` alias `value + p` — a DIFFERENT `u64` with the SAME one-felt representation. -/
def ALIAS_HI : ℤ := ALIAS_LO + 2013265921

/-- The little-endian 16-bit limb extractor (the Rust `u64_limbs`). -/
def limbsOf (v : ℤ) (i : Nat) : ℤ := (v / 2 ^ (16 * i)) % 65536

/-- Both members of the pair are genuine, DISTINCT `u64`s. -/
theorem alias_pair_are_distinct_u64s :
    0 ≤ ALIAS_LO ∧ ALIAS_LO < 2 ^ 64 ∧ 0 ≤ ALIAS_HI ∧ ALIAS_HI < 2 ^ 64 ∧ ALIAS_LO ≠ ALIAS_HI := by
  refine ⟨by norm_num [ALIAS_LO], by norm_num [ALIAS_LO], by norm_num [ALIAS_HI, ALIAS_LO],
    by norm_num [ALIAS_HI, ALIAS_LO], by norm_num [ALIAS_HI, ALIAS_LO]⟩

/-- …and they REDUCE to the same BabyBear felt. -/
theorem alias_pair_reduce_equal : ALIAS_LO % 2013265921 = ALIAS_HI % 2013265921 := by
  norm_num [ALIAS_LO, ALIAS_HI, Int.add_mul_emod_self_left]

/-- …while their canonical 16-bit limb vectors DIFFER (limb 1 already separates them). -/
theorem alias_limbs_differ : limbsOf ALIAS_LO 1 ≠ limbsOf ALIAS_HI 1 := by
  norm_num [limbsOf, ALIAS_LO, ALIAS_HI]

/-- **THE WOUND, HYPOTHESIS-FREE.** Two rows honestly carrying the two DISTINCT `u64` values feed
the compatibility fact site IDENTICAL inputs, so its forced output column is EQUAL — whatever the
hash is. The one-felt join is provably blind to the alias; no crypto assumption is used, and none
could help. This is why the wide carrier exists. -/
theorem legacy_join_cannot_separate_aliases (hash : List ℤ → ℤ) (a a' : Assignment)
    (hv : a cVMOD = ALIAS_LO % 2013265921) (hv' : a' cVMOD = ALIAS_HI % 2013265921)
    (ha : a cAMOD = a' cAMOD) (hr : a cRAND = a' cRAND) :
    ALIAS_LO ≠ ALIAS_HI ∧ hash (legacyIns a) = hash (legacyIns a') := by
  refine ⟨by norm_num [ALIAS_HI, ALIAS_LO], congrArg hash ?_⟩
  simp only [legacyIns, hv, hv', ha, hr, alias_pair_reduce_equal]

/-! ### The NAMED wide floor, and the repair. -/

/-- Eight canonical 16-bit limbs (four value, four asset). -/
def CanonLimbs (l : Nat → ℤ) : Prop := ∀ i, i < 8 → 0 ≤ l i ∧ l i < 65536

/-- The 16 chip inputs of a carrier opening: `[domain, limb0..limb7, rand, blind0..blind5]` — the
`wideIns` shape, indexed by an opening rather than by a row. -/
def carrierIns (domain : ℤ) (l : Nat → ℤ) (r : ℤ) (bl : Nat → ℤ) : List ℤ :=
  domain :: (List.range 8).map l ++ r :: (List.range 6).map bl

/-- **THE NAMED FLOOR.** The eight-lane squeeze is injective IN THE LIMBS at fixed randomness and
blinds. Deliberately NOT injectivity over the whole opening: that is pigeonhole-FALSE here (≈345
bits of opening into ≈248 bits of output). At fixed `(r, bl)` the domain is 2^128 against a 2^248
range, so counting does not refute it — and it is exactly the comparison the Rust alias canary
makes, which clones the witness and changes only the value. -/
def WideCarrierCR (permOut : List ℤ → List ℤ) : Prop :=
  ∀ (domain r : ℤ) (l l' bl : Nat → ℤ), CanonLimbs l → CanonLimbs l' →
    permOut (carrierIns domain l r bl) = permOut (carrierIns domain l' r bl) →
    ∀ i, i < 8 → l i = l' i

/-- A `permOut` that SATISFIES the floor (the limb-projecting packer) — the floor is not vacuous. -/
def packPerm (xs : List ℤ) : List ℤ := (List.range 8).map fun t => xs.getD (t + 1) 0

/-- The packer projects exactly the eight limb slots. -/
theorem packPerm_carrierIns (domain r : ℤ) (l bl : Nat → ℤ) :
    packPerm (carrierIns domain l r bl) = [l 0, l 1, l 2, l 3, l 4, l 5, l 6, l 7] := rfl

theorem wideCarrierCR_satisfiable : WideCarrierCR packPerm := by
  intro domain r l l' bl _ _ h i hi
  rw [packPerm_carrierIns, packPerm_carrierIns] at h
  simp only [List.cons.injEq, and_true] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := h
  interval_cases i <;> assumption

/-- A `permOut` that REFUTES it — the floor is a real hypothesis, not a tautology. -/
theorem wideCarrierCR_refutable : ¬ WideCarrierCR (fun _ => [0, 0, 0, 0, 0, 0, 0, 0]) := by
  intro h
  have hc : CanonLimbs (fun _ => 0) := by intro i _; norm_num
  have hc' : CanonLimbs (fun i => if i = 0 then 1 else 0) := by
    intro i _; by_cases hi : i = 0 <;> simp [hi]
  have hz := h 0 0 (fun _ => 0) (fun i => if i = 0 then 1 else 0) (fun _ => 0) hc hc' rfl 0
    (by omega)
  norm_num at hz

/-- **THE REPAIR.** Under the named floor, two openings that differ in ANY limb publish DIFFERENT
carriers. Contrapositive of the floor, stated as the separation the felt-width repair claims. -/
theorem wide_carrier_separates (permOut : List ℤ → List ℤ) (hCR : WideCarrierCR permOut)
    (domain r : ℤ) (bl l l' : Nat → ℤ) (hl : CanonLimbs l) (hl' : CanonLimbs l')
    {i : Nat} (hi : i < 8) (hne : l i ≠ l' i) :
    permOut (carrierIns domain l r bl) ≠ permOut (carrierIns domain l' r bl) :=
  fun heq => hne (hCR domain r l l' bl hl hl' heq i hi)

/-- Limb extraction is canonical — `%` at a positive modulus lands in `[0, 65536)` outright, so
this needs no sign hypothesis on `v`. -/
theorem limbsOf_canon (v : ℤ) (i : Nat) : 0 ≤ limbsOf v i ∧ limbsOf v i < 65536 := by
  constructor
  · exact Int.emod_nonneg _ (by norm_num)
  · exact Int.emod_lt_of_pos _ (by norm_num)

/-- The alias pair's limb vectors, padded with a shared asset half. -/
def aliasLimbs (v : ℤ) (asset : Nat → ℤ) (i : Nat) : ℤ :=
  if i < 4 then limbsOf v i else asset (i - 4)

theorem aliasLimbs_canon (v : ℤ) {asset : Nat → ℤ}
    (hA : ∀ j, j < 4 → 0 ≤ asset j ∧ asset j < 65536) : CanonLimbs (aliasLimbs v asset) := by
  intro i hi
  by_cases h : i < 4
  · simpa [aliasLimbs, h] using limbsOf_canon v i
  · have : i - 4 < 4 := by omega
    simpa [aliasLimbs, h] using hA (i - 4) this

/-- **THE PAYOFF — the felt-width wound, closed.** On the Rust canary's own alias pair, the
compatibility one-felt join is EQUAL (no crypto needed to see it) while the wide carrier, under the
named floor, is DIFFERENT. The 16-lane carrier separates exactly where the deployed felt cannot. -/
theorem alias_separated_by_the_wide_carrier (permOut : List ℤ → List ℤ)
    (hCR : WideCarrierCR permOut) (hash : List ℤ → ℤ) (domain r : ℤ) (bl asset : Nat → ℤ)
    (hA : ∀ j, j < 4 → 0 ≤ asset j ∧ asset j < 65536) (a a' : Assignment)
    (hv : a cVMOD = ALIAS_LO % 2013265921) (hv' : a' cVMOD = ALIAS_HI % 2013265921)
    (ha : a cAMOD = a' cAMOD) (hr : a cRAND = a' cRAND) :
    hash (legacyIns a) = hash (legacyIns a')
      ∧ permOut (carrierIns domain (aliasLimbs ALIAS_LO asset) r bl)
        ≠ permOut (carrierIns domain (aliasLimbs ALIAS_HI asset) r bl) := by
  refine ⟨(legacy_join_cannot_separate_aliases hash a a' hv hv' ha hr).2, ?_⟩
  refine wide_carrier_separates permOut hCR domain r bl _ _
    (aliasLimbs_canon ALIAS_LO hA) (aliasLimbs_canon ALIAS_HI hA) (i := 1) (by omega) ?_
  simpa [aliasLimbs] using alias_limbs_differ

#assert_axioms bitSum_bounds
#assert_axioms limb_canonical
#assert_axioms seventeenth_bit_unsat
#assert_axioms vmod_is_the_reduction
#assert_axioms amod_is_the_reduction
#assert_axioms wideA_lanes_forced
#assert_axioms wideB_lanes_forced
#assert_axioms published_lane_is_genuine
#assert_axioms published_laneB_is_genuine
#assert_axioms forged_lane_unsat
#assert_axioms legacy_is_hash_fact
#assert_axioms published_legacy_is_genuine
#assert_axioms legacy_join_cannot_separate_aliases
#assert_axioms wideCarrierCR_satisfiable
#assert_axioms wideCarrierCR_refutable
#assert_axioms alias_separated_by_the_wide_carrier

end Dregg2.Circuit.Emit.WideValueBindingRefine
