/-
# `Dregg2.Circuit.FriDecodedTraceReadout` — L5·R4a: from the unique decoded codeword,
the trace columns, by low-degree restriction to the trace subdomain.

## What this file is

R2 (`FriCloseNUniqueDecode.closeN_rsCode_decode`, `FriCloseNUniqueDecode.lean:119`; fired at
the deployed instance `:172`/`:226`) ends with an `∃!` CODEWORD: a word `7340032`-close to
`friSetupDeployed.C` decodes to exactly one `g ∈ C`. The L5 target
(`DeployedTraceExtract.PositiveRadiusTraceDecode`, `DeployedTraceExtract.lean:344`) consumes a
TRACE — the per-column values on the trace rows, out of the batched multi-column commitment
(`FriBatchedOracle.MatrixOracle`, `FriBatchedOracle.lean:79`). This file is the RS/interpolation
half of that remaining distance (R4a): from the decoded codeword, READ OUT the trace column as
the restriction of the SAME low-degree polynomial to the trace subdomain.

  * `traceIdx i = ⟨8·i⟩` / `rowPt i = ω₂₄^(8·i)` — trace row `i` sits at LDE-domain index
    `8·i` (blowup `8` = `2^PROD_FRI_LOG_BLOWUP`, `circuit/src/plonky3_prover.rs:96-100`); the
    `2^21` trace points are distinct (`rowPt_injective`, via `orderOf (ω₂₄^8) = 2^21`), lie in
    the order-`2^21` subgroup (`rowPt_pow_traceRows`), and `traceIdx` hits EXACTLY the `8 ∣ x`
    residue class (`traceIdx_range`) — modeling fact (i), the subdomain embedding is clean.
  * `decodedTraceCol g = fun i => g (traceIdx i)` / `decodedTrace G` (per-column) — the readout.
  * `decodedTraceCol_eq_eval` + `decodedTrace_col_eq_interpolant` — modeling fact (ii): the
    trace column at row `i` IS `p.eval (rowPt i)` for THE unique `natDegree < 2^21` interpolant
    `p` of the decoded codeword (`mem_rsCode_iff_lowDegree_evalVec`,
    `FriCloseNUniqueDecode.lean:88`, is the bridge; uniqueness of `p` is pinned ON THE TRACE
    SUBDOMAIN itself, `trace_readout_pins_interpolant`).

## The dimension check the rung was gated on (CONFIRMED, no gap)

`friSetupDeployed` (`FriDeployedRateInstance.lean:454`): LDE domain `8·2^21 = 2^24` points,
code degree `< 2^18·8 = 2^21`, rate `1/8`. So the interpolant degree bound `2^21` EQUALS the
trace length `2^21` — `natDegree p < #rows` — and `2^21` sample points pin `p` exactly
(`trace_readout_pins_interpolant`, through `lowDegree_agree_forces_eq` on the image of
`rowPt`). The readout loses nothing: two codewords with equal traces are EQUAL
(`trace_pins_codeword`). No degree/length gap exists at the deployed parameters.

MODEL NOTE (honest): `FriDeployedRateInstance`'s domain is the plain subgroup `{ω₂₄^x}` — the
deployed plonky3 coset shift is not modeled there, so none is modeled here; the trace
subdomain is the plain index-`8` subgroup `{ω₂₄^(8i)}`.

## Assembly delivered (what R4b consumes)

  * `closeN_unique_trace` — a word inside the UD radius `7340032` has a UNIQUE trace readout:
    `∃! T, ∃ g p, g ∈ C ∧ dist ≤ e ∧ deg p < 2^21 ∧ g = evalVec p ∧ T = p ∘ rowPt`.
  * `colsClose_unique_trace` — the same at the batched multi-column commitment: a
    `MatrixOracle.ColsClose C 7340032` matrix (EXACTLY the shape L6's
    `sampled_embedding_matrix_close_or_paid`, `DeployedTraceExtract.lean:603`, delivers on its
    close branch) has a UNIQUE decoded trace MATRIX, each column the restriction of that
    column's unique interpolant.

FIRE (all hypotheses concrete, R2's fixtures): the corrupted word `fireWord24` decodes and its
trace reads out as ALL-ONES — `deployed_trace_readout_fires` (`∃!`),
`deployed_trace_readout_pins` (any witnessing trace IS all-ones, via `deployed_decode_pins`),
`fire_interpolant_pinned_C1` (the interpolant is forced to `C 1`), `decodedTrace_fires_allOnes`
(the matrix readout computes), `colsClose_unique_trace_fires` (the 1-column matrix instance).

CANARY (the decode is load-bearing for the readout): one past the radius, on R2's
`canaryWord` at `7340033`, the trace is NOT well-defined — `0` and `geomWord` are both
in-radius codewords and their readouts DIFFER at row 0 (`geomWord` reads `2^21 ≠ 0` there,
`geomWord_trace_row0` / `canary_two_traces`) — so no `∃!` (`canary_trace_ambiguous`), and
`trace_readout_radius_sharp` pairs both polarities at `e` / `e+1`.

## Scope (what R4a does NOT deliver — R4b's owe)

This file produces TRACE COLUMNS AS FIELD VECTORS (`Fin (2^21) → BabyBear`, per committed
column) from the decoded codewords, nothing more. R4b still owes the AIR-satisfaction half:
identifying those columns with a deployed `VmTrace t` and discharging the `TraceWitnessed`
legs (`MainAirAcceptF` + LogUp/range/memory legs + published-commit link,
`DeployedTraceExtract.lean:176`). The `closeN`/`ColsClose` hypothesis itself is CONSUMED, not
produced (link A / the L6 dichotomy delivers it except-with-`epsQuery`) — same posture as R2.

Additive new file; imports read-only. No sorry, no axiom, no carrier.
-/
import Dregg2.Circuit.FriCloseNUniqueDecode
import Dregg2.Circuit.FriBatchedOracle

namespace Dregg2.Circuit.FriDecodedTraceReadout

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.FriSoundness (closeN disagree)
open Dregg2.Circuit.RsUniqueDecoding (evalVec)
open Dregg2.Circuit.LowDegreeUniqueness (lowDegree_agree_forces_eq)
open Dregg2.Circuit.FriDeployedRateInstance
  (rsCode friSetupDeployed pR omega24 omega24_folded_orderOf omega24_pow_domain
   pow_inj_of_le_orderOf)
open Dregg2.Circuit.FriCloseNUniqueDecode
  (mem_rsCode_iff_lowDegree_evalVec friSetupDeployed_closeN_decode
   oneWord oneWord_mem fireWord24 fireWord24_close deployed_decode_pins
   canaryWord canary_dist_zero_le canary_dist_geomWord_le geomWord geomWord_mem)
open Dregg2.Circuit.FriBatchedOracle (MatrixOracle)

set_option autoImplicit false

/-! ## §0 — The deployed dimensions, confirmed: degree bound = trace length, LDE = 8× trace. -/

/-- **The rung's gate numbers.** The code degree bound `2^18·8` IS the trace length `2^21`,
and the LDE domain `8·2^21` IS `2^24` — the interpolant degree does NOT exceed the trace
length; they coincide exactly (rate `1/8`, blowup `8`). -/
theorem trace_dims_confirmed :
    (2 ^ 18 * 8 : ℕ) = 2 ^ 21 ∧ (8 * 2 ^ 21 : ℕ) = 2 ^ 24 := by norm_num

/-! ## §1 — The trace subdomain, pinned inside the LDE domain (modeling fact (i)). -/

/-- Trace row `i` sits at LDE-domain index `8·i` — the blowup-`8` embedding. -/
def traceIdx (i : Fin (2 ^ 21)) : Fin (8 * 2 ^ 21) :=
  ⟨8 * (i : ℕ), mul_lt_mul_of_pos_left i.isLt (by norm_num)⟩

theorem traceIdx_injective : Function.Injective traceIdx := by
  intro i j h
  have h8 : 8 * (i : ℕ) = 8 * (j : ℕ) := congrArg Fin.val h
  exact Fin.ext (by omega)

/-- **The trace-row point**: `rowPt i = ω₂₄^(8·i)` — the evaluation point of trace row `i`. -/
noncomputable def rowPt (i : Fin (2 ^ 21)) : BabyBear := omega24 ^ (8 * (i : ℕ))

/-- The trace-row point IS the LDE evaluation point at the embedded index — `rowPt` genuinely
indexes the trace subdomain inside the deployed domain (definitionally). -/
theorem rowPt_eq_pR (i : Fin (2 ^ 21)) :
    rowPt i = pR 8 (2 ^ 21) omega24 (traceIdx i) := rfl

/-- `rowPt i = (ω₂₄^8)^i` — the trace points are the powers of the blowup-`8` root. -/
theorem rowPt_eq_pow_blowup (i : Fin (2 ^ 21)) :
    rowPt i = (omega24 ^ 8) ^ (i : ℕ) := pow_mul omega24 8 (i : ℕ)

/-- The `2^21` trace points are DISTINCT (`orderOf (ω₂₄^8) = 2^21`,
`FriDeployedRateInstance.omega24_folded_orderOf`) — the subdomain is genuinely `2^21` rows. -/
theorem rowPt_injective : Function.Injective rowPt := by
  intro i j h
  apply pow_inj_of_le_orderOf omega24_folded_orderOf.ge
  show (omega24 ^ 8) ^ (i : ℕ) = (omega24 ^ 8) ^ (j : ℕ)
  rw [← rowPt_eq_pow_blowup, ← rowPt_eq_pow_blowup]
  exact h

/-- Every trace point is a `2^21`-th root of unity: the trace subdomain lies in the
order-`2^21` subgroup (with `rowPt_injective` it fills it — `2^21` distinct members). -/
theorem rowPt_pow_traceRows (i : Fin (2 ^ 21)) : rowPt i ^ (2 ^ 21) = 1 := by
  show (omega24 ^ (8 * (i : ℕ))) ^ (2 ^ 21) = 1
  rw [← pow_mul, show 8 * (i : ℕ) * 2 ^ 21 = 8 * 2 ^ 21 * (i : ℕ) by ring, pow_mul,
    omega24_pow_domain, one_pow]

/-- The embedded rows are EXACTLY the `8 ∣ x` residue class of the LDE domain — the trace
subdomain is the index-`8` subgroup, nothing more, nothing less. -/
theorem traceIdx_range (x : Fin (8 * 2 ^ 21)) :
    (∃ i, traceIdx i = x) ↔ 8 ∣ (x : ℕ) := by
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨(i : ℕ), rfl⟩
  · rintro ⟨y, hy⟩
    have hx : (x : ℕ) < 8 * 2 ^ 21 := x.isLt
    have h21 : (2 ^ 21 : ℕ) = 2097152 := by norm_num
    have hylt : y < 2 ^ 21 := by omega
    exact ⟨⟨y, hylt⟩, Fin.ext hy.symm⟩

/-! ## §2 — The readout: `decodedTrace`, and the same-polynomial restriction (fact (ii)). -/

/-- **The per-column trace readout**: the decoded codeword `g`, read on the trace subdomain. -/
noncomputable def decodedTraceCol (g : Fin (8 * 2 ^ 21) → BabyBear) :
    Fin (2 ^ 21) → BabyBear :=
  fun i => g (traceIdx i)

/-- **⚑ `decodedTrace`** — the decoded TRACE MATRIX: given the per-column decoded codewords
`G` (one per committed column of the batched `MatrixOracle` commitment), the trace value at
row `i`, column `j` is column `j`'s codeword read at the embedded row. The result is itself a
`MatrixOracle` over the trace rows — the object R4b consumes toward `TraceWitnessed`. -/
noncomputable def decodedTrace {numCols : ℕ}
    (G : Fin numCols → (Fin (8 * 2 ^ 21) → BabyBear)) :
    MatrixOracle (Fin (2 ^ 21)) numCols BabyBear :=
  fun i j => decodedTraceCol (G j) i

@[simp] theorem decodedTrace_col {numCols : ℕ}
    (G : Fin numCols → (Fin (8 * 2 ^ 21) → BabyBear)) (j : Fin numCols) :
    (decodedTrace G).col j = decodedTraceCol (G j) := rfl

/-- **Restriction is evaluation of the SAME polynomial**: if `g` is the evaluation vector of
`p` on the full LDE domain, the trace column reads `p` on the trace points. Definitional once
`rowPt_eq_pR` pins the subdomain — the content is that ONE polynomial serves both domains. -/
theorem decodedTraceCol_eq_eval {g : Fin (8 * 2 ^ 21) → BabyBear} {p : Polynomial BabyBear}
    (hg : g = evalVec (pR 8 (2 ^ 21) omega24) p) (i : Fin (2 ^ 21)) :
    decodedTraceCol g i = p.eval (rowPt i) := by
  subst hg
  rfl

/-- **The trace subdomain PINS the interpolant** — `natDegree < 2^21` and the `2^21` trace
points suffice: two low-degree polynomials with the same trace readout are EQUAL. This is the
no-gap fact of §0 in force (degree bound = number of trace rows), through
`lowDegree_agree_forces_eq` on the image of `rowPt`. -/
theorem trace_readout_pins_interpolant {p q : Polynomial BabyBear}
    (hp : p.natDegree < 2 ^ 18 * 8) (hq : q.natDegree < 2 ^ 18 * 8)
    (h : ∀ i : Fin (2 ^ 21), p.eval (rowPt i) = q.eval (rowPt i)) : p = q := by
  refine lowDegree_agree_forces_eq p q (Finset.univ.image rowPt) hp hq ?_ ?_
  · rw [Finset.card_image_of_injective _ rowPt_injective, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact h i

/-- Low-degree evaluation vectors on the FULL domain are injective in the polynomial — proved
by restricting to the trace subdomain (which already pins it). -/
theorem evalVec_lowDegree_inj {p q : Polynomial BabyBear}
    (hp : p.natDegree < 2 ^ 18 * 8) (hq : q.natDegree < 2 ^ 18 * 8)
    (h : evalVec (pR 8 (2 ^ 21) omega24) p = evalVec (pR 8 (2 ^ 21) omega24) q) :
    p = q :=
  trace_readout_pins_interpolant hp hq fun i => congrFun h (traceIdx i)

/-- **The readout loses nothing**: two codewords with the same trace are the SAME codeword —
the trace column determines the whole `2^24`-point codeword (well-definedness both ways). -/
theorem trace_pins_codeword {g g' : Fin (8 * 2 ^ 21) → BabyBear}
    (hg : g ∈ friSetupDeployed.C) (hg' : g' ∈ friSetupDeployed.C)
    (h : decodedTraceCol g = decodedTraceCol g') : g = g' := by
  have hg2 : g ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hg
  have hg2' : g' ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hg'
  obtain ⟨p, hpd, rfl⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hg2
  obtain ⟨q, hqd, rfl⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hg2'
  rw [trace_readout_pins_interpolant hpd hqd fun i => congrFun h i]

/-- **⚑ L5·R4a — the trace column IS the restriction of THE interpolant.** For each committed
column `j` of a decoded codeword family, there is EXACTLY ONE `natDegree < 2^21` polynomial
`p` that (a) evaluates to the codeword on the full LDE domain and (b) gives the trace column
by evaluation on the trace subdomain: `(decodedTrace G).col j i = p.eval (rowPt i)`. Existence
via `mem_rsCode_iff_lowDegree_evalVec` (R2's bridge (i)); uniqueness via the trace subdomain
itself (`evalVec_lowDegree_inj`). -/
theorem decodedTrace_col_eq_interpolant {numCols : ℕ}
    (G : Fin numCols → (Fin (8 * 2 ^ 21) → BabyBear))
    (hG : ∀ j, G j ∈ friSetupDeployed.C) (j : Fin numCols) :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ^ 18 * 8 ∧
      G j = evalVec (pR 8 (2 ^ 21) omega24) p ∧
      ∀ i : Fin (2 ^ 21), (decodedTrace G).col j i = p.eval (rowPt i) := by
  have hmem : G j ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hG j
  obtain ⟨p, hpd, hpe⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hmem
  refine ⟨p, ⟨hpd, hpe, fun i => decodedTraceCol_eq_eval hpe i⟩, ?_⟩
  rintro q ⟨hqd, hqe, -⟩
  exact evalVec_lowDegree_inj hqd hpd (by rw [← hqe, hpe])

/-! ## §3 — The assembly on R2's decode: inside the UD radius, the trace is UNIQUE. -/

/-- **⚑ The unique trace of a close word.** A word `7340032`-close to the deployed code (R2's
UD radius) determines EXACTLY ONE trace readout: the decoded codeword is unique
(`friSetupDeployed_closeN_decode`), its interpolant is unique (§2), and the trace is that
interpolant restricted to the trace subdomain. -/
theorem closeN_unique_trace {f : Fin (8 * 2 ^ 21) → BabyBear}
    (hclose : closeN friSetupDeployed.C 7340032 f) :
    ∃! T : Fin (2 ^ 21) → BabyBear,
      ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree f g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T = fun i => p.eval (rowPt i) := by
  obtain ⟨g, ⟨hgC, hgd⟩, huniq⟩ := friSetupDeployed_closeN_decode hclose
  have hg2 : g ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hgC
  obtain ⟨p, hpd, hpe⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hg2
  refine ⟨fun i => p.eval (rowPt i), ⟨g, p, hgC, hgd, hpd, hpe, rfl⟩, ?_⟩
  rintro T ⟨g', p', hg'C, hg'd, hp'd, hp'e, rfl⟩
  have hgg : g' = g := huniq g' ⟨hg'C, hg'd⟩
  have hpp : p' = p := evalVec_lowDegree_inj hp'd hpd (by rw [← hp'e, hgg, hpe])
  rw [hpp]

/-- **⚑ The unique trace MATRIX of a close batched commitment** — the multi-column readout,
consuming EXACTLY the `MatrixOracle.ColsClose` shape the L6 dichotomy delivers
(`sampled_embedding_matrix_close_or_paid`): every committed column `7340032`-close ⟹ exactly
one decoded trace matrix, each column the restriction of that column's unique interpolant. -/
theorem colsClose_unique_trace {numCols : ℕ}
    (M : MatrixOracle (Fin (8 * 2 ^ 21)) numCols BabyBear)
    (hcols : MatrixOracle.ColsClose friSetupDeployed.C 7340032 M) :
    ∃! T : MatrixOracle (Fin (2 ^ 21)) numCols BabyBear,
      ∀ j, ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree (M.col j) g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T.col j = fun i => p.eval (rowPt i) := by
  have hdec : ∀ j : Fin numCols, ∃ p : Polynomial BabyBear,
      p.natDegree < 2 ^ 18 * 8 ∧
      evalVec (pR 8 (2 ^ 21) omega24) p ∈ friSetupDeployed.C ∧
      (disagree (M.col j) (evalVec (pR 8 (2 ^ 21) omega24) p)).card ≤ 7340032 := by
    intro j
    obtain ⟨g, ⟨hgC, hgd⟩, -⟩ := friSetupDeployed_closeN_decode (hcols j)
    have hg2 : g ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := hgC
    obtain ⟨p, hpd, rfl⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hg2
    exact ⟨p, hpd, hgC, hgd⟩
  choose P hPdeg hPmem hPdist using hdec
  refine ⟨fun i j => (P j).eval (rowPt i),
    fun j => ⟨evalVec (pR 8 (2 ^ 21) omega24) (P j), P j, hPmem j, hPdist j, hPdeg j,
      rfl, rfl⟩, ?_⟩
  rintro T hT
  funext i j
  obtain ⟨g', p', hg'C, hg'd, hp'd, hp'e, hTcol⟩ := hT j
  obtain ⟨g0, ⟨hg0C, hg0d⟩, huniq⟩ := friSetupDeployed_closeN_decode (hcols j)
  have h1 : g' = g0 := huniq g' ⟨hg'C, hg'd⟩
  have h2 : evalVec (pR 8 (2 ^ 21) omega24) (P j) = g0 := huniq _ ⟨hPmem j, hPdist j⟩
  have hpp : p' = P j :=
    evalVec_lowDegree_inj hp'd (hPdeg j) (by rw [← hp'e, h1, ← h2])
  calc T i j = T.col j i := rfl
    _ = p'.eval (rowPt i) := congrFun hTcol i
    _ = (P j).eval (rowPt i) := by rw [hpp]

/-! ## §4 — FIRE: the corrupted word decodes AND its trace reads out (R2's fixtures). -/

/-- The honest codeword's interpolant, identified: `oneWord` is the evaluation vector of the
constant polynomial `1`. -/
theorem oneWord_evalVec_C1 :
    oneWord = evalVec (pR 8 (2 ^ 21) omega24) (Polynomial.C 1) := by
  funext x
  simp [oneWord, evalVec]

/-- The readout COMPUTES on the honest codeword: the all-ones trace, definitionally. -/
theorem decodedTraceCol_oneWord :
    decodedTraceCol oneWord = fun _ : Fin (2 ^ 21) => (1 : BabyBear) := rfl

/-- **FIRE (`decodedTrace`)** — the matrix readout at the decoded 1-column family computes to
the all-ones trace matrix. -/
theorem decodedTrace_fires_allOnes :
    decodedTrace (fun _ : Fin 1 => oneWord)
      = fun (_ : Fin (2 ^ 21)) (_ : Fin 1) => (1 : BabyBear) := rfl

/-- **FIRE (`decodedTrace_col_eq_interpolant`)** — the `∃!` interpolant-readout theorem, every
hypothesis discharged on the concrete decoded family (`oneWord_mem`). -/
theorem decodedTrace_col_eq_interpolant_fires :
    ∃! p : Polynomial BabyBear,
      p.natDegree < 2 ^ 18 * 8 ∧
      oneWord = evalVec (pR 8 (2 ^ 21) omega24) p ∧
      ∀ i : Fin (2 ^ 21),
        (decodedTrace fun _ : Fin 1 => oneWord).col 0 i = p.eval (rowPt i) :=
  decodedTrace_col_eq_interpolant (fun _ => oneWord) (fun _ => oneWord_mem) 0

/-- **FIRE (the interpolant is pinned)** — any low-degree polynomial evaluating to `oneWord`
IS `C 1`: the fired `∃!`'s witness is identified, not merely asserted. -/
theorem fire_interpolant_pinned_C1 {p : Polynomial BabyBear}
    (hpd : p.natDegree < 2 ^ 18 * 8)
    (hpe : oneWord = evalVec (pR 8 (2 ^ 21) omega24) p) :
    p = Polynomial.C 1 :=
  evalVec_lowDegree_inj hpd
    (by rw [Polynomial.natDegree_C]; norm_num)
    (by rw [← hpe, oneWord_evalVec_C1])

/-- **⚑ FIRE — the corrupted word's trace reads out.** R2's concrete corrupted word
`fireWord24` (all-ones codeword, coordinate 0 flipped — corruption real,
`fireWord24_corrupted`) has a UNIQUE trace readout at the deployed UD radius. -/
theorem deployed_trace_readout_fires :
    ∃! T : Fin (2 ^ 21) → BabyBear,
      ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree fireWord24 g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T = fun i => p.eval (rowPt i) :=
  closeN_unique_trace fireWord24_close

/-- **FIRE (the trace is pinned)** — ANY trace witnessing `fireWord24`'s readout is the
all-ones trace: the decode pins the codeword to `oneWord` (`deployed_decode_pins`) and the
readout restricts it. The corrupted coordinate is REPAIRED in the trace: the readout comes
from the decoded codeword, not the received word. -/
theorem deployed_trace_readout_pins (T : Fin (2 ^ 21) → BabyBear)
    (h : ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree fireWord24 g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T = fun i => p.eval (rowPt i)) :
    T = fun _ => (1 : BabyBear) := by
  obtain ⟨g, p, hgC, hgd, hpd, hpe, rfl⟩ := h
  have hone : g = oneWord := deployed_decode_pins g hgC hgd
  funext i
  show p.eval (rowPt i) = 1
  calc p.eval (rowPt i) = g (traceIdx i) := by rw [hpe]; rfl
    _ = 1 := by rw [hone]; rfl

/-- **FIRE (multi-column)** — the batched readout at the concrete 1-column commitment
`MatrixOracle.ofWord fireWord24`: the `ColsClose` hypothesis is discharged by R2's concrete
`fireWord24_close` through the `numCols = 1` bridge. -/
theorem colsClose_unique_trace_fires :
    ∃! T : MatrixOracle (Fin (2 ^ 21)) 1 BabyBear,
      ∀ j, ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧
        (disagree ((MatrixOracle.ofWord fireWord24).col j) g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T.col j = fun i => p.eval (rowPt i) :=
  colsClose_unique_trace (MatrixOracle.ofWord fireWord24)
    ((MatrixOracle.colsClose_ofWord_iff friSetupDeployed.C 7340032 fireWord24).mpr
      fireWord24_close)

/-! ## §5 — CANARY: one past the UD radius, the trace is NOT well-defined.

R2's `canaryWord` has TWO codewords within `7340033` (`0` and `geomWord`). Their trace
readouts DIFFER — at row 0, `geomWord` reads the geometric sum at the identity point,
`Σ_{s<2^21} 1 = 2^21 ≠ 0` in BabyBear — so the readout of §3 has no `∃!` there: the decode
(radius ≤ `7340032`) is load-bearing for the trace being a well-defined object at all. -/

/-- Trace row 0 (named once so every canary statement shares the literal term). -/
def row0 : Fin (2 ^ 21) := ⟨0, by norm_num⟩

/-- Row 0's evaluation point is the identity: `rowPt 0 = ω₂₄^0 = 1`. -/
theorem rowPt_row0 : rowPt row0 = 1 := by
  show omega24 ^ (8 * ((row0 : Fin (2 ^ 21)) : ℕ)) = 1
  have h : 8 * ((row0 : Fin (2 ^ 21)) : ℕ) = 0 := rfl
  rw [h, pow_zero]

/-- `geomWord`'s trace at row 0 is `Σ_{s<2^21} 1^s = 2^21` (as a BabyBear element). -/
theorem geomWord_trace_row0 :
    geomWord (traceIdx row0) = ((2 ^ 18 * 8 : ℕ) : BabyBear) := by
  have hp1 : pR 8 (2 ^ 21) omega24 (traceIdx row0) = 1 := by
    rw [← rowPt_eq_pR, rowPt_row0]
  show (∑ s : Fin (2 ^ 18 * 8), pR 8 (2 ^ 21) omega24 (traceIdx row0) ^ (s : ℕ))
      = ((2 ^ 18 * 8 : ℕ) : BabyBear)
  rw [hp1]
  simp

/-- **The two in-`(e+1)`-radius codewords have DIFFERENT traces** — `0` reads all-zeros,
`geomWord` reads `2^21 ≠ 0` at row 0 (`2^21 < p = 2013265921`, via the characteristic, not
`decide`). The ambiguity is in the READOUT, not just the codeword. -/
theorem canary_two_traces :
    decodedTraceCol (0 : Fin (8 * 2 ^ 21) → BabyBear) ≠ decodedTraceCol geomWord := by
  intro h
  have h0 : (0 : BabyBear) = geomWord (traceIdx row0) := congrFun h row0
  rw [geomWord_trace_row0] at h0
  have hne : ((2 ^ 18 * 8 : ℕ) : BabyBear) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff BabyBear babyBearP]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    norm_num at hle
  exact hne h0.symm

/-- **⚑ CANARY — beyond the UD radius the trace readout is AMBIGUOUS.** At `7340033` on
`canaryWord`, no unique trace exists: both the zero codeword (interpolant `0`) and `geomWord`
(its unique interpolant) witness the readout, and their traces differ at row 0. The §3
assembly's radius hypothesis is load-bearing — remove the decode and "the trace of the
committed word" stops denoting. -/
theorem canary_trace_ambiguous :
    ¬ ∃! T : Fin (2 ^ 21) → BabyBear,
        ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
          g ∈ friSetupDeployed.C ∧ (disagree canaryWord g).card ≤ 7340033 ∧
          p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
          T = fun i => p.eval (rowPt i) := by
  rintro ⟨T, -, huniq⟩
  have hzeroEval : (0 : Fin (8 * 2 ^ 21) → BabyBear)
      = evalVec (pR 8 (2 ^ 21) omega24) (0 : Polynomial BabyBear) := by
    funext x
    simp [evalVec]
  have hA : (fun i : Fin (2 ^ 21) => (0 : Polynomial BabyBear).eval (rowPt i)) = T :=
    huniq _ ⟨0, 0, friSetupDeployed.C.zero_mem, canary_dist_zero_le,
      by rw [Polynomial.natDegree_zero]; norm_num, hzeroEval, rfl⟩
  have hg2 : geomWord ∈ rsCode (pR 8 (2 ^ 21) omega24) (2 ^ 18 * 8) := geomWord_mem
  obtain ⟨p, hpd, hpe⟩ := (mem_rsCode_iff_lowDegree_evalVec (by norm_num)).mp hg2
  have hB : (fun i : Fin (2 ^ 21) => p.eval (rowPt i)) = T :=
    huniq _ ⟨geomWord, p, geomWord_mem, canary_dist_geomWord_le, hpd, hpe, rfl⟩
  apply canary_two_traces
  funext i
  calc decodedTraceCol (0 : Fin (8 * 2 ^ 21) → BabyBear) i
      = (0 : Polynomial BabyBear).eval (rowPt i) := decodedTraceCol_eq_eval hzeroEval i
    _ = p.eval (rowPt i) := congrFun (hA.trans hB.symm) i
    _ = decodedTraceCol geomWord i := (decodedTraceCol_eq_eval hpe i).symm

/-- **The R4a headline, both polarities on one instance**: at the deployed parameters the
radius `7340032` gives a unique trace readout and `7340033` does not — the readout inherits
R2's sharp radius exactly. -/
theorem trace_readout_radius_sharp :
    (∃! T : Fin (2 ^ 21) → BabyBear,
      ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree fireWord24 g).card ≤ 7340032 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T = fun i => p.eval (rowPt i)) ∧
    ¬ (∃! T : Fin (2 ^ 21) → BabyBear,
      ∃ (g : Fin (8 * 2 ^ 21) → BabyBear) (p : Polynomial BabyBear),
        g ∈ friSetupDeployed.C ∧ (disagree canaryWord g).card ≤ 7340033 ∧
        p.natDegree < 2 ^ 18 * 8 ∧ g = evalVec (pR 8 (2 ^ 21) omega24) p ∧
        T = fun i => p.eval (rowPt i)) :=
  ⟨deployed_trace_readout_fires, canary_trace_ambiguous⟩

/-! ## §6 — Axiom hygiene. -/

#assert_all_clean [trace_dims_confirmed, traceIdx_injective, rowPt_eq_pR,
  rowPt_eq_pow_blowup, rowPt_injective, rowPt_pow_traceRows, traceIdx_range,
  decodedTrace_col, decodedTraceCol_eq_eval, trace_readout_pins_interpolant,
  evalVec_lowDegree_inj, trace_pins_codeword, decodedTrace_col_eq_interpolant,
  closeN_unique_trace, colsClose_unique_trace, oneWord_evalVec_C1,
  decodedTraceCol_oneWord, decodedTrace_fires_allOnes,
  decodedTrace_col_eq_interpolant_fires, fire_interpolant_pinned_C1,
  deployed_trace_readout_fires, deployed_trace_readout_pins,
  colsClose_unique_trace_fires, rowPt_row0, geomWord_trace_row0, canary_two_traces,
  canary_trace_ambiguous, trace_readout_radius_sharp]

end Dregg2.Circuit.FriDecodedTraceReadout
