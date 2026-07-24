/-
# `AutomataflLegCRefine` — THE LEG C REFINEMENT (multi-round braid milestone **M2**)

`docs/reference/AUTOMATAFL-MULTIROUND-BRAID-DESIGN.md` §1.4 (M2), corrected by M1's finding. This
file proves `legC_sat_imp_roundAgainN`: a satisfying Leg C trace decodes to a `roundStep` `.again`
transition, up to `RoundStateAgrees` (permutation on `marks`, cell-wise board equality). The `=`
form the design stated is FALSE (M1 §8.6 exhibits it); `RoundStateAgrees` loses nothing — `MoveLegal`
reads `marks` only through `∉`, `RoundWF` only through `Nodup`, both permutation-invariant.

⚑ **SUBSTRATE.** No AIR is authored here — the Leg C AIR is `AutomataflLegCEmit` (Lean-authored). This
file is pure REFINEMENT: it reads `Satisfied2 (automataflLegCDescN n)` and concludes a fact about the
spec `AutomataflRules.roundStep`. No Rust.

## The membership-transport re-key (M1's flagged first task)

The reusable `_of_sat` extractors in `AutomataflResolveRefine`/`AutomataflResolveCapstone` are keyed
on `Satisfied2 (automataflResolveDescN n)` (they call `rgateN`/`rgateHN`, the resolve-specific
single-row extractors, and pull the FULL `ResolveFactsN` bundle — carries, flow-through, occlusion —
which Leg C does NOT emit). Leg C emits the front half (onePin / autoRead / validateMove×2 /
srcNonVac / patternBit / selection) VERBATIM but under a DIFFERENT descriptor, so those extractors do
not transfer for free (M1's honest finding: `surv_iff_clash_empty_of_sat` is keyed through
`resolveFactsN_of_sat`).

So §1 below re-derives the SELECTION BLOCK ALONE — descriptor-generic, off `AutomataflCoord`'s
`ngate`/`ngateH` (which take an arbitrary descriptor `d`) plus explicit family-membership transport
hypotheses. The proof bodies mirror the resolve ones with `rgateN → ngate`, `rgateHN → ngateH`; the
`evalH`-`rfl` polynomial shapes are structure-only, so they are unchanged. §2 instantiates them at
`automataflLegCDescN n` through `AutomataflLegCEmit`'s membership interface and builds the surv↔clash
bridge; `hclash` then FOLLOWS from `mem_clashPin` rather than being assumed.
-/
import Dregg2.Circuit.Emit.AutomataflLegCEmit
import Dregg2.Circuit.Emit.AutomataflResolveCapstone

namespace Dregg2.Circuit.Emit.AutomataflLegCRefine

open Dregg2.Circuit.Emit.AutomataflResolveEmit
open Dregg2.Circuit.Emit.AutomataflResolveMembership
open Dregg2.Circuit.Emit.AutomataflCoord
open Dregg2.Circuit.Emit.AutomataflOcclusionGeneric (OneHotAt)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.AutomataflStepRefine
open Dregg2.Circuit.Emit.AutomataflResolveRefine
open Dregg2.Games.Automatafl (Board Coord Particle Move MoveValid)

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-! ## §1 — THE SELECTION BLOCK, descriptor-generic.

Each lemma below is the descriptor-generic twin of an `AutomataflResolveRefine`/`Capstone` extractor:
`hsat : Satisfied2 hash d …` for an ARBITRARY descriptor `d`, with the family memberships the resolve
version discharged internally (via `mem_resolve_of_mem_*` / `mem_selection_idx`) supplied as explicit
transport hypotheses. The bodies are the resolve bodies with `rgateN`/`rgateHN` swapped for
`AutomataflCoord.ngate`/`ngateH`. -/

section Generic
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace} {n : Nat}

/-- `Builder::one`, off `d`. -/
theorem oneD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hone : NGen.onePin n ∈ d.constraints) :
    (envAt t i).loc (NGen.ONE n) = 1 := by
  have hg := ngateH hsat i hi (h := (Head.lin 1 (NGen.ONE n)).addConst (-1)) hone
  have hE : (headToExpr ((Head.lin 1 (NGen.ONE n)).addConst (-1))).eval (envAt t i).loc
      = (envAt t i).loc (NGen.ONE n) + (-1) := rfl
  rw [hE] at hg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hg)

/-- `Builder::cond_nonzero`, off `d`. -/
theorem condNonzeroD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (v inv : Nat)
    (hone : NGen.onePin n ∈ d.constraints)
    (hg : cg (gCondNonzero (NGen.ONE n) v inv) ∈ d.constraints) :
    ¬ ((envAt t i).loc v ≡ 0 [ZMOD 2013265921]) := by
  set e := envAt t i with he
  have hone1 := oneD_of_sat hsat hc i hi hone
  rw [← he] at hone1
  have h := ngate hsat i hi hg
  simp only [gCondNonzero, EmittedExpr.eval] at h
  rw [hone1, one_mul] at h
  intro hz
  have : (e.loc v * e.loc inv + -1) ≡ (0 * e.loc inv + -1) [ZMOD 2013265921] :=
    Int.ModEq.add (Int.ModEq.mul hz (Int.ModEq.refl _)) (Int.ModEq.refl _)
  have h2 : (0 : ℤ) ≡ -1 [ZMOD 2013265921] := by
    calc (0 : ℤ) ≡ e.loc v * e.loc inv + -1 [ZMOD 2013265921] := h.symm
    _ ≡ 0 * e.loc inv + -1 [ZMOD 2013265921] := this
    _ = -1 := by ring
  exact absurd (eq_of_modEq_small (by norm_num) (by norm_num) h2) (by norm_num)

/-- `Builder::alloc_prod`, off `d`. -/
theorem prodD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out a b : Nat)
    (hg : cgH ((Head.lin (-1) out).addProd 1 [a, b]) ∈ d.constraints)
    (ha : (envAt t i).loc a = 0 ∨ (envAt t i).loc a = 1)
    (hb : (envAt t i).loc b = 0 ∨ (envAt t i).loc b = 1) :
    (envAt t i).loc out = (envAt t i).loc a * (envAt t i).loc b := by
  set e := envAt t i with he
  have hgg := ngateH hsat i hi hg
  have hE : (headToExpr ((Head.lin (-1) out).addProd 1 [a, b])).eval e.loc
      = (-1) * e.loc out + e.loc a * e.loc b := rfl
  rw [hE] at hgg
  refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hgg)).symm
  rcases ha with h | h <;> rcases hb with h' | h' <;> rw [h, h'] <;>
    exact ⟨by norm_num, by norm_num⟩

/-- `Builder::not_bit`, off `d`. -/
theorem notBitD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (out col : Nat)
    (hg : notBitPin out col ∈ d.constraints)
    (hb : (envAt t i).loc col = 0 ∨ (envAt t i).loc col = 1) :
    (envAt t i).loc out = 1 - (envAt t i).loc col := by
  set e := envAt t i with he
  have hgg := ngateH hsat i hi hg
  have hE : (headToExpr (((Head.lin 1 out).addLin 1 col).addConst (-1))).eval e.loc
      = e.loc out + e.loc col + (-1) := rfl
  rw [hE] at hgg
  refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hgg)
  rcases hb with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩

/-- The 5-bit `forced_ge0` extractor, off `d` (`ge0_5N_of_sat`'s descriptor-generic twin). -/
theorem ge0_5D_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (val ib bit0 : Nat)
    (hib : cg (gBin ib) ∈ d.constraints)
    (hbit : ∀ k, k < 5 → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hrec : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))
             ∈ d.constraints)
    (hlo : -99 ≤ (envAt t i).loc val) (hhi : (envAt t i).loc val ≤ 99) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 → 1 ≤ (envAt t i).loc val)
      ∧ ((envAt t i).loc ib = 0 → (envAt t i).loc val ≤ 0) := by
  set e := envAt t i with he
  have hibv : e.loc ib = 0 ∨ e.loc ib = 1 :=
    bin_of_gate (ngate hsat i hi hib) (canon_loc hc i _)
  have B : ∀ k : Nat, k < 5 → (0 ≤ e.loc (bit0 + k) ∧ e.loc (bit0 + k) ≤ 1) := by
    intro k hk
    have hb : e.loc (bit0 + k) = 0 ∨ e.loc (bit0 + k) = 1 :=
      bin_of_gate (ngate hsat i hi (hbit k hk)) (canon_loc hc i _)
    rcases hb with h | h <;> omega
  have h0 := B 0 (by norm_num); have h1 := B 1 (by norm_num); have h2 := B 2 (by norm_num)
  have h3 := B 3 (by norm_num); have h4 := B 4 (by norm_num)
  set S : ℤ := e.loc (bit0 + 0) + 2 * e.loc (bit0 + 1) + 4 * e.loc (bit0 + 2)
    + 8 * e.loc (bit0 + 3) + 16 * e.loc (bit0 + 4) with hS
  have hS0 : 0 ≤ S := by rw [hS]; omega
  have hS1 : S ≤ 31 := by rw [hS]; omega
  have hg := ngateH hsat i hi hrec
  have hE : (headToExpr ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
        (forcedGe0Term ((Head.lin 1 val).addConst (-1)) ib))).eval e.loc
      = 2 * (e.loc ib * e.loc val) + (-2) * e.loc ib + e.loc ib + (-1) * e.loc val
        + (-1) * e.loc (bit0 + 0) + (-2) * e.loc (bit0 + 1) + (-4) * e.loc (bit0 + 2)
        + (-8) * e.loc (bit0 + 3) + (-16) * e.loc (bit0 + 4) := by rfl
  rw [hE] at hg
  have hmod : (2 * e.loc ib * (e.loc val - 1) + e.loc ib - (e.loc val - 1) - 1)
      ≡ S [ZMOD 2013265921] := by
    refine (gate_modEq_iff ?_).mp hg
    rw [hS]; ring
  obtain ⟨hp, hn⟩ := forcedGe0_core hibv hS0 hS1 hmod (by omega) (by omega)
  exact ⟨hibv, fun h => by have := hp h; omega, fun h => by have := hn h; omega⟩

/-- The auto pin, off `d` (`AutomataflCoord.autoPinN_of_sat`'s descriptor-generic twin). -/
theorem autoPinD_of_sat (hn : (n : ℤ) < 2013265921)
    (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hauto : ∀ {g : VmConstraint2}, g ∈ NGen.autoReadConstraints n → g ∈ d.constraints) :
    ∃ X Y : Nat, X < n ∧ Y < n
      ∧ (envAt t i).loc (NGen.AX_C n) = (X : ℤ) ∧ (envAt t i).loc (NGen.AY_C n) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.old n (Y * n + X)) = AUTO_CODE := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hayEq, hrow⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.selAutoRow n) (NGen.AY_C n)
      (fun j hj => hauto (ar_selRowBit n j hj)) (hauto (ar_selRowSum n)) (hauto (ar_selRowIdx n))
  obtain ⟨ax, haxLt, haxEq, hcol⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.selAutoCol n) (NGen.AX_C n)
      (fun j hj => hauto (ar_selColBit n j hj)) (hauto (ar_selColSum n)) (hauto (ar_selColIdx n))
  rw [← he] at hayEq haxEq
  have hg := ngateH hsat i hi (hauto (ar_autoPin n))
  rw [headToExpr_eval, evalH_autoPinHead] at hg
  rw [dot_oneHot2 hrow hcol (fun y x => e.loc (NGen.old n (y * n + x)))] at hg
  have hmod : e.loc (NGen.old n (ay * n + ax)) ≡ AUTO_CODE [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  have hcell : e.loc (NGen.old n (ay * n + ax)) = AUTO_CODE :=
    eq_of_modEq_canon (canon_loc hc i _) canon_three hmod
  exact ⟨ax, ay, haxLt, hayLt, haxEq, hayEq, hcell⟩

/-- The witnessed source read, off `d` (`sourceReadN_of_sat`'s descriptor-generic twin). -/
theorem sourceReadD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (b : Nat)
    (hn : (n : ℤ) < 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n b → g ∈ d.constraints) :
    ∃ X Y : Nat, X < n ∧ Y < n
      ∧ (envAt t i).loc (NGen.cFx n b) = (X : ℤ) ∧ (envAt t i).loc (NGen.cFy n b) = (Y : ℤ)
      ∧ (envAt t i).loc (NGen.cFp n b) = (envAt t i).loc (NGen.old n (Y * n + X)) := by
  set e := envAt t i with he
  obtain ⟨ay, hayLt, hfyEq, hrow⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.cSelRow n b) (NGen.cFy n b)
      (fun j hj => hmv (vm_selRow n b j hj)) (hmv (vm_srRs n b)) (hmv (vm_srRi n b))
  obtain ⟨ax, haxLt, hfxEq, hcol⟩ :=
    oneHotN_of_sat hsat hc i hi n hn (NGen.cSelCol n b) (NGen.cFx n b)
      (fun j hj => hmv (vm_selCol n b j hj)) (hmv (vm_srCs n b)) (hmv (vm_srCi n b))
  rw [← he] at hfyEq hfxEq
  have hg := ngateH hsat i hi (hmv (vm_srcRd n b))
  rw [headToExpr_eval, evalH_sourceReadHead,
    dot_oneHot2 hrow hcol (fun y x => - e.loc (NGen.old n (y * n + x)))] at hg
  have hmod : e.loc (NGen.cFp n b) ≡ e.loc (NGen.old n (ay * n + ax)) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hg
  exact ⟨ax, ay, haxLt, hayLt, hfxEq, hfyEq,
    eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) hmod⟩

/-- `validate_move ⇒ MoveValid`, off `d` (`validMoveN_of_sat`'s descriptor-generic twin). -/
theorem validMoveD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (M : ℤ)
    (hn1 : 1 ≤ n) (hnlt : (n : ℤ) < 2013265921) (hM : M = (n : ℤ) - 1) (hwin : M * M ≤ 1000000)
    (hcw : (2 : ℤ) ^ (NGen.COORD_RBITS n + 1) ≤ 2013265921)
    (hone : NGen.onePin n ∈ d.constraints)
    (hauto : ∀ {g : VmConstraint2}, g ∈ NGen.autoReadConstraints n → g ∈ d.constraints)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ d.constraints) :
    MoveValid (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) which) := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hbdef
  have embFx : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)
        → g ∈ d.constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (hg)))))))))))))
  have embFy : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)
        → g ∈ d.constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg)))))))))))))
  have embTx : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)
        → g ∈ d.constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg))))))))))))
  have embTy : ∀ {g : VmConstraint2},
      g ∈ NGen.decomposeConstraints n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)
        → g ∈ d.constraints := by
    intro g hg; apply hmv; rw [NGen.validateMove]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (hg)))))))))))
  obtain ⟨X, hXlt, hfxE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)
      hn1 hnlt hcw
      (fun k hk => embFx (mem_decompose_loBit n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b) k hk))
      (embFx (mem_decompose_loHead n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)))
      (fun k hk => embFx (mem_decompose_hiBit n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b) k hk))
      (embFx (mem_decompose_hiHead n (NGen.cFx n b) (NGen.cFxLo n b) (NGen.cFxHi n b)))
  obtain ⟨Y, hYlt, hfyE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)
      hn1 hnlt hcw
      (fun k hk => embFy (mem_decompose_loBit n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b) k hk))
      (embFy (mem_decompose_loHead n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)))
      (fun k hk => embFy (mem_decompose_hiBit n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b) k hk))
      (embFy (mem_decompose_hiHead n (NGen.cFy n b) (NGen.cFyLo n b) (NGen.cFyHi n b)))
  obtain ⟨TX, hTXlt, htxE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)
      hn1 hnlt hcw
      (fun k hk => embTx (mem_decompose_loBit n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b) k hk))
      (embTx (mem_decompose_loHead n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)))
      (fun k hk => embTx (mem_decompose_hiBit n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b) k hk))
      (embTx (mem_decompose_hiHead n (NGen.cTx n b) (NGen.cTxLo n b) (NGen.cTxHi n b)))
  obtain ⟨TY, hTYlt, htyE⟩ :=
    coordN_of_sat hsat hc i hi n (NGen.COORD_RBITS n) (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)
      hn1 hnlt hcw
      (fun k hk => embTy (mem_decompose_loBit n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b) k hk))
      (embTy (mem_decompose_loHead n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)))
      (fun k hk => embTy (mem_decompose_hiBit n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b) k hk))
      (embTy (mem_decompose_hiHead n (NGen.cTy n b) (NGen.cTyLo n b) (NGen.cTyHi n b)))
  obtain ⟨AX, AY, hAXlt, hAYlt, hAXe, hAYe, _⟩ := autoPinD_of_sat hnlt hsat hc i hi hauto
  rw [← he] at hfxE hfyE htxE htyE hAXe hAYe
  have bfx : 0 ≤ e.loc (NGen.cFx n b) ∧ e.loc (NGen.cFx n b) ≤ M := by rw [hfxE, hM]; omega
  have bfy : 0 ≤ e.loc (NGen.cFy n b) ∧ e.loc (NGen.cFy n b) ≤ M := by rw [hfyE, hM]; omega
  have btx : 0 ≤ e.loc (NGen.cTx n b) ∧ e.loc (NGen.cTx n b) ≤ M := by rw [htxE, hM]; omega
  have bty : 0 ≤ e.loc (NGen.cTy n b) ∧ e.loc (NGen.cTy n b) ≤ M := by rw [htyE, hM]; omega
  have bax : 0 ≤ e.loc (NGen.AX_C n) ∧ e.loc (NGen.AX_C n) ≤ M := by rw [hAXe, hM]; omega
  have bay : 0 ≤ e.loc (NGen.AY_C n) ∧ e.loc (NGen.AY_C n) ≤ M := by rw [hAYe, hM]; omega
  have hxn : (e.loc (NGen.cFx n b)).toNat = X := by rw [hfxE]; simp
  have hyn : (e.loc (NGen.cFy n b)).toNat = Y := by rw [hfyE]; simp
  have htxn : (e.loc (NGen.cTx n b)).toNat = TX := by rw [htxE]; simp
  have htyn : (e.loc (NGen.cTy n b)).toNat = TY := by rw [htyE]; simp
  have hd1sq : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith [bfx.1, bfx.2, btx.1, btx.2] : (0:ℤ) ≤ M - (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))) (by linarith [bfx.1, bfx.2, btx.1, btx.2] : (0:ℤ) ≤ M + (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)))]
  have hd2sq : (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) ≤ M * M :=
    by nlinarith [mul_nonneg (by linarith [bfy.1, bfy.2, bty.1, bty.2] : (0:ℤ) ≤ M - (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b))) (by linarith [bfy.1, bfy.2, bty.1, bty.2] : (0:ℤ) ≤ M + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
  have hrook : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) = 0 := by
    have hg := ngateH hsat i hi (hmv (vm_rook n b))
    have hE : (headToExpr (NGen.rookAlignHead n b)).eval e.loc
        = e.loc (NGen.cFx n b) * e.loc (NGen.cFy n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cTy n b))
          + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cFy n b)) + e.loc (NGen.cTx n b) * e.loc (NGen.cTy n b) := rfl
    rw [hE] at hg
    have hmod : (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b))
        ≡ 0 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    refine eq_of_modEq_win ⟨?_, ?_⟩ ⟨by norm_num, by norm_num⟩ hmod
    · nlinarith [hd1sq, hd2sq, hwin, mul_self_nonneg (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b) + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
    · nlinarith [hd1sq, hd2sq, hwin, mul_self_nonneg (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b) - (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)))]
  have hdsqDef : e.loc (NGen.cDsq n b)
      = (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b)) * (e.loc (NGen.cFx n b) - e.loc (NGen.cTx n b))
        + (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) * (e.loc (NGen.cFy n b) - e.loc (NGen.cTy n b)) := by
    have hg := ngateH hsat i hi (hmv (vm_dsqDef n b))
    have hE : (headToExpr (NGen.dsqHead n b)).eval e.loc
        = e.loc (NGen.cDsq n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cFx n b))
          + 2 * (e.loc (NGen.cFx n b) * e.loc (NGen.cTx n b)) + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cTx n b))
          + (-1) * (e.loc (NGen.cFy n b) * e.loc (NGen.cFy n b)) + 2 * (e.loc (NGen.cFy n b) * e.loc (NGen.cTy n b))
          + (-1) * (e.loc (NGen.cTy n b) * e.loc (NGen.cTy n b)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bfx btx bfy bty (by nlinarith [hwin]) hg
  have hdnz : ¬ ((e.loc (NGen.cDsq n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroD_of_sat hsat hc i hi (NGen.cDsq n b) (NGen.cDistinctInv n b) hone (hmv (vm_dsqNz n b))
    rwa [← he] at this
  have hdistinct : ¬ (e.loc (NGen.cFx n b) = e.loc (NGen.cTx n b) ∧ e.loc (NGen.cFy n b) = e.loc (NGen.cTy n b)) := by
    rintro ⟨h1, h2⟩; exact hdnz (by rw [hdsqDef, h1, h2]; simp [Int.ModEq])
  have hfaDef : e.loc (NGen.cFa n b)
      = (e.loc (NGen.cFx n b) - e.loc (NGen.AX_C n)) * (e.loc (NGen.cFx n b) - e.loc (NGen.AX_C n))
        + (e.loc (NGen.cFy n b) - e.loc (NGen.AY_C n)) * (e.loc (NGen.cFy n b) - e.loc (NGen.AY_C n)) := by
    have hg := ngateH hsat i hi (hmv (vm_faDef n b))
    have hE : (headToExpr (NGen.autoDistHead n (NGen.cFa n b) (NGen.cFx n b) (NGen.cFy n b))).eval e.loc
        = e.loc (NGen.cFa n b) + (-1) * (e.loc (NGen.cFx n b) * e.loc (NGen.cFx n b))
          + 2 * (e.loc (NGen.cFx n b) * e.loc (NGen.AX_C n)) + (-1) * (e.loc (NGen.AX_C n) * e.loc (NGen.AX_C n))
          + (-1) * (e.loc (NGen.cFy n b) * e.loc (NGen.cFy n b)) + 2 * (e.loc (NGen.cFy n b) * e.loc (NGen.AY_C n))
          + (-1) * (e.loc (NGen.AY_C n) * e.loc (NGen.AY_C n)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bfx bax bfy bay (by nlinarith [hwin]) hg
  have hfanz : ¬ ((e.loc (NGen.cFa n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroD_of_sat hsat hc i hi (NGen.cFa n b) (NGen.cFnaInv n b) hone (hmv (vm_faNz n b))
    rwa [← he] at this
  have hfnotauto : ¬ (e.loc (NGen.cFx n b) = e.loc (NGen.AX_C n) ∧ e.loc (NGen.cFy n b) = e.loc (NGen.AY_C n)) := by
    rintro ⟨h1, h2⟩; exact hfanz (by rw [hfaDef, h1, h2]; simp [Int.ModEq])
  have htaDef : e.loc (NGen.cTa n b)
      = (e.loc (NGen.cTx n b) - e.loc (NGen.AX_C n)) * (e.loc (NGen.cTx n b) - e.loc (NGen.AX_C n))
        + (e.loc (NGen.cTy n b) - e.loc (NGen.AY_C n)) * (e.loc (NGen.cTy n b) - e.loc (NGen.AY_C n)) := by
    have hg := ngateH hsat i hi (hmv (vm_taDef n b))
    have hE : (headToExpr (NGen.autoDistHead n (NGen.cTa n b) (NGen.cTx n b) (NGen.cTy n b))).eval e.loc
        = e.loc (NGen.cTa n b) + (-1) * (e.loc (NGen.cTx n b) * e.loc (NGen.cTx n b))
          + 2 * (e.loc (NGen.cTx n b) * e.loc (NGen.AX_C n)) + (-1) * (e.loc (NGen.AX_C n) * e.loc (NGen.AX_C n))
          + (-1) * (e.loc (NGen.cTy n b) * e.loc (NGen.cTy n b)) + 2 * (e.loc (NGen.cTy n b) * e.loc (NGen.AY_C n))
          + (-1) * (e.loc (NGen.AY_C n) * e.loc (NGen.AY_C n)) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) btx bax bty bay (by nlinarith [hwin]) hg
  have htanz : ¬ ((e.loc (NGen.cTa n b)) ≡ 0 [ZMOD 2013265921]) := by
    have := condNonzeroD_of_sat hsat hc i hi (NGen.cTa n b) (NGen.cTnaInv n b) hone (hmv (vm_taNz n b))
    rwa [← he] at this
  have htnotauto : ¬ (e.loc (NGen.cTx n b) = e.loc (NGen.AX_C n) ∧ e.loc (NGen.cTy n b) = e.loc (NGen.AY_C n)) := by
    rintro ⟨h1, h2⟩; exact htanz (by rw [htaDef, h1, h2]; simp [Int.ModEq])
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro hEq
    simp only [moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact hdistinct ⟨by omega, by omega⟩
  · rcases mul_eq_zero.mp hrook with h | h
    · left; simp only [moveDecodeN, ← hbdef]; omega
    · right; simp only [moveDecodeN, ← hbdef]; omega
  · show (moveDecodeN n e which).frm.x < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [hxn]; exact hXlt
  · show (moveDecodeN n e which).frm.y < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [hyn]; exact hYlt
  · show (moveDecodeN n e which).to.x < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [htxn]; exact hTXlt
  · show (moveDecodeN n e which).to.y < (boardDecodeOldN n e).size
    simp only [moveDecodeN, ← hbdef, boardDecodeOldN]; rw [htyn]; exact hTYlt
  · intro hEq
    simp only [Board.isAutomaton, boardDecodeOldN, moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact hfnotauto ⟨by omega, by omega⟩
  · intro hEq
    simp only [Board.isAutomaton, boardDecodeOldN, moveDecodeN, ← hbdef, Coord.mk.injEq] at hEq
    obtain ⟨q1, q2⟩ := hEq
    exact htnotauto ⟨by omega, by omega⟩
  · simp [Board.isConflict, boardDecodeOldN]
  · simp [Board.isConflict, boardDecodeOldN]

/-- An `eq_coords` pattern bit, off `d` (`eqCoordsN_of_sat`'s descriptor-generic twin). -/
theorem eqCoordsD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (xa ya xb yb ec : Nat) (M : ℤ)
    (hwin : 2 * M * M ≤ 999)
    (bxa : 0 ≤ (envAt t i).loc xa ∧ (envAt t i).loc xa ≤ M)
    (bya : 0 ≤ (envAt t i).loc ya ∧ (envAt t i).loc ya ≤ M)
    (bxb : 0 ≤ (envAt t i).loc xb ∧ (envAt t i).loc xb ≤ M)
    (byb : 0 ≤ (envAt t i).loc yb ∧ (envAt t i).loc yb ≤ M)
    (hlift : ∀ {g : VmConstraint2}, g ∈ NGen.eqCoordsConstraints n xa ya xb yb ec
            → g ∈ d.constraints) :
    ((envAt t i).loc (NGen.cEqBit n ec) = 0 ∨ (envAt t i).loc (NGen.cEqBit n ec) = 1)
      ∧ ((envAt t i).loc (NGen.cEqBit n ec) = 1 ↔
          ((envAt t i).loc xa = (envAt t i).loc xb ∧ (envAt t i).loc ya = (envAt t i).loc yb)) := by
  set e := envAt t i with he
  have hdsq : e.loc (NGen.cEqDsq n ec)
      = (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb)
        + (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) := by
    have hgm : cgH ((((((Head.lin 1 (NGen.cEqDsq n ec)).addProd (-1) [xa, xa]).addProd 2 [xa, xb]).addProd (-1)
          [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb] |>.addProd (-1) [yb, yb])
          ∈ d.constraints := by
      apply hlift; rw [NGen.eqCoordsConstraints]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_singleton.mpr rfl))
    have hg := ngateH hsat i hi hgm
    have hE : (headToExpr ((((((Head.lin 1 (NGen.cEqDsq n ec)).addProd (-1) [xa, xa]).addProd 2
          [xa, xb]).addProd (-1) [xb, xb]).addProd (-1) [ya, ya]).addProd 2 [ya, yb]
          |>.addProd (-1) [yb, yb])).eval e.loc
        = e.loc (NGen.cEqDsq n ec) + (-1) * (e.loc xa * e.loc xa) + 2 * (e.loc xa * e.loc xb)
          + (-1) * (e.loc xb * e.loc xb) + (-1) * (e.loc ya * e.loc ya)
          + 2 * (e.loc ya * e.loc yb) + (-1) * (e.loc yb * e.loc yb) := rfl
    rw [hE] at hg
    exact sqdistN_pure (canon_loc hc i _) bxa bxb bya byb (by nlinarith [hwin]) hg
  have hbnd : -999 ≤ e.loc (NGen.cEqDsq n ec) ∧ e.loc (NGen.cEqDsq n ec) ≤ 999 := by
    rw [hdsq]
    refine ⟨by nlinarith [mul_self_nonneg (e.loc xa - e.loc xb),
        mul_self_nonneg (e.loc ya - e.loc yb)], ?_⟩
    nlinarith [mul_nonneg (by linarith [bxa.1, bxa.2, bxb.1, bxb.2] :
        (0:ℤ) ≤ M - (e.loc xa - e.loc xb)) (by linarith [bxa.1, bxa.2, bxb.1, bxb.2] :
        (0:ℤ) ≤ M + (e.loc xa - e.loc xb)),
      mul_nonneg (by linarith [bya.1, bya.2, byb.1, byb.2] :
        (0:ℤ) ≤ M - (e.loc ya - e.loc yb)) (by linarith [bya.1, bya.2, byb.1, byb.2] :
        (0:ℤ) ≤ M + (e.loc ya - e.loc yb)), hwin]
  have gib : cg (gBin (NGen.cEqNeq n ec)) ∈ d.constraints := by
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_ib ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS))
  have gbit : ∀ k, k < 9 → cg (gBin (NGen.eqBitAt n ec 0 + k)) ∈ d.constraints := by
    intro k hk
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_bit ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS k hk))
  have ghead : cgH ((List.range 9).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (NGen.eqBitAt n ec 0 + k))
      (forcedGe0Term ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)))
      ∈ d.constraints := by
    apply hlift; rw [NGen.eqCoordsConstraints]
    exact List.mem_append_left _ (List.mem_append_right _
      (mem_forcedGe0N_head ((Head.lin 1 (NGen.cEqDsq n ec)).addConst (-1)) (NGen.cEqNeq n ec)
        (NGen.eqBitAt n ec 0) RBITS))
  obtain ⟨hnb, hn1, hn0⟩ :=
    Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.ge0_9N_of_sat hsat hc i hi
      (NGen.cEqDsq n ec) (NGen.cEqNeq n ec) (NGen.eqBitAt n ec 0)
      gib gbit ghead hbnd.1 hbnd.2
  rw [← he] at hnb hn1 hn0
  have hbit : e.loc (NGen.cEqBit n ec) = 1 - e.loc (NGen.cEqNeq n ec) := by
    have hep : cgH (((Head.lin 1 (NGen.cEqBit n ec)).addLin 1 (NGen.cEqNeq n ec)).addConst (-1))
        ∈ d.constraints := by
      apply hlift; rw [NGen.eqCoordsConstraints]
      exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have := Dregg2.Circuit.Emit.AutomataflOcclusionBridgeN.eqPinN_of_sat hsat hc i hi
      (NGen.cEqBit n ec) (NGen.cEqNeq n ec) hep hnb
    rwa [← he] at this
  refine ⟨by rcases hnb with h | h <;> rw [hbit, h] <;> norm_num, ?_⟩
  constructor
  · intro hone
    have hn : e.loc (NGen.cEqNeq n ec) = 0 := by omega
    have hle := hn0 hn
    rw [hdsq] at hle
    have hx0 : (e.loc xa - e.loc xb) * (e.loc xa - e.loc xb) = 0 :=
      le_antisymm (by nlinarith [mul_self_nonneg (e.loc ya - e.loc yb)]) (mul_self_nonneg _)
    have hy0 : (e.loc ya - e.loc yb) * (e.loc ya - e.loc yb) = 0 :=
      le_antisymm (by nlinarith [mul_self_nonneg (e.loc xa - e.loc xb)]) (mul_self_nonneg _)
    exact ⟨by have := mul_self_eq_zero.mp hx0; linarith,
           by have := mul_self_eq_zero.mp hy0; linarith⟩
  · rintro ⟨e1, e2⟩
    have hz : e.loc (NGen.cEqDsq n ec) = 0 := by rw [hdsq, e1, e2]; ring
    have : e.loc (NGen.cEqNeq n ec) = 0 := by
      rcases hnb with h | h
      · exact h
      · have := hn1 h; omega
    omega

/-- The source-non-vacuum bit, off `d` (`srcNonVacN_of_sat`'s descriptor-generic twin). -/
theorem srcNonVacD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which ib bit0 : Nat)
    (hnlt : (n : ℤ) < 2013265921)
    (hmv : ∀ {g : VmConstraint2}, g ∈ NGen.validateMove n (NGen.mvBase n which)
            → g ∈ d.constraints)
    (hbrold : ∀ c, c < NGen.KK n → cg (memberExpr (NGen.old n c) [0, 1, 2, 3]) ∈ d.constraints)
    (hib : cg (gBin ib) ∈ d.constraints)
    (hbit : ∀ k, k < 5 → cg (gBin (bit0 + k)) ∈ d.constraints)
    (hrec : cgH ((List.range 5).foldl (fun acc k => acc.addLin (-((2 : ℤ) ^ k)) (bit0 + k))
                 (forcedGe0Term ((Head.lin 1 (NGen.cFp n (NGen.mvBase n which))).addConst (-1)) ib))
             ∈ d.constraints) :
    ((envAt t i).loc ib = 0 ∨ (envAt t i).loc ib = 1)
      ∧ ((envAt t i).loc ib = 1 ↔
          ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) which).frm).isVacuum
            = false) := by
  set e := envAt t i with he
  set b := NGen.mvBase n which with hbdef
  obtain ⟨X, Y, hX, hY, hfxE, hfyE, hfp⟩ := sourceReadD_of_sat hsat hc i hi b hnlt hmv
  rw [← he] at hfxE hfyE hfp
  have hXY : Y * n + X < NGen.KK n := by
    simp only [NGen.KK]
    have hle : (Y + 1) * n ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hexp : (Y + 1) * n = Y * n + n := by ring
    omega
  have hcellAlpha : e.loc (NGen.old n (Y * n + X)) = 0 ∨ e.loc (NGen.old n (Y * n + X)) = 1
      ∨ e.loc (NGen.old n (Y * n + X)) = 2 ∨ e.loc (NGen.old n (Y * n + X)) = 3 :=
    AutomataflStepRefine.mem4_of_gate
      (ngate hsat i hi (hbrold (Y * n + X) hXY)) (canon_loc hc i _)
  have hfpv : e.loc (NGen.cFp n b) = 0 ∨ e.loc (NGen.cFp n b) = 1
      ∨ e.loc (NGen.cFp n b) = 2 ∨ e.loc (NGen.cFp n b) = 3 := by rw [hfp]; exact hcellAlpha
  have hbnd : -99 ≤ e.loc (NGen.cFp n b) ∧ e.loc (NGen.cFp n b) ≤ 99 := by
    rcases hfpv with h | h | h | h <;> rw [h] <;> constructor <;> norm_num
  obtain ⟨hb, h1, h0⟩ :=
    ge0_5D_of_sat hsat hc i hi (NGen.cFp n b) ib bit0 hib hbit hrec hbnd.1 hbnd.2
  rw [← he] at hb h1 h0
  have hcell : (boardDecodeOldN n e).cellAt (moveDecodeN n e which).frm
      = codeToParticle (e.loc (NGen.cFp n b)) := by
    have hxn : (e.loc (NGen.cFx n b)).toNat = X := by rw [hfxE]; simp
    have hyn : (e.loc (NGen.cFy n b)).toNat = Y := by rw [hfyE]; simp
    simp only [Board.cellAt, boardDecodeOldN, moveDecodeN, ← hbdef]
    rw [hxn, hyn, if_pos ⟨hX, hY⟩, hfp]
  rw [hcell]
  refine ⟨hb, ?_⟩
  rcases hfpv with hv | hv | hv | hv <;> rw [hv] at h1 h0 ⊢ <;>
    norm_num [codeToParticle, Particle.isVacuum] <;>
    (first
      | (intro hone; have := h1 hone; omega)
      | (rcases hb with hz | ho
         · exact absurd (h0 hz) (by norm_num)
         · exact ho))

/-- The selection truth table, off `d` (`selectionN_of_sat`'s descriptor-generic twin). -/
theorem selectionD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsel : ∀ {g : VmConstraint2}, g ∈ NGen.selectionConstraints n → g ∈ d.constraints)
    (hff : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (htt : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cFork n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0))
    ∧ ((envAt t i).loc (NGen.cCollide n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
          ∧ (envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1))
    ∧ ((envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    ∧ ((envAt t i).loc (NGen.cSurv n) = 1 ↔
        ((envAt t i).loc (NGen.cFork n) = 0 ∧ (envAt t i).loc (NGen.cCollide n) = 0)) := by
  set e := envAt t i with he
  have hsi : ∀ k (hk : k < (NGen.selectionConstraints n).length),
      (NGen.selectionConstraints n)[k] ∈ d.constraints := fun k hk => hsel (List.getElem_mem hk)
  have hforkv : e.loc (NGen.cFork n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 0))
        - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := by
    have hg := ngateH hsat i hi
      (h := ((Head.lin 1 (NGen.cFork n)).addLin (-1) (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
              [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])
      (hsi 0 (show (0:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cFork n)).addLin (-1)
          (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
          [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])).eval e.loc
        = e.loc (NGen.cFork n) + (-1) * e.loc (NGen.cEqBit n (NGen.eqBase n 0))
          + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc (NGen.cNeqFf n) = 1 - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) := by
    have hg := ngateH hsat i hi
      (h := ((Head.lin 1 (NGen.cNeqFf n)).addLin 1 (NGen.cEqBit n (NGen.eqBase n 0))).addConst (-1))
      (hsi 1 (show (1:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cNeqFf n)).addLin 1
        (NGen.cEqBit n (NGen.eqBase n 0))).addConst (-1))).eval e.loc
        = e.loc (NGen.cNeqFf n) + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rw [a] <;> exact ⟨by norm_num, by norm_num⟩
  have hcol1 : e.loc (NGen.cCol1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) := by
    have hg := ngateH hsat i hi
      (h := (Head.lin (-1) (NGen.cCol1 n)).addProd 1 [NGen.cEqBit n (NGen.eqBase n 1), NGen.cNeqFf n])
      (hsi 2 (show (2:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCol1 n)).addProd 1
        [NGen.cEqBit n (NGen.eqBase n 1), NGen.cNeqFf n])).eval e.loc
        = (-1) * e.loc (NGen.cCol1 n)
          + e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rw [hnff, a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hcol2 : e.loc (NGen.cCol2 n) = e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) := by
    have hg := ngateH hsat i hi
      (h := (Head.lin (-1) (NGen.cCol2 n)).addProd 1 [NGen.cCol1 n, NGen.cAnz n])
      (hsi 3 (show (3:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCol2 n)).addProd 1
        [NGen.cCol1 n, NGen.cAnz n])).eval e.loc
        = (-1) * e.loc (NGen.cCol2 n) + e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rw [hcol1, hnff, a, b, c] <;> exact ⟨by norm_num, by norm_num⟩
  have hcollv : e.loc (NGen.cCollide n) = e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) := by
    have hg := ngateH hsat i hi
      (h := (Head.lin (-1) (NGen.cCollide n)).addProd 1 [NGen.cCol2 n, NGen.cBnz n])
      (hsi 4 (show (4:Nat) < 6 by decide))
    have hE : (headToExpr ((Head.lin (-1) (NGen.cCollide n)).addProd 1
        [NGen.cCol2 n, NGen.cBnz n])).eval e.loc
        = (-1) * e.loc (NGen.cCollide n) + e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) := rfl
    rw [hE] at hg
    refine (eq_of_modEq_canon ?_ (canon_loc hc i _) ((gate_modEq_iff (by ring)).mp hg)).symm
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with dd | dd <;> rw [hcol2, hcol1, hnff, a, b, c, dd] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hsurvv : e.loc (NGen.cSurv n)
      = 1 - e.loc (NGen.cFork n) - e.loc (NGen.cCollide n)
        + e.loc (NGen.cFork n) * e.loc (NGen.cCollide n) := by
    have hg := ngateH hsat i hi
      (h := ((((Head.lin 1 (NGen.cSurv n)).addConst (-1)).addLin 1 (NGen.cFork n)).addLin 1
              (NGen.cCollide n)).addProd (-1) [NGen.cFork n, NGen.cCollide n])
      (hsi 5 (show (5:Nat) < 6 by decide))
    have hE : (headToExpr (((((Head.lin 1 (NGen.cSurv n)).addConst (-1)).addLin 1
        (NGen.cFork n)).addLin 1 (NGen.cCollide n)).addProd (-1)
        [NGen.cFork n, NGen.cCollide n])).eval e.loc
        = e.loc (NGen.cSurv n) + e.loc (NGen.cFork n) + e.loc (NGen.cCollide n)
          + (-1) * (e.loc (NGen.cFork n) * e.loc (NGen.cCollide n)) + (-1) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
      rcases hbnz with dd | dd <;> rw [hforkv, hcollv, hcol2, hcol1, hnff, a, b, c, dd] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases hff with a | a <;> rcases htt with b | b <;> rcases hanz with c | c <;>
    rcases hbnz with dd | dd <;>
    rw [hcollv, hcol2, hcol1, hnff] at hsurvv ⊢ <;> rw [hforkv] at hsurvv ⊢ <;>
    rw [a, b, c, dd] at hsurvv ⊢ <;> norm_num at hsurvv ⊢ <;>
    simp_all

/-- The `fork`/`collide` columns are boolean, off `d` (`forkCollideBoolN`'s twin). -/
theorem forkCollideBoolD_of_sat (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hsel : ∀ {g : VmConstraint2}, g ∈ NGen.selectionConstraints n → g ∈ d.constraints)
    (hff : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (htt : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hanz : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnz : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cFork n) = 0 ∨ (envAt t i).loc (NGen.cFork n) = 1)
      ∧ ((envAt t i).loc (NGen.cCollide n) = 0 ∨ (envAt t i).loc (NGen.cCollide n) = 1) := by
  set e := envAt t i with he
  have hsi : ∀ k (hk : k < (NGen.selectionConstraints n).length),
      (NGen.selectionConstraints n)[k] ∈ d.constraints := fun k hk => hsel (List.getElem_mem hk)
  have hforkv : e.loc (NGen.cFork n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 0))
        - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := by
    have hg := ngateH hsat i hi
      (h := ((Head.lin 1 (NGen.cFork n)).addLin (-1) (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
              [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])
      (hsi 0 (show (0:Nat) < 6 by decide))
    have hE : (headToExpr (((Head.lin 1 (NGen.cFork n)).addLin (-1)
          (NGen.cEqBit n (NGen.eqBase n 0))).addProd 1
          [NGen.cEqBit n (NGen.eqBase n 0), NGen.cEqBit n (NGen.eqBase n 1)])).eval e.loc
        = e.loc (NGen.cFork n) + (-1) * e.loc (NGen.cEqBit n (NGen.eqBase n 0))
          + e.loc (NGen.cEqBit n (NGen.eqBase n 0)) * e.loc (NGen.cEqBit n (NGen.eqBase n 1)) := rfl
    rw [hE] at hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ ((gate_modEq_iff (by ring)).mp hg)
    rcases hff with a | a <;> rcases htt with b | b <;> rw [a, b] <;>
      exact ⟨by norm_num, by norm_num⟩
  have hnff : e.loc (NGen.cNeqFf n) = 1 - e.loc (NGen.cEqBit n (NGen.eqBase n 0)) :=
    notBitD_of_sat hsat hc i hi (NGen.cNeqFf n) (NGen.cEqBit n (NGen.eqBase n 0)) (hsi 1 (show (1:Nat) < 6 by decide)) hff
  have hnffB : e.loc (NGen.cNeqFf n) = 0 ∨ e.loc (NGen.cNeqFf n) = 1 := by
    rcases hff with a | a <;> rw [hnff, a] <;> norm_num
  have hcol1 : e.loc (NGen.cCol1 n)
      = e.loc (NGen.cEqBit n (NGen.eqBase n 1)) * e.loc (NGen.cNeqFf n) :=
    prodD_of_sat hsat hc i hi (NGen.cCol1 n) (NGen.cEqBit n (NGen.eqBase n 1)) (NGen.cNeqFf n)
      (hsi 2 (show (2:Nat) < 6 by decide)) htt hnffB
  have hcol1B : e.loc (NGen.cCol1 n) = 0 ∨ e.loc (NGen.cCol1 n) = 1 := by
    rcases htt with a | a <;> rcases hnffB with b | b <;> rw [hcol1, a, b] <;> norm_num
  have hcol2 : e.loc (NGen.cCol2 n) = e.loc (NGen.cCol1 n) * e.loc (NGen.cAnz n) :=
    prodD_of_sat hsat hc i hi (NGen.cCol2 n) (NGen.cCol1 n) (NGen.cAnz n)
      (hsi 3 (show (3:Nat) < 6 by decide)) hcol1B hanz
  have hcol2B : e.loc (NGen.cCol2 n) = 0 ∨ e.loc (NGen.cCol2 n) = 1 := by
    rcases hcol1B with a | a <;> rcases hanz with b | b <;> rw [hcol2, a, b] <;> norm_num
  have hcollv : e.loc (NGen.cCollide n) = e.loc (NGen.cCol2 n) * e.loc (NGen.cBnz n) :=
    prodD_of_sat hsat hc i hi (NGen.cCollide n) (NGen.cCol2 n) (NGen.cBnz n)
      (hsi 4 (show (4:Nat) < 6 by decide)) hcol2B hbnz
  refine ⟨?_, ?_⟩
  · rcases hff with a | a <;> rcases htt with b | b <;> rw [hforkv, a, b] <;> norm_num
  · rcases hcol2B with a | a <;> rcases hbnz with b | b <;> rw [hcollv, a, b] <;> norm_num

end Generic

/-! ## §2 — LEG C INSTANTIATION + the surv↔clash bridge.

The generic extractors above, pointed at `automataflLegCDescN n` through `AutomataflLegCEmit`'s
membership interface (§5.1 there), and composed with `AutomataflRules.clashCoords_pair_iff` exactly
as `surv_iff_clash_empty_of_sat` does for Leg R. -/

section LegC
open Dregg2.Circuit.Emit.AutomataflLegCEmit
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow moveCoordBounds toNat_injN)
open Dregg2.Games.AutomataflRules (clashCoords carAt clashCoords_pair_iff)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- `onePin` is Leg C's first family. -/
theorem mem_legc_onePin : NGen.onePin n ∈ (automataflLegCDescN n).constraints :=
  mem_legC (by simp [legCFamilies]) (List.mem_singleton_self _)

/-- The OLD-board alphabet gate is in Leg C's board-range family. -/
theorem mem_legc_br_old (c : Nat) (hc : c < NGen.KK n) :
    cg (memberExpr (NGen.old n c) [0, 1, 2, 3]) ∈ (automataflLegCDescN n).constraints :=
  mem_boardRange (List.mem_append_left _ (List.mem_map.mpr ⟨c, List.mem_range.mpr hc, rfl⟩))

/-- The `validateMove` transport for move `which ∈ {0,1}`, at Leg C. -/
theorem legc_mv (which : Nat) (hw : which = 0 ∨ which = 1) {g : VmConstraint2}
    (hg : g ∈ NGen.validateMove n (NGen.mvBase n which)) :
    g ∈ (automataflLegCDescN n).constraints :=
  mem_validateMove hw hg

/-- The four move coordinates decoded into `[0, n)`, at Leg C (`moveCoordBounds`' twin). -/
theorem legcMoveCoordBounds (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which = 0 ∨ which = 1) :
    (0 ≤ (envAt t i).loc (NGen.cFx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cFx n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cFy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cFy n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n which)) < (n : ℤ))
    ∧ (0 ≤ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which))
        ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n which)) < (n : ℤ)) := by
  obtain ⟨-, -, ⟨hfx, hfy⟩, ⟨htx, hty⟩, -, -, -, -⟩ :=
    validMoveD_of_sat hsat hc i hi which ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM W.rbits
      mem_legc_onePin (fun hg => mem_autoRead hg) (fun hg => legc_mv which hw hg)
  have c1 := (canon_loc hc i (NGen.cFx n (NGen.mvBase n which))).1
  have c2 := (canon_loc hc i (NGen.cFy n (NGen.mvBase n which))).1
  have c3 := (canon_loc hc i (NGen.cTx n (NGen.mvBase n which))).1
  have c4 := (canon_loc hc i (NGen.cTy n (NGen.mvBase n which))).1
  simp only [moveDecodeN, boardDecodeOldN] at hfx hfy htx hty
  refine ⟨⟨c1, ?_⟩, ⟨c2, ?_⟩, ⟨c3, ?_⟩, ⟨c4, ?_⟩⟩ <;> omega

/-- **THE LEG C `MoveValid`** for move `which ∈ {0,1}`. -/
theorem legcMoveValid (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (which : Nat) (hw : which = 0 ∨ which = 1) :
    MoveValid (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) which) :=
  validMoveD_of_sat hsat hc i hi which ((n : ℤ) - 1) W.pos W.lt_p rfl W.sqM W.rbits
    mem_legc_onePin (fun hg => mem_autoRead hg) (fun hg => legc_mv which hw hg)

/-- **THE LEG C `surv` BOOLEANS + iffs.** The `selectionD`/`forkCollideBoolD` extractors, pointed at
Leg C's selection family (verbatim Leg R's). -/
theorem legcSurvFacts (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (hffB : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1)
    (httB : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0
        ∨ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1)
    (hanzB : (envAt t i).loc (NGen.cAnz n) = 0 ∨ (envAt t i).loc (NGen.cAnz n) = 1)
    (hbnzB : (envAt t i).loc (NGen.cBnz n) = 0 ∨ (envAt t i).loc (NGen.cBnz n) = 1) :
    ((envAt t i).loc (NGen.cFork n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0))
    ∧ ((envAt t i).loc (NGen.cCollide n) = 1 ↔
        ((envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
          ∧ (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0
          ∧ (envAt t i).loc (NGen.cAnz n) = 1 ∧ (envAt t i).loc (NGen.cBnz n) = 1))
    ∧ ((envAt t i).loc (NGen.cSurv n) = 0 ∨ (envAt t i).loc (NGen.cSurv n) = 1)
    ∧ ((envAt t i).loc (NGen.cSurv n) = 1 ↔
        ((envAt t i).loc (NGen.cFork n) = 0 ∧ (envAt t i).loc (NGen.cCollide n) = 0))
    ∧ ((envAt t i).loc (NGen.cFork n) = 0 ∨ (envAt t i).loc (NGen.cFork n) = 1)
    ∧ ((envAt t i).loc (NGen.cCollide n) = 0 ∨ (envAt t i).loc (NGen.cCollide n) = 1) := by
  obtain ⟨hf, hcoll, hsb, hsi⟩ := selectionD_of_sat hsat hc i hi
    (fun hg => mem_selection hg) hffB httB hanzB hbnzB
  obtain ⟨hforkB, hcollB⟩ := forkCollideBoolD_of_sat hsat hc i hi
    (fun hg => mem_selection hg) hffB httB hanzB hbnzB
  exact ⟨hf, hcoll, hsb, hsi, hforkB, hcollB⟩

/-- **THE LEG C `survIff`** — the `ResolveFactsN.survIff` shape, re-derived off Leg C's front half
alone (no carries / occlusion). `cSurv = 1` exactly when the pair neither forks nor collides. -/
theorem legcSurvIff (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.cSurv n) = 1 ↔
      ¬ (((moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm
            ∧ (moveDecodeN n (envAt t i) 0).to ≠ (moveDecodeN n (envAt t i) 1).to)
         ∨ ((moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to
            ∧ (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm
            ∧ ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 0).frm).isVacuum = false
            ∧ ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 1).frm).isVacuum = false)) := by
  obtain ⟨hfxa, hfya, htxa, htya⟩ := legcMoveCoordBounds W hsat hc i hi 0 (Or.inl rfl)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ := legcMoveCoordBounds W hsat hc i hi 1 (Or.inr rfl)
  have hMb : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  obtain ⟨hffB, hffI⟩ := eqCoordsD_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hMb _ hfxa) (hMb _ hfya) (hMb _ hfxb) (hMb _ hfyb)
    (fun hg => mem_patternBit (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg))))
  obtain ⟨httB, httI⟩ := eqCoordsD_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hMb _ htxa) (hMb _ htya) (hMb _ htxb) (hMb _ htyb)
    (fun hg => mem_patternBit (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))))
  obtain ⟨hanzB, hanzI⟩ := srcNonVacD_of_sat hsat hc i hi 0 (NGen.cAnz n) (NGen.anzBit n 0) W.lt_p
    (fun hg => legc_mv 0 (Or.inl rfl) hg)
    (fun c hc => mem_legc_br_old c hc)
    (mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_head _ _ _ _)))
  obtain ⟨hbnzB, hbnzI⟩ := srcNonVacD_of_sat hsat hc i hi 1 (NGen.cBnz n) (NGen.bnzBit n 0) W.lt_p
    (fun hg => legc_mv 1 (Or.inr rfl) hg)
    (fun c hc => mem_legc_br_old c hc)
    (mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _)))
  obtain ⟨hforkI, hcollI, _hsurvB, hsurvI, hforkB, hcollB⟩ :=
    legcSurvFacts W hsat hc i hi hffB httB hanzB hbnzB
  have hffC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm := by
    rw [hffI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN hfxa.1 hfxb.1, toNat_injN hfya.1 hfyb.1]
  have httC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to := by
    rw [httI]
    simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN htxa.1 htxb.1, toNat_injN htya.1 htyb.1]
  rw [hsurvI]
  constructor
  · rintro ⟨hf0, hc0⟩ hPQ
    rcases hPQ with h | h
    · have httz : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 0 := by
        rcases httB with hz | ho
        · exact hz
        · exact absurd (httC.mp ho) h.2
      have : (envAt t i).loc (NGen.cFork n) = 1 := hforkI.mpr ⟨hffC.mpr h.1, httz⟩
      omega
    · have hffz : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 0 := by
        rcases hffB with hz | ho
        · exact hz
        · exact absurd (hffC.mp ho) h.2.1
      have : (envAt t i).loc (NGen.cCollide n) = 1 :=
        hcollI.mpr ⟨httC.mpr h.1, hffz, hanzI.mpr h.2.2.1, hbnzI.mpr h.2.2.2⟩
      omega
  · intro hno
    refine ⟨?_, ?_⟩
    · rcases hforkB with hz | ho
      · exact hz
      · obtain ⟨h1, h2⟩ := hforkI.mp ho
        refine absurd (Or.inl ⟨hffC.mp h1, ?_⟩) hno
        intro hEq
        have := httC.mpr hEq
        omega
    · rcases hcollB with hz | ho
      · exact hz
      · obtain ⟨h1, h2, h3, h4⟩ := hcollI.mp ho
        refine absurd (Or.inr ⟨httC.mp h1, ?_, hanzI.mp h3, hbnzI.mp h4⟩) hno
        intro hEq
        have := hffC.mpr hEq
        omega

/-- **THE LEG C surv↔clash BRIDGE.** `cSurv = 1` exactly when the reference round has no
fork/collide conflict — `surv_iff_clash_empty_of_sat`'s twin, off Leg C's front half. -/
theorem legc_surv_iff_clash_empty (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (envAt t i).loc (NGen.cSurv n) = 1 ↔
      clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] = [] := by
  set e := envAt t i with he
  set bd := boardDecodeOldN n e with hbd
  set ma := moveDecodeN n e 0 with hma
  set mb := moveDecodeN n e 1 with hmb
  have hbr := clashCoords_pair_iff bd ma mb
  have hcaA : carAt bd ma.frm = true ↔ (bd.cellAt ma.frm).isVacuum = false := by simp [carAt]
  have hcaB : carAt bd mb.frm = true ↔ (bd.cellAt mb.frm).isVacuum = false := by simp [carAt]
  rw [legcSurvIff W hsat hc i hi]
  constructor
  · intro hnd
    by_contra hcl
    apply hnd
    rcases hbr.mp hcl with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hcaA.mp h3, hcaB.mp h4⟩
  · intro hcl hd
    refine (hbr.mpr ?_) hcl
    rcases hd with h | ⟨h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, hcaA.mpr h3, hcaB.mpr h4⟩

/-- **`hclash` IS A CONSEQUENCE, NOT A HYPOTHESIS.** `clashPin` gates `cSurv = 0` (`mem_clashPin`),
so via the bridge the round is a genuine clash: `clashCoords ≠ []`. -/
theorem legc_clash_of_sat (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] ≠ [] := by
  set e := envAt t i with he
  -- clashPin forces cSurv = 0
  have hsurv0 : e.loc (NGen.cSurv n) = 0 := by
    have hg := ngateH hsat i hi (h := Head.lin 1 (NGen.cSurv n)) (mem_clashPin n)
    have hE : (headToExpr (Head.lin 1 (NGen.cSurv n))).eval e.loc = e.loc (NGen.cSurv n) := rfl
    rw [hE] at hg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_zero ((gate_modEq_iff (by ring)).mp hg)
  intro hcl
  have : e.loc (NGen.cSurv n) = 1 := (legc_surv_iff_clash_empty W hsat hc i hi).mpr hcl
  omega

/-! ## §2.1 — Non-vacuity: the bridge at the DEPLOYED `n = 11` and the minimal `n = 2`. -/

open Dregg2.Circuit.Emit.AutomataflResolveCapstone (boardWindow_eleven boardWindow_two)

/-- The clash consequence at the deployed board — `n = 11`, `BoardWindow` discharged. -/
theorem legc_clash_of_sat11
    (hsat : Satisfied2 hash (automataflLegCDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    clashCoords (boardDecodeOldN 11 (envAt t i))
        [moveDecodeN 11 (envAt t i) 0, moveDecodeN 11 (envAt t i) 1] ≠ [] :=
  legc_clash_of_sat boardWindow_eleven hsat hc i hi

/-- …and at the minimal instance, `n = 2`. -/
theorem legc_clash_of_sat2
    (hsat : Satisfied2 hash (automataflLegCDescN 2) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    clashCoords (boardDecodeOldN 2 (envAt t i))
        [moveDecodeN 2 (envAt t i) 0, moveDecodeN 2 (envAt t i) 1] ≠ [] :=
  legc_clash_of_sat boardWindow_two hsat hc i hi

end LegC

/-! ## §2.2 — Axiom hygiene: the selection block and the bridge rest only on the kernel triple. -/

#assert_axioms AutomataflLegCRefine.selectionD_of_sat
#assert_axioms AutomataflLegCRefine.validMoveD_of_sat
#assert_axioms AutomataflLegCRefine.srcNonVacD_of_sat
#assert_axioms AutomataflLegCRefine.eqCoordsD_of_sat
#assert_axioms AutomataflLegCRefine.legcSurvIff
#assert_axioms AutomataflLegCRefine.legc_surv_iff_clash_empty
#assert_axioms AutomataflLegCRefine.legc_clash_of_sat
#assert_axioms AutomataflLegCRefine.legc_clash_of_sat11
#assert_axioms AutomataflLegCRefine.legc_clash_of_sat2

open Dregg2.Circuit.Emit.AutomataflLegCEmit

/-! ## Helper: `evalH_readAtHead` — the generic twin of `evalH_sourceReadHead`. -/

theorem evalH_readAtHead (a : Nat → ℤ) (n outCol : Nat) (rowSel colSel cellCol : Nat → Nat) :
    evalH (readAtHead n outCol rowSel colSel cellCol) a
      = a outCol
        + ((List.range n).map (fun y => ((List.range n).map (fun x =>
            a (rowSel y) * a (colSel x) * (- a (cellCol (y * n + x))))).sum)).sum := by
  have hinner : ∀ (h : Head) (y : Nat),
      evalH ((List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [rowSel y, colSel x, cellCol (y * n + x)]) h) a
        = evalH h a
          + ((List.range n).map (fun x =>
              a (rowSel y) * a (colSel x) * (- a (cellCol (y * n + x))))).sum := by
    intro h y
    exact evalH_foldl_step a h (List.range n)
      (fun h2 x => h2.addProd (-1) [rowSel y, colSel x, cellCol (y * n + x)])
      (fun x => a (rowSel y) * a (colSel x) * (- a (cellCol (y * n + x))))
      (by intro h2 x; rw [evalH_addProd]; simp only [varsVal, List.foldl_cons, List.foldl_nil]; ring)
  rw [readAtHead,
    evalH_foldl_step a (Head.lin 1 outCol) (List.range n)
      (fun h y => (List.range n).foldl (fun h2 x =>
          h2.addProd (-1) [rowSel y, colSel x, cellCol (y * n + x)]) h)
      (fun y => ((List.range n).map (fun x =>
          a (rowSel y) * a (colSel x) * (- a (cellCol (y * n + x))))).sum)
      hinner,
    evalH_lin]
  ring

/-! ## Lemma (2): the marks indicator column ↔ its row-major list. -/

theorem mem_marksListDecode_iff (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) (x y : Nat) :
    (⟨x, y⟩ : Coord) ∈ marksListDecode n cellCol e
      ↔ (x < n ∧ y < n ∧ e.loc (cellCol (y * n + x)) = 1) := by
  unfold marksListDecode
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨i, hi, hcond⟩
    rw [List.mem_range] at hi
    by_cases h1 : e.loc (cellCol i) == 1
    · rw [if_pos h1] at hcond
      simp only [Option.some.injEq, Coord.mk.injEq] at hcond
      obtain ⟨hxx, hyy⟩ := hcond
      have hyn : y < n := by
        subst hyy
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
      have hxn : x < n := by subst hxx; exact Nat.mod_lt _ (by omega)
      refine ⟨hxn, hyn, ?_⟩
      have hi' : y * n + x = i := by
        subst hxx hyy
        rw [Nat.mul_comm, Nat.div_add_mod]
      rw [hi']
      rw [beq_iff_eq] at h1
      exact h1
    · rw [if_neg h1] at hcond; exact absurd hcond (by simp)
  · rintro ⟨hxn, hyn, hval⟩
    refine ⟨y * n + x, ?_, ?_⟩
    · rw [List.mem_range]
      calc y * n + x < y * n + n := by omega
        _ = (y + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    · have hxx : (y * n + x) % n = x := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hxn]
      have hyy : (y * n + x) / n = y := by
        rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < n), Nat.div_eq_of_lt hxn, Nat.add_zero]
      rw [if_pos (by rw [hval]; rfl), hxx, hyy]

/-! ## Helper: the generic read collapses to the pinned cell. -/

section RA
variable {hash : List ℤ → ℤ} {d : EffectVmDescriptor2} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace} {n : Nat}

theorem readAt_collapse (hsat : Satisfied2 hash d minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length)
    (outCol : Nat) (rowSel colSel cellCol : Nat → Nat) (ay ax : Nat)
    (hrow : OneHotAt (fun j => (envAt t i).loc (rowSel j)) n ay)
    (hcol : OneHotAt (fun j => (envAt t i).loc (colSel j)) n ax)
    (hg : cgH (readAtHead n outCol rowSel colSel cellCol) ∈ d.constraints) :
    (envAt t i).loc outCol = (envAt t i).loc (cellCol (ay * n + ax)) := by
  set e := envAt t i with he
  have hgate := ngateH hsat i hi hg
  rw [headToExpr_eval, evalH_readAtHead,
    dot_oneHot2 hrow hcol (fun y x => - e.loc (cellCol (y * n + x)))] at hgate
  have hmod : e.loc outCol ≡ e.loc (cellCol (ay * n + ax)) [ZMOD 2013265921] :=
    (gate_modEq_iff (by ring)).mp hgate
  exact eq_of_modEq_canon (canon_loc hc i _) (canon_loc hc i _) hmod

end RA

/-! ## Helper: the destination one-hots of move `w`. -/

section Dest
variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat}
  {maddrs : List ℤ} {t : VmTrace} {n : Nat}

theorem destOneHots_of_sat
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1)
    (hn : (n : ℤ) < 2013265921) :
    (∃ TY : Nat, TY < n ∧ (envAt t i).loc (NGen.cTy n (NGen.mvBase n w)) = (TY : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (cTSelRow n w j)) n TY)
    ∧ (∃ TX : Nat, TX < n ∧ (envAt t i).loc (NGen.cTx n (NGen.mvBase n w)) = (TX : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (cTSelCol n w j)) n TX) := by
  have hmemRowBit : ∀ j, j < n →
      cg (gBin (cTSelRow n w j)) ∈ (automataflLegCDescN n).constraints := by
    intro j hj
    apply mem_destOneHot hw
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨cTSelRow n w j,
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, rfl⟩
  have hmemRowSum :
      cgH ((tSelRowCols n w).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
        ∈ (automataflLegCDescN n).constraints := by
    apply mem_destOneHot hw
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_singleton_self _
  have hmemRowIdx :
      cgH (((tSelRowCols n w).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
          ((Head.lin 1 (NGen.cTy n (NGen.mvBase n w))).scale (-1)))
        ∈ (automataflLegCDescN n).constraints := by
    apply mem_destOneHot hw
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_singleton_self _
  have hmemColBit : ∀ j, j < n →
      cg (gBin (cTSelCol n w j)) ∈ (automataflLegCDescN n).constraints := by
    intro j hj
    apply mem_destOneHot hw
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨cTSelCol n w j,
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩, rfl⟩
  have hmemColSum :
      cgH ((tSelColCols n w).foldl (fun acc s => acc.addLin 1 s) (Head.c (-1)))
        ∈ (automataflLegCDescN n).constraints := by
    apply mem_destOneHot hw
    apply List.mem_append_right
    apply List.mem_append_left
    apply List.mem_append_right
    exact List.mem_singleton_self _
  have hmemColIdx :
      cgH (((tSelColCols n w).zipIdx.foldl (fun acc p => acc.addLin (p.2 : ℤ) p.1) Head.zero).append
          ((Head.lin 1 (NGen.cTx n (NGen.mvBase n w))).scale (-1)))
        ∈ (automataflLegCDescN n).constraints := by
    apply mem_destOneHot hw
    apply List.mem_append_right
    apply List.mem_append_right
    exact List.mem_singleton_self _
  refine ⟨?_, ?_⟩
  · obtain ⟨ty, htyLt, htyEq, hrow⟩ :=
      oneHotN_of_sat hsat hc i hi n hn (cTSelRow n w) (NGen.cTy n (NGen.mvBase n w))
        hmemRowBit hmemRowSum hmemRowIdx
    exact ⟨ty, htyLt, htyEq, hrow⟩
  · obtain ⟨tx, htxLt, htxEq, hcol⟩ :=
      oneHotN_of_sat hsat hc i hi n hn (cTSelCol n w) (NGen.cTx n (NGen.mvBase n w))
        hmemColBit hmemColSum hmemColIdx
    exact ⟨tx, htxLt, htxEq, hcol⟩

theorem srcOneHots_of_sat
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1)
    (hn : (n : ℤ) < 2013265921) :
    (∃ Y : Nat, Y < n ∧ (envAt t i).loc (NGen.cFy n (NGen.mvBase n w)) = (Y : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (NGen.cSelRow n (NGen.mvBase n w) j)) n Y)
    ∧ (∃ X : Nat, X < n ∧ (envAt t i).loc (NGen.cFx n (NGen.mvBase n w)) = (X : ℤ)
        ∧ OneHotAt (fun j => (envAt t i).loc (NGen.cSelCol n (NGen.mvBase n w) j)) n X) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨ay, hayLt, hfyEq, hrow⟩ :=
      oneHotN_of_sat hsat hc i hi n hn (NGen.cSelRow n (NGen.mvBase n w)) (NGen.cFy n (NGen.mvBase n w))
        (fun j hj => mem_validateMove hw (vm_selRow n (NGen.mvBase n w) j hj))
        (mem_validateMove hw (vm_srRs n (NGen.mvBase n w)))
        (mem_validateMove hw (vm_srRi n (NGen.mvBase n w)))
    exact ⟨ay, hayLt, hfyEq, hrow⟩
  · obtain ⟨ax, haxLt, hfxEq, hcol⟩ :=
      oneHotN_of_sat hsat hc i hi n hn (NGen.cSelCol n (NGen.mvBase n w)) (NGen.cFx n (NGen.mvBase n w))
        (fun j hj => mem_validateMove hw (vm_selCol n (NGen.mvBase n w) j hj))
        (mem_validateMove hw (vm_srCs n (NGen.mvBase n w)))
        (mem_validateMove hw (vm_srCi n (NGen.mvBase n w)))
    exact ⟨ax, haxLt, hfxEq, hcol⟩

end Dest

/-! ## Helper: per-coordinate membership in `clashCoords` on a pair. -/

section Clash
open Dregg2.Games.AutomataflRules (clashCoords carAt forkAt collideAt candidates forkAt_pair
  collideAt_pair)

theorem mem_clashCoords_pair (b : Board) (ma mb : Move) (c : Coord) :
    c ∈ clashCoords b [ma, mb] ↔
      ((ma.frm = c ∧ mb.frm = c ∧ ma.to ≠ mb.to)
        ∨ (ma.to = c ∧ mb.to = c ∧ ma.frm ≠ mb.frm
            ∧ carAt b ma.frm = true ∧ carAt b mb.frm = true)) := by
  unfold clashCoords
  rw [List.mem_dedup, List.mem_filter, Bool.or_eq_true, forkAt_pair, collideAt_pair]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨hf1, _, _⟩ | ⟨hc1, _, _, _, _⟩
    · simp only [candidates, List.map_cons, List.map_nil, List.mem_append, List.mem_cons]
      exact Or.inl (Or.inl hf1.symm)
    · simp only [candidates, List.map_cons, List.map_nil, List.mem_append, List.mem_cons]
      exact Or.inr (Or.inl hc1.symm)

end Clash

/-! ## Helper: `cFork`/`cCollide` ⟺ the move geometry (the clash arms). -/

section FC
open Dregg2.Games.AutomataflRules (clashCoords carAt)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow toNat_injN)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

theorem legcForkCollide (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    ((envAt t i).loc (NGen.cFork n) = 0 ∨ (envAt t i).loc (NGen.cFork n) = 1)
    ∧ ((envAt t i).loc (NGen.cCollide n) = 0 ∨ (envAt t i).loc (NGen.cCollide n) = 1)
    ∧ ((envAt t i).loc (NGen.cFork n) = 1 ↔
        ((moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm
          ∧ (moveDecodeN n (envAt t i) 0).to ≠ (moveDecodeN n (envAt t i) 1).to))
    ∧ ((envAt t i).loc (NGen.cCollide n) = 1 ↔
        ((moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to
          ∧ (moveDecodeN n (envAt t i) 0).frm ≠ (moveDecodeN n (envAt t i) 1).frm
          ∧ carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true
          ∧ carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true)) := by
  obtain ⟨hfxa, hfya, htxa, htya⟩ := legcMoveCoordBounds W hsat hc i hi 0 (Or.inl rfl)
  obtain ⟨hfxb, hfyb, htxb, htyb⟩ := legcMoveCoordBounds W hsat hc i hi 1 (Or.inr rfl)
  have hMb : ∀ z : ℤ, 0 ≤ z ∧ z < (n : ℤ) → 0 ≤ z ∧ z ≤ (n : ℤ) - 1 := fun z h => ⟨h.1, by omega⟩
  obtain ⟨hffB, hffI⟩ := eqCoordsD_of_sat hsat hc i hi (NGen.cFx n (NGen.mvBase n 0))
    (NGen.cFy n (NGen.mvBase n 0)) (NGen.cFx n (NGen.mvBase n 1)) (NGen.cFy n (NGen.mvBase n 1))
    (NGen.eqBase n 0) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hMb _ hfxa) (hMb _ hfya) (hMb _ hfxb) (hMb _ hfyb)
    (fun hg => mem_patternBit (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg))))
  obtain ⟨httB, httI⟩ := eqCoordsD_of_sat hsat hc i hi (NGen.cTx n (NGen.mvBase n 0))
    (NGen.cTy n (NGen.mvBase n 0)) (NGen.cTx n (NGen.mvBase n 1)) (NGen.cTy n (NGen.mvBase n 1))
    (NGen.eqBase n 1) ((n : ℤ) - 1) (by have := W.sq999; linarith)
    (hMb _ htxa) (hMb _ htya) (hMb _ htxb) (hMb _ htyb)
    (fun hg => mem_patternBit (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))))
  obtain ⟨hanzB, hanzI⟩ := srcNonVacD_of_sat hsat hc i hi 0 (NGen.cAnz n) (NGen.anzBit n 0) W.lt_p
    (fun hg => legc_mv 0 (Or.inl rfl) hg)
    (fun c hc => mem_legc_br_old c hc)
    (mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_srcNonVac (List.mem_append_left _ (mem_forcedGe0N_head _ _ _ _)))
  obtain ⟨hbnzB, hbnzI⟩ := srcNonVacD_of_sat hsat hc i hi 1 (NGen.cBnz n) (NGen.bnzBit n 0) W.lt_p
    (fun hg => legc_mv 1 (Or.inr rfl) hg)
    (fun c hc => mem_legc_br_old c hc)
    (mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_ib _ _ _ _)))
    (fun k hk => mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_bit _ _ _ _ k hk)))
    (mem_srcNonVac (List.mem_append_right _ (mem_forcedGe0N_head _ _ _ _)))
  obtain ⟨hforkI, hcollI, _hsurvB, _hsurvI, hforkB, hcollB⟩ :=
    legcSurvFacts W hsat hc i hi hffB httB hanzB hbnzB
  have hffC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 0)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).frm = (moveDecodeN n (envAt t i) 1).frm := by
    rw [hffI]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN hfxa.1 hfxb.1, toNat_injN hfya.1 hfyb.1]
  have httC : (envAt t i).loc (NGen.cEqBit n (NGen.eqBase n 1)) = 1
      ↔ (moveDecodeN n (envAt t i) 0).to = (moveDecodeN n (envAt t i) 1).to := by
    rw [httI]; simp only [moveDecodeN, Coord.mk.injEq]
    rw [toNat_injN htxa.1 htxb.1, toNat_injN htya.1 htyb.1]
  have hcaA : carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 0).frm = true
      ↔ ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 0).frm).isVacuum = false := by
    simp [carAt]
  have hcaB : carAt (boardDecodeOldN n (envAt t i)) (moveDecodeN n (envAt t i) 1).frm = true
      ↔ ((boardDecodeOldN n (envAt t i)).cellAt (moveDecodeN n (envAt t i) 1).frm).isVacuum = false := by
    simp [carAt]
  refine ⟨hforkB, hcollB, ?_, ?_⟩
  · rw [hforkI]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨hffC.mp h1, ?_⟩
      intro hEq; have := httC.mpr hEq; omega
    · rintro ⟨h1, h2⟩
      refine ⟨hffC.mpr h1, ?_⟩
      rcases httB with hz | ho
      · exact hz
      · exact absurd (httC.mp ho) h2
  · rw [hcollI]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨httC.mp h1, ?_, hcaA.mpr (hanzI.mp h3), hcaB.mpr (hbnzI.mp h4)⟩
      intro hEq; have := hffC.mpr hEq; omega
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨httC.mpr h1, ?_, hanzI.mpr (hcaA.mp h3), hbnzI.mpr (hcaB.mp h4)⟩
      rcases hffB with hz | ho
      · exact hz
      · exact absurd (hffC.mp ho) h2

end FC

/-! ## Lemma (1): the clash-delta indicator IS `clashCoords` membership. -/

section CsCell
open Dregg2.Games.AutomataflRules (clashCoords carAt)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

theorem csCell_iff_mem_clash (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcn : c < NGen.KK n) :
    (envAt t i).loc (cCsCell n c) = 1 ↔
      (⟨c % n, c / n⟩ : Coord) ∈ clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1] := by
  set e := envAt t i with he
  have hnn : c < n * n := by simpa [NGen.KK] using hcn
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h] at hnn; simp at hnn
    · exact h
  have hcdivn : c / n < n := Nat.div_lt_of_lt_mul hnn
  have hcmodn : c % n < n := Nat.mod_lt _ hnpos
  obtain ⟨hforkB, hcollB, hforkC, hcollC⟩ := legcForkCollide W hsat hc i hi
  obtain ⟨⟨Y0, hY0lt, hfy0, hrow0⟩, ⟨X0, hX0lt, hfx0, hcol0⟩⟩ :=
    srcOneHots_of_sat hsat hc i hi 0 (Or.inl rfl) W.lt_p
  obtain ⟨⟨TY0, hTY0lt, hty0, hdrow0⟩, ⟨TX0, hTX0lt, htx0, hdcol0⟩⟩ :=
    destOneHots_of_sat hsat hc i hi 0 (Or.inl rfl) W.lt_p
  have hmd0frm : (moveDecodeN n e 0).frm = (⟨X0, Y0⟩ : Coord) := by
    simp only [moveDecodeN]; rw [hfx0, hfy0]; simp
  have hmd0to : (moveDecodeN n e 0).to = (⟨TX0, TY0⟩ : Coord) := by
    simp only [moveDecodeN]; rw [htx0, hty0]; simp
  have hexcl : ¬(e.loc (NGen.cFork n) = 1 ∧ e.loc (NGen.cCollide n) = 1) := by
    rintro ⟨hF, hCo⟩
    exact absurd (hcollC.mp hCo).1 (hforkC.mp hF).2
  -- the csCell value
  have hg := ngateH hsat i hi (mem_cs (List.mem_append_right _
      (List.mem_map.mpr ⟨c, List.mem_range.mpr hnn, rfl⟩)))
  rw [← he] at hg
  have hE : (headToExpr (csCellHead n c)).eval e.loc
      = e.loc (cCsCell n c)
        + (-1) * (e.loc (NGen.cFork n) * e.loc (NGen.cSelRow n (NGen.mvBase n 0) (c / n))
            * e.loc (NGen.cSelCol n (NGen.mvBase n 0) (c % n)))
        + (-1) * (e.loc (NGen.cCollide n) * e.loc (cTSelRow n 0 (c / n))
            * e.loc (cTSelCol n 0 (c % n))) := rfl
  have er0 : e.loc (NGen.cSelRow n (NGen.mvBase n 0) (c / n)) = if c / n = Y0 then (1 : ℤ) else 0 :=
    hrow0.2 (c / n) hcdivn
  have ec0 : e.loc (NGen.cSelCol n (NGen.mvBase n 0) (c % n)) = if c % n = X0 then (1 : ℤ) else 0 :=
    hcol0.2 (c % n) hcmodn
  have edr0 : e.loc (cTSelRow n 0 (c / n)) = if c / n = TY0 then (1 : ℤ) else 0 :=
    hdrow0.2 (c / n) hcdivn
  have edc0 : e.loc (cTSelCol n 0 (c % n)) = if c % n = TX0 then (1 : ℤ) else 0 :=
    hdcol0.2 (c % n) hcmodn
  rw [hE, er0, ec0, edr0, edc0] at hg
  have hcsEq : e.loc (cCsCell n c)
      = e.loc (NGen.cFork n) * (if c / n = Y0 then (1 : ℤ) else 0) * (if c % n = X0 then 1 else 0)
        + e.loc (NGen.cCollide n) * (if c / n = TY0 then 1 else 0) * (if c % n = TX0 then 1 else 0) := by
    have hmod : e.loc (cCsCell n c)
        ≡ e.loc (NGen.cFork n) * (if c / n = Y0 then (1 : ℤ) else 0) * (if c % n = X0 then 1 else 0)
          + e.loc (NGen.cCollide n) * (if c / n = TY0 then 1 else 0) * (if c % n = TX0 then 1 else 0)
          [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
    rcases hforkB with hF | hF <;> rcases hcollB with hCo | hCo <;>
      rw [hF, hCo] <;> split_ifs <;> exact ⟨by norm_num, by norm_num⟩
  -- arm rewrites
  have harm1 : ((moveDecodeN n e 0).frm = (⟨c % n, c / n⟩ : Coord)
        ∧ (moveDecodeN n e 1).frm = (⟨c % n, c / n⟩ : Coord)
        ∧ (moveDecodeN n e 0).to ≠ (moveDecodeN n e 1).to)
      ↔ (e.loc (NGen.cFork n) = 1 ∧ (moveDecodeN n e 0).frm = (⟨c % n, c / n⟩ : Coord)) := by
    constructor
    · rintro ⟨ha, hb, hd⟩; exact ⟨hforkC.mpr ⟨ha.trans hb.symm, hd⟩, ha⟩
    · rintro ⟨hF, ha⟩
      obtain ⟨heq, hne⟩ := hforkC.mp hF
      exact ⟨ha, heq.symm.trans ha, hne⟩
  have harm2 : ((moveDecodeN n e 0).to = (⟨c % n, c / n⟩ : Coord)
        ∧ (moveDecodeN n e 1).to = (⟨c % n, c / n⟩ : Coord)
        ∧ (moveDecodeN n e 0).frm ≠ (moveDecodeN n e 1).frm
        ∧ carAt (boardDecodeOldN n e) (moveDecodeN n e 0).frm = true
        ∧ carAt (boardDecodeOldN n e) (moveDecodeN n e 1).frm = true)
      ↔ (e.loc (NGen.cCollide n) = 1 ∧ (moveDecodeN n e 0).to = (⟨c % n, c / n⟩ : Coord)) := by
    constructor
    · rintro ⟨ha, hb, hd, hca, hcb⟩; exact ⟨hcollC.mpr ⟨ha.trans hb.symm, hd, hca, hcb⟩, ha⟩
    · rintro ⟨hCo, ha⟩
      obtain ⟨heq, hne, hca, hcb⟩ := hcollC.mp hCo
      exact ⟨ha, heq.symm.trans ha, hne, hca, hcb⟩
  rw [mem_clashCoords_pair, harm1, harm2, hmd0frm, hmd0to, hcsEq]
  -- now: F*ite*ite + Co*ite*ite = 1 ↔ (F=1 ∧ ⟨X0,Y0⟩=⟨c%n,c/n⟩) ∨ (Co=1 ∧ ⟨TX0,TY0⟩=⟨c%n,c/n⟩)
  rcases hforkB with hF | hF
  · rcases hcollB with hCo | hCo <;>
      · simp only [hF, hCo, Coord.mk.injEq] <;>
        by_cases a : c / n = Y0 <;> by_cases b : c % n = X0 <;>
        by_cases cc : c / n = TY0 <;> by_cases dd : c % n = TX0 <;>
        simp_all <;> omega
  · rcases hcollB with hCo | hCo
    · simp only [hF, hCo, Coord.mk.injEq]
      by_cases a : c / n = Y0 <;> by_cases b : c % n = X0 <;>
        by_cases cc : c / n = TY0 <;> by_cases dd : c % n = TX0 <;>
        simp_all <;> omega
    · exact absurd ⟨hF, hCo⟩ hexcl

end CsCell

/-! ## Lemma (4): the legality read ⇒ `MoveLegal` (marks half). -/

section Legality
open Dregg2.Games.AutomataflRules (MoveLegal)
open Dregg2.Circuit.Emit.AutomataflMarks (mem2_of_gate)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

theorem legcMoveLegal (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1) :
    MoveLegal (boardDecodeOldN n (envAt t i)) (marksListDecode n (cMarksInCell n) (envAt t i))
      (moveDecodeN n (envAt t i) w) := by
  set e := envAt t i with he
  have hvalid := legcMoveValid W hsat hc i hi w hw
  obtain ⟨⟨Yw, hYlt, hfyw, hrow⟩, ⟨Xw, hXlt, hfxw, hcol⟩⟩ := srcOneHots_of_sat hsat hc i hi w hw W.lt_p
  obtain ⟨⟨TYw, hTYlt, htyw, hdrow⟩, ⟨TXw, hTXlt, htxw, hdcol⟩⟩ :=
    destOneHots_of_sat hsat hc i hi w hw W.lt_p
  have hfrm : (moveDecodeN n e w).frm = (⟨Xw, Yw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [hfxw, hfyw]; simp
  have hto : (moveDecodeN n e w).to = (⟨TXw, TYw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [htxw, htyw]; simp
  have hidxF : Yw * n + Xw < n * n := by
    calc Yw * n + Xw < Yw * n + n := by omega
      _ = (Yw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidxT : TYw * n + TXw < n * n := by
    calc TYw * n + TXw < TYw * n + n := by omega
      _ = (TYw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  -- reads collapse to the marks cells
  have hrdF : e.loc (cInMarksFrm n w) = e.loc (cMarksInCell n (Yw * n + Xw)) :=
    readAt_collapse hsat hc i hi (cInMarksFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
      (NGen.cSelCol n (NGen.mvBase n w)) (cMarksInCell n) Yw Xw hrow hcol
      (mem_legality hw (List.mem_cons_self))
  have hrdT : e.loc (cInMarksTo n w) = e.loc (cMarksInCell n (TYw * n + TXw)) :=
    readAt_collapse hsat hc i hi (cInMarksTo n w) (cTSelRow n w) (cTSelCol n w) (cMarksInCell n)
      TYw TXw hdrow hdcol (mem_legality hw (List.mem_cons_of_mem _ (List.mem_cons_self)))
  -- marks cells are {0,1}
  have hmiF : e.loc (cMarksInCell n (Yw * n + Xw)) = 0 ∨ e.loc (cMarksInCell n (Yw * n + Xw)) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_marksIn (mem_marks_range hidxF (cMarksInCell n)
      (cMarksInFelt n) (piMarksIn n)))) (canon_loc hc i _)
  have hmiT : e.loc (cMarksInCell n (TYw * n + TXw)) = 0 ∨ e.loc (cMarksInCell n (TYw * n + TXw)) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_marksIn (mem_marks_range hidxT (cMarksInCell n)
      (cMarksInFelt n) (piMarksIn n)))) (canon_loc hc i _)
  -- legal[w] = 1
  have hlegal1 : e.loc (cLegal n w) = 1 := by
    have hgg := ngateH hsat i hi (mem_legality hw (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))
    have hE : (headToExpr ((Head.lin 1 (cLegal n w)).addConst (-1))).eval e.loc
        = e.loc (cLegal n w) + (-1) := rfl
    rw [hE] at hgg
    exact eq_of_modEq_canon (canon_loc hc i _) canon_one ((gate_modEq_iff (by ring)).mp hgg)
  -- the NOR gate
  have hnorEq : e.loc (cInMarksFrm n w) + e.loc (cInMarksTo n w)
      - e.loc (cInMarksFrm n w) * e.loc (cInMarksTo n w) = 0 := by
    have hgg := ngateH hsat i hi (mem_legality hw (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_self))))
    have hE : (headToExpr (norHead (cLegal n w) (cInMarksFrm n w) (cInMarksTo n w))).eval e.loc
        = e.loc (cLegal n w) + (-1) + e.loc (cInMarksFrm n w) + e.loc (cInMarksTo n w)
          + (-1) * (e.loc (cInMarksFrm n w) * e.loc (cInMarksTo n w)) := by
      rw [headToExpr_eval]
      simp only [norHead, evalH_addProd, evalH_addLin, evalH_addConst, evalH_lin, varsVal,
        List.foldl_cons, List.foldl_nil]
      ring
    rw [hE, hlegal1] at hgg
    have haF : e.loc (cInMarksFrm n w) = 0 ∨ e.loc (cInMarksFrm n w) = 1 := by rw [hrdF]; exact hmiF
    have hbT : e.loc (cInMarksTo n w) = 0 ∨ e.loc (cInMarksTo n w) = 1 := by rw [hrdT]; exact hmiT
    have hmod : e.loc (cInMarksFrm n w) + e.loc (cInMarksTo n w)
        - e.loc (cInMarksFrm n w) * e.loc (cInMarksTo n w) ≡ 0 [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hgg
    refine eq_of_modEq_canon ?_ canon_zero hmod
    rcases haF with h | h <;> rcases hbT with h' | h' <;> rw [h, h'] <;> exact ⟨by norm_num, by norm_num⟩
  have haF : e.loc (cInMarksFrm n w) = 0 ∨ e.loc (cInMarksFrm n w) = 1 := by rw [hrdF]; exact hmiF
  have hbT : e.loc (cInMarksTo n w) = 0 ∨ e.loc (cInMarksTo n w) = 1 := by rw [hrdT]; exact hmiT
  have hab : e.loc (cInMarksFrm n w) = 0 ∧ e.loc (cInMarksTo n w) = 0 := by
    rcases haF with h | h <;> rcases hbT with h' | h' <;> rw [h, h'] at hnorEq <;>
      first | exact ⟨h, h'⟩ | (exfalso; norm_num at hnorEq)
  have hmarksInF : e.loc (cMarksInCell n (Yw * n + Xw)) = 0 := by rw [← hrdF]; exact hab.1
  have hmarksInT : e.loc (cMarksInCell n (TYw * n + TXw)) = 0 := by rw [← hrdT]; exact hab.2
  have hfrmNotMem : (⟨Xw, Yw⟩ : Coord) ∉ marksListDecode n (cMarksInCell n) e := by
    intro hmem
    rw [mem_marksListDecode_iff] at hmem
    rw [hmarksInF] at hmem
    exact absurd hmem.2.2 (by norm_num)
  have htoNotMem : (⟨TXw, TYw⟩ : Coord) ∉ marksListDecode n (cMarksInCell n) e := by
    intro hmem
    rw [mem_marksListDecode_iff] at hmem
    rw [hmarksInT] at hmem
    exact absurd hmem.2.2 (by norm_num)
  obtain ⟨hne, hrook, hibF, hibT, hautoF, -, -, -⟩ := hvalid
  exact ⟨hne, hrook, hibF, hibT, hautoF, by rw [hfrm]; exact hfrmNotMem,
    by rw [hto]; exact htoNotMem⟩

end Legality

/-! ## Helper: `marksListDecode` is duplicate-free. -/

theorem marksListDecode_nodup (n : Nat) (cellCol : Nat → Nat) (e : VmRowEnv) :
    (marksListDecode n cellCol e).Nodup := by
  unfold marksListDecode
  refine List.Nodup.filterMap ?_ List.nodup_range
  intro a a' b h1 h2
  by_cases c1 : e.loc (cellCol a) == 1
  · by_cases c2 : e.loc (cellCol a') == 1
    · rw [if_pos c1] at h1; rw [if_pos c2] at h2
      simp only [Option.mem_def, Option.some.injEq] at h1 h2
      subst h1
      rw [Coord.mk.injEq] at h2
      obtain ⟨ha, hd⟩ := h2
      have e1 := Nat.div_add_mod a n
      have e2 := Nat.div_add_mod a' n
      rw [← hd, ← ha] at e1
      omega
    · rw [if_neg c2] at h2; simp at h2
  · rw [if_neg c1] at h1; simp at h1

/-! ## Lemma (3): `marksOut = marksIn ∨ cs` decodes to a permutation of `(marks ++ cs).dedup`. -/

section Perm
open Dregg2.Games.AutomataflRules (clashCoords carAt candidates)
open Dregg2.Circuit.Emit.AutomataflMarks (mem2_of_gate)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- The `marksOut = marksIn ∨ cs` gate at cell `c`. -/
theorem marksOr_cellEq (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (c : Nat) (hcn : c < NGen.KK n) :
    (envAt t i).loc (cMarksOutCell n c) = 1 ↔
      ((envAt t i).loc (cMarksInCell n c) = 1 ∨ (envAt t i).loc (cCsCell n c) = 1) := by
  set e := envAt t i with he
  have hcn' : c < n * n := by simpa [NGen.KK] using hcn
  have hin : e.loc (cMarksInCell n c) = 0 ∨ e.loc (cMarksInCell n c) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_marksIn (mem_marks_range hcn' (cMarksInCell n)
      (cMarksInFelt n) (piMarksIn n)))) (canon_loc hc i _)
  have hcs : e.loc (cCsCell n c) = 0 ∨ e.loc (cCsCell n c) = 1 :=
    bin_of_gate (ngate hsat i hi (mem_cs (List.mem_append_left _
      (List.mem_map.mpr ⟨c, List.mem_range.mpr hcn, rfl⟩)))) (canon_loc hc i _)
  have hout : e.loc (cMarksOutCell n c) = 0 ∨ e.loc (cMarksOutCell n c) = 1 :=
    mem2_of_gate (ngate hsat i hi (mem_marksOut (mem_marks_range hcn' (cMarksOutCell n)
      (cMarksOutFelt n) (piMarksOut n)))) (canon_loc hc i _)
  have hoeq : e.loc (cMarksOutCell n c)
      = e.loc (cMarksInCell n c) + e.loc (cCsCell n c)
        - e.loc (cMarksInCell n c) * e.loc (cCsCell n c) := by
    have hgg := ngateH hsat i hi (mem_marksOr
      (List.mem_map.mpr ⟨c, List.mem_range.mpr hcn, rfl⟩))
    have hE : (headToExpr (orHead (cMarksOutCell n c) (cMarksInCell n c) (cCsCell n c))).eval e.loc
        = e.loc (cMarksOutCell n c) + (-1) * e.loc (cMarksInCell n c) + (-1) * e.loc (cCsCell n c)
          + e.loc (cMarksInCell n c) * e.loc (cCsCell n c) := by
      rw [headToExpr_eval]
      simp only [orHead, evalH_addProd, evalH_addLin, evalH_lin, varsVal,
        List.foldl_cons, List.foldl_nil]
      ring
    rw [hE] at hgg
    have hmod : e.loc (cMarksOutCell n c)
        ≡ e.loc (cMarksInCell n c) + e.loc (cCsCell n c)
          - e.loc (cMarksInCell n c) * e.loc (cCsCell n c) [ZMOD 2013265921] :=
      (gate_modEq_iff (by ring)).mp hgg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
    rcases hin with h | h <;> rcases hcs with h' | h' <;> rw [h, h'] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases hin with h | h <;> rcases hcs with h' | h' <;> rw [hoeq, h, h'] <;> simp

/-- Every clash coordinate is in-bounds (it is some move's endpoint). -/
theorem cs_inbounds (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (coord : Coord)
    (hmem : coord ∈ clashCoords (boardDecodeOldN n (envAt t i))
      [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]) :
    coord.x < n ∧ coord.y < n := by
  have hv0 := legcMoveValid W hsat hc i hi 0 (Or.inl rfl)
  have hv1 := legcMoveValid W hsat hc i hi 1 (Or.inr rfl)
  rw [mem_clashCoords_pair] at hmem
  rcases hmem with ⟨ha, _, _⟩ | ⟨ha, _, _, _, _⟩
  · rw [← ha]; exact ⟨hv0.2.2.1.1, hv0.2.2.1.2⟩
  · rw [← ha]; exact ⟨hv0.2.2.2.1.1, hv0.2.2.2.1.2⟩

theorem marksOut_perm (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) :
    (marksListDecode n (cMarksOutCell n) (envAt t i)).Perm
      ((marksListDecode n (cMarksInCell n) (envAt t i)
         ++ clashCoords (boardDecodeOldN n (envAt t i))
              [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]).dedup) := by
  set e := envAt t i with he
  set cs := clashCoords (boardDecodeOldN n e) [moveDecodeN n e 0, moveDecodeN n e 1] with hcsdef
  refine (List.perm_ext_iff_of_nodup (marksListDecode_nodup n (cMarksOutCell n) e)
    (List.nodup_dedup _)).mpr ?_
  intro coord
  obtain ⟨x, y⟩ := coord
  rw [List.mem_dedup, List.mem_append, mem_marksListDecode_iff, mem_marksListDecode_iff]
  by_cases hb : x < n ∧ y < n
  · obtain ⟨hxn, hyn⟩ := hb
    have hcell : y * n + x < NGen.KK n := by
      simp only [NGen.KK]
      calc y * n + x < y * n + n := by omega
        _ = (y + 1) * n := by ring
        _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
    have hmodx : (y * n + x) % n = x := by
      rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hxn]
    have hdivy : (y * n + x) / n = y := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < n), Nat.div_eq_of_lt hxn, Nat.add_zero]
    have hcsmem : (envAt t i).loc (cCsCell n (y * n + x)) = 1 ↔ (⟨x, y⟩ : Coord) ∈ cs := by
      rw [hcsdef, csCell_iff_mem_clash W hsat hc i hi (y * n + x) hcell, hmodx, hdivy]
    rw [marksOr_cellEq hsat hc i hi (y * n + x) hcell]
    constructor
    · rintro ⟨-, -, hor⟩
      rcases hor with hIn | hCs
      · exact Or.inl ⟨hxn, hyn, hIn⟩
      · exact Or.inr (hcsmem.mp hCs)
    · rintro (⟨-, -, hIn⟩ | hCs)
      · exact ⟨hxn, hyn, Or.inl hIn⟩
      · exact ⟨hxn, hyn, Or.inr (hcsmem.mpr hCs)⟩
  · constructor
    · rintro ⟨hxn, hyn, -⟩; exact absurd ⟨hxn, hyn⟩ hb
    · rintro (⟨hxn, hyn, -⟩ | hCs)
      · exact absurd ⟨hxn, hyn⟩ hb
      · exact absurd (cs_inbounds W hsat hc i hi ⟨x, y⟩ hCs) hb

end Perm

/-! ## The seat table: `inClash`, and `lockedOut = 0` / `waitingOut = 1`. -/

section Seat
open Dregg2.Games.AutomataflRules (clashCoords carAt)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

/-- `cCsFrm[w]` / `cCsTo[w]` are the `cs` indicator at the move's endpoints. -/
theorem csEndpoint_iff (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1) :
    ((envAt t i).loc (cCsFrm n w) = 1 ↔ (moveDecodeN n (envAt t i) w).frm ∈
        clashCoords (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1])
    ∧ ((envAt t i).loc (cCsTo n w) = 1 ↔ (moveDecodeN n (envAt t i) w).to ∈
        clashCoords (boardDecodeOldN n (envAt t i))
          [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1])
    ∧ ((envAt t i).loc (cCsFrm n w) = 0 ∨ (envAt t i).loc (cCsFrm n w) = 1)
    ∧ ((envAt t i).loc (cCsTo n w) = 0 ∨ (envAt t i).loc (cCsTo n w) = 1) := by
  set e := envAt t i with he
  obtain ⟨⟨Yw, hYlt, hfyw, hrow⟩, ⟨Xw, hXlt, hfxw, hcol⟩⟩ := srcOneHots_of_sat hsat hc i hi w hw W.lt_p
  obtain ⟨⟨TYw, hTYlt, htyw, hdrow⟩, ⟨TXw, hTXlt, htxw, hdcol⟩⟩ :=
    destOneHots_of_sat hsat hc i hi w hw W.lt_p
  have hfrm : (moveDecodeN n e w).frm = (⟨Xw, Yw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [hfxw, hfyw]; simp
  have hto : (moveDecodeN n e w).to = (⟨TXw, TYw⟩ : Coord) := by
    simp only [moveDecodeN]; rw [htxw, htyw]; simp
  have hidxF : Yw * n + Xw < NGen.KK n := by
    simp only [NGen.KK]
    calc Yw * n + Xw < Yw * n + n := by omega
      _ = (Yw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hidxT : TYw * n + TXw < NGen.KK n := by
    simp only [NGen.KK]
    calc TYw * n + TXw < TYw * n + n := by omega
      _ = (TYw + 1) * n := by ring
      _ ≤ n * n := Nat.mul_le_mul (by omega) (le_refl n)
  have hmodF : (Yw * n + Xw) % n = Xw := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hXlt]
  have hdivF : (Yw * n + Xw) / n = Yw := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < n), Nat.div_eq_of_lt hXlt, Nat.add_zero]
  have hmodT : (TYw * n + TXw) % n = TXw := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hTXlt]
  have hdivT : (TYw * n + TXw) / n = TYw := by
    rw [Nat.mul_comm, Nat.mul_add_div (by omega : 0 < n), Nat.div_eq_of_lt hTXlt, Nat.add_zero]
  have hrdF : e.loc (cCsFrm n w) = e.loc (cCsCell n (Yw * n + Xw)) :=
    readAt_collapse hsat hc i hi (cCsFrm n w) (NGen.cSelRow n (NGen.mvBase n w))
      (NGen.cSelCol n (NGen.mvBase n w)) (cCsCell n) Yw Xw hrow hcol
      (mem_inClash hw (List.mem_cons_self))
  have hrdT : e.loc (cCsTo n w) = e.loc (cCsCell n (TYw * n + TXw)) :=
    readAt_collapse hsat hc i hi (cCsTo n w) (cTSelRow n w) (cTSelCol n w) (cCsCell n) TYw TXw
      hdrow hdcol (mem_inClash hw (List.mem_cons_of_mem _ (List.mem_cons_self)))
  have hcsBF : e.loc (cCsCell n (Yw * n + Xw)) = 0 ∨ e.loc (cCsCell n (Yw * n + Xw)) = 1 :=
    bin_of_gate (ngate hsat i hi (mem_cs (List.mem_append_left _
      (List.mem_map.mpr ⟨Yw * n + Xw, List.mem_range.mpr hidxF, rfl⟩)))) (canon_loc hc i _)
  have hcsBT : e.loc (cCsCell n (TYw * n + TXw)) = 0 ∨ e.loc (cCsCell n (TYw * n + TXw)) = 1 :=
    bin_of_gate (ngate hsat i hi (mem_cs (List.mem_append_left _
      (List.mem_map.mpr ⟨TYw * n + TXw, List.mem_range.mpr hidxT, rfl⟩)))) (canon_loc hc i _)
  refine ⟨?_, ?_, by rw [hrdF]; exact hcsBF, by rw [hrdT]; exact hcsBT⟩
  · rw [hrdF, csCell_iff_mem_clash W hsat hc i hi (Yw * n + Xw) hidxF, hmodF, hdivF, hfrm]
  · rw [hrdT, csCell_iff_mem_clash W hsat hc i hi (TYw * n + TXw) hidxT, hmodT, hdivT, hto]

/-- `inClash[w] = 1` when the move touches `cs`. -/
theorem inClash_one (W : BoardWindow n)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (w : Nat) (hw : w = 0 ∨ w = 1)
    (htouch : (moveDecodeN n (envAt t i) w).frm ∈ clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]
      ∨ (moveDecodeN n (envAt t i) w).to ∈ clashCoords (boardDecodeOldN n (envAt t i))
        [moveDecodeN n (envAt t i) 0, moveDecodeN n (envAt t i) 1]) :
    (envAt t i).loc (cInClash n w) = 1 := by
  set e := envAt t i with he
  obtain ⟨hfrmI, htoI, hfrmB, htoB⟩ := csEndpoint_iff W hsat hc i hi w hw
  have hgg := ngateH hsat i hi (mem_inClash hw
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))
  have hE : (headToExpr (orHead (cInClash n w) (cCsFrm n w) (cCsTo n w))).eval e.loc
      = e.loc (cInClash n w) + (-1) * e.loc (cCsFrm n w) + (-1) * e.loc (cCsTo n w)
        + e.loc (cCsFrm n w) * e.loc (cCsTo n w) := by
    rw [headToExpr_eval]
    simp only [orHead, evalH_addProd, evalH_addLin, evalH_lin, varsVal,
      List.foldl_cons, List.foldl_nil]
    ring
  rw [hE] at hgg
  have hval : e.loc (cInClash n w)
      = e.loc (cCsFrm n w) + e.loc (cCsTo n w) - e.loc (cCsFrm n w) * e.loc (cCsTo n w) := by
    have hmod : e.loc (cInClash n w)
        ≡ e.loc (cCsFrm n w) + e.loc (cCsTo n w) - e.loc (cCsFrm n w) * e.loc (cCsTo n w)
          [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hgg
    refine eq_of_modEq_canon (canon_loc hc i _) ?_ hmod
    rcases hfrmB with h | h <;> rcases htoB with h' | h' <;> rw [h, h'] <;>
      exact ⟨by norm_num, by norm_num⟩
  rcases htouch with hf | ht
  · have : e.loc (cCsFrm n w) = 1 := hfrmI.mpr hf
    rcases htoB with h | h <;> rw [hval, this, h] <;> norm_num
  · have : e.loc (cCsTo n w) = 1 := htoI.mpr ht
    rcases hfrmB with h | h <;> rw [hval, this, h] <;> norm_num

/-- `lockedOut[s] = 0`. -/
theorem lockedOut_zero (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (s : Nat) (hs : s = 0 ∨ s = 1)
    (hinc : (envAt t i).loc (cInClash n s) = 1) :
    (envAt t i).loc (cLockedOutBit n s) = 0 := by
  set e := envAt t i with he
  have hgg := ngateH hsat i hi (mem_seat hs (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))
  have hE : (headToExpr (((Head.lin 1 (cLockedOutBit n s)).addConst (-1)).addLin 1 (cInClash n s))).eval e.loc
      = e.loc (cLockedOutBit n s) + (-1) + e.loc (cInClash n s) := by
    rw [headToExpr_eval]; simp only [evalH_addLin, evalH_addConst, evalH_lin]; ring
  rw [hE, hinc] at hgg
  have hmod : e.loc (cLockedOutBit n s) ≡ 0 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hgg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_zero hmod

/-- `waitingOut[s] = 1`. -/
theorem waitingOut_one (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (i : Nat) (hi : i + 1 < t.rows.length) (s : Nat) (hs : s = 0 ∨ s = 1)
    (hinc : (envAt t i).loc (cInClash n s) = 1) :
    (envAt t i).loc (cWaitingOutBit n s) = 1 := by
  set e := envAt t i with he
  have hgg := ngateH hsat i hi (mem_seat hs (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))
  have hE : (headToExpr ((Head.lin 1 (cWaitingOutBit n s)).addLin (-1) (cInClash n s))).eval e.loc
      = e.loc (cWaitingOutBit n s) + (-1) * e.loc (cInClash n s) := by
    rw [headToExpr_eval]; simp only [evalH_addLin, evalH_lin]; ring
  rw [hE, hinc] at hgg
  have hmod : e.loc (cWaitingOutBit n s) ≡ 1 [ZMOD 2013265921] := (gate_modEq_iff (by ring)).mp hgg
  exact eq_of_modEq_canon (canon_loc hc i _) canon_one hmod

end Seat

/-! ## THE CAPSTONE: a satisfying Leg C trace IS `roundStep`'s `.again` transition. -/

section Capstone
open Dregg2.Games.AutomataflRules (RoundState RoundOutcome roundStep clashCoords carAt moveLegalB
  moveLegalB_iff GoalAssignment GameConfig clashCoords_pair_iff)
open Dregg2.Circuit.Emit.AutomataflLegCEmit (RoundStateAgrees roundStateDecodeIn roundStateDecodeOut
  freshSubsDecode legcMoveDecode marksListDecode lockedDecodeAt waitingDecodeAt)
open Dregg2.Circuit.Emit.AutomataflResolveCapstone (BoardWindow boardWindow_eleven boardWindow_two)

variable {hash : List ℤ → ℤ} {minit : ℤ → ℤ} {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}
  {n : Nat}

theorem legC_sat_imp_roundAgainN (W : BoardWindow n) (g : Dregg2.Games.AutomataflRules.GoalAssignment)
    (hsat : Satisfied2 hash (automataflLegCDescN n) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) :
    ∃ rs', roundStep ⟨.column⟩ g (roundStateDecodeIn n (envAt t 0)) (freshSubsDecode n (envAt t 0))
             = .again rs'
           ∧ Dregg2.Circuit.Emit.AutomataflLegCEmit.RoundStateAgrees rs'
               (roundStateDecodeOut n (envAt t 0)) := by
  set e := envAt t 0 with he
  have hi : (0 : Nat) + 1 < t.rows.length := by omega
  set bd := boardDecodeOldN n e with hbd
  set cs := clashCoords bd [moveDecodeN n e 0, moveDecodeN n e 1] with hcsdef
  -- IN seat pins
  have pin0 : ∀ col : Nat, cgH (Head.lin 1 col) ∈ (automataflLegCDescN n).constraints → e.loc col = 0 := by
    intro col hmem
    have hgg := ngateH hsat 0 hi hmem
    rw [← he] at hgg
    have hE : (headToExpr (Head.lin 1 col)).eval e.loc = e.loc col := rfl
    rw [hE] at hgg
    exact eq_of_modEq_canon (canon_loc hc 0 _) canon_zero ((gate_modEq_iff (by ring)).mp hgg)
  have pin1 : ∀ col : Nat, cgH ((Head.lin 1 col).addConst (-1)) ∈ (automataflLegCDescN n).constraints
      → e.loc col = 1 := by
    intro col hmem
    have hgg := ngateH hsat 0 hi hmem
    rw [← he] at hgg
    have hE : (headToExpr ((Head.lin 1 col).addConst (-1))).eval e.loc = e.loc col + (-1) := rfl
    rw [hE] at hgg
    exact eq_of_modEq_canon (canon_loc hc 0 _) canon_one ((gate_modEq_iff (by ring)).mp hgg)
  have hlockIn : ∀ s, s = 0 ∨ s = 1 → e.loc (cLockedInBit n s) = 0 := fun s hs =>
    pin0 _ (mem_seat hs (List.mem_cons_self))
  have hwaitIn : ∀ s, s = 0 ∨ s = 1 → e.loc (cWaitingInBit n s) = 1 := fun s hs =>
    pin1 _ (mem_seat hs (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))
  -- rs.locked = [] and rs.waiting = [0,1]
  have hrange2 : List.range LEGC_SEATS = [0, 1] := by decide
  have hLockedIn : lockedDecodeAt (cLockedInBit n) (cLockedInFx n) (cLockedInFy n) (cLockedInTx n)
      (cLockedInTy n) e = [] := by
    rw [lockedDecodeAt, hrange2]
    simp [hlockIn 0 (Or.inl rfl), hlockIn 1 (Or.inr rfl)]
  have hWaitingIn : waitingDecodeAt (cWaitingInBit n) e = [0, 1] := by
    rw [waitingDecodeAt, hrange2]
    simp [hwaitIn 0 (Or.inl rfl), hwaitIn 1 (Or.inr rfl)]
  -- both moves are legal
  have hlegalB : ∀ w, w = 0 ∨ w = 1 →
      moveLegalB bd (marksListDecode n (cMarksInCell n) e) (legcMoveDecode n e w) = true := by
    intro w hw
    rw [moveLegalB_iff]
    exact legcMoveLegal W hsat hc 0 hi w hw
  -- fresh = both moves
  have hfresh : freshSubsDecode n e = [legcMoveDecode n e 0, legcMoveDecode n e 1] := by
    simp only [freshSubsDecode, LEGC_SEATS]; rfl
  -- clash nonempty
  have hclashNe : cs ≠ [] := legc_clash_of_sat W hsat hc 0 hi
  -- dichotomy fork ∨ collide, hence both moves touch cs
  obtain ⟨_, _, hforkC, hcollC⟩ := legcForkCollide W hsat hc 0 hi
  have hgeom := (clashCoords_pair_iff (b := bd) (ma := moveDecodeN n e 0) (mb := moveDecodeN n e 1)).mp hclashNe
  have htouch : ∀ w, w = 0 ∨ w = 1 →
      (moveDecodeN n e w).frm ∈ cs ∨ (moveDecodeN n e w).to ∈ cs := by
    intro w hw
    rcases hgeom with ⟨heq, hne⟩ | ⟨heq, hne, ca, cb⟩
    · -- fork: both frms = shared ∈ cs
      left
      rw [hcsdef, mem_clashCoords_pair]
      rcases hw with rfl | rfl
      · exact Or.inl ⟨rfl, heq.symm, hne⟩
      · exact Or.inl ⟨heq, rfl, hne⟩
    · -- collide: both tos = shared ∈ cs
      right
      rw [hcsdef, mem_clashCoords_pair]
      rcases hw with rfl | rfl
      · exact Or.inr ⟨rfl, heq.symm, hne, ca, cb⟩
      · exact Or.inr ⟨heq, rfl, hne, ca, cb⟩
  have hinc : ∀ w, w = 0 ∨ w = 1 → e.loc (cInClash n w) = 1 := fun w hw =>
    inClash_one W hsat hc 0 hi w hw (htouch w hw)
  -- OUT seat bits
  have hlockOut : ∀ s, s = 0 ∨ s = 1 → e.loc (cLockedOutBit n s) = 0 := fun s hs =>
    lockedOut_zero hsat hc 0 hi s hs (hinc s hs)
  have hwaitOut : ∀ s, s = 0 ∨ s = 1 → e.loc (cWaitingOutBit n s) = 1 := fun s hs =>
    waitingOut_one hsat hc 0 hi s hs (hinc s hs)
  have hLockedOut : lockedDecodeAt (cLockedOutBit n) (cLockedOutFx n) (cLockedOutFy n)
      (cLockedOutTx n) (cLockedOutTy n) e = [] := by
    rw [lockedDecodeAt, hrange2]
    simp [hlockOut 0 (Or.inl rfl), hlockOut 1 (Or.inr rfl)]
  have hWaitingOut : waitingDecodeAt (cWaitingOutBit n) e = [0, 1] := by
    rw [waitingDecodeAt, hrange2]
    simp [hwaitOut 0 (Or.inl rfl), hwaitOut 1 (Or.inr rfl)]
  -- the Bool touch predicate for the spec filters
  have htouchB : ∀ w, w = 0 ∨ w = 1 →
      (cs.contains (legcMoveDecode n e w).frm || cs.contains (legcMoveDecode n e w).to) = true := by
    intro w hw
    rcases htouch w hw with h | h
    · rw [Bool.or_eq_true]; exact Or.inl (List.contains_iff_mem.mpr h)
    · rw [Bool.or_eq_true]; exact Or.inr (List.contains_iff_mem.mpr h)
  -- roundStep reduces to .again
  have hcsEmpty : cs.isEmpty = false := by
    cases h : cs.isEmpty with
    | false => rfl
    | true => exact absurd (List.isEmpty_iff.mp h) hclashNe
  -- the fresh filter keeps both moves
  have hfilt : List.filter
      (fun m => (([0, 1] : List Dregg2.Games.Automatafl.Pid).contains m.who)
        && moveLegalB (boardDecodeOldN n e) (marksListDecode n (cMarksInCell n) e) m)
      [legcMoveDecode n e 0, legcMoveDecode n e 1] = [legcMoveDecode n e 0, legcMoveDecode n e 1] := by
    apply List.filter_eq_self.mpr
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · show (([0, 1] : List _).contains (legcMoveDecode n e 0).who
        && moveLegalB (boardDecodeOldN n e) (marksListDecode n (cMarksInCell n) e)
          (legcMoveDecode n e 0)) = true
      rw [hlegalB 0 (Or.inl rfl)]; rfl
    · show (([0, 1] : List _).contains (legcMoveDecode n e 1).who
        && moveLegalB (boardDecodeOldN n e) (marksListDecode n (cMarksInCell n) e)
          (legcMoveDecode n e 1)) = true
      rw [hlegalB 1 (Or.inr rfl)]; rfl
  have hclashFold : clashCoords (boardDecodeOldN n e)
      [legcMoveDecode n e 0, legcMoveDecode n e 1] = cs := rfl
  have hRawLocked : List.filter (fun m => !(cs.contains m.frm || cs.contains m.to))
      [legcMoveDecode n e 0, legcMoveDecode n e 1] = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro m hm hpred
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [htouchB 0 (Or.inl rfl)] at hpred; simp at hpred
    · rw [htouchB 1 (Or.inr rfl)] at hpred; simp at hpred
  have hRawWaiting : ((List.filter (fun m => cs.contains m.frm || cs.contains m.to)
      [legcMoveDecode n e 0, legcMoveDecode n e 1]).map (·.who)).dedup = [0, 1] := by
    rw [show List.filter (fun m => cs.contains m.frm || cs.contains m.to)
        [legcMoveDecode n e 0, legcMoveDecode n e 1] = [legcMoveDecode n e 0, legcMoveDecode n e 1]
      from List.filter_eq_self.mpr (by
        intro m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl
        · exact htouchB 0 (Or.inl rfl)
        · exact htouchB 1 (Or.inr rfl))]
    rfl
  have hstepEq : roundStep ⟨.column⟩ g (roundStateDecodeIn n e) (freshSubsDecode n e)
      = RoundOutcome.again
          { board := boardDecodeOldN n e
          , marks := (marksListDecode n (cMarksInCell n) e ++ cs).dedup
          , locked := []
          , waiting := [0, 1] } := by
    rw [hfresh]
    unfold roundStep
    simp only [roundStateDecodeIn, hLockedIn, hWaitingIn, List.nil_append, hfilt, hclashFold,
      hcsEmpty, Bool.false_eq_true, if_false, hRawLocked, hRawWaiting]
  refine ⟨_, hstepEq, ?_⟩
  refine ⟨rfl, rfl, fun c => rfl, (marksOut_perm W hsat hc 0 hi).symm, ?_, ?_⟩
  · exact hLockedOut.symm
  · exact hWaitingOut.symm

/-- The capstone at the DEPLOYED board `n = 11`. -/
theorem legC_sat_imp_roundAgainN11 (g : Dregg2.Games.AutomataflRules.GoalAssignment)
    (hsat : Satisfied2 hash (automataflLegCDescN 11) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) :
    ∃ rs', roundStep ⟨.column⟩ g (roundStateDecodeIn 11 (envAt t 0)) (freshSubsDecode 11 (envAt t 0))
             = .again rs'
           ∧ Dregg2.Circuit.Emit.AutomataflLegCEmit.RoundStateAgrees rs'
               (roundStateDecodeOut 11 (envAt t 0)) :=
  legC_sat_imp_roundAgainN boardWindow_eleven g hsat hc hlen

/-- The capstone at the minimal `n = 2` (non-vacuous). -/
theorem legC_sat_imp_roundAgainN2 (g : Dregg2.Games.AutomataflRules.GoalAssignment)
    (hsat : Satisfied2 hash (automataflLegCDescN 2) minit mfin maddrs t)
    (hc : StepCanon t) (hlen : 1 < t.rows.length) :
    ∃ rs', roundStep ⟨.column⟩ g (roundStateDecodeIn 2 (envAt t 0)) (freshSubsDecode 2 (envAt t 0))
             = .again rs'
           ∧ Dregg2.Circuit.Emit.AutomataflLegCEmit.RoundStateAgrees rs'
               (roundStateDecodeOut 2 (envAt t 0)) :=
  legC_sat_imp_roundAgainN boardWindow_two g hsat hc hlen

end Capstone

#assert_axioms AutomataflLegCRefine.csCell_iff_mem_clash
#assert_axioms AutomataflLegCRefine.marksOut_perm
#assert_axioms AutomataflLegCRefine.legcMoveLegal
#assert_axioms AutomataflLegCRefine.legC_sat_imp_roundAgainN
#assert_axioms AutomataflLegCRefine.legC_sat_imp_roundAgainN11
#assert_axioms AutomataflLegCRefine.legC_sat_imp_roundAgainN2

end Dregg2.Circuit.Emit.AutomataflLegCRefine
