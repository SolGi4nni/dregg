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

end Dregg2.Circuit.Emit.AutomataflLegCRefine
