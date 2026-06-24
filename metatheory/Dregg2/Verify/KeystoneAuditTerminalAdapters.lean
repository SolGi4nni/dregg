/-
# Dregg2.Verify.KeystoneAuditTerminalAdapters — the two `UniversalBridge` leaf/index adapters (WELDED).

The integrity guarantee (C) pins two adapter keystones the campaign once labelled
TERMINAL-CRYPTO-FLOOR:

  • `Exec.UniversalBridge.cap_leaf_value_codec` — the generic `Heap.leafOf` over the cap-cell value
    codec binds the FULL `(holder, target, rights, op)` tuple, under `Poseidon2SpongeCR hash`.
  • `Exec.UniversalBridge.index_boundary_mroot_derived` — the receipt-index MMR root reconstructed from
    the final index cells equals today's root (list canonicity; the `hash` is threaded through `MMR.mroot`
    but the proof uses NO collision-resistance at all).

NEITHER is terminal. The Wave-4 finding generalizes: `Poseidon2SpongeCR` is REALIZABLE by the concrete
proven-injective sponge `FloorsNonVacuous.encodeSponge` (`encodeSponge_cr`), and a canonicity adapter is
realizable trivially (any `hash` works). So both weld by supplying the realizable carrier + an honest
concrete instance, exactly as `published_position_pins_value` did:

  • `cap_leaf_value_codec` — satisfiable: `hash := encodeSponge`, equal tuples ⇒ equal generic leaves ⇒
    the conclusion `(h₁,t₁,r₁,o₁) = (h₂,t₂,r₂,o₂)` is EXERCISED (all four equalities fire). Teeth: the
    flat-leaf injective sibling `cap_leaf_flat_injective` over `encodeSponge` discriminates — DISTINCT
    tuples produce DISTINCT leaves, so the codec is not `:= True`.
  • `index_boundary_mroot_derived` — satisfiable: a concrete log `L := [7, 8]` and a `fin'` returning the
    log rows at positions `0, 1`, where `hsem` holds; the conclusion `mroot L = mroot (reconstructed)`
    FIRES (the reconstruction recovers `L`). Teeth: the reconstruction `boundaryCells` DISCRIMINATES — a
    `fin'` that DROPS a cell reconstructs a SHORTER list, so the boundary view is a real function of the
    final cells, not a constant.

`#assert_axioms` on every witness + re-pinned alias ⊆ {propext, Classical.choice, Quot.sound}. No
`native_decide`, no `sorry`. NEW file; imports are READ-ONLY (it owns only its own declarations).
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Exec.UniversalBridge
import Dregg2.Circuit.FloorsNonVacuous

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditTerminalAdapters

open Dregg2.Exec.UniversalBridge (capCellValue cap_leaf_value_codec cap_leaf_flat_injective
  index_boundary_mroot_derived indexRange)
open Dregg2.Crypto.UniversalMemory (boundaryCells)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.FloorsNonVacuous (encodeSponge encodeSponge_cr)
open Dregg2.Substrate.Heap (leafOf)

set_option autoImplicit false

/-! ## §1 — `cap_leaf_value_codec` — the generic cap-leaf binds the full tuple (WELDED). -/

/-- **`cap_leaf_value_codec_satisfiable`.** The conclusion FIRES on the realized carrier `encodeSponge`:
two EQUAL cap tuples `(1,2,3,4)` produce the same generic leaf (`heq` is `rfl`), so `cap_leaf_value_codec`
yields `1 = 1 ∧ 2 = 2 ∧ 3 = 3 ∧ 4 = 4` — the tuple-binding conclusion exercised on a concrete instance,
the `Poseidon2SpongeCR` hypothesis discharged by `encodeSponge_cr`. -/
theorem cap_leaf_value_codec_satisfiable :
    ((1 : ℤ) = 1 ∧ (2 : ℤ) = 2 ∧ (3 : ℤ) = 3 ∧ (4 : ℤ) = 4) :=
  cap_leaf_value_codec encodeSponge encodeSponge_cr
    (h₁ := 1) (t₁ := 2) (r₁ := 3) (o₁ := 4) (h₂ := 1) (t₂ := 2) (r₂ := 3) (o₂ := 4) rfl

/-- **`cap_leaf_value_codec_teeth`.** The cap-leaf codec DISCRIMINATES: distinct tuples produce DISTINCT
leaves under `encodeSponge` (the flat-leaf injective sibling, contrapositive) — so a leaf equality is a
real constraint, the codec is not `:= True`. Concretely, if the leaves of `(1,2,3,4)` and `(9,2,3,4)`
were equal, injectivity would force `1 = 9`, absurd. -/
theorem cap_leaf_value_codec_teeth :
    encodeSponge [1, 2, 3, 4] ≠ encodeSponge [9, 2, 3, 4] := by
  intro heq
  have h := cap_leaf_flat_injective encodeSponge encodeSponge_cr
    (h₁ := 1) (t₁ := 2) (r₁ := 3) (o₁ := 4) (h₂ := 9) (t₂ := 2) (r₂ := 3) (o₂ := 4) heq
  exact absurd h.1 (by decide)

/-! ## §2 — `index_boundary_mroot_derived` — the index-domain canonicity adapter (WELDED). -/

/-- A concrete final-index reader: positions `0, 1` carry the log rows `7, 8`, everything else `none`. -/
def finIdx : ℤ → Option ℤ := fun a => if a = 0 then some 7 else if a = 1 then some 8 else none

/-- The concrete index log the adapter reconstructs. -/
def Lidx : List ℤ := [7, 8]

theorem finIdx_hsem : ∀ i : Nat, (h : i < Lidx.length) → finIdx (i : ℤ) = some Lidx[i] := by
  intro i h
  match i, h with
  | 0, _ => rfl
  | 1, _ => rfl

/-- **`index_boundary_mroot_derived_satisfiable`.** The conclusion FIRES on the concrete index `Lidx =
[7,8]` with `finIdx` carrying its rows at positions `0,1`: the boundary cells reconstruct `Lidx`, so its
MMR root (under any `hash`, here `encodeSponge`) EQUALS the boundary-derived root — the canonicity
equation exercised on a real reader. -/
theorem index_boundary_mroot_derived_satisfiable :
    Dregg2.Lightclient.MMR.mroot encodeSponge Lidx
      = Dregg2.Lightclient.MMR.mroot encodeSponge
          ((boundaryCells finIdx (indexRange 0 Lidx.length)).map Prod.snd) :=
  index_boundary_mroot_derived encodeSponge finIdx_hsem

/-- **`index_boundary_mroot_derived_teeth`.** The boundary reconstruction DISCRIMINATES: a reader that
DROPS the first cell (`finDrop`, returning `none` at position `0`) reconstructs a SHORTER list than
`Lidx`, so the boundary view is a real function of the final cells — the adapter is not `:= True`. -/
def finDrop : ℤ → Option ℤ := fun a => if a = 1 then some 8 else none

theorem index_boundary_mroot_derived_teeth :
    (boundaryCells finDrop (indexRange 0 Lidx.length)).map Prod.snd ≠ Lidx := by
  decide

/-! ## §3 — TAG both adapters with their welded companions. -/

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTerminalAdapters.cap_leaf_value_codec_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTerminalAdapters.cap_leaf_value_codec_teeth]
def cap_leaf_value_codec_KS := @Dregg2.Exec.UniversalBridge.cap_leaf_value_codec

@[load_bearing_keystone
    satisfiable := Dregg2.Verify.KeystoneAuditTerminalAdapters.index_boundary_mroot_derived_satisfiable
    teeth := Dregg2.Verify.KeystoneAuditTerminalAdapters.index_boundary_mroot_derived_teeth]
def index_boundary_mroot_derived_KS := @Dregg2.Exec.UniversalBridge.index_boundary_mroot_derived

/-! ## §4 — RUN the audit (the CI gate over the two leaf/index adapters). -/

#keystone_audit Dregg2.Verify.KeystoneAuditTerminalAdapters.cap_leaf_value_codec_KS
#keystone_audit Dregg2.Verify.KeystoneAuditTerminalAdapters.index_boundary_mroot_derived_KS

#keystone_audit_tagged

/-! ## §5 — axiom-hygiene over the witnesses + re-pinned aliases (kernel-triple clean). -/

#assert_axioms cap_leaf_value_codec_satisfiable
#assert_axioms cap_leaf_value_codec_teeth
#assert_axioms index_boundary_mroot_derived_satisfiable
#assert_axioms index_boundary_mroot_derived_teeth
#assert_axioms cap_leaf_value_codec_KS
#assert_axioms index_boundary_mroot_derived_KS

end Dregg2.Verify.KeystoneAuditTerminalAdapters
