import Dregg2.Circuit.Emit.EffectVmEmitRotationV3
import Dregg2.Circuit.Emit.RotatedLayout

/-
# RotatedLayoutBridge — the emit's hand-carried positions ARE the RotatedLayout projection

Phase 2b, non-invasive: rather than rewrite the DEPLOYED `EffectVmEmitRotationV3.*GroupCol` defs (which
risks moving a descriptor byte / VK), we PROVE each of the 7 group-cols equals `rotated178.groupCol`.
The verified `RotatedLayout` (whose `Legal` proof guarantees disjointness/bounds/alignment) is now the
PROVEN source of truth for the emit's faithful-8-felt geometry — WITHOUT changing a single emitted byte.

Next: pin the Rust producer mirror (`compute_rotated_pre_limbs`) to the same source, and (optionally)
refactor the emit defs to literally project — both are now proof-backed pure refactors. This retires the
producer↔circuit drift class that caused the revoked-root carrier bug.
-/

namespace Dregg2.Circuit.Emit

open Dregg2.Circuit.Emit.EffectVmEmitRotationV3

/-- Every deployed `*GroupCol` DERIVES from `rotated178.groupCol` at every lane — the emit geometry is
    the verified layout's projection, byte-for-byte unchanged. -/
theorem capRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    capRootGroupCol blockBase i = blockBase + (rotated178.groupCol .cap i).getD 0 := by
  unfold capRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem heapRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    heapRootGroupCol blockBase i = blockBase + (rotated178.groupCol .heap i).getD 0 := by
  unfold heapRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem fieldsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    fieldsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .fields i).getD 0 := by
  unfold fieldsRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem nullifierRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    nullifierRootGroupCol blockBase i = blockBase + (rotated178.groupCol .nullifier i).getD 0 := by
  unfold nullifierRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem commitmentsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    commitmentsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .commitments i).getD 0 := by
  unfold commitmentsRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem revokedRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    revokedRootGroupCol blockBase i = blockBase + (rotated178.groupCol .revoked i).getD 0 := by
  unfold revokedRootGroupCol; congr 1; fin_cases i <;> native_decide

theorem cellsRootGroupCol_eq_layout (blockBase : Nat) (i : Fin 8) :
    cellsRootGroupCol blockBase i = blockBase + (rotated178.groupCol .cells i).getD 0 := by
  unfold cellsRootGroupCol; congr 1; fin_cases i <;> native_decide

end Dregg2.Circuit.Emit
