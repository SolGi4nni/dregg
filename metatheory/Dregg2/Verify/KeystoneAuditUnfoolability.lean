/-
# Dregg2.Verify.KeystoneAuditUnfoolability — the UNFOOLABILITY family keystone-audit (guarantee E).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the light-client
unfoolability keystones pinned in `AssuranceCase`'s unfoolability guarantee:

  • the RECURSIVE-AGGREGATION light client (`Circuit.RecursiveAggregation.{light_client_verifies_whole_
    history, attested_history_conserves, conserves_from_verification, real_engine_sound,
    leaf_pairing_defeats_swap}`);
  • the HISTORY-AGGREGATION tooth (`Distributed.HistoryAggregation.{wellformed_attests_whole_history,
    verified_history_conserves, kernelChained_conserves, root_tooth_pins_kernel}`);
  • the light-client UC reduction (`Crypto.LightClientUC.{unfoolable_of_floor, fooling_breaks_floor,
    unfoolable_iff_not_foolable}`).

Each is a THEOREM, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — the hypothesis `verify agg.root = true` / `WellFormedChain` / `ExtractsTo+binding` is
      SATISFIABLE on a concrete instance: the honest 1-step chain over `teethGenesis` makes the light
      client FIRE (`light_client_fires_on_real_chain`, `honest_chain_wellformed`,
      `honest_kernelChained_conserves`), and the toy even/odd verifier makes the floor hold
      (`refUnfoolable`). These are concrete `def`+`decide`/structure witnesses — NOT vacuous.
  [2] TEETH — each carries a refutation on a hostile instance: a TAMPERED (reordered) aggregate cannot
      bind (`tampered_aggregate_cannot_bind`, concludes `False`), a broken seam is REJECTED
      (`tooth_rejects_broken_order`, concludes `¬ ChainBound`), and a FOOLING attack breaks the
      extractability floor (`refFoolingBreaksFloor`, concludes `¬ ExtractsTo`).

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate over the unfoolability family. The
`_KS` re-pinning aliases are `:= <the keystone>` (type inferred, home modules untouched).

NOT covered here (STOP-REPORT — satisfiable not cheaply witnessed):
  • `Circuit.Argus.Aggregate.{argus_strand_light_client, argus_strand_conserves}` — their hypothesis is
    `argusStrand g turns = some steps`, which requires stepping the Argus interpreter `interpChained` on a
    real command list to produce a concrete strand; no standalone concrete Argus strand instance exists,
    so the satisfiable would be a fresh, non-trivial interpreter run. Deferred. (Their TEETH
    `tampered_argus_strand_rejected` already exists, so only the satisfiable is the obstacle.)
  • `LightClientUC.SimAccepts` and the `Reference.refUnfoolable`/`refFoolingBreaksFloor` are themselves
    the concrete witnesses for the family above — they are not separately re-audited as keystones.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.RecursiveAggregation
import Dregg2.Distributed.HistoryAggregation
import Dregg2.Crypto.LightClientUC

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditUnfoolability

/-! ## §1 — TAG the unfoolability keystones with their companions (re-pinning aliases, type inferred). -/

/-! ### the recursive-aggregation light client. -/

-- (1) LIGHT-CLIENT VERIFIES WHOLE HISTORY.
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
def light_client_verifies_whole_history_KS :=
  @Dregg2.Circuit.RecursiveAggregation.light_client_verifies_whole_history

-- (2) ATTESTED HISTORY CONSERVES.
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_kernelChained_conserves
    teeth := Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order]
def attested_history_conserves_KS :=
  @Dregg2.Circuit.RecursiveAggregation.attested_history_conserves

-- (3) CONSERVES FROM VERIFICATION (the CRITICAL-3 closure).
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_kernelChained_conserves
    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
def conserves_from_verification_KS :=
  @Dregg2.Circuit.RecursiveAggregation.conserves_from_verification

-- (4) REAL-ENGINE-SOUND (the EngineSound carrier is inhabited).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
def real_engine_sound_KS :=
  @Dregg2.Circuit.RecursiveAggregation.real_engine_sound

-- (5) LEAF-PAIRING-DEFEATS-SWAP (a verifying leaf binds its own step).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.RecursiveAggregation.light_client_fires_on_real_chain
    teeth := Dregg2.Circuit.RecursiveAggregation.tampered_aggregate_cannot_bind]
def leaf_pairing_defeats_swap_KS :=
  @Dregg2.Circuit.RecursiveAggregation.leaf_pairing_defeats_swap

/-! ### the history-aggregation tooth. -/

-- (6) WELLFORMED ATTESTS WHOLE HISTORY.
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_chain_wellformed
    teeth := Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order]
def wellformed_attests_whole_history_KS :=
  @Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history

-- (7) VERIFIED HISTORY CONSERVES (the headline CRITICAL-3 closure).
-- ⚑ REPOINTED 2026-08-01 to the FLOOR-FREE twin. The registered keystone used to be
-- `verified_history_conserves`, whose four `compressInjective`/`compressNInjective`/`cellLeafInjective`
-- premises are REFUTED at deployed BabyBear width — so the instrument was certifying a VACUOUS
-- statement. The `_orBreak` form concludes the same conservation OR a concrete `StateBreakP`.
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_kernelChained_conserves
    teeth := Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order]
def verified_history_conserves_KS :=
  @Dregg2.Distributed.HistoryAggregation.verified_history_conserves_orBreak

-- (8) KERNEL-CHAINED CONSERVES.
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_kernelChained_conserves
    teeth := Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order]
def kernelChained_conserves_KS :=
  @Dregg2.Distributed.HistoryAggregation.kernelChained_conserves

-- (9) ROOT-TOOTH PINS KERNEL (CR root-recovery to kernel equality).
-- ⚑ REPOINTED 2026-08-01 to the FLOOR-FREE twin, same reason as (7): the injective form is vacuous at
-- deployed width, so the light client "genuinely learns the adjacent kernels coincide" only against a
-- hash nobody runs. `root_tooth_pins_kernel_orBreak` earns it at the real hash.
@[load_bearing_keystone
    satisfiable := Dregg2.Distributed.HistoryAggregation.honest_chain_kernelChained
    teeth := Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order]
def root_tooth_pins_kernel_KS :=
  @Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel_orBreak

/-! ### the light-client UC reduction. -/

-- (10) UNFOOLABLE OF FLOOR.
@[load_bearing_keystone
    satisfiable := Dregg2.Crypto.LightClientUC.Reference.refUnfoolable
    teeth := Dregg2.Crypto.LightClientUC.Reference.refFoolingBreaksFloor]
def unfoolable_of_floor_KS :=
  @Dregg2.Crypto.LightClientUC.unfoolable_of_floor

-- (11) FOOLING BREAKS FLOOR (the contrapositive — both polarities witnessed).
@[load_bearing_keystone
    satisfiable := Dregg2.Crypto.LightClientUC.Reference.refFoolingBreaksFloor
    teeth := Dregg2.Crypto.LightClientUC.Reference.refUnfoolable]
def fooling_breaks_floor_KS :=
  @Dregg2.Crypto.LightClientUC.fooling_breaks_floor

-- (12) UNFOOLABLE IFF NOT FOOLABLE.
@[load_bearing_keystone
    satisfiable := Dregg2.Crypto.LightClientUC.Reference.refUnfoolable
    teeth := Dregg2.Crypto.LightClientUC.Reference.refFoolingBreaksFloor]
def unfoolable_iff_not_foolable_KS :=
  @Dregg2.Crypto.LightClientUC.unfoolable_iff_not_foolable

/-! ## §2 — RUN the audit (the CI gate over the unfoolability family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.light_client_verifies_whole_history_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.attested_history_conserves_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.conserves_from_verification_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.real_engine_sound_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.leaf_pairing_defeats_swap_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.wellformed_attests_whole_history_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.verified_history_conserves_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.kernelChained_conserves_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.root_tooth_pins_kernel_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.unfoolable_of_floor_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.fooling_breaks_floor_KS
#keystone_audit Dregg2.Verify.KeystoneAuditUnfoolability.unfoolable_iff_not_foolable_KS

/-! ## §3 — axiom-hygiene over the re-pinned aliases (kernel-triple clean). -/

#assert_axioms light_client_verifies_whole_history_KS
#assert_axioms attested_history_conserves_KS
#assert_axioms conserves_from_verification_KS
#assert_axioms real_engine_sound_KS
#assert_axioms leaf_pairing_defeats_swap_KS
#assert_axioms wellformed_attests_whole_history_KS
#assert_axioms verified_history_conserves_KS
#assert_axioms kernelChained_conserves_KS
#assert_axioms root_tooth_pins_kernel_KS
#assert_axioms unfoolable_of_floor_KS
#assert_axioms fooling_breaks_floor_KS
#assert_axioms unfoolable_iff_not_foolable_KS

end Dregg2.Verify.KeystoneAuditUnfoolability
