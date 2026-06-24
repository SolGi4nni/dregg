/-
# Dregg2.Verify.KeystoneAuditFreshness — the FRESHNESS family keystone-audit (guarantee D).

This module RUNS the `#keystone_audit` discipline (`Dregg2.Verify.KeystoneLint`) over the
freshness/anti-replay keystones pinned in `AssuranceCase`'s freshness guarantee — the no-double-spend
gate (`Argus.noteSpendStmt_*`), the sorted-neighbor non-membership bridge
(`Crypto.NonMembership.nonmembership_{sound,complete}`), and the stored-capability staleness gate
(`Apps.CapSlotFactory.*`). Each is a THEOREM, so the keystone-audit's two checks bite:

  [1] NON-VACUITY — each keystone carries a `*_satisfiable` companion (in its home module) that
      EXERCISES its conclusion on a concrete instance: a fresh nullifier spend COMMITS and excludes
      the spent value (`noteSpendStmt_*_satisfiable`), the absence `2 ∉ [1,3]` admits a real satisfying
      non-membership trace (`nonmembership_*_satisfiable`), a stored cap retrieves freshly under an
      unrevoked epoch (`stored_cap_*_satisfiable`, `no_forge_*_satisfiable`); and
  [2] TEETH — each carries a `*_teeth` companion REFUTING the predicate on a hostile instance: a REPLAY
      of a present nullifier is REFUSED (`noteSpendStmt_teeth`), a genuine MEMBER is not non-member
      (`nonmembership_*_teeth`), and a retrieval AFTER a revoke is REFUSED / an UNHELD payload cannot be
      stored (`stored_cap_*_teeth`, `no_forge_*_teeth`, `store_then_revoke_refused_*`).

`#keystone_audit` THROWS on any FAIL, so this module is a CI gate over the freshness family. The `_KS`
re-pinning aliases are written `:= <the keystone>` (the type is INFERRED from the keystone, so the
attribute attaches its companions without re-stating — and without editing the home modules).

ALSO covered here (the revocation-at-finality leg of guarantee D):
  • `Dregg2.Liveness.revocation_needs_consensus` — WELDED. A genuine forward implication
    (`CrossVatSound parties d view → (∀ v, view v d → d.agreeing v) → Consensus parties d`) whose
    conclusion `Consensus` is a two-valued predicate, so the keystone-audit checks bite: the
    satisfiable witness (`revocation_needs_consensus_satisfiable`) EXERCISES `Consensus` on a concrete
    two-vat agreeing revocation, and the teeth (`revocation_needs_consensus_teeth`) REFUTES `Consensus`
    on a unilateral revocation where one party did NOT agree — the contrapositive "revocation requires
    consensus" made concrete (drop one party's agreement and the conclusion collapses).

NOT covered here (out of this family's accept⟹produced shape):
  • `Dregg2.Liveness.dead_undecidable` — an IMPOSSIBILITY result (`¬ ∃ decider`, a halting reduction),
    not an `admit ⟹ produced` keystone; satisfiable/teeth do not apply (a satisfiable would contradict
    the theorem). It is an impossibility gate, a different discipline.
-/
import Dregg2.Verify.KeystoneLint
import Dregg2.Circuit.Argus.Effects.NoteSpend
import Dregg2.Crypto.NonMembership
import Dregg2.Apps.CapSlotFactory
import Dregg2.Liveness

open Dregg2.Verify.KeystoneLint

namespace Dregg2.Verify.KeystoneAuditFreshness

/-! ## §1 — TAG the freshness keystones with their companions (re-pinning aliases, type inferred). -/

/-! ### noteSpend family. -/

-- (1) NO-DOUBLE-SPEND (in the term).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.noteSpendStmt_no_double_spend_satisfiable
    teeth := Dregg2.Circuit.Argus.noteSpendStmt_teeth]
def noteSpendStmt_no_double_spend_KS :=
  @Dregg2.Circuit.Argus.noteSpendStmt_no_double_spend

-- (2) INSERTS.
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.noteSpendStmt_inserts_satisfiable
    teeth := Dregg2.Circuit.Argus.noteSpendStmt_teeth]
def noteSpendStmt_inserts_KS :=
  @Dregg2.Circuit.Argus.noteSpendStmt_inserts

-- (3) THEN-REJECT.
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.noteSpendStmt_then_reject_satisfiable
    teeth := Dregg2.Circuit.Argus.noteSpendStmt_teeth]
def noteSpendStmt_then_reject_KS :=
  @Dregg2.Circuit.Argus.noteSpendStmt_then_reject

-- (4) REPLAY-REJECTED (the conclusion IS a refutation; its teeth shows the rejection isn't `:= True`).
@[load_bearing_keystone
    satisfiable := Dregg2.Circuit.Argus.noteSpendStmt_replay_rejected_satisfiable
    teeth := Dregg2.Circuit.Argus.noteSpendStmt_replay_rejected_teeth]
def noteSpendStmt_replay_rejected_KS :=
  @Dregg2.Circuit.Argus.noteSpendStmt_replay_rejected

/-! ### non-membership bridge. -/

-- (5) NON-MEMBERSHIP SOUNDNESS.
@[load_bearing_keystone
    satisfiable := Dregg2.Crypto.NonMembership.Reference.nonmembership_sound_satisfiable
    teeth := Dregg2.Crypto.NonMembership.Reference.nonmembership_sound_teeth]
def nonmembership_sound_KS :=
  @Dregg2.Crypto.NonMembership.nonmembership_sound

-- (6) NON-MEMBERSHIP COMPLETENESS.
@[load_bearing_keystone
    satisfiable := Dregg2.Crypto.NonMembership.Reference.nonmembership_complete_satisfiable
    teeth := Dregg2.Crypto.NonMembership.Reference.nonmembership_complete_teeth]
def nonmembership_complete_KS :=
  @Dregg2.Crypto.NonMembership.nonmembership_complete

/-! ### stored-capability staleness. -/

-- (7) STORED-CAP FRESH-ONLY.
@[load_bearing_keystone
    satisfiable := Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked_satisfiable
    teeth := Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked_teeth]
def stored_cap_only_fresh_if_epoch_unrevoked_KS :=
  @Dregg2.Apps.CapSlotFactory.stored_cap_only_fresh_if_epoch_unrevoked

-- (8) NO-FORGE-FROM-STORAGE.
@[load_bearing_keystone
    satisfiable := Dregg2.Apps.CapSlotFactory.no_forge_from_storage_satisfiable
    teeth := Dregg2.Apps.CapSlotFactory.no_forge_from_storage_teeth]
def no_forge_from_storage_KS :=
  @Dregg2.Apps.CapSlotFactory.no_forge_from_storage

-- (9) REVOKE-STALES (the conclusion IS a refutation; teeth shows fresh commits).
@[load_bearing_keystone
    satisfiable := Dregg2.Apps.CapSlotFactory.store_then_revoke_refused_satisfiable
    teeth := Dregg2.Apps.CapSlotFactory.store_then_revoke_refused_teeth]
def revoke_stales_stored_cap_KS :=
  @Dregg2.Apps.CapSlotFactory.revoke_stales_stored_cap

-- (10) STORE-THEN-REVOKE-REFUSED (end-to-end staleness corollary).
@[load_bearing_keystone
    satisfiable := Dregg2.Apps.CapSlotFactory.store_then_revoke_refused_satisfiable
    teeth := Dregg2.Apps.CapSlotFactory.store_then_revoke_refused_teeth]
def store_then_revoke_refused_KS :=
  @Dregg2.Apps.CapSlotFactory.store_then_revoke_refused

/-! ### revocation-at-finality (the consensus-bound negative lifecycle). -/

-- (11) REVOCATION-NEEDS-CONSENSUS (welded: `Consensus` is exercised, and refuted on a unilateral view).
@[load_bearing_keystone
    satisfiable := Dregg2.Liveness.revocation_needs_consensus_satisfiable
    teeth := Dregg2.Liveness.revocation_needs_consensus_teeth]
def revocation_needs_consensus_KS :=
  @Dregg2.Liveness.revocation_needs_consensus

/-! ## §2 — RUN the audit (the CI gate over the freshness family). -/

#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.noteSpendStmt_no_double_spend_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.noteSpendStmt_inserts_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.noteSpendStmt_then_reject_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.noteSpendStmt_replay_rejected_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.nonmembership_sound_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.nonmembership_complete_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.stored_cap_only_fresh_if_epoch_unrevoked_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.no_forge_from_storage_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.revoke_stales_stored_cap_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.store_then_revoke_refused_KS
#keystone_audit Dregg2.Verify.KeystoneAuditFreshness.revocation_needs_consensus_KS

/-! ## §3 — axiom-hygiene over the re-pinned aliases (kernel-triple clean). -/

#assert_axioms noteSpendStmt_no_double_spend_KS
#assert_axioms noteSpendStmt_inserts_KS
#assert_axioms noteSpendStmt_then_reject_KS
#assert_axioms noteSpendStmt_replay_rejected_KS
#assert_axioms nonmembership_sound_KS
#assert_axioms nonmembership_complete_KS
#assert_axioms stored_cap_only_fresh_if_epoch_unrevoked_KS
#assert_axioms no_forge_from_storage_KS
#assert_axioms revoke_stales_stored_cap_KS
#assert_axioms store_then_revoke_refused_KS
#assert_axioms revocation_needs_consensus_KS

end Dregg2.Verify.KeystoneAuditFreshness
