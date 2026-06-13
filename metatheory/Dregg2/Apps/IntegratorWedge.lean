/-
# Dregg2.Apps.IntegratorWedge — the integrator-wedge app lane (aggregator).

This lane refutes the "lamesauce" critique ("you can't build apps that don't scream 'I am a
toy'") with TWO genuinely real userspace apps that exercise the FULL landed cell-program
expressiveness (`Exec/Program.lean`'s `admitsCtx`: turn-sender binding, balance gates, affine
arithmetic, the `countGe` M-of-N quorum with its anti-aliasing `eraseDups` design, the
`preimageGate` knowledge gate, the actor-bound Heyting composite) AND the async `notify` cap
algebra (`Firmament/NotifyAuthority.lean`). Each app has a non-vacuous theorem suite (accept AND
reject/UNSAT teeth) and is `#assert_all_clean`.

  * **`AgentOrchestrationBudget`** — the integrator wedge as ONE dispatch-board cell program: the
    six primitives buildr/builders/sig/simbi each hand-rolled UNGATED (cap-gated authority, signed
    provenance, atomic budget, atomic handoff, surfaces-as-caps, async notify wake), each now a
    constraint or a cap, each refusal a theorem. Teeth: a forged handoff is UNSAT
    (`forged_dispatch_rejected`); an over-budget runaway is refused (`over_budget_rejected`); a
    stolen baton is UNSAT (`stolen_baton_rejected`); a replay is UNSAT (`replayed_dispatch_rejected`);
    a worker cannot widen its reach (`worker_cannot_widen_reach`); an un-capped wake is rejected
    (`uncapped_wake_rejected`) — while the honest dispatch + capped wake COMMIT.

  * **`EscrowDeskCouncil`** — an M-of-N council-governed escrow desk: a release demands a council
    quorum (`countGe`, duplicate-padded approvers COLLAPSE), a secret reveal (`preimageGate`), a
    drained balance (`balanceLe`, no stranded value), and operator provenance (`senderInField`).
    Teeth: a forged (duplicate-padded) quorum is UNSAT (`forged_quorum_rejected`); a wrong reveal
    is UNSAT (`wrong_reveal_rejected`); a stranded-value resolve is UNSAT (`stranded_value_rejected`);
    a non-operator turn is UNSAT (`non_operator_rejected`) — while the faithful release COMMITS.

Both sit beside the EXISTING orchestration apps — `AgentOrchestration` (the kernel-executor swarm:
real transfers + attenuated delegation + the credential gate) and `SwarmSignal` (the async notify
demo). This lane adds the POLICY layer those two lacked: the orchestration board and the escrow
desk as cell PROGRAMS the executor enforces on every turn.

`lake build Dregg2.Apps.IntegratorWedge` pulls both apps + their proofs.
-/
import Dregg2.Apps.AgentOrchestrationBudget
import Dregg2.Apps.EscrowDeskCouncil

namespace Dregg2.Apps.IntegratorWedge

/-! This module is a pure aggregator: it re-exports the two apps' namespaces so a downstream
consumer can `import Dregg2.Apps.IntegratorWedge` and reach both. The verification lives in the
imported modules (each `#assert_all_clean` at its close). -/

end Dregg2.Apps.IntegratorWedge
