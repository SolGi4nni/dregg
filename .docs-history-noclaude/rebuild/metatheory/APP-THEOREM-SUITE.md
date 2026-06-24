# The App Theorem Suite — what "a verified userspace app" means in dregg2

**Directive (ember, 2026-06-04):** dregg2's `Exec` must actually *run* userspace apps, AND we prove
*useful end-user theorems* about them — correctness, safety, liveness, privacy. An app is not "verified"
because its module is kernel-clean; it is verified when it (1) executes on the **real kernel**
(`RecordKernelState` + `execFullTurnA`/`execFullForestA`, NOT the `DemoRes` toy), and (2) carries the
end-user property theorems below, each with **teeth** (a discriminating counter-instance).

This is the anti-sprawl anchor: apps **reuse** the proved kernel/temporal scaffolding rather than
re-deriving it. Map every app property to one of the reusable keystones.

## The reusable palette (already proved, kernel-clean)

| Property class | Reusable keystone(s) | Module |
|---|---|---|
| **Conservation** (no mint/burn) | `recKExecAsset_conserves_per_asset`, `recKExecAsset_no_cross_asset_leak`, `execFullTurnA_conserves_per_asset`; (Intent side) `settle_sigma_conserves` | Exec/RecordKernel, Apps/SealedBidAuction |
| **Authority** (only authorized moves; no amplification) | `IsNonAmplifyingF` / granted ≤ held, `derive_no_amplify`, `recKDelegate_grants`/`heldCapTo` | Exec/EffectsAuthority, Exec/AuthTurn |
| **Atomicity / rollback** (all-or-nothing) | executor fail-closed (`execFullForestA … |>.getD s` = stutter), `escrow_conserves_across_pair` | Exec/FullForest, Exec/RecordKernel |
| **No double-spend** | `note_no_double_spend`, nullifier-set fail-closed | Exec/RecordKernel, Exec/NullifierCell |
| **Anti-frontrunning** (causal reveal-order) | `no_frontrunning`, `met_iff_frontrunExcluded`, causal `Deadline` | Apps/SealedBidAuction, Intent/* (Time) |
| **Liveness ◇** (eventually settles; no starvation) | `just_progress`, `AF_just` (just-paths), `loser_refunded_eventually`/`auction_loser_refunded`, `gst_liveness` | Proof/Fairness, Proof/CTLLiveness, Proof/GST |
| **Temporal safety/branching** | CTL (8 modalities), μ-calculus encodings, `livingAG_*` | Proof/CTL, Proof/MuCalculus |
| **Privacy / noninterference** | `lowEq` unwinding (balance = HIGH), `makeSovereign_leaks` teeth | Proof/Noninterference |
| **Resource ⊗ structure** | escrow monad, `exchange_sigma_conserves`, FLP weld | Intent/Centers, Apps/SealedBidAuction |

## The per-app checklist

Every app module should establish, on the **real kernel**:

1. **RUNS-ON-EXEC**: the app's turns are `FullActionA`/`execFullTurnA` programs over `RecordKernelState`
   (or a proven refinement of a `DemoRes` model into the kernel — see `Intent/KernelBridge`), not a bespoke
   toy transition. State: cells + `bal` ledger + escrows/nullifiers.
2. **CORRECTNESS**: the app delivers its specified outcome exactly when its precondition holds
   (an iff, not a one-way implication). Teeth: an off-spec input yields the off-spec result.
3. **SAFETY**: conservation (no mint) + authority (only authorized actors move only their assets) +
   atomicity (partial failure ⇒ pre-state unchanged). Each via the palette above; each with a teeth
   counter-instance (a mint / an unauthorized pull / a partial settle is REJECTED).
4. **LIVENESS ◇**: a well-formed, funded, authorized request *eventually* settles (under justness), and
   no party starves. Via `just_progress`/`AF_just` + an app-specific enabledness witness.
5. **PRIVACY** (where the app is confidential, e.g. sealed-bid): noninterference at balance = HIGH.

## App roster (toward "real complex userspace apps")

- **AtomicSwap** (in flight) — multi-party atomic escrow swap on the real `bal` ledger. Has: conservation,
  atomicity, authority. TODO after landing: a **liveness** theorem (a fully-escrowed, authorized swap
  eventually settles) + a **correctness** iff (each party gets its wanted iff all legs match).
- **SealedBidAuction** (committed, on `DemoRes`) — has anti-frontrunning, Σ-conservation, loser-refund
  liveness. TOY to remediate: lift it to run on the real kernel via `Intent/KernelBridge`; add the
  sealed-bid **privacy** theorem (noninterference, balance = HIGH).
- **NameRegistry** (proposed) — register/transfer/revoke names; safety = unique ownership + only-owner
  transfers (authority), liveness = a valid claim eventually registers, correctness = lookup reflects the
  last committed write. Exercises caps + delegation + revocation.
- **Subscription** (proposed) — recurring entitlement with revocation; safety = no charge after revoke
  (the revocation keystone), liveness = an active sub eventually renews, conservation across charges.
- **Vault / escrow-marketplace** (proposed) — generalize AtomicSwap to standing offers + partial fills;
  reuses `exchange_sigma_conserves` + the escrow monad.
- **DAO vote / multi-party agreement** (proposed) — ties to the hyperdoctrine: agreement = a limit;
  safety = only enfranchised caps vote once (no double-vote = nullifier), correctness = the tallied
  outcome is the argmax, liveness = a quorum'd proposal eventually resolves.

## Discipline

Reuse the palette; don't re-derive. Run on the real kernel or prove the `DemoRes→kernel` refinement.
Every safety/liveness claim gets a teeth counter-instance. `#assert_axioms`-pin keystones. Gate the full
build + read bodies before commit (verify-don't-trust). A module isn't "a verified app" until it RUNS and
its end-user theorems hold with teeth.
