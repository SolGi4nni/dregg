# WIRE-3 — Lifting the partial-turn (ConditionalBatch) into the apex `FullActionA`

*Source-verified scope, 2026-06-24. The goal: make a FLOWING turn (a conditional / partial turn with
holes and `EventualRef` promises) covered by the light-client unfoolability apex — the SAME
unfoolability the atomic effects already have. This is the soundness floor reaching the liquid layer.*

The audit `docs/INTENT-FLUIDITY-AUDIT.md` §1f found the residual seam: the executable partial-turn
layer is **ALIVE-WIRED** to the real `RecChainedState` / `RecordKernel`, but rides a narrower op-set
than the apex the light client verifies. This doc maps that seam EXACTLY (against the code, not the
labels), states whether the smaller-than-feared path holds, gives the honest lift plan, and records
the first additive step taken.

---

## 1. The EXACT seam (verified against source)

Both executors run over the SAME substrate `RecChainedState` (`Exec/RecordKernel.lean:795`). The seam
is purely the **op-set vocabulary**:

| | Partial-turn layer | Apex (light-client-verified) |
|---|---|---|
| Action type | `FullAction` (`TurnExecutorFull.lean:298`) | `FullActionA` (`TurnExecutorFull.lean:2145`) |
| # ops | **5** | **~30** |
| Ops | `balance`, `delegate`, `revoke`, `mint`, `burn` | `balanceA`, `delegate`, `revoke`, `mintA`, `burnA`, `setFieldA`, `emitEventA`, `incrementNonceA`, `setPermissionsA`, `setVKA`, `setProgramA`, `introduceA`, `delegateAttenA`, `attenuateA`, `revokeDelegationA`, `exerciseA`, `createCellA`, `createCellFromFactoryA`, `spawnA`, `bridgeMintA`, `noteSpendA`, `noteCreateA`, `makeSovereignA`, `refusalA`, `receiptArchiveA`, `pipelinedSendA`, `cellSealA`, `cellUnsealA`, `cellDestroyA`, `refreshDelegationA`, `heapWriteA` |
| Balance model | single scalar | **per-asset** (`AssetId`) |
| Executor | `execFull` / `execFullTurn` (`:323`/`:333`) | `execFullA` / `execFullTurnA` (`:2512`/`:2896`) |
| Driven by | `Exec/ConditionalTurn.lean`, `Exec/GuardedHole.lean` | `FullForestAuth`, `recCexec`, the apex fold; what the light client's `verifyBatch` covers |

So `execConditionalTurn` (the topo-sort + `EventualRef` slot machinery) runs each batch node as a
`List FullAction` via `execFullTurn` — the 5-op set — **not** `FullActionA`. A conditional/partial
turn is therefore NOT yet inside the apex vocabulary the light client certifies. Closing the seam =
running (or refining) each batch node in the `FullActionA` vocabulary.

### The op-set is in TWO fragments, with DIFFERENT lift difficulty

The 5 partial-turn ops split cleanly:

- **Authority fragment — `delegate`, `revoke`.** Both `execFull` (`:326`/`:327`) and `execFullA`
  (`:2514`/`:2515`) dispatch to the **literally identical** chained primitives `recCDelegate` /
  `recCRevoke`. There is NO asset, NO projection, NO gate difference. The lift is **definitional
  (`rfl`)**: an authority action executed in the apex vocabulary commits to EXACTLY the same
  `RecChainedState`.
- **Value fragment — `balance`, `mint`, `burn`.** These do NOT lift `rfl`:
  - `balance`: `execFull` runs the SCALAR `recCexec s a.move` (`:324`) — no asset scope, no
    `acceptsEffects` gate. `execFullA .balanceA` runs the per-asset `recCexecAsset s t a` (`:2513`),
    which adds the `acceptsEffects s.kernel t.dst` gate (`:895`) and an asset-scoped balance check.
  - `mint`/`burn`: the receipt `src/dst` bookkeeping DIFFERS. Scalar `recCMint` writes a self-row
    `src=dst=cell` (`:281`); per-asset `recCMintAsset` writes the truthful issuer-move row `src=well a`,
    `dst=cell` (`:906`). The kernel deltas relate through the `projAsset` projection
    (`Intent/RingFFI.lean:89` `recKExec_projAsset_commits_iff`), but they are NOT byte-equal.

## 2. Is the hole ALREADY a nullifier? (the smaller-than-feared path)

The memory `project-partial-turn-promises` says "a promise-hole IS a nullifier; resolution = a spend;
the circuit ALREADY enforces the double-spend non-membership." Verifying the source: this is TRUE at
the **`Await` spec layer** (the one-shot continuation = a linear nullifier-style resource) but is NOT
how the **executable `GuardedHole`** binds:

- `Exec/GuardedHole.lean:48` `fillGuarded h s n := predStateStepGuarded h.guard s h.field h.actor
  h.target n` — a guarded **field write** (`stateStep` write gated by a `Pred` caveat), NOT a
  `noteSpendA` nullifier-set insert. The keystone `holeFill_binds_in_circuit` (`:59`) binds the **δ
  (the exact `stateStep` write) AND the guard** into the post-state — the predicate analogue of the
  cap-bridge, not the nullifier non-membership.
- The actual nullifier machinery is `noteSpendA` → `noteSpendChainA` (`TurnExecutorFull.lean:2574`),
  whose anti-replay is `EffectsPaired.noteSpend_no_double_spend` (`EffectsPaired.lean:449`).

**Verdict:** the hole-resolution is NOT (yet) literally a nullifier spend in the executable layer — it
is a guarded field write. The "hole IS a nullifier" identity is the *Await/promise* model's linearity
(one-shot continuation), realized executably as the eager-shape/lazy-witness guarded `put`. So the lift
canNOT simply "reuse the noteSpend non-membership" for hole-resolution; that reuse is a *possible
future unification* (route a `GuardedHole` fill through a nullifier so its one-shot-ness is the
double-spend gate), recorded below as an optional rung, not a free win. The genuinely-free win is the
AUTHORITY fragment (§3), which lifts with no new descriptor at all.

## 3. The lift plan, sized honestly

The lift has three rungs of increasing cost. None requires editing the apex/`FullActionA` core.

### Rung A — AUTHORITY fragment: FREE (definitional). **← first additive step, DONE.**
`delegate`/`revoke` lift `rfl`. An authority-only `ConditionalBatch` executes IDENTICALLY in the apex
executor `execFullTurnA`, so `condTurn_atomic` / `condTurn_dependency_sound` / `condTurn_conserves`
transport verbatim. No new descriptor, no new apex rung. **Done — see `Exec/ConditionalTurnLift.lean`.**

### Rung B — VALUE fragment at a fixed asset: a SMALL projection campaign.
Lift `balance`/`mint`/`burn` via `toA a` and prove `execFullA (toA a fa)` agrees with `execFull fa`
**modulo the `projAsset a` projection** (and the extra `acceptsEffects`/asset-balance gate, which is a
REFINEMENT — the apex is STRICTER, so an apex-accepted lift is a fortiori a scalar-accepted turn).
This is a real theorem over `projAsset` (the bridge already exists at the kernel level,
`recKExec_projAsset_commits_iff`), lifted to the chained layer + the receipt-row reconciliation
(scalar self-row vs per-asset issuer-row). Sizing: ~1 file, the chained-layer analogue of the existing
kernel projection lemma + a receipt-representation bridge. NOT an `rfl`; NOT a new descriptor either —
it reuses the per-asset `balanceA`/`mintA`/`burnA` descriptors the apex already verifies.

### Rung C — `ConditionalBatch` as a FIRST-CLASS apex `Effect` (the full lift).
For `verifyBatch` to cover a flowing turn directly (not just node-by-node), `ConditionalBatch` becomes
its own apex `Effect` with a descriptor + rung. The honest assessment: the batch's per-node steps are
ALREADY `FullActionA` turns once Rungs A+B land, and `execConditionalTurn`'s extra structure (the Kahn
topo-order + slot forwarding + all-or-nothing) is a PURE-CONTROL wrapper that touches no balance/cap
state of its own — every state move is a node's `execFullTurnA`. So the descriptor for a
`ConditionalBatch` effect is the **composition** of its nodes' (already-verified) descriptors under the
topo order, plus the `condTurn_dependency_sound` ordering witness. This is a COMPOSITION rung
(the same shape as the OPEN `∀ e, descriptorRefines` assembly in
`docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`), NOT a brand-new crypto floor. The hole/promise resolution
rides the slot environment, whose monotone forwarding (`runOrder_filled_stays`/`runOrder_fills`) is
proven; the one-shot linearity is the `Await` continuation (optionally unified with `noteSpendA`'s
nullifier set as a future hardening — see §2). Sizing: a real (but bounded) campaign — a composite
descriptor + an apex rung that folds the node descriptors under the proven topo order. It does NOT
need a new effect kind in `FullActionA` if the apex fold is taught to accept a node-list-with-edges as
a composite turn.

**Net honest verdict:** the lift is SMALLER than a from-scratch effect, because (i) the substrate is
already shared, (ii) the authority fragment is free, (iii) the value fragment is a projection over
descriptors the apex already has, and (iv) the batch wrapper is pure control whose state moves are all
already-verified node turns. It is NOT vacuous — Rung B is a genuine projection theorem and Rung C is a
genuine composition rung. We did NOT launder it as a one-line `rfl`.

## 4. The first additive step TAKEN (Rung A, proven)

`Dregg2/Exec/ConditionalTurnLift.lean` (new, additive; edits no apex/descriptor core):

- `FullAction.toA (a : AssetId) : FullAction → FullActionA` — the embedding of the 5-op partial-turn
  vocabulary into the apex vocabulary at a fixed asset.
- `execFullA_toA_eq_execFull_authority` — **THE BRIDGE.** For any authority op, the apex executor of
  its lift equals the partial-turn executor (`recCDelegate`/`recCRevoke` are the same primitive). The
  cap-graph evolution of a flowing conditional turn is, op-for-op, what the apex light client certifies.
- `execFullTurnA_lift_authority` — a whole AUTHORITY-ONLY `ConditionalBatch` node executes IDENTICALLY
  under the apex `execFullTurnA`. So the `ConditionalTurn` guarantees transport onto the apex executor.
- `liftBatch_node_agrees` — the batch-level per-node agreement (the fold's transport hook).
- `ledgerDeltaAsset_toA_authority_zero` — a lifted authority op is per-asset conservation-neutral at
  every asset (matching `condTurn_conserves` in the apex's per-asset measure).
- Non-vacuity: a real `delegate`-then-`revoke` authority batch lifts and executes identically (proven
  `example`s + `#guard`s); the fragment boundary fires (`isAuthority (.mint …) = false`).

All keystones are `#assert_axioms`-clean. `lake build Dregg2.Exec.ConditionalTurnLift` is GREEN.

**Scoped residual (named, with its lane):** the VALUE fragment (`balance`/`mint`/`burn`) lift is Rung
B above — a `projAsset` projection theorem + receipt-row bridge — NOT done here, deliberately not
claimed as `rfl`. Rung C (the composite `ConditionalBatch` apex rung) is the full closure. The next
additive step is Rung B for one value op (`balance`), reusing `recKExec_projAsset_commits_iff`.

---

*Method note: every claim carries a `file:line`; the executors were read at HEAD. The "hole IS a
nullifier" memory was checked against `Exec/GuardedHole.lean` source and found to be the Await-spec
linearity, NOT the executable fill (which is a guarded field write) — recorded honestly in §2 rather
than assumed.*
