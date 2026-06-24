# House Capacities — Weld Plan (verify-the-source census)

The dregg "house capacities" are the `cell/src/*.rs` capability prototypes that an
autonomous agent *living inside dregg* should be able to HOLD as first-class moves:
lock value (vault), trade atomically (escrow), carry a recurring duty (obligation),
hand a sub-agent bounded money (allowance), publish a verifiable view (derived),
compose two authorities (membrane), close a transfer ring (ring_closure), carry a
custom verifier (custom_effect), layer its VK (vk_v2), or attest a self-transition
(unilateral).

This plan answers ONE question per capability, from source (not from a label):
**is it a live move the protocol reaches, or a built-but-disconnected prototype, or
superseded by a wired thing?** It was written because a sibling census *overstated*
the Polis (calling a CI-enforced lakefile default-target "orphaned") — so every line
below is verified against the live `Effect` enums, the executor dispatch, the circuit
descriptors, and the Lean spec.

## The two facts that reshape the whole plan

1. **There is no per-capability `Effect`.** Neither the executor's vocabulary
   (`turn/src/action.rs:948` `enum Effect`) nor the circuit's
   (`circuit/src/effect_vm/effect.rs` `enum Effect`) contains a `Vault`, `Escrow`,
   `Obligation`, `Allowance`, `Derived`, `Membrane`, `Blueprint`, `RingClosure`, or
   `Unilateral` variant. The wired vocabulary is the dregg3 set — `Transfer`,
   `SetField`, `IncrementNonce`, `GrantCapability`, `RevokeCapability`,
   `SetPermissions`, `SetVerificationKey`, `CreateCell`, `CreateCellFromFactory`,
   `SpawnWithDelegation`, `Refresh/RevokeDelegation`, `NoteSpend/NoteCreate`, `Mint`,
   `Burn`, `BridgeMint`, `Introduce`, `PipelinedSend`, `ExerciseViaCapability`,
   `MakeSovereign`, `CellSeal/Unseal/Destroy`, `AttenuateCapability`, `ReceiptArchive`,
   `Refusal`, `EmitEvent`, and (circuit-only) `Custom`.

2. **Blueprint is the wired settlement route — and it SUPERSEDES standalone
   escrow/obligation/vault as a *family*.** `blueprint.rs` does not add an effect; it
   publishes per-deal `FactoryDescriptor`s whose `state_constraints` ARE the verified
   Lean state machines, settled by the already-wired
   `CreateCellFromFactory` + `Transfer` + `SetField` triple. The locked value lives
   in the minted cell's own `balance`; there is no side-table, so conservation is the
   ordinary kernel move law. This is live: `sdk/src/trustline.rs:159` builds a real
   turn `[Effect::CreateCellFromFactory { descriptor: trustline_factory_descriptor… },
   Effect::Transfer (fund), Effect::SetField (open)]`, and node services
   (`node/src/trustline_service.rs`, `channels_service.rs`, `dkg_service.rs`) drive it.
   The Lean twins are proved: `Dregg2/Apps/EscrowFactory.lean`,
   `ObligationFactory.lean`, `BridgeCell.lean`, with the falsification probe
   `Dregg2/Verify/EscrowFactoryProbe.lean` returning **PASS** (escrow-as-cell-program
   genuinely captures the kernel-verb semantics; the bespoke `k.escrows` side-table
   and its conservation theorems DISAPPEAR).

**Therefore the weld is not "add 11 effects."** It is: a few prototypes are already
alive; the standalone settlement prototypes (`escrow_sealed`, `obligation_standing`)
are *superseded by blueprint* and are NOT weld targets; and the genuinely-orphaned,
genuinely-weldable rooms (`vault`, `allowance`) weld the SAME way blueprint does —
as factory descriptors over the existing constraint vocabulary, **with no new
`Effect` variant and no VK change.**

---

## The census

| Capability | Status (file:line) | What an agent does with it | Weld shape + size |
|---|---|---|---|
| **blueprint** | **ALIVE-WIRED** `cell/src/blueprint.rs:1` → `sdk/src/trustline.rs:159` | Mint a conditional-settlement cell (escrow / obligation / bridge / trustline / channel / DKG) whose program enforces the deal; settle it with ordinary moves | — (this IS the route; vault+allowance should mirror it) |
| **escrow_sealed** | **SUPERSEDED** `cell/src/escrow_sealed.rs:1` (by `blueprint::EscrowTerms`/`escrow_factory_descriptor`, Lean `Apps/EscrowFactory.lean`, probe PASS) | Two-party atomic swap | NOT a weld target — a standalone heap-cell prototype the factory route replaces. Either delete or fold its `LegRequirement`/dual-leg shape into a blueprint `SwapTerms` descriptor if 2-asset-leg swaps aren't yet covered by `EscrowTerms` |
| **obligation_standing** | **ORPHANED, but in the blueprint FAMILY** `cell/src/obligation_standing.rs:1` | A *recurring* (every-PERIOD) duty — rent/subscription/tithe; distinct from blueprint's one-shot bonded `ObligationTerms` | Add a blueprint descriptor `standing_obligation_factory_descriptor` (recurring schedule via `Monotonic` cursor + `FieldGteHeight` due-gate) + a Lean `Apps/StandingObligation.lean` twin. **Small-medium, no new effect, no VK change.** Lower priority (recurring is a niche of the bonded case) |
| **vault** | **ORPHANED — top weld target** `cell/src/vault.rs:1`, `open_vault` (`:495`) has ZERO live callers | Lock value until a release rule (height OR preimage proof), claimable exactly once by the beneficiary — savings, vesting, a commitment device, a deadbolt fund | Write it AS a blueprint descriptor: `vault_state_constraints` over the heap slots it already uses (`set_heap` `VAULT_COLL`), gated by **existing** constraints `FieldGteHeight` (timelock) / `PreimageGate` (proof) / `WriteOnce`+`Monotonic` `settled` (claim-once). Settle via `CreateCellFromFactory` + `Transfer` (claim) + `SetField`. **Small, no new effect, no VK change.** Lean twin `Apps/Vault.lean` |
| **allowance** | **ORPHANED — 2nd weld target** `cell/src/allowance.rs:1`, `open_allowance` (`:452`)/`spend` (`:472`) have ZERO live callers | Hand a sub-agent rate-limited pocket money: spend up to `limit_per_epoch` per period, refills each period, can't over-drain or fake headroom | Write it AS a blueprint descriptor: epoch math is *derived from block height* (`epoch_of`, so early-refill is structurally impossible) → expressible with **existing** `RateLimit`/`RateLimitBySum` + `Monotonic` epoch cursor + `BoundedBy` headroom. Settle via factory + `Transfer` (spend out) + `SetField` (cursor). **Small-medium, no new effect, no VK change.** Lean twin `Apps/Allowance.lean` |
| **derived** | **ORPHANED** `cell/src/derived.rs:1`, `verify_derivation` (`:356`) has ZERO live callers (the `verify_derivation` hits in `circuit/` are a NAME COLLISION — the STARK IVC `cell::derivation`, not this materialized-view `cell::derived`) | Publish a cell whose committed state IS a verifiable function of other cells (`sum(balances)`, join/filter/count) — a light-client-checkable materialized view | This is a *read/query* face, not a value move. Weld is a cross-state binding in the circuit (the `cross_state_derivation` AIR exists) + a `DerivationSpec`-bound `SetField` whose value is constrained `== eval(spec)` via a new `StateConstraint::DerivedEquals`. **Medium, likely VK-affecting** (new cross-cell constraint in the AIR). Lower priority (read-only, not an agent-held authority) |
| **membrane** | **ORPHANED** `cell/src/membrane.rs:1`, `compose_both` (`:118`)/`SealedMembrane` (`:285`) have ZERO live callers | Compose two held caps A,B into a new cap C exercisable only by presenting BOTH — the *upward* (conjunction) dual of attenuation; the unit of ocap abstraction (a forwarder) | Weld is in the CAP layer, not the value layer: a `Membrane` cell + an authorization arm that requires presenting both inner facets, with the non-amplification floor (`compose_both` mask ⊆ A⊓B). Mirrors `ExerciseViaCapability` / `AttenuateCapability`. **Medium, VK-affecting** (new authorization predicate + circuit auth check). Higher *value* (genuinely new authority shape) but bigger than vault/allowance |
| **ring_closure** | **ASPIRATIONAL (Silver)** `cell/src/ring_closure.rs:1`, `silver` (`:280`) BLAKE3 commitment, no STARK; `RingClosureAttestation` has ZERO live callers | Attest that N parallel transfers form a closed cycle (coequalizer of the bilateral binding) — composable rings for apps | The bilateral binding is wired (`turn/src/bilateral_schedule.rs` `ExpectedBilateral` is consumed in `executor/proof_verify.rs`); ring_closure is its N-ary Silver sibling, BLAKE3-only ("Golden = STARK" deferred in-module). Weld = lift the cycle-closure into the accumulator the way bilateral is. **Medium-large, VK-affecting** (Golden). Low priority — Silver is a witness commitment, not yet a verified move |
| **custom_effect** | **PARTIALLY-WIRED** `cell/src/custom_effect.rs:188` `CustomEffectRegistry`; circuit `Effect::Custom` IS wired (`effect.rs:209`, columns `:475`, PI `CUSTOM_PROOFS_BASE`, `trace_rotated.rs:3053` lays the wide row); executor HOLDS the registry (`executor/mod.rs:721` + setter `:996`) | Register a `vk_hash → verifier` so a cell program can dispatch a domain-specific external proof as a first-class `Effect::Custom` | The circuit descriptor exists end-to-end; the **missing seam** is the executor's *consumption* — `custom_effect_registry` is set but never read back to verify a turn's `Effect::Custom` (the live `verify_custom_authorization` in `executor/authorize.rs` is the *predicate*-Custom path, a different Custom). Weld = wire the registry lookup+dispatch into the proof-verify arm. **Small (a dispatch seam, the descriptor already exists), not VK-affecting.** Good early win |
| **unilateral** | **ALIVE-WIRED (data + PI), accumulator-orphaned** `cell/src/unilateral.rs:1`; `turn/src/bilateral_schedule.rs:333` `unilateral_pi_tag`/`unilateral_salt` project into the circuit's `UNILATERAL_ATTESTATION_KIND_*` PI lanes (`circuit/src/effect_vm/pi.rs:538`); `cross_fed_cite.rs:43` builds attestations | A cell binding a property over its OWN transition without a counterparty (the 1-arity sibling of bilateral Transfer/Grant and trilateral Introduce) | The PI-tag/salt/build path is live and tested; the **accumulator** functions (`bilateral_schedule.rs:458` `push_unilateral`, `:470` `unilateral_root_for`) have NO live consumer — the bilateral path IS driven (`extract_from_pi` in proof_verify), the unilateral sibling is not folded into a turn yet. Weld = drive `push_unilateral` from the executor the way bilateral is. **Small, not VK-affecting** (PI lanes reserved) |
| **vk_v2** | **ASPIRATIONAL** `cell/src/vk_v2.rs:1`; `canonical_vk_v2`/`VerifierFingerprint`/`ProvingSystemId` have ZERO live callers; `VkComponents` appears only in a `circuit/src/air_descriptor.rs:13` DOC comment | A 4-component VK hash (program ∥ AIR fingerprint ∥ verifier fingerprint ∥ proving-system id) closing same-program-different-AIR / cross-proving-system collisions | The live VK path is the single-hash v1. Adopting v2 means changing how every `SetVerificationKey` / factory `child_program_vk` is computed — a **system-wide, VK-affecting** migration. **Large.** Not a weldable "room an agent holds" — it's a hardening of the VK *commitment scheme* itself. Out of scope for this plan |

---

## The blueprint-supersedes resolution (explicit, as asked)

**Blueprint SUPERSEDES standalone `escrow_sealed` and the one-shot half of obligation as a
settlement *family*, and it is the WIRED route.** It is NOT itself orphaned: it has a live
turn-builder caller (`sdk/src/trustline.rs`), live node services, and proved Lean twins with
a PASS falsification probe. The standalone `escrow_sealed.rs` heap-cell prototype is a *dead
prototype* (build + 15 smoke tests, no live caller) that the factory route replaces — do not
inflate it into a weld target.

The nuance: **blueprint covers the kernel-verb FAMILIES (escrow/obligation/bridge), not every
house room.** `vault` (timelock+preimage lock) and `allowance` (rate-limited budget) are
NOT in the escrow/obligation/bridge family — they are *new* conditional-settlement shapes.
But they weld the SAME way blueprint does, because they already use the SAME committed-heap
substrate (`set_heap`/`compute_heap_root`) and every constraint they need is ALREADY in the
`StateConstraint` / `SimpleStateConstraint` vocabulary (`cell/src/program/types.rs:915`):
`FieldGteHeight`/`FieldLteHeight` (timelock), `PreimageGate` (proof gate), `RateLimit` /
`RateLimitBySum` (the allowance ceiling), `Monotonic`/`StrictMonotonic` (cursors),
`WriteOnce`/`BoundedBy`/`BalanceDeltaLte`. So the vault/allowance weld is "re-express the
standalone `open_/claim/spend` library as a blueprint-style `*_state_constraints` +
`*_factory_descriptor`," riding `CreateCellFromFactory` + `Transfer` + `SetField`. **No new
`Effect`. No VK change.**

---

## Headline

**Genuinely un-wired and weldable rooms (in recommended sequence):**

1. **vault** — *weld FIRST.* Highest value × smallest. A pure value-lock every agent
   wants (savings/vesting/commitment-device/deadbolt), it already uses the heap substrate,
   and every gate it needs (`FieldGteHeight`, `PreimageGate`, claim-once) already exists.
   Weld = a blueprint-twin `vault_state_constraints` + `vault_factory_descriptor` + a
   `Dregg2/Apps/Vault.lean` twin + the `EscrowFactoryProbe`-style PASS probe. **No new
   effect, no VK change.**
2. **allowance** — *weld SECOND.* Same shape, slightly more arithmetic (epoch-derived
   rate-limit). The sub-agent-budget primitive that makes "hand an agent bounded money"
   real. `RateLimit`/`RateLimitBySum` already exist. **No new effect, no VK change.**
3. **custom_effect dispatch seam** — *cheap early win, parallel to 1–2.* The circuit
   descriptor and PI lanes are fully wired; only the executor's registry-lookup consumption
   is missing. Wiring it lights up first-class app-defined proofs. **Small, no VK change.**
4. **unilateral accumulator drive** — *small.* PI lanes + tag/salt + builder are live; only
   `push_unilateral`/`unilateral_root_for` lack a live consumer. Drive it from the executor
   the way bilateral already is. **Small, no VK change.**
5. **obligation_standing** — *medium, lower priority.* A recurring-schedule blueprint
   descriptor (a niche of the bonded obligation already in blueprint). No new effect.
6. **membrane** — *medium, VK-affecting, higher conceptual value.* A genuinely new authority
   shape (cap conjunction / forwarder, the dual of attenuation). Bigger because it touches
   the cap-authorization circuit, not just heap settlement.
7. **derived** — *medium, VK-affecting, lower priority.* A read/query face (materialized
   view), not an agent-held value move; needs a cross-cell `DerivedEquals` constraint in the
   AIR.
8. **ring_closure (Golden)** — *large, deferred.* Silver is a BLAKE3 witness commitment;
   Golden (STARK, accumulator-lifted) is the real weld and is module-deferred.

**Already-wired (verify-source wins, the Polis-style corrections):**
- **blueprint** is ALIVE-WIRED, not orphaned (live turn-builder + node services + proved Lean
  twins).
- **unilateral** is ALIVE on its data + PI-projection path (only the accumulator fold is
  un-driven).
- **custom_effect** is PARTIALLY-WIRED (full circuit descriptor + executor registry field;
  only the verify-dispatch seam is open).

**Do-not-weld (honest negatives):**
- **escrow_sealed** is SUPERSEDED (a dead standalone prototype; the factory route is the live
  escrow).
- **vk_v2** is ASPIRATIONAL — a hardening of the VK *commitment scheme*, a system-wide
  VK-affecting migration, not a room an agent holds.

**One sentence:** the only two genuinely-orphaned, genuinely-agent-held, genuinely-cheap
rooms are **vault** and **allowance**, and both weld as blueprint-style factory descriptors
over the EXISTING constraint vocabulary and the EXISTING `CreateCellFromFactory` +
`Transfer` + `SetField` path — no new `Effect`, no VK change — so vault is the recommended
first weld.
