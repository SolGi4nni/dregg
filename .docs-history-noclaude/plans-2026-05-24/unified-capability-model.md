# Unified Capability Model

## Status: PROPOSAL (2026-05-23)

## Problem Statement

The executor currently has four parallel authorization paths that each enforce
different subsets of the capability invariants:

1. **Signature/Proof path** (`verify_authorization` -> `check_single_auth_requirement`)
   - Checks: cell permissions, Ed25519 sig or ZK proof validity
   - Does NOT check: facets, expiry, revocation channels (those only live on c-list caps)

2. **Breadstuff/c-list path** (`check_breadstuff`)
   - Checks: actor's c-list has a cap with matching breadstuff hash pointing at target
   - Does NOT check: facets, expiry, revocation (just token-hash existence)

3. **Bearer delegation path** (`verify_bearer_cap`)
   - Checks: expiry, revocation channel, delegation proof (sig or STARK), delegator still holds cap, amplification
   - Does NOT check: facets (bearer caps have no allowed_effects field)

4. **ExerciseViaCapability path** (inline in `apply_effect`)
   - Checks: slot lookup, expiry, revocation channel (breadstuff-as-channel), target cell permissions, facet mask
   - This is the ONLY path that enforces facets

The consequence: the same capability can be exercised differently depending on
which authorization variant you use to present it. A cap with
`allowed_effects = FACET_TRANSFER_ONLY` is only enforced if you go through
`ExerciseViaCapability`. If you use `Authorization::Breadstuff` directly on an
action with `SetField` effects, the facet mask is never consulted.

---

## Part 1: The Unified Enforcement Function

### Core Insight

Authorization has two phases: **resolution** (turning what you presented into a
structured capability claim) and **enforcement** (checking that claim against
the target). The four paths differ in resolution but should share enforcement.

### The Model

Every authorization check answers three questions:
- **WHO**: prove you have authority (sig, STARK, c-list lookup, bearer delegation)
- **WHAT**: scope of authority (facet mask, target cell, action type)
- **STILL VALID**: not expired, not revoked

```rust
/// A resolved capability claim, regardless of how it was presented.
pub struct ResolvedCapability {
    /// The cell being acted upon.
    target: CellId,
    /// Permission level of the authority being exercised.
    permissions: AuthRequired,
    /// Facet restriction (which effect types are permitted).
    allowed_effects: Option<EffectMask>,
    /// Block height after which this authority expires.
    expires_at: Option<u64>,
    /// Revocation channel binding (if tripped, authority is void).
    revocation_channel: Option<[u8; 32]>,
    /// How the authority was demonstrated.
    proof_method: ProofMethod,
}

enum ProofMethod {
    /// Signature directly on the action (target cell's own key).
    DirectSignature,
    /// ZK proof verified against target cell's verification key.
    ZkProof { bound_action: String, bound_resource: String },
    /// Breadstuff token hash matched in actor's c-list.
    BreadstuffLookup { token_hash: [u8; 32], slot: u32 },
    /// C-list slot exercised via ExerciseViaCapability.
    CListExercise { slot: u32 },
    /// Bearer delegation chain proven (sig or STARK).
    BearerDelegation { chain_length: u32 },
    /// Presentation proof (ZK proof over attenuated token chain).
    PresentationProof { air_name: String },
}
```

### The Enforcement Function

```rust
fn enforce_capability(
    &self,
    resolved: &ResolvedCapability,
    target_cell: &Cell,
    effects: &[Effect],
    current_height: u64,
) -> Result<(), TurnError> {
    // 1. Expiry (uniform across all paths)
    if let Some(exp) = resolved.expires_at {
        if current_height > exp {
            return Err(TurnError::CapabilityExpired { ... });
        }
    }

    // 2. Revocation (uniform across all paths)
    if let Some(ref channel_id) = resolved.revocation_channel {
        if self.revocation_channels.is_tripped(channel_id) {
            return Err(TurnError::CapabilityRevoked { ... });
        }
    }

    // 3. Facet enforcement (uniform across all paths)
    if let Some(mask) = resolved.allowed_effects {
        if mask != 0 && mask != EFFECT_ALL {
            for effect in effects {
                let effect_bit = effect.effect_kind_mask();
                if effect_bit & mask == 0 {
                    return Err(TurnError::FacetViolation { ... });
                }
            }
        }
    }

    // 4. Target cell permission check (uniform)
    //    The resolved.permissions must satisfy the target cell's requirements
    //    for each effect's permission action.
    for effect in effects {
        if let Some((perm_action, action_name)) = effect.required_permission_action() {
            let required = target_cell.permissions.for_action(perm_action);
            if !resolved.permissions.satisfies(required) {
                return Err(TurnError::PermissionDenied { ... });
            }
        }
    }

    Ok(())
}
```

### Resolution Functions (one per path)

```rust
fn resolve_signature(action: &Action, target_cell: &Cell) -> Result<ResolvedCapability, TurnError> {
    // Verify Ed25519 sig... (existing logic)
    Ok(ResolvedCapability {
        target: action.target,
        permissions: AuthRequired::Signature,
        allowed_effects: None,      // Direct sig = full authority over that cell
        expires_at: None,           // Sigs don't expire (key rotation is separate)
        revocation_channel: None,   // No channel for direct ownership
        proof_method: ProofMethod::DirectSignature,
    })
}

fn resolve_zk_proof(action: &Action, target_cell: &Cell) -> Result<ResolvedCapability, TurnError> {
    // Verify ZK proof against VK... (existing logic)
    Ok(ResolvedCapability {
        target: action.target,
        permissions: AuthRequired::Proof,
        allowed_effects: None,      // TODO: derive from bound_action (see below)
        expires_at: None,
        revocation_channel: None,
        proof_method: ProofMethod::ZkProof { ... },
    })
}

fn resolve_breadstuff(actor: &Cell, token: &[u8;32], target: CellId) -> Result<ResolvedCapability, TurnError> {
    let cap = actor.capabilities.find_by_breadstuff(token, target)?;
    Ok(ResolvedCapability {
        target: cap.target,
        permissions: cap.permissions.clone(),
        allowed_effects: cap.allowed_effects, // FACETS NOW ENFORCED for breadstuff path
        expires_at: cap.expires_at,           // EXPIRY NOW ENFORCED for breadstuff path
        revocation_channel: cap.breadstuff,   // breadstuff IS the channel id
        proof_method: ProofMethod::BreadstuffLookup { token_hash: *token, slot: cap.slot },
    })
}

fn resolve_bearer(proof: &BearerCapProof, ledger: &Ledger) -> Result<ResolvedCapability, TurnError> {
    // Verify delegation chain... (existing logic)
    // NEW: look up delegator's cap to inherit facets
    let delegator_cap = find_delegator_cap(proof, ledger)?;
    Ok(ResolvedCapability {
        target: proof.target,
        permissions: proof.permissions.clone(),
        allowed_effects: delegator_cap.allowed_effects, // FACETS NOW FLOW THROUGH DELEGATION
        expires_at: Some(proof.expires_at),
        revocation_channel: proof.revocation_channel,
        proof_method: ProofMethod::BearerDelegation { chain_length: 1 },
    })
}

fn resolve_clist_exercise(actor: &Cell, slot: u32) -> Result<ResolvedCapability, TurnError> {
    let cap = actor.capabilities.lookup(slot)?;
    Ok(ResolvedCapability {
        target: cap.target,
        permissions: cap.permissions.clone(),
        allowed_effects: cap.allowed_effects,
        expires_at: cap.expires_at,
        revocation_channel: cap.breadstuff, // breadstuff doubles as channel
        proof_method: ProofMethod::CListExercise { slot },
    })
}
```

### What Changes

| Current behavior | Unified behavior |
|---|---|
| Breadstuff path ignores facet mask | Breadstuff path enforces facet mask |
| Breadstuff path ignores expiry | Breadstuff path checks expiry |
| Bearer caps have no facets | Bearer caps inherit delegator's facets |
| Direct sig/proof has no facet concept | Direct sig/proof = full authority (explicit None) |
| Four separate error paths | One enforcement function, one error surface |

---

## Part 2: E-Language Semantics Verdict

### Genuinely Useful (KEEP)

**1. Vat Isolation (cells communicate only via capabilities)**

This is the load-bearing architectural decision. Every security property flows
from it. Without isolation, there is no meaningful capability model. The cell
is the vat; the c-list is the only way to reach another cell.

Verdict: **Foundation. Non-negotiable.**

**2. Capability Confinement (authority can only be narrowed)**

Implemented as: facet attenuation (bitwise subset), permission narrowing
(`is_narrower_or_equal`), delegation chain verification. This is what makes the
system composable -- you can safely delegate a subset of your authority.

Verdict: **Essential. The unified model makes it actually consistent.**

**3. Facets (restricted views of objects)**

The `EffectMask` system is the right idea but currently under-enforced (only on
the `ExerciseViaCapability` path). The unified model fixes this. Facets are what
let you give someone "transfer-only access" to a cell without risking them
changing its state fields.

Verdict: **Useful, currently broken, unified model fixes it.**

**4. Three-Party Introduction**

`Effect::Introduce` -- Alice introduces Bob to Carol by giving Bob a capability
to Carol. This is the E-language pattern for secure capability transfer between
parties who don't directly know each other. Essential for composing multi-party
protocols without an ambient authority registry.

Verdict: **Useful, correctly implemented.**

### Partially Useful (SIMPLIFY)

**5. Eventual Sends / Pipeline Batching**

The module header in `eventual.rs` already says the quiet part loud:
> "This is NOT async promise pipelining in the E-language sense. All execution
> is synchronous and local."

What it actually provides: batched topological execution where later turns can
reference earlier turns' outputs. This IS useful -- it enables atomic multi-step
operations like "create a cell, then grant a cap to it" in a single submission.

But calling it "eventual" and "pipelining" creates false expectations. It's a
**turn batch with data-flow edges**. The semantics are:

- Submit N turns together
- They execute in topo order
- Earlier outputs feed into later inputs
- All-or-nothing atomicity (if `atomic = true`)

This is NOT promise pipelining because:
- There is no "waiting" -- everything resolves in one block
- There is no "remote" object -- everything is local ledger state
- There is no "partial failure with retry" -- it's all-or-nothing

Verdict: **The mechanism is useful. The naming is misleading. Rename
`Pipeline` -> `TurnBatch` (already aliased), drop the E-language pretense from
docs and comments. Keep the `EventualRef` -> `OutputRef` alias as the primary
name.**

**6. Sealer/Unsealer Pairs**

The cryptographic construction (X25519 + ChaCha20-Poly1305) is sound. But the
USE CASE overlaps confusingly with ZK proofs:

- Sealing hides a capability from the executor/federation (data privacy)
- ZK proofs hide the capability from the verifier (proof privacy)

When would you seal rather than prove?

Answer: **Partition tolerance.** If Alice wants to transfer a capability to Bob
and both are offline from the federation, she can seal it into a box that only
Bob can open. The federation never sees the transfer. This is the E-language
"offline delegation" pattern -- useful when the federation is unavailable or
untrusted for a specific transfer.

Verdict: **Useful for a specific threat model (federation-bypass delegation).
Not useful as a general privacy mechanism (ZK does that better). Keep but
document the specific use case. Do not expand.**

### Cargo-Culted (REMOVE OR RADICALLY SIMPLIFY)

**7. Promise Pipelining (as distinct from turn batching)**

`Effect::PipelinedSend` is syntactically present and functionally equivalent to
"submit a turn that depends on another turn." The inner action gets its
placeholders rewritten to resolved CellIds after the dependency executes. This
is just data-flow in the turn batch with extra steps.

The E-language distinction between `E.send(target, msg)` (eventual) and
`target.msg()` (immediate) is meaningless in a system where:
- All execution is synchronous within a block
- "Eventual" means "next turn in the same batch"
- There is no async event loop

Verdict: **Merge PipelinedSend into the OutputRef/dependency mechanism. Remove
the pretense that this is promise pipelining. A turn batch entry that says
"use the output of turn N" is simpler and more honest than
`Effect::PipelinedSend { target: EventualRef { ... }, action: Box<Action> }`.**

Concrete change: `PipelinedSend` becomes a turn-level dependency declaration
(which it already is via `depends_on`), not an effect. The "inner action"
becomes a regular action in a dependent turn.

**8. "Eventual" Terminology Throughout**

The word "eventual" in E means "message send that returns a promise, resolved
asynchronously by the event loop." In dregg, turns are synchronous and
deterministic. Using "eventual" is misleading.

Verdict: **Replace "eventual" with "deferred" or "output-dependent" in all
non-E-alignment documentation. Keep the type alias `OutputRef = EventualRef`
and make `OutputRef` primary.**

---

## Part 3: How ZK and Object-Capabilities Compose

### The Tension (Restated)

E says: **holding a reference IS authority.**
ZK says: **proving a property IS authority.**

These are not contradictory -- they are two REPRESENTATIONS of the same thing.
The question is: what IS the "thing"?

### The Resolution: Capability as Committed Fact

A capability is a **committed fact** in someone's state:

```
fact: has_cap(holder, target, permissions, facet, expiry)
```

This fact can be EXERCISED in two ways:

1. **Reveal-based** (E-style): "Look, it's in my c-list at slot 3."
   - The executor sees the full fact.
   - Simple, fast, no cryptography beyond the initial auth.
   - Reveals holder identity, target, permissions.

2. **Proof-based** (ZK-style): "I can prove the fact exists without showing it."
   - The executor sees only the proof's public inputs.
   - Expensive (proof generation), but private.
   - Reveals only what the proof's public inputs expose.

Both exercise THE SAME underlying authority. The difference is **information
disclosure**, not **authorization semantics**. The enforcement function doesn't
care HOW you demonstrated authority -- it only cares WHAT authority was
demonstrated.

### The Unified View

```
ResolvedCapability
    |
    |-- resolved via c-list lookup (reveals slot, target, permissions)
    |-- resolved via breadstuff match (reveals token hash)
    |-- resolved via bearer delegation (reveals chain endpoint)
    |-- resolved via ZK presentation proof (reveals only bound_action + resource)
    |
    v
enforce_capability() -- same function regardless of path
```

### Where ZK Adds Value (and Where It Doesn't)

ZK presentation proofs add value when:
- You want to prove authority WITHOUT revealing which specific capability you hold
- You want to prove attenuation chain without revealing intermediate parties
- You want selective disclosure (prove some facts, hide others)

ZK presentation proofs do NOT add value when:
- The executor needs to KNOW what effects you'll perform (it always does)
- The target cell needs to update its state (it always does)
- The action is publicly visible in the receipt anyway

This means: **ZK proofs are useful for the WHO question, not the WHAT question.**
You can hide who holds the authority and how they got it. You cannot hide what
they're doing with it (because the effects must be executed).

### The bound_action Problem

`Authorization::Proof { bound_action, bound_resource }` -- the prover commits to
an action string ("transfer", "read") and a resource string ("service-x",
"app-y"). But these are free-form strings with no connection to the `EffectMask`
system or the `AuthRequired` permissions model.

Resolution: **bound_action should map to a facet mask.** The proof commits to a
set of allowed effect types. The verifier extracts this as the
`allowed_effects` field of the `ResolvedCapability`. This connects the ZK path
to the same facet enforcement as the c-list path.

```rust
fn resolve_zk_proof(...) -> ResolvedCapability {
    // The proof's public inputs include a 32-bit facet mask commitment.
    // The prover committed to this mask when generating the proof.
    // The verifier extracts it from the public inputs.
    let facet_mask = extract_facet_mask_from_proof_public_inputs(&proof);

    ResolvedCapability {
        allowed_effects: Some(facet_mask),
        // ... bound_action becomes documentation, not enforcement
    }
}
```

This resolves the "contradiction" from Design Question 1: ZK proofs DO have
facets -- the facet mask IS a public input of the proof. You don't reveal which
SPECIFIC capability you hold, but you DO commit to what CATEGORY of effects
you're allowed to perform.

---

## Part 4: Design Questions Answered

### Q1: Should Authorization::Proof have facets?

**Yes.** The proof's public inputs include a committed facet mask. The prover
chooses which effects they're allowed to perform WHEN GENERATING THE PROOF, and
this choice is binding. The executor extracts the mask from public inputs and
enforces it uniformly.

The privacy guarantee is: you hide WHICH cap you hold and WHO delegated it.
The enforcement guarantee is: you cannot perform effects outside the committed
facet mask.

### Q2: Should all capabilities go through the c-list?

**No.** The c-list is one REPRESENTATION. The unified model says: all paths go
through `enforce_capability()`, but not all paths require c-list storage.

- C-list caps: persisted, looked up by slot, efficient for repeated use
- Bearer caps: ephemeral, proven per-turn, never stored
- ZK presentation: proven per-turn, never stored

The E-language principle "if I sent you a cap, you HAVE it" maps to: after a
`GrantCapability` effect, the cap IS in your c-list. But bearer caps and ZK
proofs are ways to EXERCISE authority without the cap being in your c-list --
you prove you COULD have it, or that someone who has it delegated to you.

### Q3: How do token caveats map to this model?

A macaroon with `service: "storage", action: "read"` becomes:

1. The token is committed via the presentation proof pipeline
2. The caveat restricts the derivable facts (Datalog evaluation)
3. The derivation trace proves `allowed(read, storage)` but not `allowed(write, storage)`
4. The proof's public inputs include a facet mask derived from what was proven:
   - `allowed(read, *)` -> `EFFECT_EMIT_EVENT` (read-only observation)
   - `allowed(write, *)` -> `EFFECT_SET_FIELD | EFFECT_EMIT_EVENT`
   - `allowed(transfer, *)` -> `EFFECT_TRANSFER`

The mapping from Datalog conclusions to facet masks is a fixed table configured
per federation (or per service). This bridges the semantic layer (what the
token "means") to the enforcement layer (what effects are permitted).

---

## Part 5: Implementation Plan

### Phase 1: Introduce ResolvedCapability (Non-Breaking)

**Files:** `turn/src/executor.rs`, new file `turn/src/resolved.rs`

1. Define `ResolvedCapability` and `ProofMethod` types
2. Define `enforce_capability()` function
3. Refactor `ExerciseViaCapability` to use resolve + enforce (it already does
   all the checks -- just restructure)
4. Add tests proving enforce_capability catches: expired, revoked, facet violation

This is pure refactoring of the ExerciseViaCapability path. No behavior change.

### Phase 2: Route Breadstuff Path Through Enforcement

**Files:** `turn/src/executor.rs`

1. Change `check_breadstuff` to call `resolve_breadstuff` -> `enforce_capability`
2. This ADDS enforcement of: facets, expiry, revocation on the breadstuff path
3. **Breaking change**: caps with `allowed_effects` that were previously
   exercisable via `Authorization::Breadstuff` on actions outside the mask will
   now be rejected

This is the most impactful change. Audit existing usage of
`Authorization::Breadstuff` to see if any rely on facet-bypass.

### Phase 3: Route Bearer Path Through Enforcement

**Files:** `turn/src/executor.rs`

1. Extend `BearerCapProof` to optionally carry `allowed_effects: Option<EffectMask>`
2. Change `verify_bearer_cap` to resolve to `ResolvedCapability` with inherited facets
3. Route through `enforce_capability`
4. **Breaking change**: bearer caps that previously could perform any effect on
   the target will now be limited to the delegator's facet mask

### Phase 4: Connect ZK Proof Path to Facets

**Files:** `turn/src/executor.rs`, `circuit/src/presentation.rs`

1. Add facet mask to presentation proof public inputs
2. The prover commits to a facet mask when generating the presentation
3. `resolve_zk_proof` extracts the mask from verified public inputs
4. Route through `enforce_capability`

This requires circuit changes -- the PresentationAir must include the mask as
public input and verify it's consistent with the derived authorization.

### Phase 5: Simplify Eventual/Pipeline Naming

**Files:** `turn/src/eventual.rs`, `turn/src/action.rs`, docs

1. Make `OutputRef` the primary type name (already aliased)
2. Deprecate `EventualRef` (keep as alias for back-compat)
3. Consider merging `PipelinedSend` into the `depends_on` + action targeting
   mechanism (the "inner action" becomes a regular action in a dependent turn
   with its target set to the OutputRef)
4. Update module doc to remove E-language claims about async/eventual semantics

### Phase 6: Document Sealer/Unsealer Scope

**Files:** `cell/src/seal.rs` docs, high-level architecture docs

1. Clearly document: sealers are for OFFLINE DELEGATION (federation-bypass)
2. They are NOT a general privacy mechanism (ZK proofs are better for that)
3. Use case: Alice and Bob are both offline, Alice seals a cap for Bob, Bob
   unseals later without the federation ever seeing the transfer
4. Anti-use-case: hiding data from the federation during normal online operation
   (use ZK presentation proofs instead)

---

## Summary Table

| E-language feature | `dregg` implementation | Verdict | Action |
|---|---|---|---|
| Vat isolation | Cell model | Correct, essential | Keep |
| Capability confinement | Facets + attenuation | Under-enforced | Fix via unified model |
| Facets | EffectMask | Only on ExerciseViaCapability | Enforce uniformly |
| Three-party introduction | Effect::Introduce | Correct | Keep |
| Eventual sends | Pipeline/TurnBatch | Misnamed, mechanism useful | Rename, simplify |
| Promise pipelining | PipelinedSend + OutputRef | Redundant with depends_on | Merge into batch deps |
| Sealer/unsealer | X25519 + ChaCha20 | Correct for specific use case | Document scope, keep |
| Object-capability model | C-list + reference = authority | Correct | Keep |
| ZK as authority proof | Presentation proofs | Sound but disconnected from facets | Connect via Phase 4 |

---

## Appendix: The Capability-as-Proof Thought Experiment

> Can we define a model where "holding a reference" and "proving a property"
> are the SAME THING?

Not literally. But we can define them as two PROJECTIONS of the same structure:

A **capability** is:
```
(holder, target, permissions, facet, expiry, revocation) + existence_proof
```

Where `existence_proof` is either:
- **Explicit**: "here it is in my c-list at slot N" (lookup)
- **Implicit**: "here is a proof that such a tuple exists" (ZK)

The `enforce_capability` function takes the tuple (minus the existence proof)
and does the same thing regardless. The proof method is METADATA for auditing,
not for enforcement logic branching.

This is the key architectural insight: **proof method selection is a privacy
decision, not a security decision.** All paths provide the same security
guarantees (expiry, revocation, facets, permissions). They differ only in what
information is revealed to the executor and the public receipt.
