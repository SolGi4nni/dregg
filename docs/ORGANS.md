# THE ORGANS — six service primitives, mostly welds

*(charter, 2026-06-11; sources: the in-tree census + the Spritely/KERI/Willow
resonance study. The finding that shapes everything: these capabilities are
not missing from the tree — they are built and disconnected. This is a
welding program, not a construction epoch.)*

## The parameterization discipline (standing design rule)

Where a design choice appears, do not collapse it: reify the choice as a
typed, legible parameter; instantiate the extremes as points; state the
theorems parametrically so every point inherits its laws. The parameter value
is itself state — set at a cell's birth, amendable under the governance
machinery — so moving along an axis is an administrative act, not a fork.
Precedents: the attestation dial (Disclosure × Transferability × Agreement),
finality tiers, proving modalities, Hosted↔Sovereign, topology
parameterization (n=1 as a point, not a different system).

Applied immediately below: **persistence is a per-collection axis** —
`attested` (inside the receipt discipline: recorded permanently,
conservation-grade, derivability invariant applies) · `retained(window)`
(attested for a challenge period, then prunable — the temporal algebra prices
it) · `prunable` (deletion is a guarded write: who may remove is law). Data
sits where its law put it.

## 1. Trustlines (one wave)

**Exists:** the shared-budget dynamics model (tau-resolution conservation,
rebalance conservation, the Byzantine overspend ceiling, golden-pinned);
two engines in coord/ (the verified Lean export resolves verdicts); the
executor's BudgetGate already seeded per-turn from the live coordinator in
the node's authoritative path; MCP check/debit tools; a payment-channel
demo (100 sub-second debits, epoch settle) on the same counter.

**The weld:** (a) the birth edge — an init path that funds a budget from a
real ledger debit (today `init_budget_coordinator` has zero callers; the
gate is always None); (b) the bilateral shape — "I extend you a line of N"
= an attenuated capability whose exercise debits the shared counter (the
StorageGatewayMandate volume-budget pattern is this exact shape, already
executor-enforced); (c) settlement — `rebalance_budgets` results applied
back to the ledger as moves. Lines of credit and payment channels are one
primitive at two settings.

## 2. Mailboxes (alive; finish the crank)

**Exists:** `dregg-node relay` — a complete hosted-inbox service (bonded
operators, send/drain/dequeue-proof routes, fees, GC) over the
storage-templates cell programs (CapInbox / ProgrammableQueue / PubSubTopic
/ BlindedQueue / RelayOperator), with Lean keystones (queue and inbox
factories) and executor-enforced sender authorization; the subscription
factory is seeded at boot; captp store-and-forward carries end-to-end
encrypted payloads.

**The weld:** seed the CapInbox factory at boot; add the crank — an SDK loop
that drains a mailbox and feeds messages to the owner's executor as deferred
turns. Delivery acceptance issues a custody receipt (the relay's dequeue
proofs are most of this), making store-and-forward accountable across
arbitrary delay — the delay-tolerant property comes free because turns are
self-certifying.

## 3. Storage (connect three existing pieces)

**Exists:** a content-addressed store with ownership/refcounting, quota
cells, metering, dedup, erasure coding — all unreachable from the node; a
verified storage-gateway-mandate cell (op allowlist, prefix scope, volume
budget with `sgm_volume_legal_forever`) seeded at boot and gating nothing;
the extension still calling the dead `/files/*` routes; seal-pairs with
epoch-freshness for encrypted payloads.

**The weld:** node routes for put/get whose admission is the mandate cell;
point the extension's existing calls at them. **Adopted from the resonance
study:** the read-cap / write-cap / verify-cap separation (hosts can prove
custody of, scrub, and replicate what they cannot read); the 3D area caveat
(subspace × path-prefix × time-range) as the storage capability's scope —
it is literal-atom material for the guard algebra; range-based set
reconciliation as the partial-sync shape, with our capability chains as the
pluggable authorization (the data-model parameterization is explicit in the
Willow design — adopt the geometry, keep our proofs). Persistence axis per
collection, per the discipline above.

## 4. Channels (the group-key lift)

**Exists:** pubsub topic cells with per-subscriber cursors and
membership-granting ops, seeded and shell-visible; point-to-point sealed
boxes; committee threshold decryption; SSE delivery.

**The design (from the earlier session):** a group is a CELL — membership
state and the group-key epoch commitment live on-cell; joins/removals are
turns under the group's program (the whole governance algebra applies to
membership). Message bodies never touch the chain: control plane on-cell,
data plane ciphertext over any transport including mailboxes. **The epoch
unification is the keystone:** the group's key epoch and the capability
freshness epoch are the same counter, so removing a member ends both their
ability to read forward and their use of group-held capabilities in one
step (the theorem-to-be: member removal ⇒ ciphertext and capability
darkness, one epoch step). RFC 9420 (MLS) is the candidate key-schedule
substrate; protocol frames as application messages make every room a
coordination surface (proposals, threshold shares, co-signing ceremonies
flowing where the conversation lives).

## 5. Adjudication (compose five built pieces)

**Exists:** equivocation evidence retained and propagated by the blocklace;
the admission registry's slash (called only from tests — the evidence→slash
pipe dead-ends, as CONSENSUS-FLEX admits); bonded escrow with slash paths
in the solver lane; council verdict machines with negative e2e tests; the
challengeWindow caveat; the obligation-factory pattern (bond in the cell's
own balance, slash = an ordinary move, no-double-resolve).

**The weld:** CONSENSUS-FLEX §7 items 1–2, already specified to the codec
level — the evidence object as a wire value, a predicate atom verifying it,
slash as a move from the bond well. The court's deep design rule (from the
Lawvere adjudication result): **witness-first** — where either party can
exhibit a verifying witness, the exhibit decides; tribunals enter only on
the non-certifiable residue. Jury selection wants organ 6.

## 6. Randomness (one shortcut, one organ)

**Exists:** commit-reveal at three layers (sealed auction with
no-late-switch keystones; causal-order anti-frontrunning; the preimage
gate); a probability model over beacon streams (consensus-liveness facing);
real BLS threshold signatures in the federation crate.

**WELDED** (`federation/src/beacon.rs`): a committee threshold-signature
beacon — `beacon_at(epoch, height)` under the `dregg-randomness-beacon-v1`
domain, verified by anyone holding the group public key; `deterministic_draw`
/ `select_jury` consumers. One correction discovered en route: the hinTS
aggregate in `threshold.rs` is SUBSET-DEPENDENT (different quorums yield
different all-verifying aggregates — right for quorum certificates, wrong
for a beacon, which would be grindable over C(n,t) subsets; pinned
executably by `hints_aggregate_is_subset_dependent_hence_not_a_beacon`).
The beacon therefore uses classical unique threshold-BLS (`σ = H(msg)^{f(0)}`,
same curve/hash-to-curve, Shamir-dealt group secret): every t-subset
produces the SAME signature — nothing to grind. Named upgrade path: DKG
replaces the dealer (no party ever holds f(0)), proactive resharing
anchored in epoch transitions, drand-style chaining. Commit-reveal among
named parties is a wave; a VRF-grade public beacon is its own later effort.

## Identity rider (from the resonance study, adopted outright)

**Pre-rotation**: every key-state event in an identity cell commits to the
digest of the NEXT, unexposed key set; rotation must exhibit the preimage.
Compromise of current keys no longer suffices to rotate. One register + one
guarded-write rule; composes with the recovery cooling period.

The kernel-side semantics is proven (`metatheory/Dregg2/Apps/PreRotation.lean`):
the `next_keys_digest` register + the rotate verb as a guarded write
(`stateStepGuarded` — authority/membership/liveness/slot-caveats compose for
free, so the council's threshold constitution gates rotation with no extra
wiring). Keystones: a rotation is admitted ONLY exhibiting the preimage of the
committed next-digest (`rotate_exhibits_preimage`); admission is a function of
the commitment alone — current keys do not occur in the guard
(`rotate_current_keys_irrelevant`, by `rfl`); under the named hash-CR carrier
(`KeySetCR`, dischargeable at the BLAKE3/Poseidon2 floor) any presented key set
other than the pre-committed one is refused (`rotate_compromise_resistant` —
an admitted forgery would BE a collision); the public commitment stream pins
the entire key history (`rotChain_pinned_by_commitments`). The cooling
composition strictly dominates either gate alone — pre-rotation removes the
attacker's ABILITY (no next-preimage ⇒ no admissible event at any height),
cooling removes their SPEED/STEALTH (even a preimage-holding event waits in
the open, visible to the council) — witnessed both ways
(`cooling_blocks_admitted_preimage` / `preimage_blocks_cooled_rotation`).

Also: the
identity cell's event history exports as an externally verifiable log
(KERI-shaped — chained, signed, witness-receipted by the federation), making
identity portable and independently checkable; the export is a contained
1–2 week artifact.

## Interop ladder (status)

dregg-auth standalone tokens (lane running) → portable receipt verifier
(wasm, planned) → OCapN netlayer adapter (bounded 2–4 week artifact: a
Goblins peer holding and exercising a dregg sturdy ref; adopt a netlayer
trait in captp regardless) → channels/RFC-9420 → KERI-shaped identity
export → SDK/MCP surfaces (landed).

## Order of work (post-epoch waves)

W-organ-1: trustline weld + mailbox crank + storage connect (all welds).
W-organ-2: adjudication composition + the beacon shortcut + pre-rotation.
W-organ-3: channels group-keys + the OCapN adapter + KERI export.
Each wave ends with its piece reachable from the shell and the SDKs.
