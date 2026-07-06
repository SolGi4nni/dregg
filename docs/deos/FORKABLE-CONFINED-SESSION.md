# Fork a confined session: the umem "scale IS fork" superpower on a live jailed agent

A grain's mind is a committed cell you own, so everything proven about cells
becomes true of the mind: it **checkpoints** (fold to one root), it **forks**
(one checkpoint → two diverging lives), and a write to one life never touches the
other (`grain-fork`, `docs/GRAIN-FORK.md`). A **confined** session is a jailed
agent body driven behind the grain's `AgentBrain` seam
(`grain-jail::ConfinedBrain`, `docs/deos/GRAIN-CONFINED-BODY.md`): its every
tool-call is cap-gated, metered against a prepaid budget, and receipted, and its
OS body reaches nothing but one granted egress door.

This document specifies the mechanism that makes those two facts one: **fork a
live confined session** — checkpoint its full state and split it into two
sovereign confined sessions, each its own jail, budget, caps, and receipt chain,
each *attenuated* from the parent and never amplified.

## Why a bare grain fork was not enough (the recorded gap)

Fork/checkpoint/rewind live on `grain-fork::Grain` — a committed mind cell + a
`hosted-lease::HostedLease`, with the proven settlement-sound branch-and-stitch.
The confined *drive* lives on `grain-jail::ConfinedBrain` (an `AgentBrain` over a
jailed body) and on `agent-platform::Tenant` (the brain-driven rent/session
state). The two never met: `Grain` models the mind, the budget, and the authority
(a c-list of `CellId` caps) — but **not** the jail's network egress surface, and
**not** the session's turn receipt chain. And `Tenant` persists only its *latest*
`SessionCarrier` (its `advance_checkpoint` overwrites the committed image via a
Monotonic cursor), so it has no checkpoint *history* to fork from.

So "fork a confined session" needed a type that is a confined session's full
state — mind + budget + caps + **egress confinement** + **receipt chain** — and
can checkpoint and fork it. That is `grain_fork::confined::ConfinedSession`.

## The four things a confined-session checkpoint captures

A `ConfinedSession` bundles the four pieces of a live confined session's state:

1. **The mind** — the grain's committed heap (working memory) + its c-list
   authority. Carried by the wrapped `Grain`; checkpointed to the grain's
   root-addressed timeline; copied byte-identically on a fork.
2. **The budget** — the prepaid reserve in the hosting `HostedLease` (the lease
   cell's funded balance). `session.budget()` reads it.
3. **The confinement** — the `Confinement`: the set of `host:port` egress doors
   the jailed body may reach, and nothing else. This is the piece a bare grain
   does not model; it is what makes a session *confined*.
4. **The receipt chain** — the ordered `Turn`s (label + metered cost) since the
   session's fork point, folded into a domain-separated hash chain rooted at that
   fork point. A confined body's audit trail, independently checkable.

## The fork: one checkpoint → two sovereign lives

`ConfinedSession::fork_two(self, spec_a, spec_b)` consumes the parent (the
checkpoint becomes the shared fork point; the two children ARE the two lives) and
yields two independent confined sessions. It is fail-closed on four teeth, each
of which bites in the tests (`grain-fork/src/confined.rs`):

### (a) Sovereign

Each child gets its **own** grain: its own `HostedLease` (own obligor — two forks
never share a lease), its own committed mind (same identity, diverging state),
its own `Confinement`, and its own receipt chain. Nothing is shared but the
provable common ancestor (the fork-point checkpoint root).

### (b) Attenuated, never amplified

- **Egress.** A child's doors must be a *subset* of the parent's confinement.
  `ConfinedForkError::EgressNotAttenuated` refuses a child asking for a door the
  parent never had. A fork cannot open a new hole in the jail.
- **Authority.** Each conferred cap must be one the parent actually holds — the
  underlying `Grain::fork` refuses an unheld cap
  (`GrainError::UnconferrableCap`). A fork mints no authority; a child starts from
  an empty c-list and receives only the deliberately-conferred subset.

### (c) Budget split, not duplicated (the conservation tooth)

The two children's budgets must **sum** to no more than the parent's budget at the
checkpoint. `ConfinedForkError::BudgetOverdraw` refuses `b_a + b_b > parent` (a
saturating sum, so a hostile `i64` cannot wrap under the ceiling). You cannot mint
budget by forking: the prepaid reserve is split across the two lives. Because the
parent is consumed, its budget is never double-counted — the checkpoint is the
ancestor, and the live budget now lives in the two children.

### (d) Independently verifiable + isolated

Each child's receipt chain is a fresh hash chain **rooted at the shared fork
root**: `link_i = H("grain-fork-confined-receipt-v1", link_{i-1} ‖ label ‖ cost)`,
with `link_0 = fork_root`. So:

- **Verifiable from the outside.** A third party recomputes a child's
  `receipt_head()` from `(fork_root, that child's turns)` alone — no access to live
  state. The chain binds label *and* cost (not a bare count): tampering with
  either, or with the fork root, changes the head.
- **Isolated.** A `record_turn` in one child writes only that child's mind and
  appends only that child's chain. It touches neither the other child's heap (umem
  isolation, inherited from `Grain::fork`'s cloned heap map) nor its receipt head.

## Where it lives, and the agent-platform follow-up

The mechanism is built on the grain/umem side, in `grain-fork` (module
`confined`), because that is where the proven fork/checkpoint/conservation
machinery already is — the confined session composes `Grain::fork` (mind + budget
+ authority conservation) and adds only the two teeth a grain does not have (the
egress-attenuation tooth and the budget-split tooth) plus the per-fork receipt
chain. No new crypto is invented: the mind conservation is `Grain::fork`'s, and
the receipt fold is the same blake3 the `grain-commons` pedigree uses.

The `agent-platform::Tenant` wire-up — making a rented, brain-driven `Tenant`
carry a `ConfinedSession` so the platform's `rent`/drive path forks directly, and
giving the `Tenant` the checkpoint *history* its single-`SessionCarrier`
persistence lacks — is the **named follow-up**. It is a shared agent-platform
file (another terminal's lane); the core mechanism here is complete and green
without it, and the `Tenant` becomes a thin adapter over `ConfinedSession` when
that lane opens.

## Try it

```
cargo test -p grain-fork confined
```

The headline test
`confined::tests::checkpoint_fork_two_sovereign_isolated_verifiable_sessions`
checkpoints a confined session, forks it into two lives with a 400k/600k budget
split and disjoint egress doors, then asserts each is sovereign, that a turn in
one touches neither the other's mind nor its receipt chain, that each head
recomputes from the shared fork root, and that the budgets sum to the parent's.
The refusal teeth are `fork_cannot_mint_budget`, `fork_cannot_amplify_egress`,
and `fork_cannot_mint_authority`.
