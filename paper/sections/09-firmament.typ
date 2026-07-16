// =============================================================================
// Section 9: The firmament
// =============================================================================

#import "../defs.typ": lean
= The firmament: one capability across a distance <sec-firmament>

The realization of @sec-realization is a userspace service today, but its
capability model does not stop at the process boundary. The *firmament* is the
substrate that holds applications, gives them a deterministic ground to run on,
and grants them capabilities under a single abstraction whose two backings --- a
local microkernel object and a distributed cell --- are the *same* capability
seen at two points on a distance parameter. This section is that unification and
the strong properties it earns at the near end.

== One capability, a distance parameter

A firmament capability is the handle of @sec-authority --- a `(target, rights)`
pair an application holds, invokes, attenuates, or delegates --- and its target
is one of three backings. A *local* target is a microkernel kernel object (a
capability slot, an endpoint, a frame): the invocation is a syscall, revocation
is synchronous, and the rights are kernel rights. A *distributed* target is a
cell on a (possibly remote) federation: the invocation is a turn through the
executor, revocation is the group-key epoch lift of @sec-realization, and the
rights are the grant attenuation of @sec-authority. A *surface* target is a cell
rendered as a window (@sec-deos); a window *is* a capability over a cell, so it
resolves by the same executor path as a distributed target.

The application does not see which backing it holds. It holds a capability and
invokes it; the firmament routes the invocation. The unification is not a slogan
but a theorem: the attenuation decision is the same `granted ⊆ held` gate
regardless of target (#lean("Firmament.attenuate_decision_backing_agnostic")), a
widening grant is rejected at *every* backing, the surface (window-share) case
included (#lean("Firmament.no_amplification"),
#lean("Firmament.no_amplification_surface")), and a surface is provably another
point on the same distance axis as a distributed cell, resolving through the same
gate and the same verb (#lean("Firmament.surface_is_another_point_on_n"),
#lean("Firmament.surface_gate_eq_distributed")). The verbs an application uses ---
invoke, attenuate, delegate --- do not depend on the distance
(#lean("Firmament.verbs_independent_of_n")); only the *bounds* on the operations
do. The Lean development is the data-refinement obligation for a runnable bridge
crate (`sel4/dregg-firmament/`) that path-depends on the genuine cell and turn
semantics, so its local mint and its distributed delegate gate on the same
attenuation predicate the kernel proves, with both polarities witnessed.

== The single-machine principle: what collapses at n = 1

The honest bounds on a distributed capability are *distance* bounds, parametrized
by the number of machines `n` the target is spread across. The firmament is the
place where `n = 1` --- everything is on one machine --- so those bounds collapse
to strong local properties rather than weakening into a degraded special case:

#figure(
  table(
    columns: (auto, auto, auto),
    align: (left, left, left),
    table.header([*operation*], [`n > 1` *(distributed)*], [`n = 1` *(firmament)*]),
    [revocation], [eventual --- the epoch lift must propagate],
      [immediate --- synchronous, dead when the call returns],
    [checkpoint], [a consistent cut across machines, possibly stale],
      [a consistent checkpoint of one domain's state, atomic],
    [commit], [quorum / finality latency], [synchronous --- one durable write],
    [agreement], [FLP-bounded, needs a round], [trivial --- one machine is its own quorum],
  ),
  caption: [The single-machine collapse. The same capability model; the distance
    parameter pinned to its minimum turns the distributed bounds into the strong
    local ones.],
)

The collapse is mechanized: the distributed bounds equal the strong-local bounds
at `n = 1` and relax above it (#lean("Firmament.distributed_collapses_at_one"),
#lean("Firmament.bounds_relax_above_one")), with the protocol-level precedent for
revocation specifically (#lean("Distributed.Revocation.single_machine_collapse")).
This is the single-machine principle made architectural: `n = 1` is not a
crippled subset but the *collapsed limit* of one model. A local deployment is a
first-class deployment, and the moment one of its programs invokes a capability
whose target lives on another machine, the same handle routes over the wire and
the program flows into distributed operation with no seam --- the same verbs, the
same receipts and proofs, only the bounds relaxing as `n` rises. The same binary
that runs at `n = 1` scales out without a rewrite, because there was only ever one
model.

== The deterministic ground

The firmament's second job is to make the applications it holds *deterministic
and reproducible* --- pure, with no hidden nondeterminism and no path to assert a
transition the kernel did not produce. The enforcement is structural rather than a
matter of application good behaviour. An application holds *only* the capabilities
the firmament minted for it, so ambient authority is absent: it cannot reach a
clock, a random source, another application's memory, a device, or the network
except through a capability handed to it, and a value like time or randomness it
does need is supplied as an *input to its turn*, recorded in the receipt, so it
enters the replayable transcript rather than as an ambient draw. Every action is a
turn through the verified executor; re-running the recorded turns from a
checkpoint reproduces the exact state, and that determinism is checked, not
trusted, because the executor is the verified entry of @sec-realization.

Checkpoint and restore are this determinism made portable. A snapshot is a
checkpoint plus an overlay --- a full state at a height cut, plus every cell
post-state committed after it --- and the recovery equation
`recover = checkpoint ⊕ overlay = replay` is a theorem for *any* cut, so where
one checkpoints is free (#lean("Distributed.CrashRecovery.recover_eq_replay")).
The integrity tooth is a claimed root carried with the snapshot and bound to the
chain's finalized commitment: the shipper never ships a snapshot whose
reconstructed root differs from its recorded root, the joiner recomputes the root
from `checkpoint ⊕ overlay` and refuses a mismatch, and a verified restore checks
the claimed root against a root it already trusts --- so a server cannot ship a
self-consistent snapshot of a *different* ledger. This is orthogonal to the
lifecycle *seal* of @sec-realization: seal pauses an application in place
(reversibly, by `unseal`); a snapshot ships its state with an unforgeable
self-attestation. A transparent move of a running application is
seal, ship, restore-verified, unseal.

== Status

The section's claims divide into theorems and running artifacts. The theorems
are the capability unification, the `n = 1` collapse, and the recovery
equation, each cited above to its Lean name. Three artifacts run.

The capability bridge runs against the real executor. The bridge crate
(`sel4/dregg-firmament/`) routes local and distributed invocations through the
attenuation gate the Lean development proves, and its tests exercise both
backings, including boot, isolation, and surface migration.

The snapshot model and its root tooth are live in the durable store
(`persist/src/snapshot.rs`). The shipper records the reconstructed root with
the snapshot; the joiner recomputes the root from `checkpoint ⊕ overlay` and
refuses a mismatch.

The executor protection domain runs. The verified entry the node calls ---
`dregg_exec_full_forest_auth`, the admission gate over `execFullForestG` ---
commits a turn inside a seL4 protection domain booted under
`qemu-system-aarch64` and emits the accepted receipt over serial. The boot
evidence and the build pipeline that produced it are in-tree
(`sel4/dregg-pd/executor-rootserver/`, `sel4/dregg-pd/executor-pd/`): the
proof closure recompiled to ELF under `leanc`, the Lean runtime rebuilt from
the toolchain's sources with its event-loop dependency excised, and GMP
cross-built for the target. The same executor is a Microkit protection domain
in the multi-PD assembly (`sel4/dregg.system`); its capability partition
grants the turn-input region read-only and the commit-output region
read-write, and no device capability. An ingress domain accepts a signed turn
over TCP, verifies the Ed25519 signature at the edge, and stages only an
accepted turn into the executor's input region (`sel4/dregg-pd/net-client/`).

The device edges that remain, surveyed at the current tree: the durable-store
domain holds its seat in the assembly but not yet a block-device capability,
so durable commit without leaving the assembly --- the store backend over a
raw block capability --- is open; the display domain scans out as the sole
holder of the display device capability, and the verified per-viewer
projection as that domain's render path is open (@sec-deos); the verifier
domain enforces the one-way executor-to-verifier edge through its capability
partition, and on-device checking of the deployed descriptor proofs is open
(@sec-sel4). @sec-sel4 takes up the protection-domain partition in full.
