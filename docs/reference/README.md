# Subsystem reference

Per-subsystem reference docs grounded to `file:line` at HEAD — what each subsystem *is*, its key types/functions, and the Lean theorems backing its load-bearing claims. Start at [`docs/OVERVIEW.md`](../OVERVIEW.md) for the whole-system map and [`docs/KERNEL.md`](../KERNEL.md) for the verified kernel core; this index is the drill-down beneath them.

## Rust subsystems

- [cells.md](cells.md) — Cells & substances: the unit of sovereign capability-secure state (identity, signed-balance value, c-list, guarded state, lifecycle) folded into one canonical commitment.
- [turns.md](turns.md) — `dregg-turn`: the call-forest transaction subsystem — Turn → CallForest → Action → Effect, executed atomically with journaled rollback and a chained receipt.
- [umem.md](umem.md) — Universal memory: the witnessed key→value store whose committed root is its boundary — six domains, the init-binding keystone, per-cell heaps, the `Working` domain, composable umem-refs, and the time-travel / continuation revolutions.
- [services.md](services.md) — Cells as service objects: the userspace `InterfaceDescriptor` (not a committed field), the `invoke()` front door (no `Effect::Invoke`), the kvstore exemplar, and the Service Explorer.
- [circuit.md](circuit.md) — Descriptor circuit & light client: a turn proven as a batch STARK, folded into a constant-size recursive whole-chain aggregate, verified by a re-witnessing-nothing light client.
- [faithful-commitment.md](faithful-commitment.md) — The faithful state commitment (v9→v11): every Merkle-root component of the rotated commitment at 8-felt (~124-bit) via the shared node8 primitive, the cap-write family's shape-matched keystones (insert/remove/update), the accumulator INSERT keystone, the degraded-felt CI gate, and the named residuals.
- [persist.md](persist.md) — `dregg-persist`: the node's single durable redb store — crash-consistent commit log + index, torn-tail recovery, the Lean-verified recover = checkpoint ⊕ overlay model.
- [deos-view.md](deos-view.md) — `deos-view`: renderer extraction over one gpui-free `deos.ui.*` view-tree, with native gpui-component and web HTML renderers.
- [cockpit.md](cockpit.md) — starbridge-v2 shell: cap-first window manager, verified-scene compositor (three authority teeth), the shared_fork membrane, and the login/logout cap ceremony.
- [firmament.md](firmament.md) — Firmament & seL4: the cap-gradation bridge — one Capability handle dispatched to four backings over an emulated seL4 CNode kernel, with process-backed MMU isolation.
- [captp.md](captp.md) — CapTP / promises / conditional-turns: turns carried across federations by promise pipelining and STARK-conditional batches — pipelining grants latency, not authority.
- [wasm-web.md](wasm-web.md) — wasm & in-browser deos: two cdylib crates compiling the real verified substrate to wasm32 and driving it from a browser tab.
- [dsl-apps.md](dsl-apps.md) — DSL & apps: `dregg-dsl` (one constraint → eight backends), `dregg-app-framework` (cap-gated affordances), and `starbridge-apps` (native-primitive userspace apps).

## Lean theory

- [lean-kernel.md](lean-kernel.md) — The kernel spec: the l4v-shaped spec ⊑ design formalization — conservation algebra, the law layer, the fail-closed Exec machine, and Exec ⊑ Spec.
- [lean-authority.md](lean-authority.md) — Authority: "authority = production under non-forgeability" — the attenuation algebra, credential lifecycle, and the macaroon↔kernel-gate bridge.
- [lean-circuit.md](lean-circuit.md) — Circuit soundness / unfoolability: the apex `lightclient_unfoolable`, per-effect refinement, freshness, whole-history aggregation, and settlement soundness.
- [lean-conserve.md](lean-conserve.md) — Conservation & supply: the six-color linearity law, per-domain Σδ = 0 over an arbitrary value monoid, the four key theorems, and the `conserve` tactics.
- [lean-distributed.md](lean-distributed.md) — Distributed theory: the single-machine proofs reindexed over a topology — settlement soundness at the tip, the membrane, revocation, and joint turns.
