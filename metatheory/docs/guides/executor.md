# Guide: The Executor & Effect Model

*A newcomer's orientation to the verified state-transition machine — what a turn is, how an effect
executes, where the ONE entry point lives, and how soundness is proved.*

See also: [`../NAVIGATION.md`](../NAVIGATION.md) · [`circuit.md`](circuit.md) ·
[`authority.md`](authority.md) · [`../../README.md`](../../README.md).

---

## The one-sentence model

A **turn** is an atomic batch of **effects** applied to one or more **cells**. The executor is a
*fail-closed* function `(state, turn) → Option state'`: it returns `some state'` only if the turn is
**authorized** and **conservation-respecting**, else `none`. Everything else — circuits, the FFI,
the apps — is built on top of this function and its soundness theorems.

## The altitudes (you'll meet all of them)

dregg2 is l4v-shaped: the same machine appears at several altitudes, each refining the one above.

1. **Abstract Spec** (`Dregg2/Core.lean`, `Spec/*`) — the *laws* a turn must obey (conservation =
   Law 1; authority; confluence). No commitment to a representation.
2. **Universe-A executor** (`Dregg2/Exec/FullForest.lean`, `Exec/Effect*.lean`, `Exec/EffectsState.lean`)
   — the *richer abstract surface*: per-effect `*Spec`s over the full `RecordKernelState` (all 17
   fields). This is what the circuit emission projects from, and where the per-effect declarative
   specs live (`BalanceMovementSpec`, `SetFieldSpec`, …).
3. **Record kernel** (`Dregg2/Exec/RecordKernel.lean`) — the runnable, `#eval`-able verified core:
   a content-addressed `Value` record cell with named fields. **`recKExec` is the verified
   transition.**
4. **Concrete kernel** (`Dregg2/Exec/ConcreteKernel.lean`) — HashMap-backed, efficient; an
   `Exec ⊑ Spec` data-refinement *proves* the abstract soundness transfers to this fast runtime.

The point of the ladder: prove soundness once at the abstract altitude, then *transport* it down by
refinement so the fast runtime inherits it.

## The ONE entry point (and why it matters)

There is exactly **one credential-gated turn entry**, and historically the project's biggest rot was
*multiplying* entries (ungated escape hatches). Do not re-introduce that. The entry is:

```
Dregg2/Exec/FullForestAuth.lean
  execFullForestG : RecChainedState → … → Option …        -- the gated forest executor
  execFullTurnG   : …                                       -- a single gated turn
```

The gate is *unavoidable*: `execFullForestG_unauthorized_fails:949` proves an unauthorized turn
returns `none`. The credential model (`NodeAuth`, `GatedCaveat`, the 10-variant `Authorization`)
lives alongside; the authority story is in [`authority.md`](authority.md).

The **FFI export** that the Rust runtime calls is in `Dregg2/Exec/FFI.lean`:

```
@[export dregg_exec_full_forest_auth]    -- FFI.lean:3487  (the production entry)
```

The previously-existing *ungated* `dregg_exec_handler_turn` export was **removed** (`FFI.lean:3831`)
— the symbol is absent so the Rust side cannot call an unfenced path. The Rust bridge calls it via
`extern "C" fn dregg_exec_full_forest_auth_str` (`dregg-lean-ffi/src/lib.rs:177`).

## How an effect executes — the verified core (`recKExec`)

`Dregg2/Exec/RecordKernel.lean`:

```
def recKExec (k : RecordKernelState) (turn : Turn) : Option RecordKernelState := …   -- :640
```

The load-bearing theorems (all `#assert_axioms`-clean) that make `recKExec` *mean something*:

| Theorem | `file:line` | What it guarantees |
|---|---|---|
| `recKExec_conserves` | `:686` | total value is preserved (Law 1) |
| `recKExec_authorized` | `:703` | a successful step was authorized |
| `recKExec_unauthorized_fails` | `:712` | an unauthorized step returns `none` (fail-closed) |
| `recKExec_frame` | `:721` | untouched fields are frozen (the frame condition) |
| `recKExecAsset_no_cross_asset_leak` | `:846` | multi-asset: no value crosses asset boundaries |

The **frame condition** is the crux of "an effect touches what it says it touches and nothing else"
— it's what makes the per-effect circuit descriptors meaningful (see [`circuit.md`](circuit.md)).

## The ~56 effects

The kernel `CellEffect` constructors (`setField`, `transfer`, `mint`, `burn`, `grantCap`,
`revokeCap`, `emitEvent`, `incrementNonce`, `createCell`, `createEscrow`, `noteSpend`, `seal`,
swiss-handoff, …) are catalogued in `Dregg2/CatalogEffects.lean`; their handlers are in
`Dregg2/Exec/Handlers/` and `Exec/Handler.lean`. Each maps many-to-one onto a circuit descriptor
(`EffectVmEmit*`) — the per-effect circuit-assurance state is the
[circuit guide](circuit.md) + [`../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md`](../rebuild/_CIRCUIT-ASSURANCE-PER-EFFECT.md).

## Soundness — the spine

The proof spine that lifts a single-step guarantee to a whole run:

- **`Dregg2/Exec/StepComplete.lean` + `Boundary.lean`** — `stepComplete_preserves`, the proved
  coinductive keystone over the `νF` cell (soundness is preserved across the infinite unfolding of
  the living cell).
- **`Dregg2/Proof/WP.lean`** — a weakest-precondition / VCG calculus (`wp`/`Triple`/`vcg`) whose
  `vcg_run_sound` *reduces to* `stepComplete_preserves`: the run-level soundness was already proved,
  the VCG only *generates* per-turn obligations. This is what a developer uses to verify their own
  cell program.
- **`Dregg2/Proof/LTS.lean`** — the operational LTS: `absStep'_forward` unions the balance-turn and
  authority-turn forward-simulation squares (single-cell complete; cross-cell whole-history closure
  is the named in-progress research front).

## CapTP — moving capabilities between cells

The object-capability transport (`Dregg2/Exec/CapTP*.lean`) is its own verified subsystem:

- `CapTPHandoffSound.handoff_unforgeable:348` — a handoff cannot fabricate authority.
- `CapTPGC.captp_no_premature_reclaim:106` / `captp_gc_by_lease:94` / `captp_leaked_handle_reclaimed_by_lease:171`
  — leased GC: live handles aren't reclaimed; leaked ones eventually are.
- `CapTPConsentLace.*` — consent recorded on the blocklace; equivocation detectable.

## The swap (the in-flight part)

Today the *running* runtime is the legacy dregg1 Rust executor (`turn/src/apply.rs`,
`TurnExecutor::execute`). THE SWAP = making the verified Lean executor *be* the runtime. The bridge
exists (`dregg-lean-ffi`) and a **live differential** (`turn/tests/rust_lean_divergence_finder.rs`,
output in [`../rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md`](../rebuild/_RUST-LEAN-DIVERGENCE-LEDGER.md))
runs both side-by-side. The honest frontier (named in the README): the FFI admission context must be
host-fed, the success-bit must distinguish a committed body from a fee-only prologue, and the cutover
itself is a rewrite tracked separately — not a modeling gap. The differential's principle (per
project memory): pin **kernel-vs-new-Rust**, never against the *buggy* dregg1 oracle (matching a
buggy oracle launders the bug).

## Where to start reading

1. `Dregg2/Exec/RecordKernel.lean` — `recKExec` + its five theorems. The whole model in one file.
2. `Dregg2/Exec/FullForestAuth.lean` — the gate.
3. `Dregg2/Proof/WP.lean` — how you verify a program on top.
