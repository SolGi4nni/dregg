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

The gate is *unavoidable*: `execFullForestG_unauthorized_fails` (`FullForestAuth.lean`) proves an
unauthorized turn returns `none`. The credential model (`NodeAuth`, `GatedCaveat`, the 10-variant
`Authorization`) lives alongside; the authority story is in [`authority.md`](authority.md).

The **FFI export** that the Rust runtime calls is in `Dregg2/Exec/FFI.lean`:

```
@[export dregg_exec_full_forest_auth]    -- in FFI.lean  (the production entry)
```

The previously-existing *ungated* `dregg_exec_handler_turn` export was **removed** (the source still
carries a REMOVED marker in `FFI.lean`) — the symbol is absent so the Rust side cannot call an
unfenced path. The Rust bridge calls it via
`extern "C" fn dregg_exec_full_forest_auth_str` (`dregg-lean-ffi/src/lib.rs`).

## How an effect executes — the verified core (`recKExec`)

`Dregg2/Exec/RecordKernel.lean`:

```
def recKExec (k : RecordKernelState) (turn : Turn) : Option RecordKernelState := …
```

The load-bearing theorems (all `#assert_axioms`-clean) that make `recKExec` *mean something*
(all in `RecordKernel.lean`):

| Theorem | What it guarantees |
|---|---|
| `recKExec_conserves` | total value is preserved (Law 1) |
| `recKExec_authorized` | a successful step was authorized |
| `recKExec_unauthorized_fails` | an unauthorized step returns `none` (fail-closed) |
| `recKExec_frame` | untouched fields are frozen (the frame condition) |
| `recKExecAsset_no_cross_asset_leak` | multi-asset: no value crosses asset boundaries |

The **frame condition** is the crux of "an effect touches what it says it touches and nothing else"
— it's what makes the per-effect circuit descriptors meaningful (see [`circuit.md`](circuit.md)).

## The effects — eight verbs, a 27-tag wire enum

The kernel signature is **eight survivor verbs** (`Dregg2/Substrate/VerbRegistry.lean`); the live
wire surface is the **27-variant `EffectTag`** enum (`effect_tag_count` proves `= 27`). The
conservation-bearing core `CellEffect` (`Dregg2/Exec/Effect.lean`) is a representative 9-constructor
slice — `setField`, `transfer`, `mint`, `burn`, `grantCap`, `revokeCap`, `emitEvent`,
`incrementNonce`, `createCell` — whose no-`_`-arm `linearity` match makes a new constructor a
compile error until it declares its conservation class. The *doomed* families (escrow, bridge-3phase,
queue, seal/swiss/sturdyref…) are **deleted** from the kernel — `no_live_factory_tags` proves it —
and re-land as verified factory cell-programs (`Dregg2/Apps/*Factory.lean`), not as live kernel
constructors. Handlers are in `Dregg2/Exec/Handlers/` and `Exec/Handler.lean`; each effect maps
many-to-one onto a circuit descriptor (`EffectVmEmit*`) — the per-effect circuit-assurance state is
the [circuit guide](circuit.md) + the source-grounded [`../COMPOSITION-SOUNDNESS-CENSUS.md`](../COMPOSITION-SOUNDNESS-CENSUS.md).

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

- `CapTPHandoffSound.handoff_unforgeable` — a handoff cannot fabricate authority.
- `CapTPGC.captp_no_premature_reclaim` / `captp_gc_by_lease` / `captp_leaked_handle_reclaimed_by_lease`
  — leased GC: live handles aren't reclaimed; leaked ones eventually are.
- `CapTPConsentLace.*` — consent recorded on the blocklace; equivocation detectable.

## The swap (live, partial — not pending)

The node already routes turns through the verified Lean executor as the authoritative state
**producer**: `node/src/executor_setup.rs` calls `dregg_exec_lean::produce_via_lean`, logging under
`dregg::lean_shadow::producer`. THE SWAP is the burn-down of the *covered set* — which turn shapes
route through the Lean producer by default (`producer_covered_effects` / `producer_uncovered_effects`
in `node/src/api.rs`) — toward total. The legacy `TurnExecutor::execute` (`turn/src/apply.rs`)
remains for the uncovered residual. The bridge exists (`dregg-lean-ffi`) and a **live differential**
(`turn/tests/rust_lean_divergence_finder.rs`) runs both side-by-side. The honest frontier (named in
the README): the FFI admission context must be host-fed, the success-bit must distinguish a committed
body from a fee-only prologue. The differential's principle (per project memory): pin
**kernel-vs-new-Rust**, never against the *buggy* dregg1 oracle (matching a buggy oracle launders the
bug).

## Where to start reading

1. `Dregg2/Exec/RecordKernel.lean` — `recKExec` + its five theorems. The whole model in one file.
2. `Dregg2/Exec/FullForestAuth.lean` — the gate.
3. `Dregg2/Proof/WP.lean` — how you verify a program on top.
