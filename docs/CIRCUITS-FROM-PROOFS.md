# Circuits From Proofs — law #1 as a mechanism

Architectural law #1 (`metatheory/README.md:15`):

> **Circuits are emitted from Lean** (architectural **law #1: zero Rust-authored
> constraints or AIRs, ever**). Every constraint set the prover enforces is a byte-pinned
> artifact emitted from a proved Lean module (the Argus IR and the descriptor JSONs); Rust
> only *interprets* those artifacts. A coverage gap is closed by emitting from a new proved
> module, never by hand-authoring a constraint.

This document explains the law as a *mechanism*: why constraint-authorship is the
soundness boundary, the pipeline that carries a proved Lean module to the deployed
prover, the byte-pinning that keeps the two identical, and the CI gate that makes a
hand-authored constraint a build failure rather than a code-review hope. Every claim
below is pinned to the tree.

Companions: [`reference/circuit.md`](reference/circuit.md) (the Rust prove/verify
crates), [`reference/lean-circuit.md`](reference/lean-circuit.md) (the soundness
theorems), [`OVERVIEW.md`](OVERVIEW.md) (the system spine),
[`../metatheory/CLAIMS.md`](../metatheory/CLAIMS.md) (the skeptic-facing proof ledger).

## Why constraint-authorship is the soundness boundary

A STARK verifier accepts exactly what the constraint set admits — nothing about the
system is enforced except what the deployed polynomials say. So the constraint set *is*
the deployed statement, and everything upstream of it is only as good as the identity
between "the object the theorems are about" and "the object the prover runs".

The theorems live on the Lean side. Each emitted circuit family carries, next to its
emitter in `metatheory/Dregg2/Circuit/Emit/`:

- **Rung 1 — functional refinement**: the descriptor's row semantics equal the intended
  semantics. E.g. `turnChain_descriptor_refines_rust_air`
  (`metatheory/Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean:327`) and its
  converse `turnChain_descriptor_iff_rust_air` (`:371`).
- **Rung 2 — semantic no-forgery**: refutation teeth, stated as rejections. E.g.
  `turnChain_rejects_broken_continuity` (`:409`), `turnChain_rejects_bad_idx_step`
  (`:424`), `turnChain_rejects_bad_real_count` (`:439`).

Those theorems quantify over the Lean `EffectVmDescriptor2` object. A constraint written
in Rust is a constraint **no theorem is about**: it changes what the verifier accepts
without changing anything the proofs say, and the gap is invisible to every Lean gate.
That is the whole boundary. Witness generation, trace layout, FRI, hashing — all of that
is Rust and is allowed to be, because a wrong witness generator produces proofs that
fail to verify (a liveness bug), while a wrong *constraint* produces proofs that verify
statements nobody proved (a soundness bug).

The tree contains a demonstrated instance of the failure class. The by-name predicate
descriptor `predicate-arith.json` once reached disk through an ungated hand
transcription and diverged to a re-authoring with both Poseidon2 weld legs missing — a
deployed, demonstrated forgery (the history is recorded in the module docs at
`circuit/src/descriptor_by_name.rs:40-48`). The standing falsifier is
`circuit/tests/predicate_arith_fact_weld_canary.rs`:
`forged_value_with_honest_commitment_is_refused` presents the honest, verifier-expected
fact commitment alongside a predicate proved on a value of the prover's choosing, and
must be refused; it is paired with an honest-path test so it can never pass vacuously.
An unproved constraint set is not "less audited" — it is *forgeable in ways no artifact
in the repository can see*.

## The pipeline: Lean module → byte-pinned artifact → interpreting prover

```
metatheory/Dregg2/Circuit/Emit/<Family>Emit.lean     -- constraints AUTHORED + proved here
        │  emitVmJson2 / emitVmJson (Lean serializers)
        ▼
EmitAllJson.lean · EmitByName.lean · EmitTurnChain.lean · …   -- SERIALIZE-only executables
        │  scripts/emit-descriptors.sh  →  scripts/emit_descriptors.py
        ▼
circuit/descriptors/*.json + by-name/*.json + PROVENANCE.json  -- the checked-in CACHE
        │  include_str! + parse_vm_descriptor2 (circuit/src/descriptor_ir2.rs:1073)
        ▼
effect_vm_descriptors.rs (selector → JSON) · descriptor_by_name.rs (name → descriptor)
        │
        ▼
prove_vm_descriptor2 (descriptor_ir2.rs:5630) · verify_vm_descriptor2 (descriptor_ir2.rs:5785)
```

Stage by stage:

1. **Authorship** is a Lean module under `metatheory/Dregg2/Circuit/Emit/` that defines
   the descriptor (columns, public inputs, `VmConstraint2` list) *and proves about it*
   (the `*Refine.lean` / `*Rung2.lean` neighbors). The module byte-pins its own emission
   with a `#guard`: `EffectVmEmitTurnChainBinding.lean:230` checks
   `emitVmJson2 turnChainBindingDescriptor == TURN_CHAIN_BINDING_GOLDEN` at Lean
   compile time, so the proved object and the golden string cannot separate.
2. **Serialization** is deliberately trivial. `EmitTurnChain.lean` is 20 lines and says
   so in its header: "the constraints are AUTHORED in
   `Dregg2/Circuit/Emit/EffectVmEmitTurnChainBinding.lean` (proved there, with
   refutation teeth); this file only SERIALIZES them." `EmitAllJson.lean` does the same
   for the whole effect-selector registry (one line per descriptor,
   `<def>\t<name>\t<json>`), `EmitByName.lean` for the by-name dispatch surface.
3. **Regeneration** is one command: `scripts/emit-descriptors.sh` (→
   `scripts/emit_descriptors.py`) runs every emitter and installs the JSONs plus the
   generated `*_FP` sha256 constants in the Rust sources. On a clean tree it is a
   no-op (idempotent). A byte-*changing* install is refused (exit 3) unless
   `DREGG_VK_REGEN_ACK` names the exact `metatheory/Dregg2` tree hash — re-emitting
   re-keys the federation's verifying keys, so it is a controlled act; see
   [`VK-REGEN-CONTROLS.md`](VK-REGEN-CONTROLS.md).
4. **Interpretation** is the only thing Rust does with a descriptor.
   `parse_vm_descriptor2` decodes the JSON; `prove_vm_descriptor2` /
   `verify_vm_descriptor2` run the generic IR2 interpreter over it. Dispatch is
   fail-closed: `descriptor_by_name` (`circuit/src/descriptor_by_name.rs:328`) returns
   `Option::None` on a miss — never a stand-in descriptor, never a silent accept — and
   the selector registry (`circuit/src/effect_vm_descriptors.rs`) maps effect selector
   → embedded JSON the same way. The depth-general membership families are *built* (a
   parameterized construction) rather than parsed, behind the same name-dispatch.

## Byte-pinning: three layers, each with its limit stated

The checked-in JSON is a **cache** of the Lean emission, and the pinning distinguishes
what each layer can and cannot prove:

- **Lean-side `#guard` goldens** — the emitter module refuses to compile if the proved
  descriptor's serialization moves (e.g. `EffectVmEmitTurnChainBinding.lean:222-230`).
  Binds *proof → bytes* at Lean build time.
- **`*_FP` sha256 constants + `PROVENANCE.json`** — self-consistency pins. The registry
  header (`circuit/src/effect_vm_descriptors.rs`) states their limit exactly:
  `sha256(bytes) == FP` proves a file matches the hash committed *next to it*, not that
  the bytes still equal the current Lean emission. `circuit/descriptors/PROVENANCE.json`
  stamps each install with the `metatheory/Dregg2` tree hash, repo HEAD, toolchain, the
  emitter list, and per-file sha256 legs (including a separate `by_name_sha256` leg
  sourced from the emitted content, not a disk re-hash).
- **The GENERATE-FRESH drift gate** — `scripts/check-descriptor-drift.sh` rebuilds the
  Lean corpus (fresh oleans, so it cannot be blind to an un-rebuilt Lean change),
  re-runs every emitter, and diffs the result against the checked-in artifacts. This is
  the only layer that catches a committed JSON gone stale while the Lean moved
  underneath it. It runs in CI as the `descriptor-drift` job
  (`.github/workflows/ci.yml:343`).

`emit_descriptors.py` additionally enforces **coverage**: its check recurses into
`by-name/`, so a descriptor file that no emitter reproduces is a routing-gap failure —
there is no way for a JSON to sit on disk outside the Lean-derived set.

## The gate: law #1 fails the build

`circuit-prove/tests/law1_enforcement_gate.rs` is the ratchet that turns the prose law
into a red test. Its design answers the reason four prior audits miscounted the
violation surface — **there are three constraint dialects**, and a grep for one sees a
third of the truth (`law1_enforcement_gate.rs:8-11`):

1. `builder.assert_zero / assert_eq / when` — plonky3 symbolic;
2. `Constraint { eval: Box::new(|..| ..) }` — closures, invisible to (1);
3. `ConstraintExpr::{..}` struct literals — data, invisible to (1) and (2).

`count_constraint_sites` (`:43`) counts all three in **every** `.rs` under
`circuit/src` + `circuit-prove/src` (a `*_air.rs` filename proves nothing — many hold no
algebra, much algebra lives elsewhere) and ratchets against a frozen baseline (`:62`):
**48 files, 757 sites** as of 2026-07-16. A *new* file containing constraint algebra, or
a listed file *growing*, fails with a message that says to emit from Lean and explicitly
not to add yourself to the baseline. Shrinking is always allowed — that is the
direction of the law. The failure mode was verified to bite (a planted
`eval: Box::new` probe fails the test; removing it goes green — recorded in
`b0f8c8eb7`). The gate lives in `circuit-prove/tests/`, a workspace default member, so
it runs under the workspace test gate (`.github/workflows/ci.yml:80`,
`cargo test --workspace`) — a ratchet that cannot compile cannot bite, so it sits in a
crate that builds.

The baseline is a **classified ledger, not an amnesty** (`law1_enforcement_gate.rs:25-38`).
Its entries are:

- **Interpreters** — the law *working*: `descriptor_ir2.rs` (99 sites),
  `dsl/dsl_p3_air.rs` (86), `lean_lookup_air.rs`. These evaluate Lean-authored
  constraint data; they author nothing.
- **Proved-faithful lowerings** — `custom_leaf_adapter.rs` (50), covered by
  `cell_to_descriptor_faithful` (`metatheory/Dregg2/Circuit/CustomLeafEncoding.lean:212`).
- **Drift-detectors, deliberately kept** — `dsl/derivation.rs`, `dsl/note_spending.rs`:
  the emitted paths walk these v1 descriptors as their *source*, so "a drift in the
  deployed circuit is a build-time refusal here, never a silent divergence"
  (`circuit/src/note_spend_witness.rs:225-227`).
- **The user-program grammar** — `dsl/predicates/*`, `dsl/descriptors.rs`: the
  host-trusted smart-contract surface users deploy programs against; interpreted, and
  fail-closed on an unknown `vk_hash`.
- **Named residuals** — see the horizon section below.

The baseline is a ceiling, not a description: entries shrink under it without edits to
the gate. At HEAD, `circuit/src/dsl/revocation.rs` holds **zero** constraint sites under
its baseline entry of 40 — non-revocation proves through the Lean-emitted
`dregg-non-revocation-adjacency::poseidon2-fact-v1`
(`metatheory/Dregg2/Circuit/Emit/NonRevocationAdjacencyEmit.lean` →
`circuit/descriptors/by-name/non-revocation-adjacency.json`, byte-pinned by
`circuit-prove/tests/non_revocation_adjacency_emit_gate.rs` — the neighboring
`non_revocation_emit_gate.rs` pins the historical depth-2 sorted-tree descriptor, not
this one — dispatched at `dsl/revocation.rs:435` via `descriptor_by_name` +
`prove_vm_descriptor2`).

The net position, per the scope classification in
[`../GOAL-STARK-KILL.md`](../GOAL-STARK-KILL.md) ("THE COMPLETE SCOPE, CLASSIFIED",
2026-07-16): **every deployed first-party Rust-authored circuit is retired** — what
remains in the baseline is interpreters, proved lowerings, drift-detectors, the
predicate grammar, and the named residuals. The full deletion plan is
[`deos/LEGACY-STARK-DELETION-SCOPE.md`](deos/LEGACY-STARK-DELETION-SCOPE.md).

## Closing a coverage gap

The gate's failure message is the procedure. A new circuit need is met by emission,
never authorship (`law1_enforcement_gate.rs:18-23`):

1. Author the constraints in a new `metatheory/Dregg2/Circuit/Emit/<Family>Emit.lean`,
   with the Rung-1 refinement and Rung-2 rejection theorems beside them and a `#guard`
   byte-pin of `emitVmJson2` output. The worked end-to-end example is
   `EffectVmEmitTurnChainBinding.lean` + `metatheory/EmitTurnChain.lean`.
2. Run `scripts/emit-descriptors.sh` on the Lean host; commit the descriptor JSON (under
   `circuit/descriptors/` or `by-name/`) and the regenerated pins.
3. Route it: an effect selector entry in `effect_vm_descriptors.rs`, or a
   `descriptor_by_name` arm (fail-closed on a miss), consumed through
   `prove_vm_descriptor2` / `verify_vm_descriptor2`.
4. The drift gate, the coverage check, and the law-1 ratchet then hold it: the JSON is
   re-derived from Lean on every drift run, an orphan JSON is a routing-gap failure, and
   any Rust constraint algebra added instead is a red test.

Lowering the baseline when algebra retires is routine; raising it requires a recorded
reason in `GOAL-STARK-KILL.md`.

## Named residuals (the horizon, labeled)

- **`circuit/src/ivc.rs`** (14 sites): **test-only** — no production path reaches them.
  The `IvcAir` family this bullet once described as SDK-reachable is GONE: the mock-proof
  purge (`1fdd4a671`) deleted the simulated IVC engine outright — `prove_ivc` / `verify_ivc`,
  `IvcProof`, `IvcBuilder` (+ `finalize_with_air`), `IvcAir`, and the `CipherClerk::export_state_proof`
  → `enable_ivc` path that was its only indirect consumer (zero callers). `StateTransitionAir`
  followed (2026-07-17): it was a bare unit struct implementing no `Air` at all. What remains in
  the file is the REAL Poseidon2 hash-chain + the state-transition trace layout
  (`circuit/src/ivc.rs:19-25`, `:167-178`). The residual stays because its emitter is one Lean
  *proves insufficient* (`ivc_anchor_insufficient`: no copy-forward gate, every `old_hash` at i>0
  is a free column), so cutting onto that descriptor would trade a stronger check for a weaker
  one. The real turn-chain recursion is `circuit-prove/src/ivc_turn_chain.rs`.
- **`circuit/src/dsl/fold.rs::FoldAir`** (15 closure-dialect sites): **test-only** scaffolding
  (`circuit/src/tests.rs`, `bridge/src/tests.rs`). It was previously reached from the `prove_ivc`
  family; that family is deleted, so tests are now its whole reachability. `PresentationAir`
  (`circuit/src/presentation.rs:472`) is a separate, live surface carrying 1 baseline site.
- **Drift-detectors** (`dsl/derivation.rs`, `dsl/note_spending.rs`): remaining by
  design, as the source the emitted paths compare against — retiring them removes the
  build-time drift refusal, so they stay until their consumers do.

Each of these is a *labeled* seam with its blocking reason recorded in the gate header
and `GOAL-STARK-KILL.md` — none is asserted closed here.
