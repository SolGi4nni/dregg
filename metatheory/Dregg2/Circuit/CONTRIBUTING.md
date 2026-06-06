# Contributing to dregg2 circuits (a guide for Composer & other agents)

This is a **living, accurate** guide (last verified against the build at commit `c96515d6`, Lean
4.30 / mathlib v4.30). If you change the code and a claim here goes stale, **fix this file too**.
Trust the *code* over any prose; if in doubt, `lake build` it.

## 0. What this is

`dregg2` is a formally-verified web3 capability-OS written in **Lean 4** (`metatheory/`, an l4v-shaped
proof project; the git root is `/Users/ember/dev/breadstuffs`). The current crown jewel is the
**circuit ⟺ protocol** correspondence: we *derive ZK circuits in Lean* and prove they are a sound +
complete refinement of the protocol's real executor — so an Orchard-class value-forgery is impossible
**by construction**, and the verified circuit can drive a real Plonky3 prover.

## 1. The non-negotiable discipline (read first)

- **The green build IS the gate.** Every theorem you "prove" must `lake build` green. A green build with
  passing `#assert_axioms` is the *only* acceptance. Self-reports ("it builds") are not trusted — the
  reviewer re-builds.
- `export PATH="$HOME/.elan/bin:$PATH"` before any `lake`/`lean`.
- **Build command:** `lake build Dregg2.Circuit.<Module>` (one module) or `lake build Dregg2` (root).
- **NEVER** run `cargo test --lib` or `cargo test` without an exact test name in `circuit/` — the Rust
  lib suite takes **30+ minutes**. Use `cargo build -p dregg-circuit` + `cargo test -p dregg-circuit
  <exact::path> -- --exact`.
- **NO** `sorry` / `admit` / `native_decide` / new `axiom`. Pin every keystone with `#assert_axioms
  <name>` — it must whitelist exactly `{propext, Classical.choice, Quot.sound}`. A leaked `sorryAx`
  fails the build (that's the tripwire working).
- **Never** make `/tmp` "backup" copies and restore from them — that loses work. Edit in place; WIP
  files are git-untracked and the human/main-loop commits.
- **Additive, not destructive.** Do not rewrite the proven keystones (`StateCommit`, `SetFieldCommit`,
  `EffectCommit`, `Transfer`). Add new files; if you must touch a shared file, keep its theorems intact
  and re-gate it.

## 2. The architecture — the circuit⟺spec triangle, per effect

For each protocol effect E there is a **three-corner triangle** (this is the anti-"pale-ghost" design):

```
                eSpec  (an INDEPENDENT declarative full-state post-state — the apex truth)
               /                                          \
   executor ⟺ eSpec                                    circuit ⟺ eSpec
   (the real executor produces exactly eSpec)          (a satisfying witness pins exactly eSpec)
```

- **eSpec** is full-state: it pins **every** field of the post-state. `RecordKernelState` has **17**
  fields (`accounts, cell, caps, escrows, nullifiers, revoked, commitments, bal, queues, swiss,
  slotCaveats, factories, lifecycle, deathCert, delegate, delegations, sealedBoxes`); `RecChainedState`
  adds the receipt `log`. **Miss one field in the frame and the spec is itself a ghost.**
- **executor ⟺ spec** lives in `Dregg2/Circuit/Spec/<family>.lean` (31/31 effect families done — see
  `<exec>_iff_spec` lemmas). This validates the executor against the independent spec.
- **circuit ⟺ spec** is the ZK part: `Dregg2/Circuit/StateCommit.lean` (transfer), `SetFieldCommit.lean`
  (setFieldA), and the **generic `EffectCommit.lean` framework** for the rest.

## 3. The `EffectCommit` framework — how to add a new effect (the recipe)

Adding the circuit⟺spec corner for a new effect is now a **thin instance** (~100 lines), not a bespoke
~500-line proof. The generic theorems (`effect_circuit_full_sound`, `_complete`, the four anti-ghost
teeth, emission) are proved **once** in `Dregg2/Circuit/EffectCommit.lean`. You supply:

1. An `EffectSpec St Args` value: `view` (read kernel+log out of the state), `touched pre args` (the
   `Finset CellId` the effect writes), `expectedLeaf pre args` (the new `Value` at each touched cell —
   the only effect-specific arithmetic), `logUpdate` (`none` = log frozen, `some f` = grows),
   `guardGates` (the admissibility bit/arith gates), `guardProp` (the decoded admissibility `Prop`),
   `guardWidth` (≤ 64; guard wires live below the digest floor), `guardEncode` (the guard's witness),
   `guardLocal` (guard gates read only wires `< guardWidth`), `guardWidth_le` (`by decide`).
2. `GuardDecodes` (`satisfied guardGates witness → guardProp`) — usually transported from the effect's
   existing `Spec/<family>.lean` `*_iff` lemmas.
3. `GuardEncodes` (the `←`).
4. An `apex ↔ <BespokeSpec>` bridge (a `funext` on `touchedCellMap` + And-reassoc of the 16 frame
   clauses).

Then `effect_circuit_full_sound`/`_complete`/the four anti-ghost teeth come **free**. See
`Dregg2/Circuit/EffectInstances.lean` for the worked `transferE`/`setFieldE` templates.

**The keystone insight:** `touchedDigest = StateCommit.frameDigest` over the carrier `T` — so the one
already-proved binding lemma `StateCommit.FrameDigestBindsCells` binds **both** the frame (`accounts \
T`) **and** the touched cells (`T`) at any `|T|`. No new binding lemma.

## 4. Proof-strategy playbook (the reusable tactics — avoid the known tarpits)

- **Wire lookups: use CONCRETE indices.** The digest wires are fixed literals (`64..73`), so the
  `reduceIte` simproc collapses the encoder's `if`-cascade automatically. The reusable tactic is
  **`ec_lookup`** (= `simp [encodeE, <wire abbrevs>]`). **Do NOT** use symbolic offsets like
  `guardWidth + k` in `if`-conditions — that triggers the `omega`-inside-`if_neg` metavariable tarpit
  (a real prior failure: `omega` reports "could not prove"/"no usable constraints" because the `by
  omega` elaborates against an unpinned condition).
- **`omega` over `Var`:** `Var` is `abbrev Var := Nat`, but in some spots you must `unfold Var at *`
  before `omega` sees it as `Nat`. For contradiction branches prefer `exfalso; omega`. For the
  guard-transport lemma the working shape is `unfold encodeE Var at *; simp only [<wires>]; split_ifs
  <;> first | rfl | (exfalso; omega)`.
- **`StateCommit.FrameDigestBindsCells`** takes `CH compressN` as the **first explicit args** (then
  `hN hL k k' S h`). Forgetting them gives an "application type mismatch".
- **The frame `funext`** (post cell map reconstruction) cases on `c ∈ T` (decidable Finset
  membership): touched → `expectedLeaf` (via `FrameDigestBindsCells` on carrier `T`), live-untouched →
  frozen (on carrier `accounts \ T`), dead (`c ∉ accounts`) → `AccountsWF` (both states default).
- When a closed-form proof fights a `simp` normalization (e.g. the singleton-`List.map` membership), do
  not thrash — exhibit the meaning with decidable `#guard`s and move on; note the deferral honestly.

## 5. The cardinal sins (what makes a "proof" worthless)

- **Conservation ≠ full semantic correctness.** Pinning `Σδ = 0` over the moved cells + the entry guard
  is a *projection*, not soundness — an adversary can tamper with any unconstrained field. The whole
  post-state (all 17 fields + log) must be pinned. The anti-ghost teeth (`_rejects_third_cell`,
  `_rejects_field_tamper`, …) are the proof you did this — a forgery a guard-only circuit accepts must
  be REJECTED by the full circuit.
- **Unrealizable portals.** Carry only **realizable** crypto assumptions (the injectivity of a genuine
  Poseidon hash: `compressNInjective`, `cellLeafInjective`, `logHashInjective`, `RestHashIffFrame`). A
  *sum* is not injective — `frameDigest` must be a real `compressN` sponge, never a `Finset.sum` (an
  earlier bug: sum-injectivity portals are satisfied by NO commitment ⇒ the soundness theorem is
  vacuous).
- **The frame-portal ghost.** NEVER carry a hypothesis like `postRoot = recStateCommit (applyEffect
  …)`. The frame must be *reconstructed* (by `funext` from reused-digest gates + injectivity), not
  asserted.
- **Field soundness needs range checks.** `ℤ`-soundness in Lean ≠ field-soundness after mapping to
  BabyBear (`p = 2³¹ − 2²⁷ + 1`). A value near the modulus can wrap and forge value. Range-check
  balances via lookups into `[0, 2^k)` with **`k ≤ 30`** (`2³¹ > p`, so a 32-bit gate is *vacuous*).
  See `Dregg2/Circuit/Lookup.lean` + `circuit/src/lean_descriptor_air.rs`.

## 6. The Rust side (the "swap")

`circuit/src/lean_descriptor_air.rs` is a generic Plonky3 AIR that interprets a Lean-emitted
`EmittedDescriptor` (var/const/add/mul gates + range checks) and drives the real `p3-uni-stark` prover —
so Lean-emitted circuits replace hand-coded AIRs. Lean is the verified source-of-truth; Plonky3 is the
prover. The Lean→JSON→Rust wire is live for `transferCircuit`; emitting the full-state `StateCommit`
circuit (with Poseidon2 gates) is the next step.

## 7. Map of the key files

- `Dregg2/Circuit.lean` — the IR (`Expr` var/const/add/mul, `Constraint`, `satisfied`).
- `Dregg2/Circuit/Lookup.lean` — the lookup/range-check IR.
- `Dregg2/Circuit/Transfer.lean` — transfer: `TransferSpec`, `recKExec_iff_spec`, `transferCircuit`,
  the bit-gate `*_iff` lemmas, `admitGuard`.
- `Dregg2/Circuit/StateCommit.lean` — transfer's full-state circuit⟺spec + the reusable CR carriers
  (`frameDigest`, `FrameDigestBindsCells`, `compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`,
  `logHashInjective`, `AccountsWF`).
- `Dregg2/Circuit/SetFieldCommit.lean` — setFieldA's full-state circuit⟺spec (the +log instance).
- `Dregg2/Circuit/EffectCommit.lean` — the GENERIC framework (this is what you instantiate).
- `Dregg2/Circuit/EffectInstances.lean` — `transferE`/`setFieldE` worked templates.
- `Dregg2/Circuit/Refinement.lean` — the l4v refinement tower (`circuit ⊑ spec ⊑ executor`).
- `Dregg2/Circuit/Spec/*.lean` — the 31 executor⟺spec families (the apex specs to bridge to).
- After adding a module, wire its `import` into `metatheory/Dregg2.lean` (the human/main-loop does this)
  and full-build `lake build Dregg2`.
