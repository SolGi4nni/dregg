# Circuit Functional Correctness — Light-Client Unfoolability (campaign status)

> Authoritative state of the circuit-soundness proof after the autonomous run. Honest about
> proven-vs-carried; the two **closure-blocking decisions** at the end are genuine (VK-affecting),
> not grind.

## The property (the apex — built, faithful, green)

A light client verifies a rotated proof against the live VK and runs nothing else. Soundness:
`verifyBatch accept ⟹ ∃ a genuine kernel transition committing to the published (pre,post)`.

`Dregg2/Circuit/CircuitSoundness.lean` — `lightclient_unfoolable` proves exactly that from *only*
`(pi, π)` + named floors: it **derives** `∃ pre post` (no hypothesized decode), with `StateDecode`
faithfulness a theorem (`recStateCommit` injectivity) and the cross-step frame *derived* from the
commitment binding. Green, `#assert_axioms ⊆ {propext, Classical.choice, Quot.sound}`. Carried
obligations (each explicit, none laundered): `StarkSound` (the audited p3-batch-stark verify⟹∃witness —
a legitimate crypto/audit floor), `Poseidon2SpongeCR`, `hrefines` (per-effect `descriptorRefines`),
`WitnessDecodes` (the witness→kernel-state existence rung).

## What is PROVEN (green, axiom-clean)

- **The apex** (above) and the `descriptorRefines` schema — the north star every effect discharges into.
- **The cap-authority keystone** — the long pole, because *every* `fullActionStep` arm carries
  `authorizedB`:
  - `Dregg2/Circuit/DeployedCapTree.lean` — the deployed depth-16 7-field cap-tree, now **faithful to
    the real rate-4 Poseidon2 byte-for-byte**: `capLeafDigest` = rate-4 chunked `hash_many` (2 permutes
    for 7 fields, length in capacity slot 4), `nodeOf` = single capacity-tagged permute (`0xFACF` at
    slot 5, leaf-flag at slot 6) — matching `circuit/src/poseidon2.rs`. Injectivity rides the named
    permutation-CR floor.
  - `Dregg2/Circuit/DeployedCapOpen.lean` — an in-circuit depth-16 membership-open built from **generic
    Lean-emitted constraints** (chip `Lookup`s + gates; **LAW#1-clean — zero hand-authored Rust
    constraint semantics**); `capOpen_sound ⟹ MembersAt ⟹ authorizedB`.
  - `Dregg2/Circuit/Emit/CapOpenEmit.lean` — those constraints **emitted from Lean** into a live
    descriptor (`capOpenAttenuateV3`), bridged to `authorizedB`.
- **The transfer value-rung** (`RotatedKernelRefinement.lean`) — the live transfer circuit *forces* the
  value move (debit/credit/availability/conservation), with both-polarity teeth.
- A LAW#1 cleanup: the IR-v2 map-op leaf is now a descriptor-declared field list (no hardcoded arity).

## The two CLOSURE-BLOCKING DECISIONS (genuine, VK-affecting — not mine to fake)

The cap-authority leg is proven *relative to* two named bridges that are real deployment/design
decisions. Full closure cannot honestly land until these are made:

1. **Chip-rate reconciliation.** The deployed cap-tree commits **rate-4** hashes (`hash_many`/`hash_fact`);
   the live IR-v2 chip realizes a **rate-8** single absorb. `DeployedCapOpen` proves (witness-FALSE,
   `schemeRealizedByChip_node_unrealizable`) that the rate-8 chip *cannot* reproduce the rate-4 cap hash —
   it is a genuine gap, not a modeling artifact. Closing it requires **either** (a) a rate-4 /
   capacity-tagged chip absorb mode (a Lean+Rust chip change), **or** (b) re-committing the cap-tree to
   the chip's rate-8 hash (a `cap_root.rs` + cell-commitment flag-day). Both change the VK.
2. **Mask convention.** The cap leaf commits an `EffectMask` (an *effect-kind* bitmap:
   `EFFECT_TRANSFER=1<<1`, `EFFECT_GRANT_CAPABILITY=1<<2`, …, `cell/facet.rs`), while the kernel
   `authorizedB` checks `Auth.write` (a read/write *rights* model). These are two different authority
   models; unifying them (which is canonical, how an effect-kind maps to a right) is a **design choice**.
   No constant was faked to pretend they agree.

## The remaining GRIND (unblocked once the authority leg lands)

- **`hrefines` — per-effect `descriptorRefines` × ~30**: each effect's circuit must force its
  `fullActionStep` arm. Every arm includes `authorizedB`, so all ~30 wait on the cap-authority leg going
  truly live (the two decisions + the prover wire). The transfer value-leg is the worked template.
- **`WitnessDecodes` × ~30** — the witness→kernel-state existence per effect.
- **Forest composition** — compose the per-effect refinements into `execFullForestG` (the apex's `kstep`).
- **Prover wiring** — build the cap path-witness from the c-list and pass it (`sdk/src/full_turn_proof.rs:662`
  passes `&[]` today; the cap-open is specified+proven but not yet exercised end-to-end), + the VK epoch.

## Honest bottom line

The conceptual core is closed: a **faithful apex** and a **cap-authority keystone that now matches the
deployed sponge byte-for-byte**, all LAW#1-clean and axiom-clean. What remains for "closed-closed" is
(a) **two genuine VK-affecting decisions** (chip-rate, mask convention) that gate the authority leg of
*every* effect, and (b) a **~30-effect discharge + composition + prover-wiring grind** that those
decisions unblock — realistically a weeks-to-months formal+circuit effort, not a few more steps. The
crypto floors that legitimately remain are `StarkSound` and the Poseidon2/permutation CR.

## References

- Apex: `Dregg2/Circuit/CircuitSoundness.lean`. Kernel ref: `Dregg2/Circuit/ActionDispatch.lean`
  (`fullActionStep` ⟺ `execFullA`).
- Cap-authority: `Dregg2/Circuit/DeployedCapTree.lean`, `DeployedCapOpen.lean`, `Emit/CapOpenEmit.lean`;
  deployed primitives `circuit/src/poseidon2.rs` (`hash_many` rate-4, `hash_fact`), `circuit/src/cap_root.rs`
  (`CapLeaf`, depth-16). Kernel `authorizedB`: `Dregg2/Exec/Kernel.lean`.
- Value-rung: `Dregg2/Circuit/RotatedKernelRefinement.lean` + `Spec/balancemovement.lean`.
- Crypto floor: `Dregg2/Circuit/Poseidon2Binding.lean`. Task #103 (capability crown).
