# Circuit descriptor emission — Lean is the source of truth

The circuit's per-effect AIR descriptors live as verified Lean `EffectVmDescriptor`
objects. The checked-in artifacts under `circuit/descriptors/` — the `*.json` wire
descriptors, the rotation manifests, and the staged-registry `.tsv` — together with
the `*_FP` sha256 constants in `circuit/src/*.rs`, are **machine-generated
projections** of those Lean objects. They are not hand-written.

## The one command

```
scripts/emit-descriptors.sh
```

Runs every Lean emitter, splits each emitter's stdout into the matching
`circuit/descriptors/*` files, and re-pins every `*_FP` sha256 constant. It is
**idempotent**: on a clean tree it writes byte-identical content and leaves no diff.
Run it whenever a Lean emit moves (a new gate, a width change, a renamed
descriptor), then commit the result.

## The drift gate

```
scripts/check-descriptor-drift.sh
```

Builds the Lean corpus (so the emitters run against fresh `.olean`s, not stale
ones), runs `emit-descriptors.sh`, then `git diff --exit-code`s the descriptors and
the `*_FP` constants. It exits nonzero with a clear message if the Lean emission and
the checked-in artifacts disagree. This is the **Lean↔JSON guard**.

It runs in CI as the `descriptor-drift` job (`.github/workflows/ci.yml`). It is
complementary to the in-Rust `#[test]` in `effect_vm_descriptors.rs`, which guards
JSON↔FP *self-consistency* (it re-hashes the embedded bytes) but cannot see
Lean↔JSON drift: a stale JSON whose self-consistent FP passes the round-trip while
the Lean emission has moved underneath it. The drift gate closes exactly that gap.

## What is covered

Every file under `circuit/descriptors/` is regenerated. The driver
(`scripts/emit_descriptors.py`) asserts full coverage: if a checked-in descriptor is
not reproduced by any emitter, the script fails (a routing gap is a hard error, never
a silent skip). Four Lean emitter executables back the set:

| Emitter (`metatheory/`)                     | Produces                                              | File routing |
|---------------------------------------------|------------------------------------------------------|--------------|
| `Dregg2/Circuit/Emit/EmitAllJson.lean`      | the v1 descriptors                                   | by `.name` → `<name>.json` |
| `EmitAllJsonV2.lean`                         | the ir2 descriptors                                  | by Lean def-name via the Rust `V2_DESCRIPTORS` table |
| `EmitRotationV3.lean`                        | rotation v3-staged manifests/probes + the registry `.tsv` | per-key routing |
| `EmitBilateralLegs.lean`                     | bilateral-aggregation + cross-side + bundle-fold     | by `.name` → `<name>.json` |

The `*_FP` constants are re-pinned in `effect_vm_descriptors.rs`,
`cap_reshape_descriptor.rs`, `cap_delegation_nonamp_descriptor.rs`, and
`bilateral_aggregation_air.rs`. Files with no `*_FP` constant (the rotation
manifests and the registry `.tsv` other than `V3_STAGED_REGISTRY_FP`) are guarded by
byte-diff alone, which is sufficient — the gate diffs the file content directly.

## Adding a new descriptor

1. Write the Lean emit module and add it to the relevant emitter's `main`.
2. Add the `include_str!` + `*_FP` constant pair to the appropriate Rust file (and,
   for ir2, an entry in `V2_DESCRIPTORS`).
3. Run `scripts/emit-descriptors.sh`. If routing is incomplete the script fails and
   names the unreproduced file — wire it up, then re-run and commit.
