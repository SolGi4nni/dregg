/-
# Dregg2.TurnAuthGuards — the CI root for the in-AIR authorization gadget and its cap-open weld.

A pure re-export aggregate. It exists so `lake build` COMPILES the two `TurnAuth*` modules, and
therefore RUNS their forty-six `#guard`/`#assert_axioms`.

## Why it exists (measured 2026-08-03)

`Dregg2.Circuit.Emit.TurnAuthLamportEmit` (36 guards) and `Dregg2.Circuit.Emit.TurnAuthCapOpenWeld`
(10 guards) were reachable from NO default lake target. Nothing in `metatheory/Dregg2.lean` imported
them; `EmitTurnAuthProbe.lean` and `EmitRotationV3.lean` do, but neither is in `lakefile.toml` at all.
Their oleans on disk were dated **Jul 30** — every keystone they assert had been unchecked since,
across the ChipArity absorb-arity cutover that touched this exact gadget (`ad93a6948` added
`turnDigestLookup`'s `turnIn.length ≤ CHIP_RATE` obligation).

⚑ **They were also invisible in the gate that exists to find them.** `scripts/check-lean-orphans.sh`
counted them — and printed `unlisted[:40]`, so at 59 unlisted orphans these two sat at #58/#59 and
their names were never emitted, with no flag that would emit them. Underneath that, the gate seeded
reachability from a HARDCODED five-target tuple while the lakefile listed eight, so 47 of those 59
were phantoms these two were buried under. Both are fixed in that script; this file is the other half.

## The substrate, said out loud

Both modules are **Lean-authored AIR**: every constraint is produced by a `def`-generator over
`AirBuilder.Head`/`VmConstraint2`/`chipLookupTupleN`, and the teeth are forcing lemmas over the
emitted object. Nothing here hand-writes AIR in Rust. Rooting them changes no descriptor and rotates
no VK — `authWeldedCapOpenTB` is still absent from `EmitByName`/`EmitWideRegistryProbe`, so no
registry member changes shape and no `registry_fp` moves. This file only makes the checks RUN.

## Why a lean_lib and not an `import` in `Dregg2.lean`

Exactly the reason `PicklesSynthesis`, `MinaBridgeGuards` and `CommitBindsGuards` each give: the
`Dregg2.lean` import block is swept by sibling lanes continuously, and a hot shared file is where a
`--only` commit absorbs somebody else's hunks. Its own root + `defaultTarget` roots the cone without
touching it.

Verified GREEN before rooting: `lake build Dregg2.Circuit.Emit.TurnAuthLamportEmit
Dregg2.Circuit.Emit.TurnAuthCapOpenWeld` → "Build completed successfully (3171 jobs)".
-/
import Dregg2.Circuit.Emit.TurnAuthLamportEmit
import Dregg2.Circuit.Emit.TurnAuthCapOpenWeld
