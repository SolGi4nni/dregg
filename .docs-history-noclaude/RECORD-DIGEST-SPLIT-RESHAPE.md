# Record-digest split-reshape — the mover authority closes (WAVE 1/2/3)

> **Status: design, for ember's review before build.** This reshapes the trust-bearing commitment
> (`RH` / `record_digest`), so it is the most delicate remaining light-client trust work — deliberately
> written down first. The two live-forgery closes already shipped (`9f415ca97` WAVE 0 authority-residue
> continuity, `b9b8b6973`/`4efae9380` selector-validity) do NOT cover the movers; this does.

## The hole (a genuine LIVE light-client forgery — not defense-in-depth)

The authority **movers** — `setPermissions`, `setVK`, `cellSeal`/`cellUnseal`/`cellDestroy`, `refusal`,
`receiptArchive`, `makeSovereign` — change the authority residue `r23` (`B_RECORD_DIGEST`, the concrete
realization of the Lean `StateCommit.RH`) and/or the lifecycle limb (`B_LIFECYCLE`). Their after-value is
forced ONLY by the record-pin's off-circuit anchor: `verify_and_commit_proof_rotated` overrides `dpis[38]`
with `compute_authority_digest_felt(trusted post-cell)` / `lifecycle_felt_cell(post)`
(`proof_verify.rs:253-303`). That is a **full-node** check — it consumes the trusted ledger post-cell. For a
**ledgerless light client** the pin `after_limb == PI[38]` welds a free column to a **free public input**
(the honesty boundary is documented in `EffectVmEmitRotationV3.lean:1829`). So a prover can publish a
`setPermissions` whose committed post-state binds **arbitrary** permissions/VK/lifecycle, and `verifyBatch`
alone accepts it. The authority-bearing half of the mover's transition is unforced.

WAVE 0 froze `r23`/lifecycle for the **value** cohort (they don't touch authority). The movers are
*excluded* from that cohort because they legitimately change it — so they remain the open live forgery.

## Why the obvious fix (recompute `compute_authority_digest_felt` in-circuit) is the WRONG shape

`compute_authority_digest_felt` (`cell/src/commitment.rs:750-874`) is a **variable-length byte sponge**
(`hash_bytes`) over: identity (id/pubkey/token_id) · mode byte · 8 `AuthRequired` permissions (each 1 tag
byte **+ 32 iff `Custom{vk_hash}`**) · optional VK (1+32) · optional delegate (1+32) · optional delegation
snapshot (a **length-prefixed cap list**) · the program (**postcard-serialized**, length-prefixed) ·
`fields[8..16]` · visibility · optional commitments · proved_state · four 32-byte side-table roots. Matching
that byte-for-byte in the field-based Poseidon2 chip needs in-circuit byte-packing + a variable-length sponge
with per-branch selectors — the single most expensive gadget in the whole effort, and brittle. **Do not.**

## The reshape: a MULTI-LIMB record digest (the dregg3 "sorted-Poseidon2 everywhere" shape)

Re-shape `RH` from one opaque fold into a fixed small tuple of **per-mutation-class sub-limbs**, combined by
one top fold:

```
record_digest = H( lifecycle_limb, permsVK_limb, identity_limb, delegation_limb, program_limb, fieldsExt_limb )
```

- `lifecycle_limb` — already its own felt (`lifecycle_felt`, `B_LIFECYCLE`); the seal/unseal/destroy/archive movers.
- `permsVK_limb` — fold of the 8 permissions + the VK (the `setPermissions`/`setVK` movers). Fixed shape:
  8 tag-felts + 8 optional Custom-vk felts + 1 VK-present + 1 VK-hash felt — a **fixed-width** fold, no
  variable sponge.
- `identity_limb` — id/pubkey/token_id/**mode** (the `makeSovereign` mover touches only the mode felt).
- `delegation_limb` — delegate + the delegation snapshot (the cap-family movers; the snapshot list folds via
  the SAME 7-field cap leaf the cap-tree already commits — reuse `cap_root` machinery).
- `program_limb` · `fieldsExt_limb` — the rarely-moved remainder (`setFieldDyn` touches `fieldsExt`).

Then each mover **recomputes only its small sub-limb in-circuit** from the effect's declared params and
**continuity-welds the other sub-limbs** before↔after (the WAVE-0 `colEq` pattern, extended per sub-limb).
This converts "recompute a variable-length sponge" into "continuity-weld the rest + one small fixed-width
recompute" — tractable, and it makes each mover light-client-sound (the after-authority is forced by the
in-circuit sub-limb recompute, no trusted post-cell).

## Law #1 + call-Lean-from-Rust (no reimplement-and-differential friction)

`record_digest` is the Lean `RH`; the descriptor constraints are emitted from Lean. The Rust producer fills
the witness by **calling the exported Lean realization** (the `@[export]` path / `libdregg_lean.a`), so there
is ONE definition of each sub-limb fold, not a Rust copy to differential. The single seam to keep honest is
the top-fold byte-layout (the existing `effect_vm_commit_lean_differential.rs` discipline, extended to the
tuple). `compute_authority_digest_felt`'s reshape is a coordinated Rust+Lean change of the SAME fold.

## Wave decomposition (cheapest-highest-value first; each: Lean sub-limb fold + gate + tooth + re-emit; VK-epoch ember-gated)

- **WAVE 1 — lifecycle movers** (cheapest; `lifecycle_limb` is already separate & small). Recompute the
  lifecycle felt in-circuit from the effect's declared transition (`Live→Sealed`, `→Destroyed{deathCert}`,
  `→Archived`), gate the per-effect disc transition, continuity-weld the other sub-limbs. Closes
  seal/unseal/destroy/archive light-client. Tooth: a forged after-lifecycle is UNSAT *without* the trusted
  post-cell.
- **WAVE 2 — perms/VK split-digest** (the structural reshape). Land the multi-limb `record_digest` itself;
  recompute the fixed-width `permsVK_limb` for `setPermissions`/`setVK`; continuity-weld the rest. This is
  the VK-affecting reshape of the commitment — the piece that wants the most care.
- **WAVE 3 — refusal + makeSovereign + setFieldDyn** (the tail; refusal lands in `fields_root`/`fieldsExt`,
  makeSovereign in the `identity_limb` mode felt, setFieldDyn in `fieldsExt`).

## The decision for ember

The reshape changes the per-cell commitment preimage (`compute_commitment` already absorbs `record_digest`
as limb 12 — `9f415ca97` era; this splits *what `record_digest` is*). It is one coordinated Lean `RH` +
Rust `compute_authority_digest_felt` reshape + the `effect_vm_commit_lean_differential` extension + the VK
epoch. Confirm the limb partition (the six sub-limbs above) and that WAVE 1 (lifecycle, cheapest, no full
reshape) is the right beachhead before WAVE 2 lands the split itself.
