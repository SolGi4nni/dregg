# VK-REGEN CONTROLS — misuse-resistant guardrails around descriptor/VK regeneration

Regenerating the circuit descriptors **re-keys the live federation**: the AIR
fingerprint of the deployed Effect VM descriptor feeds the recursive VK hash
(`compute_recursive_vk_hash`, `circuit-prove/src/recursive_witness_bundle.rs:135-172`),
every verifier pins that hash (`lookup_recursive_vk`,
`circuit-prove/src/recursive_witness_bundle.rs:180-186`; rejection at
`verifier/src/lib.rs:773-775`; the pin's tooth is
`foreign_circuit_root_is_refused_by_vk_pin`,
`circuit-prove/tests/ivc_turn_chain_rotated.rs:606`), and "distributing the new
VK to light clients" is a `git push` + client rebuild
(`docs/HANDOFF-v13-VK-EPOCH.md` §1c). Until now the epoch flip was gated only by
**convention** (ember-by-hand). This note records the actual regen lifecycle as
found, the four controls, and what is implemented.

## 1. The regen lifecycle as it exists

| Step | Where |
|---|---|
| Source of truth | Lean emitters, `metatheory/Dregg2/Circuit/Emit/*.lean` (the `EMITTERS` list in `scripts/emit_descriptors.py`) |
| Regen command | `scripts/emit-descriptors.sh:1-23` → `scripts/emit_descriptors.py` — runs `lake env lean --run` per emitter, routes stdout into `circuit/descriptors/*.{json,tsv}`, re-pins the `*_FP` sha256 constants in five Rust files (the `GUARDED` list, `scripts/check-descriptor-drift.sh:40-47`) |
| Freshness gate | `scripts/check-descriptor-drift.sh` (regenerate-and-diff), run in CI as the `descriptor-drift` job (`.github/workflows/ci.yml:253-287`) |
| The deployed VK | Compiled into the binary: `compute_recursive_vk_hash()` = VK-v2 layered hash over program bytes (`recursive_witness_bundle.rs:103`), the AIR fingerprint of `AIR_DESCRIPTOR` (`:137`), the verifier source hash (`:123`), and the pinned Plonky3 rev (`:111`). The registry accepts exactly this one hash (`:180-186`) |
| Byte pins at rest | `*_FP` constants + `include_str!` in `circuit/src/effect_vm_descriptors.rs` etc. (self-consistency only — the drift-gate header, `check-descriptor-drift.sh:6-10`, says so plainly); the by-name predicate goldens (`circuit/src/descriptor_by_name.rs:33-40`) are additionally byte-pinned by Lean `#guard`s + `circuit-prove/tests/*_emit_gate.rs` |
| Deployment | Descriptors are committed in-repo; the flip = push + rebuild (`docs/HANDOFF-v13-VK-EPOCH.md:54-69`). `genesis.json` carries only per-app factory VKs (`node/src/genesis.rs:365-383`), never the circuit VK |

**Who could trigger a regen before this change: anyone with a shell.**
`scripts/emit-descriptors.sh` silently rewrote the tree. **What bound a deployed
VK to its source: nothing at regen time** — no record of which
`metatheory/Dregg2` tree minted the artifacts (the closest precedent was
`dregg-lean-ffi/lean-seed.pin`, which binds `DREGG_TREE_HASH` for the Lean seed
artifact — that pattern is what control 1 generalizes). **Slip-in vectors:**
(a) a regen from a tampered or *uncommitted* Dregg2 tree — the drift gate
*blesses* any Lean change, it only checks JSON↔Lean agreement; (b) a hand-edited
descriptor+FP pair (self-consistent; caught only when CI re-derives); (c) no log
that a regen ever happened.

## 2. The four controls

### Control 1 — PROVENANCE (implemented)

Every authorized regen writes `circuit/descriptors/PROVENANCE.json`: the exact
`git rev-parse HEAD:metatheory/Dregg2` tree hash, repo HEAD, a `source_dirty`
bit, the Lean toolchain, the emitter list, operator@host, UTC, and per-file
sha256 for all emitted descriptors, the by-name goldens, and the five FP-bearing
Rust files. Anyone — CI, a federation operator pre-epoch-flip — verifies with:

```
python3 scripts/emit_descriptors.py --verify-provenance            # hashes match the stamp
python3 scripts/emit_descriptors.py --verify-provenance --strict   # + clean source, tree hash
                                                                    #   matches THIS checkout
```

No Lean toolchain needed. `--strict` refuses a stamp minted from a dirty tree
(`source_dirty=true`) or one attesting a *different* Dregg2 tree than the
checkout being deployed. Honesty note: the stamp is **tamper-evident, not
tamper-proof** — a re-stamp is itself ack-gated + audit-logged, and the stamp is
a committed file, so replacing it shows in review/`git log`. The hard edge
(future work) is federation-side: bind the stamp's hash into the epoch-flip
admission message so a node *refuses* a flip whose stamp fails `--strict`
verification, alongside the existing committee check
(`federation_id` re-derivation, `verifier/src/cross_fed.rs:415-421`). That
requires an operator signing key over the stamp — deliberately not faked here.

### Control 2 — CONFIRMATION GATE (implemented)

`scripts/emit_descriptors.py` now **buffers** the whole emission, diffs against
disk, and treats a byte-identical result as an ungated no-op (so CI's drift gate
and idempotent re-runs are untouched). A **byte-changing install refuses**
(exit 3, tree untouched) unless:

- `DREGG_VK_REGEN_ACK` equals the current `git rev-parse HEAD:metatheory/Dregg2`
  — the operator must *name the exact reviewed source tree*, so a stale shell
  export from last month's regen cannot authorize today's, and a regen can never
  happen as a silent side effect; and
- if `metatheory/Dregg2` is dirty (uncommitted/untracked Lean), additionally
  `DREGG_VK_REGEN_ALLOW_DIRTY=1` — minting from an unreviewable tree is an
  eyes-open second factor, and the stamp records `source_dirty=true` (which
  `--strict` refuses, keeping dirty mints out of the deployable path).

`scripts/check-descriptor-drift.sh` deliberately passes **no ack**: on drift it
now reports and leaves the tree untouched (previously it left the tree silently
regenerated — itself a misuse vector this closes).

### Control 3 — AUDIT TRAIL (implemented)

Every authorized install or re-stamp appends one row to the git-tracked
`docs/VK-REGEN-LOG.md`: UTC, operator@host, mode (`emit` vs `stamp-existing`),
the Dregg2 tree hash, repo HEAD, the dirty bit, and the changed files. Rows are
append-only by convention; git history is the tamper-evidence.

### Control 4 — DIFFERENTIAL: covered-relation non-regression (design only)

Before an epoch flip is accepted, show the new descriptor set covers the old:
**member-for-member, name-stable, no narrowing**. The repo already has the exact
invariant shape to reuse: the wide+umem weld's Lean `#guard` pins
("member-for-member name-stable cover · NO-NARROWING invariant: traceWidth =
host+7 ∧ piCount unchanged" — `metatheory/Dregg2.lean:637`,
`metatheory/Dregg2/Circuit/Emit/EffectVmEmitUMemWeldWide.lean`) plus the Rust
per-member weld-parity tooth. The differential generalizes that to *any*
old→new regen: parse both registries through
`circuit/src/descriptor_ir2.rs::parse_vm_descriptor2`, require (i) every old
registry key present, (ii) per-member `piCount` unchanged and PI-binding offsets
stable, (iii) trace width monotone, (iv) constraint set of the old member
embeds in the new — i.e. no capability the old VK adjudicated is silently
dropped. Proposed entry point: `scripts/emit_descriptors.py --differential
<old-git-rev>` (read the old set via `git show <rev>:circuit/descriptors/...`),
with the Lean refinement statement as the proving lane. **Not implemented** —
(iv) needs a real structured-embedding check over descriptor IR2 (or the
existing faithful-commitment/refinement machinery in
`metatheory/Dregg2/Circuit/Emit/*Refine*.lean` lifted to registry granularity),
and faking it with a name-only diff would launder regressions as green.

## 3. Operator protocol (the happy path)

1. Review + commit the Lean change under `metatheory/Dregg2/`.
2. `DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)" scripts/emit-descriptors.sh`
3. Review the printed change set; commit descriptors + FP files +
   `PROVENANCE.json` + the `docs/VK-REGEN-LOG.md` row together.
4. Consumers/federation operators: `python3 scripts/emit_descriptors.py
   --verify-provenance --strict` at the deploy rev before rebuilding/flipping.
5. CI: the `descriptor-drift` job keeps re-deriving from Lean; adding a
   `--verify-provenance` step to it (after the first stamp is committed) is a
   one-line follow-up.

Bootstrap note: the initial committed stamp is `mode=stamp-existing` (hashed
from the on-disk set, not witnessed from an emit run) and records
`source_dirty=true` because in-flight lanes had uncommitted Lean at stamp time.
The first authorized `emit`-mode regen on a clean tree replaces it with a
witnessed, strict-clean stamp.

Exit codes: `0` ok/no-op · `1` routing/verify failure · `2` emitter failed ·
`3` regen refused (unauthorized byte-changing install; tree untouched).
