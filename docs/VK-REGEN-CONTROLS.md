# VK-REGEN CONTROLS — misuse-resistant guardrails around descriptor/VK regeneration

Regenerating the circuit descriptors **re-keys the live federation**: the AIR
fingerprint of the deployed Effect VM descriptor feeds the recursive VK hash
(`compute_recursive_vk_hash`, `circuit-prove/src/recursive_witness_bundle.rs:161`),
every verifier pins that hash (`lookup_recursive_vk`,
`circuit-prove/src/recursive_witness_bundle.rs:206`; rejection at
`verifier/src/lib.rs:793`, `"unknown recursive_vk_hash: …"` — note `:774` is a
*different* refusal, the missing-`recursive_proof` one; the pin's tooth is
`foreign_circuit_root_is_refused_by_vk_pin`,
`circuit-prove/tests/ivc_turn_chain_rotated.rs:703`), and "distributing the new
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
| The deployed VK | Compiled into the binary: `compute_recursive_vk_hash()` = VK-v2 layered hash over program bytes (`recursive_witness_bundle.rs:103`), the AIR fingerprint of `AIR_DESCRIPTOR` (`:148`), the verifier source hash (`:134`), and the pinned Plonky3 rev (`:122`). The registry accepts exactly this one hash (`:191-197`) |
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
python3 scripts/emit_descriptors.py --verify-provenance --rev HEAD  # ⇐ THE ONE THAT RUNS
python3 scripts/emit_descriptors.py --verify-provenance             # same, on the working tree
python3 scripts/emit_descriptors.py --verify-provenance --rev HEAD --strict   # + ceremony clause
python3 scripts/emit_descriptors.py --verify-by-name-routing        # the routing round trip
```

No Lean toolchain needed.

#### ⚑ Which form to run, and why the answer changed (2026-08-02)

**`--rev HEAD` is the standing form.** It materialises the revision in a detached, `git
status`-clean worktree and asks the only question that is always answerable: *are the
committed bytes what the committed stamp pins?* Wired as the `provenance` row of
`scripts/local-gates.sh` and as a CI step ahead of the drift gate. ~5s, python + git.

Without `--rev` the check grades **the working tree**, and in a tree worked by ~10 lanes that
means any sibling's in-flight emission reds it for everyone. That is not a hypothetical: it is
why this gate spent months at **zero invocations** while being fully implemented, and it
compounded into a loop with `--stamp-existing`, whose only repair path REFUSES while
`metatheory/Dregg2` is dirty — which it never isn't. Forcing it with
`DREGG_VK_REGEN_ALLOW_DIRTY=1` records `source_dirty=true`, which the checker then refuses: a
stamp that looks taken and attests nothing. Three lanes hit that wall on 2026-08-01, all three
correctly declined, and the artifacts stayed unstamped. **The escape is a detached worktree on
the WRITE side too** — `git worktree add --detach`, stamp there, commit the stamp. `f0a34748f`
did exactly that and got `source_dirty=false` while ten lanes churned the shared tree.

⚠ **`source_dirty` is checked WITHOUT `--strict`.** It used to be strict-only, which made the
one clause that catches a force-stamp reachable only through the form nothing ran. It is a
property of the committed stamp — always answerable, at any revision.

⚠ **`--strict` is for a ceremony, not for a gate.** Its extra clause compares the stamp's tree
hash against this checkout's `HEAD:metatheory/Dregg2`, which moves on **any** commit to any of
~2300 Lean modules — so as a standing check it is red within minutes of a stamp and permanently
after. Run it at an epoch flip, against the deploy revision. The question it gestures at ("are
the descriptors stale with respect to Lean?") is not answerable by comparing a tree hash anyway;
it is answered by RE-DERIVING, which is `scripts/check-descriptor-drift.sh --rev HEAD`.

The gate's own red-proof is `--self-test-provenance` (the `provenance-red` local-gates row): it
drives a mutated descriptor byte, a dropped stamp row, a stamp row whose artifact is gone, and a
`source_dirty=true` stamp, each measured as a **delta against HEAD's baseline findings** (so a
co-tenant's unrelated red cannot disable the proof), plus restore-to-baseline in both directions
and a vacuity floor. Scratch copies only.

`--verify-by-name-routing` is the leg the hash checks structurally cannot carry.
Every hash check starts from a file that EXISTS and asks whether the stamp covers
it, so a name in `metatheory/EmitByName.lean`'s `byNameDescriptors` routing table
whose artifact was **never committed** is invisible to all of them — as it is to
the emit's own coverage check (which also walks files on disk, and needs a
multi-hour Lean build to run at all) and to the derived-coverage test in
`circuit/src/effect_vm_descriptors.rs`. The Lean-side `#guard
byNameDescriptors.length == N` counts such a ghost as a member, so it passes too.
This mode parses the table's name literals STATICALLY out of the `.lean` and
reconciles table ↔ checked-in `by-name/` ↔ stamp in both directions; it needs
neither Lean nor cargo, so it keeps reporting while the emit is blocked — which is
exactly when a routing gap sits unnoticed. It is wired as CI job
`descriptor-by-name-routing` and as a fail-fast preflight in
`scripts/check-descriptor-drift.sh`. A table shape it cannot parse is FATAL, never
a pass.

`--strict` refuses a stamp minted from a dirty tree
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
disk, and treats a byte-identical result **that PROVENANCE.json already attests**
as an ungated no-op (so CI's drift gate and idempotent re-runs are untouched). A
**byte-changing install refuses** (exit 3, tree untouched) unless:

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

**Byte-identical is not the same as stamped** (fixed 2026-07-26). The no-op
short-circuit compared *emitted bytes against disk*, so a descriptor already
carrying exactly the Lean bytes but with **no row in the stamp** was invisible to
it: the emit printed `NO-OP`, exited 0, and left the coverage hole permanently
unreachable from the canonical ceremony — the only way to close one was
`--stamp-existing`, which re-stamps every file as a **disk re-hash**, demoting
`mode` from a Lean witness to self-consistency for the whole set as the price of
covering the few. Found live: the four light-client verifiers and
`dfa-routing-table-exact-public-v1.json`, all five live `include_str!` targets of
`circuit/src/descriptor_by_name.rs`, tracked and shipping with nothing attesting
their bytes. `provenance_stamp_gap()` now asks the stamp directly whether it
covers the emission (the two descriptor legs only — `fp_file_sha256` pins source
files that legitimately move), and a shortfall is a **stamp-only regen**: ack-gated
like any other provenance claim, audit-logged with what it was short of, and
written with `mode: "emit"`, which is the true claim — this run re-derived every
descriptor from Lean and found them identical. The Rust mirror of the same
invariant is `provenance_json_pins_match_checked_in_descriptor_bytes`
(`circuit/src/effect_vm_descriptors.rs`), which was the detector that caught it.

### Control 3 — AUDIT TRAIL (implemented)

Every authorized install or re-stamp appends one row to the git-tracked
`docs/VK-REGEN-LOG.md`: UTC, operator@host, mode (`emit` vs `stamp-existing`),
the Dregg2 tree hash, repo HEAD, the dirty bit, the changed files, and a
machine-readable `epoch:N` trailer. Rows are append-only by convention; git
history is the tamper-evidence.

⚑ **AND THE AUDIT TRAIL IS NOT ITS OWN GATE.** `CANONICAL_STATE_SCHEMA_EPOCH`
(`persist/src/lib.rs`) is a **Rust constant any commit can bump**, while only
`emit_descriptors.py` appends here — so on 2026-08-01 `6441705e8` moved the epoch
20 → 21 with no emit and no row, and the log stopped reconstructing the epoch
history. A check inside the emit path would reproduce that blind spot exactly.
The check is therefore keyed on the **constant** and lives outside this script:

* `scripts/check-schema-epoch-log.py` (a `scripts/local-gates.sh` row, with its
  own `--self-test`) — the last `epoch:N` row must equal the constant, the
  SCHEMA EPOCH LEDGER must be complete against `git log -p -- persist/src/lib.rs`,
  and an unparseable epoch cell is **RED, never green**.
* `dregg_persist::schema_epoch_log_row` — the same comparison one altitude closer,
  so it reds for a lane that edits the constant and runs `cargo test -p
  dregg-persist` without ever running a gate script.

Bumping the epoch is therefore a two-line ceremony: an **event row** and a
**ledger row** saying what re-genesised, what re-emits, and what now refuses to
load. Never widen the comparison to clear a red.

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
2. ⚑ **Emit from a detached worktree, not the shared tree.** In a live swarm
   `metatheory/Dregg2` is never clean, so an emit in place either REFUSES or
   (with `DREGG_VK_REGEN_ALLOW_DIRTY=1`) mints `source_dirty=true` — a stamp the
   checker refuses, which is the loop that left ten table AIRs unstamped for two
   days. Do this instead:
   ```
   git worktree add --detach /tmp/emit-wt HEAD && cd /tmp/emit-wt
   DREGG_VK_REGEN_ACK="$(git rev-parse HEAD:metatheory/Dregg2)" scripts/emit-descriptors.sh
   ```
   The tree is clean by construction, so `source_dirty=false` without anyone
   having to hold the shared tree still. (`ALLOW_DIRTY` remains, for the case
   where you genuinely mean it — but it is no longer the only way through.)
3. Review the printed change set; copy the results back and commit descriptors +
   FP files + `PROVENANCE.json` + the `docs/VK-REGEN-LOG.md` row together.
4. Consumers/federation operators, at the deploy rev before rebuilding/flipping:
   `python3 scripts/emit_descriptors.py --verify-provenance --rev <deploy-sha> --strict`.
   This is the one place `--strict` belongs — you are asserting that *this exact
   revision's* Lean source is what the stamp attests.
5. Standing gates (**wired 2026-08-02, no longer a follow-up**): the `provenance`
   and `provenance-red` rows of `scripts/local-gates.sh`, and a
   `Descriptor provenance stamp` step in `ci.yml` ahead of the drift gate. Both
   run `--verify-provenance --rev HEAD` — non-strict, because the strict clause
   reds on any unrelated `metatheory/` commit and a permanently-red gate is
   furniture. The Rust mirror
   (`effect_vm_descriptors.rs::provenance_json_pins_match_checked_in_descriptor_bytes`)
   covers the same bytes on every `cargo test -p dregg-circuit`, and as of the
   same date discovers descriptor SUBDIRECTORIES instead of naming two legs — it
   had been structurally blind to `table-airs/` since that directory landed.
6. ⚠ **NOT wired into `scripts/git-hooks/pre-push`,** deliberately and for now:
   HEAD carries an unrelated by-name routing GHOST at the time of writing, so a
   pre-push row would block every lane's push over a defect that is not theirs.
   Wire it there once HEAD is clean — that is the position where this class stops
   reaching `main` at all, and it is one line.

Exit codes: `0` ok/no-op · `1` routing/verify failure · `2` emitter failed ·
`3` regen refused (unauthorized byte-changing install; tree untouched).
