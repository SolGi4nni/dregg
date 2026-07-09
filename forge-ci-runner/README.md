# forge-ci-runner

**"Check, don't trust" CI for the dregg-native forge: the confined runner that produces a
work-binding `CiVerdict`, and the re-executor that convicts a lying host — the two faces of
one macOS-Seatbelt confined-run core.**

The forge gate `dregg_doc::CheckRequirement::CiRun` is satisfied by a committed,
executor-signed `CiVerdict` bound inside a signed turn. But the *signer* is the CI host: it
can sign a well-formed verdict for the real code while lying about what the command actually
did. This crate is the pair that closes that gap. The soundness architecture is documented
ground-truth-first in
[`docs/reference/forge-as-a-grain.md`](../docs/reference/forge-as-a-grain.md); the vision is
[`docs/deos/DREGG-FORGE.md`](../docs/deos/DREGG-FORGE.md); operating it is
[`docs/operator/forge-operations.md`](../docs/operator/forge-operations.md).

## The two faces (`src/confined.rs`, macOS-only)

- **`run_check_confined`** — the CONFINED PRODUCER (L2). Given a trusted `&History`, it
  *self-materializes* that code into a fresh dir IT controls (`materialize`, never a
  host-seeded `document.txt`), runs the check command inside a firmament Seatbelt jail
  (`ProcessKernel::spawn_pd_confined_exec`), digests stdout, reaps the exit code, and commits
  a `CiVerdict { input_root, command_id, confinement_id, exit_code, output_digest }` as the
  GENESIS turn of a fresh CI-run cell (`dregg_doc::run_ci_verdict`) — so the signed
  `turn_hash` equals the fresh-genesis re-derivation `dregg_doc::planned_ci_run_hash` the
  forge check runs. Returns a `CiRunReceipt { verdict, receipt }` to present as the forge's
  `CheckWitness::CiRun`.

- **`reexecute_and_verify`** — the AUDITOR (L3, the non-circular audit). Given a `verdict` +
  the PR's *trusted* committed `&History` (the auditor's, never the host's on-disk dir), it
  RE-MATERIALIZES that history into a fresh dir it owns, re-runs the SAME command in a fresh
  confinement, and compares `{input_root, confinement_id, exit_code, output_digest}`. Returns
  `AuditVerdict::Honest` iff every field matches, else `AuditVerdict::HostLied { field,
  claimed, recomputed }`. Because L3 re-materializes from the history rather than trusting the
  host's dir, the serve-X-commit-Y attack is caught: an honest re-run over the committed code
  Y diverges from the output a host produced over attacker code X.

## The materialization round-trip (`src/materialize.rs`, `src/lib.rs`)

A PR's code today is ONE document — the fold of one `DocGraph`'s patch `History` — so
`materialize(history, dir)` writes `document.txt` (the rendered content the command reads)
plus a `.dregg-ci/merged.history` canonical sidecar. `input_root_of_dir` recognises the
sidecar, replays it to a `DocGraph`, and returns the REAL `dregg_doc::substrate_commit` of
that graph — the exact value `canonical_input_root` and a real PR's `pr.input_root()` compute,
provenance and all. The history (not the bare graph) is the canonical unit because
`substrate_commit` binds each atom's provenance, and the only faithful public reconstruction
is a deterministic replay. Before emitting the root, `verify_faithful_materialization` checks
the tree IS the sidecar's materialization (`document.txt` equals the committed fold
byte-for-byte, no stray readable file) — else `InputRootError::Mismatch` and no root. So a
verdict this crate produces carries the `input_root` the forge L1 gate binds. The
`confinement_id(image, argv, brew)` digest is path-agnostic (the writable work dir is the
`WORK_TOKEN` placeholder, not the ephemeral path), so both runs digest to the same identity.

## The determinism requirement (load-bearing)

`output_digest` matching across the L2 run and the L3 re-run REQUIRES the check command to be
DETERMINISTIC in the confined inputs. The confinement fixes the inputs (fresh work dir, one
`execve` door, no ambient network) but the command itself must embed no nondeterminism
(wall-clock, RNG, unsorted directory walks, network fetches) — a flaky check is a
FALSE-CONVICTION hazard (L3 reports `HostLied` on an honest host whose output merely varied).
Digest a normalized artifact, not raw bytes. Because zkVM proving of a general build is
~10⁴–10⁶× native, the general-CI soundness is the optimistic stack
(`ReExecuted{quorum}` + `OptimisticChallenge` + `Staked` slash), not `Proven`.

## Scope

macOS-Seatbelt today: the executing surface (`confined.rs`) is `cfg(target_os = "macos")`
because `spawn_pd_confined_exec`'s backend is `sandbox_init` (SBPL); the pure projection/id
helpers in `lib.rs` are platform-independent. A PR is one document today, so `materialize` is
one file — a path→doc repo tree is the named onward seam.

## Build

This is an EXCLUDED workspace: its own empty `[workspace]` root, path-depending on the REAL
`dregg-doc` (`features = ["substrate"]`) and `dregg-firmament` (`features =
["process-pd-sandbox"]`), and — because a self-rooted workspace does not inherit the parent
`[patch]` — carrying the plonky3-recursion `[patch]` and ark-serialize `[patch.crates-io]`
blocks itself (kept in sync with `sel4/dregg-firmament`). It is in the repo-root `exclude`
list, so `cargo build --workspace` never pulls it.

```sh
cd forge-ci-runner && cargo test
```
