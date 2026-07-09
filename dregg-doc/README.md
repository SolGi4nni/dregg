# dregg-doc

**The patch-theory document core AND the dregg-native code forge — a Pijul-shaped VCS
where merge is the categorical pushout, review is resolution, and a pull request cannot
land until every required check is satisfied by a cryptographic witness, not a bool.**

A dreggverse document is a *patch-theoretic object* (`src/lib.rs`): a graph of
alive/dead content atoms with order-edges, an edit is a `Patch` (`Op::Add` /
`Delete`(tombstone) / `Connect` / `SetField`), `merge` is the total-union pushout
(Mimram–Di Giusto), and a conflict is a first-class *state* — an antichain of live,
mutually-unordered alternatives resolved by a later patch, never a merge failure. On top
of that core sits the forge: PR / merge / review-as-resolution and the CI check gate. The
soundness architecture is documented ground-truth-first in
[`docs/reference/forge-as-a-grain.md`](../docs/reference/forge-as-a-grain.md); the vision
is [`docs/deos/DREGG-FORGE.md`](../docs/deos/DREGG-FORGE.md); operating it is
[`docs/operator/forge-operations.md`](../docs/operator/forge-operations.md).

## The patch core (default, standalone)

With the feature off this is a dependency-free core of pure data structures + algorithms
(`cargo test`-able in isolation):

| type / fn | what it is |
|---|---|
| `DocGraph`, `Atom`/`AtomId`/`Provenance`/`Status` | the graph of atoms + order-edges + the single-valued field store |
| `Patch` (`Op::{Add,Delete,Connect,SetField}`) | the authored grammar: `apply`, `compose`, `invert` (RCCS reversibility) |
| `History` | a document *as* its patch-history; `replay`/`replay_to` (time-travel), `branch`/`stitch` |
| `dependencies` / `commute` / `unrecord` / `cherry_pick` | the theory of patches — deps, commutation, surgical pull/graft |
| `Doc` / `Granularity` | ergonomic authoring: `edit` diffs text (token LCS) into the minimal patch |
| `merge` / `content` / `blame` | the pushout; the fold with `ConflictRegion`s; correct content-addressed authorship |
| `render_three_way` / `merge_base` / `Regime` | the diff3 view; the two-regime (prose antichain vs. field-conservation) classifier |
| `resolutions` / `resolve_connect` / `resolve_keep` / `resolve_field` | one-click resolution patches — the conflict view *becomes* an editor |
| `commit` / `Commitment` | binds atoms/edges/fields *with provenance* so a light client can't be shown a hidden alternative |

## The forge (the `substrate` feature)

`--features substrate` rides the document onto the REAL dregg cell substrate (a document
IS a `dregg_cell::Cell`, an edit IS a real `dregg_turn::Turn` through the genuine
`TurnExecutor` — cap-gated, finalized, journaled) and unlocks the forge modules:

- **`PullRequest`** (`pull_request.rs`) — a `head` `History` offered against a `base`.
  `merge` is refused (`PullRequestError::UnresolvedConflict`) while any conflict stands;
  once clean it yields a `MergeOutcome` (merged `DocGraph` + the landing patch set).
  `land` drives each landing patch through `ExecutorDrivenDoc::edit` (`executor_drive.rs`,
  the crate's sole executor entry) — a non-holder of the region edit cap is refused
  in-band with `TurnError::CapabilityNotHeld`. `input_root()` is
  `substrate_commit(merged_graph())` — the digest that binds a verdict to *this* PR's code.

- **The check gate** (`check.rs`) — `land_checked` verifies every `RequiredCheck { id,
  requirement }` against a presented witness BEFORE driving any merge turn, refusing with
  `PullRequestError::CheckNotSatisfied`. The proof IS the pass; no trusted CI runner. A
  `CheckRequirement` is one of `CommittedReceipt` (binds authorship: a trusted-key-signed
  finalized receipt for a named `turn_hash`), `Condition` (a `ProofCondition`), or
  **`CiRun`** — the work-binding check.

- **`CiVerdict`** (`ci_verdict.rs`) — the statement "`command_id` ran in `confinement_id`
  against `input_root` → `exit_code` + `output_digest`", committed INSIDE a signed
  genesis check-turn (its `turn_hash` re-derived via `planned_ci_run_hash` and matched to
  the receipt, so a loose verdict can't forge the binding). `CiRun` accepts it only when
  `input_root == pr.input_root()` and `exit_code == 0`. Anti-replay is the
  `CiNullifierAccumulator` (a committed `dregg_commit` Merkle tree with a shareable root +
  membership/non-membership proofs); `publish_nullifier_root` / `fetch_nullifier_root` are
  the federation cross-node leg (schemes real, HTTP call out-of-test).

- **`CiAssurance`** (`ci_assurance.rs`) — the legible tradeoff lattice, weakest→strongest,
  each variant documented at the type with a uniform trust / cost / latency / determinism /
  *catches-a-liar?* block:
  `TrustedSigned{keys}` (one signed verdict, no) → `ReExecuted{keys, quorum}` (quorum of
  distinct-active-key matching attestations, a divergence → `Conviction`, **yes**) →
  `OptimisticChallenge{keys, window}` (a fraud-proof window; a challenger's divergent
  verdict posted to the `blocklace` is an equivocation `detect_upheld_challenge` convicts)
  → `Proven{vk}` (a real `dregg-circuit` STARK binding the verdict as public inputs +
  a pass-gate — proves the pass-gate + verdict-binding, NOT the execution) →
  `Staked{bond_ref, inner}` (a wrapper). Keys are a governed, rotatable/revocable
  `GovernedKeySet`; a `Conviction` is unforgeable (private fields, `evaluate`-only minters).

- **`StakedBond`** (`staked_bond.rs`) — the real economic slash behind `Staked`. A
  `SlashOutcome` can only be built from a real `Conviction` (`from_conviction`); `slash_bond`
  moves the bonded amount out of the lying host to a beneficiary conservingly (the
  `dregg_cell` signed-`i64` balance ledger, `Σδ = 0`) and at-most-once (the `escrow_sealed`
  committed-heap `Consumed` one-shot flag). A satisfied policy leaves the bond `release_bond`-able.

- **`ReviewThread`** (`review.rs`) — comments + approvals as cryptographically-owned,
  receipted document atoms: a comment is an `Op::Add` authored by its reviewer through
  `ExecutorDrivenDoc::edit`, attributable by `blame`, immutable once said. The reading side
  (`comments_of` / `approvals_of`) is standalone; posting needs the executor.

Other features: `cell-heap` (the commitment ride alone — projects a `DocGraph` into a real
cell heap via `substrate_commit`, no executor; `substrate` includes it) and `rope` (the
`ropey::Rope` editor-buffer bridge).

## Build

This is an EXCLUDED workspace (its own empty `[workspace]` in `Cargo.toml`, out of the
parent `cargo build --workspace`, mirroring the parent `[patch]` for `ark-serialize`). The
default core builds anywhere; the forge needs the feature:

```sh
cd dregg-doc && cargo test                      # the standalone patch core
cd dregg-doc && cargo test --features substrate  # + the forge (PR / check / verdict / assurance / bond / review)
```
