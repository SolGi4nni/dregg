# The dregg-native forge — code collaboration with no git, all the way down

*Design note (2026-07-07). A code forge that is NOT a git host: dregg's own patch theory IS the
version control, a repo IS a cell, a commit IS a receipted turn, and a pull-request review IS the
stitcher. Sibling of `GRAIN-HOMESERVER.md` — the homeserver-grain hosts the community, the
forge-grain hosts its code; both ride the membrane. This is a WELD doc: the substrate already
exists (census below), the frontier is the collaboration surface + the federated hosting.*

## The thesis

Every code forge is a git host with a review UI bolted on. Git is the substrate; the forge is
chrome. Dregg inverts it: the substrate is **patch theory + capabilities + verified turns**, so the
forge is not "a nicer GitHub" — it is *what version control looks like when the history is
cryptographically owned, the merges are provably sound, and every operation is a cap-gated receipted
turn.* No git. Dregg has, as ember puts it, full Pijul.

## The substrate (already built — census, not aspiration)

- **The VCS core IS Pijul, operational.** `dregg-doc/src/depend.rs` header: *"The Pijul theory of
  patches made operational: patch dependencies, unrecord (pull a patch — and only what truly depends
  on it — out), cherry-pick (apply onto another branch), and commute (the independence test)."*
  `patch.rs` (`Patch`/`Op`/`PatchId`, compose), `merge.rs` (the **pushout** merge — Mimram–Di Giusto,
  total/commutative/associative/idempotent), `resolution.rs`/`ConflictRegion` (conflicts are
  first-class objects, never silent overwrites), `blame.rs`, `history.rs`. This is a sound-merge VCS,
  not a diff-and-pray one.
- **History lives IN the cell.** A document's whole patch/blame chain is committed heap state
  (`doc_heap.rs` `COLL_HISTORY`): reopen reconstructs history, every tampered history byte is
  refused, edit ORDER is committed. A repo's log is not a side-file — it is the cell.
- **A git-face already exists over it.** `deos-zed-full/src/cell_git.rs`: *"each save = a verified turn
  = a commit; the dregg-doc patch theory"* — it serves `status`/`blame`/`show`/`load_commit`/`diff`/
  `branches`/`head_sha`/`revparse`/`search_commits`/`file_history` off the patch chain + `History::
  replay_to`. Editors that speak git talk to dregg without knowing git isn't underneath.
- **Multi-author fork/merge IS branch-and-stitch.** `starbridge-apps/branch-stitch-multiplayer` +
  `distributed_card` + `shared_fork`: two principals fork one artifact, each edits, stitch by pushout,
  a true conflict surfaces as a `ConflictRegion`. That IS a pull request: fork → diverge → review the
  conflict → resolve by a verified patch.
- **I-confluent offline merge.** `dregg-merge` (CvRDT join) for the freely-mergeable ops.

## The mapping (git noun → dregg noun)

| Forge concept | Dregg realization | Status |
|---|---|---|
| repository | a cell (or a path-tree of cells, as `cell_git` maps paths→cells) | substrate built |
| commit | a receipted verified **turn** (a patch applied, cap-gated) | built (`cell_git`) |
| history / log | the patch chain in the cell's heap (`COLL_HISTORY`) | built |
| branch | a fork of the repo cell (the membrane fork) | built (branch-and-stitch) |
| merge | the **pushout** (`dregg-doc::merge`) — provably sound | built |
| conflict | a first-class `ConflictRegion` | built |
| pull request | fork → stitch; the diff IS the two forks' divergence | built (`pull_request.rs`) |
| code review | the **stitcher** over the `ConflictRegion` + `resolution` | built (`review.rs`) |
| blame | `dregg-doc::blame` over the patch chain | built |
| CI check | a verified turn whose receipt gates the merge (`CheckRequirement::{CommittedReceipt, Condition, CiRun}`) | built (`dregg-doc/src/check.rs` + `ci_verdict.rs`) |
| access control | capabilities — who may push/merge/review is a cap you hold | built (the whole kernel) |
| forge host | a **forge-grain** on the community platform | FRONTIER (this doc) |

## The frontier (what to build)

Everything above is a substrate; the forge is the *product surface* welded onto it:

1. **The repo-as-cell object + a real branch/PR model.** The `PullRequest` object is built
   (`dregg-doc/src/pull_request.rs`: the proposed fork + target + stitch state + review, with
   `land`/`land_checked` gated on checks and conflict resolution; `review.rs` is the
   review-as-resolution surface). Remaining frontier: first-class branches over repo-cell forks —
   `cell_git` serves ONE synthetic `main` branch (read-mostly) — and the live-repo wiring (see
   Follow-ups).
2. **CI as receipted turns — built.** `dregg-doc/src/check.rs` + `ci_verdict.rs`: a merge cannot
   land until every `RequiredCheck` is satisfied by a real cryptographic witness (signed committed
   receipt, `ProofCondition`, or work-binding `CiRun` verdict). No trusted CI runner — the proof is
   the pass. Remaining frontier: running the check job as a confined grain body (see the
   CI-runner-grain slice below).
3. **The federated forge-grain.** A repo lives on a **grain** (like the homeserver-grain): confined,
   cap-metered, R2. A repo hosted on box A is fork-able by box B over the membrane; a PR crosses the
   same `MembraneEnvelope` a co-driven card does. Federation = your repo is reachable from anyone's
   client, push rights are a cap you granted. This is where forge-grain meets homeserver-grain: the
   community platform hosts both the chat rooms and the code.
4. **The surface (a deos-view face).** Repo browser / diff / review / blame as `deos-view` cards, so
   the forge paints in every glass (cockpit, browser, Discord, terminal) — like the other reflective
   cards. `cell_git` already computes the data; the forge card renders it.

## THE FULL COMPOSITION (3-lane census, 2026-07-08) — it is ONE weld, not reinvention

A comprehensive census of the grain economy (mandate/workflow/gateway + hosting/lease/economy/grain +
market/bounty/orchestration) found that the ENTIRE forge-as-a-grain body already exists and composes.
The map:

| Lifecycle leg | Existing crate / entry point |
|---|---|
| List + rent the runner | `grain-commons::GrainRegistry`/`RentQuote` → `agent-platform::AgentPlatform::rent` |
| Fund + meter the lease (prepaid, fused meter⊗draw); lapse/reap | `hosted-lease::HostedLease` · `bill_period` · `reap_if_behind` |
| Settle rent (conserving, exactly-once) | `hosted-durable::{Settlement, LeaseCharge, SettleReceipt}` |
| Confine the runner body (one egress door) | `grain-jail::ConfinedBrain` + firmament `process-pd` / `spawn_pd_confined_exec` |
| The CI pipeline (DAG: fetch→build→test→report, no-skip, exact-+1) | `compartment-workflow-mandate` (CWM) `cwm_cell_program` + `advance_step` |
| Per-step COMPUTE budget tooth (`SPEND_ACCUM ≤ BUDGET`) | CWM `colonist_job` |
| Clearance (which runner role runs which step) | CWM `ClearanceDominates` root-bound lattice |
| Runner cap (rate/deadline/scope, revocable) | `tool-access-delegation` `Grant`/`fire_invoke`/`RevokeDelegation` |
| Runner identity + spend budget + caps body | `edge-mandate` `CapMandate` + `authorized_keys_line` |
| Artifact/log upload (volume-metered) | `storage-gateway-mandate` `fire_put` |
| Drive each step as a metered kernel turn | `agent-platform::drive_serving` → `grain-turn::ToolGatewayMinter` |
| Finalize + cross-node verify | `agent-platform::node::LocalNode` · `verify_landed`/`verify_r2` |
| Renter attestation (R2 ladder) | `grain-verify::GrainAttestation::verify_r2_for_renter` |
| Fork the runner (matrix / fan-out jobs) | `grain-fork::ConfinedSession::fork_two` (egress+budget attenuated) |
| CI-fan-out orchestration (N runners, one budget, audited) | `swarm-orchestration` (+ `agent-orchestration::audit_run`) |
| Pay to trigger / entitlement | `discharge-gateway` `PaymentEvaluator`/`ProofRequiredEvaluator` |
| **PR-as-a-bounty** (post→claim→submit→payout, no-double-pay) | `bounty-board` `BountyTreasury::payout` (conserving) |
| **CI-as-a-market-job** (post/bid/settle, conservation) | `compute-exchange` |
| Branch-protection (who changes the required-check set) | `governed-namespace` threshold-committee swap |
| **Terminal check-receipt the forge gate consumes** | **built — the weld below is LANDED** (`sdk/src/runtime.rs` signed drive path; proven end-to-end by `compartment-workflow-mandate/tests/forge_ci_weld.rs`) |

## THE ONE WELD: the executor-SIGNED terminal check receipt — LANDED (Route ii)

The forge gate `CheckRequirement::CommittedReceipt` (`dregg-doc/src/check.rs:126`) refuses an
unsigned receipt fail-closed (`CheckRefusal::Unsigned`) and Ed25519-verifies over
`canonical_executor_signed_message`. The weld is exactly one signature domain, and both signer
routes exist in-tree:

- **Route (i) — the forge's own executor signs the terminal check turn.** A check turn committed
  through the forge-grain's `ExecutorDrivenDoc` (`dregg-doc/src/executor_drive.rs:182` sets the
  key; the drive commits `Finality::Final`) produces a receipt `RequiredCheck::satisfied_by`
  accepts, with the forge-grain's executor key as the trust anchor pinned in
  `trusted_executor_keys`.
- **Route (ii) — the grain HOST signs the whole drive path (ember's chosen route; DEPLOYED).**
  The grain host is the thing doing the executing, so it is the natural signer. The SDK runtime
  installs the host's executor signing key (`sdk/src/runtime.rs:139`; the builder/setter surface
  is `with_executor_signing_key` / `set_executor_signing_key` at `sdk/src/runtime.rs:449-460`),
  and `agent-platform` threads the host seed through it
  (`agent-platform/src/node.rs:269` `runtime.set_executor_signing_key(seed)`;
  `AgentPlatform::with_executor_signing_key`, `agent-platform/src/lib.rs:456`). Every grain turn
  is `Final` + SIGNED → forge-admissible, and a CWM CI charter's terminal `advance_step` receipt
  directly satisfies `CommittedReceipt` — proven end-to-end (charter-not-terminal refused ·
  terminal signed receipt lands the PR · wrong host key refused) by
  `starbridge-apps/compartment-workflow-mandate/tests/forge_ci_weld.rs`. The grain host's key is
  a forge trust anchor, kept honest by the **audit/slashing horizon**:
  `agent-orchestration::audit_run` re-derives every receipt from the committed turns, so a host
  that signs a false pass is DETECTABLE; for deterministic / high-value workloads, random
  re-execution audits + a stake-slashing bond on the host make lying unprofitable. (Vision — the
  audit machinery exists; the slashing bond is a later economic layer.)

Beyond authorship, the WORK-binding check exists too: `CheckRequirement::CiRun`
(`dregg-doc/src/ci_verdict.rs`) is satisfied only by a signed receipt committing a `CiVerdict`
whose `input_root` equals the PR's real post-merge code and whose `exit_code == 0` — the
CI-grade gate; `CommittedReceipt` remains for approval-shaped checks.

**The same weld closes the market side (open — gap 2 below):** bind `bounty-board::payout` /
`compute-exchange::settle` to require the runner's terminal SIGNED receipt (the completion witness) —
then *PR merges → the runner's signed terminal receipt satisfies BOTH the forge merge gate AND the
bounty payout*. One signature, three gates lit (CI, bounty, market).

## The weld gaps, prioritized

Landed:

- **Signed terminal receipt** (Route ii, the one hard blocker) — the SDK runtime + agent-platform
  sign the grain drive path (see THE ONE WELD above).
- **`planned_advance_turn_hash`** on CWM — `starbridge-apps/compartment-workflow-mandate/src/lib.rs:880`,
  the pre-image so the forge can name the terminal turn before it runs (the analogue of
  `ExecutorDrivenDoc::planned_turn_hash`); exercised by `starbridge-apps/compartment-workflow-mandate/tests/forge_ci_weld.rs`.
- **The forge↔CWM weld itself** — `forge_ci_weld.rs` seeds a charter, drives it signed, and gates a
  `PullRequest` on the terminal receipt, end-to-end.

Open (the remaining new code):

1. **A production forge-grain binding** — a thin grain that hosts the weld the test proves (seed a
   CWM charter, drive it, hand the receipt to `PullRequest::present_witness`) as a leased, confined
   service rather than an in-process test.
2. **Completion-witness precondition** on `bounty-board::payout` / `compute-exchange::settle`.
3. **2→N orchestration arity** (the orchestration crates hardwire two-worker enums:
   `swarm-orchestration` `Worker`, `agent-orchestration` `WorkerSlot`) + a **forge-event→turn
   settlement reactor** (auto-payout on merge; the `CoordinatorReactor` pattern is the template).

## Forge-as-a-grain (the design, grounded in the confinement machinery)

The forge-grain is the homeserver-grain's sibling — and it reuses the EXACT machinery the
homeserver-as-a-grain proved (`docs/deos/GRAIN-HOMESERVER.md`): the firmament heavy-body `Confinement`
tier + `spawn_pd_confined_exec`, the membrane, the agent-platform lease. Three parts:

**(a) A repo is a cell; the forge SERVICE is receipted turns.** The repo state already lives in a cell
(the doc rides the umem-heap; the patch chain is committed heap state). Hosting = a **repo-grain**: a
cap-metered lease (`agent-platform` rent/host/meter/reap) over the repo cell, whose forge operations
(open PR, comment, approve, land) are the cap-gated receipted turns the forge core (`dregg-doc`
`PullRequest`/`check`/`review`) already produces. No heavy external process — the forge core is native
dregg, so the repo-grain is LIGHTER than the homeserver-grain (it needs no rocksdb/exec door).

**(b) Federated: a PR crosses the membrane between instances.** A pull request from another instance
is a fork carried over the SAME `MembraneEnvelope` a co-driven card rides (`card_carry` + the
branch-and-stitch machinery). Open-PR-from-elsewhere = `seal_fork` → cross → `rehydrate` → the target
holder reviews the `ConflictRegion` and lands a verified merge turn. Your repo is reachable from
anyone's client; push/merge rights are caps you granted and can attenuate/revoke. This is where
forge-grain meets homeserver-grain: the community platform hosts the chat rooms AND the code, over one
membrane.

**(c) CI-as-confined-grains — the part that MOST reuses tonight's work.** A check job is exactly the
heavy-body confined body we just built for the homeserver: `spawn_pd_confined_exec` a build/test runner
under a `Confinement` with {`write_path` = a scratch build dir, `exec_image` = the build tool,
`system_reads` for the toolchain, NO net (or one `net_out` proxy door for deps) — and crucially its
ONLY meaningful output is committing the check-turn receipt the merge gate demands (`check.rs`'s
`CommittedReceipt`). No trusted CI runner: the runner is a cap-bounded body that *physically cannot* do
anything but produce the receipt — the proof IS the pass, and the runner can't forge it, reach the
network, or touch anything but its scratch dir. The homeserver-grain proved a heavy rocksdb+tokio body
runs under the deny-default tier + the named doors; a CI runner is the same shape pointed at a build.

**The convergence.** homeserver-grain (community) + forge-grain (code) + CI-as-grains (verification) are
ONE substrate: the firmament confinement tier + the membrane + the agent-platform lease, pointed at
three services. Every one is confined, cap-metered, federated, and receipted — a town with a square, a
workshop, and a foundry, all built the same way, caps all the way down.

**CI-as-grains, welded to the WorkflowMandate (the census — DON'T reinvent it).** A CI pipeline is a
`compartment-workflow-mandate` (CWM) **charter**: a step DAG (fetch → build → test → report) where each
`advance_step` is a `Signature`-cap-gated, `step_clearance_ok` clearance-checked, `cwm_cell_program`-
enforced turn (teeth: `FieldLteField(STEP_CURSOR ≤ CHARTER_TERMINAL)`, `MonotonicSequence(STEP_CURSOR)`),
and the CWM **reactor** self-drives (one committed step wakes the next — the on-chain officer loop). Three
things weld:
1. **The step's WORK runs confined** — `spawn_pd_confined_exec` (firmament heavy-body tier) runs the
   build/test tool under {`write_path` = scratch, `exec_image` = the tool, no net or one proxy door}. The
   runner physically can't do anything but its build + advance the step.
2. **The terminal step's receipt IS the forge check** — the CI charter's terminal `advance_step` commits
   an executor-signed receipt; a forge `PullRequest`'s `CheckRequirement::CommittedReceipt{turn_hash}`
   (`dregg-doc/src/check.rs:126`) is bound to exactly that turn. So "merge requires CI green" = the forge
   merge gate requires the CWM charter to reach its terminal step. No trusted runner: the proof IS the
   pass, and the workflow-mandate + confinement mean the runner can neither forge the receipt nor escape.
3. **Metered** — the run's lease/discharge rides `discharge-gateway` / `agent-platform` (a CI run costs;
   the mandate discharges it), for free.
The weld keystone is BUILT: `compartment-workflow-mandate/tests/forge_ci_weld.rs` binds a forge
`RequiredCheck` to a CWM charter's terminal receipt and proves a PR gates on the charter completing
(incomplete → merge refused; terminal signed receipt → admitted; wrong host key → refused). The
confined-exec of a real build as the terminal step's work is the layered-on frontier.

**First buildable slices (safe zones, hbox-gated):** the repo-grain lease (agent-platform over a repo
cell — `agent-platform` is a root crate, coordinate) · the CI-runner grain (reuse
`spawn_pd_confined_exec` + `check.rs::CommittedReceipt` — firmament excluded ws + dregg-doc excluded ws,
CLEAN of the other terminal) · the membrane PR carry (extend `card_carry` — the pattern is proven). The
CI-runner grain is the highest-leverage next: it's the "no trusted runner" property, and it's a direct
composition of two existing pieces (the confined exec-spawn + the receipt-gated check).

## Follow-ups (post 2026-07-07 adversarial-review + surfaces session)

The forge core is built + hardened + surfaced (card in every glass; `dregg-forge` CLI). Named residues:
- **Live-repo wiring (the primary one):** a `From<PullRequest> for deos_view::ForgeView` (+ diff/conflict/
  check/review sub-shapes) in `dregg-doc`, and the CLI driving a real `DocHeapCell` / `cell_git` on-disk
  tree instead of the in-memory demo. `cell_git` already computes status/diff/blame — this is the last mile.
- **Re-export `author_of_editor` + a `bound_author()` convenience** from the dregg-doc crate root (the CLI
  had to reproduce the editor-identity fold because `review` is a private module).
- **card-carry authenticity (F4c):** fold an originator signature over `fork_root` + verify on open, so the
  tooth is authenticity-not-just-integrity in-layer (today authenticity is the Matrix transport's job — see
  `card_carry_bridge.rs` honest-scope note); + the consistent-forge test.
- **world_bridge (F4b):** confirm the deos-hermes test on hbox (the bind-semantics fix is code-correct; the
  local build kept timing out).
- **THE CI-RUNNER GRAIN (the exciting next build):** `spawn_pd_confined_exec` a check runner under the
  heavy-body `Confinement` whose only output is committing the `check.rs::CommittedReceipt` — the "no trusted
  runner, the proof IS the pass" property, a direct composition of two things shipped 2026-07-07, both in
  CLEAN excluded workspaces (firmament + dregg-doc). See the forge-as-a-grain design above.

## Why this is not "GitHub on dregg"

- **The history is owned + unforgeable.** A commit is a cap-gated receipted turn; a forged history is
  inexpressible (the heap root binds the patch chain). You cannot rewrite someone's blame.
- **The merge is a theorem, not a heuristic.** The pushout is provably the least state containing both
  edits; a conflict is an object you resolve, never a silent stomp.
- **Access is capabilities, not ACL rows.** "Can merge to main" is a cap you hold and can attenuate /
  delegate / revoke — the same lattice as everything else in dregg.
- **It's a member of the community, not a separate silo.** The forge-grain and the homeserver-grain
  are the same architecture; your town has both a square and a workshop.

## The keystone slice (no kernel, no git) — BUILT

The **`PullRequest` object + the review-as-stitcher weld** over branch-and-stitch + the `dregg-doc`
merge exists in-tree (`dregg-doc/src/pull_request.rs`, `review.rs`), with both poles: a PR whose
forks merge cleanly lands verified merge turns; a PR with a true conflict is refused
(`PullRequestError::UnresolvedConflict`) until the target cap-holder resolves it, and a
non-holder's merge is refused (`CapabilityNotHeld` on the first turn — nothing lands). It welds
primitives only — no localnet, no kernel change, no git.
