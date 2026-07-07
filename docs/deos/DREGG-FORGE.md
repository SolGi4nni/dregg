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
- **History lives IN the cell.** As of 2026-07-07 (`3f754287e`), a document's whole patch/blame chain
  is committed heap state (`doc_heap.rs` `COLL_HISTORY`): reopen reconstructs history, every tampered
  history byte is refused, edit ORDER is committed. A repo's log is not a side-file — it is the cell.
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
| history / log | the patch chain in the cell's heap (`COLL_HISTORY`) | built (2026-07-07) |
| branch | a fork of the repo cell (the membrane fork) | built (branch-and-stitch) |
| merge | the **pushout** (`dregg-doc::merge`) — provably sound | built |
| conflict | a first-class `ConflictRegion` | built |
| pull request | fork → stitch; the diff IS the two forks' divergence | built (mechanism) |
| code review | the **stitcher** over the `ConflictRegion` + `resolution` | built (mechanism) |
| blame | `dregg-doc::blame` over the patch chain | built |
| CI check | a verified turn whose receipt gates the merge (a `ProofCondition`) | primitives exist |
| access control | capabilities — who may push/merge/review is a cap you hold | built (the whole kernel) |
| forge host | a **forge-grain** on the community platform | FRONTIER (this doc) |

## The frontier (what to build)

Everything above is a substrate; the forge is the *product surface* welded onto it:

1. **The repo-as-cell object + a real branch/PR model.** `cell_git` today serves ONE synthetic `main`
   branch (read-mostly). A forge needs first-class branches (repo-cell forks), a `PullRequest` object
   (a proposed fork + its target + the stitch state + review threads), and merge-gated-on-review
   (the target's cap-holder resolves the `ConflictRegion` → a verified merge turn). Branch-and-stitch
   already gives the fork/diverge/stitch; the PR is the named, reviewable, cap-gated wrapper.
2. **CI as receipted turns.** A check is a turn whose `ProofCondition`/receipt is the merge gate: the
   merge cannot land until the check-turns are committed. No trusted CI runner — the proof is the pass.
   (Composes with the confined-brain grain: a CI job is a confined body driving verified turns.)
3. **The federated forge-grain.** A repo lives on a **grain** (like the homeserver-grain): confined,
   cap-metered, R2. A repo hosted on box A is fork-able by box B over the membrane; a PR crosses the
   same `MembraneEnvelope` a co-driven card does. Federation = your repo is reachable from anyone's
   client, push rights are a cap you granted. This is where forge-grain meets homeserver-grain: the
   community platform hosts both the chat rooms and the code.
4. **The surface (a deos-view face).** Repo browser / diff / review / blame as `deos-view` cards, so
   the forge paints in every glass (cockpit, browser, Discord, terminal) — like the other reflective
   cards. `cell_git` already computes the data; the forge card renders it.

## Why this is not "GitHub on dregg"

- **The history is owned + unforgeable.** A commit is a cap-gated receipted turn; a forged history is
  inexpressible (the heap root binds the patch chain). You cannot rewrite someone's blame.
- **The merge is a theorem, not a heuristic.** The pushout is provably the least state containing both
  edits; a conflict is an object you resolve, never a silent stomp.
- **Access is capabilities, not ACL rows.** "Can merge to main" is a cap you hold and can attenuate /
  delegate / revoke — the same lattice as everything else in dregg.
- **It's a member of the community, not a separate silo.** The forge-grain and the homeserver-grain
  are the same architecture; your town has both a square and a workshop.

## The first buildable slice (no kernel, no git)

Build the **`PullRequest` object + the review-as-stitcher weld** over the existing branch-and-stitch +
`dregg-doc` merge, entirely in-process, two poles: a PR whose forks merge cleanly lands a verified
merge turn; a PR with a true conflict surfaces a `ConflictRegion` that the target cap-holder must
resolve before the merge turn is admitted (an unresolved conflict → merge refused; a non-holder's
merge → refused). This is the forge's keystone, and like the homeserver body it needs neither the
localnet nor a kernel change — it welds primitives that already exist.
