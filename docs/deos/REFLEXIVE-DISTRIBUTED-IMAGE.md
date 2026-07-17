# THE REFLEXIVE DISTRIBUTED IMAGE
## Debugging a remote sovereign image across the firmament `n`, and bridging ClusterVision as deos's collective-intelligence substrate

*An architect's treatment. The reflexive image goes distributed — suspend / branch /
time-travel / debug a REMOTE sovereign image, unforgeably and witnessed; the thing
Smalltalk and 3-Lisp structurally could not do. And `~/dev/cv` (ClusterVision) — the
record of ember orchestrating agent swarms — bridges in as the collective-intelligence
component: the swarm's work, accreted into the witnessed knowledge graph the document
language holds. The companion docs are `FIRMAMENT-REFLEXIVE-SUBSTRATE.md` (the mirror-cap
tower + Suspend this builds ON), `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` (what a distributed
branch IS), and `DOCUMENT-LANGUAGE.md` (where the collective intelligence accretes). What
I assert about cv I read from its tree (cited as `cv:<path>`); what I cite from the deos
docs is from HEAD.*

> **STATUS — the §3.3 first milestone SHIPPED (and §1's remote reflection is substantially
> built).** The mirror-cap dialed over the firmament `n` lives in `starbridge-v2/src/`:
> `remote_mirror.rs` + `remote_mirror_live.rs` + `two_image_firmament.rs` + `netlayer_image.rs`
> (the remote sovereign image over the netlayer), `meta_debug.rs` (the M5 suspend / "debug the
> debugger", `impl Presentable for MetaDebugView`), and `cv_provenance.rs` (`impl Presentable for
> CvProvenance` — the cv blame/provenance bridge of §3.3). So the "buildable this week" framing of
> §2.5 / §3.3 is now the delivered record. Two grounding corrections applied inline below: (1) the
> **mirror-cap is a `starbridge-v2` + companion-doc construct** layered over firmament's real
> `Target::Distributed{cell}` — the firmament `Target` enum (`sel4/dregg-firmament/src/lib.rs`) has
> no `Mirror` variant; (2) cv is at **v0.9.21** at HEAD. The §1 mechanism prose and §4 seams remain
> the accurate design rationale.

---

## 0. THE ONE-SENTENCE ANSWER

> **The firmament's mirror-cap (a `Capability` carrying a `Mirror{over, depth}` handle — a
> `starbridge-v2` construct over firmament's `Target::Distributed`) dialed
> over the netlayer at `n>1` makes reflection itself distributable — you inspect, branch,
> time-travel, suspend, and resume a REMOTE sovereign image through the same
> `granted ⊆ held` gate, seeing exactly the depth your mirror authorizes and nothing more,
> with the `Bounds` relaxing honestly across distance; and ClusterVision — the lossless,
> queryable corpus of ember orchestrating agent swarms (one IR across 20 harnesses, an
> event catalog of what every session *did*, and a live coordination board) — bridges in as
> the collective-intelligence source that feeds that record into the dreggverse document
> language as a living, witnessed knowledge graph.**

The reflexive-distributed image is **not new mechanism** — it is the
`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` tower (mirror-caps, the cap-stratified tower, Suspend)
read at `n>1` instead of `n=1`. The cv bridge is **not a new store** — cv already holds the
shape the document language wants (provenance, two-way links, a forest of agents), and the
work is the *welding*. This doc designs both and names the first buildable milestone.

---

## 1. THE REFLEXIVE DISTRIBUTED IMAGE

### 1.1 What "distributed reflection" is, and why it was structurally impossible before

A Smalltalk/Pharo image gives you live, suspendable, self-hosting reflection — but *local,
ambient, and unwitnessed*: anything in the image can reach the meta-level, the debugger
leaves no tamper-evident receipt, and "debug a remote image" means opening a privileged
remote-eval channel (a hole, not an attenuated handle). 3-Lisp gives you the reflective
tower but the same locality. **Neither gives you reflection that is unforgeable, witnessed,
AND distributable** (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.4). The reflexive distributed
image is exactly that missing third axis: the meta-level sits on a *different node* than the
base it reflects, and the only thing that crosses the wire is an *attenuated mirror-cap*.

The enabling fact is already in the substrate: a mirror-cap is a firmament `Capability`
(`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §1.2), and the firmament's distance parameter `n`
(`Bounds::distributed(n)` in `sel4/dregg-firmament/src/lib.rs`) resolves *any* cap local (`n=1`,
kernel/executor path) or distributed (`n>1`, the executor→net path) **with the same verbs**.
So a remote meta-level is, verbatim:

> a **mirror-cap dialed over the netlayer** (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.1) — a
> `Mirror{ over }` handle (a `starbridge-v2` construct — `remote_mirror.rs`; firmament's own
> `Target` enum carries no `Mirror` variant) whose `over` resolves to firmament's real
> `Target::Distributed{cell}` on another federation member.

### 1.2 The four reflective acts, distributed

Each act from the reflexive substrate is the SAME act at `n>1`, honestly weaker:

| act | local (`n=1`) | distributed (`n>1`) — the same handle |
|---|---|---|
| **inspect** | a `ReadState`/`Structure` mirror over `Target::Cell`, reading the live ledger fresh | a mirror whose `over` is `Target::Distributed{cell}`; the remote operator sees exactly the mirror's `depth` (Structure for an audit, ReadState to debug, Live to watch it run) — redaction enforced at the cap fabric, not by a remote-API policy (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.1) |
| **time-travel** | `History::replay_to(k)` re-derives a past head, root-verified, fail-closed on `RootMismatch` (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §1.1) | fork at a cursor whose witness slices you may not hold → **parties serve historical witnesses** trustlessly (a slice + a proof it is the slice the origin committed; Willow attested-fetch, `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §3.7) |
| **branch** | `History::fork_at(k, alt)` — a cheap, root-verified divergent configuration, mainline provably untouched | a divergent configuration of the *shared* event structure (the blocklace); free + verifiable; becomes real only by **settling on a consensus tip** (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §3.3–3.4) |
| **suspend → resume(modified)** | the `commit_turn` gate halts the local loop; the continuation is a `ConditionalBatch` (partial turn); resume drains it in topo order (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §3) | the continuation is **content-addressed portable data** — a remote operator is *handed the partial turn*, edits it, and submits the drain as a **delegated, attenuated turn over the net** (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.2) |

The continuation being a portable firmament object is the keystone: a suspended remote loop
is paused at a frozen-but-live head, its pending work is a `ConditionalBatch` whose open
`EventualRef` edges are holes/promises, and that batch is content-addressed — so "debug a
remote image's stuck turn, edit its continuation, resume it" is *handing someone an
inspectable partial turn across the wire and accepting their edited drain through the full
`commit_turn` gate*. The edit changes *which* turns run, never a turn's δ/authority shape
(`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §3.3, §5).

### 1.3 What `Bounds` relax (the honest weakening)

The `Bounds{revocation_immediate, commit_synchronous, n}` on every resolution
(`pub struct Bounds` in `sel4/dregg-firmament/src/lib.rs`) state honestly what held — and distributed reflection differs from local
*only* in these, never in the verbs (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.3):

- **`revocation_immediate`** — at `n=1`, drop the remote operator's mirror-cap and they lose
  reflective authority the instant the syscall returns. At `n>1`, the epoch lift must
  propagate; the remote mirror dies *eventually*. (This is the same non-monotone-revocation
  subtlety the distributed-time-travel semantics isolates: authority is evaluated at the
  **settlement tip**, not at branch time — `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §4.2.)
- **`commit_synchronous`** — at `n=1`, a `resume(modified_continuation)` drain is final the
  moment it returns. At `n>1`, the drain is **quorum-gated**: the remote image's continuation
  commits when the federation agrees (the branch settles on the tip).
- **the freeze consistency** — Suspend halts a *local* loop into a consistent head; halting a
  remote loop freezes the remote `World`'s head observed across a relaxing consistency bound.

### 1.4 Architecture: the distributed `MetaStack`

The `MetaStack` (the lazily-materialized 3-Lisp tower, `FIRMAMENT-REFLEXIVE-SUBSTRATE.md`
§2.2) needs *no structural change* to go distributed — a `MetaLevel` already holds a
`MirrorCap` over the level below, and the cap's `over` just resolves to a remote target.
What the distributed case adds is plumbing the cv bridge will feed (§2):

```
struct MetaLevel {
    mirror: MirrorCap,        // its `over` may be Target::Distributed{cell} on node N
    view:   MetaDebugView,    // the projection state (focus, scrub_cursor, sub-cockpit)
    node:   Option<NodeId>,   // None = local (n=1); Some(N) = remote (n>1)  ← the only addition
}
```

- **Grounding stays local.** The tower still bottoms out at the *local* native gpui loop —
  the operator's own machine is the 3-Lisp ground that keeps the whole tower drawable while
  every remote cell-loop above it is suspended (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §2.2,
  §3.5). You debug a remote image *from* your own un-suspendable floor.
- **"Debug the debugger" crosses `n`.** A `MetaLevel` over a remote `DebugFrame(k)` reflects
  a *remote operator's* meta-view — federated meta-debugging falls out of the same
  `Registry::present` dispatch (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §2.3), now viewer-and-node
  parametrized.

### 1.5 The honest hard parts

1. **Remote suspend authority is an ember-decision on the cap kind** — whether "halt a
   remote loop" is a write-class mirror right or a dedicated control-cell cap
   (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §4.2, Seam 6). Halting *someone else's* loop is a
   strong authority; it must be a cap they granted, attenuable and revocable.
2. **The freeze is not a global stop.** At `n>1` you cannot freeze the federation; you freeze
   *one* sovereign image's turn-application, observed across a consistency bound. "Suspend the
   federation" is not a thing — only "suspend a sovereign," which is correct (each sovereign
   owns its own loop; the n=1 single-machine collapse is the strong case, distributed is the
   honest-weaker one).
3. **The dataflow self-cycle is still deferred** (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §5, §6
   Seam 1): when a mirror reflects a remote `Cockpit`/`World` whose state includes the
   mirror's own view cells, the self-invalidation cycle needs stratification (unit-delay vs.
   exact). The distance `n` does not change this; the mechanism is correct under either, and
   the seam is the handoff to the fixpoint explorer, not a defect.
4. **Witness availability across `n`.** Time-travel on a remote image needs witness slices the
   operator does not hold; `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §3.7 gives the attested-fetch
   path, but the *liveness* of "someone still serves the slice you want to fork at" is a real
   availability assumption (the freshness/availability admissibility crown).

---

## 2. THE CV BRIDGE — THE COLLECTIVE-INTELLIGENCE SUBSTRATE

### 2.1 What ClusterVision actually is (read from `~/dev/cv`)

ClusterVision (`cv`, version 0.9.21, an 8-crate Rust workspace) is *not* a chat viewer — it
is a **lossless, queryable, cross-harness corpus of agent-coding work**. The README's framing
("Vibecoding is a clusterfuck. When it gets hazy, you need clustervision") undersells the
substrate underneath. Concretely, from the tree:

- **One unified IR.** `Session → Message → Block{Text | Thinking | ToolUse | ToolResult |
  File | Image}` with four normalized roles (`cv:crates/cv-core/src/ir.rs`). Twenty harnesses
  parse into it (Claude Code, Codex, Grok, OpenCode, Gemini, Hermes, OpenClaw, Cursor, Kimi,
  Qwen, LM Studio, Cline, Roo, Continue, Goose, Zed, the Claude/ChatGPT apps + account exports
  — the `harnesses!` macro, `cv:crates/cv-core/src/ir.rs:43-77`); 13 also *emit* (N-way
  conversion via the IR). No database import, no telemetry — it reads the real local session
  storage in place.
- **OpenSession** — the harness-neutral interchange format the IR is the reference
  implementation of, whose central heresy is *"cwd is metadata, not identity"*
  (the cv OpenSession design note). A session is "an ordered list of messages plus provenance";
  threading is an optional `parentId` DAG.
- **An event catalog — what a session *did*, not just said.** Every `ToolUse`/`ToolResult`
  is distilled into a normalized `Event{kind, tool, target, detail}` row in SQLite
  (`cv:crates/cv-core/src/events.rs`, `catalog.rs`). This powers `cv touched <file>` (every
  session that edited a file) and **`cv blame <file>`** — a file's git history tied back to
  the agent conversation that wrote it: *"why does this code exist?"* answered by the actual
  reasoning that produced it. This is **provenance as a queryable graph**.
- **A query calculus** — one boolean DSL (`field op value`, AND/OR/NOT, ranges, regex `~`)
  that every corpus-spanning command accepts, driven by one `FIELDS` table; evaluation is
  three-valued (`Tri`) so a catalog-cheap prefilter prunes before parsing
  (`cv:crates/cv-core/src/query.rs`). Forest-tier fields reach into the sub-agent forest:
  `agent`, `agents`, `workflow`, `workflows`, `compactions`, `subtool`.
- **Search** — full-text (tantivy) + semantic (`model2vec`); `cv recall` answers "have I
  solved this before?" (`cv:crates/cv-search/`).
- **The forest** — a deep agent run is not a flat transcript, it is a *forest*: `cv workflow`
  renders a Workflow-tool run as its real shape (phase tree → agents under each phase →
  journaled outcomes/tokens/tool-calls + the driving script); `cv tools` is cross-agent
  analytics over the whole orchestrator+subagent forest.
- **A live coordination board** — `cv:crates/cv-core/src/board.rs`: an append-only,
  cross-process message bus where agents *talk* (post status, request/reply, claim/lease,
  heartbeat, presence). Safe under many simultaneous writers across processes (per-channel
  advisory lock + POSIX `O_APPEND` atomicity). The MCP server exposes ~15 board verbs
  (`board_post/read/await/request/reply/claim/release/who/heartbeat/...`,
  `cv:crates/cv-mcp/src/main.rs`).
- **An MCP server** (`cv-mcp`) — so a *running* agent reads *other* agents' sessions mid-task:
  `list_sessions`, `search_sessions`, `read_session`, `project_sessions`, `recall`, the board
  verbs, `prune_session`, `doctor`.
- **A daemon** (`cvd`) with an HTTP API — `sync`/`watch` archives the fleet;
  `cv:crates/cvd/src/serve.rs` serves `/api/sessions`, `/api/session/{harness}/{id}` (+
  `/messages`, `/events`, `/compactions`, `/subagents`, `/subagent/{agent}`, `/workflow`),
  `/api/touched`, and the board (`/api/board`, `/api/claims`, `/api/who`).

The shape that matters for deos: **cv is already a witnessed-ish knowledge graph of work.**
Nodes = sessions and the agents in their forest; edges = `touched`/`blame` (work → file),
`parentId` (orchestrator → subagent), board messages (agent ↔ agent). It is the record of
the exact thing the deos-ux-vision memory names as the convergence: *ember orchestrating
swarms of agents over the codebase.*

### 2.2 The identification: cv's corpus IS a document-language graph, pre-witness

The dreggverse document language (`DOCUMENT-LANGUAGE.md` §1.1) identifies a document with a
cell, an edit with a patch/turn, content with the patch-fold, transclusion with a verified
cross-cell quote, and a two-way link with the witness-graph read backward. cv already holds
the *un-witnessed shadow* of every one of these:

| document-language notion | cv's existing realization |
|---|---|
| **a document / a unit of work** | a `Session` (`cv:ir.rs`) — an ordered list of typed-block messages + provenance |
| **an edit / a patch** | a `ToolUse`/`ToolResult` distilled into an `Event{file_edit, target}` (`cv:events.rs`) |
| **content = fold of edits** | the event catalog *is* the fold of what a session did to the filesystem |
| **transclusion (a verified quote)** | `cv pack` / `cv splice` — composing a new context from spans of others; the span-reference *is* a transclusion, lacking only the cryptographic quote |
| **two-way link (witness-graph backward)** | `cv blame <file>` / `cv touched <file>` — the file→session backlink, and the orchestrator→subagent `parentId` forest |
| **a branch / a fork** | `cv loom` / `cv splice` / `cv fork-and-graft` — a Janus-loom branch of a transcript, generated forward by an LLM |
| **collaborative editing / the bus** | the **coordination board** (`cv:board.rs`) — agents posting/claiming/replying across a swarm |

So cv is, structurally, *the document language's knowledge graph minus the witness layer*. The
bridge is not "import chat logs into a database"; it is **lifting cv's provenance graph onto
the cell substrate so it becomes witnessed, cap-gated, and transcludable** — the Engelbart
collective-intelligence augmentation, made sovereign.

### 2.3 How a cv query becomes a deos query over witnessed cells

The bridge is a *projection*, in both directions, because cv's IR and deos's substrate are
structurally aligned (`OpenSession` is already a clean, harness-neutral, lossy-but-honest
interchange — the same design instinct as deos's per-viewer membrane).

- **cv → deos (ingest as cells).** A `Session` becomes a cell-subgraph: the session a document
  cell, each `Message` a child cell, each `Event` an edit-patch annotation, the `parentId`
  forest the cell graph, `touched`/`blame` the backlink edges. The fold of the session's events
  is the document content (`DOCUMENT-LANGUAGE.md` §1.1's content-as-patch-fold). The lift is
  *additive*: cv's corpus is the genesis history; deos's `History::replay_to` re-derives it,
  and from then on edits to *that knowledge* are witnessed turns.
- **deos query → cv query.** cv's query calculus (`field op value`) maps almost 1:1 onto a
  deos cell query: `touched:<path>` is a backlink traversal; `agent:`/`workflow:` is a forest
  walk; `text:`/`recall` is the semantic index over message cells. A deos inspector pane that
  asks "who touched this cell / why does it exist" is *running a cv `blame`/`touched` query
  over witnessed cells* — the cv event catalog generalizes to the dregg provenance log.
- **The membrane is OpenSession's `redact`.** cv already ships `cv redact` (scrub
  secrets/PII before sharing) and `cv share` (a CSP-pinned, redacted-by-default artifact). That
  is *exactly* the per-viewer projection the document-language membrane is
  (`DOCUMENT-LANGUAGE.md` §3.2): a viewer sees the slice their mirror authorizes. cv's redact
  is the un-cap-gated prototype of the membrane; the bridge makes the redaction a *mirror-cap
  depth* (Structure / ReadState / Live).

### 2.4 Rides the cell substrate, or bridges externally? — the honest call

**Bridge externally first; ride the substrate where the witness earns its cost.** cv reads
2,245+ real local sessions across 8 harnesses with *zero import* — its whole virtue is that it
touches your real on-disk storage and stays lossless and fast. Forcing the entire corpus onto
the cell substrate up front would (a) be enormous, (b) discard cv's lazy-resolve memory
discipline (`cv:ir.rs` `materialize`, the span-not-bytes catalog), and (c) witness a vast
amount of work that nobody needs cryptographic provenance over yet. The right architecture is
a **boundary**:

- cv stays the **fast, lossless, external corpus + index** (the read/query face — exactly the
  monotone-substrate role the rhizomatic-slotting memory assigns to read-only query). It keeps
  its SQLite catalog, its tantivy/semantic index, its board.
- The **bridge lifts on demand**: when a piece of work *matters* — a design decision, a
  resolved conflict, a settled branch — it is promoted from a cv session-span into a
  **witnessed document cell** (a turn that transcludes the cv span, content-addressed,
  cap-gated). The promotion is the patch; the cv span is the transcluded source quote; the
  promotion's receipt is the provenance.
- This is the I-confluent / conservation split the rhizomatic-slotting memory names: cv is the
  monotone, append-only, mergeable read substrate; deos cells add the *one* axis cv lacks —
  conservation/authority/witness — exactly where it is load-bearing.

cv's own OpenSession `extra` bag and the `git` field (`branch`/`commit`/`remote`) are the
attachment points: a witnessed promotion writes the cell's content-address back into a
session's `extra`, so cv's index can find "which witnessed document this session became" and
`cv blame` can answer all the way through to the settled decision.

### 2.5 The concrete first bridge

The smallest end-to-end bridge that delivers real value, in three already-existing pieces:

1. **`cv-mcp` is the dialer.** A deos inspector (or an agent inside deos) calls the cv MCP
   server's `recall`/`search_sessions`/`read_session` — cv is *already an MCP server an agent
   uses mid-task* (`cv:crates/cv-mcp/src/main.rs`). The first bridge is: a deos cell-inspector
   pane whose "where was this solved before / who touched this" button is a cv MCP call,
   rendered as a Presentable. No new store; cv answers, deos presents.
2. **`cv blame` → the provenance backlink.** Wire `cv blame <cell-source-path>` into the cell
   inspector's backlinks view (`DOCUMENT-LANGUAGE.md` §1.1's two-way link): clicking a cell
   shows the agent conversation whose reasoning wrote it. This is the Engelbart augmentation in
   one gesture — code, annotated by *why it exists*, sourced from the real swarm record.
3. **The board → the live swarm feed.** cv's coordination board (`cv:board.rs`) is *already* a
   cross-process agent bus; deos surfaces it as a live cell (a `Live`-depth mirror over the
   board channel = the fleet activity feed the deos-ux-vision memory's "watch every agent work
   in one feed" wants). `cv scry` / `cvd watch` is the data; deos is the moldable inspector
   over it.

These three need *no* substrate change — cv ships them today; deos consumes them as
Presentables. That is the buildable-this-week bridge.

---

## 3. THE CONVERGENCE — EMBER ORCHESTRATING SWARMS IS THIS

### 3.1 The three pieces are one loop

The deos-ux-vision memory names the convergence directly: *"ember orchestrating swarms of
agents over the codebase (inspect/branch/commit/rewind) IS deos-in-spirit; the agent-native OS
is her daily REALITY."* The three threads of this doc are the three faces of that one loop:

- **cv records the swarm's work.** Every session, every subagent forest, every file the swarm
  touched, every board message — cv is the lossless, queryable record of the exact activity the
  deos-ux-vision memory calls the convergence (`cv:events.rs`, `board.rs`, the forest renderer).
- **The reflexive distributed image lets her inspect / branch / rewind it.** A swarm running
  across machines is a federation of sovereign images; a mirror-cap dialed over `n` lets her
  *suspend a stuck remote agent's loop, inspect its frozen-but-live head, edit its continuation,
  and resume it* — witnessed, attenuated, revocable. This is the §1 machinery pointed at the
  swarm: the agents *are* the remote images; debugging them is distributed reflection.
- **The document language is where the collective intelligence accretes.** The decisions,
  dead-ends, and hard-won understanding cv preserves are promoted (§2.4) into witnessed
  document cells — a conflicted design is a first-class *state* two agents resolve with a later
  patch (`DOCUMENT-LANGUAGE.md` §2.3), not a lost merge. The knowledge graph *compounds instead
  of rotting* (cv's own `cv distill` framing), now witnessed and sovereign.

The self-hosting loop closes exactly as the deos-ux-vision memory states: *"a session like this
runs INSIDE deos — the moldable inspector orchestrating the swarm, the document language holding
the design, the meta-debug rewinding an overboard strand, persistence keeping the image."* cv is
the missing organ that record-keeps the swarm; the reflexive distributed image is the organ that
inspects/branches/rewinds it; the document language is the organ it accretes into.

### 3.2 Why this is the Engelbart collective intelligence, made sovereign

Engelbart's augmentation thesis: a collective gets smarter by *recording, linking, and reusing*
its own work, in a system the collective lives inside and improves from within. cv is the
recording-and-linking face (provenance + backlinks + recall). The document language is the
reuse-and-accretion face (transclusion + conflicts-as-states). The reflexive distributed image
is the *living-inside-and-improving-from-within* face — and dregg adds the one thing Engelbart's
NLS and every successor lacked: **the augmentation is cap-secure and witnessed**. The collective
record cannot be silently tampered (every promotion is a receipted turn); reflection over a
collaborator's image is an *attenuated mirror*, not ambient access; and it is *distributable*,
so the collective can span machines without a trusted central image.

### 3.3 The first buildable milestone `[SHIPPED — starbridge-v2/src/cv_provenance.rs + meta_debug.rs + remote_mirror*.rs]`

**Milestone: "Blame this cell" — the cv provenance backlink, live in the deos inspector.**

The smallest slice that is end-to-end real, demonstrates the convergence, and needs no
substrate change:

1. **Stand up the cv MCP dialer in deos.** A deos inspector pane calls `cv-mcp`'s
   `recall`/`read_session`/`search_sessions` and renders the result as a Presentable (the
   moldable-inspector framework already has the Presentable/Gadget spine). cv answers; deos
   presents. *(cv ships this today; deos adds one Presentable.)*
2. **Wire `cv blame` into the cell inspector's backlinks.** Selecting a cell whose `source_path`
   is a real file shows the agent conversation that wrote it — the two-way link of
   `DOCUMENT-LANGUAGE.md` §1.1, sourced from cv's event catalog. *"Why does this cell exist?"*
   answered by the swarm's actual reasoning.
3. **Surface the board as a live fleet feed.** A `Live`-depth mirror over a cv board channel,
   presented as a cell — the "watch every agent work in one feed" the deos-ux-vision memory
   wants, now a deos object you can click into (AOL-wonder) and inspect/modify live (Pharo).

That is the buildable now. It proves the bridge (cv → deos query over the work record), seats
the collective-intelligence substrate, and is the front edge from which §1's distributed
reflection grows: once the swarm's agents are deos sovereign images and cv records them, "blame
this cell" generalizes to "suspend, inspect, and resume the *remote agent* that wrote it" —
distributed reflection over the collective record.

**Sequencing.** Steps 1–3 are independent and ship on cv-as-it-is + one Presentable each. The
§2.4 on-demand promotion (cv span → witnessed document cell) is the *next* milestone — it
introduces the first witnessed turn over cv-sourced content and is the seam where the document
language and the cell substrate meet the corpus. §1's remote-suspend (the mirror-cap over `n`
pointed at a remote agent) sequences after the local reflexive tower (`FIRMAMENT-REFLEXIVE-
SUBSTRATE.md` §6 Tasks A–C) lands and the federation is multi-node; it is the same handle, dialed
across the gorge.

---

## 4. THE SEAMS (the honest residual)

1. **Remote suspend authority** — an ember-decision on the cap kind (write-class mirror vs.
   dedicated control-cell cap); halting another sovereign's loop is strong authority and must be
   a granted, attenuable, revocable cap (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §6 Seam 6).
2. **The dataflow self-cycle** — deferred to the fixpoint explorer; distance `n` does not change
   it (`FIRMAMENT-REFLEXIVE-SUBSTRATE.md` §5–6 Seam 1).
3. **Witness availability across `n`** — time-travelling a remote image needs witness slices
   someone still serves; the attested-fetch path exists, the *liveness* is an availability
   assumption (the freshness/availability admissibility crown).
4. **The cv boundary is a real boundary, not a wall.** cv stays external for the corpus; the
   bridge promotes work onto cells *on demand*. The seam is the promotion (§2.4) — and per the
   "seams are work, not walls" discipline, the closure lane is the §3.3 next-milestone (the first
   witnessed promotion turn), running with the bridge, not parked.
5. **cv's `extra`/`git` back-references** — the promotion must write the witnessed cell's
   content-address back into the cv session's `extra` so `cv blame` can answer through to the
   settled decision; a one-field convention, not a schema change.
6. **OpenSession ↔ cell-subgraph correspondence** is lossy-but-honest by construction (both are
   designed that way); the lift must be *additive* (cv corpus = genesis history, re-derivable by
   `History::replay_to`), never a destructive rewrite of the real on-disk sessions cv reads.

---

*( ◕‿◕ ) a closing couplet, since the swarm's record is just a mirror turned outward:*
*the image learned to climb its own reflective stair —*
*now it dials a mirror across the gorge, and reads the swarm's work there.*
