# The Refinement Design — from substrate to something people live in

This document is the design synthesis for the refinement epoch: how dregg moves
from "a verified substrate with witness-apps" to "a system real applications are
natural in," soundly, without spending the verification capital we built. It is
organized around five load-bearing design decisions, then the sequencing.

The problems it answers (the honest census): apps program against raw slots like
assembly; the SDK makes the unauthorized path the easiest one; identity is a hex
key; the deployed node sits partly outside the theorems' hypotheses; nothing
reacts; one node runs. None of these requires new theory. Most require *assembly
of what is already verified into what can be lived in* — plus two real builds:
the data model and identity.

---

## Decision 1 — THE HEAP: cell state becomes registers + an openable map
*(the keystone; everything else composes with it)*

### The diagnosis

A cell's programmable state is eight anonymous `[u8;32]` slots. Real
applications need named fields, growable collections (members, names, entries,
votes), and references. The polis lane bit-packed council members into slot
positions and capped membership at N≤3 — that is the system telling us the slot
model fails at the first real app. Mina's zkApps shipped with exactly this shape
(8 field elements) and its entire ecosystem's pain became commitment-roots and
off-chain state machinery bolted on after the fact. We can do deliberately what
that ecosystem did under duress.

### The design

**Hybrid: a register file plus a heap.** Two access patterns genuinely exist,
so the split carves at a joint:

- **Registers** — N small named scalar fields (today's 8 slots, grown to 16 in
  the rotation). These are the *state machine*: status codes, thresholds,
  staged hashes, counters. Every turn touches them; their circuit cost must
  stay flat per-turn. The `FactoryDescriptor` gains a `fields` declaration
  (`name → register index, type`) so programs, inspectors, and the language
  speak names; compilation resolves indices. (The studio's worked examples
  already fake this; make it real.)

- **The heap** — one register holds `heap_root`: a **sorted Poseidon2 Merkle
  map** over `(collection_id, key) → value`. Collections of unbounded size;
  pay-per-touch proving (each touched key = one membership/update opening,
  O(log n) hashing); untouched data costs nothing.

**The crucial reuse:** the heap is the *generalization of the capability root
we already built and proved*. `cap_root` is an openable sorted-Poseidon2 tree
with cell≡circuit identity proven, membership-open + leaf-update + sorted-
insert gates landed, and the non-membership opening proven for nullifiers.
The heap is the same gadget family with a generic leaf. This is reuse of
verified machinery, not invention.

**The kernel does not grow.** The `write` verb's specification has read
"guarded **heap**/program/permission update" since the VerbRegistry was
written — the eight slots were the placeholder heap. Heap operations are
`write`-verb instances under the same frame discipline. Building the heap is
*completing the verb's own specification*. Lean side: `RecordKernelState`
gains the heap component; `stateStepGuarded` extends; the conservation and
frame theorems extend trivially (the heap is balance-neutral by construction);
the guard algebra gains `heap_contains / heap_get` atoms whose coordination
cost is classified exactly like the existing relational atoms.

**Wire/executor:** turns carry heap witnesses for touched keys; the verified
producer reconstructs by commit-gated replay — the same `CapOp`/`StateOp`
lever proven five times this session.

### The rotation bundle

Layout changes ride **one** rotation (the standing discipline), which is
already owed: registers 8→16 + `heap_root` + the W1 signed-well balance
representation + the RESERVED column removal + the 186→159 column compaction
+ PI v3. One VK/commitment epoch, one descriptor regeneration (Lean emit +
Rust goldens together), succession drill #2. The deployment-correspondence
fixes land in the same wave: genesis seeded by issuer-moves (so
`reachable_total_zero` applies to the *deployed* chain) and fees as moves.

### What it dissolves

Slot budget (councils of any N) · collections (real nameservice: one
declaration) · the counter patterns (threshold over a counter register whose
increments are proven by heap-update old-values) · most of the "toy" feeling,
because apps stop being slot-packing puzzles.

---

## Decision 2 — IDENTITY IS A GOVERNANCE CELL
*(the polis machinery we built is the identity layer we lack)*

Identity today is a hex pubkey and an env token. The houyhnhnm answer is not
an identity *product* bolted on — it falls out of what we built:

- **A person's identity is a small council cell** governing their key set.
  One device = 1-of-1. Two devices = 1-of-2 for daily acts, 2-of-2 for grave
  ones (the threshold gate, exactly as built). Adding a device = a proposal;
  losing a device = a revocation; **recovery = a 2-of-3 council of friend
  cells empowered to rotate the key set** — social recovery as constitutional
  amendment, with the cooling-period TemporalGate making theft-by-recovery
  slow and visible. Every piece is landed, proven machinery.
- Staging: (1) *now* — named local profiles in the cipherclerk
  (`dregg id create ember`, persistent default; days of work); (2) the
  identity-council factory + SDK verbs (`id.add_device`, `id.recover_via`);
  (3) petnames — the cipherclerk's existing petname DB syncs against the
  now-real heap-backed nameservice.

This is the most houyhnhnm-grade idea available to us: *your identity is a
tiny constitution.*

---

## Decision 3 — CELLS ARE LAW, AGENTS ARE WILL, RECEIPTS ARE THE NERVOUS SYSTEM
*(the reactivity model — where app logic lives)*

Cell programs are passive law: they constrain, they never act. Apps need
reaction. The honest model, stated once and built to:

- **The receipt stream is the event bus.** The node gains
  `/api/events/stream` (SSE); the SDK gains
  `node.subscribe(filter) → Stream<Receipt>`; the site's poll-refresh becomes
  push.
- **Agents are the actuators.** A reactive app = a mandate-cell (built) + an
  agent process holding its attenuated capability (built) + a subscription
  (small). The agent reacts to receipts by exercising turns; the mandate
  bounds what its reaction *can* do; the receipts of its reactions are
  themselves auditable. The agent-orchestration usecase stops being a demo
  and becomes the standard app runtime shape.

No daemons inside cells, ever — that would re-smuggle ambient authority. The
triad keeps the law/will separation that makes the system verifiable.

---

## Decision 4 — CROSS-CELL READS ARE VERIFIED OBSERVATIONS
*(the principled answer to the deepest expressiveness gap — staged later)*

Constraints reading other cells' live state would couple commits across cells
(the I-confluence cost is real and the classifier would say so). Two-stage
answer:

1. **Now (with the uplift):** copy-at-birth becomes first-class — a
   descriptor `imports` block with content-addressed provenance, so the
   pattern stops feeling like a workaround and the lie-visibility is
   structural.
2. **Later (post-heap):** a turn may carry a **state proof of another cell at
   a finalized height** as a witness — the light-client machinery turned
   inward. "Oracle by proof": not shared state, but verified observation of
   finalized state, which *commutes* (coordination-free by the classifier).
   One proof-verify per read, priced honestly.

---

## Decision 5 — THE SDK COLLAPSES TO TWO NOUNS AND AUTHORIZATION-FIRST

- **You cannot express an unauthorized act.** `Authorization::Unchecked`
  leaves the public API (internal genesis only). The path of least
  resistance becomes: `Identity → .turn() → typed verb builders
  (.transfer/.write/.grant/…) → .sign() → .submit()`. The factories/polis
  builders already have this shape; it becomes the *only* public shape; raw
  `Action`/`Turn` construction moves to a `raw` module.
- **Two user-facing nouns:** `Receipt` (with `.proof()` lazily attached —
  the five internal proof types disappear from the surface) and
  `AttestedHistory` (the light-client artifact). Everything else is plumbing.
- The 5,000-line cipherclerk splits: key custody / session client / explain.

---

## The distributed reality: n=3, live

`peer_count: 0` forever is the gap between proven capability and lived
reality. Stand up nodes 2 and 3 (same graviton, port-separated systemd
templates, the existing federation.json genesis). The code paths are
harness-tested; running them live is the cheapest way to surface
correspondence debt nothing else can find. Then the first shipware drill on
real infrastructure: partition node 3, let 1+2 progress, heal, verify
convergence. The status page reading `peer_count: 2` is the first true
sentence of the form "this is a distributed OS."

---

## Sequencing (waves; green-or-bust; one rotation)

- **R1 (running now):** language uplift (sender/context atoms, composite
  gates) · devnet truth (proofs attach; producer coverage) · DSL census →
  one-core design · proof economics + pickles beachhead.
- **R2 (the keystone wave):** THE HEAP — Lean model + circuit gadget (cap_root
  reuse) + executor replay + **the one rotation bundle** (registers 16,
  heap_root, signed wells, RESERVED removal, column compaction, PI v3,
  genesis/fee correspondence). Parallel, disjoint: SDK authorization-first
  collapse · identity step 1 (named profiles) · federation n=3 live.
- **R3 (the lamesauce exit):** the language gains named fields + collections
  compiling to registers+heap · nameservice/council/feed **rebuilt as real
  apps** · reactivity (SSE + subscribe + the agent-actuator pattern) ·
  identity-as-council.
- **R4 (the home):** cross-cell reads by proof · the image becomes the shell
  (boot into your polis) · factory publishing as app distribution · the
  performance epoch (proving latency, archive size, wasm size).

Standing disciplines throughout: every wave keeps the deployed system inside
the theorems' hypotheses (correspondence is half of assurance); teach-what-is
in every outward artifact; no fallbacks, green or bust; the verified artifact
is the running artifact.
