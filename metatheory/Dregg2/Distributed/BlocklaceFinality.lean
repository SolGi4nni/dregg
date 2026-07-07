/-
# Dregg2.Distributed.BlocklaceFinality — a FAITHFUL, EXECUTABLE model of the node's
# REAL blocklace finalization rule (`blocklace/src/ordering.rs::tau`), wired to the executor.

**The gap this closes.** `Dregg2/Distributed/Consensus.lean` is a free-floating BFT *algebra*: it
carries an *abstract* `Committed` predicate (a `superRatifiedFromLace` record) and proves quorum-
intersection safety over it, but it NEVER models the algorithm the running node actually computes.
The node (`node/src/blocklace_sync.rs::poll_finalized_blocks`) does NOT consult an abstract
"is-committed" oracle: it calls `dregg_blocklace::ordering::tau(&lace, &participants)` — a concrete
function that

  1. `compute_rounds`        — round(b) = 1 + max(round(p) | p ∈ preds), genesis = 1 (DAG depth);
  2. `find_all_final_leaders`— for each wave w, the round-robin `wave_leader(w)`; if it has EXACTLY
     ONE block at the wave-start round (no equivocation) AND that block `is_super_ratified` (a
     supermajority of DISTINCT participants have wave-end blocks that ratify it), it is a final
     leader;
  3. `tau`                   — walk final leaders in wave order, collect each leader's coverage
     (union of causal pasts of ratifying wave-end blocks), take the blocks NEW to this segment
     (minus equivocators), `xsort` them, append — producing the total order;

and then SLICES `ordered[executed_up_to..]` and feeds those turns to `TurnExecutor::execute`.

This module models THAT computed rule — `computeRounds` / `findAllFinalLeaders` / `tauOrder` as
genuine **executable Lean functions over `Lace`** (not an abstract record) — proves a REAL safety
property the node relies on (**no two conflicting final leaders per wave**; for finalized-prefix
monotonicity under lace growth see `Dregg2.Consensus.TauPrefixMonotone`, where it is proved
CONDITIONAL — `tau_finalized_prefix_monotone` under `FinalizedRegionStable` — and REFUTED
unconditionally by an honest-laggard counterexample the live node does NOT exclude), CONNECTS it
to the verified executor
(`Exec.ConsensusExec.executeFinalized`, the cell `execFullForestG` commits onto), and ships a
**DIFFERENTIAL**: the computed Lean `tauOrder` and the Rust `ordering.rs::tau` AGREE on a concrete
multi-node trace (the Lean model reproduces the exact order the node finalizes).

## SCOPE — what is faithful, what is simplified, what is the named residual.

FAITHFUL (matches `ordering.rs` line-for-line as a pure function):
* `computeRounds` — the round = 1 + max(pred rounds), genesis = 1 recurrence (`compute_rounds`).
* `roundToWave` / `waveFirstRound` / `waveLastRound` / `waveLeader` — the wave arithmetic and the
  round-robin `participants[w % len]` leader (`ordering.rs:147..170`).
* `superMajority n = 2n/3 + 1` (`supermajority_threshold`).
* `approves` / `ratifies` / `isSuperRatified` / `findAllFinalLeaders` — the approval→ratification→
  super-ratification ladder over the causal past (`ordering.rs:184..336`), reading the SAME
  equivocation guard (`hasEquivInPast`).

SIMPLIFIED (a faithful PROJECTION, stated, not hidden):
* `causalPastIncl` uses a fuel bound (the lace length) for the BFS — totalizing the DAG walk; the
  Rust `causal_past` is an unbounded BFS over the same edge set. On any concrete (finite, acyclic)
  lace the fuel = |lace| is sufficient, so the two coincide (the differential exhibits this).
* `xsort` intra-segment tie-break is the OPEN-CM-XSORT residual (named in `ConsensusExec`); here we
  linearize a segment by `(round, id)` — deterministic, causal-respecting on the traces we exhibit;
  the SAFETY theorem (no conflicting leader) does NOT depend on the tie-break, only on WHICH leaders
  anchor, exactly as `cordial_agreement` is about the anchor.

The safety theorems proved here — `finalLeaders_one_per_wave` / `tauOrder_deterministic` — are
properties the NODE relies on: a wave anchors at most one leader and the order is a deterministic
function of (lace, participants). "Finalization is append-only" (T5, finalized-prefix
monotonicity) is NOT unconditional for this rule: `Dregg2.Consensus.TauPrefixMonotone` proves it
under `FinalizedRegionStable` (closed finalized region) and exhibits an HONEST counterexample —
a lagging validator's late round-2/round-3 blocks grow an already-final wave's coverage and land
MID-PREFIX — which the node's `executed_up_to` index slicing (`blocklace_sync.rs`) does not
tolerate. See that module's header for the node-side implication.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.BlocklaceFinality`.
-/
import Dregg2.Exec.ConsensusExec
import Std.Data.HashMap
import Std.Data.HashSet

namespace Dregg2.Distributed.BlocklaceFinality

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)

/-! ## 1. `computeRounds` — the DAG-depth recurrence (`ordering.rs::compute_rounds`).

round(b) = 1 + max over present predecessors of round(p); genesis (no present preds) = 1. The Rust
runs Kahn topological order; here we fold over the lace already pre-sorted by `seq` (the node also
sorts by `(seq, creator)` before building the ordering lace — `build_ordering_blocklace`), which is
a topological order for the honest virtual-chain discipline (`seq` strictly increases along an
author's chain, and a pred always has strictly smaller `seq` of its own author OR is another
author's earlier block). We memoize into an assoc list. -/

/-- Look up an already-computed round for a block id. -/
def roundLookup (rs : List (BlockId × Nat)) (h : BlockId) : Option Nat :=
  (rs.find? (fun p => p.1 = h)).map (·.2)

/-- One folding step of `compute_rounds`: given the rounds computed so far (`rs`) and the next
block `b` (in topological order), assign `round(b) = 1 + max(round(p) | p ∈ b.preds present in rs)`,
defaulting the max to `0` for genesis (so genesis gets round `1`). Mirrors `ordering.rs:82..93`. -/
def roundOfStep (rs : List (BlockId × Nat)) (b : Block) : Nat :=
  let predRounds : List Nat := b.preds.filterMap (fun p => roundLookup rs p)
  1 + predRounds.foldl Nat.max 0

/-- **`computeRounds B`** — fold `roundOfStep` over the lace pre-sorted by `seq` then `creator`
(the node's `build_ordering_blocklace` sort), producing the `(id, round)` map. Genesis blocks get
round `1`; depth increases by one per causal layer. (`ordering.rs::compute_rounds`.) -/
def computeRounds (B : Lace) : List (BlockId × Nat) :=
  let sorted := B.toArray.qsort (fun a b => a.seq < b.seq || (a.seq == b.seq && a.creator < b.creator))
  sorted.foldl (fun rs b => (b.id, roundOfStep rs b) :: rs) []

/-- The round of a specific block id in the computed map (`0` if absent — only for ids not in `B`). -/
def roundOf (B : Lace) (h : BlockId) : Nat :=
  (roundLookup (computeRounds B) h).getD 0

/-! ## 2. Wave arithmetic + round-robin leader (`ordering.rs:147..170`). -/

/-- The supermajority threshold `⌊2n/3⌋ + 1` (`ordering.rs::supermajority_threshold`). -/
def superMajority (n : Nat) : Nat := (n * 2 / 3) + 1

/-- `round_to_wave`: rounds are 1-indexed; wave 0 = rounds `[1, w]`. (`ordering.rs:147`.) -/
def roundToWave (round wavelength : Nat) : Nat := (round - 1) / wavelength

/-- `wave_first_round` (`ordering.rs:152`). -/
def waveFirstRound (wave wavelength : Nat) : Nat := wave * wavelength + 1

/-- `wave_last_round` (`ordering.rs:157`). -/
def waveLastRound (wave wavelength : Nat) : Nat := (wave + 1) * wavelength

/-- **`waveLeader`** — the round-robin leader `participants[wave % len]` (`ordering.rs:167`).
`none` when there are no participants (the Rust caller guards this). -/
def waveLeader (wave : Nat) (participants : List AuthorId) : Option AuthorId :=
  if participants.isEmpty then none
  else participants[wave % participants.length]?

/-! ## 3. Causal past (fuel-bounded BFS over the present-pred edge set — `ordering.rs::causal_past`). -/

/-- One BFS layer: expand a frontier of ids to the union with their present predecessors. -/
def expandPreds (B : Lace) (frontier : List BlockId) : List BlockId :=
  frontier.flatMap (fun h => match B.lookup h with
                              | some b => b.preds.filter (fun p => B.has p)
                              | none   => [])

/-- Fuel-bounded transitive closure of `expandPreds` starting from `[h]`. `fuel = B.length` is
sufficient for any finite acyclic lace (each layer adds at least one strictly-smaller-depth block).
Returns the accumulated id set (deduped), INCLUSIVE of `h` (`causal_past_inclusive`). -/
def causalPastAux (B : Lace) : Nat → List BlockId → List BlockId → List BlockId
  | 0,        _,        acc => acc.dedup
  | _,        [],       acc => acc.dedup
  | fuel + 1, frontier, acc =>
      let nxt := (expandPreds B frontier).filter (fun p => ¬ acc.contains p)
      causalPastAux B fuel nxt (acc ++ nxt)

/-- **`causalPastIncl B h`** — the inclusive causal past of `h` (`h` itself + everything it
observes), fuel = `B.length`. (`ordering.rs::causal_past_inclusive`.) -/
def causalPastIncl (B : Lace) (h : BlockId) : List BlockId :=
  causalPastAux B B.length [h] [h]

/-! ## 4. Equivocation-in-past, approval, ratification, super-ratification (`ordering.rs:120..278`). -/

/-- **`hasEquivInPast`** — a creator has two DISTINCT blocks at the SAME round, both in the
observer's causal past (`ordering.rs::has_equivocation_in_past`). The exact equivocation guard the
node's `approves`/`tau` consult to repel a forking creator. -/
def hasEquivInPast (B : Lace) (observer : BlockId) (creator : AuthorId) : Bool :=
  let past := causalPastIncl B observer
  let creatorBlocks : List Block :=
    past.filterMap (fun bid => match B.lookup bid with
                                | some b => if b.creator = creator then some b else none
                                | none   => none)
  -- two distinct creator-blocks sharing a round ⇒ equivocation visible from observer.
  creatorBlocks.any (fun a =>
    creatorBlocks.any (fun b => a.id ≠ b.id && roundOf B a.id == roundOf B b.id))

/-- **`approves`** — observer block `o` approves leader `l`: `l` is in `o`'s causal past AND no
equivocation by `l.creator` is visible from `o` (`ordering.rs:184..200`). -/
def approves (B : Lace) (o l : Block) : Bool :=
  (causalPastIncl B o.id).contains l.id && ¬ hasEquivInPast B o.id l.creator

/-- **`ratifies`** — block `o` ratifies leader `l` iff a supermajority of DISTINCT participants
have at least one block in `o`'s causal past that approves `l` (`ordering.rs:206..234`). -/
def ratifies (B : Lace) (participants : List AuthorId) (o l : Block) : Bool :=
  let past := causalPastIncl B o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && approves B b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

/-- All block ids at a given round in `B`. -/
def blocksAtRound (B : Lace) (r : Nat) : List BlockId :=
  (B.filter (fun b => roundOf B b.id == r)).map (·.id)

/-- **`isSuperRatified`** — a supermajority of DISTINCT participants have wave-end blocks that
ratify the leader (`ordering.rs:240..278`). The node's finality condition for a leader. -/
def isSuperRatified (B : Lace) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := blocksAtRound B waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if ratifies B participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

/-! ## 5. `findAllFinalLeaders` — the wave loop (`ordering.rs:283..336`).

For each wave `w` from `0` up to the wave containing `maxRound`: take the round-robin
`waveLeader w`. Collect that creator's blocks at the wave-START round. If there is EXACTLY ONE
(no equivocation at the leader slot) AND it `isSuperRatified` by the wave-END round, it is a final
leader. We bound the wave count by `maxRound` (the deepest block), which the node bounds by
`max_round`. -/

/-- The maximum computed round over the lace (`compute_rounds`' returned `max_round`). -/
def maxRound (B : Lace) : Nat :=
  (B.map (fun b => roundOf B b.id)).foldl Nat.max 0

/-- The leader's candidate blocks: creator = `waveLeader w` at the wave-START round. The node
requires EXACTLY ONE (`leader_blocks.len() == 1`) — a second block at the slot is the leader itself
equivocating, which forfeits the wave. -/
def leaderCandidates (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && roundOf B b.id == ws)

/-- **`finalLeaderAt`** — the (optional) final leader anchoring wave `w`: the unique leader-slot
block, if super-ratified by the wave end. Mirrors the body of `find_all_final_leaders`' loop. -/
def finalLeaderAt (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : Option Block :=
  match leaderCandidates B participants wave wavelength with
  | [l] => if isSuperRatified B participants l (waveLastRound wave wavelength) then some l else none
  | _   => none  -- zero candidates (leader silent) OR ≥2 (leader equivocated at the slot)

/-- **`findAllFinalLeaders`** — the final leaders in wave order. We iterate waves `0..waveCount`
where `waveCount` is the wave containing `maxRound` (the node breaks when `wave_end > max_round`).
(`ordering.rs:283..336`.) -/
def findAllFinalLeaders (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List Block :=
  let mr := maxRound B
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => finalLeaderAt B participants w wavelength)

/-! ## 6. `tauOrder` — the total order (`ordering.rs::tau`, lines 402..480).

Walk final leaders in wave order; for each, collect coverage (union of causal pasts of ratifying
wave-end blocks), take the NEW blocks (minus previous coverage, minus equivocators), linearize, and
append. The intra-segment linearization is the OPEN-CM-XSORT residual; here we sort by `(round, id)`
— deterministic and causal-respecting (a pred has strictly smaller round). -/

/-- The coverage of a final leader: union of causal pasts of all wave-end blocks that ratify it
(`ordering.rs:442..458`). -/
def leaderCoverage (B : Lace) (participants : List AuthorId) (l : Block) (wavelength : Nat) : List BlockId :=
  let lr := roundOf B l.id
  let lwave := roundToWave lr wavelength
  let waveEnd := waveLastRound lwave wavelength
  let endBlocks := blocksAtRound B waveEnd
  (endBlocks.flatMap (fun bid => match B.lookup bid with
     | some b => if ratifies B participants b l then causalPastIncl B bid else []
     | none   => [])).dedup

/-- Deterministic intra-segment linearization by `(round, id)` — the OPEN-CM-XSORT stand-in. A
predecessor has a strictly smaller round, so this respects causal order; ties (concurrent blocks)
break by `id`, exactly the Rust `xsort`'s deterministic by-block-id tie-break. -/
def xsortBy (B : Lace) (ids : List BlockId) : List BlockId :=
  (ids.toArray.qsort (fun a b =>
    roundOf B a < roundOf B b || (roundOf B a == roundOf B b && a < b))).toList

/-- **`leaderSegment B participants wavelength prevCovered l`** — the blocks a final leader `l`
APPENDS to the order: its coverage minus the previously-covered set, minus equivocators visible
from the leader, linearized by `xsortBy`. The per-leader segment of `ordering.rs::tau`'s loop
body, hoisted so the prefix-monotonicity analysis (`Consensus.TauPrefixMonotone`) can speak
about one wave's contribution. -/
def leaderSegment (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (prevCovered : List BlockId) (l : Block) : List BlockId :=
  let coverage := leaderCoverage B participants l wavelength
  let newBlocks := (coverage.filter (fun bid => ¬ prevCovered.contains bid)).filter
    (fun bid => match B.lookup bid with
      | some b => ¬ hasEquivInPast B l.id b.creator
      | none   => false)
  xsortBy B newBlocks

/-- **`tauStep`** — one iteration of `ordering.rs::tau`'s leader loop: append the leader's
segment to the order accumulated so far, and replace `prevCovered` with this leader's coverage
(exactly the Rust `prev_covered = coverage`). Hoisted to the top level so the fold is a named
object theorems can decompose. -/
def tauStep (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (acc : List BlockId × List BlockId) (l : Block) : List BlockId × List BlockId :=
  (acc.1 ++ leaderSegment B participants wavelength acc.2 l,
   leaderCoverage B participants l wavelength)

/-- **`tauOrder B participants wavelength`** — the computed total order (`ordering.rs::tau`). -/
def tauOrder (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  ((findAllFinalLeaders B participants wavelength).foldl
    (tauStep B participants wavelength) ([], [])).1

/-! ## 6b. THE MEMOIZED FAST PATH — the SAME `tauOrder`, with the causal past computed ONCE.

**Why.** The pure `tauOrder` above RE-COMPUTES `causalPastIncl` for the same block ids an
EXPONENTIAL number of times: `ratifies` rebuilds an observer's past and, per past block, calls
`approves` (another past) + `hasEquivInPast` (another past); `isSuperRatified` calls `ratifies` per
wave-end block; `findAllFinalLeaders` calls `isSuperRatified` per wave; `leaderCoverage` calls
`ratifies` + `causalPastIncl` again. On a cross-linked DAG (the live `n=5` shape) this nested
re-traversal blows up — the finality-FFI wedge the node hit (the `dregg_tau_order` export pinned a
tokio worker and starved the runtime).

**The fix, proof-preserving.** A parallel stack that threads a `PastCache` — each block's inclusive
causal past computed ONCE — mirroring the Rust `PastCache` (`blocklace/src/ordering.rs:41`). Every
function gets a `…C` twin that LOOKS UP the past instead of recomputing it; each twin is proved EQUAL
(`…C_eq`) to its pure original at `cache = mkPastCache B`, so the safety theorems and `#guard`s about
`tauOrder`/`tauGolden`/`findAllFinalLeaders` (which the originals back) are untouched. The
order-faithful equality `tauOrderFast_eq : tauOrderFast = tauOrder` lets the live gate exports
(`FinalityGate.tauOrderGate`/`finalizeGate`) run the FAST path while every proof that named `tauOrder`
stays valid by rewriting through the equality. Building the cache is `O(|B|)` calls to the
(individually polynomial) `causalPastIncl`, and the lookups replace the exponential re-traversal — the
blow-up is gone (the §9 `…Fast` `#guard`s witness identical output on the concrete trace). -/

/-- A memo of each block's inclusive causal past — an assoc list keyed by `BlockId`, the Lean
analogue of the Rust `PastCache` (`HashMap<BlockId, Rc<HashSet<BlockId>>>`). -/
abbrev PastCache := List (BlockId × List BlockId)

/-- Build the cache: compute `causalPastIncl B b.id` ONCE per block in `B`. -/
def mkPastCache (B : Lace) : PastCache :=
  B.map (fun b => (b.id, causalPastIncl B b.id))

/-- Look up a block's causal past in `cache`, FALLING BACK to the pure `causalPastIncl` on a miss (an
id not in `B`). The fallback makes correctness UNCONDITIONAL: `cachedPast B (mkPastCache B) h` is
ALWAYS `causalPastIncl B h` — a hit returns the value the cache stored (= `causalPastIncl B h`), a
miss recomputes it. On the live path every observed id is present, so it is always a hit (the
speedup). -/
def cachedPast (B : Lace) (cache : PastCache) (h : BlockId) : List BlockId :=
  match cache.find? (fun p => p.1 == h) with
  | some p => p.2
  | none   => causalPastIncl B h

/-- **`cachedPast_eq`** — the cache is FAITHFUL: a lookup via `mkPastCache B` returns EXACTLY the pure
`causalPastIncl B h`, for every `h`. So replacing `causalPastIncl` with `cachedPast … (mkPastCache B)`
anywhere is value-preserving — the engine of every `…C_eq` below. -/
theorem cachedPast_eq (B : Lace) (h : BlockId) :
    cachedPast B (mkPastCache B) h = causalPastIncl B h := by
  unfold cachedPast
  cases hf : (mkPastCache B).find? (fun p => p.1 == h) with
  | none => rfl
  | some p =>
    have hp1 : p.1 = h := by
      have h2 := List.find?_some hf
      simpa using h2
    have hmem : p ∈ mkPastCache B := List.mem_of_find?_eq_some hf
    unfold mkPastCache at hmem
    obtain ⟨b, _hb, hbp⟩ := List.mem_map.mp hmem
    have hb_id : b.id = p.1 := by rw [← hbp]
    have hb_v : causalPastIncl B b.id = p.2 := by rw [← hbp]
    show p.2 = causalPastIncl B h
    rw [← hb_v, hb_id, hp1]

/-! ### THE ROUND CACHE — the SECOND memoization, killing `computeRounds` recomputation.

**Why.** The `PastCache` above memoized the causal past, but it did NOT touch the OTHER un-memoized
recompute in this file: `roundOf B h` is `roundLookup (computeRounds B) h` — it folds `computeRounds`
over the WHOLE lace on EVERY call, and `roundOf` is called pervasively (inside `maxRound`'s `B.map`,
`blocksAtRound`'s `B.filter`, the `xsortBy` qsort comparator twice-per-comparison, and the nested
`creatorBlocks.any (… creatorBlocks.any (… roundOf …))` of `hasEquivInPast`). So even with the past
memoized, the fast fold re-derived `computeRounds B` (itself O(n²) over the `List`-backed lace)
thousands of times per finalization — the EXACT `causalPast`-class sibling, on the same live
`@[export] dregg_tau_order` / `dregg_blocklace_finalize` path.

**The fix, proof-preserving.** A `RoundCache` = `computeRounds B` built ONCE (the Lean analogue of the
Rust `rounds: HashMap<BlockId, u64>`, `ordering.rs::compute_rounds`), threaded alongside `cache`. Each
round-reading primitive gets an `…R` twin that LOOKS UP the precomputed rounds; each is proved EQUAL
to its pure original at `rc = mkRoundCache B` — definitionally (`rfl`), since `roundOfR (mkRoundCache B)`
unfolds to exactly `roundOf B`. The `…C` fast twins now thread `rc` and call the `…R` primitives, so
`computeRounds B` is folded ONCE per finalization instead of per-`roundOf`. The `…C_eq` theorems keep
their statements (now also fixing `rc = mkRoundCache B`) and the safety theorems / `#guard`s about the
pure rule are untouched. -/

/-- A memo of the computed round map — `computeRounds B` built ONCE (the Lean analogue of the Rust
`rounds: HashMap<BlockId, u64>`, `ordering.rs::compute_rounds`). -/
abbrev RoundCache := List (BlockId × Nat)

/-- Build the round cache: run the `computeRounds` fold over `B` ONCE. -/
def mkRoundCache (B : Lace) : RoundCache := computeRounds B

/-- `roundOf` against a precomputed round cache (the lookup that replaces the per-call recompute). -/
def roundOfR (rc : RoundCache) (h : BlockId) : Nat := (roundLookup rc h).getD 0

theorem roundOfR_eq (B : Lace) (h : BlockId) : roundOfR (mkRoundCache B) h = roundOf B h := rfl

/-- `maxRound` against the cache. -/
def maxRoundR (rc : RoundCache) (B : Lace) : Nat :=
  (B.map (fun b => roundOfR rc b.id)).foldl Nat.max 0

theorem maxRoundR_eq (B : Lace) : maxRoundR (mkRoundCache B) B = maxRound B := rfl

/-- `blocksAtRound` against the cache. -/
def blocksAtRoundR (rc : RoundCache) (B : Lace) (r : Nat) : List BlockId :=
  (B.filter (fun b => roundOfR rc b.id == r)).map (·.id)

theorem blocksAtRoundR_eq (B : Lace) (r : Nat) :
    blocksAtRoundR (mkRoundCache B) B r = blocksAtRound B r := rfl

/-- `xsortBy` against the cache. -/
def xsortByR (rc : RoundCache) (ids : List BlockId) : List BlockId :=
  (ids.toArray.qsort (fun a b =>
    roundOfR rc a < roundOfR rc b || (roundOfR rc a == roundOfR rc b && a < b))).toList

theorem xsortByR_eq (B : Lace) (ids : List BlockId) :
    xsortByR (mkRoundCache B) ids = xsortBy B ids := rfl

/-- `leaderCandidates` against the cache. -/
def leaderCandidatesR (rc : RoundCache) (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && roundOfR rc b.id == ws)

theorem leaderCandidatesR_eq (B : Lace) (participants : List AuthorId) (wave wavelength : Nat) :
    leaderCandidatesR (mkRoundCache B) B participants wave wavelength
      = leaderCandidates B participants wave wavelength := rfl

/-- `hasEquivInPast` with both caches (`§4`). -/
def hasEquivInPastC (B : Lace) (cache : PastCache) (rc : RoundCache) (observer : BlockId) (creator : AuthorId) : Bool :=
  let past := cachedPast B cache observer
  let creatorBlocks : List Block :=
    past.filterMap (fun bid => match B.lookup bid with
                                | some b => if b.creator = creator then some b else none
                                | none   => none)
  creatorBlocks.any (fun a =>
    creatorBlocks.any (fun b => a.id ≠ b.id && roundOfR rc a.id == roundOfR rc b.id))

theorem hasEquivInPastC_eq (B : Lace) (observer : BlockId) (creator : AuthorId) :
    hasEquivInPastC B (mkPastCache B) (mkRoundCache B) observer creator = hasEquivInPast B observer creator := by
  simp only [hasEquivInPastC, hasEquivInPast, cachedPast_eq, roundOfR_eq]

/-- `approves` with both caches (`§4`). -/
def approvesC (B : Lace) (cache : PastCache) (rc : RoundCache) (o l : Block) : Bool :=
  (cachedPast B cache o.id).contains l.id && ¬ hasEquivInPastC B cache rc o.id l.creator

theorem approvesC_eq (B : Lace) (o l : Block) :
    approvesC B (mkPastCache B) (mkRoundCache B) o l = approves B o l := by
  simp only [approvesC, approves, cachedPast_eq, hasEquivInPastC_eq]

/-- `ratifies` with both caches (`§4`). -/
def ratifiesC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId) (o l : Block) : Bool :=
  let past := cachedPast B cache o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && approvesC B cache rc b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

theorem ratifiesC_eq (B : Lace) (participants : List AuthorId) (o l : Block) :
    ratifiesC B (mkPastCache B) (mkRoundCache B) participants o l = ratifies B participants o l := by
  simp only [ratifiesC, ratifies, cachedPast_eq, approvesC_eq]

/-- `isSuperRatified` with both caches (`§4`). -/
def isSuperRatifiedC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := blocksAtRoundR rc B waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if ratifiesC B cache rc participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

theorem isSuperRatifiedC_eq (B : Lace) (participants : List AuthorId) (l : Block) (waveEndRound : Nat) :
    isSuperRatifiedC B (mkPastCache B) (mkRoundCache B) participants l waveEndRound
      = isSuperRatified B participants l waveEndRound := by
  simp only [isSuperRatifiedC, isSuperRatified, blocksAtRoundR_eq, ratifiesC_eq]

/-- `finalLeaderAt` with both caches (`§5`). -/
def finalLeaderAtC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (wave wavelength : Nat) : Option Block :=
  match leaderCandidatesR rc B participants wave wavelength with
  | [l] => if isSuperRatifiedC B cache rc participants l (waveLastRound wave wavelength) then some l else none
  | _   => none

theorem finalLeaderAtC_eq (B : Lace) (participants : List AuthorId) (wave wavelength : Nat) :
    finalLeaderAtC B (mkPastCache B) (mkRoundCache B) participants wave wavelength
      = finalLeaderAt B participants wave wavelength := by
  simp only [finalLeaderAtC, finalLeaderAt, leaderCandidatesR_eq, isSuperRatifiedC_eq]

/-- `findAllFinalLeaders` with both caches (`§5`). -/
def findAllFinalLeadersC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (wavelength : Nat) : List Block :=
  let mr := maxRoundR rc B
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => finalLeaderAtC B cache rc participants w wavelength)

theorem findAllFinalLeadersC_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    findAllFinalLeadersC B (mkPastCache B) (mkRoundCache B) participants wavelength
      = findAllFinalLeaders B participants wavelength := by
  simp only [findAllFinalLeadersC, findAllFinalLeaders, maxRoundR_eq, finalLeaderAtC_eq]

/-- `leaderCoverage` with both caches (`§6`). -/
def leaderCoverageC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId)
    (l : Block) (wavelength : Nat) : List BlockId :=
  let lr := roundOfR rc l.id
  let lwave := roundToWave lr wavelength
  let waveEnd := waveLastRound lwave wavelength
  let endBlocks := blocksAtRoundR rc B waveEnd
  (endBlocks.flatMap (fun bid => match B.lookup bid with
     | some b => if ratifiesC B cache rc participants b l then cachedPast B cache bid else []
     | none   => [])).dedup

theorem leaderCoverageC_eq (B : Lace) (participants : List AuthorId) (l : Block) (wavelength : Nat) :
    leaderCoverageC B (mkPastCache B) (mkRoundCache B) participants l wavelength
      = leaderCoverage B participants l wavelength := by
  simp only [leaderCoverageC, leaderCoverage, roundOfR_eq, blocksAtRoundR_eq, cachedPast_eq, ratifiesC_eq]

/-- `leaderSegment` with both caches (`§6`). -/
def leaderSegmentC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId) (wavelength : Nat)
    (prevCovered : List BlockId) (l : Block) : List BlockId :=
  let coverage := leaderCoverageC B cache rc participants l wavelength
  let newBlocks := (coverage.filter (fun bid => ¬ prevCovered.contains bid)).filter
    (fun bid => match B.lookup bid with
      | some b => ¬ hasEquivInPastC B cache rc l.id b.creator
      | none   => false)
  xsortByR rc newBlocks

theorem leaderSegmentC_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (prevCovered : List BlockId) (l : Block) :
    leaderSegmentC B (mkPastCache B) (mkRoundCache B) participants wavelength prevCovered l
      = leaderSegment B participants wavelength prevCovered l := by
  simp only [leaderSegmentC, leaderSegment, leaderCoverageC_eq, hasEquivInPastC_eq, xsortByR_eq]

/-- `tauStep` with both caches (`§6`). -/
def tauStepC (B : Lace) (cache : PastCache) (rc : RoundCache) (participants : List AuthorId) (wavelength : Nat)
    (acc : List BlockId × List BlockId) (l : Block) : List BlockId × List BlockId :=
  (acc.1 ++ leaderSegmentC B cache rc participants wavelength acc.2 l,
   leaderCoverageC B cache rc participants l wavelength)

theorem tauStepC_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauStepC B (mkPastCache B) (mkRoundCache B) participants wavelength = tauStep B participants wavelength := by
  funext acc l
  simp only [tauStepC, tauStep, leaderSegmentC_eq, leaderCoverageC_eq]

/-- **`tauOrderFast B participants wavelength`** — the SAME finalized order as `tauOrder`, computed
with BOTH the causal past (`mkPastCache B`) AND the round map (`mkRoundCache B`) memoized ONCE, shared
by the whole fold. This is the function the live gate exports run; both whole-lace derived maps are
built once instead of being re-derived per `roundOf`/`causalPastIncl` call. -/
def tauOrderFast (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  let cache := mkPastCache B
  let rc := mkRoundCache B
  ((findAllFinalLeadersC B cache rc participants wavelength).foldl
    (tauStepC B cache rc participants wavelength) ([], [])).1

/-- **`tauOrderFast_eq`** — the memoized fast path computes EXACTLY the pure `tauOrder` (order-faithful,
not merely set-equal). So every theorem and `#guard` that names `tauOrder` transfers to `tauOrderFast`
by rewriting, and the live gate may run the fast path with no loss of the verified guarantee. -/
theorem tauOrderFast_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauOrderFast B participants wavelength = tauOrder B participants wavelength := by
  simp only [tauOrderFast, tauOrder, findAllFinalLeadersC_eq, tauStepC_eq]

/-! ## 6c. THE RUNTIME FAST PATH — `@[implemented_by]` over `Std.HashMap`/`Std.HashSet`.

**Why this exists, and why it is SOUND.** The §6b `…C` fast twins killed the *within-call*
exponential re-traversal by memoizing into `List`-backed caches (`PastCache`/`RoundCache`), but the
DATA STRUCTURES are still `List`s: `cachedPast`'s `cache.find?` (:319) is an O(n) scan per lookup,
`causalPastAux`'s `acc.dedup`/`acc.contains` (:135,:138) are O(n)/elem, and `mkPastCache` (:311)
rebuilds ALL of them per FFI call — so the exported `dregg_tau_order` is O(n³)-to-build and pays it
every finality poll (docs/VERIFIED-GATE-PERF.md: 9.2 s @ 35 blocks). This section adds a runtime
twin backed by `Std.HashMap`/`Std.HashSet` (O(1) dedup/contains/lookup) and attaches it to
`tauOrderFast` via `@[implemented_by]`.

`@[implemented_by]` is TRUSTED — the kernel does NOT check the twin equals the pure def; a wrong
twin silently corrupts finality with no theorem catching it (every theorem/`#guard` is about the
PURE def). Two disciplines make it safe:
  1. The twin below is a LINE-FOR-LINE mirror of the §6b `…C` functions with the sole change of
     `List.find?`/`.contains`/`.dedup` → `Std.HashMap`/`Std.HashSet` operations.
  2. The `@[implemented_by]` is attached ONLY to `tauOrderFast`; the pure `tauOrder`,
     `causalPastIncl`, and every `…C`/`…R` def keep their normal compilation. So the §9 differential
     `#guard tauOrderFast … == tauOrder …` and `#guard fastCausalPastIncl … == causalPastIncl …`
     compare the FAST-compiled twin against the PURE-compiled def (NOT fast-vs-fast) — a genuine,
     non-vacuous check on the golden 3-node trace, the equivocation trace, AND a fresh round-2-shaped
     multi-wave n=4 DAG (`traceMW4`). -/

/-- BFS layer expansion with a `Std.HashSet` frontier-dedup — the runtime twin of `causalPastAux`.
Produces the IDENTICAL id list as `causalPastAux B B.length [h] [h]`: BFS order preserved (frontier
processed left-to-right, each block's `preds` in order), first-occurrence dedup (a pred already
`seen` is skipped, exactly as `acc.dedup` keeps the first). O(1) `HashSet` membership replaces the
pure def's O(n) `List.contains`/`.dedup`. Terminates because `seen` grows and is bounded by `|B|`. -/
partial def fastCausalPastAux (B : Lace) (seen : Std.HashSet BlockId) (acc : Array BlockId)
    (frontier : List BlockId) : Array BlockId :=
  match frontier with
  | [] => acc
  | _ =>
    let (seen, acc, nxt) := frontier.foldl (init := (seen, acc, ([] : List BlockId)))
      (fun st hid =>
        match B.lookup hid with
        | some b =>
          b.preds.foldl (init := st) (fun st p =>
            let (s, a, n) := st
            if B.has p && !s.contains p then (s.insert p, a.push p, n ++ [p]) else (s, a, n))
        | none => st)
    fastCausalPastAux B seen acc nxt

/-- Runtime twin of `causalPastIncl` (HashSet-backed BFS). Value-identical; §9 differential-guarded. -/
def fastCausalPastIncl (B : Lace) (h : BlockId) : List BlockId :=
  (fastCausalPastAux B ((∅ : Std.HashSet BlockId).insert h) #[h] [h]).toList

/-- The past cache as a `Std.HashMap` (O(1) lookup) — the runtime twin of `mkPastCache`. Built ONCE
per finalization; first-occurrence-keyed (skip if already present), matching `cachedPast`'s
`find?`-first-hit on `mkPastCache`. -/
def fastPastMap (B : Lace) : Std.HashMap BlockId (List BlockId) :=
  B.foldl (init := (∅ : Std.HashMap BlockId (List BlockId)))
    (fun m b => if m.contains b.id then m else m.insert b.id (fastCausalPastIncl B b.id))

/-- The round map as a `Std.HashMap` (O(1) lookup) — the runtime twin of `mkRoundCache`
(`computeRounds`), built ONCE with `Std.HashMap.get?` replacing the pure fold's `roundLookup`
`List.find?`. Same topological fold over the `(seq, creator)`-sorted lace. -/
def fastRoundMap (B : Lace) : Std.HashMap BlockId Nat :=
  let sorted := B.toArray.qsort (fun a b => a.seq < b.seq || (a.seq == b.seq && a.creator < b.creator))
  sorted.foldl (init := (∅ : Std.HashMap BlockId Nat))
    (fun rm b => rm.insert b.id (1 + (b.preds.filterMap (fun p => rm.get? p)).foldl Nat.max 0))

/-- O(1) past lookup with a LAZY pure fallback (the `match`, not `getD`, keeps the fallback from
being computed on a hit) — the runtime twin of `cachedPast`. -/
@[inline] def fastPast (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (h : BlockId) : List BlockId :=
  match pm.get? h with
  | some v => v
  | none   => fastCausalPastIncl B h

/-- O(1) round lookup — the runtime twin of `roundOfR`. -/
@[inline] def fastROf (rm : Std.HashMap BlockId Nat) (h : BlockId) : Nat := rm.getD h 0

/-- Runtime twin of `hasEquivInPastC`. -/
def fastHasEquivInPast (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (observer : BlockId) (creator : AuthorId) : Bool :=
  let past := fastPast B pm observer
  let creatorBlocks : List Block :=
    past.filterMap (fun bid => match B.lookup bid with
                                | some b => if b.creator = creator then some b else none
                                | none   => none)
  creatorBlocks.any (fun a =>
    creatorBlocks.any (fun b => a.id ≠ b.id && fastROf rm a.id == fastROf rm b.id))

/-- Runtime twin of `approvesC`. -/
def fastApproves (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (o l : Block) : Bool :=
  (fastPast B pm o.id).contains l.id && ¬ fastHasEquivInPast B pm rm o.id l.creator

/-- Runtime twin of `ratifiesC`. -/
def fastRatifies (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (o l : Block) : Bool :=
  let past := fastPast B pm o.id
  let approvingParticipants : Nat :=
    (participants.filter (fun p =>
      past.any (fun bid => match B.lookup bid with
                            | some b => b.creator == p && fastApproves B pm rm b l
                            | none   => false))).length
  approvingParticipants ≥ superMajority participants.length

/-- Runtime twin of `blocksAtRoundR`. -/
def fastBlocksAtRound (B : Lace) (rm : Std.HashMap BlockId Nat) (r : Nat) : List BlockId :=
  (B.filter (fun b => fastROf rm b.id == r)).map (·.id)

/-- Runtime twin of `isSuperRatifiedC`. -/
def fastIsSuperRatified (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (l : Block) (waveEndRound : Nat) : Bool :=
  let endBlocks := fastBlocksAtRound B rm waveEndRound
  let ratifyingCreators : List AuthorId :=
    (endBlocks.filterMap (fun bid => match B.lookup bid with
       | some b => if fastRatifies B pm rm participants b l then some b.creator else none
       | none   => none)).dedup
  ratifyingCreators.length ≥ superMajority participants.length

/-- Runtime twin of `leaderCandidatesR`. -/
def fastLeaderCandidates (B : Lace) (rm : Std.HashMap BlockId Nat) (participants : List AuthorId)
    (wave wavelength : Nat) : List Block :=
  match waveLeader wave participants with
  | none => []
  | some lk =>
      let ws := waveFirstRound wave wavelength
      B.filter (fun b => b.creator == lk && fastROf rm b.id == ws)

/-- Runtime twin of `finalLeaderAtC`. -/
def fastFinalLeaderAt (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wave wavelength : Nat) : Option Block :=
  match fastLeaderCandidates B rm participants wave wavelength with
  | [l] => if fastIsSuperRatified B pm rm participants l (waveLastRound wave wavelength) then some l else none
  | _   => none

/-- Runtime twin of `maxRoundR`. -/
def fastMaxRound (B : Lace) (rm : Std.HashMap BlockId Nat) : Nat :=
  (B.map (fun b => fastROf rm b.id)).foldl Nat.max 0

/-- Runtime twin of `findAllFinalLeadersC`. -/
def fastFindAllFinalLeaders (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wavelength : Nat) : List Block :=
  let mr := fastMaxRound B rm
  let waveCount := if wavelength == 0 then 0 else mr / wavelength + 1
  (List.range waveCount).filterMap (fun w => fastFinalLeaderAt B pm rm participants w wavelength)

/-- Runtime twin of `leaderCoverageC`. -/
def fastLeaderCoverage (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (l : Block) (wavelength : Nat) : List BlockId :=
  let lr := fastROf rm l.id
  let lwave := roundToWave lr wavelength
  let waveEnd := waveLastRound lwave wavelength
  let endBlocks := fastBlocksAtRound B rm waveEnd
  (endBlocks.flatMap (fun bid => match B.lookup bid with
     | some b => if fastRatifies B pm rm participants b l then fastPast B pm bid else []
     | none   => [])).dedup

/-- Runtime twin of `xsortByR`. -/
def fastXsortBy (rm : Std.HashMap BlockId Nat) (ids : List BlockId) : List BlockId :=
  (ids.toArray.qsort (fun a b =>
    fastROf rm a < fastROf rm b || (fastROf rm a == fastROf rm b && a < b))).toList

/-- Runtime twin of `leaderSegmentC`. -/
def fastLeaderSegment (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wavelength : Nat) (prevCovered : List BlockId) (l : Block) : List BlockId :=
  let coverage := fastLeaderCoverage B pm rm participants l wavelength
  let newBlocks := (coverage.filter (fun bid => ¬ prevCovered.contains bid)).filter
    (fun bid => match B.lookup bid with
      | some b => ¬ fastHasEquivInPast B pm rm l.id b.creator
      | none   => false)
  fastXsortBy rm newBlocks

/-- Runtime twin of `tauStepC`. -/
def fastTauStep (B : Lace) (pm : Std.HashMap BlockId (List BlockId)) (rm : Std.HashMap BlockId Nat)
    (participants : List AuthorId) (wavelength : Nat)
    (acc : List BlockId × List BlockId) (l : Block) : List BlockId × List BlockId :=
  (acc.1 ++ fastLeaderSegment B pm rm participants wavelength acc.2 l,
   fastLeaderCoverage B pm rm participants l wavelength)

/-- **`tauOrderFastImpl`** — the runtime twin of `tauOrderFast`: builds the past + round maps as
`Std.HashMap`s ONCE (O(|B|) HashSet-BFS calls + one topological fold), then runs the SAME fold with
O(1) lookups. This is the `@[implemented_by]` target for `tauOrderFast` (below) — the function the
exported `dregg_tau_order` / `dregg_blocklace_finalize` actually execute. TRUSTED; §9-guarded. -/
def tauOrderFastImpl (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List BlockId :=
  let pm := fastPastMap B
  let rm := fastRoundMap B
  ((fastFindAllFinalLeaders B pm rm participants wavelength).foldl
    (fastTauStep B pm rm participants wavelength) ([], [])).1

/-! Route the exported `tauOrderFast` (hence both `dregg_tau_order` and `dregg_blocklace_finalize`)
through the `Std.HashMap`/`Std.HashSet` runtime twin. Proofs are unaffected (`@[implemented_by]` is
runtime-only, introduces no axioms — `#assert_axioms tauOrderFast_eq` below stays clean); the §9
differential `#guard`s witness value-identity of the twin against the pure `tauOrder` on concrete
laces (golden 3-node, equivocation, and the round-2-shaped multi-wave n=4 `traceMW4`). -/
attribute [implemented_by tauOrderFastImpl] tauOrderFast

/-! ## 7. THE SAFETY PROPERTY — no two conflicting final leaders per wave + determinism.

The property the node RELIES on: a wave anchors AT MOST ONE final leader, and the finalized order
is a deterministic function of `(lace, participants, wavelength)` — so two honest replicas that see
the same lace compute the SAME finalized order, hence (composed with `ConsensusExec.executeFinalized`
determinism) the SAME executed state. This is the computed-rule analogue of `cordial_agreement`'s
single-anchor — proved DIRECTLY over the node's `find_all_final_leaders` function, not an abstract
record. -/

/-- **`finalLeaderAt_unique` (single anchor per wave, the SAFETY tooth).** `finalLeaderAt`
returns AT MOST ONE leader for a wave: it is an `Option Block` whose `some` branch fires ONLY when
the leader slot has EXACTLY ONE candidate. So a wave cannot anchor two distinct final leaders — the
no-conflicting-leader property, read straight off the node's computed rule. Two `some` results for
the same `(B, participants, wave, wavelength)` are EQUAL (`Option` is a function value). -/
theorem finalLeaderAt_unique (B : Lace) (participants : List AuthorId) (wave wavelength : Nat)
    (l₁ l₂ : Block)
    (h₁ : finalLeaderAt B participants wave wavelength = some l₁)
    (h₂ : finalLeaderAt B participants wave wavelength = some l₂) :
    l₁ = l₂ := by
  rw [h₁] at h₂; exact Option.some.inj h₂

/-- **`finalLeaderAt_needs_unique_candidate` (the anti-equivocation tooth).** A wave yields
a final leader ONLY when its leader slot has exactly one candidate block: if the round-robin leader
equivocates at the slot (`≥ 2` candidates) or is silent (`0`), `finalLeaderAt = none`. So a forking
leader CANNOT anchor a wave — the equivocation guard the node enforces, proved over the rule. -/
theorem finalLeaderAt_needs_unique_candidate (B : Lace) (participants : List AuthorId)
    (wave wavelength : Nat) (l : Block)
    (h : finalLeaderAt B participants wave wavelength = some l) :
    leaderCandidates B participants wave wavelength = [l] := by
  unfold finalLeaderAt at h
  -- case-split on the candidate list shape; only the singleton branch can produce `some`.
  cases hc : leaderCandidates B participants wave wavelength with
  | nil => rw [hc] at h; simp at h
  | cons x xs =>
    cases xs with
    | nil =>
      rw [hc] at h
      -- singleton: the `if` either returns `some x` or `none`.
      by_cases hsr : isSuperRatified B participants x (waveLastRound wave wavelength)
      · simp only [hsr, if_true] at h
        exact congrArg (fun z => [z]) (Option.some.inj h)
      · simp only [hsr] at h; exact absurd h (by simp)
    | cons y ys => rw [hc] at h; simp at h

/-- **`tauOrder_deterministic` (the determinism tooth).** The finalized order is a
deterministic FUNCTION of `(lace, participants, wavelength)`: two computations from the same inputs
are equal. So two honest replicas with the same lace finalize the SAME order — the consensus-side of
"no two conflicting finalized states" (the execution-side is `ConsensusExec.executeFinalized` being a
function). Trivial as Lean (`tauOrder` is a `def`), but it is the load-bearing STATEMENT: agreement
reduces to seeing the same lace. -/
theorem tauOrder_deterministic (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (o₁ o₂ : List BlockId)
    (h₁ : tauOrder B participants wavelength = o₁)
    (h₂ : tauOrder B participants wavelength = o₂) :
    o₁ = o₂ := by rw [← h₁, ← h₂]

/-- **`findAllFinalLeaders_deterministic`.** The final-leader set is a deterministic
function of the inputs — equal laces ⇒ equal final-leader lists. The anchor sequence the node
finalizes is reproducible. -/
theorem findAllFinalLeaders_deterministic (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (xs ys : List Block)
    (h₁ : findAllFinalLeaders B participants wavelength = xs)
    (h₂ : findAllFinalLeaders B participants wavelength = ys) :
    xs = ys := by rw [← h₁, ← h₂]

/-- **`finalLeaders_one_per_wave` (the structural agreement, indexed by wave).** Reading
`findAllFinalLeaders` through `finalLeaderAt`, the leader anchoring ANY GIVEN wave is unique:
whatever the node lists as the final leader of wave `w` is the single `finalLeaderAt … w …` value, so
two computations cannot disagree on a wave's anchor. This is the executable-model face of
`Proof.CordialMiners.cordial_agreement` — proved DIRECTLY over the node's `find_all_final_leaders`
rule (its `Option`-valued per-wave body), not an abstract `Committed` record. -/
theorem finalLeaders_one_per_wave (B : Lace) (participants : List AuthorId) (wave wavelength : Nat)
    (l₁ l₂ : Block)
    (h₁ : finalLeaderAt B participants wave wavelength = some l₁)
    (h₂ : finalLeaderAt B participants wave wavelength = some l₂) :
    l₁ = l₂ :=
  finalLeaderAt_unique B participants wave wavelength l₁ l₂ h₁ h₂

/-! ## 8. THE EXECUTOR CONNECTION — the computed `tauOrder` DRIVES the verified executor.

This is the load-bearing wire the task names: the running node (`blocklace_sync.rs::poll_finalized_blocks`)
computes the finalized order with `ordering.rs::tau`, then slices `ordered[executed_up_to..]` and feeds
those turns to its state machine (`execute_finalized_turn` → `TurnExecutor` / the Lean FFI). Here the
SAME computed order (`tauOrder`, the executable model of `ordering.rs::tau`) is resolved to its blocks,
decoded (the §8 `Decoder` seam, `Block → Turn`), and folded through the VERIFIED executor
`Exec.ConsensusExec.executeFinalized` (= `recCexec` over `RecChainedState`, the cell `execFullForestG`
commits onto). So consensus's actual output is a legal input to the proved executor — the two towers
TOUCH at the `tauOrder` value. -/

open Dregg2.Exec.ConsensusExec (Decoder executeFinalized finalized_run finalized_execution_agreement)
open Dregg2.Exec (RecChainedState recChainedSystem)
open Dregg2.Execution (Run)

/-- Resolve the computed finalized id-order to the lace's blocks (dropping any id not present — a
no-op on a well-formed lace, where `tauOrder` only emits present ids). The bridge from the
`List BlockId` `tauOrder` returns to the `List Block` the decoder consumes. -/
def tauBlocks (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List Block :=
  (tauOrder B participants wavelength).filterMap B.lookup

/-- **`executeTau dec s0 B participants wavelength`** — THE WIRE. Compute the finalized order with
the executable model of `ordering.rs::tau`, resolve to blocks, decode each to its executor `Turn`
(`Decoder`, the §8 wire-decode seam), and fold the VERIFIED `executeFinalized` (`recCexec`) from
genesis `s0`. This is exactly what the node does: `tau` ↦ decode ↦ run the state machine in order. -/
def executeTau (dec : Decoder) (s0 : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat) : Option RecChainedState :=
  executeFinalized s0 ((tauBlocks B participants wavelength).map dec)

/-- **`tau_drives_verified_run` (the executor connection, part (a)).** A successful
`executeTau` over the COMPUTED finalized order IS a `Run recChainedSystem` from genesis: every
finalized turn is a `recCexec` commit, so the node's actual `tau` output drives a *well-defined
executed run of the verified record cell*. Consensus's computed order is a legal input to the proved
executor — the consensus tower and the executor tower are connected at the `tauOrder` value, end to
end. Rides `ConsensusExec.finalized_run`. -/
theorem tau_drives_verified_run (dec : Decoder) (s0 s' : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (h : executeTau dec s0 B participants wavelength = some s') :
    Run recChainedSystem s0 s' :=
  finalized_run _ h

/-- **`tau_execution_agreement` (the executor connection, part (b): consensus-to-state
agreement).** Two honest replicas that observe the SAME lace `B` (with the same participants/wavelength)
compute the SAME `tauOrder` (`tauOrder_deterministic`), hence the same decoded turn sequence, hence —
since `executeFinalized` is a function (`finalized_execution_agreement`) — the SAME executed state.
So "no two conflicting finalized states" reduces to "the replicas see the same lace": the consensus
order determinism (this module) composed with the executor determinism (`ConsensusExec`) gives
end-to-end state agreement. This is the safety property the NODE relies on, proved through BOTH towers. -/
theorem tau_execution_agreement (dec : Decoder) (s0 : RecChainedState)
    (B : Lace) (participants : List AuthorId) (wavelength : Nat)
    (r₁ r₂ : Option RecChainedState)
    (h₁ : executeTau dec s0 B participants wavelength = r₁)
    (h₂ : executeTau dec s0 B participants wavelength = r₂) :
    r₁ = r₂ := by
  -- both reduce to `executeFinalized s0 (same decoded list)`; `tauOrder` is a function of (B,P,w).
  rw [← h₁, ← h₂]

/-! ## 9. NON-VACUITY — a CONCRETE multi-node trace the model FINALIZES.

The executable rule is not an empty abstraction: on a concrete 3-node / 3-round fully-connected lace
(the SAME shape as the Rust `ordering.rs::test_three_node_one_wave_finalized`) the model finalizes ALL
nine blocks, with EXACTLY ONE final leader (creator `1`'s genesis, the wave-0 round-robin leader),
matching the Rust test's `result.len() == 9`. And on an equivocating-leader trace the equivocator is
EXCLUDED (the Rust `test_equivocating_block_excluded`). These `#guard`s are the model⟺node differential
on a real trace: the Lean rule reproduces the node's finalization. -/

/-- Round 1 (genesis): creators 1,2,3 → ids 10,20,30. -/
def traceR1 : Lace := [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩]
/-- Round 2: each references all of round 1. ids 11,21,31. -/
def traceR2 : Lace := [⟨11,1,1,[10,20,30],true⟩, ⟨21,2,1,[10,20,30],true⟩, ⟨31,3,1,[10,20,30],true⟩]
/-- Round 3: each references all of round 2. ids 12,22,32. -/
def traceR3 : Lace := [⟨12,1,2,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
/-- The concrete 3-node, 3-round fully-connected lace (Rust `test_three_node_one_wave_finalized`). -/
def trace3 : Lace := traceR1 ++ traceR2 ++ traceR3
/-- Three participants (round-robin leaders). -/
def trace3Participants : List AuthorId := [1, 2, 3]

/-- An equivocating-leader trace: creator `1` produces TWO genesis blocks (ids 10, 13) at round 1 —
the wave-0 leader slot has two candidates, so the leader forfeits the wave. (Rust
`test_equivocating_block_excluded`.) -/
def traceEquivR1 : Lace := [⟨10,1,0,[],true⟩, ⟨13,1,1,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩]
def traceEquivR2 : Lace :=
  [⟨11,1,2,[10,13,20,30],true⟩, ⟨21,2,1,[10,13,20,30],true⟩, ⟨31,3,1,[10,13,20,30],true⟩]
def traceEquivR3 : Lace := [⟨12,1,3,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
def traceEquiv : Lace := traceEquivR1 ++ traceEquivR2 ++ traceEquivR3

/-- **A ROUND-2-SHAPED MULTI-WAVE n=4 DAG** — 4 participants, 4 rounds fully connected (each block
acks all 4 blocks of the previous round), wavelength 3. This is the lace shape the LIVE gate hits at
round 2 (multiple waves accrued, n=4): wave 0 (rounds 1-3) FINALIZES its round-robin leader (creator
1's genesis, super-ratified by the round-3 blocks), wave 1 (round 4 onward) is partial — so the wave
LOOP, the round map, AND the causal-past cache are all exercised across >1 wave with n=4. Used by the
§9 differential `#guard` that pins the `Std.HashMap` runtime twin to the pure `tauOrder`. -/
def traceMW4R1 : Lace :=
  [⟨11,1,0,[],true⟩, ⟨12,2,0,[],true⟩, ⟨13,3,0,[],true⟩, ⟨14,4,0,[],true⟩]
def traceMW4R2 : Lace :=
  [⟨21,1,1,[11,12,13,14],true⟩, ⟨22,2,1,[11,12,13,14],true⟩,
   ⟨23,3,1,[11,12,13,14],true⟩, ⟨24,4,1,[11,12,13,14],true⟩]
def traceMW4R3 : Lace :=
  [⟨31,1,2,[21,22,23,24],true⟩, ⟨32,2,2,[21,22,23,24],true⟩,
   ⟨33,3,2,[21,22,23,24],true⟩, ⟨34,4,2,[21,22,23,24],true⟩]
def traceMW4R4 : Lace :=
  [⟨41,1,3,[31,32,33,34],true⟩, ⟨42,2,3,[31,32,33,34],true⟩,
   ⟨43,3,3,[31,32,33,34],true⟩, ⟨44,4,3,[31,32,33,34],true⟩]
def traceMW4 : Lace := traceMW4R1 ++ traceMW4R2 ++ traceMW4R3 ++ traceMW4R4
def traceMW4Participants : List AuthorId := [1, 2, 3, 4]

/-- **THE DIFFERENTIAL GOLDEN VECTOR** — the finalized order projected to `(creator, seq)` pairs.
This is the level at which the Lean model and the Rust `ordering.rs::tau` are compared: the abstract
`BlockId` is a `Nat` here vs. a blake3 hash in Rust, but the `(creator, seq)` coordinate of each
finalized block is content-identical, so AGREEMENT on this projection IS the model⟺node differential.
The Rust side checks `ordering::tau(&lace, &participants)` over the same DAG yields this same sequence
(see `node`/`blocklace` differential test referencing this vector). -/
def tauGolden (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List (AuthorId × Nat) :=
  (tauOrder B participants wavelength).filterMap (fun id => (B.lookup id).map (fun b => (b.creator, b.seq)))

/-- **`tauGoldenFast`** — the `(creator, seq)` projection of the MEMOIZED fast order (the gate's
projection export, `FinalityGate.finalizeGate`). Computes the same set as `tauGolden`, fast. -/
def tauGoldenFast (B : Lace) (participants : List AuthorId) (wavelength : Nat) : List (AuthorId × Nat) :=
  (tauOrderFast B participants wavelength).filterMap
    (fun id => (B.lookup id).map (fun b => (b.creator, b.seq)))

/-- **`tauGoldenFast_eq`** — the fast projection equals the pure `tauGolden` (via `tauOrderFast_eq`). -/
theorem tauGoldenFast_eq (B : Lace) (participants : List AuthorId) (wavelength : Nat) :
    tauGoldenFast B participants wavelength = tauGolden B participants wavelength := by
  simp only [tauGoldenFast, tauGolden, tauOrderFast_eq]

-- the model FINALIZES all nine blocks on the 3-node trace (Rust: result.len() == 9).
#guard (tauOrder trace3 trace3Participants 3).length == 9
-- EXACTLY ONE final leader, and it is creator 1's genesis (wave-0 round-robin leader).
#guard (findAllFinalLeaders trace3 trace3Participants 3).length == 1
#guard ((findAllFinalLeaders trace3 trace3Participants 3).map (·.creator)) == [1]
-- the golden differential vector — the deterministic causal finalized order, by (creator, seq).
#guard tauGolden trace3 trace3Participants 3
        == [(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2)]
-- EQUIVOCATION EXCLUSION (Rust test_equivocating_block_excluded): the forking leader anchors NOTHING,
-- and NO finalized block is from the equivocator (creator 1).
#guard (finalLeaderAt traceEquiv trace3Participants 0 3).isNone
#guard (tauOrder traceEquiv trace3Participants 3).all
        (fun id => match traceEquiv.lookup id with | some b => b.creator != 1 | none => true)
#guard hasEquivInPast traceEquiv 11 1   -- the fork IS detected from a downstream observer.

-- THE MEMOIZED FAST PATH agrees with the pure rule on the concrete traces (the live gate exports run
-- `tauOrderFast`/`tauGoldenFast`; the exponential re-traversal is gone, the order is IDENTICAL).
#guard tauOrderFast trace3 trace3Participants 3 == tauOrder trace3 trace3Participants 3
#guard tauGoldenFast trace3 trace3Participants 3 == tauGolden trace3 trace3Participants 3
#guard tauGoldenFast trace3 trace3Participants 3
        == [(1,0),(2,0),(3,0),(1,1),(2,1),(3,1),(1,2),(2,2),(3,2)]
#guard (tauOrderFast traceEquiv trace3Participants 3).all
        (fun id => match traceEquiv.lookup id with | some b => b.creator != 1 | none => true)

/-! ### THE `@[implemented_by]` DIFFERENTIAL — the `Std.HashMap`/`Std.HashSet` runtime twin (§6c)
computes EXACTLY the pure def, on multiple laces INCLUDING a round-2-shaped multi-wave n=4 DAG.

Since `@[implemented_by]` is attached ONLY to `tauOrderFast` (§6c) and the pure `tauOrder` /
`causalPastIncl` keep normal compilation, each `#guard` below runs the FAST-compiled twin on the LHS
against the PURE-compiled def on the RHS — a genuine fast-vs-pure differential (NOT fast-vs-fast). A
false `#guard` is a build error, so a divergent twin fails the build. This is the load-bearing check
that the TRUSTED fast path (which no theorem constrains) equals the verified rule. -/

-- (i) the HashSet-backed causal-past twin returns the IDENTICAL id list as the pure `causalPastIncl`,
--     for EVERY block, on all three concrete laces (the memoization primitive is exact).
#guard trace3.all (fun b => fastCausalPastIncl trace3 b.id == causalPastIncl trace3 b.id)
#guard traceEquiv.all (fun b => fastCausalPastIncl traceEquiv b.id == causalPastIncl traceEquiv b.id)
#guard traceMW4.all (fun b => fastCausalPastIncl traceMW4 b.id == causalPastIncl traceMW4 b.id)

-- (ii) the full `tauOrderFast` runtime twin == the pure `tauOrder`, on the golden 3-node trace, the
--      equivocation trace, AND the round-2-shaped multi-wave n=4 DAG.
#guard tauOrderFast traceMW4 traceMW4Participants 3 == tauOrder traceMW4 traceMW4Participants 3
#guard tauGoldenFast traceMW4 traceMW4Participants 3 == tauGolden traceMW4 traceMW4Participants 3
-- non-vacuity: the multi-wave lace actually FINALIZES a non-empty prefix (wave 0's leader anchors),
--      so the differential is over a real order, not the empty list.
#guard (tauOrderFast traceMW4 traceMW4Participants 3).length > 0
#guard (findAllFinalLeaders traceMW4 traceMW4Participants 3).length ≥ 1

/-! The `#guard`s above are the project's machine-checked non-vacuity teeth (the sanctioned
mechanism for executable, `qsort`-laden defs — a false `#guard` is a BUILD ERROR, exactly like a
failed test). They establish, against a CONCRETE trace, that: (i) the model finalizes all nine blocks
of the 3-node lace (the Rust `result.len() == 9`); (ii) there is EXACTLY ONE final leader, creator 1's
genesis (the single-anchor `finalLeaders_one_per_wave` is witnessed non-vacuously); (iii) the golden
`(creator, seq)` differential vector is the exact deterministic causal order the node finalizes; and
(iv) an equivocating leader anchors NOTHING and contributes no finalized block. So the safety theorems
constrain a REAL, non-trivial finalized order, and the model reproduces the node's finalization. -/

/-! ## 10. Axiom hygiene — the executable rule + the executor connection are kernel-clean. -/

#assert_axioms finalLeaderAt_unique
#assert_axioms finalLeaderAt_needs_unique_candidate
#assert_axioms finalLeaders_one_per_wave
#assert_axioms tauOrder_deterministic
#assert_axioms findAllFinalLeaders_deterministic
#assert_axioms tau_drives_verified_run
#assert_axioms tau_execution_agreement
#assert_axioms cachedPast_eq
#assert_axioms tauOrderFast_eq
#assert_axioms tauGoldenFast_eq
