/-
# Dregg2.Consensus.TauPrefixMonotone — T5: finalized-prefix monotonicity for `tauOrder`,
# proved WHERE IT IS TRUE and REFUTED where the node assumed it unconditionally.

**The claim (CONSENSUS-FLEX §4 T5).** As the lace grows (new blocks arriving through the
verified `insert`), the finalized order computed by the node's rule
(`blocklace/src/ordering.rs::tau`, modeled executably as
`Distributed.BlocklaceFinality.tauOrder`) only EXTENDS: previously-finalized blocks keep
their positions — no rollback, no reorder of the finalized region. The live node RELIES on
this: `node/src/blocklace_sync.rs::poll_finalized_blocks` keeps a bare INDEX
(`executed_up_to`), slices `ordered[executed_up_to..]` each poll, and advances the index —
sound iff the already-executed prefix of `ordered` is bit-identical across polls.

**THE FINDING — the unconditional claim is FALSE, by an HONEST counterexample.** The
`BlocklaceFinality.lean` header claimed `finalized_prefix_monotone` with no theorem in the
tree; the proof attempt refutes the unconditional statement. A wave's segment is its
leader's COVERAGE (union of causal pasts of the wave-END blocks that ratify it,
`leaderCoverage`) and coverage is NOT closed under lace growth: a wave-end block arriving
LATE and ratifying an ALREADY-FINAL leader grows that wave's coverage, and the new blocks
`xsort` into the MIDDLE of the already-executed region. No Byzantine behavior is needed —
the counterexample below (`lagBase → lagGrown`) is a 4-validator run where validator 4
merely LAGS one wave: its round-2/round-3 blocks (41, 42) pass every check of the verified
`insert` (signed, preds present, seq monotone, no equivocation by ANYONE), yet

  `tauOrder lagBase   = [10,20,30,40,11,21,31,12,22,32]`            (executed_up_to → 10)
  `tauOrder lagGrown  = [10,20,30,40,11,21,31,41,12,22,32,42]`      (41 lands at index 7)

so the old order is NOT a prefix of the new one. **Node implication** (the `#guard`s below
pin it): at the next poll the node slices `ordered[10..] = [32, 42]` — block 32 is
RE-EXECUTED (it was index 9 of the old order) and block 41, a finalized honest turn, falls
BEHIND the cursor and is NEVER EXECUTED (the index only advances; the FinalityGate admits
by `(creator, seq)` MEMBERSHIP, not position, so it does not catch this). The wavelength-3
discipline and honest supermajority do NOT exclude the trace; nothing
`blocklace_sync.rs` checks implies the needed stability. The deployed code does NOT sit
inside the true theorem — that is the soundness finding this module reports.

**What IS true (the corrected T5, proved below).** Prefix monotonicity holds exactly when
the finalized region is STABLE under the growth — `FinalizedRegionStable B B' P wl`:
  (1) `leaders_extend` — the final-leader sequence of `B` is a prefix of that of `B'`
      (no already-anchored wave is forfeited, no earlier skipped wave anchors late); and
  (2) `fold_agrees` — replaying the OLD leaders' segment computation in the GROWN lace
      reproduces the same segments and coverages (no late ratifier grew an old wave's
      coverage; the pointwise sufficient condition is `fold_agrees_of_pointwise`).
Under that hypothesis `tau_finalized_prefix_monotone` gives `tauOrder B P wl <+:
tauOrder B' P wl`, and `tau_executed_prefix_fixed` is the node-shaped corollary: the first
`(tauOrder B).length` entries — the executed region — are bit-identical, which is precisely
what index slicing needs. The hypothesis is NAMED as the node's missing check: a node that
verified `stableCheck` (the executable `Bool` mirror, below) before advancing
`executed_up_to` — or diffed the recomputed prefix against the executed one — would sit
inside the theorem. Today it does not.

**Why the conditional shape (not a synchrony assumption).** The natural primitive
hypothesis "every new block's round exceeds the finalized region's wave-end" implies
`FinalizedRegionStable`, but it is a TIMELINESS assumption the node neither checks nor can
check locally; stating T5 with it would smuggle synchrony in as if deployed code enforced
it. `FinalizedRegionStable` is the exact boundary: it is what the growth must preserve, it
is executable (`stableCheck`), and the counterexample witnesses its failure mode.

Non-vacuity (the sanctioned `#guard` teeth for these `qsort`-laden executable defs —
kernel reduction of `Array.qsort` is impractical and `native_decide` is banned, exactly as
in `BlocklaceFinality` §9):
  * POSITIVE — `trace6` (the 3-node `trace3` grown by a full second wave, rounds 4–6):
    `stableCheck` holds, the order extends 9 → 18, the old order IS a prefix.
  * NEGATIVE — `lagBase → lagGrown`: insert-valid, equivocation-free, yet NOT a prefix;
    `stableCheck` is `false` and the failing field is coverage growth (`leaders_extend`
    still holds — the guards isolate the mechanism).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Consensus.TauPrefixMonotone`.
-/
import Dregg2.Distributed.BlocklaceFinality

namespace Dregg2.Consensus.TauPrefixMonotone

open Dregg2.Authority.Blocklace (Block Lace BlockId AuthorId)
open Dregg2.Distributed.BlocklaceFinality

/-! ## 1. The stability hypothesis — what lace growth must preserve for no-rollback. -/

/-- **`FinalizedRegionStable B B' P wl`** — the finalized region of `B` is undisturbed by
the growth to `B'`:

* `leaders_extend` — `B'`'s final-leader sequence extends `B`'s (no anchored wave is
  forfeited by a late leader-slot equivocation; no earlier skipped wave anchors late and
  splices a segment mid-order);
* `fold_agrees` — replaying the OLD leaders through `B'`'s segment computation
  (`tauStep B'`) reproduces the `B` fold exactly: same emitted segments AND same coverage
  sets (no late wave-end ratifier grew an old wave's coverage);
* `enrollment_agrees` — the growth does not RECLASSIFY an already-ordered block's creator:
  `enrolledId` returns the same verdict in `B` and `B'` for every id the old fold emitted.
  Added with `BlocklaceFinality.enrolledId` (the enrollment filter that closed the
  unenrolled-creator hole). It is a real condition, not bookkeeping: `enrolledId` reads the
  lace (`Lace.lookup`), so a growth that first orders an id the lace does not yet hold and
  LATER supplies it with an unenrolled creator would drop an already-executed entry — a
  rollback, exactly what T5 forbids. On the growths that matter it is free: `Lace.lookup` is
  `List.find?`, so a `B' = B ++ new` extension resolves every id already in `B` to the same
  block, and both §5's `trace6` growth and §4's `lagGrown` satisfy it (`#guard`s below).

This is the exact boundary of T5: `tau_finalized_prefix_monotone` proves it SUFFICIENT,
and `lagBase → lagGrown` (§4) witnesses that dropping `fold_agrees` admits an honest,
insert-valid reorder. The node currently checks NONE of the fields (the finding). -/
structure FinalizedRegionStable (B B' : Lace) (P : List AuthorId) (wl : Nat) : Prop where
  leaders_extend :
    findAllFinalLeaders B P wl <+: findAllFinalLeaders B' P wl
  fold_agrees :
    (findAllFinalLeaders B P wl).foldl (tauStep B' P wl) ([], [])
      = (findAllFinalLeaders B P wl).foldl (tauStep B P wl) ([], [])
  enrollment_agrees :
    ∀ bid ∈ tauOrderUnfiltered B P wl, enrolledId B P bid = enrolledId B' P bid

/-- **`stableCheck`** — the executable `Bool` mirror of `FinalizedRegionStable` (what a
node WOULD evaluate before advancing `executed_up_to` to sit inside the theorem). -/
def stableCheck (B B' : Lace) (P : List AuthorId) (wl : Nat) : Bool :=
  (findAllFinalLeaders B P wl).isPrefixOf (findAllFinalLeaders B' P wl)
  && decide ((findAllFinalLeaders B P wl).foldl (tauStep B' P wl) ([], [])
           = (findAllFinalLeaders B P wl).foldl (tauStep B P wl) ([], []))
  && (tauOrderUnfiltered B P wl).all (fun bid => enrolledId B P bid == enrolledId B' P bid)

/-- The mirror is faithful: a `true` `stableCheck` yields the `Prop`-level hypothesis. -/
theorem FinalizedRegionStable.of_check {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (h : stableCheck B B' P wl = true) : FinalizedRegionStable B B' P wl := by
  unfold stableCheck at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  refine ⟨List.isPrefixOf_iff_prefix.mp h.1.1, of_decide_eq_true h.1.2, ?_⟩
  intro bid hbid
  exact eq_of_beq (List.all_eq_true.mp h.2 bid (by simpa using hbid))

/-- **`fold_agrees_of_pointwise`** — the prose-level sufficient condition for
`fold_agrees`: every already-final leader's SEGMENT function and COVERAGE are unchanged by
the growth (the CONSENSUS-FLEX T5 proof sketch's "coverage of earlier waves is closed",
now an explicit hypothesis rather than a false unconditional). -/
theorem fold_agrees_of_pointwise {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (hseg : ∀ l ∈ findAllFinalLeaders B P wl, ∀ c : List BlockId,
        leaderSegment B' P wl c l = leaderSegment B P wl c l)
    (hcov : ∀ l ∈ findAllFinalLeaders B P wl,
        leaderCoverage B' P l wl = leaderCoverage B P l wl) :
    (findAllFinalLeaders B P wl).foldl (tauStep B' P wl) ([], [])
      = (findAllFinalLeaders B P wl).foldl (tauStep B P wl) ([], []) := by
  suffices h : ∀ (L : List Block),
      (∀ l ∈ L, ∀ c : List BlockId, leaderSegment B' P wl c l = leaderSegment B P wl c l) →
      (∀ l ∈ L, leaderCoverage B' P l wl = leaderCoverage B P l wl) →
      ∀ acc : List BlockId × List BlockId,
        L.foldl (tauStep B' P wl) acc = L.foldl (tauStep B P wl) acc from
    h _ hseg hcov ([], [])
  intro L
  induction L with
  | nil => intro _ _ _; rfl
  | cons l L ih =>
    intro hseg' hcov' acc
    have hstep : tauStep B' P wl acc l = tauStep B P wl acc l := by
      simp [tauStep, hseg' l (List.mem_cons_self ..) acc.2, hcov' l (List.mem_cons_self ..)]
    simp only [List.foldl_cons, hstep]
    exact ih (fun x hx c => hseg' x (List.mem_cons_of_mem _ hx) c)
             (fun x hx => hcov' x (List.mem_cons_of_mem _ hx)) _

/-! ## 2. The fold only APPENDS — the structural half of T5. -/

/-- One `tauStep` extends the accumulated order by the leader's segment (definitional). -/
theorem tauStep_fst (B : Lace) (P : List AuthorId) (wl : Nat)
    (acc : List BlockId × List BlockId) (l : Block) :
    (tauStep B P wl acc l).1 = acc.1 ++ leaderSegment B P wl acc.2 l := rfl

/-- **`foldl_tauStep_fst_extend`** — folding ANY further leader list onto an accumulator
only APPENDS to the ordered component: `ordering.rs::tau`'s loop never edits what it has
already emitted. The reorder risk therefore lives ENTIRELY in the leader list and the
per-leader segments — exactly the two fields of `FinalizedRegionStable`. -/
theorem foldl_tauStep_fst_extend (B : Lace) (P : List AuthorId) (wl : Nat) :
    ∀ (T : List Block) (acc : List BlockId × List BlockId),
      ∃ rest, (T.foldl (tauStep B P wl) acc).1 = acc.1 ++ rest
  | [], acc => ⟨[], by simp⟩
  | l :: T, acc => by
    obtain ⟨r, hr⟩ := foldl_tauStep_fst_extend B P wl T (tauStep B P wl acc l)
    exact ⟨leaderSegment B P wl acc.2 l ++ r, by
      simp only [List.foldl_cons, hr, tauStep_fst, List.append_assoc]⟩

/-! ## 3. T5 — the corrected finalized-prefix monotonicity theorem. -/

/-- **`tau_finalized_prefix_monotone` (T5, corrected).** If the growth `B → B'` leaves the
finalized region stable (`FinalizedRegionStable`), the computed finalized order only
extends: `tauOrder B P wl` is a prefix of `tauOrder B' P wl` — previously-finalized blocks
keep their positions; no rollback, no reorder. This is the property the node's
`executed_up_to` slicing needs, with its true hypothesis made explicit (and, per §4,
NOT dischargeable from what the node currently checks). -/
theorem tau_finalized_prefix_monotone {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (h : FinalizedRegionStable B B' P wl) :
    tauOrder B P wl <+: tauOrder B' P wl := by
  obtain ⟨T, hT⟩ := h.leaders_extend
  obtain ⟨rest, hrest⟩ :=
    foldl_tauStep_fst_extend B' P wl T
      ((findAllFinalLeaders B P wl).foldl (tauStep B' P wl) ([], []))
  -- The UNFILTERED fold only appends (the structural half, unchanged by the enrollment filter).
  have hunf : tauOrderUnfiltered B' P wl = tauOrderUnfiltered B P wl ++ rest := by
    unfold tauOrderUnfiltered
    rw [← hT, List.foldl_append, hrest, h.fold_agrees]
  -- The filter then distributes over the append, and `enrollment_agrees` says the old prefix's
  -- verdicts are unchanged by the growth — so the filtered order extends too.
  refine ⟨rest.filter (enrolledId B' P), ?_⟩
  unfold tauOrder
  rw [hunf, List.filter_append, List.filter_congr h.enrollment_agrees]

/-- **`tau_executed_prefix_fixed`** — the node-shaped corollary: under stability, the
first `(tauOrder B).length` entries of the grown order — the region `executed_up_to`
indexes into — are EXACTLY the old order. Index-based slicing is sound precisely here. -/
theorem tau_executed_prefix_fixed {B B' : Lace} {P : List AuthorId} {wl : Nat}
    (h : FinalizedRegionStable B B' P wl) :
    tauOrder B P wl = (tauOrder B' P wl).take (tauOrder B P wl).length :=
  List.prefix_iff_eq_take.mp (tau_finalized_prefix_monotone h)

/-! ## 4. THE COUNTEREXAMPLE — an honest laggard breaks the unconditional claim.

Four validators `[1,2,3,4]` (supermajority = 3), wavelength 3. Validator 4 publishes its
genesis block 40, then LAGS (a partition, a slow link — pure asynchrony, no fault).
Validators 1–3 proceed: rounds 2 and 3 complete without 4, wave 0's leader (validator 1's
genesis, block 10) is super-ratified by wave-end blocks {12, 22, 32} — three distinct
ratifying creators ≥ 3 — and the run finalizes all 10 blocks. THEN validator 4 catches up:
its round-2 block 41 and round-3 block 42 arrive, both passing every verified-insert check
(signed, preds present, seq strictly monotone 0 < 1 < 2, NO equivocation by anyone). Block
42 sits at wave 0's END round and RATIFIES leader 10, so wave 0's coverage grows by
{41, 42}; `xsortBy` places 41 (round 2) BEFORE the round-3 blocks the node already
executed. The old order is not a prefix of the new one — `stableCheck` fails on
`fold_agrees` while `leaders_extend` still holds (the guards isolate the mechanism). -/

/-- Round 1 (genesis): all four validators. -/
def lagR1 : Lace := [⟨10,1,0,[],true⟩, ⟨20,2,0,[],true⟩, ⟨30,3,0,[],true⟩, ⟨40,4,0,[],true⟩]
/-- Round 2: validators 1–3 only (validator 4 lags). -/
def lagR2 : Lace :=
  [⟨11,1,1,[10,20,30,40],true⟩, ⟨21,2,1,[10,20,30,40],true⟩, ⟨31,3,1,[10,20,30,40],true⟩]
/-- Round 3 (wave-0 end): validators 1–3 ratify leader 10. -/
def lagR3 : Lace := [⟨12,1,2,[11,21,31],true⟩, ⟨22,2,2,[11,21,31],true⟩, ⟨32,3,2,[11,21,31],true⟩]
/-- The lace at the first poll: wave 0 fully finalized WITHOUT validator 4's rounds 2–3. -/
def lagBase : Lace := lagR1 ++ lagR2 ++ lagR3
/-- Validator 4 catches up: an honest round-2 block and a round-3 block ratifying leader 10. -/
def lagLate : Lace := [⟨41,4,1,[10,20,30,40],true⟩, ⟨42,4,2,[11,21,31,41],true⟩]
/-- The grown lace at the next poll. -/
def lagGrown : Lace := lagBase ++ lagLate
/-- The four participants (round-robin leaders; supermajority `4*2/3+1 = 3`). -/
def lagParticipants : List AuthorId := [1, 2, 3, 4]

/-- **`insertValidArrival`** — the arrival order satisfies the verified `insert`'s
feed-integrity discipline (`blocklace/src/lib.rs::insert`): every block signed, all preds
already present, and per-creator `seq` strictly monotone (which also rules out the
`(creator, seq)` equivocation arm). Certifies the counterexample needs NO Byzantine step
and no fail-open path — the verified reception accepts it. -/
def insertValidArrival (arrival : List Block) : Bool := go [] arrival
  where go (acc : Lace) : List Block → Bool
    | [] => true
    | b :: rest =>
        b.signed
        && b.preds.all (fun p => acc.has p)
        && acc.all (fun a => a.creator != b.creator || a.seq < b.seq)
        && go (acc ++ [b]) rest

-- The arrival is honest: verified-insert-valid, and NOBODY ever equivocates (each
-- creator has at most one block per round, lace-wide).
#guard insertValidArrival lagGrown
#guard lagGrown.all (fun a => lagGrown.all (fun b =>
        a.id == b.id || a.creator != b.creator
          || roundOf lagGrown a.id != roundOf lagGrown b.id))
#guard superMajority lagParticipants.length == 3
-- The growth is a plain superset extension (lagGrown = lagBase ++ lagLate).
#guard lagBase.all (fun b => lagGrown.contains b)

-- THE REFUTATION: both laces finalize wave 0 (leader = validator 1's genesis), yet the
-- old finalized order is NOT a prefix of the new one — 41 lands at index 7, INSIDE the
-- already-executed region.
#guard tauOrder lagBase lagParticipants 3 == [10,20,30,40,11,21,31,12,22,32]
#guard tauOrder lagGrown lagParticipants 3 == [10,20,30,40,11,21,31,41,12,22,32,42]
#guard !(tauOrder lagBase lagParticipants 3).isPrefixOf (tauOrder lagGrown lagParticipants 3)
-- The failing stability field is the SEGMENT/COVERAGE one: the leader list still extends
-- (same single wave-0 anchor), so `leaders_extend` holds and `stableCheck` fails on
-- `fold_agrees` — wave 0's coverage grew by the late ratifier's causal past.
#guard (findAllFinalLeaders lagBase lagParticipants 3).isPrefixOf
        (findAllFinalLeaders lagGrown lagParticipants 3)
#guard !stableCheck lagBase lagGrown lagParticipants 3
#guard leaderCoverage lagGrown lagParticipants ⟨10,1,0,[],true⟩ 3
        != leaderCoverage lagBase lagParticipants ⟨10,1,0,[],true⟩ 3

-- NODE IMPLICATION (`blocklace_sync.rs::poll_finalized_blocks` index slicing): after the
-- first poll `executed_up_to = 10`. At the next poll the slice `ordered[10..]` is
-- `[32, 42]`: block 32 — already executed at index 9 — would be RE-EXECUTED, and block 41
-- — validator 4's finalized honest turn — falls BEHIND the cursor and is NEVER executed.
#guard (tauOrder lagGrown lagParticipants 3).drop 10 == [32, 42]
#guard (tauOrder lagBase lagParticipants 3).contains 32          -- 32 already executed…
#guard ((tauOrder lagGrown lagParticipants 3).drop 10).contains 32  -- …and re-served.
#guard !(tauOrder lagBase lagParticipants 3).contains 41         -- 41 never executed…
#guard !((tauOrder lagGrown lagParticipants 3).drop 10).contains 41 -- …and never will be.

/-! ## 5. NON-VACUITY (positive) — a real growth that IS stable, verified end to end.

`trace3` (the 3-node, 3-round lace of `BlocklaceFinality` §9, wave 0 finalized) grows by a
FULL second wave (rounds 4–6, fully connected): wave 1's round-robin leader (validator 2's
round-4 block 23) is super-ratified at round 6, its segment — the nine new blocks — is
APPENDED, and nothing touches wave 0's coverage (the late blocks all sit at rounds > 3).
`stableCheck` holds, so by `FinalizedRegionStable.of_check` +
`tau_finalized_prefix_monotone` the 9-block order is a prefix of the 18-block order — and
the `#guard`s witness it executably. The hypothesis is satisfiable by real growth and the
theorem's conclusion is non-trivial: T5 is not vacuous. -/

/-- Round 4 (wave 1 start): fully connected to round 3. -/
def trace6R4 : Lace := [⟨13,1,3,[12,22,32],true⟩, ⟨23,2,3,[12,22,32],true⟩, ⟨33,3,3,[12,22,32],true⟩]
/-- Round 5. -/
def trace6R5 : Lace := [⟨14,1,4,[13,23,33],true⟩, ⟨24,2,4,[13,23,33],true⟩, ⟨34,3,4,[13,23,33],true⟩]
/-- Round 6 (wave 1 end): ratifies wave 1's leader 23. -/
def trace6R6 : Lace := [⟨15,1,5,[14,24,34],true⟩, ⟨25,2,5,[14,24,34],true⟩, ⟨35,3,5,[14,24,34],true⟩]
/-- `trace3` grown by a complete second wave — the STABLE growth. -/
def trace6 : Lace := trace3 ++ trace6R4 ++ trace6R5 ++ trace6R6

#guard insertValidArrival trace6
#guard stableCheck trace3 trace6 trace3Participants 3
#guard (findAllFinalLeaders trace6 trace3Participants 3).map (·.creator) == [1, 2]
#guard (tauOrder trace6 trace3Participants 3).length == 18
#guard (tauOrder trace3 trace3Participants 3).isPrefixOf (tauOrder trace6 trace3Participants 3)
-- the executed region is bit-identical under the stable growth (the take-corollary, executably).
#guard (tauOrder trace6 trace3Participants 3).take 9 == tauOrder trace3 trace3Participants 3

/-! The `#guard`s are the sanctioned executable teeth (a false one is a BUILD ERROR;
`Array.qsort` is impractical for kernel reduction and `native_decide` is banned — same
regime as `BlocklaceFinality` §9). Together: the POSITIVE instance shows a real,
insert-valid growth satisfying `FinalizedRegionStable` with a strictly longer order
(hypothesis satisfiable, conclusion non-trivial); the NEGATIVE instance shows an
insert-valid, equivocation-free growth where the conclusion FAILS — so the hypothesis is
load-bearing and the unconditional T5 the node assumed is REFUTED, with the failing field
isolated (`fold_agrees`, coverage growth) and the node-side damage pinned (block 41
skipped forever, block 32 re-served). -/

/-! ## 6. Axiom hygiene. -/

#assert_axioms FinalizedRegionStable.of_check
#assert_axioms fold_agrees_of_pointwise
#assert_axioms foldl_tauStep_fst_extend
#assert_axioms tau_finalized_prefix_monotone
#assert_axioms tau_executed_prefix_fixed

end Dregg2.Consensus.TauPrefixMonotone
