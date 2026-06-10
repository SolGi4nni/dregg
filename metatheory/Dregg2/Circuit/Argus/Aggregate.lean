/-
# Dregg2.Circuit.Argus.Aggregate — WELDING the Argus IR to the STRAND / LIGHT-CLIENT layer.

**What this module is.** `Argus/{Stmt,Compile,Turn}.lean` built the Argus IR: a reified `RecStmt`
whose `interp` IS the verified executor (`interp_transferStmt_eq_recKExec` — the cornerstone) and
whose `compile` IS the circuit, with the turn wrapper `runTurn` producing the three-way `TurnOutcome`.
Separately, `Distributed/HistoryAggregation.lean` + `Circuit/RecursiveAggregation.lean` built the
STRAND / LIGHT-CLIENT layer: a history is a `List ChainStep` (each carrying an executor witness
`recCexec pre turn = some post`), and a light client that checks ONE succinct aggregate
learns the WHOLE chain executed correctly, is correctly ordered, and folds to the genuine final root
(`light_client_verifies_whole_history`), with an apex anti-ghost (tamper any seam ⇒ reject).

These were two disjoint towers. **This module is the wire between them.** The strand the light client
talks about is a sequence of ARGUS turn receipts: each `ChainStep` is produced by running an Argus IR
term's effect body, and the executor witness the aggregation layer demands is discharged BY THE ARGUS
CORNERSTONE — not re-derived. The new content here is the CONNECTION (the Argus-produced state/turn IS
what the layer talks about), reusing the layer's soundness theorems verbatim.

## The honest bridge — at the EXECUTOR-BODY level (`interpChained`), routed through the cornerstone

The aggregation layer's `ChainStep.commits` is `recCexec s.pre s.turn = some s.post` — the BARE chained
executor (`recKExec` effect body + a receipt-log append). The Argus IR's executor interpretation of the
transfer term, lifted to chained state, is `interpChained (transferStmt turn)`, which by the cornerstone
`interpChained_transferStmt` equals `recKExec` on the kernel. So:

  * `argus_body_is_recCexec` — **THE CONNECTION LEMMA.** When the Argus transfer BODY commits
    (`interpChained (transferStmt turn) s = some sBody`), the genuine bare-executor step is
    `recCexec s turn = some { sBody with log := turn :: s.log }`. The Argus cornerstone IS the executor
    witness the strand needs; the only reconciliation is the receipt-log append (`recCexec` appends the
    turn to the log; the Argus body leaves the log frozen — the body is not what records the receipt).

  * `argusChainStep` — from an Argus transfer effect commit, BUILD the aggregation `ChainStep` whose
    `commits` is discharged by `argus_body_is_recCexec`. This is the unit of an Argus strand.

  * `argusStrand` / `argus_strand_stateChained` — a sequence of Argus transfer turns folds into a
    `List ChainStep` that is `StateChained` from genesis (a contiguous executor run).

  * `argus_strand_light_client` — **THE APEX.** Threaded into `light_client_verifies_whole_history`
    (the layer's headline, REUSED), a light client that checks ONLY the succinct aggregate over the
    Argus-produced strand learns: EVERY Argus turn executed correctly per the verified executor, the
    strand is correctly ordered, and the public final root is the genuine fold of the whole Argus
    history. Plus `argus_strand_conserves` (value conserved over the whole Argus strand) and the apex
    anti-ghost `tampered_argus_strand_rejected` (tamper any guarantee-relevant seam ⇒ the binding is
    impossible ⇒ reject) — both rides of the reused layer keystones.

## SCOPE — the two NAMED, UNPAPERED gaps (do not over-read)

1. **The fee/nonce/distribution PROLOGUE-EPILOGUE is OUTSIDE this strand.** The connection is at the
   BODY level (`interpChained`), which IS `recCexec`. The Argus FULL turn `runTurn` additionally
   commits a prologue (fee debit + nonce tick, never rolled back) and an epilogue (fee distribution,
   conservation-MODULO-BURN). That wrapper is `Turn.lean`'s concern (`conservation_modulo_burn_on_-
   commit`), and it is NOT folded into the aggregation's bare-executor `recCexec` model — which
   conserves value EXACTLY (`recKExec_conserves`, no burn). So the strand welded here is the
   body-executor strand (the conserved core), NOT the fee-wrapped turn. The burn-modulo conservation
   of the wrapper composes ALONGSIDE this, it is not subsumed by it. (`argus_full_turn_body_links`
   states precisely how an accepted `runTurn` exposes the body step the strand consumes.)

2. **The shape-AIR vs real-AIR CENSUS GAP remains the named carried hypothesis.** The IVC accumulator
   (`RecursiveAggregation`) names `EngineSound.leaf_sound : verify p = true → recCexec s.pre s.turn =
   some s.post` — the per-turn leaf-proof soundness — as a hypothesis (the plonky3/pickles FRI part
   outside Lean). This module THREADS THE SAME EXECUTOR (`interp`/`recCexec`) the leaf names, so the
   connection is sound AT THE EXECUTOR LEVEL. But whether the recursion engine's folded leaf AIR IS
   the REAL per-effect EffectVM descriptor (transfer's 36-constraint `transferVmDescriptor`,
   `Compile.lean`) or a SHAPE placeholder leaf is the census gap: `leaf_sound` is satisfied by the
   Argus executor here, yet the identity "the folded leaf's AIR = the descriptor `compile` emits" is
   the carried `InnerProofSound` hypothesis, NOT proved in Lean.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); NO `sorry`/`:=True`. The reused
layer hypotheses are `structure` FIELDS, not axioms; non-vacuity witnessed over a real Argus transfer
strand (§5). Verified with `lake build Dregg2.Circuit.Argus.Aggregate`.
-/
import Dregg2.Circuit.Argus.Turn
import Dregg2.Circuit.RecursiveAggregation

namespace Dregg2.Circuit.Argus.Aggregate

open Dregg2.Exec (RecChainedState recCexec recKExec recChainedSystem recTotal)
open Dregg2.Circuit.Argus (RecStmt interp transferStmt interpChained interpChained_transferStmt
  runTurn TurnOutcome)
open Dregg2.Distributed.HistoryAggregation
  (ChainStep StateChained ChainBound Continues lastStateOf foldedFinalRoot stateRoot zeroTurn
   WellFormedChain wellformed_is_run wellformed_history_conserves seam_roots_chain
   root_tooth_pins_state)
open Dregg2.Circuit.RecursiveAggregation
  (Aggregate EngineSound AggregateAttests light_client_verifies_whole_history
   attested_history_is_run attested_history_conserves tampered_aggregate_cannot_bind
   leaf_pairing_defeats_swap)

/-! ## §1 — THE CONNECTION LEMMA: the Argus transfer body IS a `recCexec` step.

The aggregation layer wants `recCexec s turn = some post`. The Argus IR's `interpChained
(transferStmt turn)` is, by the cornerstone `interpChained_transferStmt`, `recKExec` on the kernel,
mapped back to the chained state with the log FROZEN. `recCexec` is exactly `recKExec` on the kernel
WITH the turn appended to the log. So when the Argus body commits, the genuine `recCexec` step is the
Argus body's post-state with the receipt appended — the cornerstone IS the executor witness, modulo
the receipt-log append (which the BODY does not do — the receipt is the chain's record, not the
effect's). -/

/-- The chained post-state of a committed Argus transfer body, with the turn appended to the receipt
log. This is the genuine `recCexec` post-state (see `argus_body_is_recCexec`): the Argus body moves
the kernel; the strand step additionally records the receipt. -/
def argusPost (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState) : RecChainedState :=
  { sBody with log := turn :: s.log }

/-- **`argus_body_is_recCexec` — THE CONNECTION LEMMA.** When the Argus transfer body commits
(`interpChained (transferStmt turn) s = some sBody`), the genuine bare-executor chained step is
`recCexec s turn = some (argusPost turn s sBody)`: the Argus body's kernel transition IS `recKExec`'s
(the cornerstone), and `recCexec` is that with the receipt appended. So the Argus IR cornerstone
DISCHARGES the executor witness `ChainStep.commits` the strand layer demands — it is not re-derived. -/
theorem argus_body_is_recCexec (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hbody : interpChained (transferStmt turn) s = some sBody) :
    recCexec s turn = some (argusPost turn s sBody) := by
  -- the cornerstone (lifted to chained state): the Argus body IS `recKExec` on the kernel, mapped back.
  rw [interpChained_transferStmt] at hbody
  -- decode the `map`: `recKExec s.kernel turn = some k'` with `sBody = { s with kernel := k' }`.
  rw [Option.map_eq_some_iff] at hbody
  obtain ⟨k', hk, hsBody⟩ := hbody
  -- `recCexec` unfolds to the same `recKExec` on the kernel, appending the turn to the log.
  unfold recCexec argusPost
  rw [hk]
  -- both sides are `some` of the same chained record: kernel `k'`, log `turn :: s.log`.
  subst hsBody
  rfl

/-- **`argus_body_commits_iff_recCexec`.** The Argus transfer BODY commits IFF the bare
executor `recCexec` commits — the two agree on WHETHER the transfer happens (both are gated by exactly
`recKExec`'s admissibility), and the strand step `recCexec` is the Argus body plus the receipt append.
So building an Argus strand never silently drops or invents a transfer relative to the executor. -/
theorem argus_body_commits_iff_recCexec (turn : Dregg2.Exec.Turn) (s : RecChainedState) :
    (interpChained (transferStmt turn) s).isSome = (recCexec s turn).isSome := by
  rw [interpChained_transferStmt]
  unfold recCexec
  cases hk : recKExec s.kernel turn <;> simp

/-! ## §2 — `argusChainStep`: an Argus transfer effect commit, as an aggregation strand step.

Given an Argus transfer term whose body commits at `s`, we BUILD the layer's `ChainStep` — its `pre`
is `s`, its `turn` is the Argus turn, its `post` is `argusPost` (the body's post-state + receipt), and
its `commits` field is discharged by `argus_body_is_recCexec`. This is the unit of an Argus strand: a
real verified executor step whose genuineness is the Argus cornerstone. -/

/-- **`argusChainStep` — an Argus transfer effect commit, AS a `ChainStep`.** The strand-layer step
whose executor witness is the Argus IR cornerstone (`argus_body_is_recCexec`). The light-client layer
consumes a `List` of these and cannot tell them from any other `recCexec` chain — which is exactly the
point: the Argus-produced strand IS a genuine verified-executor history. -/
def argusChainStep (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hbody : interpChained (transferStmt turn) s = some sBody) : ChainStep where
  pre     := s
  turn    := turn
  post    := argusPost turn s sBody
  commits := argus_body_is_recCexec turn s sBody hbody

/-- The Argus strand step's `pre`/`turn`/`post` are exactly what we put in (definitional accessors,
so downstream rewrites see through `argusChainStep`). -/
@[simp] theorem argusChainStep_pre (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hbody : interpChained (transferStmt turn) s = some sBody) :
    (argusChainStep turn s sBody hbody).pre = s := rfl
@[simp] theorem argusChainStep_turn (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hbody : interpChained (transferStmt turn) s = some sBody) :
    (argusChainStep turn s sBody hbody).turn = turn := rfl
@[simp] theorem argusChainStep_post (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hbody : interpChained (transferStmt turn) s = some sBody) :
    (argusChainStep turn s sBody hbody).post = argusPost turn s sBody := rfl

/-! ## §3 — `argusStrand`: a sequence of Argus transfer turns, folded into a `List ChainStep`.

A strand is "a seq of Argus receipts". We model the producer directly: fold the Argus transfer
effect-body executor over a list of turns from genesis, building one `argusChainStep` per turn that
commits (fail-closed: a non-committing turn aborts the strand, exactly the executor's discipline). The
resulting `List ChainStep` is what the light client verifies — and it is `StateChained`. -/

/-- **`argusStrand s turns`** — fold the Argus transfer body executor from genesis `s`, building one
strand step per committing turn. `none` if any Argus body fails to commit (fail-closed). Each step's
executor witness is the Argus cornerstone (`argusChainStep`), so the strand is a genuine
verified-executor history produced by the Argus IR. -/
def argusStrand (s : RecChainedState) : List Dregg2.Exec.Turn → Option (List ChainStep)
  | []           => some []
  | turn :: rest =>
    match hbody : interpChained (transferStmt turn) s with
    | some sBody =>
      (argusStrand (argusPost turn s sBody) rest).map
        (fun tail => argusChainStep turn s sBody hbody :: tail)
    | none       => none

/-- **`argus_strand_stateChained`.** Every strand the Argus producer yields is
`StateChained` from genesis: the first step's `pre` is genesis, and each step's `post` is the next
step's `pre` (the fold threads `argusPost` as the next pre-state by construction). So the Argus-produced
strand is a contiguous verified-executor run — the precondition the layer's run/conservation keystones
(`wellformed_is_run`/`…_conserves`) consume. -/
theorem argus_strand_stateChained (s : RecChainedState) (turns : List Dregg2.Exec.Turn)
    (steps : List ChainStep) (h : argusStrand s turns = some steps) :
    StateChained s steps := by
  induction turns generalizing s steps with
  | nil =>
    simp only [argusStrand, Option.some.injEq] at h
    subst h
    -- `StateChained s [] = True`.
    trivial
  | cons turn rest ih =>
    simp only [argusStrand] at h
    -- case on whether the head Argus body commits.
    split at h
    · next sBody hbody =>
      rw [Option.map_eq_some_iff] at h
      obtain ⟨tail, htail, hsteps⟩ := h
      subst hsteps
      -- the head step's `pre` IS `s`; its `post` IS `argusPost`, which is the tail's genesis.
      refine ⟨rfl, ?_⟩
      exact ih (argusPost turn s sBody) tail htail
    · next hbody => exact absurd h (by simp)

/-! ## §4 — THE APEX: the light client verifies the whole Argus history.

Now we feed the Argus-produced strand into the layer's headline. The light client checks ONE succinct
aggregate over the strand and — under the layer's named, realizable engine-soundness hypotheses
(`EngineSound`, REUSED) — learns the whole Argus history executed correctly, is correctly
ordered, and folds to the genuine final root. The strand is the Argus one; the soundness is the layer's. -/

/-- **`argus_strand_light_client` (THE APEX).** A light client that checks ONLY `verify
agg.root = true` over an Argus-produced strand `steps` (re-witnessing NOTHING) obtains
`AggregateAttests`: EVERY Argus turn executed correctly per the verified executor (`recCexec` — the
Argus body, by the cornerstone), the strand is correctly ordered (no reorder/drop/insert), and the
public final root is the genuine fold of the whole Argus history — UNDER the layer's named, realizable
engine-soundness hypotheses (`EngineSound`, REUSED verbatim). The strand the layer's headline talks
about IS the Argus-produced one; this theorem is the wire. The conclusion ALSO carries that the verified
steps are a genuine `Run recChainedSystem` from genesis (consumed from `hstrand` via
`argus_strand_stateChained`), pinning that the attested history is the actual Argus producer's run — not
merely some list satisfying `EngineSound`. -/
theorem argus_strand_light_client
    {Proof : Type} (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState)
    (turns : List Dregg2.Exec.Turn) (steps : List ChainStep)
    (hstrand : argusStrand g turns = some steps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    AggregateAttests Proof CH RH cmb compress compressN agg g steps
      ∧ Dregg2.Execution.Run recChainedSystem g (lastStateOf g steps) :=
  -- the attestation is the layer's headline (REUSED); the run pins that these steps ARE the Argus
  -- producer's genuine contiguous run from genesis (`hstrand` ⇒ `StateChained` ⇒ `wellformed_is_run`).
  ⟨light_client_verifies_whole_history Proof verify CH RH cmb compress compressN agg g steps es hroot,
   wellformed_is_run g steps (argus_strand_stateChained g turns steps hstrand)⟩

/-- **`argus_strand_every_turn_executed`.** Reading the apex's conclusion: every turn of the
Argus-produced strand the light client verified executed per the verified executor
(`recCexec pre turn = some post`). The light client, having checked only the succinct root, learns
that each Argus turn in the history is a real verified-executor step. -/
theorem argus_strand_every_turn_executed
    {Proof : Type} (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState)
    (turns : List Dregg2.Exec.Turn) (steps : List ChainStep)
    (hstrand : argusStrand g turns = some steps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g steps)
    (hroot : verify agg.root = true) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post :=
  (argus_strand_light_client verify CH RH cmb compress compressN agg g turns steps hstrand es hroot).1.every_turn

/-- **`argus_strand_is_run`.** The Argus-produced strand is a genuine `Run recChainedSystem`
from genesis to the folded endpoint — so the light client inherits EVERY run-level theorem of the
verified record cell over the whole Argus history, having re-executed nothing. Rides the layer's
`wellformed_is_run` over the `argus_strand_stateChained` witness. -/
theorem argus_strand_is_run (g : RecChainedState)
    (turns : List Dregg2.Exec.Turn) (steps : List ChainStep)
    (hstrand : argusStrand g turns = some steps) :
    Dregg2.Execution.Run recChainedSystem g (lastStateOf g steps) :=
  wellformed_is_run g steps (argus_strand_stateChained g turns steps hstrand)

/-- **`argus_strand_conserves` (KEYSTONE).** Value is conserved across the WHOLE Argus-produced
strand: the ledger total at the folded endpoint equals the genesis total. A light client trusting the
aggregate over an Argus strand trusts a no-mint/no-burn history of arbitrary length, having re-executed
nothing. Rides the layer's `wellformed_history_conserves` over the Argus strand's `StateChained`
witness. (This is the conserved CORE — the fee/nonce/distribution wrapper's modulo-burn is a SEPARATE
layer, see the honest-scope note; it is not folded into this bare-executor strand.) -/
theorem argus_strand_conserves (g : RecChainedState)
    (turns : List Dregg2.Exec.Turn) (steps : List ChainStep)
    (hstrand : argusStrand g turns = some steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  wellformed_history_conserves g steps (argus_strand_stateChained g turns steps hstrand)

/-! ## §5 — THE APEX ANTI-GHOST: tamper any guarantee-relevant seam of the Argus strand ⇒ reject.

The connection is only meaningful if the aggregate cannot attest a BROKEN Argus history. We surface the
layer's two anti-ghost teeth over the Argus-produced strand:
  (a) a REORDERED Argus strand (a seam where the first step's post-root ≠ the next's pre-root, i.e. a
      spliced/dropped/inserted Argus turn) CANNOT be bound — any engine whose binding leaf verifies is
      contradictory (`tampered_aggregate_cannot_bind`, REUSED).
  (b) the leaf↔step PAIRING binds each Argus turn's proof to ITS OWN step (`leaf_pairing_defeats_swap`,
      REUSED) — a proof of Argus turn `j` cannot satisfy the `i`-th leaf.
Both are the layer's teeth, now over an Argus strand. -/

/-- **`tampered_argus_strand_rejected` (THE APEX ANTI-GHOST).** No sound aggregate can attest a
REORDERED Argus strand. If two adjacent Argus steps `s, s'` have a broken seam (the first's post-root ≠
the second's pre-root — a spliced/reordered/dropped Argus turn), then for ANY engine whose binding leaf
verifies, the binding soundness would force `ChainBound [s, s']`, which is FALSE. Hence the aggregate
REJECTS a tampered Argus history — tampering any guarantee-relevant seam-state field (which
moves the §8 full-state root) breaks the binding. Rides the layer's `tampered_aggregate_cannot_bind`. -/
theorem tampered_argus_strand_rejected
    {Proof : Type} (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (s s' : ChainStep)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g [s, s'])
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s')
    (hverify : verify agg.bindingProof = true) :
    False :=
  tampered_aggregate_cannot_bind Proof verify CH RH cmb compress compressN agg g s s' es hbreak hverify

/-- **`argus_strand_leaf_bound_to_own_turn` (the leg-swap tooth, Argus form).** A verifying leaf
proof in the Argus strand's aggregate attests the transition of ITS OWN positionally-paired Argus step,
not some other Argus turn's. An adversary cannot satisfy the head leaf with a proof of a DIFFERENT Argus
turn while exporting this step's roots. Rides the layer's `leaf_pairing_defeats_swap`. -/
theorem argus_strand_leaf_bound_to_own_turn
    {Proof : Type} (verify : Proof → Bool)
    (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
    (RH : Dregg2.Exec.RecordKernelState → ℤ)
    (cmb compress : ℤ → ℤ → ℤ) (compressN : List ℤ → ℤ)
    (agg : Aggregate Proof) (g : RecChainedState) (p : Proof) (ps : List Proof)
    (s : ChainStep) (ss : List ChainStep)
    (hagg : agg.leafProofs = p :: ps)
    (es : EngineSound Proof verify CH RH cmb compress compressN agg g (s :: ss))
    (hleafverify : verify p = true) :
    recCexec s.pre s.turn = some s.post :=
  leaf_pairing_defeats_swap Proof verify CH RH cmb compress compressN agg g p ps s ss hagg es hleafverify

/-! ## §6 — THE FULL-TURN BOUNDARY (named gap 1, stated precisely).

The strand welded above is the Argus BODY-executor strand (the conserved core). The Argus FULL turn
`runTurn` wraps that body in an admission gate + a committed fee/nonce prologue + a fee-distribution
epilogue. We state EXACTLY how an accepted `runTurn` exposes the body step the strand consumes, so the
boundary between "what this strand covers" (the body = `recCexec`) and "what the wrapper adds" (the
fee/nonce/distribution, a SEPARATE conservation-modulo-burn layer) is a theorem, not a comment. -/

/-- **`argus_full_turn_body_links` (the boundary, stated).** If the Argus FULL turn `runTurn`
is ACCEPTED (`bodyCommitted`), then its body — run on the post-PROLOGUE state `commitPrologue s agent
fee` — committed, and THAT body step is a genuine `recCexec` step the strand consumes
(`argus_body_is_recCexec`). The strand here is built over the body executor; the prologue's fee/nonce
debit and the epilogue's fee distribution are the WRAPPER's concern (`Turn.lean`'s
`conservation_modulo_burn_on_commit`), explicitly NOT folded into the bare-executor `recCexec` strand —
which conserves EXACTLY (no burn). This pins gap 1: the connection is at the body, and the wrapper
composes alongside, not within. -/
theorem argus_full_turn_body_links
    (ctx : Dregg2.Exec.Admission.AdmCtx) (hdr : Dregg2.Exec.Admission.TurnHdr)
    (turn : Dregg2.Exec.Turn) (s sBody : RecChainedState)
    (hadm : Dregg2.Exec.Admission.admissible ctx hdr s = true)
    (hbody : interpChained (transferStmt turn)
                (Dregg2.Exec.Admission.commitPrologue s hdr.agent hdr.fee) = some sBody) :
    -- the accepted full turn is `bodyCommitted (distributeFee … sBody)` …
    runTurn ctx hdr (transferStmt turn) s
        = TurnOutcome.bodyCommitted (Dregg2.Exec.Admission.distributeFee ctx sBody hdr.fee)
    -- … and the body step (over the post-prologue state) IS a genuine `recCexec` step the strand
    --   consumes (the conserved core; the fee distribution is the wrapper's separate modulo-burn layer).
    ∧ recCexec (Dregg2.Exec.Admission.commitPrologue s hdr.agent hdr.fee) turn
        = some (argusPost turn (Dregg2.Exec.Admission.commitPrologue s hdr.agent hdr.fee) sBody) := by
  refine ⟨?_, ?_⟩
  · exact Dregg2.Circuit.Argus.runTurn_body_committed ctx hdr (transferStmt turn) s sBody hadm hbody
  · exact argus_body_is_recCexec turn (Dregg2.Exec.Admission.commitPrologue s hdr.agent hdr.fee) sBody hbody

/-! ## §7 — NON-VACUITY: the connection FIRES on a REAL Argus transfer strand (witnessed both ways).

The apex would be hollow if `argusStrand` never produced a non-empty strand, or if the connection lemma
could not fire. We exhibit a CONCRETE Argus transfer over the teeth genesis: the body commits, the
connection lemma yields a genuine `recCexec` step, the strand is a real `[argusChainStep]`, and it is
`StateChained`. We ALSO witness the negative: an INADMISSIBLE transfer (e.g. amount exceeding balance)
produces NO Argus body, so the strand fails closed — the connection separates a real transfer
from a non-transfer. -/

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn)

/-- The Argus body of the honest teeth transfer COMMITS — `interpChained (transferStmt honestTurn)
teethGenesis` is `some`. So the connection lemma applies to a REAL Argus transfer, not a vacuous
`none`. (Cell `0` transfers `10` to cell `1` over the teeth genesis.) -/
theorem honest_argus_body_commits :
    (interpChained (transferStmt honestTurn) teethGenesis).isSome = true := by decide

/-- The connection lemma FIRES on the honest Argus transfer: the Argus body's committed post-state, with
the receipt appended, IS the genuine bare-executor step `recCexec teethGenesis honestTurn`. So the Argus
IR cornerstone really does discharge the strand's executor witness on a concrete transfer. -/
theorem honest_argus_body_is_recCexec :
    recCexec teethGenesis honestTurn
      = some (argusPost honestTurn teethGenesis
                ((interpChained (transferStmt honestTurn) teethGenesis).get (by decide))) :=
  argus_body_is_recCexec honestTurn teethGenesis _ (Option.some_get _).symm

/-- **`honest_argus_strand_some` (non-vacuity, positive).** The single-turn honest Argus strand
PRODUCES a strand: `argusStrand teethGenesis [honestTurn]` is `some [_]` — a real one-step
Argus history. So the apex/run/conservation theorems apply to a REAL non-empty Argus strand. -/
theorem honest_argus_strand_some :
    (argusStrand teethGenesis [honestTurn]).isSome = true := by decide

/-- **`honest_argus_strand_stateChained` (the produced strand is a real run).** The Argus strand
the producer yields over `[honestTurn]` is `StateChained` from the teeth genesis — a contiguous
verified-executor run. So `argus_strand_is_run`/`…_conserves` apply to a REAL Argus strand. -/
theorem honest_argus_strand_stateChained :
    ∀ steps, argusStrand teethGenesis [honestTurn] = some steps → StateChained teethGenesis steps :=
  fun steps h => argus_strand_stateChained teethGenesis [honestTurn] steps h

/-- The honest Argus strand CONSERVES value over its (folded) endpoint — the body-executor strand's
no-mint/no-burn core, on a concrete Argus transfer (ledger total `100` preserved: cell-0 debit `10` =
cell-1 credit `10`). The conserved core of the connection, witnessed. -/
theorem honest_argus_strand_conserves :
    ∀ steps, argusStrand teethGenesis [honestTurn] = some steps →
      recTotal (lastStateOf teethGenesis steps).kernel = recTotal teethGenesis.kernel :=
  fun steps h => argus_strand_conserves teethGenesis [honestTurn] steps h

/-- A TAMPERED (inadmissible) Argus transfer: cell `0` tries to send `999` (exceeds its balance `100`).
The Argus body does NOT commit — `interpChained (transferStmt …)` is `none`. So the connection
separates a real transfer (commits, becomes a `recCexec` step) from a non-transfer (fails closed, no
step), exactly as the executor's discipline demands. The strand producer then aborts (`none`). -/
def overdraftTurn : Dregg2.Exec.Turn := { actor := 0, src := 0, dst := 1, amt := 999 }

/-- **`overdraft_argus_body_fails` (non-vacuity, negative).** An overdrafting Argus transfer's
body fails closed: `interpChained (transferStmt overdraftTurn) teethGenesis` is `none`. So the Argus body
REJECTS an inadmissible transfer — the connection lemma's hypothesis is a real constraint, and
`argus_body_commits_iff_recCexec` is non-vacuous (the executor agrees: `recCexec` also fails). -/
theorem overdraft_argus_body_fails :
    (interpChained (transferStmt overdraftTurn) teethGenesis).isNone = true := by decide

/-- **`overdraft_argus_strand_none` (the producer fails closed).** The strand producer aborts on
the overdrafting turn: `argusStrand teethGenesis [overdraftTurn]` is `none`. A non-executable Argus turn
cannot enter a strand — fail-closed, exactly `recCexec`'s discipline. -/
theorem overdraft_argus_strand_none :
    argusStrand teethGenesis [overdraftTurn] = none := by decide

/-- **`argus_strand_separates_honest_from_tampered` (the connection HAS TEETH).** The honest
Argus transfer produces a strand (`some`), the overdrafting one does not (`none`): the strand producer
distinguishes an executable Argus transfer from an inadmissible one. So the connection is not
a husk that accepts anything — it tracks the verified executor's accept/reject exactly. -/
theorem argus_strand_separates_honest_from_tampered :
    (argusStrand teethGenesis [honestTurn]).isSome = true
    ∧ argusStrand teethGenesis [overdraftTurn] = none := by
  refine ⟨by decide, by decide⟩

/-! ## §8 — Axiom hygiene: the connection keystones are `{propext, Classical.choice, Quot.sound}`-clean. -/

#assert_axioms argus_body_is_recCexec               -- THE CONNECTION LEMMA
#assert_axioms argus_body_commits_iff_recCexec
#assert_axioms argus_strand_stateChained
#assert_axioms argus_strand_light_client            -- THE APEX
#assert_axioms argus_strand_every_turn_executed
#assert_axioms argus_strand_is_run
#assert_axioms argus_strand_conserves               -- KEYSTONE
#assert_axioms tampered_argus_strand_rejected       -- THE APEX ANTI-GHOST
#assert_axioms argus_strand_leaf_bound_to_own_turn
#assert_axioms argus_full_turn_body_links           -- the boundary (gap 1), stated
#assert_axioms honest_argus_body_is_recCexec
#assert_axioms honest_argus_strand_stateChained
#assert_axioms honest_argus_strand_conserves
#assert_axioms overdraft_argus_strand_none
#assert_axioms argus_strand_separates_honest_from_tampered

end Dregg2.Circuit.Argus.Aggregate
