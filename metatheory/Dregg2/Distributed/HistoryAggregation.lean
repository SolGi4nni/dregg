/-
# Dregg2.Distributed.HistoryAggregation — the FOLD model under the IVC accumulator.

**What this is.** The whole-chain IVC accumulator (`circuit/src/ivc_turn_chain.rs`) folds a
sequence of finalized-turn proofs into ONE recursive proof attesting "all turns `1..K` executed
correctly AND the finalized state root advanced correctly from genesis to final, in that order."
This module is the EXECUTABLE/DECLARATIVE model that fold is supposed to attest — stated over the
VERIFIED executor (`Exec.RecordKernel.recCexec`, the same machine `BlocklaceFinality.executeTau`
drives) and the GENUINE per-turn commitment the deployed chain folds: the ROTATED commit `chainedCommit`
(= `hash_many [d, iroot]`, `trace_rotated.rs`), whose first limb is the injective §8 kernel digest `d =
`Circuit.StateCommit.recStateCommit` (the full-state root the whole-turn triangle pins —
`whole_turn_circuit_pins_intent_fold`) and whose second limb is the receipt-log root `iroot`
(`logRoot`), so the folded commitment BINDS the receipt log — whole-history non-omission is real, not
just the single-step root face (`root_tooth_pins_log`, `logChained_of_verified`).

It is the *meaning* of the chain. `RecursiveAggregation.lean` adds the SNARK recursion layer on top:
it names the inner-proof-soundness + recursive-verifier-soundness hypotheses (the part you cannot
prove in Lean — plonky3/pickles FRI), and shows that, UNDER those named hypotheses, an aggregate
proof's validity is exactly `AggregateAttests` from this file — so a light client that checks only
the succinct aggregate learns the whole history is correct.

**The two binding facts modeled here** (the `TurnChainBindingAir` of `ivc_turn_chain.rs:188`):
  1. **Per-step correctness** — each fold step `(pre, turn, post)` is a GENUINE `recCexec` step
     (its `commits` field), so the step proof, when sound, attests the verified executor actually
     ran that turn.
  2. **The temporal tooth** — `new_root[i] == old_root[i+1]` (`ivc_turn_chain.rs:246`): step `i`'s
     post-root is step `i+1`'s pre-root. Reorder / drop / insert ⇒ the chain breaks (UNSAT).

**The headline (`wellformed_attests_whole_history`):** a `WellFormedChain` from a genesis state
yields — for EVERY turn in the chain — a real `recCexec` step (the turn executed correctly per the
verified executor), the chain is correctly ordered (each post-root = next pre-root), and the whole
chain is a `Run recChainedSystem` from genesis whose final state is the genuine fold of the history,
so `recChained_run_conserves` (no mint/burn over the entire history) applies.

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}).
Verified with `lake build Dregg2.Distributed.HistoryAggregation`.
-/
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.StateCommitReduceRaw
import Dregg2.Exec.ConsensusExec

namespace Dregg2.Distributed.HistoryAggregation

open Dregg2.Exec (RecChainedState recCexec recChainedSystem recChained_run_conserves recTotal)
open Dregg2.Execution (System Run)
open Dregg2.Circuit.StateCommit (recStateCommit recStateCommit_binds recStateCommit_binds_kernel
  compressInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF cellDigest)
open Dregg2.Circuit.CollisionReduce (OrBreak SpongeCollision spongeN_orBreak)
open Dregg2.Circuit.StateCommitReduce (StateBreakP recStateCommit_binds_orBreak
  recStateCommit_binds_kernel_orBreak)

/-- The all-zero turn — `Turn` has no `Inhabited` instance, so we name the canonical default
turn-context used to commit the genesis/empty-chain root. -/
def zeroTurn : Dregg2.Exec.Turn := ⟨0, 0, 0, 0⟩

/-! ## 0. The §8 state-commitment portal (the kernel-digest limb of the rotated per-turn commit).

`recStateCommit k t` is the injective full-state KERNEL commitment from the whole-turn triangle
(`StateCommit.lean:196`) — the FIRST limb (`d`) the deployed rotated per-turn commit `chainedCommit`
absorbs (the prover folds the rotated commit, not this limb alone; see `chainedCommit` below). It is
parametric in the Poseidon portal functions; we carry them as section variables exactly as
`StateCommit`/`WholeTurnTriangle` do, plus the collision-resistance carriers the binding lemmas need
(`compressInjective cmb` for the kernel-digest split, `compressNInjective compressN` for the OUTER
rotated sponge + the receipt-log root — both REALIZABLE Poseidon CR). -/

section Portal

variable (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
variable (RH : Dregg2.Exec.RecordKernelState → ℤ)
variable (cmb : ℤ → ℤ → ℤ)
variable (compress : ℤ → ℤ → ℤ)
variable (compressN : List ℤ → ℤ)

/-- **`stateRoot k t`** — the §8 KERNEL DIGEST `d`: the injective full-state commitment of kernel
`k` under turn-context `t` (`recStateCommit` with the portal fixed). This is the FIRST limb the
deployed rotated commit absorbs (`chainedCommit` below = `hash_many [d, iroot]`, `trace_rotated.rs`),
NOT the whole per-turn commitment any longer — it is blind to the receipt log (that is the point of
the §2 repair: the log is bound by the SECOND limb). It still serves as the empty-chain anchor (a
chain with no steps has no receipts to omit) and as the kernel-faithful core the rotated commit
refines (`recStateCommit_binds_kernel` recovers the whole kernel from this limb). -/
def stateRoot (k : Dregg2.Exec.RecordKernelState) (t : Dregg2.Exec.Turn) : ℤ :=
  recStateCommit CH RH cmb compress compressN k t

/-! ### The receipt-log root + the DEPLOYED ROTATED per-turn commitment (the §2 repair, canonical).

The deployed live chained commit is NOT the kernel-only `recStateCommit` — it is the ROTATED WIDE
commitment `state_commit = hash_many [d, iroot]` (`circuit/src/effect_vm/trace_rotated.rs`, `B_IROOT`;
`turn/src/executor/proof_verify.rs:349` "iroot … absorbed INTO the v9 commitment, which the proof
binds"), where `d = recStateCommit … k t` is the kernel digest and `iroot` is the receipt-index root
over the turn's receipt log. We model it here so the per-turn commitment the IVC chain folds BINDS the
receipt log — making whole-history non-omission REAL, not just the single-step root face.

The receipt-index root is modeled as the CR sponge digest `compressN` of the receipt-felt list
(`logRoot`). This is the faithful in-layer stand-in for the deployed Poseidon2 receipt MMR root: both
are injective Poseidon2 commitments to the SAME receipt-felt list under the ONE CR floor
(`compressNInjective compressN = Poseidon2SpongeCR compressN`). The MMR's succinct-RANGE-opening
structure (`mroot`, `CommitBindsMMR`) lives DOWNSTREAM in `Lightclient/MMR` (which imports this
module); the aggregation model needs only the BINDING (omission-resistance), which the sponge digest
delivers identically. -/

/-- A single receipt felt — the deployed per-turn receipt commitment, modeled as the CR digest of the
turn's four fields `(actor, src, dst, amt)`. Injective in the turn (a receipt commits the whole turn,
`turnReceipt_injective`). -/
def turnReceipt (t : Dregg2.Exec.Turn) : ℤ :=
  compressN [(t.actor : ℤ), (t.src : ℤ), (t.dst : ℤ), t.amt]

/-- The receipt-felt list of an audit log — the append-only receipt index the deployed `iroot` is
built over. `RecChainedState.log : List Turn` mapped to its receipt felts. -/
def logFelts (log : List Dregg2.Exec.Turn) : List ℤ :=
  log.map (turnReceipt compressN)

/-- **`logRoot log`** — the receipt-index root the rotated commit absorbs as its second (`iroot`)
limb: a CR sponge digest of the receipt-felt list. A node cannot drop / reorder / forge a receipt
without moving this root (`logRoot_injective`). The model's faithful stand-in for the deployed
receipt-index MMR root. -/
def logRoot (log : List Dregg2.Exec.Turn) : ℤ :=
  compressN (logFelts compressN log)

/-- **`chainedCommit st t`** — THE DEPLOYED ROTATED per-turn commitment, canonical: the sponge
`hash_many [d, iroot]` over the kernel digest `d = recStateCommit … st.kernel t` and the receipt-log
root `iroot = logRoot … st.log`. It STRICTLY REFINES `recStateCommit`: the kernel digest `d` is the
FIRST absorbed limb (so it still binds the WHOLE kernel via `recStateCommit_binds_kernel` — kernel
guarantees are PRESERVED, not weakened), AND it binds the receipt log via the SECOND limb (so
omission of any receipt at this turn moves the published commit). The roots the IVC chain folds
(`ChainStep.oldRoot/newRoot`) are this commitment. -/
def chainedCommit (st : RecChainedState) (t : Dregg2.Exec.Turn) : ℤ :=
  compressN [recStateCommit CH RH cmb compress compressN st.kernel t, logRoot compressN st.log]

/-! #### Binding of the receipt encoding — REDUCTION FORM (floor-free), then the injective bridges.

⚑ **DRAINED 2026-08-01.** `turnReceipt/logFelts/logRoot_injective` bound `compressNInjective compressN`
— the predicate `HashFloorHonesty.compressNInjective_false_of_finite_range` REFUTES for any
bounded-range sponge, so at deployed BabyBear width every one of them, and every keystone conditioned
on them, was VACUOUSLY true. The `_orBreak` twins below carry the SAME good conclusion or hand back a
CONCRETE `SpongeCollision compressN` — a break of the DEPLOYED sponge at a NAMED pair. No injectivity
hypothesis appears in them; they hold at the real hash.

Both peels here (`turnReceipt`'s 4-felt absorb and `logRoot`'s list absorb) are the SAME `compressN`,
so ONE break event covers the family — there is no second carried primitive to price.

The `_injective` forms are RETAINED below, re-derived THROUGH the twins as standalone bridges
(`SystemRoots`/`ListCommitRegrounded` doctrine): they witness that nothing genuinely proved was given
up, and they are never a hypothesis on a keystone. -/

/-- The strength bridge: the (refuted) universal sponge injectivity kills every concrete collision, so
each `_injective` form below is exactly the `resolve` of its twin. ⚠ A RECOVERY LEMMA, NOT A LICENCE —
its premise is false at deployed width. -/
theorem noSpongeColl_of_inj (hCompressN : compressNInjective compressN) :
    ¬ SpongeCollision compressN := fun ⟨_, _, hne, heq⟩ => hne (hCompressN _ _ heq)

/-- **Twin of `turnReceipt_injective`, floor-free.** A receipt felt commits the whole turn — or the
deployed sponge collides on the two named 4-felt absorbs. -/
theorem turnReceipt_binds_orBreak {t t' : Dregg2.Exec.Turn}
    (h : turnReceipt compressN t = turnReceipt compressN t') :
    OrBreak (SpongeCollision compressN) (t = t') := by
  obtain ⟨a, b, c, d⟩ := t
  obtain ⟨a', b', c', d'⟩ := t'
  unfold turnReceipt at h
  -- original: `hCompressN _ _ h` — the sponge-injectivity appeal, now an `OrBreak` leaf.
  refine OrBreak.imp ?_ (spongeN_orBreak compressN h)
  intro hl
  simp only [List.cons.injEq, and_true, Nat.cast_inj] at hl
  obtain ⟨h1, h2, h3, h4⟩ := hl
  subst h1; subst h2; subst h3; subst h4; rfl

/-- **Twin of `logFelts_injective`, floor-free.** The receipt-felt list determines the audit log — or
the sponge collides. Structural recursion mirrors the original, threading with `bind`/`map₂`. -/
theorem logFelts_binds_orBreak :
    ∀ {L L' : List Dregg2.Exec.Turn}, logFelts compressN L = logFelts compressN L' →
      OrBreak (SpongeCollision compressN) (L = L')
  | [], [], _ => OrBreak.ok rfl
  | [], _ :: _, h => by simp [logFelts] at h
  | _ :: _, [], h => by simp [logFelts] at h
  | x :: xs, y :: ys, h => by
    simp only [logFelts, List.map_cons, List.cons.injEq] at h
    exact OrBreak.map₂ (fun (hx : x = y) (hxs : xs = ys) => by rw [hx, hxs])
      (turnReceipt_binds_orBreak compressN h.1)
      (logFelts_binds_orBreak (L := xs) (L' := ys) h.2)

/-- **⚑ Twin of `logRoot_injective` — THE LOG ROOT BINDS THE WHOLE AUDIT LOG, FLOOR-FREE.** Two audit
logs with equal receipt-index roots are EQUAL, OR the proof names a concrete collision of the deployed
sponge. A node that keeps the published root while suppressing, forging, reordering or truncating a
receipt therefore does not merely "violate an assumption" — it EXHIBITS a `SpongeCollision compressN`.
This is the non-omission keystone at deployed parameters, which `logRoot_injective` never was. -/
theorem logRoot_binds_orBreak {L L' : List Dregg2.Exec.Turn}
    (h : logRoot compressN L = logRoot compressN L') :
    OrBreak (SpongeCollision compressN) (L = L') := by
  unfold logRoot at h
  exact OrBreak.bind (spongeN_orBreak compressN h) (logFelts_binds_orBreak compressN)

/-- `turnReceipt` is injective: a receipt felt commits the whole turn. ⚠ **BRIDGE ONLY** — the
`compressNInjective` premise is FALSE at deployed width; re-derived through `turnReceipt_binds_orBreak`
so "nothing genuinely proved was given up" is itself machine-checked. Never a keystone hypothesis. -/
theorem turnReceipt_injective (hCompressN : compressNInjective compressN)
    {t t' : Dregg2.Exec.Turn} (h : turnReceipt compressN t = turnReceipt compressN t') : t = t' :=
  (turnReceipt_binds_orBreak compressN h).resolve (noSpongeColl_of_inj compressN hCompressN)

/-- `logFelts` is injective. ⚠ **BRIDGE ONLY** (see `turnReceipt_injective`). -/
theorem logFelts_injective (hCompressN : compressNInjective compressN)
    {L L' : List Dregg2.Exec.Turn} (h : logFelts compressN L = logFelts compressN L') : L = L' :=
  (logFelts_binds_orBreak compressN h).resolve (noSpongeColl_of_inj compressN hCompressN)

/-- **`logRoot_injective` — the log root binds the whole audit log.** ⚠ **BRIDGE ONLY.** The
`compressNInjective` premise is FALSE at deployed BabyBear width, so as a deployed claim this was
VACUOUS; `logRoot_binds_orBreak` above is the statement that survives the real sponge. Retained,
re-derived through the twin, so the strength relation is machine-checked. -/
theorem logRoot_injective (hCompressN : compressNInjective compressN)
    {L L' : List Dregg2.Exec.Turn} (h : logRoot compressN L = logRoot compressN L') : L = L' :=
  (logRoot_binds_orBreak compressN h).resolve (noSpongeColl_of_inj compressN hCompressN)

/-! ## 1. One fold step — a finalized turn + the roots it advances.

The Rust `FinalizedTurn` (`ivc_turn_chain.rs:100`) carries a whole-turn proof whose PI exposes
`(OLD_COMMIT, NEW_COMMIT)`. Here a `ChainStep` carries the pre-state chained record, the turn, and
the post-state chained record, together with the EXECUTOR WITNESS `recCexec pre turn = some post` —
so this is a real verified step, not an asserted one. Its roots are the GENUINE `stateRoot` of the
pre/post kernels. -/

/-- A single fold step: a genuine `recCexec` transition `(pre, turn) ↦ post`, plus the receipt logs
the chained state carries. Modeled directly over the verified executor so the step's roots are the
real commitments of states the executor reached — what an honest inner step proof, when
sound, attests. -/
structure ChainStep where
  /-- The pre-state chained record (kernel + receipt log). -/
  pre  : RecChainedState
  /-- The turn applied this step. -/
  turn : Dregg2.Exec.Turn
  /-- The post-state chained record. -/
  post : RecChainedState
  /-- **The executor witness**: `recCexec pre turn = some post`. -/
  commits : recCexec pre turn = some post

/-- The step's pre-state root — the DEPLOYED ROTATED commitment of the pre-state (kernel digest +
receipt-log root). The Rust `old_root`. -/
def ChainStep.oldRoot (s : ChainStep) : ℤ := chainedCommit CH RH cmb compress compressN s.pre s.turn

/-- The step's post-state root — the DEPLOYED ROTATED commitment of the post-state (kernel digest +
receipt-log root). The Rust `new_root`. -/
def ChainStep.newRoot (s : ChainStep) : ℤ := chainedCommit CH RH cmb compress compressN s.post s.turn

/-! ## 2. The temporal tooth — `new_root[i] == old_root[i+1]`.

`TurnChainBindingAir` constraint 1 (`ivc_turn_chain.rs:246`): each step's `new_root` must be the
NEXT step's `old_root`. A reordered/dropped/inserted turn breaks this and is UNSAT. -/

/-- **`Continues s s'`** — the temporal tooth between adjacent steps: `s.newRoot = s'.oldRoot`
(`new_root[i] == old_root[i+1]`). Its failure is the `TurnChainError::ChainBreak` rejection. -/
def Continues (s s' : ChainStep) : Prop :=
  ChainStep.newRoot CH RH cmb compress compressN s = ChainStep.oldRoot CH RH cmb compress compressN s'

/-- **`ChainBound steps`** — every adjacent pair satisfies the temporal tooth. The whole sequence is
the genuine finalized order (no reorder/drop/insert at the root level). -/
def ChainBound : List ChainStep → Prop
  | []            => True
  | [_]           => True
  | s :: s' :: rest => Continues CH RH cmb compress compressN s s' ∧ ChainBound (s' :: rest)

/-! ## 3. State-level continuity + the well-formed chain.

The Rust chain binding is over ROOTS; the executor model adds the underlying STATE continuity (step
`i`'s post-state IS step `i+1`'s pre-state — `RecChainedState` equality), which §5 shows the
root-level tooth recovers under CR. `lastStateOf` is the state the chain reaches from genesis. -/

/-- **`StateChained g steps`** — the steps form a contiguous executor run from genesis `g`: the first
step's pre-state is `g`, and each step's post-state is the next step's pre-state. -/
def StateChained (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: rest => s.pre = g ∧ StateChained s.post rest

/-- **`lastStateOf g steps`** — the state the chain reaches from genesis `g`: genesis if empty,
else the last step's `post`. (Defined structurally so the run keystone can name the endpoint.) -/
def lastStateOf (g : RecChainedState) : List ChainStep → RecChainedState
  | []        => g
  | s :: rest => lastStateOf s.post rest

/-- **`WellFormedChain g steps`** — the steps are a genuine executor chain from genesis `g` AND the
root-level temporal tooth holds. -/
structure WellFormedChain (g : RecChainedState) (steps : List ChainStep) : Prop where
  /-- State-level continuity from genesis (each `recCexec` post is the next pre). -/
  chained : StateChained g steps
  /-- Root-level temporal tooth (the `TurnChainBindingAir` continuity constraint). -/
  bound   : ChainBound CH RH cmb compress compressN steps

/-! ## 4. The genuine final root of the whole history.

The accumulator's final claim is "`final_root` = the genuine fold of the whole history"
(`ivc_turn_chain.rs:18`): the §8 commitment of the kernel reached by folding `recCexec` over all the
turns. `lastStateOf g steps` IS that folded state; its commitment is the genuine final root. -/

/-- **`foldedFinalRoot g steps`** — the genuine final root: the DEPLOYED ROTATED commitment
(`chainedCommit` = kernel digest + receipt-log root) of the folded post-state (`lastStateOf`) under
the last step's turn-context (the `NEW_COMMIT` the accumulator exposes). The empty chain commits the
genesis kernel digest under `default` (the empty-chain anchor: no steps, hence no receipts to bind). -/
def foldedFinalRoot (g : RecChainedState) (steps : List ChainStep) : ℤ :=
  match steps.getLast? with
  | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
  | some s => chainedCommit CH RH cmb compress compressN (lastStateOf g steps) s.turn

/-! ## 5. The CR recovery — the ROOT tooth recovers STATE continuity.

The accumulator's verifier only sees ROOTS, not states. Under collision-resistance of the commitment
(`compressInjective cmb`, via `recStateCommit_binds`), the root-level tooth recovers the underlying
kernel continuity. This is why the LIGHT CLIENT, seeing only roots, learns state
continuity — the §8 root is an injective full-state commitment. -/

/-- **`seam_roots_chain` (the easy direction).** State-level continuity at a seam ENTAILS
the root-level tooth: if `s.post = s'.pre` and the turn-contexts agree at the seam, their roots
chain. So an honest accumulator never asserts the tooth separately — it is free from execution. -/
theorem seam_roots_chain (s s' : ChainStep)
    (hstate : s.post = s'.pre) (hturn : s.turn = s'.turn) :
    ChainStep.newRoot CH RH cmb compress compressN s
      = ChainStep.oldRoot CH RH cmb compress compressN s' := by
  unfold ChainStep.newRoot ChainStep.oldRoot
  rw [hstate, hturn]

/-- **`root_tooth_pins_state` (THE CR RECOVERY).** Under collision-resistance of the
commitment combiner, the ROOT-level tooth pins the underlying full-state COMMITMENT: if two steps
share a turn-context and their seam roots agree, then their cell-digests AND rest-hashes agree
(`cellDigest s.post = cellDigest s'.pre ∧ RH s.post = RH s'.pre`). That is exactly the binding
`recStateCommit_binds` provides — the §8 root is an injective commitment to (live-cell digest, rest
hash), i.e. to the WHOLE kernel (every cell binds via `cellLeafInjective`; the 16 non-cell fields via
`RestHashIffFrame`). So a light client that sees only the matching roots GENUINELY learns the states
chained, up to CR. This is the load-bearing fact that makes "verify the succinct aggregate"
sufficient: the root IS the full-state commitment. -/
theorem root_tooth_pins_state_orBreak (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    OrBreak (StateBreakP CH cmb compress compressN)
      (cellDigest CH compress compressN s.post.kernel s'.turn
          = cellDigest CH compress compressN s'.pre.kernel s'.turn
        ∧ RH s.post.kernel = RH s'.pre.kernel) := by
  unfold ChainStep.newRoot ChainStep.oldRoot chainedCommit at htooth
  rw [hturn] at htooth
  -- original: `hCompressN _ _ htooth` — the OUTER rotated-sponge peel, now an `OrBreak` leaf.
  refine OrBreak.bind (OrBreak.weaken (StateBreakP.ofSponge CH cmb compress compressN)
    (spongeN_orBreak compressN htooth)) ?_
  intro hlimbs
  simp only [List.cons.injEq, and_true] at hlimbs
  -- original: `recStateCommit_binds … hCmb …` — now `StateCommitReduceRaw`'s floor-free twin.
  exact recStateCommit_binds_orBreak CH cmb compress compressN RH
    s.post.kernel s'.pre.kernel s'.turn hlimbs.1

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** `compressInjective cmb` / `compressNInjective compressN`
are REFUTED at deployed BabyBear width, so this statement is VACUOUSLY true there and the light-client
conclusion it announces was never earned. `root_tooth_pins_state_orBreak` above is the surviving form.
Retained, re-derived through the twin, never a keystone hypothesis. -/
theorem root_tooth_pins_state (hCmb : compressInjective cmb)
    (hCompressN : compressNInjective compressN) (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    cellDigest CH compress compressN s.post.kernel s'.turn
        = cellDigest CH compress compressN s'.pre.kernel s'.turn
      ∧ RH s.post.kernel = RH s'.pre.kernel := by
  unfold ChainStep.newRoot ChainStep.oldRoot chainedCommit at htooth
  rw [hturn] at htooth
  -- peel the OUTER rotated sponge (compressN): the kernel-digest limb agrees.
  have hlimbs := hCompressN _ _ htooth
  simp only [List.cons.injEq, and_true] at hlimbs
  exact recStateCommit_binds CH RH cmb compress compressN hCmb
          s.post.kernel s'.pre.kernel s'.turn hlimbs.1

/-- **`root_tooth_pins_kernel` (THE STRENGTHENED CR RECOVERY — state-equality, not just commitment).**
The critique's precise gap: `root_tooth_pins_state` recovers only `cellDigest`+`RH` EQUALITY
(commitment-level), not the `s.post.kernel = s'.pre.kernel` STATE equality `StateChained` needs — so
the headline still took state continuity as a separate prover hypothesis. This closes it: under the
FULL standard Poseidon CR set + the PROVED-preserved `AccountsWF` structural invariant on BOTH seam
kernels, an agreeing root-tooth at a matched turn-context forces the WHOLE kernel equal
(`recStateCommit_binds_kernel`: `RH` recovers the 15 non-cell fields incl. `accounts`, then the cell
digest recovers `cell` over the now-common carrier). So a light client seeing only the matching roots
GENUINELY learns the adjacent KERNELS coincide — up to CR — not merely their commitments. (The
receipt LOG is the one `RecChainedState` component the §8 state root does NOT bind; see
`KernelChained` below — conservation rides on the kernel alone, so the log is conservation-irrelevant,
and that is the exact, named residual rather than a hidden hypothesis.) -/
theorem root_tooth_pins_kernel_orBreak
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH) (s s' : ChainStep)
    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s.post.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s'.pre.kernel)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    OrBreak (StateBreakP CH cmb compress compressN) (s.post.kernel = s'.pre.kernel) := by
  unfold ChainStep.newRoot ChainStep.oldRoot chainedCommit at htooth
  rw [hturn] at htooth
  -- original: `hCompressN _ _ htooth` — the OUTER rotated-sponge peel, now an `OrBreak` leaf.
  refine OrBreak.bind (OrBreak.weaken (StateBreakP.ofSponge CH cmb compress compressN)
    (spongeN_orBreak compressN htooth)) ?_
  intro hlimbs
  simp only [List.cons.injEq, and_true] at hlimbs
  -- original: `recStateCommit_binds_kernel … hCmb hCompress hCompressN hLeaf hRest …` — all four
  -- refuted injectivities gone; only the non-hash `RestHashIffFrameFin` modelling premise remains.
  exact recStateCommit_binds_kernel_orBreak CH cmb compress compressN RH hRest
    s.post.kernel s'.pre.kernel s'.turn hwf hwf' hfin hfin' hlimbs.1

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** All four hash premises are REFUTED at deployed BabyBear
width (`HashFloorHonesty.*_false_of_finite_range`, `StateCommitFloorRegrounded.*_false_babyBear`), so
this — the keystone `KeystoneAuditUnfoolability` registered — was VACUOUSLY true as deployed. The
surviving form is `root_tooth_pins_kernel_orBreak` above: same conclusion, or a CONCRETE collision of
one of the four commitment primitives. Retained, re-derived through the twin. -/
theorem root_tooth_pins_kernel
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH) (s s' : ChainStep)
    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s.post.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s'.pre.kernel)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.kernel = s'.pre.kernel := by
  unfold ChainStep.newRoot ChainStep.oldRoot chainedCommit at htooth
  rw [hturn] at htooth
  -- peel the OUTER rotated sponge (compressN): the kernel-digest limb `d` agrees, then
  -- `recStateCommit_binds_kernel` recovers the WHOLE kernel from it (REUSED unchanged — the rotated
  -- commit absorbs the SAME kernel digest as its first limb, so kernel faithfulness is preserved).
  have hlimbs := hCompressN _ _ htooth
  simp only [List.cons.injEq, and_true] at hlimbs
  exact recStateCommit_binds_kernel CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
          s.post.kernel s'.pre.kernel s'.turn hwf hwf' hfin hfin' hlimbs.1

/-- **`root_tooth_pins_log` (THE NON-OMISSION KEYSTONE — the rotated commit binds the receipt log).**
The §2 repair, now at the aggregation seam: an agreeing root tooth at a matched turn-context forces the
adjacent RECEIPT LOGS equal (`s.post.log = s'.pre.log`), under the one CR floor. The kernel-only
`recStateCommit` was BLIND to the log (`NonOmissionAttack.recStateCommit_admits_receipt_omission`);
the rotated `chainedCommit` absorbs `logRoot … st.log` as its second limb, so the OUTER sponge peel
yields the log-root agreement and `logRoot_injective` recovers the whole audit log. A light client
seeing only the matching published roots GENUINELY learns the receipt logs coincide — no node dropped,
forged, reordered, or truncated a receipt at this turn. This is the component the §8 kernel root did
NOT bind, now bound (the residual named in `NonOmissionAttack` §3, closed). -/
theorem root_tooth_pins_log_orBreak (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    OrBreak (SpongeCollision compressN) (s.post.log = s'.pre.log) := by
  unfold ChainStep.newRoot ChainStep.oldRoot chainedCommit at htooth
  rw [hturn] at htooth
  refine OrBreak.bind (spongeN_orBreak compressN htooth) ?_
  intro hlimbs
  simp only [List.cons.injEq, and_true] at hlimbs
  -- the second limb is the receipt-log root; `logRoot_binds_orBreak` recovers the audit log.
  exact logRoot_binds_orBreak compressN hlimbs.2

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** `compressNInjective compressN` is REFUTED at deployed
width, so "the light client CATCHES a dropped receipt" was, as stated here, a claim about a sponge the
node does not run. `root_tooth_pins_log_orBreak` above is the deployed-true form: the logs agree, or
the adversary EXHIBITS a `SpongeCollision compressN`. Note the break event is the NARROW sponge one —
this leg costs only the sponge, not the full four-way `StateBreakP`. -/
theorem root_tooth_pins_log (hCompressN : compressNInjective compressN) (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.log = s'.pre.log :=
  (root_tooth_pins_log_orBreak CH RH cmb compress compressN s s' hturn htooth).resolve
    (noSpongeColl_of_inj compressN hCompressN)

/-! ## 6. THE HEADLINE — a well-formed chain attests the WHOLE history. -/

/-- **`every_turn_executed_correctly`.** For EVERY turn in the chain, the turn executed
correctly per the verified executor: each `ChainStep.commits` IS the `recCexec` witness, so it holds
by construction. The first headline conjunct, made explicit. -/
theorem every_turn_executed_correctly (steps : List ChainStep) :
    ∀ s ∈ steps, recCexec s.pre s.turn = some s.post :=
  fun s _ => s.commits

/-- **`wellformed_is_run` (the run-level keystone).** A state-chained sequence from genesis
`g` IS a `Run recChainedSystem` from `g` to `lastStateOf g steps`: each step is a
`recChainedSystem.Step` (`⟨turn, commits⟩`), composed along `StateChained`. So ALL of `RecordKernel`'s
run-level theorems apply to the whole history. -/
theorem wellformed_is_run (g : RecChainedState) (steps : List ChainStep)
    (hch : StateChained g steps) :
    Run recChainedSystem g (lastStateOf g steps) := by
  induction steps generalizing g with
  | nil => exact Run.refl (S := recChainedSystem) g
  | cons s rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    subst hpre
    have hstep : recChainedSystem.Step s.pre s.post := ⟨s.turn, s.commits⟩
    simpa [lastStateOf] using Run.step (S := recChainedSystem) hstep (ih s.post hrest)

/-- **`wellformed_history_conserves` (KEYSTONE).** Value is conserved across the WHOLE
folded history: the ledger total at the folded endpoint equals the genesis total. The aggregate
attests a no-mint/no-burn history of arbitrary length. Rides `recChained_run_conserves`
over the run keystone. The light client, trusting only the aggregate, inherits this. -/
theorem wellformed_history_conserves (g : RecChainedState) (steps : List ChainStep)
    (hch : StateChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  recChained_run_conserves (wellformed_is_run g steps hch)

/-! ### Conservation-over-history from KERNEL continuity alone (the §8 root binds the kernel, not the log).

`StateChained` is full `RecChainedState` equality at every seam — it includes the receipt LOG, which
the §8 state commitment does NOT bind (`recStateCommit`/`cellDigest`/`RH` are pure functions of the
kernel; `RecChainedState.log` is uncommitted). A light client verifying roots can therefore recover
KERNEL continuity (`root_tooth_pins_kernel`) but not log continuity. The headline content the critique
demands — conservation-over-history — needs ONLY kernel continuity (`recTotal` reads the kernel), so we
factor it through `KernelChained` and DERIVE it from the verified root teeth, with no `StateChained`
hypothesis. (Full `Run`/`StateChained` — which a few downstream theorems use for run-level facts beyond
conservation — is what additionally needs the log; named, not hidden.) -/

/-- The kernel projection of `recCexec`: a committed chained step commits the underlying kernel step
`recKExec pre.kernel turn = some post.kernel`. Read off the `recCexec` match (the success arm sets
`post.kernel := k'`). -/
theorem recCexec_kernel {s s' : RecChainedState} {t : Dregg2.Exec.Turn}
    (h : recCexec s t = some s') : Dregg2.Exec.recKExec s.kernel t = some s'.kernel := by
  unfold recCexec at h
  split at h
  · next k' heq => simp only [Option.some.injEq] at h; rw [← h]; exact heq
  · exact absurd h (by simp)

/-- **`KernelChained g steps`** — the steps form a contiguous executor run from genesis `g` AT THE
KERNEL LEVEL (the receipt log set aside): the first step's pre-KERNEL is `g`'s, and each step's
post-kernel is the next step's pre-kernel. This is exactly what the §8 root tooth recovers under CR
(`root_tooth_pins_kernel`) — and exactly what conservation needs. -/
def KernelChained (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: rest => s.pre.kernel = g.kernel ∧ KernelChained s.post rest

/-- **`KernelGenesisPin g steps`** — the head step's pre-KERNEL is genesis `g`'s (vacuous if empty).
Genesis is a PUBLIC, agreed value (the chain's declared start, pinned in `Aggregate.genesisRoot`), so
this is an honest input, NOT the malicious-prover surface (which is the INTER-step continuity, derived
below). Named as its own predicate so the conservation headlines share one stable hypothesis type. -/
def KernelGenesisPin (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: _    => s.pre.kernel = g.kernel

/-- `StateChained` (full-state) entails `KernelChained` (its kernel projection): equal states have
equal kernels. So `KernelChained` is the strictly weaker continuity the commitment can actually
deliver, and every honest `StateChained` chain is a `KernelChained` chain. -/
theorem kernelChained_of_stateChained (g : RecChainedState) (steps : List ChainStep)
    (hch : StateChained g steps) : KernelChained g steps := by
  induction steps generalizing g with
  | nil => trivial
  | cons s rest ih =>
    obtain ⟨hpre, hrest⟩ := hch
    exact ⟨by rw [hpre], ih s.post hrest⟩

/-- **`kernelChained_conserves` (KEYSTONE — conservation rides KERNEL continuity, no log).** Value is
conserved across the whole history given only KERNEL continuity from genesis: the ledger total at the
folded endpoint equals the genesis total. Proved by direct induction on the per-step kernel
conservation (`recKExec_conserves` over each `ChainStep.commits`, projected by `recCexec_kernel`) —
NOT via `Run`, so it never touches the receipt log. This is the conservation the §8 root genuinely
buys a light client, since the commitment binds the kernel. -/
theorem kernelChained_conserves (g : RecChainedState) (steps : List ChainStep)
    (hkc : KernelChained g steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  induction steps generalizing g with
  | nil => rfl
  | cons s rest ih =>
    obtain ⟨hpre, hrest⟩ := hkc
    -- this step conserves at the kernel level …
    have hstep : recTotal s.post.kernel = recTotal s.pre.kernel :=
      Dregg2.Exec.recKExec_conserves s.pre.kernel s.post.kernel s.turn (recCexec_kernel s.commits)
    -- … and the tail conserves from `s.post` by IH.
    have htail : recTotal (lastStateOf s.post rest).kernel = recTotal s.post.kernel := ih s.post hrest
    rw [show lastStateOf g (s :: rest) = lastStateOf s.post rest from rfl, htail, hstep, hpre]

/-- **`SeamStruct steps`** — the per-seam STRUCTURAL facts (NOT continuity, NOT roots): at every
adjacent pair the turn-contexts match AND both seam kernels are `AccountsWF` AND both are FINITELY
REPRESENTABLE (⚑ the last two are NEW, 2026-07-31: `root_tooth_pins_kernel` now runs through the
finite-support rest frame — `Circuit.RestFrameFin`). These are exactly the
non-cryptographic side facts `root_tooth_pins_kernel` consumes beyond the tooth itself: turn-match
holds under the accumulator's NoOp-padding (`ivc_turn_chain.rs:325`), and `AccountsWF` is the
structural invariant every `recKExec` PRESERVES (`StateCommit.recKExec_preserves_AccountsWF`). The
TOOTH itself is NOT here — it comes from `ChainBound`, which a verified `bindingProof` supplies. So
`SeamStruct` is the honest, non-prover-controlled structural envelope; continuity is DERIVED. -/
def SeamStruct : List ChainStep → Prop
  | []            => True
  | [_]           => True
  | s :: s' :: rest =>
      (s.turn = s'.turn ∧ AccountsWF s.post.kernel ∧ AccountsWF s'.pre.kernel
        ∧ Dregg2.Circuit.RestFrameFin.FiniteRepresentable s.post.kernel
        ∧ Dregg2.Circuit.RestFrameFin.FiniteRepresentable s'.pre.kernel)
      ∧ SeamStruct (s' :: rest)

/-- **`kernelChained_of_verified` (THE DERIVATION — state continuity FROM verification).** From the
genesis pin `s₀.pre.kernel = g.kernel` (genesis is public/agreed — NOT the malicious surface), the
verified root tooth `ChainBound` (what a verified `bindingProof` delivers, = `AggregateAttests.ordered`),
and the structural envelope `SeamStruct` (matched turns + `AccountsWF`), the whole chain is
`KernelChained`. Each inter-step seam `s.post.kernel = s'.pre.kernel` is DERIVED by
`root_tooth_pins_kernel` from the `ChainBound` tooth — it is no longer the prover-supplied `StateChained`
hypothesis the critique flagged. Kernel continuity (hence conservation) follows from the VERIFIED root
under the CR floor, with only the genesis pin + structural envelope as honest inputs. -/
theorem kernelChained_of_verified_orBreak
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) :
    ∀ steps : List ChainStep,
      KernelGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamStruct steps →
      OrBreak (StateBreakP CH cmb compress compressN) (KernelChained g steps)
  | [], _, _, _ => OrBreak.ok trivial
  | [_], hgen, _, _ => OrBreak.ok ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hstruct => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨⟨hturn, hwf, hwf', hfin, hfin'⟩, hstructrest⟩ := hstruct
    -- the seam is DERIVED from the verified tooth — or the chain hands back a concrete collision.
    refine OrBreak.bind (root_tooth_pins_kernel_orBreak CH RH cmb compress compressN hRest
      s s' hwf hwf' hfin hfin' hturn htooth) ?_
    intro hseam
    exact OrBreak.imp (fun htail => ⟨hgen, htail⟩)
      (kernelChained_of_verified_orBreak hRest s.post (s' :: rest)
        hseam.symm hboundrest hstructrest)

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** Four REFUTED premises ⇒ vacuous at deployed width.
`kernelChained_of_verified_orBreak` above is the surviving form. -/
theorem kernelChained_of_verified
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) :
    ∀ steps : List ChainStep,
      KernelGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamStruct steps →
      KernelChained g steps
  | [], _, _, _ => trivial
  | [s], hgen, _, _ => ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hstruct => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨⟨hturn, hwf, hwf', hfin, hfin'⟩, hstructrest⟩ := hstruct
    -- the seam `s.post.kernel = s'.pre.kernel` is DERIVED from the verified `ChainBound` tooth.
    have hseam : s.post.kernel = s'.pre.kernel :=
      root_tooth_pins_kernel CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
        s s' hwf hwf' hfin hfin' hturn htooth
    refine ⟨hgen, ?_⟩
    -- recurse on the tail from `s.post`; the next genesis pin is the derived seam (`s'.pre = s.post`).
    exact kernelChained_of_verified hCmb hCompress hCompressN hLeaf hRest s.post (s' :: rest)
      hseam.symm hboundrest hstructrest

/-- **`verified_history_conserves` (THE HEADLINE CLOSURE — conservation from VERIFICATION ALONE).**
Conservation across the WHOLE history with NO `StateChained` hypothesis: given the genesis pin, the
VERIFIED root tooth `ChainBound` (= `AggregateAttests.ordered`), and the structural envelope
`SeamStruct`, the ledger total at the folded endpoint equals the genesis total. Composes
`kernelChained_of_verified` (verified tooth ⇒ kernel continuity, via the strengthened
`root_tooth_pins_kernel`) with `kernelChained_conserves` (kernel continuity ⇒ conservation). This is
the precise statement the critique asked for: "trusting the aggregate trusts a no-mint/no-burn history"
now follows from the VERIFIED root, not from the prover's honesty about state continuity. -/
theorem verified_history_conserves_orBreak
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    OrBreak (StateBreakP CH cmb compress compressN)
      (recTotal (lastStateOf g steps).kernel = recTotal g.kernel) :=
  OrBreak.imp (kernelChained_conserves g steps)
    (kernelChained_of_verified_orBreak CH RH cmb compress compressN hRest g steps hgen hbound hstruct)

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** The headline "conservation from VERIFICATION ALONE" was, at
deployed BabyBear width, conservation from four FALSE premises. `verified_history_conserves_orBreak`
above is what the verified root actually buys: the conservation, or a named break of a deployed
primitive. -/
theorem verified_history_conserves
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  kernelChained_conserves g steps
    (kernelChained_of_verified CH RH cmb compress compressN hCmb hCompress hCompressN hLeaf hRest
      g steps hgen hbound hstruct)

/-! ### NON-OMISSION over the WHOLE history from the VERIFIED root tooth (the §2 repair, lifted).

The kernel-continuity path (`kernelChained_of_verified`) recovers KERNEL continuity from the verified
root tooth; its RECEIPT-LOG twin recovers LOG continuity, by the EXACT same induction but riding
`root_tooth_pins_log` (the rotated commit's second limb) instead of `root_tooth_pins_kernel`. Where the
kernel root needed the full Poseidon CR set + `AccountsWF`, the log root needs ONLY `compressNInjective`
(the outer sponge peel + `logRoot_injective`) — `SeamStruct`'s turn-match alone, its `AccountsWF` arm
unused. So a light client trusting the aggregate learns the receipt log chains genuinely across EVERY
folded step: no node dropped, forged, reordered, or truncated a receipt ANYWHERE in history. -/

/-- **`LogChained g steps`** — the steps form a contiguous executor run from genesis `g` AT THE
RECEIPT-LOG LEVEL: the first step's pre-LOG is `g`'s, and each step's post-log is the next step's
pre-log. The log twin of `KernelChained` — exactly what the rotated commit's receipt-log root recovers
under CR (`root_tooth_pins_log`). -/
def LogChained (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: rest => s.pre.log = g.log ∧ LogChained s.post rest

/-- **`LogGenesisPin g steps`** — the head step's pre-LOG is genesis `g`'s (vacuous if empty). The
honest, agreed genesis input (the published chain start), NOT the malicious surface (which is the
inter-step continuity, derived below). -/
def LogGenesisPin (g : RecChainedState) : List ChainStep → Prop
  | []        => True
  | s :: _    => s.pre.log = g.log

/-- **`logChained_of_verified` (THE NON-OMISSION DERIVATION — log continuity FROM verification).** From
the genesis log pin, the VERIFIED root tooth `ChainBound` (= `AggregateAttests.ordered`), and the
structural envelope `SeamStruct` (only its turn-match arm is used), the whole chain is `LogChained`:
each inter-step seam `s.post.log = s'.pre.log` is DERIVED by `root_tooth_pins_log` from the verified
tooth. So a light client verifying the aggregate root learns the receipt log chains genuinely across
the WHOLE history — omission impossible at every folded step — with NO `hweld`, resting on the rotated
commit's receipt-log limb under the one CR floor. -/
theorem logChained_of_verified_orBreak (g : RecChainedState) :
    ∀ steps : List ChainStep,
      LogGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamStruct steps →
      OrBreak (SpongeCollision compressN) (LogChained g steps)
  | [], _, _, _ => OrBreak.ok trivial
  | [_], hgen, _, _ => OrBreak.ok ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hstruct => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨⟨hturn, _, _⟩, hstructrest⟩ := hstruct
    refine OrBreak.bind
      (root_tooth_pins_log_orBreak CH RH cmb compress compressN s s' hturn htooth) ?_
    intro hseam
    exact OrBreak.imp (fun htail => ⟨hgen, htail⟩)
      (logChained_of_verified_orBreak s.post (s' :: rest)
        hseam.symm hboundrest hstructrest)

/-- ⚠ **BRIDGE ONLY (drained 2026-08-01).** `logChained_of_verified_orBreak` above is the deployed-true
whole-history non-omission statement: the log chains at every folded step, or the omitting node
EXHIBITS a `SpongeCollision compressN`. -/
theorem logChained_of_verified (hCompressN : compressNInjective compressN) (g : RecChainedState) :
    ∀ steps : List ChainStep,
      LogGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamStruct steps →
      LogChained g steps
  | [], _, _, _ => trivial
  | [_], hgen, _, _ => ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hstruct => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨⟨hturn, _, _⟩, hstructrest⟩ := hstruct
    have hseam : s.post.log = s'.pre.log :=
      root_tooth_pins_log CH RH cmb compress compressN hCompressN s s' hturn htooth
    exact ⟨hgen, logChained_of_verified hCompressN s.post (s' :: rest)
      hseam.symm hboundrest hstructrest⟩

/-- **`chainBound_of_stateChained`.** State-level continuity entails the root-level temporal
tooth at every seam WHERE THE TURN-CONTEXTS AGREE. We state the per-seam fact directly via
`seam_roots_chain`; whole-list `ChainBound` follows when each seam's turn-contexts agree (the
configuration the accumulator's NoOp-padding establishes — see `ivc_turn_chain.rs:325`). This makes
`WellFormedChain.bound` derivable from `chained` at matched seams, so an honest chain is well-formed
without separately asserting the binding. -/
theorem chainBound_of_stateChained (s s' : ChainStep) (rest : List ChainStep)
    (hcont : StateChained s.pre (s :: s' :: rest))
    (hturn : s.turn = s'.turn) :
    Continues CH RH cmb compress compressN s s' := by
  obtain ⟨_, hpre', _⟩ := hcont
  exact seam_roots_chain CH RH cmb compress compressN s s' hpre'.symm hturn

/-- **`wellformed_attests_whole_history` (THE HEADLINE).** A well-formed chain from genesis
`g` GENUINELY attests the whole history:
  (1) **every turn executed correctly** — for every step, `recCexec pre turn = some post` (the
      verified executor ran that turn);
  (2) **the chain is correctly ordered** — the root-level temporal tooth holds (`ChainBound`), so no
      reorder/drop/insert;
  (3) **the final root is the genuine fold of the whole history** — `foldedFinalRoot` commits the
      `lastStateOf`, the kernel reached by folding `recCexec` over ALL the turns, and the whole chain
      is a `Run recChainedSystem` from `g` to that state (so conservation et al. apply).
This is the meaning the IVC accumulator's `WholeChainProof` claims; `RecursiveAggregation.lean`
shows the SNARK aggregate, under the named soundness hypotheses, delivers EXACTLY this. -/
theorem wellformed_attests_whole_history (g : RecChainedState) (steps : List ChainStep)
    (hwf : WellFormedChain CH RH cmb compress compressN g steps) :
    (∀ s ∈ steps, recCexec s.pre s.turn = some s.post)         -- (1) every turn correct
      ∧ ChainBound CH RH cmb compress compressN steps          -- (2) correctly ordered
      ∧ Run recChainedSystem g (lastStateOf g steps)           -- (3) genuine fold = a real run …
      ∧ foldedFinalRoot CH RH cmb compress compressN g steps
          = match steps.getLast? with
            | none   => stateRoot CH RH cmb compress compressN g.kernel zeroTurn
            | some s => chainedCommit CH RH cmb compress compressN (lastStateOf g steps) s.turn :=
  ⟨every_turn_executed_correctly steps, hwf.bound,
   wellformed_is_run g steps hwf.chained, rfl⟩

/-! ## 7. NON-VACUITY — the binding tooth has TEETH (witnessed BOTH ways).

`WellFormedChain` is not empty (a real 1-step chain over the teeth genesis is well-formed), and the
temporal tooth REJECTS a broken order (two steps whose seam roots differ are NOT
`ChainBound`). Both witnessed below over the concrete `ConsensusExec.teethGenesis`. -/

open Dregg2.Exec.ConsensusExec (teethGenesis honestTurn tamperedTurn)

/-- A genuine honest step over the teeth genesis: cell 0 transfers 10 to cell 1. The `commits` field
is discharged by `decide` — `recCexec teethGenesis honestTurn` really is `some _`. -/
def honestStep : ChainStep where
  pre := teethGenesis
  turn := honestTurn
  post := (recCexec teethGenesis honestTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- **`honest_chain_wellformed` (non-vacuity, positive).** The single-step honest chain is
state-chained from genesis: `WellFormedChain` is INHABITED by a real executor run, so the headline is
not vacuous. (We exhibit `StateChained`; `ChainBound` on a singleton is `True`.) -/
theorem honest_chain_wellformed :
    WellFormedChain CH RH cmb compress compressN teethGenesis [honestStep] :=
  { chained := ⟨rfl, trivial⟩, bound := trivial }

/-- **`honest_step_executes` (non-vacuity).** The honest step's turn commits:
`recCexec teethGenesis honestTurn` is `some`. So `wellformed_is_run`/`…_conserves` apply to a REAL
non-empty history, not a vacuous `none`. -/
theorem honest_step_executes :
    (recCexec teethGenesis honestTurn).isSome = true := by decide

/-- **`honest_chain_kernelChained` (non-vacuity of the kernel-continuity path).** The honest
single-step chain is `KernelChained` from genesis — exhibited by projecting its `StateChained` witness
(`kernelChained_of_stateChained`). So the kernel-continuity conservation path (`kernelChained_conserves`
/ `verified_history_conserves`) fires on a REAL chain, not a vacuous one. -/
theorem honest_chain_kernelChained :
    KernelChained teethGenesis [honestStep] :=
  kernelChained_of_stateChained teethGenesis [honestStep] ⟨rfl, trivial⟩

/-- **`honest_kernelChained_conserves` (the conservation ENGINE fires).** The honest chain conserves
the ledger total through the KERNEL-continuity path (`kernelChained_conserves`, the conservation engine
the verification headline rides) — `recTotal` at the endpoint equals genesis (`100`, cell-0 debit 10 =
cell-1 credit 10). This witnesses that the NEW conservation-from-kernel-continuity machinery delivers a
TRUE conservation fact on a real executor run, independent of any `StateChained`/`Run`. -/
theorem honest_kernelChained_conserves :
    recTotal (lastStateOf teethGenesis [honestStep]).kernel = recTotal teethGenesis.kernel :=
  kernelChained_conserves teethGenesis [honestStep] honest_chain_kernelChained

/-- **`honest_total_is_100` (the conserved value is REAL, not a formal husk).** Reading the conclusion:
the honest chain's endpoint ledger total is exactly `100` — the genuine conserved supply. So the
conservation the kernel-continuity path proves is a TRUE arithmetic fact about a real run. -/
theorem honest_total_is_100 :
    recTotal (lastStateOf teethGenesis [honestStep]).kernel = 100 := by
  rw [honest_kernelChained_conserves]; decide

/-- **`tooth_rejects_broken_order` (THE ANTI-GHOST TOOTH, witnessed negative).** A reordered
/ spliced chain is NOT `ChainBound`: if the first step's `newRoot` differs from the second's
`oldRoot`, the `Continues` tooth fails, so `ChainBound` is false. We witness this abstractly: for ANY
two steps whose seam roots disagree, `ChainBound [s, s']` is `False` — exactly the
`TurnChainError::ChainBreak` rejection (`ivc_turn_chain.rs:138`), proving the binding is non-vacuous
(it separates a continuous order from a tampered one). -/
theorem tooth_rejects_broken_order (s s' : ChainStep)
    (hbreak : ChainStep.newRoot CH RH cmb compress compressN s
                ≠ ChainStep.oldRoot CH RH cmb compress compressN s') :
    ¬ ChainBound CH RH cmb compress compressN [s, s'] := by
  intro h
  exact hbreak h.1

end Portal

/-! ## 8. Axiom hygiene. -/

-- ⚑ the FLOOR-FREE twins (2026-08-01) — these are the ones that hold at the deployed sponge.
#assert_axioms Dregg2.Distributed.HistoryAggregation.turnReceipt_binds_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.logFelts_binds_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.logRoot_binds_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_log_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_of_verified_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves_orBreak
#assert_axioms Dregg2.Distributed.HistoryAggregation.logChained_of_verified_orBreak

#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel
-- the rotated commit BINDS the receipt log (non-omission, the §2 repair welded into the model):
#assert_axioms Dregg2.Distributed.HistoryAggregation.turnReceipt_injective
#assert_axioms Dregg2.Distributed.HistoryAggregation.logFelts_injective
#assert_axioms Dregg2.Distributed.HistoryAggregation.logRoot_injective
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_log
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_is_run
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_history_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.wellformed_attests_whole_history
#assert_axioms Dregg2.Distributed.HistoryAggregation.tooth_rejects_broken_order
-- the §8-root binds the KERNEL (not the log): conservation-over-history from VERIFICATION, not from a
-- prover-supplied StateChained hypothesis (the critique's CRITICAL-3 closure):
#assert_axioms Dregg2.Distributed.HistoryAggregation.recCexec_kernel
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_of_stateChained
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_of_verified
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves
-- non-omission over the WHOLE history, DERIVED from the verified root tooth (no hweld):
#assert_axioms Dregg2.Distributed.HistoryAggregation.logChained_of_verified
-- non-vacuity of the kernel-continuity conservation path (witnessed on a real executor run):
#assert_axioms Dregg2.Distributed.HistoryAggregation.honest_chain_kernelChained
#assert_axioms Dregg2.Distributed.HistoryAggregation.honest_kernelChained_conserves
#assert_axioms Dregg2.Distributed.HistoryAggregation.honest_total_is_100

end Dregg2.Distributed.HistoryAggregation
