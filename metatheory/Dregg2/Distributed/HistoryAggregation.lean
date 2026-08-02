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

⚑⚑ **2026-08-01 — THE `_orBreak` TWINS OF `ee18461c1` WERE ALSO VACUOUS, AND ARE NOW BRIDGES.**
Those twins removed the refuted `compressNInjective`/`compressInjective`/`cellLeafInjective`
hypotheses and paid for it with a disjunct that is a GLOBAL collision existential — `SpongeCollision
compressN`, and `StateBreakP`, which opens with it. Pigeonhole SUPPLIES that existential at every
field-bounded (= deployed) sponge, so every `OrBreak (SpongeCollision …) P` and `OrBreak (StateBreakP
…) P` in this file was literally `True` (`SpongeCollisionShirk.orBreak_spongeCollision_iff_True`,
`StateCommitReduce.orBreak_stateBreakP_iff_True`, both over an ARBITRARY good branch). Vacuous by
free disjunct instead of by false hypothesis.

Every keystone now has an UNCONDITIONAL `_or_collides` form whose residual is a collision AT THE
NAMED PAIR the extraction visits (`ReceiptColl` / `LogFeltsColl` / `LogRootColl` at the log layer;
`SeamSpongeColl` + `StateCommitLeafRegrounded.RecStateCommitColl` at the kernel layer;
`ChainKernelColl` / `ChainLogColl` bounded to the attested chain's OWN seams), plus an `_of_noColl`
form carrying ONE per-instance, refutable side condition at that pair. The `_orBreak` and
`_injective` forms are RETAINED, labelled `⚠ BRIDGE ONLY`, and re-derived through the port, so the
strength relation is machine-checked rather than asserted. §7b carries the teeth the free form
provably cannot: SATISFIABLE at every hash on an honest seam, REFUTABLE at a lossy one, NOT PROVABLE,
and LOAD-BEARING (dropping the residual leaves a REFUTED statement — including a two-step chain that
MINTS 400 while satisfying the genesis pin and the verified root tooth).

⚑ **2026-08-01, second pass — the LOG leg's teeth, which did not exist.** `ChainKernelColl` carried
all four discriminations; `ChainLogColl` — the residual of the OTHER headline S3
(`RecursiveAggregation.non_omission_from_verification_of_noColl`) — carried none, and
`ChainLogColl []`/`ChainLogColl [s]` are `False` by definition, so the lift is exactly where they
were needed. Built: `seamLogColl_fires_at_the_diagonal_seam`, `noSeamLogColl_not_provable`,
`logChained_of_verified_unconditional_false` and `chainLogColl_fires_at_the_omitting_chain` (firing
at that theorem's own counterexample — a two-step chain that DROPS a receipt while satisfying the
genesis log pin, the verified root tooth and a uniform turn-context). Two firing companions were also
added on the kernel side, where the load-bearing claims cited a theorem proved at a DIFFERENT witness
than their own counterexample: `seamKernelColl_fires_at_the_diagonal_seam` and
`seamStateColl_fires_at_the_diagonal_seam`.

⚠ **WHAT THE `_unconditional_false` THEOREMS IN THIS FILE DO NOT REACH, said once at the top.** Every
one of them refutes an `hno`-deleted keystone OF THIS FILE, all of which hypothesise `ChainBound`
DIRECTLY. The two HEADLINE S3s live one layer up in `RecursiveAggregation` and replace `ChainBound`
with `es : EngineSound …` + `hroot : verify agg.root = true` — a STRICTLY STRONGER hypothesis set, so
none of these theorems says anything about them, and both S3 docstrings claimed one did. Their teeth
are `RecursiveAggregation.non_omission_from_verification_unconditional_false` and
`…conserves_from_verification_unconditional_false` (§5b there), which inhabit `EngineSound` at the
counterexample chains — verification genuinely does NOT exclude the omitting or the minting history.

⚑ And the honest price is now a THEOREM, not a comment: `¬ SeamLogColl` is NOT free for an honest
prover once the receipt log is non-empty (`seamLogColl_fires_at_honest_seam_with_colliding_log`
exhibits an honest seam between two genuine executor steps where it holds). The discharge is
`noSeamLogColl_of_honest_of_noSelfColl` / `noChainLogColl_of_honest` — a FINITE self-collision check
over the receipt pairs the node already holds; per-instance and decidable, a price rather than a
floor, but not zero. `noLogFeltsColl_self_of_short` pins where it starts (two receipts, not one) and
`noChainLogColl_at_the_honest_two_step_chain` witnesses that the discharge is reachable on a real
chain.

⚑⚑ **BREAKING, and say what broke.** `logChained_of_verified_or_collides` / `_of_noColl` now take
`SeamTurnMatch` (the per-seam turn-context match) instead of `SeamStruct`, and so do
`RecursiveAggregation.non_omission_from_verification_or_collides` / `_of_noColl`. The log recovery
never read `SeamStruct`'s `AccountsWF` / `FiniteRepresentable` arms — and carrying them made the S3's
load-bearing tooth UNSTATABLE, since no `ChainStep` here satisfies `AccountsWF`, so any counterexample
had to shed the envelope along with `hno`. Narrowed, the refutation is exact. Callers holding
`SeamStruct` insert `seamTurnMatch_of_seamStruct`; the two `⚠ BRIDGE ONLY` forms
(`logChained_of_verified_orBreak`, `non_omission_from_verification_orBreak`) keep the wide signature,
so `Lightclient/NonOmissionAttack` and everything else outside these two modules is untouched. The
KERNEL leg's teeth still shed the envelope — that residual is unchanged and named on
`root_tooth_pins_kernel_unconditional_false`.

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
  recStateCommit_binds_kernel_orBreak recStateCommit_binds_kernel_or_collidesFin)
-- ⚑ the PER-INSTANCE residual vocabulary (2026-08-01, the free-disjunct port): a collision at a
-- NAMED pair, never `∃ two colliding inputs`.
open Dregg2.Circuit.SpongeCollisionShirk (SpongeColl)
open Dregg2.Circuit.StateCommitLeafRegrounded (CompressColl RecStateCommitColl
  recStateCommit_binds_or_collides noRecStateCommitColl_diag)

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

/-! #### ⚑⚑ THE PER-INSTANCE PORT (2026-08-01) — the `_orBreak` twins above were ALSO free.

`SpongeCollision compressN` is a GLOBAL existential ("there EXIST two colliding lists"), which
`SpongeCollisionShirk.spongeCollision_of_fieldBounded` SUPPLIES at every field-bounded sponge — i.e.
at every sponge this chain deploys. So `OrBreak (SpongeCollision compressN) P` is literally `True`
(`SpongeCollisionShirk.orBreak_spongeCollision_iff_True`, over an arbitrary good branch `P`), and the
twins landed in `ee18461c1` traded vacuous-by-false-hypothesis for vacuous-by-free-disjunct.

The sound shape is the one `Circuit/StateCommitLeafRegrounded` and `Circuit/AggregationAirSound`
use: an UNCONDITIONAL dichotomy whose residual is a collision AT THE NAMED PAIR the extraction
visits (`SpongeCollisionShirk.SpongeColl hash xs ys := xs ≠ ys ∧ hash xs = hash ys`), and a
per-instance side condition `¬ Coll … p` at THAT pair. ⚠ Universally quantifying the side condition
would re-write injectivity and restore the vacuity; none of the `_of_noColl` forms below does. -/

/-- The four felts the deployed receipt absorb feeds the sponge — `turnReceipt`'s SPONGE ARGUMENT,
named so a residual can talk about the specific pair rather than about "some pair". -/
def receiptFelts (t : Dregg2.Exec.Turn) : List ℤ :=
  [(t.actor : ℤ), (t.src : ℤ), (t.dst : ℤ), t.amt]

/-- `turnReceipt` IS the sponge of `receiptFelts` (definitional). -/
theorem turnReceipt_eq (t : Dregg2.Exec.Turn) :
    turnReceipt compressN t = compressN (receiptFelts t) := rfl

/-- The receipt encoding is injective — a STRUCTURAL fact about the four-field layout, no hash
anywhere. This is what makes `ReceiptColl` a claim about the SPONGE and not about the framing. -/
theorem receiptFelts_injective {t t' : Dregg2.Exec.Turn}
    (h : receiptFelts t = receiptFelts t') : t = t' := by
  obtain ⟨a, b, c, d⟩ := t
  obtain ⟨a', b', c', d'⟩ := t'
  simp only [receiptFelts, List.cons.injEq, and_true, Nat.cast_inj] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  subst h1; subst h2; subst h3; subst h4; rfl

/-- **`ReceiptColl compressN t t'`** — the two turns' 4-felt absorbs are a GENUINE collision of the
deployed sponge, AT THE NAMED PAIR. Distinctness is inside `SpongeColl`, so the side condition is
never satisfied vacuously by an equal pair. -/
def ReceiptColl (t t' : Dregg2.Exec.Turn) : Prop :=
  SpongeColl compressN (receiptFelts t) (receiptFelts t')

/-- **⚑ UNCONDITIONAL receipt binding.** A receipt felt commits the whole turn, OR the deployed
sponge collides at the two NAMED 4-felt absorbs. No injectivity hypothesis, no global existential. -/
theorem turnReceipt_binds_or_collides {t t' : Dregg2.Exec.Turn}
    (h : turnReceipt compressN t = turnReceipt compressN t') :
    t = t' ∨ ReceiptColl compressN t t' := by
  by_cases hp : receiptFelts t = receiptFelts t'
  · exact Or.inl (receiptFelts_injective hp)
  · exact Or.inr ⟨hp, h⟩

/-- **`LogFeltsColl compressN L L'`** — a receipt-level equivocation at a pair of turns DRAWN FROM
the two logs in play. Bounded to the named lists (the `StateCommitLeafRegrounded.FrameLeafColl`
shape); it is NOT the global "some two turns collide", which pigeonhole would supply for free. -/
def LogFeltsColl (L L' : List Dregg2.Exec.Turn) : Prop :=
  ∃ t ∈ L, ∃ t' ∈ L', ReceiptColl compressN t t'

/-- **⚑ UNCONDITIONAL receipt-felt-list binding.** The receipt-felt list determines the audit log, OR
a named pair of its turns collides. Structural recursion mirrors the injective original. -/
theorem logFelts_binds_or_collides :
    ∀ {L L' : List Dregg2.Exec.Turn}, logFelts compressN L = logFelts compressN L' →
      L = L' ∨ LogFeltsColl compressN L L'
  | [], [], _ => Or.inl rfl
  | [], _ :: _, h => by simp [logFelts] at h
  | _ :: _, [], h => by simp [logFelts] at h
  | x :: xs, y :: ys, h => by
    simp only [logFelts, List.map_cons, List.cons.injEq] at h
    rcases turnReceipt_binds_or_collides compressN h.1 with hx | hc
    · rcases logFelts_binds_or_collides (L := xs) (L' := ys) h.2 with hxs | ⟨t, ht, t', ht', hc⟩
      · exact Or.inl (by rw [hx, hxs])
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, t', List.mem_cons_of_mem _ ht', hc⟩
    · exact Or.inr ⟨x, by simp, y, by simp, hc⟩

/-- **`LogRootColl compressN L L'`** — the receipt-index root equivocated on the two NAMED logs: the
sponge collided at the two named felt lists, or a named receipt pair did. -/
def LogRootColl (L L' : List Dregg2.Exec.Turn) : Prop :=
  SpongeColl compressN (logFelts compressN L) (logFelts compressN L')
    ∨ LogFeltsColl compressN L L'

/-- **⚑ THE UNCONDITIONAL LOG-ROOT BINDING — the non-omission primitive at deployed parameters.**
Two audit logs with equal receipt-index roots are EQUAL, OR the NAMED residual `LogRootColl` holds at
the exact argument pairs the extraction visits. No `compressNInjective` (refuted), no
`SpongeCollision` (free): a node that keeps the published root while suppressing, forging, reordering
or truncating a receipt must break the deployed sponge AT A PAIR THIS THEOREM NAMES. -/
theorem logRoot_binds_or_collides {L L' : List Dregg2.Exec.Turn}
    (h : logRoot compressN L = logRoot compressN L') :
    L = L' ∨ LogRootColl compressN L L' := by
  by_cases hp : logFelts compressN L = logFelts compressN L'
  · exact Or.imp_right Or.inr (logFelts_binds_or_collides compressN hp)
  · exact Or.inr (Or.inl ⟨hp, h⟩)

/-- **S3** — the injective original's conclusion, from the PER-INSTANCE residual at the named pair. -/
theorem logRoot_binds_of_noColl {L L' : List Dregg2.Exec.Turn}
    (hno : ¬ LogRootColl compressN L L')
    (h : logRoot compressN L = logRoot compressN L') : L = L' :=
  (logRoot_binds_or_collides compressN h).resolve_right hno

/-! #### The FREE-DISJUNCT twins, retained as ⚠ BRIDGE ONLY and re-derived through the port.

Each `_orBreak` below is now `_or_collides` with its NAMED pair forgotten into the global existential
— which is exactly the step that makes it free. They are kept (consumers in `Lightclient/
NonOmissionAttack` still open them) and re-derived, so the strength relation is machine-checked
rather than asserted; nothing in this file's ported chain consumes them. -/

/-- A named receipt collision cashes out as a sponge break (⚠ the direction that LOSES the pair). -/
theorem ReceiptColl.toSponge {t t' : Dregg2.Exec.Turn} (h : ReceiptColl compressN t t') :
    SpongeCollision compressN := ⟨_, _, h.1, h.2⟩

/-- A named receipt-felt-list collision cashes out as a sponge break. -/
theorem LogFeltsColl.toSponge {L L' : List Dregg2.Exec.Turn} (h : LogFeltsColl compressN L L') :
    SpongeCollision compressN := by
  obtain ⟨_, _, _, _, hc⟩ := h
  exact hc.toSponge compressN

/-- A named log-root collision cashes out as a sponge break. -/
theorem LogRootColl.toSponge {L L' : List Dregg2.Exec.Turn} (h : LogRootColl compressN L L') :
    SpongeCollision compressN := by
  rcases h with ⟨hne, heq⟩ | hc
  · exact ⟨_, _, hne, heq⟩
  · exact hc.toSponge compressN

/-- ⚠ **BRIDGE ONLY.** `SpongeCollision compressN` is a GLOBAL existential, hence FREE at every
field-bounded sponge, so this dichotomy is `True` as deployed. `turnReceipt_binds_or_collides` is the
form that discriminates. -/
theorem turnReceipt_binds_orBreak {t t' : Dregg2.Exec.Turn}
    (h : turnReceipt compressN t = turnReceipt compressN t') :
    OrBreak (SpongeCollision compressN) (t = t') :=
  Or.imp_right (ReceiptColl.toSponge compressN) (turnReceipt_binds_or_collides compressN h)

/-- ⚠ **BRIDGE ONLY** (see `turnReceipt_binds_orBreak`). -/
theorem logFelts_binds_orBreak {L L' : List Dregg2.Exec.Turn}
    (h : logFelts compressN L = logFelts compressN L') :
    OrBreak (SpongeCollision compressN) (L = L') :=
  Or.imp_right (LogFeltsColl.toSponge compressN) (logFelts_binds_or_collides compressN h)

/-- ⚠ **BRIDGE ONLY.** Announced as "the non-omission keystone at deployed parameters" in
`ee18461c1`; it is not — its disjunct is supplied by pigeonhole at the deployed sponge.
`logRoot_binds_or_collides` is the surviving statement. -/
theorem logRoot_binds_orBreak {L L' : List Dregg2.Exec.Turn}
    (h : logRoot compressN L = logRoot compressN L') :
    OrBreak (SpongeCollision compressN) (L = L') :=
  Or.imp_right (LogRootColl.toSponge compressN) (logRoot_binds_or_collides compressN h)

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

/-! ### ⚑⚑ THE SEAM RESIDUAL, PER-INSTANCE (2026-08-01) — the port of §5's three teeth.

Every seam theorem does the same two things: peel ONE outer rotated sponge at ONE NAMED limb pair,
then hand the kernel-digest limb to the whole-kernel binding or the receipt-log limb to the log root.
Both callees already have per-instance ports (`StateCommitReduce.recStateCommit_binds_kernel_-
or_collidesFin`, residual `StateCommitLeafRegrounded.RecStateCommitColl`; `logRoot_binds_or_collides`,
residual `LogRootColl`), so the seam residual is exactly the union of the outer sponge event at the
named limb pair and the callee's residual — never a global existential. -/

/-- The two limbs the deployed rotated commit absorbs at a state/turn — `chainedCommit`'s SPONGE
ARGUMENT, named so the outer peel's residual can name the specific pair. -/
def seamLimbs (st : RecChainedState) (t : Dregg2.Exec.Turn) : List ℤ :=
  [recStateCommit CH RH cmb compress compressN st.kernel t, logRoot compressN st.log]

/-- `chainedCommit` IS the sponge of `seamLimbs` (definitional). -/
theorem chainedCommit_eq (st : RecChainedState) (t : Dregg2.Exec.Turn) :
    chainedCommit CH RH cmb compress compressN st t
      = compressN (seamLimbs CH RH cmb compress compressN st t) := rfl

/-- The seam tooth, restated at the sponge argument the peel actually inspects. -/
theorem seam_limbs_of_tooth (s s' : ChainStep) (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    compressN (seamLimbs CH RH cmb compress compressN s.post s'.turn)
      = compressN (seamLimbs CH RH cmb compress compressN s'.pre s'.turn) := by
  unfold ChainStep.newRoot ChainStep.oldRoot at htooth
  rw [hturn] at htooth
  exact htooth

/-- **`SeamSpongeColl s s'`** — the OUTER rotated sponge collided at the seam's NAMED limb pair. -/
def SeamSpongeColl (s s' : ChainStep) : Prop :=
  SpongeColl compressN (seamLimbs CH RH cmb compress compressN s.post s'.turn)
    (seamLimbs CH RH cmb compress compressN s'.pre s'.turn)

/-- **`SeamStateColl s s'`** — the outer sponge collided at the named limb pair, or the ROOT COMBINER
did at the named `(cellDigest, RH)` pair. The residual of the commitment-level seam recovery. -/
def SeamStateColl (s s' : ChainStep) : Prop :=
  SeamSpongeColl CH RH cmb compress compressN s s'
    ∨ CompressColl cmb
        (cellDigest CH compress compressN s.post.kernel s'.turn) (RH s.post.kernel)
        (cellDigest CH compress compressN s'.pre.kernel s'.turn) (RH s'.pre.kernel)

/-- **`SeamKernelColl s s'`** — the outer sponge collided at the named limb pair, or one of the four
commitment primitives did at the argument pairs `RecStateCommitColl` names. -/
def SeamKernelColl (s s' : ChainStep) : Prop :=
  SeamSpongeColl CH RH cmb compress compressN s s'
    ∨ RecStateCommitColl CH RH cmb compress compressN s.post.kernel s'.pre.kernel s'.turn

/-- **`SeamLogColl s s'`** — the outer sponge collided at the named limb pair, or the receipt-index
root did at the named log pair. The NARROW seam residual: this leg costs only the sponge. -/
def SeamLogColl (s s' : ChainStep) : Prop :=
  SeamSpongeColl CH RH cmb compress compressN s s'
    ∨ LogRootColl compressN s.post.log s'.pre.log

/-- **⚑ `root_tooth_pins_state_or_collides` — THE COMMITMENT-LEVEL SEAM RECOVERY, UNCONDITIONAL.**
An agreeing root tooth at a matched turn-context forces the adjacent cell-digests AND rest-hashes
equal, OR the NAMED residual `SeamStateColl` holds at the exact pairs the extraction visits. No
injectivity hypothesis, no global collision existential. -/
theorem root_tooth_pins_state_or_collides (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    (cellDigest CH compress compressN s.post.kernel s'.turn
        = cellDigest CH compress compressN s'.pre.kernel s'.turn
      ∧ RH s.post.kernel = RH s'.pre.kernel)
      ∨ SeamStateColl CH RH cmb compress compressN s s' := by
  have hsp := seam_limbs_of_tooth CH RH cmb compress compressN s s' hturn htooth
  by_cases hp : seamLimbs CH RH cmb compress compressN s.post s'.turn
      = seamLimbs CH RH cmb compress compressN s'.pre s'.turn
  · have hlimb : recStateCommit CH RH cmb compress compressN s.post.kernel s'.turn
        = recStateCommit CH RH cmb compress compressN s'.pre.kernel s'.turn := by
      simp only [seamLimbs, List.cons.injEq, and_true] at hp
      exact hp.1
    exact Or.imp_right Or.inr
      (recStateCommit_binds_or_collides CH RH cmb compress compressN
        s.post.kernel s'.pre.kernel s'.turn hlimb)
  · exact Or.inr (Or.inl ⟨hp, hsp⟩)

/-- **S3** — the injective original's conclusion, from the per-instance residual at the named pair. -/
theorem root_tooth_pins_state_of_noColl (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (hno : ¬ SeamStateColl CH RH cmb compress compressN s s')
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    cellDigest CH compress compressN s.post.kernel s'.turn
        = cellDigest CH compress compressN s'.pre.kernel s'.turn
      ∧ RH s.post.kernel = RH s'.pre.kernel :=
  (root_tooth_pins_state_or_collides CH RH cmb compress compressN s s' hturn htooth).resolve_right
    hno

/-- **⚑⚑ `root_tooth_pins_kernel_or_collides` — THE STRENGTHENED SEAM RECOVERY, UNCONDITIONAL.**
An agreeing root tooth at a matched turn-context forces the adjacent KERNELS equal, OR the NAMED
four-way residual `SeamKernelColl` holds. `RestHashIffFrameFin` is the one carried premise (a
structural rest-frame correspondence, not a hash floor — `Verify.RestFrameFiniteSupportSuccessor`);
`AccountsWF`/`FiniteRepresentable` are structural. This is what a light client seeing only matching
roots genuinely learns AT THE DEPLOYED HASH. -/
theorem root_tooth_pins_kernel_or_collides
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH) (s s' : ChainStep)
    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s.post.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s'.pre.kernel)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.kernel = s'.pre.kernel ∨ SeamKernelColl CH RH cmb compress compressN s s' := by
  have hsp := seam_limbs_of_tooth CH RH cmb compress compressN s s' hturn htooth
  by_cases hp : seamLimbs CH RH cmb compress compressN s.post s'.turn
      = seamLimbs CH RH cmb compress compressN s'.pre s'.turn
  · have hlimb : recStateCommit CH RH cmb compress compressN s.post.kernel s'.turn
        = recStateCommit CH RH cmb compress compressN s'.pre.kernel s'.turn := by
      simp only [seamLimbs, List.cons.injEq, and_true] at hp
      exact hp.1
    exact Or.imp_right Or.inr
      (recStateCommit_binds_kernel_or_collidesFin CH cmb compress compressN RH hRest
        s.post.kernel s'.pre.kernel s'.turn hwf hwf' hfin hfin' hlimb)
  · exact Or.inr (Or.inl ⟨hp, hsp⟩)

/-- **S3** — the injective original's conclusion, from the per-instance residual at the named seam. -/
theorem root_tooth_pins_kernel_of_noColl
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH) (s s' : ChainStep)
    (hwf : AccountsWF s.post.kernel) (hwf' : AccountsWF s'.pre.kernel)
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s.post.kernel)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable s'.pre.kernel)
    (hturn : s.turn = s'.turn)
    (hno : ¬ SeamKernelColl CH RH cmb compress compressN s s')
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.kernel = s'.pre.kernel :=
  (root_tooth_pins_kernel_or_collides CH RH cmb compress compressN hRest s s' hwf hwf' hfin hfin'
    hturn htooth).resolve_right hno

/-- **⚑ `root_tooth_pins_log_or_collides` — THE NON-OMISSION SEAM TOOTH, UNCONDITIONAL.** An agreeing
root tooth at a matched turn-context forces the adjacent RECEIPT LOGS equal, OR the NAMED residual
`SeamLogColl` holds. A node that drops, forges, reorders or truncates a receipt must break the
deployed sponge at a pair THIS THEOREM NAMES. -/
theorem root_tooth_pins_log_or_collides (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.log = s'.pre.log ∨ SeamLogColl CH RH cmb compress compressN s s' := by
  have hsp := seam_limbs_of_tooth CH RH cmb compress compressN s s' hturn htooth
  by_cases hp : seamLimbs CH RH cmb compress compressN s.post s'.turn
      = seamLimbs CH RH cmb compress compressN s'.pre s'.turn
  · have hlimb : logRoot compressN s.post.log = logRoot compressN s'.pre.log := by
      simp only [seamLimbs, List.cons.injEq, and_true] at hp
      exact hp.2
    exact Or.imp_right Or.inr (logRoot_binds_or_collides compressN hlimb)
  · exact Or.inr (Or.inl ⟨hp, hsp⟩)

/-- **S3** — the injective original's conclusion, from the per-instance residual at the named seam. -/
theorem root_tooth_pins_log_of_noColl (s s' : ChainStep)
    (hturn : s.turn = s'.turn)
    (hno : ¬ SeamLogColl CH RH cmb compress compressN s s')
    (htooth : ChainStep.newRoot CH RH cmb compress compressN s
                = ChainStep.oldRoot CH RH cmb compress compressN s') :
    s.post.log = s'.pre.log :=
  (root_tooth_pins_log_or_collides CH RH cmb compress compressN s s' hturn htooth).resolve_right hno

/-! #### The cash-out maps (⚠ the direction that LOSES the named pair, kept only for the bridges). -/

/-- A `RecStateCommitColl` at a named pair cashes out as a `StateBreakP` — the four-way apex break
with the pair FORGOTTEN. ⚠ It is that forgetting that makes the target free at deployed parameters
(`StateCommitReduce.orBreak_stateBreakP_iff_True`); nothing on a ported path may travel this way. -/
theorem stateBreakP_of_recStateCommitColl {k k' : Dregg2.Exec.RecordKernelState}
    {t : Dregg2.Exec.Turn} (h : RecStateCommitColl CH RH cmb compress compressN k k' t) :
    StateBreakP CH cmb compress compressN := by
  rcases h with hr | hn | hf | hm
  · exact StateBreakP.ofCmb CH cmb compress compressN hr.extracts
  · exact StateBreakP.ofCompress CH cmb compress compressN hn.extracts
  · rcases hf.extracts with hs | hc
    · exact StateBreakP.ofSponge CH cmb compress compressN hs
    · exact StateBreakP.ofCell CH cmb compress compressN hc
  · rcases hm.extracts with hn2 | hc
    · exact StateBreakP.ofCompress CH cmb compress compressN hn2
    · exact StateBreakP.ofCell CH cmb compress compressN hc

/-- The seam sponge event cashes out as a bare sponge existential. -/
theorem SeamSpongeColl.toSponge {s s' : ChainStep}
    (h : SeamSpongeColl CH RH cmb compress compressN s s') : SpongeCollision compressN :=
  ⟨_, _, h.1, h.2⟩

/-- The kernel seam residual cashes out as the apex break. -/
theorem SeamKernelColl.toStateBreak {s s' : ChainStep}
    (h : SeamKernelColl CH RH cmb compress compressN s s') :
    StateBreakP CH cmb compress compressN := by
  rcases h with hs | hk
  · exact StateBreakP.ofSponge CH cmb compress compressN (hs.toSponge CH RH cmb compress compressN)
  · exact stateBreakP_of_recStateCommitColl CH RH cmb compress compressN hk

/-- The commitment-level seam residual cashes out as the apex break. -/
theorem SeamStateColl.toStateBreak {s s' : ChainStep}
    (h : SeamStateColl CH RH cmb compress compressN s s') :
    StateBreakP CH cmb compress compressN := by
  rcases h with hs | hc
  · exact StateBreakP.ofSponge CH cmb compress compressN (hs.toSponge CH RH cmb compress compressN)
  · exact StateBreakP.ofCmb CH cmb compress compressN hc.extracts

/-- The log seam residual cashes out as a bare sponge existential. -/
theorem SeamLogColl.toSponge {s s' : ChainStep}
    (h : SeamLogColl CH RH cmb compress compressN s s') : SpongeCollision compressN := by
  rcases h with hs | hl
  · exact hs.toSponge CH RH cmb compress compressN
  · exact hl.toSponge compressN

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
        ∧ RH s.post.kernel = RH s'.pre.kernel) :=
  -- ⚠ BRIDGE ONLY (2026-08-01): re-derived from the per-instance port by FORGETTING the named pair,
  -- which is exactly the step that makes the disjunct free at deployed parameters.
  Or.imp_right (SeamStateColl.toStateBreak CH RH cmb compress compressN)
    (root_tooth_pins_state_or_collides CH RH cmb compress compressN s s' hturn htooth)

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
    OrBreak (StateBreakP CH cmb compress compressN) (s.post.kernel = s'.pre.kernel) :=
  -- ⚠ BRIDGE ONLY (2026-08-01): `StateBreakP` opens with a GLOBAL sponge existential, so this
  -- dichotomy is `True` at deployed parameters. `root_tooth_pins_kernel_or_collides` is the form
  -- that discriminates; this one is retained only to machine-check that nothing was given up.
  Or.imp_right (SeamKernelColl.toStateBreak CH RH cmb compress compressN)
    (root_tooth_pins_kernel_or_collides CH RH cmb compress compressN hRest s s' hwf hwf' hfin hfin'
      hturn htooth)

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
    OrBreak (SpongeCollision compressN) (s.post.log = s'.pre.log) :=
  -- ⚠ BRIDGE ONLY (2026-08-01). `root_tooth_pins_log_or_collides` is the form that discriminates.
  Or.imp_right (SeamLogColl.toSponge CH RH cmb compress compressN)
    (root_tooth_pins_log_or_collides CH RH cmb compress compressN s s' hturn htooth)

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

/-! ### **`kernelChained_of_verified` (THE DERIVATION — state continuity FROM verification).** From the
genesis pin `s₀.pre.kernel = g.kernel` (genesis is public/agreed — NOT the malicious surface), the
verified root tooth `ChainBound` (what a verified `bindingProof` delivers, = `AggregateAttests.ordered`),
and the structural envelope `SeamStruct` (matched turns + `AccountsWF`), the whole chain is
`KernelChained`. Each inter-step seam `s.post.kernel = s'.pre.kernel` is DERIVED by
`root_tooth_pins_kernel` from the `ChainBound` tooth — it is no longer the prover-supplied `StateChained`
hypothesis the critique flagged. Kernel continuity (hence conservation) follows from the VERIFIED root
under the CR floor, with only the genesis pin + structural envelope as honest inputs. -/
/-- **`ChainKernelColl steps`** — SOME adjacent seam of THE NAMED LIST equivocated. Bounded to the
steps in play (the `FrameLeafColl` shape): it names a seam of `steps`, never "some seam somewhere". -/
def ChainKernelColl : List ChainStep → Prop
  | []              => False
  | [_]             => False
  | s :: s' :: rest =>
      SeamKernelColl CH RH cmb compress compressN s s'
        ∨ ChainKernelColl (s' :: rest)

/-- **⚑⚑ `kernelChained_of_verified_or_collides` — KERNEL CONTINUITY FROM VERIFICATION,
UNCONDITIONAL.** From the genesis pin, the VERIFIED root tooth `ChainBound`, and the structural
envelope `SeamStruct`, the whole chain is `KernelChained`, OR the NAMED residual `ChainKernelColl`
holds at one of the chain's own seams. No injectivity hypothesis and no global existential: the
adversary must name the seam and the argument pair it broke. -/
theorem kernelChained_of_verified_or_collides
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) :
    ∀ steps : List ChainStep,
      KernelGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamStruct steps →
      KernelChained g steps ∨ ChainKernelColl CH RH cmb compress compressN steps
  | [], _, _, _ => Or.inl trivial
  | [_], hgen, _, _ => Or.inl ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hstruct => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨⟨hturn, hwf, hwf', hfin, hfin'⟩, hstructrest⟩ := hstruct
    rcases root_tooth_pins_kernel_or_collides CH RH cmb compress compressN hRest
        s s' hwf hwf' hfin hfin' hturn htooth with hseam | hc
    · rcases kernelChained_of_verified_or_collides hRest s.post (s' :: rest)
          hseam.symm hboundrest hstructrest with htail | hc
      · exact Or.inl ⟨hgen, htail⟩
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hc)

/-- **S3** — kernel continuity from the PER-INSTANCE chain residual. -/
theorem kernelChained_of_verified_of_noColl
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps)
    (hno : ¬ ChainKernelColl CH RH cmb compress compressN steps) :
    KernelChained g steps :=
  (kernelChained_of_verified_or_collides CH RH cmb compress compressN hRest g steps hgen hbound
    hstruct).resolve_right hno

/-- The chain residual cashes out as the apex break (⚠ the direction that LOSES the seam). -/
theorem ChainKernelColl.toStateBreak : ∀ {steps : List ChainStep},
    ChainKernelColl CH RH cmb compress compressN steps → StateBreakP CH cmb compress compressN
  | [], h => False.elim h
  | [_], h => False.elim h
  | _ :: s' :: rest, h => by
    rcases h with hc | hrest
    · exact SeamKernelColl.toStateBreak CH RH cmb compress compressN hc
    · exact ChainKernelColl.toStateBreak (steps := s' :: rest) hrest

/-- ⚠ **BRIDGE ONLY (2026-08-01).** Re-derived from `kernelChained_of_verified_or_collides` by
forgetting which seam and which pair broke; `StateBreakP`'s leading global sponge existential then
makes the dichotomy `True` at deployed parameters. Retained so the strength relation is
machine-checked; nothing on the ported path consumes it. -/
theorem kernelChained_of_verified_orBreak
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    OrBreak (StateBreakP CH cmb compress compressN) (KernelChained g steps) :=
  Or.imp_right (ChainKernelColl.toStateBreak CH RH cmb compress compressN)
    (kernelChained_of_verified_or_collides CH RH cmb compress compressN hRest g steps hgen hbound
      hstruct)

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
theorem verified_history_conserves_or_collides
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel
      ∨ ChainKernelColl CH RH cmb compress compressN steps :=
  Or.imp_left (kernelChained_conserves g steps)
    (kernelChained_of_verified_or_collides CH RH cmb compress compressN hRest g steps hgen hbound
      hstruct)

/-- **S3 — THE HEADLINE, from the PER-INSTANCE residual.** Conservation across the whole history from
`verify`-supplied inputs plus ONE refutable side condition naming the chain's own seams. -/
theorem verified_history_conserves_of_noColl
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps)
    (hno : ¬ ChainKernelColl CH RH cmb compress compressN steps) :
    recTotal (lastStateOf g steps).kernel = recTotal g.kernel :=
  (verified_history_conserves_or_collides CH RH cmb compress compressN hRest g steps hgen hbound
    hstruct).resolve_right hno

/-- ⚠ **BRIDGE ONLY (2026-08-01).** The free-disjunct twin, re-derived from the port.
`verified_history_conserves_or_collides` is the form that discriminates. -/
theorem verified_history_conserves_orBreak
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (g : RecChainedState) (steps : List ChainStep)
    (hgen : KernelGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    OrBreak (StateBreakP CH cmb compress compressN)
      (recTotal (lastStateOf g steps).kernel = recTotal g.kernel) :=
  Or.imp_right (ChainKernelColl.toStateBreak CH RH cmb compress compressN)
    (verified_history_conserves_or_collides CH RH cmb compress compressN hRest g steps hgen hbound
      hstruct)

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

/-! ### **`logChained_of_verified` (THE NON-OMISSION DERIVATION — log continuity FROM verification).** From
the genesis log pin, the VERIFIED root tooth `ChainBound` (= `AggregateAttests.ordered`), and the
structural envelope `SeamStruct` (only its turn-match arm is used), the whole chain is `LogChained`:
each inter-step seam `s.post.log = s'.pre.log` is DERIVED by `root_tooth_pins_log` from the verified
tooth. So a light client verifying the aggregate root learns the receipt log chains genuinely across
the WHOLE history — omission impossible at every folded step — with NO `hweld`, resting on the rotated
commit's receipt-log limb under the one CR floor. -/
/-- **`ChainLogColl steps`** — SOME adjacent seam of THE NAMED LIST equivocated at the receipt-log
limb. Bounded to the steps in play; the narrow (sponge-only) twin of `ChainKernelColl`. -/
def ChainLogColl : List ChainStep → Prop
  | []              => False
  | [_]             => False
  | s :: s' :: rest =>
      SeamLogColl CH RH cmb compress compressN s s'
        ∨ ChainLogColl (s' :: rest)

/-- **`SeamTurnMatch steps`** — the per-seam turn-context match, and NOTHING else. This is the ONLY
arm of `SeamStruct` the log recovery reads: `root_tooth_pins_log` carries no `AccountsWF` and no
`FiniteRepresentable` obligation, because the receipt-log limb of the rotated commit is a plain
sponge over the log, not the finite-support kernel frame.

⚑ **BREAKING (2026-08-01), and why.** `logChained_of_verified_or_collides` / `_of_noColl` previously
took the whole `SeamStruct` and ignored four fifths of it. That was not merely untidy: it made the
S3's load-bearing tooth UNSTATABLE, because no `ChainStep` in this file satisfies `AccountsWF` (see
`root_tooth_pins_kernel_unconditional_false`), so any counterexample refuting the `hno`-deleted form
had to drop the structural envelope too — leaving "hno is what excludes it" a claim about a proof
term rather than a theorem. With the hypothesis narrowed to what the proof consumes,
`logChained_of_verified_unconditional_false` refutes the `hno`-deleted `logChained_of_verified_-
of_noColl` EXACTLY, envelope intact (the headline S3 one layer up,
`RecursiveAggregation.non_omission_from_verification_of_noColl`, is a DIFFERENT statement and takes
its own tooth — `RecursiveAggregation.non_omission_from_verification_unconditional_false`).
`seamTurnMatch_of_seamStruct` re-derives the old callers; the two `⚠ BRIDGE ONLY` forms keep their
`SeamStruct` signature so nothing outside this file and `RecursiveAggregation` had to change. -/
def SeamTurnMatch : List ChainStep → Prop
  | []              => True
  | [_]             => True
  | s :: s' :: rest => s.turn = s'.turn ∧ SeamTurnMatch (s' :: rest)

/-- The structural envelope entails the turn-match arm — so every caller holding `SeamStruct` keeps
its conclusion, and the narrowing above gives up nothing. -/
theorem seamTurnMatch_of_seamStruct : ∀ steps : List ChainStep,
    SeamStruct steps → SeamTurnMatch steps
  | [], _ => trivial
  | [_], _ => trivial
  | _ :: s' :: rest, h => ⟨h.1.1, seamTurnMatch_of_seamStruct (s' :: rest) h.2⟩

/-- **⚑⚑ `logChained_of_verified_or_collides` — WHOLE-HISTORY NON-OMISSION, UNCONDITIONAL.** From the
genesis log pin, the VERIFIED root tooth, and the per-seam turn match, the receipt log chains across
the WHOLE history, OR the NAMED residual `ChainLogColl` holds at one of the chain's own seams. An
omitting node must exhibit a sponge collision at a pair this theorem names. -/
theorem logChained_of_verified_or_collides (g : RecChainedState) :
    ∀ steps : List ChainStep,
      LogGenesisPin g steps →
      ChainBound CH RH cmb compress compressN steps →
      SeamTurnMatch steps →
      LogChained g steps ∨ ChainLogColl CH RH cmb compress compressN steps
  | [], _, _, _ => Or.inl trivial
  | [_], hgen, _, _ => Or.inl ⟨hgen, trivial⟩
  | s :: s' :: rest, hgen, hbound, hmatch => by
    obtain ⟨htooth, hboundrest⟩ := hbound
    obtain ⟨hturn, hmatchrest⟩ := hmatch
    rcases root_tooth_pins_log_or_collides CH RH cmb compress compressN s s' hturn htooth with
      hseam | hc
    · rcases logChained_of_verified_or_collides s.post (s' :: rest)
          hseam.symm hboundrest hmatchrest with htail | hc
      · exact Or.inl ⟨hgen, htail⟩
      · exact Or.inr (Or.inr hc)
    · exact Or.inr (Or.inl hc)

/-- **S3** — whole-history log continuity from the PER-INSTANCE chain residual.

⚑ **WHAT `hno` COSTS AN HONEST NODE, stated here rather than in a neighbouring comment.** Unlike the
kernel leg — where `noSeamKernelColl_of_honest` refutes the residual at an honest seam for FREE, at
every hash — `¬ ChainLogColl` is a real obligation once any step's receipt log is non-empty:
`LogRootColl L L` retains its `LogFeltsColl L L` disjunct even when the two logs are EQUAL, so an
honest seam still carries "two distinct turns of that same log collide under `compressN`".
`seamLogColl_fires_at_honest_seam_with_colliding_log` EXHIBITS an honest seam, between two genuine
executor steps, where the residual holds. The discharge is `noChainLogColl_of_honest`: every seam
honest, plus at each step the FINITE self-collision check over the `|log|²` receipt pairs that step
already holds. That check is per-instance and decidable — it is a price, not a floor — but it is not
zero, and `noSeamLogColl_of_honest_nil` is the only corner where it is.

⚑ **AND `hno` IS LOAD-BEARING, exactly.** Delete it and this theorem is FALSE at the same envelope —
`logChained_of_verified_unconditional_false`, on a two-step chain that satisfies `LogGenesisPin`,
`ChainBound` and `SeamTurnMatch` and still DROPS a receipt, with `chainLogColl_fires_at_the_omitting_-
chain` firing at that witness. Nothing is dropped alongside `hno` in that refutation (which is why
the hypothesis is `SeamTurnMatch` and not `SeamStruct` — see the note on `SeamTurnMatch`). -/
theorem logChained_of_verified_of_noColl (g : RecChainedState) (steps : List ChainStep)
    (hgen : LogGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hmatch : SeamTurnMatch steps)
    (hno : ¬ ChainLogColl CH RH cmb compress compressN steps) :
    LogChained g steps :=
  (logChained_of_verified_or_collides CH RH cmb compress compressN g steps hgen hbound
    hmatch).resolve_right hno

/-- The log-chain residual cashes out as a bare sponge existential (⚠ loses the seam). -/
theorem ChainLogColl.toSponge : ∀ {steps : List ChainStep},
    ChainLogColl CH RH cmb compress compressN steps → SpongeCollision compressN
  | [], h => False.elim h
  | [_], h => False.elim h
  | _ :: s' :: rest, h => by
    rcases h with hc | hrest
    · exact SeamLogColl.toSponge CH RH cmb compress compressN hc
    · exact ChainLogColl.toSponge (steps := s' :: rest) hrest

/-- ⚠ **BRIDGE ONLY (2026-08-01).** Re-derived from the port.
`logChained_of_verified_or_collides` is the form that discriminates. Keeps the wider `SeamStruct`
hypothesis (adapted through `seamTurnMatch_of_seamStruct`) so its external callers are unaffected. -/
theorem logChained_of_verified_orBreak (g : RecChainedState) (steps : List ChainStep)
    (hgen : LogGenesisPin g steps)
    (hbound : ChainBound CH RH cmb compress compressN steps)
    (hstruct : SeamStruct steps) :
    OrBreak (SpongeCollision compressN) (LogChained g steps) :=
  Or.imp_right (ChainLogColl.toSponge CH RH cmb compress compressN)
    (logChained_of_verified_or_collides CH RH cmb compress compressN g steps hgen hbound
      (seamTurnMatch_of_seamStruct steps hstruct))

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

/-! ## 7b. ⚑⚑ TEETH FOR THE PER-INSTANCE RESIDUALS — SATISFIABLE, REFUTABLE, LOAD-BEARING.

These are the three discriminations the free-disjunct form provably CANNOT make: at deployed
parameters `OrBreak (StateBreakP …) P` and `OrBreak (SpongeCollision …) P` are literally `True`
(`StateCommitReduce.orBreak_stateBreakP_iff_True`, `SpongeCollisionShirk.orBreak_spongeCollision_-
iff_True`), so nothing about them is satisfiable-but-not-provable and no hypothesis of theirs can be
load-bearing. -/

/-- **TOOTH (SATISFIABLE, AT EVERY HASH).** At an HONEST seam — the post-state genuinely IS the next
pre-state — the kernel seam residual is REFUTED outright, for every choice of the five portal
functions (no injective one need be picked). So `¬ SeamKernelColl` is inhabited. -/
theorem noSeamKernelColl_of_honest (s s' : ChainStep) (hst : s.post = s'.pre) :
    ¬ SeamKernelColl CH RH cmb compress compressN s s' := by
  rintro (hsp | hk)
  · exact hsp.1 (by rw [hst])
  · rw [hst] at hk
    exact noRecStateCommitColl_diag CH RH cmb compress compressN s'.pre.kernel s'.turn hk

/-- **⚑⚑ TOOTH (DISCHARGEABLE) — the log leg, and THE HONEST NODE'S ACTUAL PRICE, stated as a
theorem rather than as a comment.** At an honest seam the log residual reduces to exactly ONE
obligation, and — unlike the kernel leg's — it is NOT free: the node must know that no two turns of
its OWN receipt log collide under the deployed sponge. Given that, `¬ SeamLogColl` follows at every
choice of the five portal functions.

⚑ The asymmetry, precisely: `LogRootColl L L'` keeps its `LogFeltsColl L L'` disjunct even when the
two logs are EQUAL, so at `L = L' = s'.pre.log` the honest seam still carries "two distinct turns of
that same log collide under `compressN`". A diagonal argument cannot discharge that once the log is
non-empty — `seamLogColl_fires_at_honest_seam_with_colliding_log` below EXHIBITS an honest seam,
between two genuine executor steps, where the residual FIRES. What makes it payable rather than a
floor in disguise is that it is a FINITE check over the `|log|²` pairs the node already holds, not a
quantification over all inputs; `noSeamLogColl_of_honest_nil` is the `|log| = 0` corner where the
price is zero. (This is the log leg's analogue of `AccountsCommit.accountsResid_dischargeable`, which
by contrast costs the honest prover nothing at all.) -/
theorem noSeamLogColl_of_honest_of_noSelfColl (s s' : ChainStep) (hst : s.post = s'.pre)
    (hself : ¬ LogFeltsColl compressN s'.pre.log s'.pre.log) :
    ¬ SeamLogColl CH RH cmb compress compressN s s' := by
  rintro (hsp | hl)
  · exact hsp.1 (by rw [hst])
  · rw [hst] at hl
    rcases hl with ⟨hne, -⟩ | hfl
    · exact hne rfl
    · exact hself hfl

/-- **TOOTH (SATISFIABLE, AT EVERY HASH) — log leg, the zero-price corner.** At an honest seam over
an EMPTY receipt log the log residual is refuted at every hash — the `|log| = 0` instance of
`noSeamLogColl_of_honest_of_noSelfColl`, where the self-collision obligation is vacuous. ⚠ This is
the ONLY corner where the log leg is free; see the dischargeable theorem above for the general
price. -/
theorem noSeamLogColl_of_honest_nil (s s' : ChainStep) (hst : s.post = s'.pre)
    (hnil : s'.pre.log = []) : ¬ SeamLogColl CH RH cmb compress compressN s s' :=
  noSeamLogColl_of_honest_of_noSelfColl CH RH cmb compress compressN s s' hst
    (by rw [hnil]; rintro ⟨t, ht, -⟩; exact absurd ht (by simp))

/-- **WHERE THE HONEST PRICE STARTS.** A receipt log holding at most ONE turn cannot self-collide:
`LogFeltsColl L L` needs two members of `L` with DISTINCT receipt-felt encodings, and a
zero-or-one-element list has no such pair — at every sponge. So the self-collision obligation of
`noSeamLogColl_of_honest_of_noSelfColl` is free up to one receipt and starts costing at two, which is
exactly where `seamLogColl_fires_at_honest_seam_with_colliding_log` lives. -/
theorem noLogFeltsColl_self_of_short : ∀ L : List Dregg2.Exec.Turn, L.length ≤ 1 →
    ¬ LogFeltsColl compressN L L
  | [], _ => by rintro ⟨t, ht, -⟩; exact absurd ht (by simp)
  | [_], _ => by
      rintro ⟨t, ht, t', ht', hne, -⟩
      rw [List.mem_singleton.mp ht, List.mem_singleton.mp ht'] at hne
      exact hne rfl
  | _ :: _ :: _, h => by simp at h

/-- **⚑ TOOTH (DISCHARGEABLE, CHAIN LEVEL) — the price `non_omission_from_verification_of_noColl`
actually charges.** The S3 of the whole-history non-omission headline carries `¬ ChainLogColl`, not
`¬ SeamLogColl`; this is what an honest node pays to discharge it. Every seam of the chain honest
(`s.post = s'.pre` along the list) plus, at every step, the finite self-collision check on that
step's own pre-log, refutes the chain residual outright — at every choice of the five portal
functions, no injective one need be picked. -/
theorem noChainLogColl_of_honest : ∀ steps : List ChainStep,
    List.IsChain (fun s s' => s.post = s'.pre) steps →
    (∀ s ∈ steps, ¬ LogFeltsColl compressN s.pre.log s.pre.log) →
    ¬ ChainLogColl CH RH cmb compress compressN steps
  | [], _, _ => fun h => h
  | [_], _, _ => fun h => h
  | s :: s' :: rest, hch, hself => by
    rintro (hc | hrest)
    · exact noSeamLogColl_of_honest_of_noSelfColl CH RH cmb compress compressN s s'
        (List.isChain_cons_cons.mp hch).1 (hself s' (by simp)) hc
    · exact noChainLogColl_of_honest (s' :: rest) (List.isChain_cons_cons.mp hch).2
        (fun x hx => hself x (List.mem_cons_of_mem s hx)) hrest

/-- A SECOND genuine executor step, from a genesis holding `500`. Needed by the chain-level tooth:
every chain built from `honestStep` alone starts AND ends at total `100`, so no such chain can
witness a conservation break — the break lives at a seam that JUMPS between supplies. -/
def richGenesis : RecChainedState where
  kernel :=
    { accounts := {0, 1}
    , cell := fun c => if c = 0 then .record [("balance", .int 500)]
                       else .record [("balance", .int 0)]
    , caps := fun _ => [] }
  log := []

/-- The rich honest step: cell `0` transfers `10` to cell `1` out of a supply of `500`. -/
def richStep : ChainStep where
  pre := richGenesis
  turn := honestTurn
  post := (recCexec richGenesis honestTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- **TOOTH (REFUTABLE — the residual FIRES).** At the all-constant portal, on a seam whose two
kernels genuinely differ, `SeamKernelColl` HOLDS: the leaf hash maps two distinct cell `Value`s
together, which the residual sees through its `MovedColl` disjunct. So `¬ SeamKernelColl` is not a
tautology — a lossy hash is CAUGHT at this seam, not defined away. -/
theorem seamKernelColl_refutable :
    SeamKernelColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) honestStep richStep := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, rfl⟩)))))
  intro h
  exact absurd (congrArg Dregg2.Exec.balOf h) (by decide)

/-- **⚑ TOOTH (REFUTABLE, AT THE DIAGONAL SEAM) — the residual fires at the witness that refutes the
kernel tooth.** `root_tooth_pins_kernel_unconditional_false` below refutes the `hno`-deleted kernel
recovery at the seam `(honestStep, honestStep)` — a step against ITSELF, whose post-kernel (cell `0`
holds `90`) and pre-kernel (`100`) differ while the constant portal pins their roots. The residual
FIRES at exactly that seam, through the same `MovedColl` leaf disjunct as
`seamKernelColl_refutable`. ⚑ This is the theorem the load-bearing claim needs: `seamKernelColl_-
refutable` fires at `(honestStep, richStep)`, which is NOT the counterexample, so citing it there
would leave the discrimination unproved at the pair that matters. -/
theorem seamKernelColl_fires_at_the_diagonal_seam :
    SeamKernelColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) honestStep honestStep := by
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, rfl⟩)))))
  intro h
  exact absurd (congrArg Dregg2.Exec.balOf h) (by decide)

/-- **⚑ TOOTH (REFUTABLE, AT THE DIAGONAL SEAM) — the commitment-level twin.** The same service for
`root_tooth_pins_state_unconditional_false`, whose counterexample is the diagonal seam at the
`CH := balOf`, `compress := snd` portal: the two cell-digests differ (`10` vs `0`) while the constant
root combiner `cmb` maps them together, which is exactly the `CompressColl cmb` disjunct
`SeamStateColl` names. So the commitment-level residual, too, excludes its own counterexample. -/
theorem seamStateColl_fires_at_the_diagonal_seam :
    SeamStateColl (fun _ v => Dregg2.Exec.balOf v) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ b => b) (fun _ => (0 : ℤ)) honestStep honestStep :=
  Or.inr ⟨fun h => absurd h.1 (by decide), rfl⟩

/-- **TOOTH (NOT PROVABLE).** Since some instantiation satisfies the seam residual, `¬ SeamKernelColl`
is not a schema true of every portal/seam choice — a genuine per-instance obligation, discharged case
by case, never a floor in disguise. -/
theorem noSeamKernelColl_not_provable :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (s s' : ChainStep),
      ¬ SeamKernelColl CH RH cmb compress compressN s s' :=
  fun h => h _ _ _ _ _ honestStep richStep seamKernelColl_refutable

/-! ### The LOG leg's teeth. `ChainLogColl` is the residual of the second headline S3
(`RecursiveAggregation.non_omission_from_verification_of_noColl`); it had none of the three
discriminations `ChainKernelColl` carries, which is what the audit of 2026-08-01 found. Built here:
REFUTABLE at a lossy sponge, NOT PROVABLE, LOAD-BEARING at the chain level, and FIRING at exactly the
witness that refutes the residual-free statement. -/

/-- **⚑ TOOTH (REFUTABLE, AT THE DIAGONAL SEAM) — the log leg.** At the all-constant sponge the log
seam residual FIRES at the DIAGONAL seam `(honestStep, honestStep)` — the very witness that refutes
`root_tooth_pins_log_unconditional_false`. The step's post-log carries the receipt it just recorded
while its own pre-log does not, so the two receipt-felt lists differ; the constant sponge maps them
together, which `LogRootColl`'s first disjunct sees. So `¬ SeamLogColl` is not a tautology — a lossy
sponge is CAUGHT at this seam, and the omission the keystone claims to catch is exactly what the
residual excludes. -/
theorem seamLogColl_fires_at_the_diagonal_seam :
    SeamLogColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) honestStep honestStep := by
  refine Or.inr (Or.inl ⟨?_, rfl⟩)
  intro h
  have hlen : honestStep.post.log.length = honestStep.pre.log.length := by
    simpa [logFelts] using congrArg List.length h
  exact absurd hlen (by decide)

/-- **TOOTH (NOT PROVABLE) — the log leg.** Since some instantiation satisfies the log seam residual,
`¬ SeamLogColl` is not a schema true of every portal/seam choice: a genuine per-instance obligation,
never `compressNInjective` in disguise. -/
theorem noSeamLogColl_not_provable :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (s s' : ChainStep),
      ¬ SeamLogColl CH RH cmb compress compressN s s' :=
  fun h => h _ _ _ _ _ honestStep honestStep seamLogColl_fires_at_the_diagonal_seam

/-- A SECOND genuine turn, distinct from `honestTurn` in its amount (`40` against `10`) — so a log
holding both carries two turns with DIFFERENT receipt-felt encodings. (Structurally the same shape as
`ConsensusExec.tamperedTurn`; named separately here because nothing about it is an attack — it is an
ordinary second transfer, used only to reach a two-receipt log.) -/
def secondTurn : Dregg2.Exec.Turn := { actor := 0, src := 0, dst := 1, amt := 40 }

/-- The second genuine executor step: from `honestStep`'s post-state, cell `0` transfers a further
`40` to cell `1`. Its post-log is `[secondTurn, honestTurn]` — the first log in this file with two
DISTINCT receipts, which is what the honest-price tooth needs. -/
def honestLogStep2 : ChainStep where
  pre := honestStep.post
  turn := secondTurn
  post := (recCexec honestStep.post secondTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- A third genuine executor step, continuing from `honestLogStep2`'s post-state. Exists so that
`(honestLogStep2, honestLogStep3)` is an HONEST seam — `honestLogStep2.post = honestLogStep3.pre` by
`rfl` — whose shared log already holds two distinct receipts. -/
def honestLogStep3 : ChainStep where
  pre := honestLogStep2.post
  turn := honestTurn
  post := (recCexec honestLogStep2.post honestTurn).get (by decide)
  commits := (Option.some_get _).symm

/-- **⚑⚑ TOOTH (THE HONEST OBLIGATION IS REAL — the log residual FIRES AT AN HONEST SEAM).** The
seam `(honestLogStep2, honestLogStep3)` is honest: the post-state genuinely IS the next pre-state,
both built by the verified executor. Yet at the constant sponge `SeamLogColl` HOLDS, through
`LogFeltsColl`'s "two turns of that log collide" disjunct at the named pair
`(secondTurn, honestTurn)`.

⚑ This is the theorem the comment on `noSeamLogColl_of_honest_nil` used to assert and nothing
proved: `¬ SeamLogColl` is NOT free for an honest prover once the receipt log is non-empty, so
`noSeamKernelColl_of_honest`'s "at EVERY hash, no hypothesis" shape has NO log-leg analogue. What the
honest node pays instead is `noSeamLogColl_of_honest_of_noSelfColl`'s finite self-collision check —
and the hypothesis there is NOT removable, because this witness satisfies everything else. -/
theorem seamLogColl_fires_at_honest_seam_with_colliding_log :
    SeamLogColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) honestLogStep2 honestLogStep3 := by
  refine Or.inr (Or.inr ⟨secondTurn, ?_, honestTurn, ?_, ?_, rfl⟩)
  · rw [show honestLogStep2.post.log = [secondTurn, honestTurn] from rfl]; simp
  · rw [show honestLogStep3.pre.log = [secondTurn, honestTurn] from rfl]; simp
  · decide

/-- **⚑ TOOTH (THE DISCHARGE IS REACHABLE — `noChainLogColl_of_honest` is not vacuous).** Its two
hypotheses are jointly satisfiable on a REAL chain: the two-step honest chain
`[honestStep, honestLogStep2]` (genuine executor steps, the second consuming the first's post-state)
meets both at EVERY choice of the five portal functions, so the chain residual is refuted there with
no injective hash picked. Without this, the dischargeability theorem could have been true of an empty
hypothesis set — the exact vacuity this campaign is about. -/
theorem noChainLogColl_at_the_honest_two_step_chain :
    ¬ ChainLogColl CH RH cmb compress compressN [honestStep, honestLogStep2] :=
  noChainLogColl_of_honest CH RH cmb compress compressN [honestStep, honestLogStep2]
    (List.isChain_pair.mpr rfl)
    (by
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact noLogFeltsColl_self_of_short compressN _ (by decide)
      · rcases List.mem_cons.mp hs with rfl | hs
        · exact noLogFeltsColl_self_of_short compressN _ (by decide)
        · exact absurd hs (by simp))

/-- **⚑⚑ TOOTH (LOAD-BEARING) — the log seam residual, at FULL strength.** `root_tooth_pins_log_-
of_noColl` with `hno` DELETED is FALSE — and nothing else was dropped, because that theorem carries
no structural side conditions beyond the turn-match. At the constant sponge two genuine executor
steps share a root while their receipt logs differ by exactly the receipt one of them recorded, which
is the omission the keystone claims to catch. (The dual reading: delete nothing from
`root_tooth_pins_log_orBreak` and it is STILL `True`.) The companion that identifies `hno` as the
side condition excluding THIS counterexample is `seamLogColl_fires_at_the_diagonal_seam`, at the same
seam and the same portal. -/
theorem root_tooth_pins_log_unconditional_false :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (s s' : ChainStep),
        s.turn = s'.turn →
        ChainStep.newRoot CH RH cmb compress compressN s
          = ChainStep.oldRoot CH RH cmb compress compressN s' →
        s.post.log = s'.pre.log := by
  intro hall
  have h := hall (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
    (fun _ => (0 : ℤ)) honestStep honestStep rfl rfl
  exact absurd (congrArg List.length h) (by decide)

/-- **⚑ TOOTH (LOAD-BEARING) — the kernel seam residual.** `root_tooth_pins_kernel_of_noColl` with
`hno` deleted is FALSE: at the constant portal a step's post-kernel and its own pre-kernel share a
root while their cell-`0` balances differ (`90` vs `100`).

⚠ **Stated precisely:** this drops the structural envelope (`RestHashIffFrameFin`, `AccountsWF`,
`FiniteRepresentable`) ALONG WITH `hno`, because a `ChainStep` carries a real `recCexec` witness and
the only such witnesses in this file run over `teethGenesis`, which is not `AccountsWF` (its dead
cells hold `.record [("balance", .int 0)]`, not the kernel default) and not a `denote` image. What
identifies `hno` as the load-bearing one is the companion `seamKernelColl_fires_at_the_diagonal_seam`
— the residual FIRES at exactly THIS witness `(honestStep, honestStep)`, so it is the side condition
that excludes the counterexample. (⚠ `seamKernelColl_refutable` fires at `(honestStep, richStep)`, a
DIFFERENT seam; it establishes refutability in general but says nothing about this counterexample.)
Building an `AccountsWF`-and-`FiniteRepresentable` `ChainStep` pair (a `FinKernelState`-backed genesis
plus a representability proof for the post-transfer cell map) is the named, unported strengthening. -/
theorem root_tooth_pins_kernel_unconditional_false :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (s s' : ChainStep),
        s.turn = s'.turn →
        ChainStep.newRoot CH RH cmb compress compressN s
          = ChainStep.oldRoot CH RH cmb compress compressN s' →
        s.post.kernel = s'.pre.kernel := by
  intro hall
  have h := hall (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
    (fun _ => (0 : ℤ)) honestStep honestStep rfl rfl
  exact absurd (congrArg (fun k => Dregg2.Exec.balOf (k.cell 0)) h) (by decide)

/-- **⚑ TOOTH (LOAD-BEARING) — the commitment-level seam residual.** `root_tooth_pins_state_of_noColl`
with `hno` deleted is FALSE at a portal that is NOT constant in the leaf/node layer: with
`CH := balOf`, `compress := snd` and a constant outer sponge the tooth still holds by `rfl` while the
two cell-digests differ (`10` vs `0`). Same precise caveat as above about the structural envelope,
which this theorem does not carry at all. The companion that identifies `hno` as the side condition
excluding THIS counterexample is `seamStateColl_fires_at_the_diagonal_seam`, at the same seam and the
same portal. -/
theorem root_tooth_pins_state_unconditional_false :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (s s' : ChainStep),
        s.turn = s'.turn →
        ChainStep.newRoot CH RH cmb compress compressN s
          = ChainStep.oldRoot CH RH cmb compress compressN s' →
        cellDigest CH compress compressN s.post.kernel s'.turn
          = cellDigest CH compress compressN s'.pre.kernel s'.turn := by
  intro hall
  have h := hall (fun _ v => Dregg2.Exec.balOf v) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
    (fun _ b => b) (fun _ => (0 : ℤ)) honestStep honestStep rfl rfl
  exact absurd h (by decide)

/-- **⚑⚑ TOOTH (LOAD-BEARING) — the CHAIN-LEVEL residual, on the conservation headline.**
`verified_history_conserves_of_noColl` with `hno` deleted is FALSE: at the constant portal the
two-step chain `[honestStep, richStep]` satisfies the genesis pin AND the verified root tooth, yet
its endpoint total is `500` against a genesis total of `100` — value MINTED across a seam the roots
did not pin. This is exactly the attack the headline claims to exclude, and `ChainKernelColl` is what
excludes it (`chainKernelColl_fires_at_the_minting_chain` below, at the SAME witness).

⚠ Same precise caveat as `root_tooth_pins_kernel_unconditional_false`: `SeamStruct` is dropped along
with `hno` for the same `ChainStep`-constructibility reason, and the companion firing theorem is what
identifies `hno` as the side condition doing the work.

⚠ **Scope.** This refutes `verified_history_conserves_of_noColl`, whose hypothesis is `ChainBound`
DIRECTLY — NOT the headline S3 `RecursiveAggregation.conserves_from_verification_of_noColl`, which
replaces `ChainBound` with the strictly stronger `es : EngineSound …` + `hroot`. That one's tooth is
`RecursiveAggregation.conserves_from_verification_unconditional_false`, which carries the engine
soundness explicitly (`RecursiveAggregation.minting_engine_sound`: a verifying aggregate genuinely
attests this minting chain, so verification is not what excludes the mint). -/
theorem verified_history_conserves_unconditional_false :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (g : RecChainedState) (steps : List ChainStep),
        KernelGenesisPin g steps →
        ChainBound CH RH cmb compress compressN steps →
        recTotal (lastStateOf g steps).kernel = recTotal g.kernel := by
  intro hall
  have h := hall (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
    (fun _ => (0 : ℤ)) teethGenesis [honestStep, richStep] rfl ⟨rfl, trivial⟩
  exact absurd h (by decide)

/-- **⚑ THE RESIDUAL COVERS THE MINTING CHAIN.** The chain-level residual FIRES at exactly the
witness that refutes the `hno`-deleted conservation headline — so the ported theorem is not merely
narrower, it is narrower *precisely where the unported one is false*. -/
theorem chainKernelColl_fires_at_the_minting_chain :
    ChainKernelColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) [honestStep, richStep] :=
  Or.inl seamKernelColl_refutable

/-- **⚑⚑ TOOTH (LOAD-BEARING) — the CHAIN-LEVEL LOG residual, on the NON-OMISSION headline.**
`logChained_of_verified_of_noColl` with `hno` DELETED is FALSE: at the constant portal the two-step
chain `[honestStep, honestStep]` satisfies the genesis LOG pin AND the verified root tooth AND the
per-seam turn match, yet its second step's pre-log is EMPTY while its first step's post-log holds the
receipt that step recorded — a receipt DROPPED across a seam the roots did not pin. That is exactly
the omission the headline claims to exclude, and `ChainLogColl` is what excludes it
(`chainLogColl_fires_at_the_omitting_chain` below, at the SAME witness).

⚑ **NOTHING IS DROPPED ALONGSIDE `hno`.** The hypotheses here are, verbatim, the other three of
`logChained_of_verified_of_noColl`; the witness satisfies all of them. This is the discrimination the
kernel-leg teeth (`root_tooth_pins_kernel_unconditional_false`,
`verified_history_conserves_unconditional_false`) still cannot make, because they must shed
`AccountsWF`/`FiniteRepresentable` to have a witness at all — which is why the log S3's hypothesis
was narrowed to `SeamTurnMatch` rather than a caveat being written.

⚠ **AND IT STOPS HERE. This theorem does NOT refute
`RecursiveAggregation.non_omission_from_verification_of_noColl`** — the headline S3 — with `hno`
deleted, and an earlier draft of this docstring said "hence" it did. That S3 replaces `ChainBound`
with `es : EngineSound …` and `hroot : verify agg.root = true`, a STRICTLY STRONGER hypothesis set
(it delivers `ChainBound` and four public pins besides), and refuting a weaker-hypothesis statement
establishes nothing about a stronger one. The theorem that does refute it, at its own hypotheses, is
`RecursiveAggregation.non_omission_from_verification_unconditional_false`, which carries the engine
soundness explicitly (`RecursiveAggregation.omitting_engine_sound`: a verifying aggregate genuinely
attests this omitting chain). -/
theorem logChained_of_verified_unconditional_false :
    ¬ ∀ (CH : Dregg2.Exec.CellId → Dregg2.Exec.Value → ℤ)
        (RH : Dregg2.Exec.RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
        (compressN : List ℤ → ℤ) (g : RecChainedState) (steps : List ChainStep),
        LogGenesisPin g steps →
        ChainBound CH RH cmb compress compressN steps →
        SeamTurnMatch steps →
        LogChained g steps := by
  intro hall
  have h := hall (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
    (fun _ => (0 : ℤ)) teethGenesis [honestStep, honestStep] rfl ⟨rfl, trivial⟩ ⟨rfl, trivial⟩
  exact absurd (congrArg List.length h.2.1) (by decide)

/-- **⚑ THE LOG RESIDUAL COVERS THE OMITTING CHAIN.** The chain-level log residual FIRES at exactly
the witness that refutes the `hno`-deleted non-omission headline — so the ported theorem is not
merely narrower, it is narrower *precisely where the unported one is false*. The chain-level twin of
`chainKernelColl_fires_at_the_minting_chain`, and the third of the three discriminations
`ChainLogColl` was missing. -/
theorem chainLogColl_fires_at_the_omitting_chain :
    ChainLogColl (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) (fun _ _ => (0 : ℤ))
      (fun _ _ => (0 : ℤ)) (fun _ => (0 : ℤ)) [honestStep, honestStep] :=
  Or.inl seamLogColl_fires_at_the_diagonal_seam

end Portal

/-! ## 8. Axiom hygiene. -/

-- ⚑⚑ THE PER-INSTANCE PORT (2026-08-01) — the statements that DISCRIMINATE at deployed parameters.
#assert_axioms Dregg2.Distributed.HistoryAggregation.receiptFelts_injective
#assert_axioms Dregg2.Distributed.HistoryAggregation.turnReceipt_binds_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.logFelts_binds_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.logRoot_binds_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.logRoot_binds_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_log_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_log_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_of_verified_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.kernelChained_of_verified_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves_of_noColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamTurnMatch_of_seamStruct
#assert_axioms Dregg2.Distributed.HistoryAggregation.logChained_of_verified_or_collides
#assert_axioms Dregg2.Distributed.HistoryAggregation.logChained_of_verified_of_noColl
-- teeth: SATISFIABLE / REFUTABLE / NOT PROVABLE / LOAD-BEARING.
#assert_axioms Dregg2.Distributed.HistoryAggregation.noSeamKernelColl_of_honest
#assert_axioms Dregg2.Distributed.HistoryAggregation.noSeamLogColl_of_honest_of_noSelfColl
#assert_axioms Dregg2.Distributed.HistoryAggregation.noSeamLogColl_of_honest_nil
#assert_axioms Dregg2.Distributed.HistoryAggregation.noLogFeltsColl_self_of_short
#assert_axioms Dregg2.Distributed.HistoryAggregation.noChainLogColl_of_honest
#assert_axioms Dregg2.Distributed.HistoryAggregation.noChainLogColl_at_the_honest_two_step_chain
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamKernelColl_refutable
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamKernelColl_fires_at_the_diagonal_seam
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamStateColl_fires_at_the_diagonal_seam
#assert_axioms Dregg2.Distributed.HistoryAggregation.noSeamKernelColl_not_provable
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_log_unconditional_false
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_kernel_unconditional_false
#assert_axioms Dregg2.Distributed.HistoryAggregation.root_tooth_pins_state_unconditional_false
#assert_axioms Dregg2.Distributed.HistoryAggregation.verified_history_conserves_unconditional_false
#assert_axioms Dregg2.Distributed.HistoryAggregation.chainKernelColl_fires_at_the_minting_chain
-- ⚑ the LOG leg's teeth (2026-08-01): `ChainLogColl` had NONE of the three before this.
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamLogColl_fires_at_the_diagonal_seam
#assert_axioms Dregg2.Distributed.HistoryAggregation.noSeamLogColl_not_provable
#assert_axioms Dregg2.Distributed.HistoryAggregation.seamLogColl_fires_at_honest_seam_with_colliding_log
#assert_axioms Dregg2.Distributed.HistoryAggregation.logChained_of_verified_unconditional_false
#assert_axioms Dregg2.Distributed.HistoryAggregation.chainLogColl_fires_at_the_omitting_chain

-- ⚠ BRIDGE ONLY (the free-disjunct twins of 2026-08-01, retained and re-derived through the port).
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
