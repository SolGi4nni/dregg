/-
# Dregg2.Circuit.Argus.Guard — the Argus GUARD layer: a `witnessed` guard and a circuit
obligation are the SAME mechanism.

This file welds three things that already exist into one term-level object:

  * `Dregg2.Spec.Guard` — the abstract `Guard Request Statement` (`firstParty`/`witnessed`/`all`/
    `any`/`gnot`), `Guard.admits`, and `attenuate_narrows` (attenuation = the meet-semilattice law).
  * `Dregg2.Exec.PredAlgebra` — the `Pred` Boolean algebra + `Pred.eval`, and the `predStateStepGuarded`
    *domain-restriction* keystone `predStateStepGuarded_eq` (a gated write = the underlying `stateStep`
    write — the gate only restricts the domain, never mutates).
  * `Dregg2.Circuit.Argus.Stmt` (the cornerstone) — `RecStmt` with the `guard (φ : RecordKernelState →
    Bool)` primitive, its executable `interp`, and `interp_transferStmt_eq_recKExec`.

## The thesis

The cornerstone already has ONE gate primitive: `RecStmt.guard (φ : RecordKernelState → Bool)`. Its
`interp` clause is `if φ k then some k else none` — a pure **domain restrictor**: it returns the state
*unchanged* on admit, `none` on reject. So a `Spec.Guard` (the unified authorization / precondition /
state-constraint / caveat object) and a circuit obligation are the same mechanism the moment we LIFT
the guard's `admits` into `φ`. That lift is `guardG` (§1), and it REUSES `Spec.Guard.admits` verbatim
— it is the existing predicate/guard language, not a new one.

The payoff is the **domain-restriction keystone** (§2, `interp_guardSeq_*`): for a guarded statement
`RecStmt.seq (guardG g …) s`, `interp` commits *iff* the guard admits AND `interp s` commits, and the
committed state is EXACTLY `interp s`'s. This is the analog of `predStateStepGuarded_eq`: the Argus
guard only restricts, never mutates — so every executor keystone proved of `interp s` (conservation,
authority, frame) lifts through the guard FOR FREE.

## Bucket-B (§4)

dregg1's `StateConstraint` catalog (`Exec/Program.lean`, ~19 variants) is `evalConstraint`-evaluated
on the LIVE leg, but the *circuit* path has historically dropped them. `constraintToGuard` routes each
constraint onto the unified `Guard`:

  * **locally-decidable** constraints (`sumEquals`, `affineLe/Eq`, `fieldDeltaInRange`,
    `allowedTransitions`, every `simple` atom, …) become `firstParty` over `evalConstraint` — they
    EVALUATE now, with no external evidence (`constraintToGuard_firstParty_eval` proves the lift IS
    `evalConstraint`);
  * **circuit-discharged / cross-cell** constraints (`boundDelta`, the bilateral conservation that the
    single-cell `evalConstraint` fails-closed on) become `witnessed (.constraint c)` — a verify-seam
    obligation NAMING the future circuit, routed through `Spec.Guard.witnessed` (no faked circuit; the
    obligation EXISTS as a `Statement` and is discharged by the §8 oracle when one is supplied).

`#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}); pure, computable, `#guard`-able.
-/
import Dregg2.Circuit.Argus.Stmt
import Dregg2.Spec.Guard
import Dregg2.Exec.PredAlgebra

namespace Dregg2.Circuit.Argus

open Dregg2.Exec
open Dregg2.Spec (Guard)
open Dregg2.Laws (Verifiable Discharged)

/-! ## §0 — The obligation statement: what a `witnessed` guard NAMES.

The cornerstone's `RecStmt.guard` reads a `RecordKernelState`, so the Argus guard's **request** is the
kernel itself (`Request := RecordKernelState`) — the cleanest faithful decode is the identity (the gate
already sees the whole state). The **statement** a `witnessed` guard discharges names a verify-seam
obligation. We give it the smallest honest shape: a sum of "this `StateConstraint` is discharged by a
circuit" plus an opaque escape for a named obligation hash. This is the SINGLE site where a future
circuit enters — `Verifiable.Verify` against a supplied witness, never a faked in-Lean proof. -/

/-- **`ObligationStmt`** — the verify-seam claim an Argus `witnessed` guard discharges. It NAMES a
circuit obligation; it does not pretend to discharge one. Two shapes:

* `constraint c` — "the `StateConstraint c` holds of this transition, proved by its circuit" (the
  future-circuit arms of Bucket-B: cross-cell `boundDelta`, opaque AIR, …);
* `named h` — an opaque obligation identified by a hash (a Merkle membership, a Pedersen range proof, …
  — the eight dregg1 verifier kinds live here as `Verifiable` instances behind the seam).

The crypto content is the §8 portal: `Verifiable ObligationStmt Witness` is a TYPECLASS PARAMETER, not
an `axiom`, so it never trips the axiom-hygiene guard and the metatheory commits only to "if `Verify`
says `true`, the certificate checked" — never to completeness. -/
inductive ObligationStmt where
  /-- The obligation "circuit discharges this `StateConstraint`" (Bucket-B's witnessed arms). -/
  | constraint (c : StateConstraint)
  /-- An opaque named obligation (hash-identified — Merkle / range / DFA / … behind the oracle). -/
  | named      (hash : Nat)
  deriving Repr

/-! ## §1 — `guardG`: LIFT a `Spec.Guard` into the cornerstone's `RecStmt.guard`.

The whole adapter. A `Spec.Guard RecordKernelState Statement` is the demand; `(k, w)` is the supply
(the kernel facts + the witness map); `Guard.admits g k w : Bool` evaluates it. `guardG` packages that
`Bool` into the cornerstone's gate primitive `RecStmt.guard`. NO new predicate language — this is
`Spec.Guard.admits`, the unified object, dropped onto the term IR. -/

/-- **`guardG g w`** — lift a `Spec.Guard RecordKernelState Statement` into a `RecStmt` by routing its
`admits` (under witness supply `w`) into the cornerstone's `RecStmt.guard`. The request the guard reads
IS the kernel state (`decode = id`, the tightest faithful decode — the gate already sees the whole
state). The result is a pure domain restrictor: `interp (guardG g w) k = if g.admits k w then some k
else none` (`interp_guardG`). -/
def guardG [Verifiable Statement Witness]
    (g : Guard RecordKernelState Statement) (w : Statement → Witness) : RecStmt :=
  RecStmt.guard (fun k => g.admits k w)

/-- **`interp_guardG` — the lift's executable meaning.** Running a lifted guard restricts the
domain by `g.admits` and otherwise leaves the state UNTOUCHED — exactly the cornerstone `RecStmt.guard`
semantics, now driven by the unified `Spec.Guard`. The guard DECIDES; it never mutates. -/
@[simp] theorem interp_guardG [Verifiable Statement Witness]
    (g : Guard RecordKernelState Statement) (w : Statement → Witness) (k : RecordKernelState) :
    interp (guardG g w) k = if g.admits k w then some k else none := by
  simp [guardG, interp]

/-! ## §2 — The DOMAIN-RESTRICTION keystone (the analog of `predStateStepGuarded_eq`).

For a guarded statement `RecStmt.seq (guardG g w) s`, `interp` factors cleanly: the guard restricts
the domain, then `interp s` runs UNCHANGED. The committed state is EXACTLY `interp s`'s — the Argus
guard only ever restricts, never mutates. This is what lifts every `interp s` keystone through the
guard for free. -/

/-- **`interp_guardSeq`.** Interpreting a guarded statement is: gate on `g.admits k w`, then
run `interp s` on the SAME `k`. (`interp` of a `guardG`-prefixed `seq` is the `admits`-gated `interp
s`.) The structural shape the keystones below read off. -/
theorem interp_guardSeq [Verifiable Statement Witness]
    (g : Guard RecordKernelState Statement) (w : Statement → Witness)
    (s : RecStmt) (k : RecordKernelState) :
    interp (RecStmt.seq (guardG g w) s) k
      = if g.admits k w then interp s k else none := by
  simp only [interp, interp_guardG]
  cases hg : g.admits k w with
  | false => simp [Option.bind]
  | true  => simp [Option.bind]

/-- **`interp_guardSeq_admits` (the keystone, ⇐ direction).** A guarded statement COMMITS to
`k'` exactly when the guard ADMITS *and* the underlying `interp s` commits to that very same `k'`. The
domain-restriction law: the committed state is precisely `interp s`'s — the guard contributes NO
mutation, only the admission side-condition. This is the analog of `predStateStepGuarded_eq` and is
what makes conservation / authority / frame lift through the guard verbatim. -/
theorem interp_guardSeq_admits [Verifiable Statement Witness]
    {g : Guard RecordKernelState Statement} {w : Statement → Witness}
    {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (RecStmt.seq (guardG g w) s) k = some k') :
    g.admits k w = true ∧ interp s k = some k' := by
  rw [interp_guardSeq] at h
  cases hg : g.admits k w with
  | false => rw [hg, if_neg (by simp)] at h; exact absurd h (by simp)
  | true  => rw [hg, if_pos rfl] at h; exact ⟨rfl, h⟩

/-- **`guardSeq_commit_eq_underlying` (the "never mutates" corollary).** A committed guarded
statement produces EXACTLY the post-state the underlying `interp s` produces on the same input. The
guard is a pure domain restrictor: it can only ever PREVENT the step, never alter its result. The
precise mirror of `predStateStepGuarded_eq` (`a Pred-gated write = the underlying stateStep write`). -/
theorem guardSeq_commit_eq_underlying [Verifiable Statement Witness]
    {g : Guard RecordKernelState Statement} {w : Statement → Witness}
    {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (RecStmt.seq (guardG g w) s) k = some k') :
    interp s k = some k' :=
  (interp_guardSeq_admits h).2

/-- **`interp_guardSeq_of_admits` (the keystone, ⇒ direction).** Conversely, if the guard
ADMITS and `interp s` commits to `k'`, the guarded statement commits to that same `k'`. Together with
`interp_guardSeq_admits` this is the IFF: a guarded statement commits to `k'` *iff* the guard admits
AND `interp s` commits to `k'`. -/
theorem interp_guardSeq_of_admits [Verifiable Statement Witness]
    {g : Guard RecordKernelState Statement} {w : Statement → Witness}
    {s : RecStmt} {k k' : RecordKernelState}
    (hadm : g.admits k w = true) (hs : interp s k = some k') :
    interp (RecStmt.seq (guardG g w) s) k = some k' := by
  rw [interp_guardSeq, if_pos hadm, hs]

/-- **`interp_guardSeq_iff` (the full domain-restriction keystone, packaged).** A guarded
statement commits to `k'` IFF the guard admits AND `interp s` commits to `k'` — and the committed state
is `interp s`'s, never anything the guard cooked up. The single statement that says "the Argus guard
restricts the domain, never mutates", from which the executor keystones lift. -/
theorem interp_guardSeq_iff [Verifiable Statement Witness]
    (g : Guard RecordKernelState Statement) (w : Statement → Witness)
    (s : RecStmt) (k k' : RecordKernelState) :
    interp (RecStmt.seq (guardG g w) s) k = some k'
      ↔ (g.admits k w = true ∧ interp s k = some k') :=
  ⟨interp_guardSeq_admits, fun ⟨ha, hs⟩ => interp_guardSeq_of_admits ha hs⟩

/-- **`interp_guardSeq_reject` (FAIL-CLOSED).** If the guard REJECTS, the guarded statement
does NOT commit — regardless of what `interp s` would do. The executor-level teeth: a violated Argus
guard rejects the WHOLE step. -/
theorem interp_guardSeq_reject [Verifiable Statement Witness]
    (g : Guard RecordKernelState Statement) (w : Statement → Witness)
    (s : RecStmt) (k : RecordKernelState)
    (h : g.admits k w = false) :
    interp (RecStmt.seq (guardG g w) s) k = none := by
  rw [interp_guardSeq, if_neg (by simp [h])]

/-! ### §2.1 — The keystone, CONCRETELY: conservation lifts through an Argus guard.

A demonstration that the domain-restriction keystone does what it is for: take `interp s :=
interp (transferStmt turn)` (the verified transfer, `= recKExec` by the cornerstone), prefix it with
ANY Argus guard, and conservation STILL holds of the guarded commit — proved by reading the keystone,
not by re-proving conservation. This is the "free lift" made real. -/

/-- **`guardSeq_transfer_conserves` (the keystone paying off).** A guarded transfer that
commits PRESERVES the total `balance` (conservation), inherited from `recKExec_conserves` THROUGH the
domain-restriction keystone — the Argus guard added an admission side-condition and changed NOTHING
about the committed state, so the executor keystone lifts verbatim. -/
theorem guardSeq_transfer_conserves [Verifiable Statement Witness]
    {g : Guard RecordKernelState Statement} {w : Statement → Witness}
    {turn : Turn} {k k' : RecordKernelState}
    (h : interp (RecStmt.seq (guardG g w) (transferStmt turn)) k = some k') :
    recTotal k' = recTotal k := by
  have hs : interp (transferStmt turn) k = some k' := guardSeq_commit_eq_underlying h
  rw [interp_transferStmt_eq_recKExec] at hs
  exact recKExec_conserves k k' turn hs

/-- **`guardSeq_transfer_authorized` (authority lifts too).** A guarded transfer that commits
was AUTHORIZED — `recKExec_authorized` lifted through the same keystone. Two independent executor
keystones (conservation, authority) lifting through ONE guard with no per-guard reproof: exactly the
"every executor keystone lifts for free" claim. -/
theorem guardSeq_transfer_authorized [Verifiable Statement Witness]
    {g : Guard RecordKernelState Statement} {w : Statement → Witness}
    {turn : Turn} {k k' : RecordKernelState}
    (h : interp (RecStmt.seq (guardG g w) (transferStmt turn)) k = some k') :
    authorizedB k.caps turn = true := by
  have hs : interp (transferStmt turn) k = some k' := guardSeq_commit_eq_underlying h
  rw [interp_transferStmt_eq_recKExec] at hs
  exact recKExec_authorized k k' turn hs

/-! ## §3 — NON-VACUITY: a concrete Argus guard that REJECTS a violating transition and ADMITS a valid
one, with a REAL predicate over the kernel.

We instantiate the seam with a trivial `Verifiable … Unit` (the `firstParty` arm needs no oracle to
evaluate; the witnessed arm is exercised in §4's routing). The guard is a genuine `firstParty` reading
the kernel: "cell `0` is a live account AND the nullifier set is below a cap" — a real admissibility
predicate, distinct on two concrete kernels. -/

/-- A trivial verify instance so the §3 `firstParty` examples can carry the `Verifiable Unit Unit`
class constraint `Guard.admits` demands (the `firstParty` arm ignores the witness entirely). For `Unit`
the verifier always accepts — a deliberately MINIMAL instance, only to make the examples reduce; the
real instances are the §8 oracles. -/
instance : Verifiable Unit Unit where
  Verify := fun _ _ => true

/-- A trivial verify instance for the obligation seam, so the §4 `constraintToGuard` examples can
EVALUATE the witnessed arm (`boundDelta` routes to `Verifiable.Verify` of an `ObligationStmt`). Always
accepts — MINIMAL, only to make the examples reduce; the REAL discharge is the §8 circuit oracle (a
Merkle/Pedersen/AIR `Verifiable ObligationStmt Witness` instance), never this stub. -/
instance : Verifiable ObligationStmt Unit where
  Verify := fun _ _ => true

/-- A REAL `firstParty` Argus guard over the kernel: admit iff cell `0` is a live account AND there are
fewer than `cap` spent nullifiers. A genuine state predicate (not `True`), distinct on the two kernels
below (decidable Finset membership + a `List.length` bound, both `decide`-reducible on literals). -/
def liveBoundGuard (cap : Nat) : Guard RecordKernelState Unit :=
  Guard.firstParty (fun k => decide (0 ∈ k.accounts) && decide (k.nullifiers.length < cap))

/-- A kernel with one live account and no spent nullifiers: the guard ADMITS. -/
def kGood : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("balance", .int 100)], caps := fun _ => [] }

/-- A kernel with NO live accounts: the guard REJECTS (the live-account conjunct fails). -/
def kEmpty : RecordKernelState :=
  { accounts := ∅, cell := fun _ => .record [("balance", .int 100)], caps := fun _ => [] }

-- ADMIT: `kGood` has cell 0 live and 0 < 3 nullifiers ⇒ the guard admits ⇒ the step commits.
-- (`RecordKernelState` has function fields ⇒ no `BEq`; we observe via `.isSome`/`.isNone`, and pin the
-- "leaves the state UNCHANGED" claim as the theorem `interp_guardG_kGood_unchanged` below.)
#guard ((liveBoundGuard 3).admits kGood (fun _ => ()))                                       -- true
#guard ((interp (guardG (liveBoundGuard 3) (fun _ => ())) kGood).isSome)                     -- commits
-- REJECT: `kEmpty` has no live account ⇒ the guard rejects ⇒ the step fails closed.
#guard ((liveBoundGuard 3).admits kEmpty (fun _ => ())) == false                             -- false
#guard ((interp (guardG (liveBoundGuard 3) (fun _ => ())) kEmpty).isNone)                    -- rejected

-- The non-vacuity at the proof layer (an ADMIT witness and a REJECT witness). We expand `admits`
-- through its `@[simp]` `firstParty` characterization first (`Guard.admits` is a `mutual` def whose
-- `Decidable` reduction stalls under bare `decide`; the `#guard`s above use the compiler evaluator,
-- which handles it — so both layers witness the two values).
example : (liveBoundGuard 3).admits kGood (fun _ => ()) = true := by
  simp [liveBoundGuard, kGood]
example : (liveBoundGuard 3).admits kEmpty (fun _ => ()) = false := by
  simp [liveBoundGuard, kEmpty]

/-- **`interp_guardG_kGood_unchanged` (the guard mutates NOTHING).** On the admitting kernel
`kGood`, running the lifted guard returns `kGood` UNCHANGED — the pure domain-restrictor semantics, at
a concrete state (the `BEq`-free statement of what the `.isSome` `#guard` observes). -/
theorem interp_guardG_kGood_unchanged :
    interp (guardG (liveBoundGuard 3) (fun _ => ())) kGood = some kGood := by
  rw [interp_guardG, if_pos (by simp [liveBoundGuard, kGood])]

/-- **`liveBoundGuard_nonvacuous` (the guard is two-valued).** It ADMITS `kGood`
and REJECTS `kEmpty` — so neither `:= True` nor `:= False`. A vacuous guard could not state this. -/
theorem liveBoundGuard_nonvacuous :
    (liveBoundGuard 3).admits kGood (fun _ => ()) = true ∧
      (liveBoundGuard 3).admits kEmpty (fun _ => ()) = false := by
  refine ⟨?_, ?_⟩
  · simp [liveBoundGuard, kGood]
  · simp [liveBoundGuard, kEmpty]

/-! ### §3.1 — Non-vacuity of the WHOLE guarded step (gate ∘ effect), end-to-end.

Prefix the verified transfer with `liveBoundGuard`, on a kernel where BOTH the guard admits and the
transfer commits: the guarded statement commits, and conservation holds — and on a kernel where the
guard rejects, the guarded statement fails closed even though the underlying transfer would have
committed. This exhibits the keystone live: the guard restricts the domain, nothing else. -/

/-- A two-account kernel: `0 → 1`, account `0` holds 100, both live. The transfer below commits. -/
def kPair : RecordKernelState :=
  { accounts := {0, 1},
    cell := fun c => if c = 0 then .record [("balance", .int 100)] else .record [("balance", .int 0)],
    caps := fun _ => [] }

/-- A self-authorized transfer of 30 from `0` to `1` (`actor = src = 0`, so `authorizedB` holds). -/
def tPair : Turn := { actor := 0, src := 0, dst := 1, amt := 30 }

-- The bare transfer commits on `kPair` (admissible). The Argus-guarded version ALSO commits (guard
-- admits); that its committed state is EXACTLY the transfer's is the theorem below (no `BEq` on state).
#guard ((liveBoundGuard 3).admits kPair (fun _ => ()))                                            -- true
#guard ((interp (RecStmt.seq (guardG (liveBoundGuard 3) (fun _ => ())) (transferStmt tPair)) kPair).isSome)   -- commits
#guard ((interp (transferStmt tPair) kPair).isSome)                                               -- bare transfer commits too
-- And on the empty-accounts kernel the guard fails the WHOLE step closed (even though the underlying
-- effect is the same term): the gate restricts the domain.
#guard ((interp (RecStmt.seq (guardG (liveBoundGuard 3) (fun _ => ())) (transferStmt tPair)) kEmpty).isNone)  -- gated out

/-- **`guardSeq_commit_eq_transfer_concrete` (the keystone, witnessed concretely).** On
`kPair` the Argus-guarded transfer commits to EXACTLY the same state as the bare transfer — the
domain-restriction keystone instantiated at a concrete admitting input. Non-vacuous: the underlying
`interp (transferStmt tPair) kPair` is `some _`, not `none`. -/
theorem guardSeq_commit_eq_transfer_concrete :
    interp (RecStmt.seq (guardG (liveBoundGuard 3) (fun _ => ())) (transferStmt tPair)) kPair
      = interp (transferStmt tPair) kPair := by
  rw [interp_guardSeq, if_pos (by simp [liveBoundGuard, kPair])]

/-! ## §4 — BUCKET-B: route the silently-ignored `StateConstraint` catalog onto the unified `Guard`.

dregg1's ~19-variant `StateConstraint` catalog (`Exec/Program.lean`) is `evalConstraint`-checked on the
LIVE leg, but the circuit path has dropped them. `constraintToGuard` routes EACH constraint onto the
single `Guard` object, splitting on locally-decidable vs circuit-discharged:

  * locally-decidable ⇒ `firstParty` over `evalConstraint` (evaluated NOW, no external evidence);
  * circuit-discharged / cross-cell ⇒ `witnessed (.constraint c)` (a verify-seam obligation NAMING the
    future circuit — discharged by the §8 oracle when a witness is supplied; NO faked circuit).

The request a constraint reads is the kernel; the `(old, new)` records it needs come from a supplied
view `view : RecordKernelState → Value × Value` (the live `setFieldA` leg already computes this — the
slot's committed value `old` and the proposed `new`; here it is a parameter so the routing is reusable
across effect terms). -/

/-- **`locallyDecidable c`** — does the single-cell `evalConstraint` evaluate `c` with real teeth
(rather than fail-closed because it needs peer state)? Exactly dregg1's split: every arm EXCEPT the
cross-cell `boundDelta` (which `evalConstraint` returns `false` on, awaiting the JointTurn discharge)
is locally decidable. The `boundDelta` arm is the future circuit obligation. -/
def locallyDecidable : StateConstraint → Bool
  | .boundDelta _ _ _ _ => false   -- cross-cell: needs peer state ⇒ circuit/JointTurn obligation
  | _                   => true    -- everything else evaluates locally with `evalConstraint`

/-- **`constraintToGuard view c`** — the Bucket-B router: lift a `StateConstraint` onto the unified
`Guard RecordKernelState ObligationStmt`. Locally-decidable constraints become a `firstParty` that
RUNS `evalConstraint` on the `(old, new)` view; the cross-cell `boundDelta` becomes a `witnessed
(.constraint c)` naming the circuit obligation (the §8 oracle discharges it — this file does NOT). -/
def constraintToGuard (view : RecordKernelState → Value × Value) :
    StateConstraint → Guard RecordKernelState ObligationStmt
  | .boundDelta lf p pf e =>
      -- cross-cell bilateral conservation — the single-cell evaluator fails closed; route to the seam.
      Guard.witnessed (.constraint (.boundDelta lf p pf e))
  | c =>
      -- locally decidable — evaluate `evalConstraint` on the slot view (the live-leg semantics).
      Guard.firstParty (fun k => evalConstraint c (view k).1 (view k).2)

/-- **`constraintToGuard_firstParty_eval`.** For a locally-decidable constraint, its Argus
guard `admits` IS `evalConstraint` on the view — i.e. the routing carries the live-leg semantics
verbatim, with no oracle. (`boundDelta` is excluded: it routes to `witnessed`, characterized
separately by `constraintToGuard_boundDelta_witnessed`.) -/
theorem constraintToGuard_firstParty_eval [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (c : StateConstraint)
    (hloc : locallyDecidable c = true) (k : RecordKernelState) (w : ObligationStmt → Witness) :
    (constraintToGuard view c).admits k w = evalConstraint c (view k).1 (view k).2 := by
  cases c with
  | boundDelta lf p pf e => simp [locallyDecidable] at hloc   -- excluded by `hloc`
  | _ => simp [constraintToGuard]

/-- **`constraintToGuard_boundDelta_witnessed`.** The cross-cell `boundDelta` routes to the
verify seam: its Argus guard `admits` IS `Verifiable.Verify` of the obligation against the supplied
witness — the SINGLE site where a future circuit enters. The obligation EXISTS (`.constraint
(.boundDelta …)`); it is not faked, it is routed. -/
theorem constraintToGuard_boundDelta_witnessed [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value)
    (lf : FieldName) (p : Nat) (pf : FieldName) (e : Bool)
    (k : RecordKernelState) (w : ObligationStmt → Witness) :
    (constraintToGuard view (.boundDelta lf p pf e)).admits k w
      = Verifiable.Verify (ObligationStmt.constraint (.boundDelta lf p pf e))
          (w (.constraint (.boundDelta lf p pf e))) := by
  simp [constraintToGuard]

/-- **`constraintToGuard_boundDelta_iff_discharged`.** Equivalently, the `boundDelta` Argus
guard admits IFF the seam DISCHARGES the obligation (`Laws.Discharged`) — the demand⊣supply bridge of
`Spec.Guard` reused: the Bucket-B witnessed arm is `Laws.Discharged` at the verify seam, importing the
oracle's soundness contract for free. -/
theorem constraintToGuard_boundDelta_iff_discharged [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value)
    (lf : FieldName) (p : Nat) (pf : FieldName) (e : Bool)
    (k : RecordKernelState) (w : ObligationStmt → Witness) :
    (constraintToGuard view (.boundDelta lf p pf e)).admits k w = true
      ↔ Discharged (ObligationStmt.constraint (.boundDelta lf p pf e))
          (w (.constraint (.boundDelta lf p pf e))) := by
  rw [constraintToGuard_boundDelta_witnessed]; rfl

/-! ### §4.1 — Bucket-B routing is NON-VACUOUS: locally-decidable constraints actually EVALUATE,
rejecting a violator and admitting a satisfier; and the witnessed `boundDelta` arm is the
seam, not a silent `true`/`false`.

We use the slot view `simpleView f` that reads field `f` of cell `0` as both `old` and `new` (the
single-record view; for an absolute constraint like `sumEquals`/`memberOf`/`fieldGe`, `old` is
irrelevant). The constraints below are real ones from the catalog. -/

/-- A slot view: read cell `0`'s record as both the `old` and the `new` value (the absolute-constraint
view — `old` unused by absolute atoms). Concrete, computable. -/
def cell0View (k : RecordKernelState) : Value × Value := (k.cell 0, k.cell 0)

/-- A kernel whose cell `0` carries `role = 2` (in the allowlist {1,2,3}) and `price = 150` (≤ 200). -/
def kRoleOk : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("role", .int 2), ("price", .int 150)],
    caps := fun _ => [] }

/-- A kernel whose cell `0` carries `role = 9` (NOT in {1,2,3}) — a violator of the `memberOf` policy. -/
def kRoleBad : RecordKernelState :=
  { accounts := {0}, cell := fun _ => .record [("role", .int 9), ("price", .int 150)],
    caps := fun _ => [] }

-- A locally-decidable `memberOf` constraint routed to an Argus guard EVALUATES: it ADMITS `kRoleOk`
-- (role ∈ set) and REJECTS `kRoleBad` (role ∉ set). The routing carries `evalConstraint`'s teeth.
#guard ((constraintToGuard cell0View (.simple (.memberOf "role" [1,2,3]))).admits
          kRoleOk (fun _ => ()))                                                         -- true
#guard ((constraintToGuard cell0View (.simple (.memberOf "role" [1,2,3]))).admits
          kRoleBad (fun _ => ())) == false                                              -- false

-- A `sumEquals` conservation constraint (role + price = 152) — admitted on `kRoleOk`.
#guard ((constraintToGuard cell0View (.sumEquals ["role", "price"] 152)).admits
          kRoleOk (fun _ => ()))                                                         -- true (2+150)

-- The cross-cell `boundDelta` routes to the seam: under the trivial `Verifiable Unit Unit` it reads as
-- the oracle's verdict (here `true`) — exercising the witnessed arm, NOT a silent constant.
#guard ((constraintToGuard cell0View (.boundDelta "amt" 1 "amt" true)).admits
          kRoleOk (fun _ => ()))                                                         -- true (oracle says so)

/-- **`bucketB_memberOf_nonvacuous`.** The routed `memberOf` Argus guard ADMITS the satisfier
and REJECTS the violator — two-valued, evaluating `evalConstraint`. The Bucket-B routing has
real teeth on the locally-decidable arms (not `:= True`). -/
theorem bucketB_memberOf_nonvacuous :
    (constraintToGuard cell0View (.simple (.memberOf "role" [1,2,3]))).admits kRoleOk (fun _ => ()) = true ∧
      (constraintToGuard cell0View (.simple (.memberOf "role" [1,2,3]))).admits kRoleBad (fun _ => ()) = false := by
  refine ⟨?_, ?_⟩
  · rw [constraintToGuard_firstParty_eval cell0View _ (by decide)]; decide
  · rw [constraintToGuard_firstParty_eval cell0View _ (by decide)]; decide

/-- **`bucketB_localcoincides_evalConstraint` (the routing IS the live-leg check).** At a
concrete locally-decidable constraint, the Argus guard's verdict coincides with `evalConstraint` on the
view — the Bucket-B `firstParty` arm is the EXACT live-leg semantics, demonstrated end-to-end. -/
theorem bucketB_localcoincides_evalConstraint :
    (constraintToGuard cell0View (.simple (.memberOf "role" [1,2,3]))).admits kRoleBad (fun _ => ())
      = evalConstraint (.simple (.memberOf "role" [1,2,3])) (cell0View kRoleBad).1 (cell0View kRoleBad).2 :=
  constraintToGuard_firstParty_eval cell0View (.simple (.memberOf "role" [1,2,3]))
    (by decide) kRoleBad (fun _ => ())

/-! ### §4.2 — Bucket-B as a `RecStmt` GATE: route a whole constraint LIST onto the guard term, so it
gates an effect via the §2 domain-restriction keystone.

A `RecordProgram.predicate cs` (a conjunction of constraints) becomes ONE Argus guard `all`-conjoining
each constraint's `constraintToGuard`. Conjoined onto an effect by `seq`, it gates that effect — and
the §2 keystone lifts the effect's executor properties through it for free. This is the structure that
makes the dropped `StateConstraint`s ENFORCED on the circuit path (the future-circuit arms named, the
local arms evaluated). -/

/-- **`programToGuard view cs`** — route a conjunctive constraint program onto ONE Argus guard, the
meet (`all`) of each constraint's routed guard. The unified-object analog of `RecordProgram.admits
(.predicate cs)`: each constraint is `firstParty` (local) or `witnessed` (circuit), AND-composed. -/
def programToGuard (view : RecordKernelState → Value × Value) (cs : List StateConstraint) :
    Guard RecordKernelState ObligationStmt :=
  Guard.all (cs.map (constraintToGuard view))

/-- **`programGuardStmt view cs s`** — gate the effect term `s` by the routed program guard (no
witness supply needed at construction; it is provided at `interp` time). The Bucket-B program, as a
`RecStmt`, ready to compose with any effect body. -/
def programGuardStmt [Verifiable ObligationStmt Witness]
    (view : RecordKernelState → Value × Value) (cs : List StateConstraint)
    (w : ObligationStmt → Witness) (s : RecStmt) : RecStmt :=
  RecStmt.seq (guardG (programToGuard view cs) w) s

/-- **`programGuardStmt_commit_eq_underlying` (Bucket-B inherits the keystone).** A
program-gated effect that commits produces EXACTLY the underlying `interp s` state — the routed
constraint program restricted the domain and mutated NOTHING. So every executor keystone of `s` lifts
through the WHOLE Bucket-B program for free, by the §2 domain-restriction keystone. -/
theorem programGuardStmt_commit_eq_underlying [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {cs : List StateConstraint}
    {w : ObligationStmt → Witness} {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (programGuardStmt view cs w s) k = some k') :
    interp s k = some k' :=
  guardSeq_commit_eq_underlying h

/-- **`programGuardStmt_admits_all`.** A program-gated commit means EVERY routed constraint
admitted (the meet semantics): the conjunction `all` of the routed guards held. The witness that the
whole Bucket-B program was enforced — each local constraint evaluated true, each witnessed obligation
discharged. -/
theorem programGuardStmt_admits_all [Verifiable ObligationStmt Witness]
    {view : RecordKernelState → Value × Value} {cs : List StateConstraint}
    {w : ObligationStmt → Witness} {s : RecStmt} {k k' : RecordKernelState}
    (h : interp (programGuardStmt view cs w s) k = some k') :
    ∀ c ∈ cs, (constraintToGuard view c).admits k w = true := by
  have hadm : (programToGuard view cs).admits k w = true := (interp_guardSeq_admits h).1
  unfold programToGuard at hadm
  rw [Guard.admits_all] at hadm
  intro c hc
  exact hadm _ (List.mem_map_of_mem hc)

/-! ## §5 — Axiom-hygiene tripwires.

Pin every keystone: the lift's meaning, the full domain-restriction keystone (both directions + the
"never mutates" corollary + fail-closed), the two concrete executor-property lifts, the non-vacuity
theorems, and the Bucket-B routing characterizations + program-level lifts. Each ⊆ {propext,
Classical.choice, Quot.sound} (no `sorryAx`). -/

#assert_axioms interp_guardG
#assert_axioms interp_guardSeq
#assert_axioms interp_guardSeq_admits
#assert_axioms guardSeq_commit_eq_underlying
#assert_axioms interp_guardSeq_of_admits
#assert_axioms interp_guardSeq_iff
#assert_axioms interp_guardSeq_reject
#assert_axioms guardSeq_transfer_conserves
#assert_axioms guardSeq_transfer_authorized
#assert_axioms liveBoundGuard_nonvacuous
#assert_axioms guardSeq_commit_eq_transfer_concrete
#assert_axioms constraintToGuard_firstParty_eval
#assert_axioms constraintToGuard_boundDelta_witnessed
#assert_axioms constraintToGuard_boundDelta_iff_discharged
#assert_axioms bucketB_memberOf_nonvacuous
#assert_axioms bucketB_localcoincides_evalConstraint
#assert_axioms programGuardStmt_commit_eq_underlying
#assert_axioms programGuardStmt_admits_all

end Dregg2.Circuit.Argus
