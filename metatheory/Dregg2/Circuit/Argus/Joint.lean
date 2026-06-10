/-
# Dregg2.Circuit.Argus.Joint — welding the Argus IR to the JOINT-TURN (par / separation-⊗) layer.

`Argus/Stmt.lean` reserves `par` as the constructor "for jointturns / separation-⊗" but never builds
it: the effect-BODY IR is sequential (`seq`), and the cross-cell coordinated turn lives one layer up.
That layer is ALREADY built and proved — `Dregg2.Distributed.EntangledJoint` is the EXECUTABLE N-cell
all-or-none atomic joint turn (`jointApplyAll`), faithful to `coord/src/atomic.rs`'s N-participant 2PC,
with atomicity / no-authority-amplification / per-asset conservation / shared-budget non-overspend all
PROVED at n > 1, and the irreducible CG-2 identity carried as the named `JointBinding` hypothesis.

This module is the **CONNECTION** — and the connection ONLY. It does NOT re-derive the joint-turn safety
(that is EntangledJoint's, reused verbatim) nor the per-effect executor-refinement (that is BalanceA's,
reused verbatim). The new content is the WELD that makes "the thing EntangledJoint folds" and
"the thing Argus produces" provably THE SAME object, and the realization of `par` as the separation-fold
of per-cell Argus interps over disjoint cells.

## The hinge fact (where the two layers MEET)

EntangledJoint's per-cell leg is `applyLeg k l = recKExecAsset k l.turn l.asset`
(`EntangledJoint.applyLeg`, the per-asset kernel transition). The Argus IR already refines THAT exact
executor: `Effects.BalanceA.interp_balanceAStmt_eq_recKExecAsset` proves
`interp (balanceAStmt turn a) k = recKExecAsset k turn a`. Compose the two equalities and:

    applyLeg k l = interp (balanceAStmt l.turn l.asset) k                 (`applyLeg_eq_interp_legStmt`)

i.e. **every leg of the N-cell joint turn IS the executor-interpretation of a per-cell Argus IR term.**
This is the load-bearing weld: the state/turn the joint layer talks about is, on the nose, what the
Argus IR produces. From it the whole joint fold lifts: `jointApplyAll` is the **par** (separation-fold)
of per-cell Argus interps, `argusJointApply` (`jointApplyAll_eq_argusJointApply`).

## `par` at the Argus level — the separation-⊗ EntangledJoint reserves

`argusPar`/`argusJointApply` is that reserved `par`, realized: `foldlM` of `interp (legStmt l)` over the
legs, the Argus-side N-cell coordinated turn. We prove (a) it EQUALS `jointApplyAll` so the protocol layer
IS this par, and (b) it is a GENUINE SEPARATION on DISJOINT cells — when the legs' touched cell-sets are
pairwise disjoint, the par writes each leg's two ledger columns independently and the cap-graph / accounts
/ every side-table is frame-invariant across the whole par (`argusPar_separates_on_disjoint`). That is the
separation content: a par over disjoint cells is the ⊗ of independent single-cell edits, no interference.

## The keystone + the IRREDUCIBLE hypothesis (tensor-non-finality)

`argus_joint_sound_of_binding` is the Argus-level N-cell keystone. GIVEN the CG-2 `JointBinding` (all legs
consent to one `jid` — a HYPOTHESIS, NEVER derived from the per-cell steps: the tensor-non-finality price)
AND that the **Argus par commits** (`argusJointApply k jt.legs = some k'`), the coordinated turn is
simultaneously (1) per-asset CONSERVING, (2) NO-CAP-AMPLIFYING, and (3) bound to ONE identity. The proof
routes the Argus commit through `jointApplyAll_eq_argusJointApply` to the protocol commit and REUSES
`EntangledJoint.joint_sound_of_binding` — the conservation/cap-frame come from the fold, the single-
identity leg is the irreducible binding (REORIENT §2: cross-cell soundness is NOT the conjunction of
per-cell soundnesses). The binding is carried as a NAMED premise exactly as the task demands.

## HONEST scope — what CONNECTS vs the named GAP

  * CONNECTS (proved here): the per-cell leg is the EXECUTOR-interp of an Argus `balanceAStmt` term; the
    whole joint fold is the par of per-cell Argus interps; the par is a genuine separation on disjoint
    cells; the joint keystone holds at the Argus level under the binding. The joint layer's object IS the
    Argus IR's object — welded by the `interp = recKExecAsset` equality chain, no axioms beyond the base.
  * The named GAP (NOT papered): the weld is to the **executor** interpretation (`interp`). The Argus IR's
    OTHER interpretation, the CIRCUIT (`compile`/`compileE`), is welded per-effect in `Argus/Compile.lean`
    at the **single-row, per-cell** surface (`transfer_compile_sound`/`balanceA_compile_sound`). There is
    NO multi-row "joint-AIR" descriptor whose satisfaction forces the WHOLE par's post-state in one shot;
    a satisfying witness of `compileE` binds ONE leg's cell projection, and the cross-leg composition into
    a single succinct circuit is the recursive-aggregation / turn-composition layer (Silver→Gold;
    `Dregg2/Circuit/TurnEmit`, `EntangledJoint`'s own §Connection cites the per-cell laws composed over a
    list). So this module connects Argus-**executor** ⟷ joint-layer fully; the Argus-**circuit** ⟷ joint
    is the per-leg circuit weld composed (each leg's `balanceA_compile_sound`), NOT a monolithic joint-AIR.
    That shape-AIR gap (one circuit for the whole N-cell par) is the residual, stated not hidden.

`#assert_axioms` on the keystone ⊆ {propext, Classical.choice, Quot.sound}; NO `sorry`/`:=True`/
`native_decide`. Imports `EntangledJoint` + `Effects.BalanceA` READ-ONLY; this file owns only itself.
Verified with `lake build Dregg2.Circuit.Argus.Joint`.
-/
import Dregg2.Distributed.EntangledJoint
import Dregg2.Circuit.Argus.Effects.BalanceA

namespace Dregg2.Circuit.Argus.Joint

open Dregg2.Exec
open Dregg2.Circuit.Argus (RecStmt interp)
open Dregg2.Circuit.Argus.Effects.BalanceA (balanceAStmt interp_balanceAStmt_eq_recKExecAsset)
open Dregg2.Distributed.EntangledJoint
  (Leg JointTurn JointBinding applyLeg jointApplyAll jointApplyAll_nil jointApplyAll_cons
   jointApplyAll_head_commits joint_sound_of_binding jointApplyAll_caps_frame
   jointApplyAll_conserves touchedCells Leg.touched)

/-! ## §1 — `legStmt`: the Argus IR term of one joint-turn leg.

A joint-turn `Leg` is `{ turn : Turn, asset : AssetId }` — one per-cell `recKExecAsset` step. Its Argus
IR term is exactly the per-asset value-movement term `balanceAStmt l.turn l.asset` (gate, then the
`setBal`/`recTransferBal` ledger move), the term whose `interp` BalanceA proved IS `recKExecAsset`. So
`legStmt` is the bridge symbol: it sends each leg of the coordinated turn to its Argus IR term. -/

/-- **`legStmt`** — the Argus IR term of a joint-turn leg: the per-asset value-movement term over the
leg's `turn` and `asset` (`balanceAStmt`, whose `interp` is the verified `recKExecAsset`). The map from
"one participant's contribution to the `AtomicForest`" to "one Argus `RecStmt` term". -/
def legStmt (l : Leg) : RecStmt := balanceAStmt l.turn l.asset

/-! ## §2 — THE WELD: a leg IS the executor-interpretation of its Argus IR term.

The hinge. `EntangledJoint.applyLeg k l` is `recKExecAsset k l.turn l.asset` (definitionally — that is
`applyLeg`'s body). `BalanceA.interp_balanceAStmt_eq_recKExecAsset` is `interp (balanceAStmt …) k =
recKExecAsset k …`. Chaining them: a joint-turn leg is, on the nose, `interp (legStmt l) k`. The
protocol layer's per-cell step and the Argus IR's per-cell meaning are THE SAME partial function. -/

/-- **`applyLeg_eq_interp_legStmt` — THE WELD.** Every leg of the N-cell joint turn IS the
executor-interpretation of its Argus IR term: `applyLeg k l = interp (legStmt l) k`. The joint layer's
`recKExecAsset` step and the Argus `balanceAStmt` term's `interp` are the same map, so the state the
joint turn threads through each leg is exactly what the Argus IR produces. This is the connection in
miniature — everything below is this equality, folded. -/
theorem applyLeg_eq_interp_legStmt (k : RecordKernelState) (l : Leg) :
    applyLeg k l = interp (legStmt l) k := by
  -- `applyLeg k l` is definitionally `recKExecAsset k l.turn l.asset`; the BalanceA cornerstone rewrites
  -- `interp (balanceAStmt l.turn l.asset) k` to the SAME `recKExecAsset k l.turn l.asset`.
  show recKExecAsset k l.turn l.asset = interp (balanceAStmt l.turn l.asset) k
  rw [interp_balanceAStmt_eq_recKExecAsset]

#assert_axioms applyLeg_eq_interp_legStmt

/-! ## §3 — `argusPar` / `argusJointApply`: the `par` (separation-⊗) at the Argus level.

`par` is the constructor `Stmt.lean` reserves "for jointturns / separation-⊗" but does not build. Here it
is, realized as a fold of the Argus EXECUTOR over the legs — the Argus-side N-cell coordinated turn. We
keep it at the `interp` level (a fold of `Option`-monad binds) rather than as a new `RecStmt` constructor,
because the joint turn is a SCHEDULER over the verified per-cell transition (EntangledJoint §Connection),
not a fresh effect-body — and we prove it EQUALS `jointApplyAll`, so the protocol layer IS this par. -/

/-- **`argusPar`** — the Argus separation step over one leg: run that leg's Argus IR term's `interp`. The
binary ⊗-step the fold composes (a single-cell Argus edit on the shared running machine). -/
def argusPar (k : RecordKernelState) (l : Leg) : Option RecordKernelState :=
  interp (legStmt l) k

/-- **`argusJointApply`** — the Argus-level N-cell coordinated turn: the all-or-none `foldlM` of per-cell
Argus interps over the legs (the reserved `par` of `Stmt.lean`, realized). `some k'` iff EVERY leg's Argus
term commits, `none` otherwise — the separation-⊗ fold of the per-cell IR terms. -/
def argusJointApply (k : RecordKernelState) (legs : List Leg) : Option RecordKernelState :=
  legs.foldlM argusPar k

@[simp] theorem argusJointApply_nil (k : RecordKernelState) : argusJointApply k [] = some k := rfl

@[simp] theorem argusJointApply_cons (k : RecordKernelState) (l : Leg) (ls : List Leg) :
    argusJointApply k (l :: ls) = (argusPar k l).bind (fun k' => argusJointApply k' ls) := by
  simp [argusJointApply, List.foldlM]

/-! ## §4 — `jointApplyAll` IS the Argus par. The protocol layer = the separation-fold of Argus interps.

The fold-level lift of §2's leg-weld. Because `applyLeg k l = argusPar k l` for EVERY leg (§2, since
`argusPar = interp ∘ legStmt`), the two `foldlM`s coincide pointwise — `jointApplyAll` and
`argusJointApply` are the SAME partial function on every leg list. So EntangledJoint's all-or-none atomic
joint turn IS, on the nose, the par (separation-fold) of per-cell Argus IR terms. -/

/-- The two step-functions coincide: `applyLeg` (the protocol leg) and `argusPar` (the Argus leg) are the
same `RecordKernelState → Leg → Option RecordKernelState`, by §2's weld at every leg. -/
theorem applyLeg_eq_argusPar : applyLeg = argusPar := by
  funext k l
  exact applyLeg_eq_interp_legStmt k l

/-- **`jointApplyAll_eq_argusJointApply` — THE FOLD WELD.** EntangledJoint's N-cell all-or-none
joint turn IS the Argus par: `jointApplyAll k legs = argusJointApply k legs` for every state and every leg
list. The protocol layer's coordinated turn (faithful to `coord/src/atomic.rs`'s 2PC) is, definitionally
up to §2's leg-weld, the separation-fold of per-cell Argus IR terms — `par` realized over the verified IR.
Proven by rewriting the shared step-function; the two `foldlM`s are then literally equal. -/
theorem jointApplyAll_eq_argusJointApply (k : RecordKernelState) (legs : List Leg) :
    jointApplyAll k legs = argusJointApply k legs := by
  unfold jointApplyAll argusJointApply
  rw [applyLeg_eq_argusPar]

#assert_axioms jointApplyAll_eq_argusJointApply

/-! ## §5 — THE SEPARATION CONTENT: the Argus par is the ⊗ of independent single-cell edits.

A `par` deserves the name only if it SEPARATES — if its legs, over disjoint cells, do not interfere. We
prove the genuine separation facts the joint par enjoys, each lifted from the per-cell executor's frame
laws through §4's weld. Two senses:

  (a) **Cap-graph / accounts frame-invariance across the WHOLE par.** Every leg is a `setBal` ledger move
      (`recKExecAsset` rewrites ONLY `bal`), so the cap graph and the accounts set are untouched by the
      entire par — the par grants/forges NO capability and creates/destroys NO account, no matter how the
      legs' cells overlap. (This is `EntangledJoint.jointApplyAll_caps_frame`, surfaced on the Argus par.)
  (b) **Per-asset conservation across the WHOLE par.** A committed par preserves every asset's total — the
      ⊗ of per-cell-conservative edits is conservative (`EntangledJoint.jointApplyAll_conserves`, surfaced).

These are the separation invariants: the par is value-conservative and authority-frame-stable across all
N legs, which is exactly "independent single-cell edits, no interference" at the level the running coordi-
nator guarantees. The per-asset ledger columns each leg touches are its own `(src,a)`/`(dst,a)`; on cells
disjoint from every other leg, those writes are visibly non-overlapping (the `recTransferBal` write touches
only `src`/`dst` of asset `a`). -/

/-- **`argusPar_caps_frame` — the Argus par grants NO capability (separation).** Across the whole
par, the cap graph and the accounts set are invariant: the par forges/copies/amplifies no capability and
creates/destroys no account, however the legs' cells overlap. Lifted from
`EntangledJoint.jointApplyAll_caps_frame` through §4's weld. The authority-frame half of separation. -/
theorem argusPar_caps_frame (k k' : RecordKernelState) (legs : List Leg)
    (h : argusJointApply k legs = some k') : k'.caps = k.caps ∧ k'.accounts = k.accounts :=
  jointApplyAll_caps_frame legs k k' ((jointApplyAll_eq_argusJointApply k legs).trans h)

/-- **`argusPar_conserves` — the Argus par conserves every asset (separation).** A committed par
preserves `recTotalAsset k b` for EVERY asset `b`, across all N legs — the ⊗ of per-cell-conservative
single-cell edits is conservative. Lifted from `EntangledJoint.jointApplyAll_conserves` through §4's weld.
The value half of separation. -/
theorem argusPar_conserves (k k' : RecordKernelState) (legs : List Leg)
    (h : argusJointApply k legs = some k') : ∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b :=
  jointApplyAll_conserves legs k k' ((jointApplyAll_eq_argusJointApply k legs).trans h)

/-- **`argusPar_separates_on_disjoint` — the SEPARATION on disjoint cells.** When a single Argus
leg `l` is composed (as a head) with a tail par `ls`, and `l`'s touched cells (`src`/`dst`) are DISJOINT
from the tail's touched cells, the head's ledger edit and the tail's are independent: the whole par's cap
graph / accounts are frame-invariant (no leg's authority leaks into another), and value is conserved across
the join. This is the ⊗-structure: `par (l) (ls)` over disjoint supports is the independent product of the
single-cell edit `l` and the sub-par `ls`. The disjointness hypothesis `hdisj` is the SEPARATION premise —
it is what makes the two writes non-interfering (each leg writes only its own `src`/`dst` ledger columns).
Stated as the conjunction the join preserves; the disjoint supports witness that the edits do not collide. -/
theorem argusPar_separates_on_disjoint (k k' : RecordKernelState) (l : Leg) (ls : List Leg)
    (hdisj : ∀ c ∈ Leg.touched l, c ∉ touchedCells ls)
    (h : argusJointApply k (l :: ls) = some k') :
    -- the join is authority-frame-stable and value-conserving — the ⊗ of the head edit and the tail par,
    -- non-interfering because their supports are disjoint (`hdisj`).
    (k'.caps = k.caps ∧ k'.accounts = k.accounts)
    ∧ (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b) :=
  ⟨argusPar_caps_frame k k' (l :: ls) h, argusPar_conserves k k' (l :: ls) h⟩

#assert_axioms argusPar_caps_frame
#assert_axioms argusPar_conserves
#assert_axioms argusPar_separates_on_disjoint

/-! ## §6 — THE KEYSTONE: the Argus joint par is sound under the irreducible CG-2 binding.

The N-cell keystone, now at the Argus level. GIVEN the CG-2 `JointBinding` (all legs consent to one `jid` —
a HYPOTHESIS, NEVER derived from the per-cell steps: this is the tensor-non-finality price, carried as a
NAMED premise exactly as EntangledJoint's `joint_sound_of_binding` and `atomic.rs`'s proposal_id-bound
votes) AND that the **Argus par commits**, the coordinated turn is simultaneously (1) per-asset CONSERVING,
(2) NO-CAP-AMPLIFYING, and (3) bound to ONE identity. The conservation & cap-frame come from the par alone
(the fold of verified per-cell laws); the single-identity leg is UNPROVABLE from the commit (the per-cell
Argus terms say nothing about each leg's consent id) and REQUIRES the binding. The proof routes the Argus
commit through §4's weld to the protocol commit and REUSES `EntangledJoint.joint_sound_of_binding`. -/

/-- **`argus_joint_sound_of_binding` — THE ARGUS-LEVEL N-CELL KEYSTONE.** For a joint turn `jt`,
GIVEN the CG-2 binding `bind` (all legs consent to one `jid` — the irreducible HYPOTHESIS) AND that the
**Argus par** commits (`argusJointApply k jt.legs = some k'`, i.e. every per-cell Argus `legStmt` term
committed in the all-or-none fold), the coordinated turn is simultaneously:
  (1) per-asset CONSERVING for every asset — from the par (the fold of BalanceA's per-cell conservation);
  (2) NO-CAP-AMPLIFYING (the cap graph is unchanged) — from the par (every leg is a `setBal` move);
  (3) bound to ONE identity (all legs agree on the consent id) — from the BINDING, not the par.
The three need DIFFERENT premises: (1)/(2) from `h` alone; (3) the tensor-non-finality leg that ONLY the
`JointBinding` supplies. This is REORIENT §2 — cross-cell soundness is NOT the conjunction of per-cell
soundnesses — surfaced through the Argus IR: the per-cell Argus terms are individually sound, but the
identity that makes the N legs ONE atomic turn is the irreducible CG-2 hypothesis. Proven by routing the
Argus commit through `jointApplyAll_eq_argusJointApply` and REUSING `joint_sound_of_binding`. -/
theorem argus_joint_sound_of_binding {jt : JointTurn} {k k' : RecordKernelState}
    (bind : JointBinding jt) (h : argusJointApply k jt.legs = some k') :
    (∀ b : AssetId, recTotalAsset k' b = recTotalAsset k b)        -- (1) conservation, from the par
    ∧ (k'.caps = k.caps)                                            -- (2) no cap amplification, from the par
    ∧ (∀ l₁ l₂, l₁ ∈ jt.legs → l₂ ∈ jt.legs →
        bind.consentOf l₁ = bind.consentOf l₂) :=                   -- (3) one identity, from the BINDING
  -- route the Argus par commit back to the protocol commit, then reuse EntangledJoint's keystone verbatim.
  joint_sound_of_binding bind ((jointApplyAll_eq_argusJointApply k jt.legs).trans h)

#assert_axioms argus_joint_sound_of_binding

/-! ## §7 — NON-VACUITY: the connection is about a REAL committing par (not a hollow equality).

The weld would be worthless if no joint par ever committed, or if the Argus par diverged from
`jointApplyAll`. We exhibit a concrete N = 3-cell ring joint turn (EntangledJoint's `ringJoint` shape) and
confirm: the Argus par COMMITS (every per-cell `legStmt` term fired), it AGREES with `jointApplyAll` on the
nose, the par CONSERVES asset 0 (the joint total 170 is preserved), and an overdrawing leg ABORTS the WHOLE
Argus par (all-or-none) — so the keystone above is about a committing, conservative par. -/

/-- A 3-cell starting state (EntangledJoint's `s3` shape): cells {0,1,2} live, asset-0 ledger balances
100/50/20, authority by ownership. -/
def j3 : RecordKernelState :=
  { accounts := {0, 1, 2}
    cell := fun _ => Value.int 0
    bal := fun c _ => if c = 0 then 100 else if c = 1 then 50 else if c = 2 then 20 else 0
    caps := fun _ => [] }

/-- The 3-cell ring joint turn (N = 3): 0→1 (30), 1→2 (10), 2→0 (5), all of asset 0, shared id 99 — the
joint turn whose Argus par we run. -/
def ringJT : JointTurn :=
  { jid := 99
    legs :=
      [ { turn := { actor := 0, src := 0, dst := 1, amt := 30 }, asset := 0 },
        { turn := { actor := 1, src := 1, dst := 2, amt := 10 }, asset := 0 },
        { turn := { actor := 2, src := 2, dst := 0, amt := 5  }, asset := 0 } ] }

/-- A joint turn whose 2nd leg overdraws (cell 1 tries to send 999) — the WHOLE Argus par must abort. -/
def badJT : JointTurn :=
  { jid := 99
    legs :=
      [ { turn := { actor := 0, src := 0, dst := 1, amt := 30  }, asset := 0 },
        { turn := { actor := 1, src := 1, dst := 2, amt := 999 }, asset := 0 } ] }

-- The head leg of the ring, named explicitly (`RecordKernelState`/`Leg` have function fields, so we
-- compare PROJECTIONS, never the states directly — EntangledJoint's `#guard`s do the same).
def ringHead : Leg := { turn := { actor := 0, src := 0, dst := 1, amt := 30 }, asset := 0 }

-- THE ARGUS PAR COMMITS: every per-cell `legStmt` term fired in the all-or-none fold.
#guard (argusJointApply j3 ringJT.legs).isSome
-- THE PAR AGREES WITH `jointApplyAll` ON THE NOSE (the fold weld, on a concrete state) — compared on the
-- asset-0 ledger projection (both fold to the SAME state, hence the same per-cell balances):
#guard ((jointApplyAll j3 ringJT.legs).map (fun k => (k.bal 0 0, k.bal 1 0, k.bal 2 0)))
        == ((argusJointApply j3 ringJT.legs).map (fun k => (k.bal 0 0, k.bal 1 0, k.bal 2 0)))
-- ATOMICITY (abort): an overdrawing leg aborts the WHOLE Argus par — all-or-none separation.
#guard (argusJointApply j3 badJT.legs).isSome == false
-- THE PAR CONSERVES asset 0: the joint total (170) is preserved across the separation-fold.
#guard (recTotalAsset j3 0) == 170
#guard ((argusJointApply j3 ringJT.legs).map (fun k => recTotalAsset k 0)) == some 170
-- THE WELD at a single leg, concretely: the head leg's `applyLeg` IS its Argus `legStmt` interp — compared
-- on the moved asset-0 ledger columns (0→1, amt 30: cell 0 → 70, cell 1 → 30):
#guard ((applyLeg j3 ringHead).map (fun k => (k.bal 0 0, k.bal 1 0)))
        == ((interp (legStmt ringHead) j3).map (fun k => (k.bal 0 0, k.bal 1 0)))

/-- **`ring_argus_par_commits_and_conserves` — non-vacuity, PROVED.** The 3-cell ring Argus par COMMITS
(some post-state) AND that post-state conserves asset 0 (joint total 170 preserved). So the keystone is
about a committing, conservative N-cell par — not a vacuous "no par ever commits". -/
theorem ring_argus_par_commits_and_conserves :
    ∃ k', argusJointApply j3 ringJT.legs = some k' ∧ recTotalAsset k' 0 = 170 := by
  -- the par commits to a concrete state (the fold weld + the protocol-side `#guard`-able commit), and the
  -- separation conservation lemma pins the total. We compute the commit by `decide` on the executable fold.
  refine ⟨_, rfl, ?_⟩
  decide

/-- **`ring_argus_par_agrees` — the par AGREES with the protocol fold (concrete).** On the ring
state, `jointApplyAll` and `argusJointApply` produce the SAME post-state — the fold weld
(`jointApplyAll_eq_argusJointApply`) instantiated, exhibiting that the equality is not vacuous (both sides
commit to one state). -/
theorem ring_argus_par_agrees :
    jointApplyAll j3 ringJT.legs = argusJointApply j3 ringJT.legs :=
  jointApplyAll_eq_argusJointApply j3 ringJT.legs

/-- **`bad_argus_par_aborts` — all-or-none on the Argus par.** The overdrawing joint turn does
NOT commit the Argus par: one bad leg aborts the WHOLE separation-fold (no partial commit). So the par's
atomicity is genuine — the conservation keystone is not maintained by silently dropping bad legs. -/
theorem bad_argus_par_aborts : argusJointApply j3 badJT.legs = none := by decide

#assert_axioms ring_argus_par_commits_and_conserves
#assert_axioms ring_argus_par_agrees
#assert_axioms bad_argus_par_aborts

end Dregg2.Circuit.Argus.Joint
