/-
# Dregg2.Apps.EscrowDeskCouncil — an M-of-N council-governed escrow desk, as ONE cell program.

A real desk that holds value in escrow and releases it ONLY when an M-of-N council approves AND
the claimant proves knowledge of the release secret AND no value is left stranded. Every clause is
a constraint of the cell's `RecordProgram`; every refusal is a theorem. This exercises the full
landed expressiveness (`Exec/Program.lean`): the in-program M-of-N quorum (`countGe`, with the
anti-aliasing `eraseDups` design), the hash-knowledge gate (`preimageGate`), the drain invariant
(`balanceLe`), turn-sender binding (`senderInField`), and the Heyting composite (`anyOf`/`not`).

## Why this is not a toy

The naive "M-of-N" is a counter you increment per approval — and an unbounded counter is faked by
ONE party writing `m`. This desk's quorum is `countGe m quorumF`: the turn must EXHIBIT the full
approver set, its §8-portal sorted-set commitment must equal the cell's published `quorum`
commitment slot, and the DISTINCT count (`List.eraseDups`) must be `≥ m`. A duplicate-padded
exhibit (`[op, op, op]` — one operator claiming to be three) COLLAPSES to one. That is the
anti-`affineLe`-flag tooth the polis council taught us, made a release gate.

And the desk does not strand value: a release that drives the desk to its RESOLVED state must
drain the balance to `≤ 0` (`balanceLe 0` under the resolved guard). A "release" that approves the
quorum but leaves the money sitting is rejected — value out, or no resolve.

## The desk cell — its state

  * `state`   — `0 OPEN`, `1 APPROVED`, `2 RESOLVED` (the lifecycle slot);
  * `operator`— the desk's registered operator identity (only it may OPEN a claim);
  * `quorum`  — the §8-portal commitment to the council's approver set (governance-written);
  * `secret`  — the commitment to the release secret (the claimant must reveal its preimage);
  * the cell's SEALED balance — the escrowed value (drained on RESOLVED), carried in `TurnCtx.balance`.

The release gate is ONE `RecordProgram.predicate`. The teeth: COMMIT a faithful release (quorum
met + correct reveal + drained); REFUSE a forged quorum (duplicate-padded approvers), a wrong
reveal (no preimage), a stranded-value resolve (balance still positive), an under-quorum release
(too few distinct approvers), and a non-operator open.

## Honest scope

* `countGe` discharges "the committed set opens with ≥ m DISTINCT elements." It does NOT bind each
  element to a live signature of THIS turn (per-element signatures are not in the scalar
  evaluator); the approval binding is the polis actor-bound approval-slot ceremony FEEDING the
  committed set, and the `quorum` commitment slot itself must be governance-written. This is the
  same carried scope as `Apps/ChannelGroup.lean`'s council point — named here, not laundered.
* `preimageGate`/`quorum` rest on the §8 crypto portal (the hash binding); the ordering/counting
  and gate laws are proved here. The portal is the named seam (`AuthPortal`, the seL4 floor).

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` —
`decide` / `#guard` / `Exec.Program`-keystone reuse only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.Program

namespace Dregg2.Apps.EscrowDeskCouncil

open Dregg2.Exec

/-! ## §0 — The desk's field names, lifecycle codes, and identities. -/

/-- The lifecycle slot: `0 OPEN`, `1 APPROVED`, `2 RESOLVED`. -/
abbrev stateF : FieldName := "state"
/-- The desk's registered operator identity. -/
abbrev operatorF : FieldName := "operator"
/-- The §8-portal commitment to the council's approver set. -/
abbrev quorumF : FieldName := "quorum"
/-- The commitment to the release secret (claimant reveals its preimage). -/
abbrev secretF : FieldName := "secret"

/-- Lifecycle: the escrow is open for claims. -/
abbrev stOPEN : Int := 0
/-- Lifecycle: the council has approved; awaiting the reveal + drain. -/
abbrev stAPPROVED : Int := 1
/-- Lifecycle: released and resolved (balance drained). -/
abbrev stRESOLVED : Int := 2

/-- The council quorum threshold (M-of-N: at least this many DISTINCT approvers). -/
abbrev quorumM : Nat := 3

/-- The desk operator's identity. -/
abbrev operatorPk : Int := 0xD3
/-- A non-operator's identity. -/
abbrev outsiderPk : Int := 0x99

/-! ## §1 — THE RELEASE GATE as a `RecordProgram` (quorum ∧ reveal ∧ drain ∧ provenance).

The desk's program is a conjunction:

  * `senderInField operatorF` — **provenance**: a turn that touches the desk must be SIGNED BY the
    registered operator. Capability possession is not enough.
  * `anyOf [.not (.fieldEquals stateF stRESOLVED), .countGe quorumM quorumF]` — **the M-of-N
    council gate**: a turn that drives the desk to RESOLVED must exhibit a council quorum (≥ M
    distinct approvers, committed to `quorum`). A turn NOT resolving is dormant for this clause.
  * `anyOf [.not (.fieldEquals stateF stRESOLVED), .preimageGate secretF]` — **the knowledge
    gate**: resolving requires revealing the preimage of the desk's `secret` commitment.
  * `anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0]` — **the drain invariant**:
    resolving requires the desk's balance be drained to `≤ 0`. Value cannot be stranded.

Each release condition is gated BY the resolved-state guard (`anyOf [.not (state=RESOLVED), …]`),
so they bind exactly when the turn resolves — the composable shape `committedRelease`/`drainTooth`
the language doc names. The conjunction is ONE predicate (all-or-nothing). -/
def releaseConstraints : List StateConstraint :=
  [ .simple (.senderInField operatorF)                                               -- provenance
  , .anyOf [.not (.fieldEquals stateF stRESOLVED), .countGe quorumM quorumF]          -- M-of-N
  , .anyOf [.not (.fieldEquals stateF stRESOLVED), .preimageGate secretF]             -- reveal
  , .anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0] ]                    -- drain

/-- **The escrow desk program** — the council-governed release as ONE coalgebra structure-map. -/
def deskProgram : RecordProgram := .predicate releaseConstraints

/-! ## §2 — Extraction plumbing (the `ChannelGroup` pattern). -/

/-- Every constraint binds on an admitted turn (`admitsCtx` on `.predicate` IS the conjunction). -/
private theorem admitted_mem {ctx : TurnCtx} {m : Nat} {o n : Value}
    (h : deskProgram.admitsCtx ctx m o n = true)
    {c : StateConstraint} (hc : c ∈ releaseConstraints) :
    evalConstraintCtx ctx c o n = true := by
  have hall : releaseConstraints.all (fun c => evalConstraintCtx ctx c o n) = true := h
  exact List.all_eq_true.mp hall c hc

/-- A two-variant `anyOf` whose first disjunct fails forces the second (the `ChannelGroup`
`anyOf_pair_right` shape). -/
private theorem anyOf_pair_right {ctx : TurnCtx} {x y : SimpleConstraint} {o n : Value}
    (h : evalConstraintCtx ctx (.anyOf [x, y]) o n = true)
    (hx : evalSimpleCtx ctx x o n = false) :
    evalSimpleCtx ctx y o n = true := by
  have h' : (evalSimpleCtx ctx x o n || (evalSimpleCtx ctx y o n || false)) = true := h
  rw [hx] at h'
  simpa using h'

/-- When a turn DRIVES the desk to RESOLVED (`new[state] = RESOLVED`), the `.not (state=RESOLVED)`
guard of each release clause is FALSE — so the second disjunct (the real release condition) must
hold. The bridge that turns each guarded `anyOf` into its binding release condition. -/
private theorem resolved_guard_false {ctx : TurnCtx} {o n : Value}
    (hres : n.scalar stateF = some stRESOLVED) :
    evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n = false := by
  show (!(evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n)) = false
  have : evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n = true := by
    show evalSimple (.fieldEquals stateF stRESOLVED) o n = true
    simp [evalSimple, hres]
  rw [this]; rfl

/-! ## §3 — THE TEETH on the release policy (both polarities, all PROVED). -/

/-- **① M-of-N COUNCIL TOOTH — a forged (duplicate-padded) quorum is UNSAT.** A release driving
the desk to RESOLVED whose exhibited approver set has FEWER than `quorumM` DISTINCT elements
(`List.eraseDups` collapses duplicates) is rejected: `admitsCtx = false`. One operator claiming to
be three (`[op, op, op]`) does NOT meet a 3-of-N quorum. The anti-`affineLe`-flag tooth as a
release gate. -/
theorem forged_quorum_rejected (ctx : TurnCtx) (m : Nat) (o n : Value)
    (hres : n.scalar stateF = some stRESOLVED)
    (hfew : ctx.exhibited.eraseDups.length < quorumM) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne : deskProgram.admitsCtx ctx m o n = true := by
    cases h : deskProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  -- The M-of-N clause is admitted; the resolved guard is false, so `countGe` must hold; but the
  -- distinct count is below the threshold — contradiction via `evalSimpleCtx_countGe_quorum`.
  have hclause := admitted_mem hne
    (c := .anyOf [.not (.fieldEquals stateF stRESOLVED), .countGe quorumM quorumF]) (by
      exact .tail _ (.head _))
  have hcount : evalSimpleCtx ctx (.countGe quorumM quorumF) o n = true :=
    anyOf_pair_right hclause (resolved_guard_false hres)
  have := evalSimpleCtx_countGe_quorum ctx quorumM quorumF o n hcount
  omega

/-- **② KNOWLEDGE-GATE TOOTH — a wrong/absent reveal is UNSAT.** A release driving the desk to
RESOLVED without revealing the preimage of the `secret` commitment (no `revealedHash`, or a hash
that does not match the slot) is rejected: `admitsCtx = false`. A claimant who has not proven
knowledge of the secret cannot drain the escrow. -/
theorem wrong_reveal_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (committed : Int)
    (hres : n.scalar stateF = some stRESOLVED)
    (hsecret : n.scalar secretF = some committed)
    (hbad : ctx.revealedHash ≠ some committed) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne : deskProgram.admitsCtx ctx m o n = true := by
    cases h : deskProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have hclause := admitted_mem hne
    (c := .anyOf [.not (.fieldEquals stateF stRESOLVED), .preimageGate secretF]) (by
      exact .tail _ (.tail _ (.head _)))
  have hpre : evalSimpleCtx ctx (.preimageGate secretF) o n = true :=
    anyOf_pair_right hclause (resolved_guard_false hres)
  -- The preimage gate admitted ⇒ revealedHash = the committed secret — contradicting hbad.
  obtain ⟨hh, hrev, hcom⟩ := (evalSimpleCtx_preimageGate_iff ctx secretF o n).mp hpre
  rw [hsecret] at hcom; injection hcom with hcom; subst hcom
  exact hbad hrev

/-- **③ DRAIN TOOTH — a stranded-value resolve is UNSAT.** A release driving the desk to RESOLVED
while its balance is still POSITIVE (value left sitting) is rejected: `admitsCtx = false`. The
escrow cannot resolve with value stranded — it must be drained (`balance ≤ 0`). -/
theorem stranded_value_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (bal : Int)
    (hres : n.scalar stateF = some stRESOLVED)
    (hbalance : ctx.balance = some bal)
    (hpos : bal > 0) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne : deskProgram.admitsCtx ctx m o n = true := by
    cases h : deskProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have hclause := admitted_mem hne
    (c := .anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0]) (by
      exact .tail _ (.tail _ (.tail _ (.head _))))
  have hdrain : evalSimpleCtx ctx (.balanceLe 0) o n = true :=
    anyOf_pair_right hclause (resolved_guard_false hres)
  -- balanceLe 0 admitted ⇒ balance ≤ 0 — contradicting hpos.
  obtain ⟨b, hb, hle⟩ := (evalSimpleCtx_balanceLe_iff ctx 0 o n).mp hdrain
  rw [hbalance] at hb; injection hb with hb; subst hb; omega

/-- **④ PROVENANCE TOOTH — a non-operator turn is UNSAT.** Any desk turn whose sender is NOT the
registered operator is rejected: `admitsCtx = false`. Only the operator may open/advance a claim;
an outsider holding a capability cannot. -/
theorem non_operator_rejected (ctx : TurnCtx) (m : Nat) (o n : Value) (recordedOp : Int)
    (hop : n.scalar operatorF = some recordedOp)
    (houtsider : ctx.sender ≠ some recordedOp) :
    deskProgram.admitsCtx ctx m o n = false := by
  by_contra hc
  have hne : deskProgram.admitsCtx ctx m o n = true := by
    cases h : deskProgram.admitsCtx ctx m o n with
    | true => rfl
    | false => exact absurd h hc
  have hprov := admitted_mem hne (c := .simple (.senderInField operatorF)) (.head _)
  have : evalSimpleCtx ctx (.senderInField operatorF) o n = true := by
    simpa [evalConstraintCtx] using hprov
  obtain ⟨s, hs, hv⟩ := (evalSimpleCtx_senderInField_iff ctx operatorF o n).mp this
  rw [hop] at hv; injection hv with hv; subst hv; exact houtsider hs

/-- **⑤ THE FAITHFUL RELEASE COMMITS (the gate is not constant-false).** A release signed by the
operator, with a met quorum (≥ M distinct approvers committed to `quorum`), the correct secret
reveal, and the balance drained, ADMITS. The conjunction of the teeth is non-vacuous: there is a
real release the desk lets through. -/
theorem faithful_release_admits (ctx : TurnCtx) (m : Nat) (o n : Value)
    (qc sc : Int)
    (hsender : ctx.sender = some operatorPk)
    (hop : n.scalar operatorF = some operatorPk)
    (_hstate : n.scalar stateF = some stRESOLVED)  -- the scenario: this IS a resolving turn
    (hquorumSlot : n.scalar quorumF = some qc)
    (hquorumCommit : ctx.exhibitedCommit = some qc)
    (hquorumCount : quorumM ≤ ctx.exhibited.eraseDups.length)
    (hsecretSlot : n.scalar secretF = some sc)
    (hreveal : ctx.revealedHash = some sc)
    (hbalance : ctx.balance = some 0) :
    deskProgram.admitsCtx ctx m o n = true := by
  have c1 : evalConstraintCtx ctx (.simple (.senderInField operatorF)) o n = true := by
    show evalSimpleCtx ctx (.senderInField operatorF) o n = true
    exact (evalSimpleCtx_senderInField_iff ctx operatorF o n).mpr ⟨operatorPk, hsender, hop⟩
  have c2 : evalConstraintCtx ctx (.anyOf [.not (.fieldEquals stateF stRESOLVED), .countGe quorumM quorumF]) o n = true := by
    -- the quorum disjunct holds, so the anyOf holds
    have hq : evalSimpleCtx ctx (.countGe quorumM quorumF) o n = true :=
      (evalSimpleCtx_countGe_iff ctx quorumM quorumF o n).mpr ⟨qc, hquorumCommit, hquorumSlot, hquorumCount⟩
    show (evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n
          || (evalSimpleCtx ctx (.countGe quorumM quorumF) o n || false)) = true
    rw [hq]; simp
  have c3 : evalConstraintCtx ctx (.anyOf [.not (.fieldEquals stateF stRESOLVED), .preimageGate secretF]) o n = true := by
    have hp : evalSimpleCtx ctx (.preimageGate secretF) o n = true :=
      (evalSimpleCtx_preimageGate_iff ctx secretF o n).mpr ⟨sc, hreveal, hsecretSlot⟩
    show (evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n
          || (evalSimpleCtx ctx (.preimageGate secretF) o n || false)) = true
    rw [hp]; simp
  have c4 : evalConstraintCtx ctx (.anyOf [.not (.fieldEquals stateF stRESOLVED), .balanceLe 0]) o n = true := by
    have hd : evalSimpleCtx ctx (.balanceLe 0) o n = true :=
      (evalSimpleCtx_balanceLe_iff ctx 0 o n).mpr ⟨0, hbalance, by omega⟩
    show (evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n
          || (evalSimpleCtx ctx (.balanceLe 0) o n || false)) = true
    rw [hd]; simp
  show releaseConstraints.all (fun c => evalConstraintCtx ctx c o n) = true
  simp only [releaseConstraints, List.all_cons, List.all_nil, c1, c2, c3, c4, Bool.and_true]

/-! ## §4 — CONSERVATION / NON-AMPLIFICATION carriers (re-exported keystones).

The release gate writes desk-metadata fields (state/operator/quorum/secret); it constrains the
SEALED balance via the `balanceLe` drain but writes no capability table — so a release cannot mint
or amplify any authority (the constraint language reads and constrains record fields; it has no
cap-table write). And on an OPEN turn (not resolving), the quorum/reveal/drain clauses are dormant
(the resolved guard is true), so the desk is freely operable until a real release. We pin the
dormancy as a theorem. -/

/-- **`open_turn_release_clauses_dormant`** — on a turn that does NOT resolve the desk
(`new[state] ≠ RESOLVED`), each guarded release clause is satisfied by its FIRST disjunct (the
resolved guard holds), regardless of quorum/reveal/balance. So a non-resolving operator turn is
never blocked by the release machinery — the desk is operable until a real release. (Witnessed
here for the M-of-N clause; the reveal/drain clauses are identical in shape.) -/
theorem open_turn_quorum_dormant (ctx : TurnCtx) (o n : Value) (st : Int)
    (hne : st ≠ stRESOLVED) (hstate : n.scalar stateF = some st) :
    evalConstraintCtx ctx (.anyOf [.not (.fieldEquals stateF stRESOLVED), .countGe quorumM quorumF]) o n = true := by
  have hguard : evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n = true := by
    show (!(evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n)) = true
    have : evalSimpleCtx ctx (.fieldEquals stateF stRESOLVED) o n = false := by
      show evalSimple (.fieldEquals stateF stRESOLVED) o n = false
      simp only [evalSimple, hstate, beq_eq_false_iff_ne, ne_eq, Option.some.injEq]
      exact hne
    rw [this]; rfl
  show (evalSimpleCtx ctx (.not (.fieldEquals stateF stRESOLVED)) o n
        || (evalSimpleCtx ctx (.countGe quorumM quorumF) o n || false)) = true
  rw [hguard]; simp

/-! ## §5 — NON-VACUITY TEETH (`#guard`): the release policy BITES on the concrete desk, both
polarities. -/

section Witnesses

/-- A faithful release: operator signs, state→RESOLVED, quorum slot = 55 (committed), secret slot
= 77 (revealed), the council exhibits 3 DISTINCT approvers, balance drained to 0. -/
def releaseCtx : TurnCtx :=
  { sender := some operatorPk, balance := some 0, revealedHash := some 77,
    exhibited := [101, 102, 103], exhibitedCommit := some 55 }
def deskNew : Value :=
  .record [(operatorF, .int operatorPk), (stateF, .int stRESOLVED),
           (quorumF, .int 55), (secretF, .int 77)]
def deskOld : Value :=
  .record [(operatorF, .int operatorPk), (stateF, .int stAPPROVED),
           (quorumF, .int 55), (secretF, .int 77)]

-- ① COMMIT: a faithful release ADMITS (3 distinct approvers, correct reveal, drained, operator-signed).
#guard deskProgram.admitsCtx releaseCtx 0 deskOld deskNew

-- ① REFUSE (forged quorum, duplicate-padded): the SAME release but the exhibit is [101,101,101]
-- (one approver pretending to be three) — collapses to 1 DISTINCT < 3. REJECTED. The anti-aliasing
-- tooth bites: you cannot fake an M-of-N by repeating yourself.
#guard deskProgram.admitsCtx
  { releaseCtx with exhibited := [101, 101, 101] } 0 deskOld deskNew == false

-- ① REFUSE (under-quorum): only 2 distinct approvers [101,102] < 3. REJECTED.
#guard deskProgram.admitsCtx
  { releaseCtx with exhibited := [101, 102] } 0 deskOld deskNew == false

-- ② REFUSE (wrong reveal): the claimant reveals a hash (5) that does not match the secret (77).
-- REJECTED — no proof of knowledge.
#guard deskProgram.admitsCtx
  { releaseCtx with revealedHash := some 5 } 0 deskOld deskNew == false

-- ② REFUSE (absent reveal): no revealedHash at all. REJECTED (fail-closed).
#guard deskProgram.admitsCtx
  { releaseCtx with revealedHash := none } 0 deskOld deskNew == false

-- ③ REFUSE (stranded value): the desk resolves but the balance is still 40 (value left sitting).
-- REJECTED — the drain invariant bites.
#guard deskProgram.admitsCtx
  { releaseCtx with balance := some 40 } 0 deskOld deskNew == false

-- ④ REFUSE (non-operator): an outsider signs the release. REJECTED — only the operator may.
#guard deskProgram.admitsCtx
  { releaseCtx with sender := some outsiderPk } 0 deskOld deskNew == false

-- ④ REFUSE (unsigned): no sender at all. REJECTED (fail-closed provenance).
#guard deskProgram.admitsCtx
  { releaseCtx with sender := none } 0 deskOld deskNew == false

-- ⑤ COMMIT (open turn dormant): an OPEN turn (state stays APPROVED, not RESOLVED) signed by the
-- operator ADMITS even with NO quorum/reveal/drain — the release clauses are dormant until resolve.
#guard deskProgram.admitsCtx
  { sender := some operatorPk } 0
  (.record [(operatorF, .int operatorPk), (stateF, .int stOPEN), (quorumF, .int 55), (secretF, .int 77)])
  (.record [(operatorF, .int operatorPk), (stateF, .int stAPPROVED), (quorumF, .int 55), (secretF, .int 77)])

-- ⑤ … but the SAME open turn by an OUTSIDER is still REJECTED (provenance always binds).
#guard deskProgram.admitsCtx
  { sender := some outsiderPk } 0
  (.record [(operatorF, .int operatorPk), (stateF, .int stOPEN), (quorumF, .int 55), (secretF, .int 77)])
  (.record [(operatorF, .int operatorPk), (stateF, .int stAPPROVED), (quorumF, .int 55), (secretF, .int 77)]) == false

-- The anti-aliasing design, isolated: 3 distinct meets threshold 3; 3 duplicates do NOT (the
-- eraseDups collapse is the whole point — a release gate that an unbounded counter cannot fake).
#guard evalSimpleCtx { exhibited := [1, 2, 3], exhibitedCommit := some 55 } (.countGe 3 quorumF)
  (.record []) (.record [(quorumF, .int 55)])
#guard evalSimpleCtx { exhibited := [1, 1, 1], exhibitedCommit := some 55 } (.countGe 3 quorumF)
  (.record []) (.record [(quorumF, .int 55)]) == false
-- … and a mismatched commitment (exhibit ≠ the published quorum slot) refuses even with 3 distinct.
#guard evalSimpleCtx { exhibited := [1, 2, 3], exhibitedCommit := some 55 } (.countGe 3 quorumF)
  (.record []) (.record [(quorumF, .int 66)]) == false

end Witnesses

/-! ## §6 — Axiom hygiene. Every load-bearing release theorem checked kernel-clean. -/

#assert_all_clean [
  forged_quorum_rejected,
  wrong_reveal_rejected,
  stranded_value_rejected,
  non_operator_rejected,
  faithful_release_admits,
  open_turn_quorum_dormant
]

end Dregg2.Apps.EscrowDeskCouncil
