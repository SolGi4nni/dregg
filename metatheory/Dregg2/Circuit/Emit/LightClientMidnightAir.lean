/-
# Dregg2.Circuit.Emit.LightClientMidnightAir — the Midnight GRANDPA VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the Midnight light client" slice — the Solana mirror)

`Dregg2.Bridge.LightClientMidnight` AUTHORS the Midnight GRANDPA-finality verification and proves
`mid_no_forgery` over `midVerifyDecision` — the scalar accept/reject a deployed node computes (the counted
signed authority weight, the total authority weight, the Ed25519 + authority-set carriers, the round + era
gates). That gives a node a Lean-PROVEN verdict — but rendered by running Lean on the node's own machine;
a peer (or an on-chain contract) that wants to trust "this dregg node saw Midnight finalize block B at
round R, era E" must RE-TRUST that node's execution. There is no portable object.

This file emits `midVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`midLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: a portable artifact any peer verifies without re-running the node,
and (via the gnark FRI-wrap → Groth16 `SettlementCircuit` → `DreggPeerRegistry`, the SAME on-chain hook
the ETH/Cosmos/Solana AIRs attach to) an on-chain contract verifies. That closes the FOURTH interchain
gap — Midnight from a TRUSTED MIRROR (the observer follows the RPC's `chain_getFinalizedHead`; no
justification is verified) to a formalized, STARK-ified, PORTABLE GRANDPA-finality proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and runs
the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`midLcAir_sound` / `midLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `midVerifyDecision` and hence
to `mid_no_forgery` — so a STARK satisfying this AIR CARRIES the no-forgery guarantee, modulo the two
named crypto carriers (below).

## The crypto boundary: IN-AIR logic vs NAMED verified carriers

  * IN-AIR (arithmetic gates over the trace — the weight TALLY logic, the Nomad-class bug locus):
      - the STRICT > 2/3 supermajority `3·signed > 2·total` as a range-checked non-negative slack
        `WDIFF = 3·SIGNED_WEIGHT − 2·TOTAL_WEIGHT − 1 ∈ [0, 2^128)` (GRANDPA's `threshold`, wrap-free — an
        EXACTLY-2/3 commit gives `WDIFF = −1`, UNSAT, so the strict boundary is enforced IN-CIRCUIT,
        unlike Solana's `≥`);
      - the empty-set floor `total > 0` as a range-checked `TPOS = TOTAL_WEIGHT − 1 ∈ [0, 2^128)`;
      - the ROUND binding (`ROUND_OK = 1` — cross-round) and the ERA binding (`ERA_OK = 1` —
        stale-authority-set) as forced boolean gates.
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1`):
      - `ED_OK`      — the aggregate Ed25519 verify over the counted authorities + the precommit message
        `(targetHash, targetNumber, round, setId)`,
      - `AUTHSET_OK` — the derived authority set binds to the pinned WS anchor root (the
        denominator-shrink pin).

The residual is HONEST and NAMED: in THIS slice the two crypto carriers are asserted, not re-derived
in-circuit, so the STARK proves the TALLY/THRESHOLD/ROUND/ERA LOGIC is correct GIVEN the Ed25519 and
authority-set results — precisely `midVerifyDecision`'s guarantee, now portable. Putting Ed25519 and the
authority-set fold in-AIR (or as their own verified sub-proofs the AIR `ProofBind`s against) is the next
iteration; the public-input anchors below are the hook it attaches to. Also named: the counted
`SIGNED_WEIGHT` distinct-authority tally is a trusted projection (the deployed node's tally), the same
posture as the ETH `PC` / Solana `ROOTED_STK` participant count.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0] = ANCHOR_ROOT`  — the pinned WS authority-set root (the governance trust anchor the AUTHSET_OK
                         carrier is a compare against). The trust root the proof is relative to.
`PI[1] = TARGET_ROOT`  — the claimed finalized block/state hash B (what a proof-of-holdings later opens
                         against).
`PI[2] = ROUND`        — the GRANDPA round R the commit is for.
`PI[3] = ERA`          — the authority-set id (era) E the finality is claimed under (the ERA_OK gate binds
                         the counted precommits + the anchored set id to this).

These ride as published witness columns pinned to the public inputs (`.piBinding`). NOT-YET-CLOSED
(named residual, identical to the other slices): the anchors are published but not yet arithmetically
bound to the carrier bits (that binding IS the in-AIR-crypto iteration — `ED_OK` derived from the
precommit message built on `TARGET_ROOT`+`ROUND`+`ERA`, `AUTHSET_OK` derived from the set fold into
`ANCHOR_ROOT`).

## Axiom hygiene
Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`midLcAir_sound` / `midLcAir_no_forgery` refinement to `midVerifyDecision` / `mid_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Bridge.LightClientMidnight

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Dregg2.Circuit.Emit.LightClientMidnightAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientMidnight

/-! ## §1 — the trace column layout (one logical row). Columns 0..7 are the six verify-logic projections
`midVerifyDecision` composes over (two crypto carriers) plus the two range slacks; columns 8..11 are the
published PUBLIC anchors. -/

/-- Counted signed authority weight; range-bounded via the quorum slack. Witness. -/
def SIGNED_WEIGHT : Nat := 0
/-- Total authority weight; the > 2/3 denominator, forced `> 0` via the `TPOS` slack. Witness. -/
def TOTAL_WEIGHT : Nat := 1
/-- The quorum SLACK `3·SIGNED_WEIGHT − 2·TOTAL_WEIGHT − 1`; the range tooth forces it into `[0, 2^128)`,
i.e. `2·total < 3·signed` (STRICT — exactly-2/3 gives `WDIFF = −1`, UNSAT). Witness. -/
def WDIFF : Nat := 2
/-- The total-positivity SLACK `TOTAL_WEIGHT − 1`; the range tooth forces `total ≥ 1`. -/
def TPOS : Nat := 3
/-- **CARRIER** — the aggregate Ed25519 verify RESULT (counted authorities signed the precommit message);
forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 4
/-- **CARRIER** — the authority-set-root compare RESULT (derived set binds the pinned WS anchor root);
forced `= 1`. NAMED carrier (the denominator-shrink pin). Witness. -/
def AUTHSET_OK : Nat := 5
/-- **GATE** — the ROUND binding (every counted precommit names the claimed round R — cross-round); forced
`= 1`. -/
def ROUND_OK : Nat := 6
/-- **GATE** — the ERA binding (the claimed set id equals the anchored era AND every counted precommit
carries it — stale-authority-set); forced `= 1`. -/
def ERA_OK : Nat := 7

/-- **PUBLIC ANCHOR** — the pinned WS authority-set root (the governance trust anchor). PI-bound. -/
def ANCHOR_ROOT : Nat := 8
/-- **PUBLIC ANCHOR** — the claimed finalized block/state root B. PI-bound. -/
def TARGET_ROOT : Nat := 9
/-- **PUBLIC ANCHOR** — the GRANDPA round R. PI-bound. -/
def ROUND_COL : Nat := 10
/-- **PUBLIC ANCHOR** — the authority-set id (era) E. PI-bound. -/
def ERA_COL : Nat := 11

/-- Total main-trace width: 8 logic columns + 4 published anchors. -/
def MID_LC_WIDTH : Nat := 12

/-- PI slot 0: the pinned WS anchor root. -/
def PI_ANCHOR_ROOT : Nat := 0
/-- PI slot 1: the claimed finalized target root. -/
def PI_TARGET_ROOT : Nat := 1
/-- PI slot 2: the GRANDPA round. -/
def PI_ROUND : Nat := 2
/-- PI slot 3: the authority-set id (era). -/
def PI_ERA : Nat := 3
/-- Number of public inputs. -/
def PI_COUNT : Nat := 4

/-- The range width — a u128 tally width comfortably above the u64 authority-weight sums; `3·signed −
2·total − 1 ∈ [0, 2^128)` and `total − 1 ∈ [0, 2^128)` for any real weight distribution; the interval's
floor `≥ 0` is the load-bearing strict > 2/3 + `total > 0` tooth. -/
def RANGE_BITS : Nat := 128

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials). -/

/-- `WDIFF − 3·SIGNED_WEIGHT + 2·TOTAL_WEIGHT + 1` — zero iff `WDIFF = 3·signed − 2·total − 1` (the STRICT
quorum slack). -/
def wDiffBody : EmittedExpr :=
  .add (.add (.add (.var WDIFF) (.mul (.const (-3)) (.var SIGNED_WEIGHT)))
    (.mul (.const 2) (.var TOTAL_WEIGHT))) (.const 1)
/-- `TPOS − TOTAL_WEIGHT + 1` — zero iff `TPOS = total − 1` (the total-positivity slack). -/
def tPosBody : EmittedExpr :=
  .add (.add (.var TPOS) (.mul (.const (-1)) (.var TOTAL_WEIGHT))) (.const 1)
/-- `ED_OK − 1` — zero iff the Ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `AUTHSET_OK − 1` — zero iff the authority-set-root carrier bit is set. -/
def authsetBody : EmittedExpr := .add (.var AUTHSET_OK) (.const (-1))
/-- `ROUND_OK − 1` — zero iff the round-binding gate bit is set. -/
def roundBody : EmittedExpr := .add (.var ROUND_OK) (.const (-1))
/-- `ERA_OK − 1` — zero iff the era-binding gate bit is set. -/
def eraBody : EmittedExpr := .add (.var ERA_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor. -/

def wDiffGate : VmConstraint2 := .base (.gate wDiffBody)
/-- The quorum range tooth: `WDIFF ∈ [0, 2^RANGE_BITS)` — the strict > 2/3 boundary, wrap-free. -/
def wRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var WDIFF]⟩
def tPosGate : VmConstraint2 := .base (.gate tPosBody)
/-- The total-positivity range tooth: `TPOS ∈ [0, 2^RANGE_BITS)` — forces `total ≥ 1`. -/
def tPosRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var TPOS]⟩
def edGate : VmConstraint2 := .base (.gate edBody)
def authsetGate : VmConstraint2 := .base (.gate authsetBody)
def roundGate : VmConstraint2 := .base (.gate roundBody)
def eraGate : VmConstraint2 := .base (.gate eraBody)
/-- Published-anchor pin: the pinned WS anchor root is `PI[0]`. -/
def anchorRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ANCHOR_ROOT PI_ANCHOR_ROOT)
/-- Published-anchor pin: the claimed finalized target root is `PI[1]`. -/
def targetRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first TARGET_ROOT PI_TARGET_ROOT)
/-- Published-anchor pin: the GRANDPA round is `PI[2]`. -/
def roundPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ROUND_COL PI_ROUND)
/-- Published-anchor pin: the era (set id) is `PI[3]`. -/
def eraPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ERA_COL PI_ERA)

/-- **`midLcVerifyDesc`** — the Midnight GRANDPA verify-decision as an emitted IR-v2 AIR. PIs
`[anchor_root, target_root, round, era]`; the six verify-logic projections + two range slacks as hidden
witnesses, the two crypto results as carrier bits. One range table (`TID_range`) carries both the quorum
tooth and the total-positivity tooth. -/
def midLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-midnight-lightclient-verify::v1"
  , traceWidth  := MID_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef RANGE_BITS]
  , constraints := [wDiffGate, wRangeLookup, tPosGate, tPosRangeLookup, edGate, authsetGate,
                    roundGate, eraGate, anchorRootPin, targetRootPin, roundPin, eraPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `wDiffBody = 0 ↔ WDIFF = 3·SIGNED_WEIGHT − 2·TOTAL_WEIGHT − 1`. -/
theorem wDiff_body_zero_iff (a : Assignment) :
    wDiffBody.eval a = 0 ↔ a WDIFF = 3 * a SIGNED_WEIGHT - 2 * a TOTAL_WEIGHT - 1 := by
  simp only [wDiffBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `tPosBody = 0 ↔ TPOS = TOTAL_WEIGHT − 1`. -/
theorem tPos_body_zero_iff (a : Assignment) :
    tPosBody.eval a = 0 ↔ a TPOS = a TOTAL_WEIGHT - 1 := by
  simp only [tPosBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `edBody = 0 ↔ ED_OK = 1`. -/
theorem ed_body_zero_iff (a : Assignment) : edBody.eval a = 0 ↔ a ED_OK = 1 := by
  simp only [edBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `authsetBody = 0 ↔ AUTHSET_OK = 1`. -/
theorem authset_body_zero_iff (a : Assignment) : authsetBody.eval a = 0 ↔ a AUTHSET_OK = 1 := by
  simp only [authsetBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `roundBody = 0 ↔ ROUND_OK = 1`. -/
theorem round_body_zero_iff (a : Assignment) : roundBody.eval a = 0 ↔ a ROUND_OK = 1 := by
  simp only [roundBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `eraBody = 0 ↔ ERA_OK = 1`. -/
theorem era_body_zero_iff (a : Assignment) : eraBody.eval a = 0 ↔ a ERA_OK = 1 := by
  simp only [eraBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate + the REFINEMENT to
`midVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and the two slacks lie in
the range interval `[0, 2^RANGE_BITS)` (the denotation `range_row_mem_iff` connects the emitted lookups
to). The published-anchor pins are the addressing layer, orthogonal to the logic. -/
def airAccepts (a : Assignment) : Prop :=
  wDiffBody.eval a = 0
  ∧ (0 ≤ a WDIFF ∧ a WDIFF < (2 : ℤ) ^ RANGE_BITS)
  ∧ tPosBody.eval a = 0
  ∧ (0 ≤ a TPOS ∧ a TPOS < (2 : ℤ) ^ RANGE_BITS)
  ∧ edBody.eval a = 0
  ∧ authsetBody.eval a = 0
  ∧ roundBody.eval a = 0
  ∧ eraBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `midVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two weights as
felts, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic gates accept, then the
exported scalar decision `midVerifyDecision` accepts. The quorum range floor discharges the STRICT > 2/3
threshold; the `TPOS` floor discharges `total > 0`. -/
theorem midLcAir_sound (a : Assignment)
    (signedW totalW : Nat) (edB authsetB roundB eraB : Bool)
    (hr : a SIGNED_WEIGHT = (signedW : ℤ)) (ht : a TOTAL_WEIGHT = (totalW : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authsetB then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundB then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    midVerifyDecision signedW totalW edB authsetB roundB eraB = true := by
  obtain ⟨hqB, ⟨hq0, _hqlt⟩, htB, ⟨ht0, _htlt⟩, hedB, hauthsetB, hroundB, heraB⟩ := hacc
  -- Threshold: WDIFF = 3·signed − 2·total − 1 ≥ 0 ⟹ 2·total < 3·signed (STRICT).
  have hqeq : a WDIFF = 3 * a SIGNED_WEIGHT - 2 * a TOTAL_WEIGHT - 1 := (wDiff_body_zero_iff a).mp hqB
  have hthrZ : (2 : ℤ) * (totalW : ℤ) < 3 * (signedW : ℤ) := by
    have := hq0; rw [hqeq, hr, ht] at this; linarith
  have hthr : 2 * totalW < 3 * signedW := by exact_mod_cast hthrZ
  -- Total positivity: TPOS = total − 1 ≥ 0 ⟹ total ≥ 1.
  have hteq : a TPOS = a TOTAL_WEIGHT - 1 := (tPos_body_zero_iff a).mp htB
  have hposZ : (1 : ℤ) ≤ (totalW : ℤ) := by
    have := ht0; rw [hteq, ht] at this; linarith
  have hpos : 0 < totalW := by
    have : 1 ≤ totalW := by exact_mod_cast hposZ
    omega
  -- Carrier / gate bits.
  have hedTrue : edB = true := by
    have h : a ED_OK = 1 := (ed_body_zero_iff a).mp hedB
    rw [hed] at h; cases edB with | true => rfl | false => simp at h
  have hauthsetTrue : authsetB = true := by
    have h : a AUTHSET_OK = 1 := (authset_body_zero_iff a).mp hauthsetB
    rw [hauthset] at h; cases authsetB with | true => rfl | false => simp at h
  have hroundTrue : roundB = true := by
    have h : a ROUND_OK = 1 := (round_body_zero_iff a).mp hroundB
    rw [hround] at h; cases roundB with | true => rfl | false => simp at h
  have heraTrue : eraB = true := by
    have h : a ERA_OK = 1 := (era_body_zero_iff a).mp heraB
    rw [hera] at h; cases eraB with | true => rfl | false => simp at h
  -- Assemble.
  unfold midVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hedTrue⟩, hauthsetTrue⟩, hroundTrue⟩, heraTrue⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Midnight GRANDPA-validity (no-forgery, routed through
the emitted AIR).** GIVEN the named authority-set CR carrier (`hcr`), if a row `a` reads update `u`'s true
projections under pinned anchor `ts` and the emitted verify-logic gates accept, then `u` is
Midnight-GRANDPA-VALID relative to `ts` — a STRICT > 2/3 subset of the authority weight, each authority
genuinely signed a precommit for the target at the claimed round under the anchored era, the denominator
pinned to the WS anchor. So a STARK proving `midLcVerifyDesc` carries `mid_no_forgery`: the portable,
trustless proof of Midnight GRANDPA finality. -/
theorem midLcAir_no_forgery (L : MidLeaf) (hcr : L.authSetCR)
    (ts : MidTrustedState L) (u : MidUpdate L) (a : Assignment)
    (hr : a SIGNED_WEIGHT = (signedWeight L u : ℤ)) (ht : a TOTAL_WEIGHT = (totalWeight L u : ℤ))
    (hed : a ED_OK = (if edOk L u then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authSetOk L ts u then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundOk L u then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraOk L ts u then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    MidValidAt L ts u := by
  have hdec := midLcAir_sound a (signedWeight L u) (totalWeight L u)
    (edOk L u) (authSetOk L ts u) (roundOk L u) (eraOk L ts u)
    hr ht hed hauthset hround hera hacc
  exact midVerifyDecision_no_forgery L hcr ts u hdec

/-- **Completeness of the range teeth (the honest prover CAN fill the slacks).** For any decision-
accepting projections whose counted weight fits the u128 tally window (`3·signed < 2^128` — the `total`
bound follows, since `2·total < 3·signed`), an honest row that fills `WDIFF = 3·signed − 2·total − 1`,
`TPOS = total − 1`, and the carrier/gate bits with the true results is accepted by the emitted logic. The
non-vacuity partner of soundness. -/
theorem midLcAir_complete (a : Assignment)
    (signedW totalW : Nat) (edB authsetB roundB eraB : Bool)
    (hr : a SIGNED_WEIGHT = (signedW : ℤ)) (ht : a TOTAL_WEIGHT = (totalW : ℤ))
    (hq : a WDIFF = 3 * (signedW : ℤ) - 2 * (totalW : ℤ) - 1)
    (hp : a TPOS = (totalW : ℤ) - 1)
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hauthset : a AUTHSET_OK = (if authsetB then (1 : ℤ) else 0))
    (hround : a ROUND_OK = (if roundB then (1 : ℤ) else 0))
    (hera : a ERA_OK = (if eraB then (1 : ℤ) else 0))
    (hrw : 3 * (signedW : ℤ) < (2 : ℤ) ^ RANGE_BITS)
    (hdec : midVerifyDecision signedW totalW edB authsetB roundB eraB = true) :
    airAccepts a := by
  unfold midVerifyDecision at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨hpos, hthr⟩, hedB⟩, hauthsetB⟩, hroundB⟩, heraB⟩ := hdec
  have hthrZ : (2 : ℤ) * (totalW : ℤ) < 3 * (signedW : ℤ) := by exact_mod_cast hthr
  have hposZ : (1 : ℤ) ≤ (totalW : ℤ) := by exact_mod_cast hpos
  have h0t : (0 : ℤ) ≤ (totalW : ℤ) := by positivity
  have h0r : (0 : ℤ) ≤ (signedW : ℤ) := by positivity
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [wDiff_body_zero_iff, hr, ht, hq]
  · rw [hq]; omega
  · rw [hq]; linarith
  · rw [tPos_body_zero_iff, ht, hp]
  · rw [hp]; linarith
  · rw [hp]; linarith
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [authset_body_zero_iff, hauthset]; simp [hauthsetB]
  · rw [round_body_zero_iff, hround]; simp [hroundB]
  · rw [era_body_zero_iff, hera]; simp [heraB]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on either
-- side breaks this `#guard`). Captured from the hbox build's `emitVmJson2` emission.
#guard emitVmJson2 midLcVerifyDesc ==
  "{\"name\":\"dregg-midnight-lightclient-verify::v1\",\"ir\":2,\"trace_width\":12,\"public_input_count\":4,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":128}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":2}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":3}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins (robust; a layout drift moves these).
#guard midLcVerifyDesc.traceWidth == MID_LC_WIDTH
#guard midLcVerifyDesc.piCount == PI_COUNT
#guard midLcVerifyDesc.constraints.length == 12
#guard midLcVerifyDesc.tables.length == 1
-- The two crypto carriers are real trace columns, and none is PI-bound (the results ride hidden).
#guard ED_OK < MID_LC_WIDTH
#guard AUTHSET_OK < MID_LC_WIDTH

/-! ## §7 — NON-VACUITY: the emitted teeth DISCRIMINATE (the strict > 2/3 boundary + the closed holes,
in-AIR). -/

-- Quorum-slack identity: signed=3,total=3 ⇒ WDIFF=2 vanishes; a mismatched WDIFF is refused.
#guard decide (wDiffBody.eval (fun i => if i = WDIFF then 2 else if i = SIGNED_WEIGHT then 3
  else if i = TOTAL_WEIGHT then 3 else 0) = 0)
#guard decide (¬ (wDiffBody.eval (fun i => if i = WDIFF then 0 else if i = SIGNED_WEIGHT then 3
  else if i = TOTAL_WEIGHT then 3 else 0) = 0))
-- THE STRICT > 2/3 BOUNDARY, in-AIR: the just-over signed=3 of total=3 slack (3·3−2·3−1 = 2) is in
-- range; the exactly-2/3 signed=2 of total=3 slack (3·2−2·3−1 = −1) is NOT — the strict accept/reject
-- tooth (GRANDPA rejects exactly-2/3).
example : ([2] : List ℤ) ∈ rangeRows RANGE_BITS := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
example : ¬ (([-1] : List ℤ) ∈ rangeRows RANGE_BITS) := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
-- Total-positivity: total=1 ⇒ TPOS=0 in range; total=0 ⇒ TPOS=−1 out (empty-set reject).
example : ([0] : List ℤ) ∈ rangeRows RANGE_BITS := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
example : ¬ (([-1] : List ℤ) ∈ rangeRows RANGE_BITS) := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
-- Carriers / gates: a set bit accepts; a cleared (forged / cross-round / stale-era) bit is refused.
#guard decide (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0)
#guard decide (¬ (edBody.eval (fun _ => 0) = 0))
#guard decide (authsetBody.eval (fun i => if i = AUTHSET_OK then 1 else 0) = 0)
#guard decide (¬ (authsetBody.eval (fun _ => 0) = 0))
#guard decide (roundBody.eval (fun i => if i = ROUND_OK then 1 else 0) = 0)
#guard decide (¬ (roundBody.eval (fun _ => 0) = 0))
#guard decide (eraBody.eval (fun i => if i = ERA_OK then 1 else 0) = 0)
#guard decide (¬ (eraBody.eval (fun _ => 0) = 0))

/-! ## §8 — axiom hygiene. -/

#assert_axioms wDiff_body_zero_iff
#assert_axioms tPos_body_zero_iff
#assert_axioms midLcAir_sound
#assert_axioms midLcAir_no_forgery
#assert_axioms midLcAir_complete

#print axioms midLcAir_sound
#print axioms midLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientMidnightAir
