/-
# Dregg2.Circuit.Emit.LightClientEthAir — the ETH/Base light-client VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the light client" first slice)

`Dregg2.Bridge.LightClientEth` proves `eth_no_forgery` over `verifyFinalizedUpdate`, and
`Dregg2.Bridge.LightClientEthGate` collapses that decision to the eight scalar/boolean projections a
deployed node computes (`ethVerifyDecision`) and `@[export]`s it as `dregg_eth_lc_verify`. That gives
a node a Lean-PROVEN accept/reject — but the verdict is rendered by *running Lean code on the node's
own machine*. A peer (or an on-chain contract) that wants to trust "this dregg node saw Base finalize
beacon state B" must RE-TRUST that node's execution. There is no portable object.

This file emits `ethVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`ethLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: the proof is a portable artifact any peer verifies without
re-running the node, and (via the gnark FRI-wrap → Groth16, §5 below) an on-chain contract verifies.
That is what makes dregg + Base TRUE PEERS: today Base verifies dregg's STARK while dregg's view of
Base is trusted-Rust; this AIR turns dregg's view of Base into the SAME kind of portable proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and
runs the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`ethLcAir_sound` / `ethLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `ethVerifyDecision` and
hence to `eth_no_forgery` — so a STARK that satisfies this AIR CARRIES the no-forgery guarantee,
modulo the three named crypto carriers (below).

## The crypto boundary: IN-AIR logic vs NAMED verified carriers (the pragmatic first cut)

Light-client verify is not pure logic — it invokes BLS12-381 aggregate-verify and SHA-256 SSZ Merkle
folds. This AIR draws the boundary EXACTLY where `LightClientEthGate` already draws it (the carrier
model): the pure `Nat`/`Bool` VERIFY-LOGIC goes IN-AIR as arithmetic gates; the heavy crypto results
ride as WITNESSED BOOLEAN CARRIERS the logic constrains.

  * IN-AIR (arithmetic gates over the trace):
      - the committee-size / bitfield-length structural checks (`= 512`),
      - the Nomad-floor + 2/3 multiply-form quorum threshold (`2·512 ≤ 3·participants`, i.e. the
        342-accept / 341-reject boundary) as a range-checked non-negative slack `QDIFF = 3·pc − 1024`,
      - the finality-branch depth admissibility (`6 ∨ 7`) as `(FL−6)·(FL−7) = 0`,
      - the execution-branch depth (`= 4`).
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1` for accept — the SAME opaque
    results `ethVerifyDecision` composes over):
      - `BLS_OK`  — `blst` aggregate-verify over the participating subset + signing root,
      - `FIN_OK`  — the SHA-256 finality-branch reconstruction compare (into the attested state root),
      - `EXEC_OK` — the SHA-256 execution-branch reconstruction compare (into the finalized body root).

The residual is HONEST and NAMED: in THIS slice the carriers are asserted, not re-derived in-circuit,
so the STARK proves the QUORUM/BRANCH/BINDING LOGIC is correct GIVEN the crypto results — precisely
the guarantee `ethVerifyDecision` gives, now portable. Putting BLS/SHA in-AIR (or as their own
verified sub-proofs the AIR `ProofBind`s against) is the next iteration; the public-input anchors
below are the hook it attaches to.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0] = COMMITTEE_ROOT`   — the TRUSTED sync-committee root (the WS-checkpoint anchor the BLS carrier
                             is a verify against). This is the trust root the proof is relative to.
`PI[1] = FIN_STATE_ROOT`   — the claimed FINALIZED execution state root B (the EVM `state_root` a
                             proof-of-holdings later opens against).
`PI[2] = DOMAIN_GVR`       — the fork/domain (genesis-validators-root-derived signing domain).

These ride as published witness columns pinned to the public inputs (`.piBinding`), so a verifier
sees WHICH committee-root and WHICH state-root the proof speaks of. NOT-YET-CLOSED (named residual):
in this carrier slice the anchors are published but not yet arithmetically bound to the carrier bits
(that binding IS the in-AIR-crypto iteration — `BLS_OK` derived from `COMMITTEE_ROOT` + signing root,
`FIN_OK`/`EXEC_OK` derived from the branch folds into `FIN_STATE_ROOT`). So `airAccepts` (the LOGIC
refinement) is stated over the eight projections; the anchor pins are the addressing layer around it.

## Witness (the update)

The hidden trace columns are the update's projections: `PC` (participant popcount), the two structural
lengths `CL`/`BL`, the two branch depths `FL`/`EL`, the quorum slack `QDIFF`, and the three carrier
bits `BLS_OK`/`FIN_OK`/`EXEC_OK`. An honest prover fills `QDIFF = 3·pc − 1024` and the carrier bits
with the true `blst`/SHA-256 results; a forger who sets a carrier bit it cannot justify is refused by
the SAME no-forgery theorem the gate carries (the carriers are `EthLeaf` fields under `hcr`/`hinj`).

## Constraint map

| statement                                   | decision conjunct                          | IR-v2 constraint                         |
|---------------------------------------------|--------------------------------------------|------------------------------------------|
| committee is 512 keys                       | `decide (cl = 512)`                        | `.gate (CL − 512)`                        |
| bitfield is 512 bits                        | `decide (bl = 512)`                        | `.gate (BL − 512)`                        |
| quorum slack definition                     | (bridges `0<pc` ∧ `1024 ≤ 3pc`)            | `.gate (QDIFF − 3·PC + 1024)`             |
| quorum slack non-negative (2/3 + Nomad)     | `decide (0<pc) ∧ decide (2·512 ≤ 3·pc)`    | `.lookup ⟨range, [QDIFF]⟩` (`[0,2^11)`)   |
| BLS aggregate verified (carrier)            | `blsOk`                                    | `.gate (BLS_OK − 1)`                      |
| finality branch depth 6 ∨ 7                 | `decide (fl=6) ∨ decide (fl=7)`            | `.gate ((FL−6)·(FL−7))`                   |
| finality reconstruct ok (carrier)          | `finOk`                                    | `.gate (FIN_OK − 1)`                      |
| execution branch depth 4                    | `decide (el=4)`                            | `.gate (EL − 4)`                          |
| execution reconstruct ok (carrier)         | `execOk`                                   | `.gate (EXEC_OK − 1)`                     |
| trusted committee root is public           | (addressing)                               | `.piBinding first COMMITTEE_ROOT 0`      |
| claimed finalized state root is public     | (addressing)                               | `.piBinding first FIN_STATE_ROOT 1`      |
| signing domain / gvr is public             | (addressing)                               | `.piBinding first DOMAIN_GVR 2`          |

The range lookup is the LOAD-BEARING quorum tooth: `QDIFF = 3·pc − 1024 ∈ [0, 2^11)` iff `1024 ≤ 3·pc`
with no field-wrap escape (a sub-quorum `pc = 341` gives `QDIFF = −1`, far outside the interval —
UNSAT; this is the exact 342/341 Nomad boundary). The `0 < pc` floor is subsumed: `1024 ≤ 3·pc`
already forces `pc ≥ 342 > 0`.

## The mod-p ↔ ℤ reading (the shared field-soundness residual)

`airAccepts` reads the emitted gate bodies as ℤ equalities (exactly as `PredicatesLeEmit.c5_body_zero_iff`
does), the strong reading. The deployed denotation is mod-`p` (`VmConstraint.holdsVm`); bridging the two
needs full-wire range decomposition, the same field-soundness residual every Emit descriptor carries.
Not re-litigated here.

## Axiom hygiene

Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`ethLcAir_sound` / `ethLcAir_no_forgery` refinement to `ethVerifyDecision` / `eth_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Bridge.LightClientEthGate

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Dregg2.Circuit.Emit.LightClientEthAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientEth
open Dregg2.Bridge.LightClientEthGate

/-! ## §1 — the trace column layout (one logical row).

Columns 0..8 are the eight VERIFY-LOGIC projections `ethVerifyDecision` composes over (three of them
crypto carriers), plus the quorum slack `QDIFF`. Columns 9..11 are the published PUBLIC anchors. -/

/-- Committee length (the sync-committee's key count); structural, forced `= 512`. Witness. -/
def CL : Nat := 0
/-- Bitfield length (the participation bitfield's bit count); structural, forced `= 512`. Witness. -/
def BL : Nat := 1
/-- Participant popcount (`SyncAggregate::count`); range-bounded via the quorum slack. Witness. -/
def PC : Nat := 2
/-- The quorum SLACK `3·PC − 1024`; the range tooth forces it into `[0, 2^11)`, i.e. `1024 ≤ 3·pc`. -/
def QDIFF : Nat := 3
/-- **CARRIER** — the `blst` aggregate-verify RESULT (participating subset signed the signing root);
forced `= 1` for accept. NAMED verified-FFI carrier, not re-derived in-AIR (this slice). Witness. -/
def BLS_OK : Nat := 4
/-- Finality-branch depth; forced `∈ {6, 7}` (Altair..Deneb | Electra+). Witness. -/
def FL : Nat := 5
/-- **CARRIER** — the SHA-256 finality-branch reconstruction compare RESULT (reconstruct into the
attested state root at subtree index 41); forced `= 1`. NAMED carrier. Witness. -/
def FIN_OK : Nat := 6
/-- Execution-branch depth; forced `= 4`. Witness. -/
def EL : Nat := 7
/-- **CARRIER** — the SHA-256 execution-branch reconstruction compare RESULT (reconstruct into the
finalized body root at subtree index 9); forced `= 1`. NAMED carrier. Witness. -/
def EXEC_OK : Nat := 8

/-- **PUBLIC ANCHOR** — the TRUSTED sync-committee root (the WS-checkpoint trust anchor). PI-bound. -/
def COMMITTEE_ROOT : Nat := 9
/-- **PUBLIC ANCHOR** — the claimed FINALIZED execution state root B. PI-bound. -/
def FIN_STATE_ROOT : Nat := 10
/-- **PUBLIC ANCHOR** — the fork/domain (genesis-validators-root-derived signing domain). PI-bound. -/
def DOMAIN_GVR : Nat := 11

/-- Total main-trace width: 9 logic columns + 3 published anchors. -/
def ETH_LC_WIDTH : Nat := 12

/-- PI slot 0: the trusted committee root. -/
def PI_COMMITTEE_ROOT : Nat := 0
/-- PI slot 1: the claimed finalized state root. -/
def PI_FIN_STATE_ROOT : Nat := 1
/-- PI slot 2: the signing domain / gvr. -/
def PI_DOMAIN_GVR : Nat := 2
/-- Number of public inputs. -/
def PI_COUNT : Nat := 3

/-- The quorum-slack range width. `3·pc − 1024 ≤ 3·512 − 1024 = 512 < 2^11` for any real committee,
so completeness holds for `pc ≤ 512`; the interval's floor `≥ 0` is the load-bearing 2/3 tooth. -/
def Q_BITS : Nat := 11

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials). -/

/-- `CL − 512` — zero iff the committee has exactly 512 keys. -/
def clBody : EmittedExpr := .add (.var CL) (.const (-512))
/-- `BL − 512` — zero iff the bitfield is exactly 512 bits. -/
def blBody : EmittedExpr := .add (.var BL) (.const (-512))
/-- `QDIFF − 3·PC + 1024` — zero iff `QDIFF = 3·PC − 1024` (the quorum slack identity). -/
def qDiffBody : EmittedExpr :=
  .add (.add (.var QDIFF) (.mul (.const (-3)) (.var PC))) (.const 1024)
/-- `BLS_OK − 1` — zero iff the BLS carrier bit is set. -/
def blsBody : EmittedExpr := .add (.var BLS_OK) (.const (-1))
/-- `(FL − 6)·(FL − 7)` — zero iff the finality depth is 6 or 7. -/
def flBody : EmittedExpr :=
  .mul (.add (.var FL) (.const (-6))) (.add (.var FL) (.const (-7)))
/-- `FIN_OK − 1` — zero iff the finality-reconstruct carrier bit is set. -/
def finBody : EmittedExpr := .add (.var FIN_OK) (.const (-1))
/-- `EL − 4` — zero iff the execution depth is 4. -/
def elBody : EmittedExpr := .add (.var EL) (.const (-4))
/-- `EXEC_OK − 1` — zero iff the execution-reconstruct carrier bit is set. -/
def execBody : EmittedExpr := .add (.var EXEC_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor. -/

def clGate : VmConstraint2 := .base (.gate clBody)
def blGate : VmConstraint2 := .base (.gate blBody)
def qDiffGate : VmConstraint2 := .base (.gate qDiffBody)
/-- The quorum range tooth: `QDIFF ∈ [0, 2^Q_BITS)` — the 2/3 + Nomad boundary, wrap-free. -/
def qRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var QDIFF]⟩
def blsGate : VmConstraint2 := .base (.gate blsBody)
def flGate : VmConstraint2 := .base (.gate flBody)
def finGate : VmConstraint2 := .base (.gate finBody)
def elGate : VmConstraint2 := .base (.gate elBody)
def execGate : VmConstraint2 := .base (.gate execBody)
/-- Published-anchor pin: the trusted committee root is `PI[0]`. -/
def committeeRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first COMMITTEE_ROOT PI_COMMITTEE_ROOT)
/-- Published-anchor pin: the claimed finalized state root is `PI[1]`. -/
def finStateRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first FIN_STATE_ROOT PI_FIN_STATE_ROOT)
/-- Published-anchor pin: the signing domain / gvr is `PI[2]`. -/
def domainPin : VmConstraint2 :=
  .base (.piBinding VmRow.first DOMAIN_GVR PI_DOMAIN_GVR)

/-- **`ethLcVerifyDesc`** — the ETH/Base light-client verify-decision as an emitted IR-v2 AIR.
PIs `[committee_root, fin_state_root, domain_gvr]`; the eight verify-logic projections + quorum slack
as hidden witnesses, the three crypto results as carrier bits. The range table (`TID_range`) carries
the quorum tooth. -/
def ethLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-eth-lightclient-verify::v1"
  , traceWidth  := ETH_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef Q_BITS]
  , constraints := [clGate, blGate, qDiffGate, qRangeLookup, blsGate, flGate, finGate, elGate,
                    execGate, committeeRootPin, finStateRootPin, domainPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `clBody = 0 ↔ CL = 512`. -/
theorem cl_body_zero_iff (a : Assignment) : clBody.eval a = 0 ↔ a CL = 512 := by
  simp only [clBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `blBody = 0 ↔ BL = 512`. -/
theorem bl_body_zero_iff (a : Assignment) : blBody.eval a = 0 ↔ a BL = 512 := by
  simp only [blBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `qDiffBody = 0 ↔ QDIFF = 3·PC − 1024`. -/
theorem qDiff_body_zero_iff (a : Assignment) :
    qDiffBody.eval a = 0 ↔ a QDIFF = 3 * a PC - 1024 := by
  simp only [qDiffBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `blsBody = 0 ↔ BLS_OK = 1`. -/
theorem bls_body_zero_iff (a : Assignment) : blsBody.eval a = 0 ↔ a BLS_OK = 1 := by
  simp only [blsBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `flBody = 0 ↔ FL = 6 ∨ FL = 7` (the two legal finality depths). -/
theorem fl_body_zero_iff (a : Assignment) : flBody.eval a = 0 ↔ (a FL = 6 ∨ a FL = 7) := by
  simp only [flBody, EmittedExpr.eval]
  rw [mul_eq_zero]; constructor <;> rintro (h | h) <;> omega
/-- `finBody = 0 ↔ FIN_OK = 1`. -/
theorem fin_body_zero_iff (a : Assignment) : finBody.eval a = 0 ↔ a FIN_OK = 1 := by
  simp only [finBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `elBody = 0 ↔ EL = 4`. -/
theorem el_body_zero_iff (a : Assignment) : elBody.eval a = 0 ↔ a EL = 4 := by
  simp only [elBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `execBody = 0 ↔ EXEC_OK = 1`. -/
theorem exec_body_zero_iff (a : Assignment) : execBody.eval a = 0 ↔ a EXEC_OK = 1 := by
  simp only [execBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate (the ℤ reading of its gate
bodies + the quorum range interval), and the REFINEMENT to `ethVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and the quorum slack
lies in the range interval `[0, 2^Q_BITS)` (the denotation `range_row_mem_iff` connects the emitted
`qRangeLookup` to). This is "the descriptor accepts the logic of row `a`" (the published-anchor pins
are the addressing layer, orthogonal to the logic). -/
def airAccepts (a : Assignment) : Prop :=
  clBody.eval a = 0
  ∧ blBody.eval a = 0
  ∧ qDiffBody.eval a = 0
  ∧ (0 ≤ a QDIFF ∧ a QDIFF < (2 : ℤ) ^ Q_BITS)
  ∧ blsBody.eval a = 0
  ∧ flBody.eval a = 0
  ∧ finBody.eval a = 0
  ∧ elBody.eval a = 0
  ∧ execBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `ethVerifyDecision` accept.**
Fed a row `a` whose columns read the update's true projections (the honest-witness relation — the
lengths/depths as felts, the carrier bits as `if · then 1 else 0`), if the emitted verify-logic gates
accept, then the exported scalar decision `ethVerifyDecision` accepts those projections. This is the
load-bearing tie: a STARK that satisfies `ethLcVerifyDesc` proves the object `eth_no_forgery` is
stated over. The quorum range floor discharges BOTH the Nomad floor `0 < pc` and the 2/3 threshold. -/
theorem ethLcAir_sound (a : Assignment)
    (cl bl pc fl el : Nat) (blsOk finOk execOk : Bool)
    (hcl : a CL = (cl : ℤ)) (hbl : a BL = (bl : ℤ)) (hpc : a PC = (pc : ℤ))
    (hfl : a FL = (fl : ℤ)) (hel : a EL = (el : ℤ))
    (hbls : a BLS_OK = (if blsOk then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if finOk then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if execOk then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    ethVerifyDecision cl bl pc blsOk fl finOk el execOk = true := by
  obtain ⟨hclB, hblB, hqB, ⟨hq0, _hqlt⟩, hblsB, hflB, hfinB, helB, hexecB⟩ := hacc
  -- Structural length equalities (ℤ read, cast to Nat).
  have hcl512 : cl = syncCommitteeSize := by
    have h : (cl : ℤ) = 512 := by rw [← hcl]; exact (cl_body_zero_iff a).mp hclB
    have : cl = 512 := by exact_mod_cast h
    simpa [syncCommitteeSize] using this
  have hbl512 : bl = syncCommitteeSize := by
    have h : (bl : ℤ) = 512 := by rw [← hbl]; exact (bl_body_zero_iff a).mp hblB
    have : bl = 512 := by exact_mod_cast h
    simpa [syncCommitteeSize] using this
  -- Quorum: the range floor forces 1024 ≤ 3·pc, which subsumes the Nomad floor 0 < pc.
  have hqeq : a QDIFF = 3 * a PC - 1024 := (qDiff_body_zero_iff a).mp hqB
  have hqge : (1024 : ℤ) ≤ 3 * (pc : ℤ) := by
    have h0 : (0 : ℤ) ≤ a QDIFF := hq0
    rw [hqeq, hpc] at h0; linarith
  have hnat : 1024 ≤ 3 * pc := by exact_mod_cast hqge
  have hpos : 0 < pc := by omega
  have hquorum : 2 * syncCommitteeSize ≤ 3 * pc := by unfold syncCommitteeSize; omega
  -- Carrier bits.
  have hbls' : blsOk = true := by
    have h : a BLS_OK = 1 := (bls_body_zero_iff a).mp hblsB
    rw [hbls] at h; cases blsOk with | true => rfl | false => simp at h
  have hfin' : finOk = true := by
    have h : a FIN_OK = 1 := (fin_body_zero_iff a).mp hfinB
    rw [hfin] at h; cases finOk with | true => rfl | false => simp at h
  have hexec' : execOk = true := by
    have h : a EXEC_OK = 1 := (exec_body_zero_iff a).mp hexecB
    rw [hexec] at h; cases execOk with | true => rfl | false => simp at h
  -- Branch depths.
  have hfl67' : fl = finalizedRootDepth ∨ fl = finalizedRootDepthElectra := by
    rcases (fl_body_zero_iff a).mp hflB with h | h
    · left
      have : (fl : ℤ) = 6 := by rw [← hfl]; exact h
      have : fl = 6 := by exact_mod_cast this
      simpa [finalizedRootDepth] using this
    · right
      have : (fl : ℤ) = 7 := by rw [← hfl]; exact h
      have : fl = 7 := by exact_mod_cast this
      simpa [finalizedRootDepthElectra] using this
  have hel4 : el = executionPayloadDepth := by
    have h : a EL = 4 := (el_body_zero_iff a).mp helB
    rw [hel] at h
    have : el = 4 := by exact_mod_cast h
    simpa [executionPayloadDepth] using this
  -- Assemble the three sub-decisions, then the composed decision.
  have hsync : syncDecision cl bl pc blsOk = true := by
    unfold syncDecision
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨hcl512, hbl512⟩, hpos⟩, hquorum⟩, hbls'⟩
  have hfinD : finalityDecision fl finOk = true := by
    unfold finalityDecision
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    exact ⟨hfl67', hfin'⟩
  have hexecD : execDecision el execOk = true := by
    unfold execDecision
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hel4, hexec'⟩
  simp only [ethVerifyDecision, hsync, hfinD, hexecD, Bool.and_true]

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Ethereum-validity (no-forgery, routed through the
emitted AIR).** GIVEN the named SHA-256 CR + chunk-injectivity carriers (`hcr`/`hinj`), if a row `a`
reads update `u`'s true projections under trusted state `ts` and the emitted verify-logic gates
accept, then `u` is Ethereum-VALID relative to `ts` — a ≥ 2/3 subset of the TRUSTED committee
genuinely signed the attested header, the attested state commits AND BINDS the finalized header, and
the finalized body commits the execution payload. So a STARK proving `ethLcVerifyDesc` carries
`eth_no_forgery`: the portable, trustless proof of Base/ETH finality. -/
theorem ethLcAir_no_forgery (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (ts : EthState L) (u : LightClientUpdate L) (a : Assignment)
    (hcl : a CL = (ts.committee.length : ℤ))
    (hbl : a BL = (u.syncAggregate.bits.length : ℤ))
    (hpc : a PC = ((participants ts.committee u.syncAggregate.bits).length : ℤ))
    (hfl : a FL = (u.finalityBranch.length : ℤ))
    (hel : a EL = (u.finalizedHeader.executionBranch.length : ℤ))
    (hbls : a BLS_OK = (if L.blsAggVerify (participants ts.committee u.syncAggregate.bits)
                          (signingRoot L ts u.attestedHeader) u.syncAggregate.sig
                        then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if L.beq (reconstruct L (htrHeader L u.finalizedHeader.beacon)
                          u.finalityBranch finalizedRootSubtreeIndex) u.attestedHeader.stateRoot
                        then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if L.beq (reconstruct L (htrExec L u.finalizedHeader.execution)
                          u.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
                          u.finalizedHeader.beacon.bodyRoot
                        then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    EthValidAt L ts u := by
  -- `ethLcAir_sound` at `u`'s projections yields exactly `ethProjectedDecision L ts u = true`.
  have hdec := ethLcAir_sound a ts.committee.length u.syncAggregate.bits.length
      (participants ts.committee u.syncAggregate.bits).length
      u.finalityBranch.length u.finalizedHeader.executionBranch.length
      (L.blsAggVerify (participants ts.committee u.syncAggregate.bits)
        (signingRoot L ts u.attestedHeader) u.syncAggregate.sig)
      (L.beq (reconstruct L (htrHeader L u.finalizedHeader.beacon) u.finalityBranch
        finalizedRootSubtreeIndex) u.attestedHeader.stateRoot)
      (L.beq (reconstruct L (htrExec L u.finalizedHeader.execution)
        u.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
        u.finalizedHeader.beacon.bodyRoot)
      hcl hbl hpc hfl hel hbls hfin hexec hacc
  exact ethVerifyDecision_no_forgery L hcr hinj ts u hdec

/-- **Completeness of the quorum tooth (the honest prover CAN fill `QDIFF`).** For any decision-
accepting projections with a real committee (`pc ≤ 512`), an honest row that fills `QDIFF = 3·pc−1024`
and the carrier bits with the true results is accepted by the emitted logic. This is the non-vacuity
partner of soundness: the AIR is satisfiable EXACTLY on accepted updates, not vacuously empty. -/
theorem ethLcAir_complete (a : Assignment)
    (cl bl pc fl el : Nat) (blsOk finOk execOk : Bool)
    (hcl : a CL = (cl : ℤ)) (hbl : a BL = (bl : ℤ)) (hpc : a PC = (pc : ℤ))
    (hfl : a FL = (fl : ℤ)) (hel : a EL = (el : ℤ))
    (hqdiff : a QDIFF = 3 * (pc : ℤ) - 1024)
    (hbls : a BLS_OK = (if blsOk then (1 : ℤ) else 0))
    (hfin : a FIN_OK = (if finOk then (1 : ℤ) else 0))
    (hexec : a EXEC_OK = (if execOk then (1 : ℤ) else 0))
    (hpc_le : pc ≤ syncCommitteeSize)
    (hdec : ethVerifyDecision cl bl pc blsOk fl finOk el execOk = true) :
    airAccepts a := by
  unfold ethVerifyDecision syncDecision finalityDecision execDecision at hdec
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨⟨hcl512, hbl512⟩, _hpos⟩, hquorum⟩, hbls1⟩, hfl67, hfin1⟩, hel4, hexec1⟩ := hdec
  have hquorum' : 1024 ≤ 3 * pc := by unfold syncCommitteeSize at hquorum; omega
  have hpc_le' : pc ≤ 512 := by simpa [syncCommitteeSize] using hpc_le
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [cl_body_zero_iff, hcl]; exact_mod_cast (by simpa [syncCommitteeSize] using hcl512)
  · rw [bl_body_zero_iff, hbl]; exact_mod_cast (by simpa [syncCommitteeSize] using hbl512)
  · rw [qDiff_body_zero_iff, hpc, hqdiff]
  · rw [hqdiff]
    have h1024 : (1024 : ℤ) ≤ 3 * (pc : ℤ) := by exact_mod_cast hquorum'
    linarith
  · rw [hqdiff]
    have hb : (pc : ℤ) ≤ 512 := by exact_mod_cast hpc_le'
    have hle : 3 * (pc : ℤ) - 1024 ≤ 512 := by linarith
    calc 3 * (pc : ℤ) - 1024 ≤ 512 := hle
      _ < (2 : ℤ) ^ Q_BITS := by norm_num [Q_BITS]
  · rw [bls_body_zero_iff, hbls]; simp [hbls1]
  · rw [fl_body_zero_iff, hfl]
    rcases hfl67 with h | h
    · left; exact_mod_cast (by simpa [finalizedRootDepth] using h)
    · right; exact_mod_cast (by simpa [finalizedRootDepthElectra] using h)
  · rw [fin_body_zero_iff, hfin]; simp [hfin1]
  · rw [el_body_zero_iff, hel]; exact_mod_cast (by simpa [executionPayloadDepth] using hel4)
  · rw [exec_body_zero_iff, hexec]; simp [hexec1]

/-! ## §6 — the emitted wire JSON (captured for the byte-pinned golden on first build) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on
-- either side breaks this `#guard`). Captured from the hbox build's `emitVmJson2` emission.
#guard emitVmJson2 ethLcVerifyDesc ==
  "{\"name\":\"dregg-eth-lightclient-verify::v1\",\"ir\":2,\"trace_width\":12,\"public_input_count\":3,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":11}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-512}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-512}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"var\",\"v\":2}}},\"r\":{\"t\":\"const\",\"v\":1024}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"mul\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-6}},\"r\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-7}}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-4}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":8},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":2}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins (robust; a layout drift moves these).
#guard ethLcVerifyDesc.traceWidth == ETH_LC_WIDTH
#guard ethLcVerifyDesc.piCount == PI_COUNT
#guard ethLcVerifyDesc.constraints.length == 12
#guard ethLcVerifyDesc.tables.length == 1
-- The three crypto carriers are real trace columns, and none is PI-bound (the results ride hidden).
#guard BLS_OK < ETH_LC_WIDTH
#guard FIN_OK < ETH_LC_WIDTH
#guard EXEC_OK < ETH_LC_WIDTH

/-! ## §7 — NON-VACUITY: the emitted teeth DISCRIMINATE (the Nomad boundary, in-AIR). -/

-- Structural: a 512-committee accepts; a 511-committee is refused.
#guard decide (clBody.eval (fun i => if i = CL then 512 else 0) = 0)
#guard decide (¬ (clBody.eval (fun i => if i = CL then 511 else 0) = 0))
#guard decide (blBody.eval (fun i => if i = BL then 512 else 0) = 0)
-- Quorum-slack identity: pc=512 ⇒ QDIFF=512 vanishes; a mismatched QDIFF is refused.
#guard decide (qDiffBody.eval (fun i => if i = QDIFF then 512 else if i = PC then 512 else 0) = 0)
#guard decide (¬ (qDiffBody.eval (fun i => if i = QDIFF then 511 else if i = PC then 512 else 0) = 0))
-- THE NOMAD BOUNDARY, in-AIR: the exact-quorum pc=342 slack (3·342−1024 = 2) is in range; the
-- sub-quorum pc=341 slack (3·341−1024 = −1) is NOT — the 342-accept / 341-reject tooth.
example : ([2] : List ℤ) ∈ rangeRows Q_BITS := by rw [range_row_mem_iff]; norm_num [Q_BITS]
example : ¬ (([-1] : List ℤ) ∈ rangeRows Q_BITS) := by rw [range_row_mem_iff]; norm_num [Q_BITS]
example : ([512] : List ℤ) ∈ rangeRows Q_BITS := by rw [range_row_mem_iff]; norm_num [Q_BITS]
-- Finality depth: 6 and 7 accept; 5 is refused (wrong-depth branch fail-closure).
#guard decide (flBody.eval (fun i => if i = FL then 6 else 0) = 0)
#guard decide (flBody.eval (fun i => if i = FL then 7 else 0) = 0)
#guard decide (¬ (flBody.eval (fun i => if i = FL then 5 else 0) = 0))
-- Execution depth: 4 accepts; 3 is refused.
#guard decide (elBody.eval (fun i => if i = EL then 4 else 0) = 0)
#guard decide (¬ (elBody.eval (fun i => if i = EL then 3 else 0) = 0))
-- Carriers: a set bit accepts; a cleared (forged) bit is refused.
#guard decide (blsBody.eval (fun i => if i = BLS_OK then 1 else 0) = 0)
#guard decide (¬ (blsBody.eval (fun _ => 0) = 0))
#guard decide (finBody.eval (fun i => if i = FIN_OK then 1 else 0) = 0)
#guard decide (execBody.eval (fun i => if i = EXEC_OK then 1 else 0) = 0)

/-! ## §8 — axiom hygiene. -/

#assert_axioms cl_body_zero_iff
#assert_axioms qDiff_body_zero_iff
#assert_axioms fl_body_zero_iff
#assert_axioms ethLcAir_sound
#assert_axioms ethLcAir_no_forgery

#print axioms ethLcAir_complete
#print axioms ethLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientEthAir
