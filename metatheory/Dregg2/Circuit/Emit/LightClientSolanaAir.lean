/-
# Dregg2.Circuit.Emit.LightClientSolanaAir — the Solana rooted-finality VERIFY-DECISION, EMITTED AS AN AIR.

## What this file IS (the "STARK-ify the Solana light client" slice — the ETH mirror, one level deeper)

`Dregg2.Bridge.LightClientSolana` AUTHORS the Solana Tower-BFT rooted-finality verification and proves
`sol_no_forgery` over `solVerifyDecision` — the scalar accept/reject a deployed node computes (the
counted rooted authorized voting stake, the active-stake total, the ed25519 + stake-table carriers, the
rooted + authorized-voter gates). That gives a node a Lean-PROVEN verdict — but rendered by running Lean
on the node's own machine; a peer (or an on-chain contract) that wants to trust "this dregg node saw
Solana root slot S with bank hash B" must RE-TRUST that node's execution. There is no portable object.

This file emits `solVerifyDecision` AS A DESCRIPTOR-IR-v2 AIR (`solLcVerifyDesc`), so a dregg node can
PROVE the verify-decision as a STARK: a portable artifact any peer verifies without re-running the node,
and (via the gnark FRI-wrap → Groth16 `SettlementCircuit` → `DreggPeerRegistry`, the SAME on-chain hook
the ETH `LightClientEthAir` attaches to) an on-chain contract verifies. That closes the biggest
interchain gap — Solana from a TRUSTED `True`-instance (the old `ProofOfHoldings` finality oracle) to a
formalized, STARK-ified, PORTABLE rooted-finality proof.

HOUSE LAW #1: the AIR is LEAN-AUTHORED. Rust only ingests the emitted `emitVmJson2` descriptor and runs
the generic multi-table prover over it; it never hand-writes these constraints. The refinement
`solLcAir_sound` / `solLcAir_no_forgery` is a machine-checked theorem over the EMITTED object
(`airAccepts` reads the descriptor's own gate bodies), tying acceptance to `solVerifyDecision` and hence
to `sol_no_forgery` — so a STARK satisfying this AIR CARRIES the no-forgery guarantee, modulo the two
named crypto carriers (below).

## The crypto boundary: IN-AIR logic vs NAMED verified carriers

  * IN-AIR (arithmetic gates over the trace — the stake TALLY logic, the Nomad-class bug locus):
      - the ≥2/3 supermajority `3·rooted ≥ 2·total` as a range-checked non-negative slack
        `QDIFF = 3·ROOTED_STK − 2·TOTAL_STK ∈ [0, 2^128)` (the u128-saturating `is_supermajority`,
        wrap-free — a minority gives `QDIFF < 0`, UNSAT);
      - the `EmptyStakeTable` floor `total > 0` as a range-checked `TPOS = TOTAL_STK − 1 ∈ [0, 2^128)`;
      - the ROOTED flag (`ROOTED_OK = 1` — HOLE-1) and the AUTHORIZED-voter binding (`AUTH_OK = 1` —
        BR-2-A) as forced boolean gates.
  * NAMED verified CARRIERS (witnessed boolean columns, forced `= 1`):
      - `ED_OK`         — the aggregate ed25519 verify over the counted authorized voters + the vote
        message `(slot, bankHash)` (`ed25519_dalek` / a verified realization),
      - `STAKE_TABLE_OK`— the derived stake table binds to the pinned WS anchor root (the SHA-256
        `EpochStakeTable::root` compare — the HOLE-2 denominator pin).

The residual is HONEST and NAMED: in THIS slice the two crypto carriers are asserted, not re-derived
in-circuit, so the STARK proves the TALLY/THRESHOLD/ROOTED/AUTHORIZED LOGIC is correct GIVEN the ed25519
and stake-table results — precisely `solVerifyDecision`'s guarantee, now portable. Putting ed25519 and
the stake-table SHA fold in-AIR (or as their own verified sub-proofs the AIR `ProofBind`s against) is the
next iteration; the public-input anchors below are the hook it attaches to. Also named: the counted
`ROOTED_STK` popcount-of-stake is a trusted projection (the deployed node's distinct-voter tally), the
same posture as the ETH `PC` participant count.

## Public inputs (the addressing layer — what the proof is ABOUT)

`PI[0]    = ANCHOR_ROOT`     — the pinned WS stake-table root (the governance trust anchor the
                            STAKE_TABLE_OK carrier is a compare against). The trust root the proof is
                            relative to.
`PI[1..9] = BANK_ROOT[0..8]` — the claimed ROOTED bank/state hash B at slot S (what a proof-of-holdings
                            later opens against): the FULL 256-bit bank hash exposed as its NINE
                            radix-`2^31`, MOST-SIGNIFICANT-limb-first limbs (`⌈256/31⌉ = 9`; the top
                            limb carries the residual 8 bits). FELT-WIDTH CLOSE: the earlier single
                            anchor felt bound only a 31-bit PROJECTION of the bank hash (two 256-bit
                            roots agreeing in 31 bits both verified — a soundness gap at the peer-wrap
                            boundary); nine PI-bound limbs bind the WHOLE root, recomposed by the
                            peer-wrap's radix-`2^31` MSB-first pack before its 128-bit split.
`PI[10]   = SLOT`           — the rooted slot S (the epoch/slot the finality is claimed at).

These ride as published witness columns pinned to the public inputs (`.piBinding`). NOT-YET-CLOSED
(named residual, identical to the ETH slice, UNCHANGED by this widening): the anchors are published
but not yet arithmetically bound to the carrier bits (that binding IS the in-AIR-crypto iteration —
`ED_OK` derived from the vote message built on `BANK_ROOT`+`SLOT`, `STAKE_TABLE_OK` derived from the
table fold into `ANCHOR_ROOT`). This change widens the BANK-ROOT anchor from 31 bits to the full 256,
orthogonal to (and leaving untouched) the logic refinement.

## Axiom hygiene
Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`solLcAir_sound` / `solLcAir_no_forgery` refinement to `solVerifyDecision` / `sol_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. NEW file; imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Bridge.LightClientSolana

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Dregg2.Circuit.Emit.LightClientSolanaAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientSolana

/-! ## §1 — the trace column layout (one logical row). Columns 0..7 are the six verify-logic
projections `solVerifyDecision` composes over (two crypto carriers) plus the two range slacks; columns
8..18 are the published PUBLIC anchors: `ANCHOR_ROOT` (8), the NINE bank-root limbs `BANK_ROOT 0..8`
(cols 9..17 — the full 256-bit bank hash, radix-`2^31`, MSB-first), and `SLOT_COL` (18). -/

/-- Counted rooted authorized voting stake (`voted_stake`); range-bounded via the quorum slack. Witness. -/
def ROOTED_STK : Nat := 0
/-- Total ACTIVE stake (`total_stake()`); the 2/3 denominator, forced `> 0` via the `TPOS` slack. Witness. -/
def TOTAL_STK : Nat := 1
/-- The quorum SLACK `3·ROOTED_STK − 2·TOTAL_STK`; the range tooth forces it into `[0, 2^128)`, i.e.
`2·total ≤ 3·rooted`. Witness. -/
def QDIFF : Nat := 2
/-- The total-positivity SLACK `TOTAL_STK − 1`; the range tooth forces `total ≥ 1` (`EmptyStakeTable`). -/
def TPOS : Nat := 3
/-- **CARRIER** — the aggregate ed25519 verify RESULT (counted authorized voters signed the bank hash at
the slot); forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 4
/-- **CARRIER** — the stake-table-root compare RESULT (derived table binds the pinned WS anchor root);
forced `= 1`. NAMED carrier (the HOLE-2 denominator pin). Witness. -/
def STAKE_TABLE_OK : Nat := 5
/-- **GATE** — the ROOTED flag (every counted vote's tower root reaches the slot — HOLE-1); forced `= 1`. -/
def ROOTED_OK : Nat := 6
/-- **GATE** — the AUTHORIZED-voter binding (every counted signer is the on-chain authorized voter —
BR-2-A); forced `= 1`. -/
def AUTH_OK : Nat := 7

/-- **PUBLIC ANCHOR** — the pinned WS stake-table root (the governance trust anchor). PI-bound. -/
def ANCHOR_ROOT : Nat := 8

/-- The number of ~31-bit limbs the FULL 256-bit rooted bank hash is exposed as: `⌈256 / 31⌉ = 9`.
Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits.
This is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION of the 256-bit bank
hash (two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def BANK_ROOT_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed rooted bank/state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `9 + i` (cols 9..17); limb `0` is
the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit bank hash exactly before its 128-bit split. -/
def BANK_ROOT (i : Nat) : Nat := 9 + i

/-- **PUBLIC ANCHOR** — the rooted slot S (epoch/slot). PI-bound. -/
def SLOT_COL : Nat := 9 + BANK_ROOT_LIMBS

/-- Total main-trace width: 8 logic columns + 1 anchor-root + 9 bank-root limbs + 1 slot anchor. -/
def SOL_LC_WIDTH : Nat := 19

/-- PI slot 0: the pinned WS anchor root. -/
def PI_ANCHOR_ROOT : Nat := 0
/-- PI slot of bank-root limb `i` (slots 1..9), MSB-first. -/
def PI_BANK_ROOT (i : Nat) : Nat := 1 + i
/-- PI slot of the rooted slot (slot 10). -/
def PI_SLOT : Nat := 1 + BANK_ROOT_LIMBS
/-- Number of public inputs: anchor root + 9 bank-root limbs + slot. -/
def PI_COUNT : Nat := 11

/-- The range width — the u128 stake tally width the Rust `is_supermajority` uses (`saturating_mul` over
`u128`). `3·rooted − 2·total ∈ [0, 2^128)` and `total − 1 ∈ [0, 2^128)` for any real stake distribution;
the interval's floor `≥ 0` is the load-bearing 2/3 + `total > 0` tooth. -/
def RANGE_BITS : Nat := 128

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials). -/

/-- `QDIFF − 3·ROOTED_STK + 2·TOTAL_STK` — zero iff `QDIFF = 3·rooted − 2·total` (the quorum slack). -/
def qDiffBody : EmittedExpr :=
  .add (.add (.var QDIFF) (.mul (.const (-3)) (.var ROOTED_STK))) (.mul (.const 2) (.var TOTAL_STK))
/-- `TPOS − TOTAL_STK + 1` — zero iff `TPOS = total − 1` (the total-positivity slack). -/
def tPosBody : EmittedExpr :=
  .add (.add (.var TPOS) (.mul (.const (-1)) (.var TOTAL_STK))) (.const 1)
/-- `ED_OK − 1` — zero iff the ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `STAKE_TABLE_OK − 1` — zero iff the stake-table-root carrier bit is set. -/
def stakeBody : EmittedExpr := .add (.var STAKE_TABLE_OK) (.const (-1))
/-- `ROOTED_OK − 1` — zero iff the rooted-flag gate bit is set. -/
def rootedBody : EmittedExpr := .add (.var ROOTED_OK) (.const (-1))
/-- `AUTH_OK − 1` — zero iff the authorized-voter-binding gate bit is set. -/
def authBody : EmittedExpr := .add (.var AUTH_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor. -/

def qDiffGate : VmConstraint2 := .base (.gate qDiffBody)
/-- The quorum range tooth: `QDIFF ∈ [0, 2^RANGE_BITS)` — the 2/3 boundary, wrap-free. -/
def qRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var QDIFF]⟩
def tPosGate : VmConstraint2 := .base (.gate tPosBody)
/-- The total-positivity range tooth: `TPOS ∈ [0, 2^RANGE_BITS)` — forces `total ≥ 1`. -/
def tPosRangeLookup : VmConstraint2 := .lookup ⟨TableId.range, [.var TPOS]⟩
def edGate : VmConstraint2 := .base (.gate edBody)
def stakeGate : VmConstraint2 := .base (.gate stakeBody)
def rootedGate : VmConstraint2 := .base (.gate rootedBody)
def authGate : VmConstraint2 := .base (.gate authBody)
/-- Published-anchor pin: the pinned WS anchor root is `PI[0]`. -/
def anchorRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ANCHOR_ROOT PI_ANCHOR_ROOT)
/-- Published-anchor pins: the NINE rooted-bank-root limbs are `PI[1..9]` (MSB-first). Each limb rides
its own PI slot, so the peer-wrap's radix-`2^31` pack over `PI[1..9]` recovers the FULL 256-bit bank
hash — not a 31-bit projection. Written as an explicit literal (limb `i` → col `9+i` → PI `1+i`) so
the byte-golden `#guard` reduces to the exact wire string with no fold. -/
def bankRootPins : List VmConstraint2 :=
  [ .base (.piBinding VmRow.first (BANK_ROOT 0) (PI_BANK_ROOT 0))
  , .base (.piBinding VmRow.first (BANK_ROOT 1) (PI_BANK_ROOT 1))
  , .base (.piBinding VmRow.first (BANK_ROOT 2) (PI_BANK_ROOT 2))
  , .base (.piBinding VmRow.first (BANK_ROOT 3) (PI_BANK_ROOT 3))
  , .base (.piBinding VmRow.first (BANK_ROOT 4) (PI_BANK_ROOT 4))
  , .base (.piBinding VmRow.first (BANK_ROOT 5) (PI_BANK_ROOT 5))
  , .base (.piBinding VmRow.first (BANK_ROOT 6) (PI_BANK_ROOT 6))
  , .base (.piBinding VmRow.first (BANK_ROOT 7) (PI_BANK_ROOT 7))
  , .base (.piBinding VmRow.first (BANK_ROOT 8) (PI_BANK_ROOT 8)) ]
/-- Published-anchor pin: the rooted slot is `PI[10]`. -/
def slotPin : VmConstraint2 :=
  .base (.piBinding VmRow.first SLOT_COL PI_SLOT)

/-- **`solLcVerifyDesc`** — the Solana rooted-finality verify-decision as an emitted IR-v2 AIR. PIs
`[anchor_root, bank_root[0..8], slot]` (11 total — the rooted bank hash is the FULL 256-bit value as
nine radix-`2^31` MSB-first limbs, not a 31-bit projection); the six verify-logic projections + two
range slacks as hidden witnesses, the two crypto results as carrier bits. One range table
(`TID_range`) carries both the quorum tooth and the total-positivity tooth. -/
def solLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-solana-lightclient-verify::v1"
  , traceWidth  := SOL_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [rangeTableDef RANGE_BITS]
  , constraints := [qDiffGate, qRangeLookup, tPosGate, tPosRangeLookup, edGate, stakeGate,
                    rootedGate, authGate, anchorRootPin] ++ bankRootPins ++ [slotPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- `qDiffBody = 0 ↔ QDIFF = 3·ROOTED_STK − 2·TOTAL_STK`. -/
theorem qDiff_body_zero_iff (a : Assignment) :
    qDiffBody.eval a = 0 ↔ a QDIFF = 3 * a ROOTED_STK - 2 * a TOTAL_STK := by
  simp only [qDiffBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `tPosBody = 0 ↔ TPOS = TOTAL_STK − 1`. -/
theorem tPos_body_zero_iff (a : Assignment) :
    tPosBody.eval a = 0 ↔ a TPOS = a TOTAL_STK - 1 := by
  simp only [tPosBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `edBody = 0 ↔ ED_OK = 1`. -/
theorem ed_body_zero_iff (a : Assignment) : edBody.eval a = 0 ↔ a ED_OK = 1 := by
  simp only [edBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `stakeBody = 0 ↔ STAKE_TABLE_OK = 1`. -/
theorem stake_body_zero_iff (a : Assignment) : stakeBody.eval a = 0 ↔ a STAKE_TABLE_OK = 1 := by
  simp only [stakeBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `rootedBody = 0 ↔ ROOTED_OK = 1`. -/
theorem rooted_body_zero_iff (a : Assignment) : rootedBody.eval a = 0 ↔ a ROOTED_OK = 1 := by
  simp only [rootedBody, EmittedExpr.eval]; constructor <;> intro h <;> omega
/-- `authBody = 0 ↔ AUTH_OK = 1`. -/
theorem auth_body_zero_iff (a : Assignment) : authBody.eval a = 0 ↔ a AUTH_OK = 1 := by
  simp only [authBody, EmittedExpr.eval]; constructor <;> intro h <;> omega

/-! ## §5 — `airAccepts`: the descriptor's LOGIC-acceptance predicate + the REFINEMENT to
`solVerifyDecision`. -/

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and the two slacks lie in
the range interval `[0, 2^RANGE_BITS)` (the denotation `range_row_mem_iff` connects the emitted lookups
to). The published-anchor pins are the addressing layer, orthogonal to the logic. -/
def airAccepts (a : Assignment) : Prop :=
  qDiffBody.eval a = 0
  ∧ (0 ≤ a QDIFF ∧ a QDIFF < (2 : ℤ) ^ RANGE_BITS)
  ∧ tPosBody.eval a = 0
  ∧ (0 ≤ a TPOS ∧ a TPOS < (2 : ℤ) ^ RANGE_BITS)
  ∧ edBody.eval a = 0
  ∧ stakeBody.eval a = 0
  ∧ rootedBody.eval a = 0
  ∧ authBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `solVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two stakes as
felts, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic gates accept, then the
exported scalar decision `solVerifyDecision` accepts. The quorum range floor discharges the 2/3 threshold;
the `TPOS` floor discharges `total > 0`. -/
theorem solLcAir_sound (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hr : a ROOTED_STK = (rootedStk : ℤ)) (ht : a TOTAL_STK = (totalStk : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true := by
  obtain ⟨hqB, ⟨hq0, _hqlt⟩, htB, ⟨ht0, _htlt⟩, hedB, hstkB, hrootedB, hauthB⟩ := hacc
  -- Threshold: QDIFF = 3·rooted − 2·total ≥ 0 ⟹ 2·total ≤ 3·rooted.
  have hqeq : a QDIFF = 3 * a ROOTED_STK - 2 * a TOTAL_STK := (qDiff_body_zero_iff a).mp hqB
  have hthrZ : (2 : ℤ) * (totalStk : ℤ) ≤ 3 * (rootedStk : ℤ) := by
    have := hq0; rw [hqeq, hr, ht] at this; linarith
  have hthr : 2 * totalStk ≤ 3 * rootedStk := by exact_mod_cast hthrZ
  -- Total positivity: TPOS = total − 1 ≥ 0 ⟹ total ≥ 1.
  have hteq : a TPOS = a TOTAL_STK - 1 := (tPos_body_zero_iff a).mp htB
  have hposZ : (1 : ℤ) ≤ (totalStk : ℤ) := by
    have := ht0; rw [hteq, ht] at this; linarith
  have hpos : 0 < totalStk := by
    have : 1 ≤ totalStk := by exact_mod_cast hposZ
    omega
  -- Carrier / gate bits.
  have hedTrue : edB = true := by
    have h : a ED_OK = 1 := (ed_body_zero_iff a).mp hedB
    rw [hed] at h; cases edB with | true => rfl | false => simp at h
  have hstkTrue : stakeB = true := by
    have h : a STAKE_TABLE_OK = 1 := (stake_body_zero_iff a).mp hstkB
    rw [hstk] at h; cases stakeB with | true => rfl | false => simp at h
  have hrootedTrue : rootedB = true := by
    have h : a ROOTED_OK = 1 := (rooted_body_zero_iff a).mp hrootedB
    rw [hrooted] at h; cases rootedB with | true => rfl | false => simp at h
  have hauthTrue : authB = true := by
    have h : a AUTH_OK = 1 := (auth_body_zero_iff a).mp hauthB
    rw [hauth] at h; cases authB with | true => rfl | false => simp at h
  -- Assemble.
  unfold solVerifyDecision
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨hpos, hthr⟩, hedTrue⟩, hstkTrue⟩, hrootedTrue⟩, hauthTrue⟩

/-- **THE PAYOFF: a satisfying AIR witness ENTAILS Solana rooted-validity (no-forgery, routed through
the emitted AIR).** GIVEN the named stake-table CR carrier (`hcr`), if a row `a` reads update `u`'s true
projections under pinned anchor `ts` and the emitted verify-logic gates accept, then `u` is
Solana-ROOTED-VALID relative to `ts` — a ≥2/3 subset of the ACTIVE stake, each account's on-chain
AUTHORIZED voter genuinely signed the bank hash at the slot, each vote ROOTED, the denominator pinned to
the WS anchor. So a STARK proving `solLcVerifyDesc` carries `sol_no_forgery`: the portable, trustless
proof of Solana rooted finality. -/
theorem solLcAir_no_forgery (L : SolLeaf) (hcr : L.stakeTableCR)
    (ts : SolTrustedState L) (u : SolUpdate L) (a : Assignment)
    (hr : a ROOTED_STK = (rootedStake L u : ℤ)) (ht : a TOTAL_STK = (totalStake L u : ℤ))
    (hed : a ED_OK = (if edOk L u then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeTableOk L ts u then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedOk L u then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authOk L u then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    SolValidAt L ts u := by
  have hdec := solLcAir_sound a (rootedStake L u) (totalStake L u)
    (edOk L u) (stakeTableOk L ts u) (rootedOk L u) (authOk L u)
    hr ht hed hstk hrooted hauth hacc
  exact solVerifyDecision_no_forgery L hcr ts u hdec

/-- **Completeness of the range teeth (the honest prover CAN fill the slacks).** For any decision-
accepting projections whose stakes fit the u128 tally window (`3·rooted < 2^128`, `total < 2^128`), an
honest row that fills `QDIFF = 3·rooted − 2·total`, `TPOS = total − 1`, and the carrier/gate bits with
the true results is accepted by the emitted logic. The non-vacuity partner of soundness. -/
theorem solLcAir_complete (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hr : a ROOTED_STK = (rootedStk : ℤ)) (ht : a TOTAL_STK = (totalStk : ℤ))
    (hq : a QDIFF = 3 * (rootedStk : ℤ) - 2 * (totalStk : ℤ))
    (hp : a TPOS = (totalStk : ℤ) - 1)
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hrw : 3 * (rootedStk : ℤ) < (2 : ℤ) ^ RANGE_BITS)
    (htw : (totalStk : ℤ) < (2 : ℤ) ^ RANGE_BITS)
    (hdec : solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true) :
    airAccepts a := by
  unfold solVerifyDecision at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨hpos, hthr⟩, hedB⟩, hstkB⟩, hrootedB⟩, hauthB⟩ := hdec
  have hthrZ : (2 : ℤ) * (totalStk : ℤ) ≤ 3 * (rootedStk : ℤ) := by exact_mod_cast hthr
  have hposZ : (1 : ℤ) ≤ (totalStk : ℤ) := by exact_mod_cast hpos
  have h0t : (0 : ℤ) ≤ (totalStk : ℤ) := by positivity
  have h0r : (0 : ℤ) ≤ (rootedStk : ℤ) := by positivity
  refine ⟨?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rw [qDiff_body_zero_iff, hr, ht, hq]
  · rw [hq]; linarith
  · rw [hq]; linarith
  · rw [tPos_body_zero_iff, ht, hp]
  · rw [hp]; linarith
  · rw [hp]; linarith
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [stake_body_zero_iff, hstk]; simp [hstkB]
  · rw [rooted_body_zero_iff, hrooted]; simp [hrootedB]
  · rw [auth_body_zero_iff, hauth]; simp [hauthB]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on either
-- side breaks this `#guard`). Captured from the hbox build's `emitVmJson2` emission. The rooted bank
-- root is now NINE `pi_binding`s (cols 9..17 → PI 1..9), the full 256-bit anchor.
#guard emitVmJson2 solLcVerifyDesc ==
  "{\"name\":\"dregg-solana-lightclient-verify::v1\",\"ir\":2,\"trace_width\":19,\"public_input_count\":11,\"tables\":[{\"id\":2,\"name\":\"range\",\"arity\":1,\"sem\":\"range\",\"bits\":128}],\"constraints\":[{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-3},\"r\":{\"t\":\"var\",\"v\":0}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":2},\"r\":{\"t\":\"var\",\"v\":1}}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":2}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":1}}},\"r\":{\"t\":\"const\",\"v\":1}}},{\"t\":\"lookup\",\"table\":2,\"tuple\":[{\"t\":\"var\",\"v\":3}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":4},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":5},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":6},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":7},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":8,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":10,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":13,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":14,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":15,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":16,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":17,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":18,\"pi_index\":10}],\"hash_sites\":[],\"ranges\":[]}"

-- Shape pins (robust; a layout drift moves these).
#guard solLcVerifyDesc.traceWidth == SOL_LC_WIDTH
#guard solLcVerifyDesc.piCount == PI_COUNT
#guard solLcVerifyDesc.constraints.length == 19
#guard solLcVerifyDesc.tables.length == 1
-- The two crypto carriers are real trace columns, and none is PI-bound (the results ride hidden).
#guard ED_OK < SOL_LC_WIDTH
#guard STAKE_TABLE_OK < SOL_LC_WIDTH
-- The widened rooted-bank-root anchor: nine limbs, contiguous cols 9..17 → PI 1..9, MSB-first, all
-- within width and below the slot anchor; `⌈256/31⌉ = 9` covers the full 256 bits.
#guard BANK_ROOT_LIMBS == 9
#guard bankRootPins.length == BANK_ROOT_LIMBS
#guard SLOT_COL == 18
#guard PI_SLOT == 10
#guard decide (BANK_ROOT 0 == 9 ∧ BANK_ROOT 8 == 17 ∧ BANK_ROOT 8 < SLOT_COL)
#guard decide (PI_BANK_ROOT 0 == 1 ∧ PI_BANK_ROOT 8 == 9 ∧ PI_BANK_ROOT 8 < PI_SLOT)
#guard decide (31 * BANK_ROOT_LIMBS ≥ 256)

/-! ## §7 — NON-VACUITY: the emitted teeth DISCRIMINATE (the 2/3 boundary + the closed holes, in-AIR). -/

-- Quorum-slack identity: rooted=2,total=3 ⇒ QDIFF=0 vanishes; a mismatched QDIFF is refused.
#guard decide (qDiffBody.eval (fun i => if i = QDIFF then 0 else if i = ROOTED_STK then 2
  else if i = TOTAL_STK then 3 else 0) = 0)
#guard decide (¬ (qDiffBody.eval (fun i => if i = QDIFF then 1 else if i = ROOTED_STK then 2
  else if i = TOTAL_STK then 3 else 0) = 0))
-- THE 2/3 BOUNDARY, in-AIR: the exact-2/3 rooted=2 of total=3 slack (3·2−2·3 = 0) is in range; the
-- sub-2/3 rooted=1 of total=3 slack (3·1−2·3 = −3) is NOT — the accept/reject tooth.
example : ([0] : List ℤ) ∈ rangeRows RANGE_BITS := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
example : ¬ (([-3] : List ℤ) ∈ rangeRows RANGE_BITS) := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
-- Total-positivity: total=1 ⇒ TPOS=0 in range; total=0 ⇒ TPOS=−1 out (EmptyStakeTable reject).
example : ([0] : List ℤ) ∈ rangeRows RANGE_BITS := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
example : ¬ (([-1] : List ℤ) ∈ rangeRows RANGE_BITS) := by rw [range_row_mem_iff]; norm_num [RANGE_BITS]
-- Carriers / gates: a set bit accepts; a cleared (forged / optimistic / imposter) bit is refused.
#guard decide (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0)
#guard decide (¬ (edBody.eval (fun _ => 0) = 0))
#guard decide (stakeBody.eval (fun i => if i = STAKE_TABLE_OK then 1 else 0) = 0)
#guard decide (¬ (stakeBody.eval (fun _ => 0) = 0))
#guard decide (rootedBody.eval (fun i => if i = ROOTED_OK then 1 else 0) = 0)
#guard decide (¬ (rootedBody.eval (fun _ => 0) = 0))
#guard decide (authBody.eval (fun i => if i = AUTH_OK then 1 else 0) = 0)
#guard decide (¬ (authBody.eval (fun _ => 0) = 0))

/-! ## §8 — axiom hygiene. -/

#assert_axioms qDiff_body_zero_iff
#assert_axioms tPos_body_zero_iff
#assert_axioms solLcAir_sound
#assert_axioms solLcAir_no_forgery
#assert_axioms solLcAir_complete

#print axioms solLcAir_sound
#print axioms solLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientSolanaAir
