/-
# Dregg2.Bridge.LightClientEthGate — the RUNTIME-CALLABLE Ethereum light-client VERIFY-LOGIC
gate, `@[export] dregg_eth_lc_verify`, PROVEN to be the same accept/reject decision the
no-forgery theorem is stated over (`LightClientEth.verifyFinalizedUpdate`).

## Why this module exists (the translation-validation closure for the ETH light client)

`Dregg2.Bridge.LightClientEth` proves `eth_no_forgery` over `verifyFinalizedUpdate` — a Lean
RE-AUTHORING of the Rust verifier's rules (`eth-lightclient/src/{lib,finality,execution}.rs`).
There is (was) NO formal tie between the deployed Rust decision and the proven Lean one: the
Rust `verify_finalized_update` and the Lean `verifyFinalizedUpdate` are TWINS that can drift.
This is the same "proven over a re-authoring, not over the emitted object" gap the
conservation / finalization-quorum twin-deletion campaign closes by `@[export]`-ing the Lean
DECISION and routing the Rust through it, fail-closed (`docs/TWIN-DELETION-MAP-2026-07-23.md`).

## The subtlety (heavy crypto stays a NAMED verified-FFI carrier; only the LOGIC is exported)

Light-client verify is not pure logic — it invokes BLS12-381 aggregate verify and SHA-256 SSZ
Merkle folds. So the twin-deletion boundary is drawn PRECISELY at the verification LOGIC:

  * EXPORTED + PROVEN (this gate): the quorum COUNTING and the ≥ 2/3 multiply-form threshold
    (`3·participants ≥ 2·512`, no rounding trap: 342 accept / 341 reject), the committee-size
    and bitfield-length checks, the zero-participant Nomad floor, and the branch-DEPTH
    admissibility (finality 6|7, execution 4). These are pure `Nat`/`Bool` — decidable in Lean
    with NO crypto — and they are exactly the Nomad-class RULES bug locus (a permissive default
    / an off-by-one threshold / a wrong-depth branch is what drains bridges).
  * NAMED verified-FFI CARRIERS (supplied to the gate as their boolean RESULTS): the BLS
    aggregate verify (`blsOk` — `blst`, the audited ETH-client library; Galois SAW proofs cover
    the field/curve arithmetic; an EverCrypt-grade verified pairing is the honest research
    frontier), and the SHA-256 branch reconstruction comparisons (`finalityOk` / `execOk` — the
    `hashPairCR` carrier; HACL*/EverCrypt SHA-256 is the project-default verified realization,
    replacing RustCrypto `sha2`). The gate does NOT re-derive the crypto; it composes the
    accept/reject over the crypto RESULTS.

`ethVerifyDecision` is that composition over the eight scalar/boolean projections. The load-
bearing theorem is `ethVerifyDecision_refines`: fed the true projections of an update, the
exported scalar decision is DEFINITIONALLY `verifyFinalizedUpdate L ts u` (`rfl`). So the
deployed node, computing the crypto primitives in `blst`/SHA-256 and handing their results +
the combinatorial facts to `dregg_eth_lc_verify`, makes the ACCEPT/REJECT decision that
`eth_no_forgery` is proven over — `ethVerifyDecision_no_forgery` states exactly that. The
re-authored-Rust LOGIC twin is then deletable: the Rust keeps only the crypto-primitive
computation, and the Lean gate renders the verdict, fail-closed when the archive lacks the
export.

## The ONE trusted projection (named, not hidden)

The participant COUNT `pc` is a popcount of the 512-bit field, computed in Rust
(`SyncAggregate::count`) and supplied on the wire — exactly as the `dregg_finalization_quorum`
gate trusts the collector to intern+dedup the `(signer,root)` tally and verifies the quorum
DECISION over it. The popcount is a mechanically-faithful `count_ones` sum; the VERIFIED
content is the threshold/floor DECISION over it. HARDENING (named, next iteration): ship the
raw `List Bool` and count in Lean via `participants`, discharging the projection with
`participants_length_eq_replicate` — removing the last logic step from Rust.
-/
import Dregg2.Bridge.LightClientEth

set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientEthGate

open Dregg2.Bridge.LightClientEth

/-! ## §1 — The three scalar sub-decisions, grouped to MATCH the three Lean/Rust sub-gates
EXACTLY (so the refinement below is `rfl`). Each takes the combinatorial facts plus the crypto
primitive's boolean RESULT; none re-derives crypto. -/

/-- **`syncDecision`** — the sync-aggregate LOGIC (`verifySyncAggregate`, `lib.rs:286-334`):
committee is exactly 512 keys, the bitfield is 512 bits, the participating count is nonzero
(the Nomad floor) and meets the multiply-form 2/3 threshold `3·pc ≥ 2·512`. `blsOk` is the
`blst` aggregate-verify RESULT over the participating subset + signing root (the named crypto
carrier). Grouping matches `verifySyncAggregate` term-for-term. -/
def syncDecision (committeeLen bitsLen participantCount : Nat) (blsOk : Bool) : Bool :=
  decide (committeeLen = syncCommitteeSize)
  && decide (bitsLen = syncCommitteeSize)
  && decide (0 < participantCount)
  && decide (2 * syncCommitteeSize ≤ 3 * participantCount)
  && blsOk

/-- **`finalityDecision`** — the finality-branch LOGIC (`verifyFinalityBranch`,
`finality.rs:151-183`): the branch depth is 6 (Altair..Deneb) or 7 (Electra+) — any other
length fail-closed. `reconstructOk` is the SHA-256 fold RESULT (reconstruct into the attested
state root at subtree index 41) — the named `hashPairCR` carrier. -/
def finalityDecision (branchLen : Nat) (reconstructOk : Bool) : Bool :=
  (decide (branchLen = finalizedRootDepth) || decide (branchLen = finalizedRootDepthElectra))
  && reconstructOk

/-- **`execDecision`** — the execution-branch LOGIC (`verifyExecutionPayload`,
`execution.rs:104-126`): depth exactly 4. `reconstructOk` is the SHA-256 fold RESULT
(reconstruct into the finalized body root at subtree index 9) — the named `hashPairCR`
carrier. -/
def execDecision (branchLen : Nat) (reconstructOk : Bool) : Bool :=
  decide (branchLen = executionPayloadDepth) && reconstructOk

/-- **`ethVerifyDecision`** — THE composed verify-logic decision, over the eight
scalar/boolean projections a deployed node computes (three of them being the crypto
primitives' results). Grouped `sync && finality && exec` to match `verifyFinalizedUpdate`
EXACTLY. This is the object `@[export] dregg_eth_lc_verify` renders and `eth_no_forgery` is
(via `ethVerifyDecision_refines`) proven over. -/
def ethVerifyDecision (committeeLen bitsLen participantCount : Nat) (blsOk : Bool)
    (finalityLen : Nat) (finalityOk : Bool) (execLen : Nat) (execOk : Bool) : Bool :=
  syncDecision committeeLen bitsLen participantCount blsOk
  && finalityDecision finalityLen finalityOk
  && execDecision execLen execOk

/-! ## §2 — THE REFINEMENT TIE: the exported scalar decision IS `verifyFinalizedUpdate`.

Each sub-gate refines its scalar decision by `rfl` (the scalars are the exact subterms), and
the composition refines by congruence. `ethVerifyDecision_refines` is the translation-
validation object: it turns "proven over a re-authoring" into "the deployed accept/reject
decision IS the proven Lean object", modulo the three named crypto carriers supplied as their
results. -/

theorem syncDecision_refines (L : EthLeaf) (ts : EthState L)
    (hdr : BeaconBlockHeader L) (agg : SyncAggregate L) :
    syncDecision ts.committee.length agg.bits.length
        (participants ts.committee agg.bits).length
        (L.blsAggVerify (participants ts.committee agg.bits) (signingRoot L ts hdr) agg.sig)
      = verifySyncAggregate L ts hdr agg := rfl

theorem finalityDecision_refines (L : EthLeaf) (finalizedBeacon : BeaconBlockHeader L)
    (branch : List L.Digest) (attestedStateRoot : L.Digest) :
    finalityDecision branch.length
        (L.beq (reconstruct L (htrHeader L finalizedBeacon) branch finalizedRootSubtreeIndex)
          attestedStateRoot)
      = verifyFinalityBranch L finalizedBeacon branch attestedStateRoot := rfl

theorem execDecision_refines (L : EthLeaf) (e : ExecutionPayloadHeader L)
    (branch : List L.Digest) (bodyRoot : L.Digest) :
    execDecision branch.length
        (L.beq (reconstruct L (htrExec L e) branch executionPayloadSubtreeIndex) bodyRoot)
      = verifyExecutionPayload L e branch bodyRoot := rfl

/-- **`ethProjection`** — the eight projections a node hands the gate for an update `u` under
trusted state `ts`: the two lengths, the participant count, the three crypto RESULTS
(`blsAggVerify` / two `reconstruct`-compares), and the two branch depths. The crypto carriers
appear here (and NOWHERE else in the gate) as opaque boolean results. -/
def ethProjectedDecision (L : EthLeaf) (ts : EthState L) (u : LightClientUpdate L) : Bool :=
  ethVerifyDecision ts.committee.length u.syncAggregate.bits.length
    (participants ts.committee u.syncAggregate.bits).length
    (L.blsAggVerify (participants ts.committee u.syncAggregate.bits)
      (signingRoot L ts u.attestedHeader) u.syncAggregate.sig)
    u.finalityBranch.length
    (L.beq (reconstruct L (htrHeader L u.finalizedHeader.beacon) u.finalityBranch
      finalizedRootSubtreeIndex) u.attestedHeader.stateRoot)
    u.finalizedHeader.executionBranch.length
    (L.beq (reconstruct L (htrExec L u.finalizedHeader.execution)
      u.finalizedHeader.executionBranch executionPayloadSubtreeIndex)
      u.finalizedHeader.beacon.bodyRoot)

/-- **THE TRANSLATION-VALIDATION THEOREM.** Fed an update's true projections, the exported
scalar decision is DEFINITIONALLY the proven gate `verifyFinalizedUpdate L ts u`. So gating a
deployed node on `dregg_eth_lc_verify` (with the crypto primitives computed in `blst`/SHA-256)
gates it, definitionally, on the decision `eth_no_forgery` is proven over. -/
theorem ethVerifyDecision_refines (L : EthLeaf) (ts : EthState L) (u : LightClientUpdate L) :
    ethProjectedDecision L ts u = verifyFinalizedUpdate L ts u := rfl

/-- **THE PAYOFF: acceptance by the EXPORTED scalar decision entails Ethereum-validity.**
GIVEN the named hash carriers, if the projected `ethVerifyDecision` accepts `u`, then `u` is
Ethereum-VALID relative to the trusted state — a ≥ 2/3 subset of the TRUSTED committee
genuinely signed the attested header, the attested state commits AND BINDS the finalized
header, and the finalized body commits the execution payload. This is `eth_no_forgery`
routed through the deployed decision object. -/
theorem ethVerifyDecision_no_forgery (L : EthLeaf) (hcr : L.hashPairCR) (hinj : L.uChunkInj)
    (ts : EthState L) (u : LightClientUpdate L)
    (h : ethProjectedDecision L ts u = true) : EthValidAt L ts u :=
  eth_no_forgery L hcr hinj ts u ((ethVerifyDecision_refines L ts u) ▸ h)

/-! ## §3 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_finalization_quorum` (`Dregg2.Distributed.FinalityGate`). Fail-closed on any malformed
wire (`"ERR"` ⇒ the node treats it as REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- **`decodeEthWire`** — parse the full `INPUT` grammar into the eight projections.
Fail-closed (`none`) on any deviation.

```
INPUT := "cl=" Nat ";bl=" Nat ";pc=" Nat ";bls=" BIT
       ";fl=" Nat ";fr=" BIT ";el=" Nat ";er=" BIT
BIT   := "0" | "1"
```
(`cl`=committee length, `bl`=bitfield length, `pc`=participant popcount, `bls`=BLS
aggregate-verify result, `fl`=finality-branch depth, `fr`=finality reconstruct result,
`el`=execution-branch depth, `er`=execution reconstruct result.) -/
def decodeEthWire (s : String) :
    Option (Nat × Nat × Nat × Bool × Nat × Bool × Nat × Bool) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7] => do
      let cl ← (parseField? "cl" p0).bind String.toNat?
      let bl ← (parseField? "bl" p1).bind String.toNat?
      let pc ← (parseField? "pc" p2).bind String.toNat?
      let bls ← (parseField? "bls" p3).bind parseBit?
      let fl ← (parseField? "fl" p4).bind String.toNat?
      let fr ← (parseField? "fr" p5).bind parseBit?
      let el ← (parseField? "el" p6).bind String.toNat?
      let er ← (parseField? "er" p7).bind parseBit?
      some (cl, bl, pc, bls, fl, fr, el, er)
  | _ => none

/-- **`ethLcVerifyGate`** — THE GATE. Decode the wire, run the VERIFIED `ethVerifyDecision`
(refined to `verifyFinalizedUpdate`, over which `eth_no_forgery` is proven), and encode
`"1"` (ACCEPT) / `"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the node
treats it as REJECT — an unproven update is never accepted). -/
def ethLcVerifyGate (s : String) : String :=
  match decodeEthWire s with
  | some (cl, bl, pc, bls, fl, fr, el, er) =>
      if ethVerifyDecision cl bl pc bls fl fr el er then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_eth_lc_verify]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same `String → String` shape as `dregg_finalization_quorum`: the
`eth-lightclient` verify path computes the crypto primitives (`blst` aggregate verify + the
SHA-256 branch reconstructions) and passes the projections; the archive renders the verdict. -/
@[export dregg_eth_lc_verify]
def dregg_eth_lc_verify (s : String) : String := ethLcVerifyGate s

/-- **`ethLcVerifyGate_eq_decision` (the gate string IS the verified decision, by
construction).** For any wire that decodes to the eight projections, the exported gate's
output is `"1"`/`"0"` off `ethVerifyDecision` on them. So gating a node on this export gates
it, definitionally, on `ethVerifyDecision` — hence (via `ethVerifyDecision_refines`) on
`verifyFinalizedUpdate`. -/
theorem ethLcVerifyGate_eq_decision (s : String)
    (cl bl pc : Nat) (bls : Bool) (fl : Nat) (fr : Bool) (el : Nat) (er : Bool)
    (h : decodeEthWire s = some (cl, bl, pc, bls, fl, fr, el, er)) :
    ethLcVerifyGate s = (if ethVerifyDecision cl bl pc bls fl fr el er then "1" else "0") := by
  unfold ethLcVerifyGate
  rw [h]

/-! ## §4 — NON-VACUITY: the DECISION DISCRIMINATES (the assembled Nomad tooth), kernel-clean.

The scalar `ethVerifyDecision` is pure `Nat`/`Bool`, so `decide` reduces it in the kernel:
accepts a full-participation depth-6 update AND the exact-quorum-342 depth-7 update; REJECTS
the sub-quorum-341 update (3·341 = 1023 < 1024 = 2·512), the forged signature (`bls=false`),
the wrong-depth finality branch (5), a failed reconstruction (`fr=false`), a wrong committee
size (511), and a wrong execution depth (3). (The STRING wire layer — `String.splitOn` /
`String.toNat?` — uses well-founded recursion the KERNEL cannot reduce under `decide`; the
`#guard`s below run it in the interpreter at build time, and `ethLcVerifyGate_eq_decision`
ties the string surface to THIS decision without needing to reduce the parser.) -/

theorem eth_decision_discriminates :
    ethVerifyDecision 512 512 512 true 6 true 4 true = true
    ∧ ethVerifyDecision 512 512 342 true 7 true 4 true = true
    ∧ ethVerifyDecision 512 512 341 true 6 true 4 true = false
    ∧ ethVerifyDecision 512 512 512 false 6 true 4 true = false
    ∧ ethVerifyDecision 512 512 512 true 5 true 4 true = false
    ∧ ethVerifyDecision 512 512 512 true 6 false 4 true = false
    ∧ ethVerifyDecision 511 512 512 true 6 true 4 true = false
    ∧ ethVerifyDecision 512 512 512 true 6 true 3 true = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE EXPORTED DECISION ACCEPTS THE MODEL GOOD UPDATE, end-to-end.** The scalar decision,
fed `goodUpdate`'s true crypto projections under the genuine `modelState`, accepts — obtained
by refining to `verifyFinalizedUpdate` and reusing `eth_gate_discriminates` (so the projection
pipeline, crypto results included, is exercised). By `ethVerifyDecision_no_forgery` that
acceptance entails `EthValidAt`. -/
theorem gate_accepts_model_good :
    ethProjectedDecision modelLeaf modelState goodUpdate = true :=
  (ethVerifyDecision_refines modelLeaf modelState goodUpdate).trans eth_gate_discriminates.1

/-! ### It runs (`#guard`): the wire gate + the scalar decision discriminate on concrete data. -/

#guard ethLcVerifyGate "cl=512;bl=512;pc=512;bls=1;fl=6;fr=1;el=4;er=1" == "1"
#guard ethLcVerifyGate "cl=512;bl=512;pc=342;bls=1;fl=7;fr=1;el=4;er=1" == "1"
#guard ethLcVerifyGate "cl=512;bl=512;pc=341;bls=1;fl=6;fr=1;el=4;er=1" == "0"
#guard ethLcVerifyGate "cl=512;bl=512;pc=512;bls=1;fl=5;fr=1;el=4;er=1" == "0"
#guard ethLcVerifyGate "garbage" == "ERR"
#guard ethVerifyDecision 512 512 342 true 7 true 4 true == true
#guard ethVerifyDecision 512 512 341 true 6 true 4 true == false
#guard dregg_eth_lc_verify "cl=512;bl=512;pc=512;bls=1;fl=6;fr=1;el=4;er=1" == "1"

/-! ## §5 — Axiom hygiene: the refinement tie + the no-forgery composition + the wire
faithfulness are kernel-clean (the crypto carriers are the visible `EthLeaf` fields / the
`hcr`/`hinj` hypotheses, invisible to `#assert_axioms` exactly because they are the audit
surface — see `LightClientEth.lean` §12). -/

#assert_axioms syncDecision_refines
#assert_axioms finalityDecision_refines
#assert_axioms execDecision_refines
#assert_axioms ethVerifyDecision_refines
#assert_axioms ethVerifyDecision_no_forgery
#assert_axioms ethLcVerifyGate_eq_decision
#assert_axioms eth_decision_discriminates
#assert_axioms gate_accepts_model_good

#print axioms ethVerifyDecision_refines
#print axioms ethVerifyDecision_no_forgery

end Dregg2.Bridge.LightClientEthGate
