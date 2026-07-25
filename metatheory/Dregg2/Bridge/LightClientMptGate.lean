/-
# Dregg2.Bridge.LightClientMptGate — the RUNTIME-CALLABLE EVM state-inclusion (EIP-1186) light-
client VERIFY-LOGIC gate, `@[export] dregg_mpt_lc_verify`, PROVEN to be the same accept/reject
decision the no-forgery / balance-binding theorems are stated over (`LightClientMpt.mptVerify`).

## Why this module exists (the translation-validation closure for the EVM-inclusion light client)

`Dregg2.Bridge.LightClientMpt` proves `mpt_noForgery` / `mpt_balance_binding` over `mptVerify` — a
Lean RE-AUTHORING of the Rust verifier's rules (`eth-lightclient/src/evm.rs`,
`verify_erc20_holding` composing `verify_evm_account_proof` + `verify_evm_storage_slot`). There is
(was) NO formal tie between the deployed Rust decision and the proven Lean one: the Rust
`verify_erc20_holding` and the Lean `mptVerify` are TWINS that can drift. This is the same "proven
over a re-authoring, not over the emitted object" gap the ETH light-client twin-deletion closes
(`LightClientEthGate.lean`), by `@[export]`-ing the Lean DECISION and routing the Rust through it,
fail-closed (`docs/TWIN-DELETION-MAP-2026-07-23.md`).

## The subtlety (the keccak-interleaved path walk stays a NAMED verified-FFI carrier)

EVM inclusion verify is a keccak-interleaved Merkle-Patricia path walk (alloy-trie's audited
EIP-1186 `verify_proof`) — heavy crypto, not pure logic. So the twin-deletion boundary is drawn
PRECISELY at the higher-level BINDING logic:

  * EXPORTED + PROVEN (this gate): the Nomad-law zero floor (`claimedBalance ≠ 0`), and the anchor
    bindings — the update's carried `state_root` / `token` / `mappingSlot` must equal the TRUSTED
    ones (`evm.rs:53-57` demands the consumer opens against the finality-verified root at the right
    contract/slot). These are pure `Nat`/`Bool`, decidable in Lean with NO crypto, and are exactly
    the RULES-bug locus (a zero-holding minted, or a proof opened against an unrelated root / the
    wrong contract, is the class that forges holdings).
  * NAMED verified-FFI CARRIERS (supplied to the gate as their RESULTS): the two MPT path-walk
    verdicts — `accountProofOk` (the account trie opens `keccak(token)` to the RLP-encoded
    `[nonce,balance,storageRoot,codeHash]` account under the state root) and `storageProofOk` (the
    storage trie opens the holder's derived slot key to the claimed balance under that account's OWN
    `storageHash`). Each is the boolean outcome of alloy-trie's keccak-interleaved `verify_proof`
    (the `CryptoLeaf.hashCR` / keccak256-CR carrier: the RLP account extraction, the
    `keccak256(pad32(holder) ‖ pad32(slot))` slot-key derivation, and the terminal-value equality
    are what the walk establishes). The gate does NOT re-walk the trie; it composes the
    accept/reject over the two walk RESULTS.

`mptVerifyDecision` is that composition over the nine scalar/boolean projections a deployed node
computes (two of them being the path-walk results). The load-bearing theorem is
`mptVerifyDecision_refines`: fed the true projections of an update, the exported scalar decision is
DEFINITIONALLY `mptVerify H ts u` (`rfl`). So the deployed node, running alloy-trie's `verify_proof`
for the two tiers and handing their results + the zero floor / anchor facts to `dregg_mpt_lc_verify`,
makes the ACCEPT/REJECT decision that `mpt_noForgery` AND `mpt_balance_binding` are proven over —
`mptVerifyDecision_no_forgery` / `mptVerifyDecision_balance_binding` state exactly that.

## The digest projections (named, not hidden)

`state_root` / `token` / `mappingSlot` are the model's `Nat` digests/identifiers (a production
instance carries the 32-byte keccak values); the node hands both the update's carried values and the
trusted ones, and the gate re-checks the equality bindings in Lean — that is the "terminal-value
equality" LOGIC being PROVEN, not delegated. The keccak carrier lives entirely inside the two
path-walk booleans.
-/
import Dregg2.Bridge.LightClientMpt

set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientMptGate

open Dregg2.Bridge.VerifiedLightClient
open Dregg2.Bridge.LightClientMpt

/-! ## §1 — THE composed EVM-inclusion verify-logic decision, over the scalar/boolean projections a
deployed node computes. Grouped to MATCH `mptVerify`'s `&&`-chain EXACTLY (so the refinement below is
`rfl`). It takes the zero floor + anchor facts plus the two path-walk RESULTS; it re-walks no trie. -/

/-- **`mptVerifyDecision`** — THE composed EVM-inclusion verify-logic decision, over the nine
scalar/boolean projections (`accountProofOk` / `storageProofOk` carry the keccak-interleaved
alloy-trie `verify_proof` results). Grouped `zero-floor && anchor-bindings && account-walk &&
storage-walk` to match `mptVerify` term-for-term. This is the object `@[export] dregg_mpt_lc_verify`
renders and `mpt_noForgery` / `mpt_balance_binding` are (via `mptVerifyDecision_refines`) proven
over. -/
def mptVerifyDecision (claimedBalance stateRoot tsStateRoot token tsToken mappingSlot
    tsMappingSlot : Nat) (accountProofOk storageProofOk : Bool) : Bool :=
  (claimedBalance != 0)
    && (stateRoot == tsStateRoot)
    && (token == tsToken)
    && (mappingSlot == tsMappingSlot)
    && accountProofOk
    && storageProofOk

/-! ## §2 — THE REFINEMENT TIE: the exported scalar decision IS `mptVerify`.

`mptProjectedDecision` feeds `mptVerifyDecision` the true projections of an update under a trusted
state — the balance / anchor scalars, and the two keccak-interleaved path-walk RESULTS.
`mptVerifyDecision_refines` is the translation-validation object: it turns "proven over a
re-authoring" into "the deployed accept/reject decision IS the proven Lean object", modulo the two
named keccak carriers supplied as their `verify_proof` results. -/

/-- **`mptProjectedDecision`** — the projections a node hands the gate for an update `u` under
trusted state `ts`: the claimed balance + the update/trusted anchor scalars (`Nat`), and the two
alloy-trie `verify_proof` RESULTS (account trie opens `keccak(token)` to the RLP account under the
state root; storage trie opens the derived slot to the claimed balance under the account's
`storageHash`). The keccak carriers appear here (and NOWHERE else in the gate) as opaque boolean
results. -/
def mptProjectedDecision (H : List Nat → Nat) (ts : MptState) (u : MptUpdate) : Bool :=
  mptVerifyDecision u.claimedBalance u.stateRoot ts.stateRoot u.token ts.token
    u.mappingSlot ts.mappingSlot
    (verifyPath H u.stateRoot (accountPath H u.token) (encAccount u.account) u.accountProof)
    (verifyPath H u.account.storageHash (storagePath H u.holder u.mappingSlot)
      (encBalance u.claimedBalance) u.storageProof)

/-- **THE TRANSLATION-VALIDATION THEOREM.** Fed an update's true projections, the exported scalar
decision is DEFINITIONALLY the proven gate `mptVerify H ts u`. So gating a deployed node on
`dregg_mpt_lc_verify` (with the two keccak-interleaved path walks computed in alloy-trie) gates it,
definitionally, on the decision `mpt_noForgery` and `mpt_balance_binding` are proven over. -/
theorem mptVerifyDecision_refines (H : List Nat → Nat) (ts : MptState) (u : MptUpdate) :
    mptProjectedDecision H ts u = mptVerify H ts u := rfl

/-- **THE PAYOFF: acceptance by the EXPORTED scalar decision entails EVM foreign-validity.** GIVEN
the keccak-CR floor (`hCR` — the unpacked CR carrier), if the projected `mptVerifyDecision` accepts
`u`, then `u` is foreign-VALID: the balance is nonzero, the account is genuinely committed at the
token's hashed key under the state root, the balance is genuinely committed at the holder's derived
slot under that account's `storageHash`, AND the slot BINDS (no other balance is committed there —
forging a second balance is a keccak collision). This is `mpt_noForgery` routed through the deployed
decision. -/
theorem mptVerifyDecision_no_forgery (H : List Nat → Nat)
    (hCR : ∀ m₁ m₂, H m₁ = H m₂ → m₁ = m₂) (ts : MptState) (u : MptUpdate)
    (h : mptProjectedDecision H ts u = true) :
    MptForeignValid H u :=
  mpt_noForgery H hCR ts u ((mptVerifyDecision_refines H ts u) ▸ h)

/-- **BALANCE BINDING, ROUTED THROUGH THE DEPLOYED DECISION.** Under ONE trusted state, ONE holder
has ONE provable balance: two updates the EXPORTED decision accepts for the same holder agree. The
keccak-CR floor is consumed through both tiers (`mpt_balance_binding`); forging a different balance
for a committed holder REQUIRES a keccak collision. This is the theorem the Merkle-Patricia structure
exists to provide, now stated over the object the deployed node actually gates on. -/
theorem mptVerifyDecision_balance_binding (H : List Nat → Nat)
    (hCR : ∀ m₁ m₂, H m₁ = H m₂ → m₁ = m₂)
    (ts : MptState) (u₁ u₂ : MptUpdate)
    (h₁ : mptProjectedDecision H ts u₁ = true) (h₂ : mptProjectedDecision H ts u₂ = true)
    (hholder : u₁.holder = u₂.holder) :
    u₁.claimedBalance = u₂.claimedBalance :=
  mpt_balance_binding H hCR ts u₁ u₂
    ((mptVerifyDecision_refines H ts u₁) ▸ h₁)
    ((mptVerifyDecision_refines H ts u₂) ▸ h₂) hholder

/-! ## §3 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as `dregg_eth_lc_verify`
/ `dregg_finalization_quorum`. Fail-closed on any malformed wire (`"ERR"` ⇒ the node treats it as
REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- **`decodeMptWire`** — parse the full `INPUT` grammar into the nine projections. Fail-closed
(`none`) on any deviation.

```
INPUT := "bal=" Nat ";sr=" Nat ";tsr=" Nat ";tk=" Nat ";ttk=" Nat ";ms=" Nat ";tms=" Nat
       ";ap=" BIT ";sp=" BIT
BIT   := "0" | "1"
```
(`bal`=claimed balance, `sr`=update state root, `tsr`=trusted state root, `tk`=update token,
`ttk`=trusted token, `ms`=update mapping slot, `tms`=trusted mapping slot, `ap`=account path-walk
result, `sp`=storage path-walk result.) -/
def decodeMptWire (s : String) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool × Bool) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8] => do
      let bal ← (parseField? "bal" p0).bind String.toNat?
      let sr  ← (parseField? "sr"  p1).bind String.toNat?
      let tsr ← (parseField? "tsr" p2).bind String.toNat?
      let tk  ← (parseField? "tk"  p3).bind String.toNat?
      let ttk ← (parseField? "ttk" p4).bind String.toNat?
      let ms  ← (parseField? "ms"  p5).bind String.toNat?
      let tms ← (parseField? "tms" p6).bind String.toNat?
      let ap  ← (parseField? "ap"  p7).bind parseBit?
      let sp  ← (parseField? "sp"  p8).bind parseBit?
      some (bal, sr, tsr, tk, ttk, ms, tms, ap, sp)
  | _ => none

/-- **`mptLcVerifyGate`** — THE GATE. Decode the wire, run the VERIFIED `mptVerifyDecision` (refined
to `mptVerify`, over which `mpt_noForgery` / `mpt_balance_binding` are proven), and encode `"1"`
(ACCEPT) / `"0"` (REJECT). A malformed wire returns `"ERR"` (fail-closed: the node treats it as
REJECT). -/
def mptLcVerifyGate (s : String) : String :=
  match decodeMptWire s with
  | some (bal, sr, tsr, tk, ttk, ms, tms, ap, sp) =>
      if mptVerifyDecision bal sr tsr tk ttk ms tms ap sp then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mpt_lc_verify]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same `String → String` shape as `dregg_eth_lc_verify`: the `eth-lightclient`
verify path computes the two keccak-interleaved alloy-trie walks and passes the projections; the
archive renders the verdict. -/
@[export dregg_mpt_lc_verify]
def dregg_mpt_lc_verify (s : String) : String := mptLcVerifyGate s

/-- **`mptLcVerifyGate_eq_decision` (the gate string IS the verified decision, by construction).**
For any wire that decodes to the nine projections, the exported gate's output is `"1"`/`"0"` off
`mptVerifyDecision` on them — so gating a node on this export gates it, definitionally, on
`mptVerifyDecision`, hence (via `mptVerifyDecision_refines`) on `mptVerify`. -/
theorem mptLcVerifyGate_eq_decision (s : String)
    (bal sr tsr tk ttk ms tms : Nat) (ap sp : Bool)
    (hd : decodeMptWire s = some (bal, sr, tsr, tk, ttk, ms, tms, ap, sp)) :
    mptLcVerifyGate s = (if mptVerifyDecision bal sr tsr tk ttk ms tms ap sp then "1" else "0") := by
  unfold mptLcVerifyGate
  rw [hd]

/-! ## §4 — NON-VACUITY: the DECISION DISCRIMINATES (the assembled Nomad tooth), kernel-clean.

The scalar `mptVerifyDecision` is pure `Nat`/`Bool`, so `decide` reduces it in the kernel: it accepts
a genuine nonzero holding under matched anchors + verifying walks AND REJECTS the zero-balance floor,
a wrong state root, a wrong contract, a wrong mapping slot, a failed account walk, and a failed
storage walk. (The STRING wire layer uses well-founded recursion the KERNEL cannot reduce under
`decide`; the `#guard`s below run it in the interpreter at build time, and
`mptLcVerifyGate_eq_decision` ties the string surface to THIS decision without needing to reduce the
parser.) -/

theorem mpt_decision_discriminates :
    mptVerifyDecision 5 100 100 1 1 0 0 true true = true
    ∧ mptVerifyDecision 0 100 100 1 1 0 0 true true = false
    ∧ mptVerifyDecision 5 999 100 1 1 0 0 true true = false
    ∧ mptVerifyDecision 5 100 100 3 1 0 0 true true = false
    ∧ mptVerifyDecision 5 100 100 1 1 7 0 true true = false
    ∧ mptVerifyDecision 5 100 100 1 1 0 0 false true = false
    ∧ mptVerifyDecision 5 100 100 1 1 0 0 true false = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE EXPORTED DECISION ACCEPTS THE MODEL GOOD HOLDING, end-to-end.** The scalar decision, fed
`exUpdate`'s true keccak projections under the genuine `exState`, accepts — obtained by refining to
`mptVerify` and reusing `mpt_gate_discriminates` (so the two-tier path-walk pipeline is exercised).
By `mptVerifyDecision_no_forgery` that acceptance entails `MptForeignValid`. -/
theorem mpt_gate_accepts_model_good :
    mptProjectedDecision toyKeccak exState exUpdate = true :=
  (mptVerifyDecision_refines toyKeccak exState exUpdate).trans mpt_gate_discriminates.1

/-! ### It runs (`#guard`): the wire gate + the scalar decision discriminate on concrete data. -/

#guard mptLcVerifyGate "bal=5;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1" == "1"
#guard mptLcVerifyGate "bal=0;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1" == "0"
#guard mptLcVerifyGate "bal=5;sr=999;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1" == "0"
#guard mptLcVerifyGate "garbage" == "ERR"
#guard mptVerifyDecision 5 100 100 1 1 0 0 true true == true
#guard mptVerifyDecision 0 100 100 1 1 0 0 true true == false
#guard dregg_mpt_lc_verify "bal=5;sr=100;tsr=100;tk=1;ttk=1;ms=0;tms=0;ap=1;sp=1" == "1"

/-! ## §5 — Axiom hygiene: the refinement tie + the no-forgery / balance-binding compositions + the
wire faithfulness are kernel-clean (the keccak carrier is the visible `H`/`hCR` hypothesis, invisible
to `#assert_axioms` exactly because it is the audit surface — see `LightClientMpt.lean` §8). -/

#assert_axioms mptVerifyDecision_refines
#assert_axioms mptVerifyDecision_no_forgery
#assert_axioms mptVerifyDecision_balance_binding
#assert_axioms mptLcVerifyGate_eq_decision
#assert_axioms mpt_decision_discriminates
#assert_axioms mpt_gate_accepts_model_good

#print axioms mptVerifyDecision_refines
#print axioms mptVerifyDecision_balance_binding

end Dregg2.Bridge.LightClientMptGate
