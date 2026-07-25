/-
# Dregg2.Bridge.LightClientTendermintGate — the RUNTIME-CALLABLE Cosmos/Tendermint light-client
VERIFY-LOGIC gate, `@[export] dregg_tm_lc_verify`, PROVEN to be the same accept/reject decision
the no-forgery theorem is stated over (`LightClientTendermint.tmVerify`).

## Why this module exists (the translation-validation closure for the Tendermint light client)

`Dregg2.Bridge.LightClientTendermint` proves `tmNoForgery` over `tmVerify` — a Lean RE-AUTHORING
of the Rust verifier's rules (`cosmos-lightclient/src/lib.rs`, `verify_cosmos_header`, which
delegates to the audited informalsystems `ProdVerifier`). There is (was) NO formal tie between
the deployed Rust decision and the proven Lean one: the Rust `verify_cosmos_header` and the Lean
`tmVerify` are TWINS that can drift. This is the same "proven over a re-authoring, not over the
emitted object" gap the ETH light-client twin-deletion closes (`LightClientEthGate.lean`) and
the conservation / finalization-quorum campaign closes generally, by `@[export]`-ing the Lean
DECISION and routing the Rust through it, fail-closed (`docs/TWIN-DELETION-MAP-2026-07-23.md`).

## The subtlety (heavy crypto stays a NAMED verified-FFI carrier; only the LOGIC is exported)

Tendermint verify is not pure logic — it invokes per-validator Ed25519 commit-signature checks
and SHA-256 validator-set hashing. So the twin-deletion boundary is drawn PRECISELY at the
STAKE-WEIGHTED verification LOGIC:

  * EXPORTED + PROVEN (this gate): the chain-id match, the adjacent-height advance
    (`height = trusted.height + 1`), the time window (monotonic advance, not-from-the-future
    under clock drift, trusted header still inside the trusting period), and — the load-bearing
    consensus arithmetic — the STRICT `> 2/3` stake threshold in its multiply form
    `2·totalPower < 3·signedPower` (no rounding trap; the exactly-2/3 boundary is REJECTED, as
    Tendermint requires). These are pure `Nat`/`Bool`, decidable in Lean with NO crypto, and are
    exactly the RULES-bug locus (a permissive threshold / a wrong adjacency / a stale-time
    acceptance is the Nomad class that drains bridges).
  * NAMED verified-FFI CARRIERS (supplied to the gate as their RESULTS): the per-validator
    Ed25519 batch-verify feeds `signedPower` — the summed voting power of validators whose commit
    signature verified against the canonical sign-bytes (the `CryptoLeaf.sigSound` carrier: a
    verifying signature means the validator genuinely signed; `signedPower` is that verified
    stake, computed in Rust, handed to the gate as a `Nat`). The SHA-256 validator-set hashing
    feeds the two binding RESULTS `epochBindOk` (the trusted `next_validators_hash` equals the
    hash of the untrusted validator-set encoding — the adjacent-advance epoch binding) and
    `selfBindOk` (the header self-binds its validator set), each the boolean outcome of a SHA-256
    hash-and-compare (the `CryptoLeaf.hashCR` carrier). The gate does NOT re-derive the crypto;
    it composes the accept/reject over the crypto RESULTS.

`tmVerifyDecision` is that composition over the eleven scalar/boolean projections a deployed node
computes (three of them carrying crypto RESULTS). The load-bearing theorem is
`tmVerifyDecision_refines`: fed the true projections of an update, the exported scalar decision is
DEFINITIONALLY `tmVerify L sb enc ts u` (`rfl`). So the deployed node, computing the Ed25519
batch-verify + SHA-256 hashes in the audited libraries and handing their results + the
combinatorial facts to `dregg_tm_lc_verify`, makes the ACCEPT/REJECT decision that `tmNoForgery`
is proven over — `tmVerifyDecision_no_forgery` states exactly that.

## The TRUSTED projections (named, not hidden)

`totalPower` (the sum of all validator voting powers) and `signedPower` (the summed verified
stake) are computed in Rust and supplied as `Nat`s — exactly as the `dregg_finalization_quorum`
gate trusts the collector to intern+dedup the `(signer,root)` tally and verifies the quorum
DECISION over it. `totalPower` is a mechanically-faithful power sum; `signedPower` is that sum
restricted to the validators whose Ed25519 signature verified (the crypto carrier). The VERIFIED
content is the `2·total < 3·signed` threshold DECISION over them.

## Scope (honest, current resolution)

`tmVerify` formalizes the ADJACENT-advance rule set (`height = trusted.height + 1`, bound by the
`next_validators_hash` epoch binding). The Rust `verify_cosmos_header` also accepts the
NON-ADJACENT / skipping shape (any higher height, bound by the trust-threshold overlap rule); the
Lean re-authoring does not yet cover it, so this gate exports exactly the adjacent decision
`tmVerify` proves. The skipping-overlap decision is the named follow-up rung (the same rung
`LightClientTendermint`'s header scopes), extended by the identical method once `tmVerify` gains
the overlap conjunct.
-/
import Dregg2.Bridge.LightClientTendermint

set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientTendermintGate

open Dregg2.Bridge.VerifiedLightClient
open Dregg2.Bridge.LightClientTendermint

/- **Axiom-hygiene note (kept the keystone genuinely axiom-free).** `LightClientTendermint`
declares `instance : DecidableEq demoLeaf.Digest` (line 435); because `demoLeaf.Digest` is
reducibly `Nat`, that instance is eligible for — and gets picked by — every downstream
`decide (n = m : Nat)`, and it transitively drags in `demoLeaf` → `demoSigSound` (a `by simp`
proof, hence `propext`). `tmVerify` itself is axiom-free only because it is defined BEFORE that
instance. Locally dropping it here makes the two pure-`Nat` equality decides in `tmVerifyDecision`
resolve to the core `DecidableEq Nat` (axiom-free), so `tmVerifyDecision_refines` reports "does not
depend on any axioms" — matching the ETH template. `DecidableEq demoLeaf.Digest` still resolves for
the demo-instance theorems below (core `instDecidableEqNat` serves it via the reducible
`demoLeaf.Digest ≡ Nat`), and every refinement stays `rfl` (all `DecidableEq Nat` are def-eq). -/
attribute [-instance] Dregg2.Bridge.LightClientTendermint.instDecidableEqDigestDemoLeaf

/-! ## §1 — THE composed stake-weighted verify-logic decision, over the scalar/boolean projections
a deployed node computes. Grouped to MATCH `tmVerify`'s `&&`-chain EXACTLY (so the refinement below
is `rfl`). It takes the combinatorial facts plus the crypto primitives' RESULTS; it re-derives no
crypto. -/

/-- **`tmVerifyDecision`** — THE composed Tendermint verify-logic decision, over the eleven
scalar/boolean projections (`epochBindOk` / `selfBindOk` carry the SHA-256 binding results,
`signedPow` carries the Ed25519-verified stake). Grouped `chain && height && time-window && bindings
&& threshold` to match `tmVerify` term-for-term. This is the object `@[export] dregg_tm_lc_verify`
renders and `tmNoForgery` is (via `tmVerifyDecision_refines`) proven over. The threshold is the
STRICT `> 2/3` in multiply form `2·totalPow < 3·signedPow` — the exactly-2/3 boundary rejects. -/
def tmVerifyDecision (chainId tsChainId height tsHeight headerTime time now clockDrift
    trustingPeriod : Nat) (epochBindOk selfBindOk : Bool) (totalPow signedPow : Nat) : Bool :=
  decide (chainId = tsChainId)
  && decide (height = tsHeight + 1)
  && decide (headerTime < time)
  && decide (time ≤ now + clockDrift)
  && decide (now < headerTime + trustingPeriod)
  && epochBindOk
  && selfBindOk
  && decide (2 * totalPow < 3 * signedPow)

/-! ## §2 — THE REFINEMENT TIE: the exported scalar decision IS `tmVerify`.

`tmProjectedDecision` feeds `tmVerifyDecision` the eight true projections of an update under a
trusted state — the nine scalar facts, the two SHA-256 binding RESULTS, and the two power sums (one
of which, `signedPower`, is the Ed25519-verified stake). `tmVerifyDecision_refines` is the
translation-validation object: it turns "proven over a re-authoring" into "the deployed
accept/reject decision IS the proven Lean object", modulo the three named crypto carriers supplied
as their results. -/

/-- **`tmProjectedDecision`** — the projections a node hands the gate for an update `u` under
trusted state `ts`: the chain-ids, heights, and time scalars (`Nat`); the two SHA-256 hash-and-
compare RESULTS (`decide (L.hash (enc u.validators) = …)`); and the total / Ed25519-verified power
sums. The crypto carriers appear here (and NOWHERE else in the gate) as their boolean / `Nat`
results. -/
def tmProjectedDecision (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (ts : TmTrustedState L) (u : TmUpdate L) : Bool :=
  tmVerifyDecision u.header.chainId ts.chainId u.header.height ts.height
    ts.headerTime u.header.time ts.now ts.clockDrift ts.trustingPeriod
    (decide (L.hash (enc u.validators) = ts.nextValidatorsHash))
    (decide (L.hash (enc u.validators) = u.header.validatorsHash))
    (totalPower u.validators)
    (signedPower L (sb u.header) u.validators u.commit)

/-- **THE TRANSLATION-VALIDATION THEOREM.** Fed an update's true projections, the exported scalar
decision is DEFINITIONALLY the proven gate `tmVerify L sb enc ts u`. So gating a deployed node on
`dregg_tm_lc_verify` (with the Ed25519 batch-verify + SHA-256 hashes computed in the audited
libraries) gates it, definitionally, on the decision `tmNoForgery` is proven over. -/
theorem tmVerifyDecision_refines (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (ts : TmTrustedState L) (u : TmUpdate L) :
    tmProjectedDecision L sb enc ts u = tmVerify L sb enc ts u := rfl

/-- **THE PAYOFF: acceptance by the EXPORTED scalar decision entails Tendermint foreign-validity.**
GIVEN the SHA-256 CR carrier (`hcr : L.hashCR`), if the projected `tmVerifyDecision` accepts `u`,
then `u` is foreign-VALID relative to the trusted state — its `validatorsHash` genuinely commits its
validator set, that commitment BINDS (uniqueness via `noCollision`), and a sub-list of that set
carrying strictly more than 2/3 of the total power GENUINELY signed the header's sign-bytes (the
`Signed` denotation, via `sigSound`). This is `tmNoForgery` routed through the deployed decision. -/
theorem tmVerifyDecision_no_forgery (L : CryptoLeaf) [DecidableEq L.Digest]
    (sb : TmHeader L.Digest → L.Msg) (enc : List (TmValidator L.PubKey) → L.Msg)
    (hcr : L.hashCR) (ts : TmTrustedState L) (u : TmUpdate L)
    (h : tmProjectedDecision L sb enc ts u = true) :
    TmForeignValid L sb enc u :=
  tmNoForgery L sb enc hcr ts u ((tmVerifyDecision_refines L sb enc ts u) ▸ h)

/-! ## §3 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_eth_lc_verify` / `dregg_finalization_quorum`. Fail-closed on any malformed wire (`"ERR"` ⇒
the node treats it as REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- **`decodeTmWire`** — parse the full `INPUT` grammar into the eleven projections. Fail-closed
(`none`) on any deviation.

```
INPUT := "ci=" Nat ";tci=" Nat ";h=" Nat ";th=" Nat ";ht=" Nat ";t=" Nat
       ";nw=" Nat ";cd=" Nat ";tp=" Nat ";eb=" BIT ";vb=" BIT ";tot=" Nat ";sp=" Nat
BIT   := "0" | "1"
```
(`ci`=untrusted chain-id, `tci`=trusted chain-id, `h`=untrusted height, `th`=trusted height,
`ht`=trusted header time, `t`=untrusted time, `nw`=now, `cd`=clock drift, `tp`=trusting period,
`eb`=epoch-binding SHA-256 result, `vb`=header-self-binding SHA-256 result, `tot`=total voting
power, `sp`=Ed25519-verified signed power.) -/
def decodeTmWire (s : String) :
    Option (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Bool × Bool × Nat × Nat) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12] => do
      let ci  ← (parseField? "ci"  p0).bind String.toNat?
      let tci ← (parseField? "tci" p1).bind String.toNat?
      let h   ← (parseField? "h"   p2).bind String.toNat?
      let th  ← (parseField? "th"  p3).bind String.toNat?
      let ht  ← (parseField? "ht"  p4).bind String.toNat?
      let t   ← (parseField? "t"   p5).bind String.toNat?
      let nw  ← (parseField? "nw"  p6).bind String.toNat?
      let cd  ← (parseField? "cd"  p7).bind String.toNat?
      let tp  ← (parseField? "tp"  p8).bind String.toNat?
      let eb  ← (parseField? "eb"  p9).bind parseBit?
      let vb  ← (parseField? "vb"  p10).bind parseBit?
      let tot ← (parseField? "tot" p11).bind String.toNat?
      let sp  ← (parseField? "sp"  p12).bind String.toNat?
      some (ci, tci, h, th, ht, t, nw, cd, tp, eb, vb, tot, sp)
  | _ => none

/-- **`tmLcVerifyGate`** — THE GATE. Decode the wire, run the VERIFIED `tmVerifyDecision` (refined to
`tmVerify`, over which `tmNoForgery` is proven), and encode `"1"` (ACCEPT) / `"0"` (REJECT). A
malformed wire returns `"ERR"` (fail-closed: the node treats it as REJECT). -/
def tmLcVerifyGate (s : String) : String :=
  match decodeTmWire s with
  | some (ci, tci, h, th, ht, t, nw, cd, tp, eb, vb, tot, sp) =>
      if tmVerifyDecision ci tci h th ht t nw cd tp eb vb tot sp then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_tm_lc_verify]` — the C-ABI entry the node's FFI bridge
(`dregg-lean-ffi`) calls. Same `String → String` shape as `dregg_eth_lc_verify`: the
`cosmos-lightclient` verify path computes the Ed25519 batch-verify + SHA-256 validator-set hashes
and passes the projections; the archive renders the verdict. -/
@[export dregg_tm_lc_verify]
def dregg_tm_lc_verify (s : String) : String := tmLcVerifyGate s

/-- **`tmLcVerifyGate_eq_decision` (the gate string IS the verified decision, by construction).**
For any wire that decodes to the eleven projections, the exported gate's output is `"1"`/`"0"` off
`tmVerifyDecision` on them — so gating a node on this export gates it, definitionally, on
`tmVerifyDecision`, hence (via `tmVerifyDecision_refines`) on `tmVerify`. -/
theorem tmLcVerifyGate_eq_decision (s : String)
    (ci tci h th ht t nw cd tp : Nat) (eb vb : Bool) (tot sp : Nat)
    (hd : decodeTmWire s = some (ci, tci, h, th, ht, t, nw, cd, tp, eb, vb, tot, sp)) :
    tmLcVerifyGate s
      = (if tmVerifyDecision ci tci h th ht t nw cd tp eb vb tot sp then "1" else "0") := by
  unfold tmLcVerifyGate
  rw [hd]

/-! ## §4 — NON-VACUITY: the DECISION DISCRIMINATES (the assembled Nomad tooth), kernel-clean.

The scalar `tmVerifyDecision` is pure `Nat`/`Bool`, so `decide` reduces it in the kernel: it accepts
a genuine adjacent 3-of-3-stake update AND REJECTS the exactly-2/3 sub-quorum (strict threshold), a
wrong chain-id, a non-adjacent height, a stale (non-monotonic) time, a future time, an expired
trusting period, a failed epoch binding, and a failed self binding. (The STRING wire layer uses
well-founded recursion the KERNEL cannot reduce under `decide`; the `#guard`s below run it in the
interpreter at build time, and `tmLcVerifyGate_eq_decision` ties the string surface to THIS decision
without needing to reduce the parser.) -/

theorem tm_decision_discriminates :
    tmVerifyDecision 5 5 11 10 50 55 60 5 100 true true 3 3 = true
    ∧ tmVerifyDecision 5 5 11 10 50 55 60 5 100 true true 3 2 = false
    ∧ tmVerifyDecision 6 5 11 10 50 55 60 5 100 true true 3 3 = false
    ∧ tmVerifyDecision 5 5 12 10 50 55 60 5 100 true true 3 3 = false
    ∧ tmVerifyDecision 5 5 11 10 50 45 60 5 100 true true 3 3 = false
    ∧ tmVerifyDecision 5 5 11 10 50 99 60 5 100 true true 3 3 = false
    ∧ tmVerifyDecision 5 5 11 10 50 55 200 5 100 true true 3 3 = false
    ∧ tmVerifyDecision 5 5 11 10 50 55 60 5 100 false true 3 3 = false
    ∧ tmVerifyDecision 5 5 11 10 50 55 60 5 100 true false 3 3 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE EXPORTED DECISION ACCEPTS THE MODEL GOOD UPDATE, end-to-end.** The scalar decision, fed
`genuineUpdate`'s true crypto projections under the genuine `ts0`, accepts — obtained by refining to
`tmVerify` and reusing `tm_gate_discriminates` (so the projection pipeline, crypto results included,
is exercised). By `tmVerifyDecision_no_forgery` that acceptance entails `TmForeignValid`. -/
theorem tm_gate_accepts_model_good :
    tmProjectedDecision demoLeaf demoSignBytes demoValSetEncode ts0 genuineUpdate = true :=
  (tmVerifyDecision_refines demoLeaf demoSignBytes demoValSetEncode ts0 genuineUpdate).trans
    tm_gate_discriminates.1

/-! ### It runs (`#guard`): the wire gate + the scalar decision discriminate on concrete data. -/

#guard tmLcVerifyGate "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3" == "1"
#guard tmLcVerifyGate "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=2" == "0"
#guard tmLcVerifyGate "ci=6;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3" == "0"
#guard tmLcVerifyGate "garbage" == "ERR"
#guard tmVerifyDecision 5 5 11 10 50 55 60 5 100 true true 3 3 == true
#guard tmVerifyDecision 5 5 11 10 50 55 60 5 100 true true 3 2 == false
#guard dregg_tm_lc_verify "ci=5;tci=5;h=11;th=10;ht=50;t=55;nw=60;cd=5;tp=100;eb=1;vb=1;tot=3;sp=3" == "1"

/-! ## §5 — Axiom hygiene: the refinement tie + the no-forgery composition + the wire faithfulness
are kernel-clean (the crypto carriers are the visible `CryptoLeaf` fields / the `hcr` hypothesis,
invisible to `#assert_axioms` exactly because they are the audit surface — see
`LightClientTendermint.lean` §8). -/

#assert_axioms tmVerifyDecision_refines
#assert_axioms tmVerifyDecision_no_forgery
#assert_axioms tmLcVerifyGate_eq_decision
#assert_axioms tm_decision_discriminates
#assert_axioms tm_gate_accepts_model_good

#print axioms tmVerifyDecision_refines
#print axioms tmVerifyDecision_no_forgery

end Dregg2.Bridge.LightClientTendermintGate
