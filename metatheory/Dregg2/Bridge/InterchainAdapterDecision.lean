/-
# Dregg2.Bridge.InterchainAdapterDecision — the interchain TRUST verdict as a verified Lean object.

Every inbound bridge leg (`bridge/src/interchain_adapter.rs`) collapses its per-chain trust dial —
Solana's `LockProofTrust`, Ethereum's `SnarkSystem`, Midnight's optimistic-watchtower `Verdict`, a
BFT-committee `FinalizedAttestation` — onto ONE ordinal, `TrustRung`, and answers a single
fail-closed question before it may mint: *did this evidence reach consensus?* That bool becomes
`BridgeMintRequest::consensus_verified`, which the committed mint gate refuses when `false`
(`BridgeMintError::TrustTooLow`).

Following the `Dregg2.Bridge.ProofOfHoldings` exemplar (the "Lean-first, the assurance IS the code"
shape shared with `Fips204Verify` / `R3Verify`): the fail-closed consensus VERDICT lives here as a
plain executable `def` (`reachedConsensusCore`), proved to REALIZE its intended fail-closed spec
(`reachedConsensusCore_correct`), and `@[export]`ed as `reachedConsensusFFI` so the live Rust
`TrustRung::reached_consensus` CALLS it — the DECISION is rendered by the proven object, not a Rust
`match`.

THE NOMAD-LAW DISCRIMINATOR (load-bearing, non-vacuous): the verdict is `true` ONLY for a
cryptographic `proof`, a *resolved-valid* watchtower, and a *quorum-reached* committee. The bare-RPC
rung (`rpc`), an *unresolved/fraudulent* watchtower, and a *no-quorum* committee are all `false` —
the lowest-trust / uninitialized dial value CANNOT mint (the $190M Nomad hack accepted every unproven
message because an uninitialized slot defaulted to "accepted"; here it defaults to REFUSED).

Kernel-clean: `#assert_axioms` hard-gates every theorem.
-/
import Dregg2.Tactics

namespace Dregg2.Bridge.InterchainAdapterDecision

/-! ## §1 — The trust ordinal (the Lean mirror of the Rust `TrustRung`).

`TrustRung` mirrors `bridge/src/interchain_adapter.rs`'s enum: the four per-chain dials each collapse
onto exactly one of these. `optimisticWatchtower` and `committee` carry the resolution/quorum bit so
an *unresolved* watchtower or a *no-quorum* committee stays fail-closed on its own. -/

/-- **`TrustRung`** — the single trust ordinal every inbound bridge leg collapses onto. Mirrors the
Rust `TrustRung` (`Proof` / `OptimisticWatchtower { resolved_valid }` / `Committee { has_quorum }` /
`Rpc`). -/
inductive TrustRung
  /-- A cryptographic proof verified (a Solana `ConsensusVerified` lock proof, or an Ethereum SNARK).
  The highest, trustless rung — always reaches consensus. -/
  | proof
  /-- An optimistic watchtower verdict (Midnight). `resolvedValid` is `true` only when the challenge
  window resolved in favor of validity; a fraud verdict leaves it `false`. -/
  | optimisticWatchtower (resolvedValid : Bool)
  /-- A BFT committee quorum finalized the root. `hasQuorum` is `true` only when a supermajority of
  DISTINCT trusted-committee signers was counted; a zero-signer (default/empty) attestation is
  `false`. -/
  | committee (hasQuorum : Bool)
  /-- A bare-RPC echo / structure-only well-formedness check with no consensus. NEVER trustless —
  the fail-closed floor. -/
  | rpc
deriving DecidableEq, Repr

/-! ## §2 — THE EXECUTABLE, EXPORTED consensus VERDICT + its realizes-spec proof. -/

/-- **`reachedConsensusCore r`** — THE fail-closed consensus verdict, the executable object the Rust
`TrustRung::reached_consensus` routes through. `true` only for a `proof`, a resolved-valid
watchtower, and a quorum-reached committee; `rpc` — and an unresolved watchtower or a no-quorum
committee — are `false`. This IS the decision `@[export]` compiles to native and the bridge calls;
the per-chain dial→rung `From`-conversions remain fast-Rust, but this VERDICT on the rung is the
verified Lean object. -/
def reachedConsensusCore : TrustRung → Bool
  | .proof => true
  | .optimisticWatchtower rv => rv
  | .committee hq => hq
  | .rpc => false

/-- **`reachesConsensusSpec r`** — the INTENDED fail-closed consensus spec as a `Prop`. A `proof`
always reaches consensus; a watchtower reaches iff it resolved valid; a committee reaches iff it hit
quorum; `rpc` NEVER reaches (the Nomad-law floor). -/
def reachesConsensusSpec : TrustRung → Prop
  | .proof => True
  | .optimisticWatchtower rv => rv = true
  | .committee hq => hq = true
  | .rpc => False

/-- **`reachedConsensusCore_correct` (THE DECISION REALIZES THE SPEC).** The exported verdict is
`true` IFF the `reachesConsensusSpec` predicate holds — so routing the trust verdict through
`reachedConsensusCore` computes EXACTLY the fail-closed spec, not a weaker or divergent Rust mirror.
The `rpc` arm reduces to `False` (never reaches) and the watchtower/committee arms reduce to their
carried bit, making this NON-VACUOUS on both polarities. -/
theorem reachedConsensusCore_correct (r : TrustRung) :
    reachedConsensusCore r = true ↔ reachesConsensusSpec r := by
  cases r with
  | proof => simp [reachedConsensusCore, reachesConsensusSpec]
  | optimisticWatchtower rv => simp [reachedConsensusCore, reachesConsensusSpec]
  | committee hq => simp [reachedConsensusCore, reachesConsensusSpec]
  | rpc => simp [reachedConsensusCore, reachesConsensusSpec]

/-! ## §3 — NON-VACUITY: the verdict DISCRIMINATES (the Nomad-law tooth on every rung). -/

/-- **PROOF REACHES (positive).** A cryptographic proof always reaches consensus. -/
theorem proof_reaches : reachedConsensusCore .proof = true := rfl

/-- **RPC REFUSES (the fail-closed floor, negative).** The bare-RPC / structure-only rung — the
default/lowest-trust dial value — NEVER reaches consensus. -/
theorem rpc_refuses : reachedConsensusCore .rpc = false := rfl

/-- **RESOLVED-VALID WATCHTOWER REACHES (positive).** -/
theorem watchtower_valid_reaches : reachedConsensusCore (.optimisticWatchtower true) = true := rfl

/-- **FRAUD/UNRESOLVED WATCHTOWER REFUSES (negative).** The SAME watchtower rung with the resolution
bit `false` (a fraud verdict or an unresolved challenge window) does NOT reach consensus. -/
theorem watchtower_fraud_refuses : reachedConsensusCore (.optimisticWatchtower false) = false := rfl

/-- **QUORUM COMMITTEE REACHES (positive).** -/
theorem committee_quorum_reaches : reachedConsensusCore (.committee true) = true := rfl

/-- **NO-QUORUM COMMITTEE REFUSES (Nomad-law default, negative).** The SAME committee rung with the
quorum bit `false` (a zero-signer / defensively-constructed attestation) does NOT reach consensus. -/
theorem committee_noquorum_refuses : reachedConsensusCore (.committee false) = false := rfl

/-- **THE DISCRIMINATOR, ASSEMBLED.** Every rung on BOTH polarities: `proof` reaches, `rpc` refuses,
and the watchtower/committee rungs turn precisely on their resolution/quorum bit. The gate is not
`fun _ => true` and not `fun _ => false` — it discriminates on every axis. -/
theorem reached_consensus_discriminates :
    reachedConsensusCore .proof = true
    ∧ reachedConsensusCore .rpc = false
    ∧ reachedConsensusCore (.optimisticWatchtower true) = true
    ∧ reachedConsensusCore (.optimisticWatchtower false) = false
    ∧ reachedConsensusCore (.committee true) = true
    ∧ reachedConsensusCore (.committee false) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## §4 — The WIRE encoding (Rust ⇄ Lean) and its realizes-core proof.

The FFI wire is two ints `"tag payload"`: `tag ∈ {0,1,2,3}` selects the rung (proof / watchtower /
committee / rpc) and `payload` carries the resolution/quorum bit for tags `1`/`2` (ignored for
`0`/`3`). `encodeRung` is the Rust side's serialization; `reachedConsensusWire` is the decision the
export runs on the wire, proved to compute EXACTLY `reachedConsensusCore` over the encoding. -/

/-- **`encodeRung r`** — the `(tag, payload)` wire encoding of a rung (the Rust marshaller's shape).
`proof → (0,0)`, `optimisticWatchtower rv → (1, rv)`, `committee hq → (2, hq)`, `rpc → (3,0)`. -/
def encodeRung : TrustRung → Int × Int
  | .proof => (0, 0)
  | .optimisticWatchtower rv => (1, if rv then 1 else 0)
  | .committee hq => (2, if hq then 1 else 0)
  | .rpc => (3, 0)

/-- **`reachedConsensusWire tag payload`** — the fail-closed consensus verdict on the WIRE. `tag = 0`
(proof) reaches; `tag = 1`/`2` (watchtower/committee) reach iff the `payload` bit is nonzero; `tag =
3` (rpc) AND any UNKNOWN tag fail CLOSED (`false`). Unknown-tag-fails-closed is the extra Nomad tooth
at the wire boundary: a malformed/out-of-range tag can never mint. -/
def reachedConsensusWire (tag payload : Int) : Bool :=
  if tag == 0 then true
  else if tag == 1 then payload != 0
  else if tag == 2 then payload != 0
  else false

/-- **`reachedConsensusWire_realizes_core` (THE WIRE PATH REALIZES THE CORE).** For every rung, the
wire verdict on its `encodeRung` serialization equals `reachedConsensusCore` — so the Rust
marshal→export→parse round trip computes EXACTLY the verified core decision, no divergence at the
boundary. -/
theorem reachedConsensusWire_realizes_core (r : TrustRung) :
    reachedConsensusWire (encodeRung r).1 (encodeRung r).2 = reachedConsensusCore r := by
  cases r with
  | proof => rfl
  | optimisticWatchtower rv => cases rv <;> rfl
  | committee hq => cases hq <;> rfl
  | rpc => rfl

/-- **UNKNOWN TAG FAILS CLOSED (wire-boundary Nomad tooth).** Any tag outside `{0,1,2}` — including a
negative or out-of-range value — does NOT reach consensus. -/
theorem unknown_tag_refuses (tag payload : Int) (h0 : tag ≠ 0) (h1 : tag ≠ 1) (h2 : tag ≠ 2) :
    reachedConsensusWire tag payload = false := by
  unfold reachedConsensusWire
  simp only [beq_iff_eq]
  rw [if_neg h0, if_neg h1, if_neg h2]

/-! ## §5 — The `@[export]` FFI entry (Rust → Lean), running the verified consensus VERDICT. -/

/-- **FFI entry** (`bridge/src/interchain_adapter.rs` → Lean): space-separated ints `"tag payload"`
(`tag` selects the rung, `payload` is the watchtower/committee resolution bit) → `"1"` (reached
consensus) / `"0"` (refused). Runs the VERIFIED `reachedConsensusWire` as native code (the "Lean is
the runtime" shape shared with `dregg_holding_grant_weight` / `dregg_grain_r3_verify`). A malformed
wire (not exactly two ints) — and any unknown tag — fails CLOSED (`"0"`). -/
@[export dregg_interchain_reached_consensus]
def reachedConsensusFFI (input : String) : String :=
  match (input.splitOn " ").filterMap String.toInt? with
  | [tag, payload] => if reachedConsensusWire tag payload then "1" else "0"
  | _ => "0"

/-! It runs on the wire (`#guard`): `proof` (tag 0) reaches; a resolved-valid watchtower (`"1 1"`) and
a quorum committee (`"2 1"`) reach; a fraud watchtower (`"1 0"`), a no-quorum committee (`"2 0"`), the
`rpc` rung (`"3 0"`), an unknown tag (`"9 0"`), and a malformed wire all fail CLOSED (`"0"`). -/

#guard reachedConsensusFFI "0 0" = "1"
#guard reachedConsensusFFI "1 1" = "1"
#guard reachedConsensusFFI "1 0" = "0"
#guard reachedConsensusFFI "2 1" = "1"
#guard reachedConsensusFFI "2 0" = "0"
#guard reachedConsensusFFI "3 0" = "0"
#guard reachedConsensusFFI "9 0" = "0"
#guard reachedConsensusFFI "garbage" = "0"
#guard reachedConsensusFFI "" = "0"

/-! ## §6 — Axiom hygiene — every theorem kernel-clean (CI hard-gate). -/

#assert_axioms reachedConsensusCore_correct
#assert_axioms proof_reaches
#assert_axioms rpc_refuses
#assert_axioms watchtower_valid_reaches
#assert_axioms watchtower_fraud_refuses
#assert_axioms committee_quorum_reaches
#assert_axioms committee_noquorum_refuses
#assert_axioms reached_consensus_discriminates
#assert_axioms reachedConsensusWire_realizes_core
#assert_axioms unknown_tag_refuses

#print axioms reachedConsensusCore_correct
#print axioms reached_consensus_discriminates

end Dregg2.Bridge.InterchainAdapterDecision
