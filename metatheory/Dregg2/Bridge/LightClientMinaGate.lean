/-
# Dregg2.Bridge.LightClientMinaGate — the RUNTIME-CALLABLE Mina light-client VERIFY-LOGIC gate,
`@[export] dregg_mina_lc_verify`, PROVEN to be the same accept/reject decision the no-forgery
theorem is stated over (`LightClientMina.minaVerify`).

## Why this module exists

`bridge/src/mina_observer.rs` decides Mina finality in Rust: it reads `bestChain`, takes the MAXIMUM
`blockHeight` it was handed, subtracts the settlement's submitted height, and accepts when the
difference clears `confirmation_depth`. Nothing in that computation is verified, and — measured on
the shipped code — nothing in it is even a check:

  * the returned blocks are never checked to form a CHAIN (no `previousStateHash` linkage),
  * the block at `submitted_height` is never checked to be among them (with the shipped
    `best_chain_length: 16` and a mainnet `confirmation_depth: 290` it CANNOT be),
  * so a node returning ONE fabricated block with a large `blockHeight` finalizes every settlement
    instantly.

This gate is the twin-deletion boundary for that path, drawn exactly where the ETH / Tendermint gates
draw theirs: the Rust computes the mechanical projections and the CRYPTO RESULTS, and the ARCHIVE
renders the accept/reject.

## EXPORTED + PROVEN vs NAMED CARRIER

  * EXPORTED + PROVEN (this gate): the segment is non-empty; the settlement's submitted height is at
    or above the pinned weak-subjectivity anchor (without which "depth" is measured from outside the
    exhibited evidence — `LightClientMina.witnessedDepth_unbounded_without_anchor_bound` shows a
    one-block segment "witnessing" depth 1001); the Samasika confirmation depth is met by the
    WITNESSED depth. Pure `Nat`/`Bool`, decidable with no crypto, and exactly the rules-bug locus.
  * NAMED CARRIERS (supplied as their RESULTS): `lk` — the Poseidon parent-linkage fold result,
    DERIVED in `LightClientMinaHashFold` rather than trusted; `pk` — the per-block Pickles/Kimchi
    Wrap-proof result (the IPA/FRI arc; `MinaRealBlockGate` renders it on a real devnet block);
    `cn` — the state-row canonicality result, DERIVED from the Lean-authored width gate
    `LightClientMinaHashFold.minaRowWidthGates`.

`minaVerifyDecision_refines` is the load-bearing tie: fed an update's true projections, the exported
scalar decision is DEFINITIONALLY `minaVerify` (`rfl`), over which `mina_no_forgery` is proven.

## Scope (honest, current resolution)

This gate decides an ANCHORED SEGMENT. It does NOT decide fork choice, so nothing THIS export
computes distinguishes two `k`-deep proved segments under different anchors. Routing the observer
through it upgrades it from "trusts an RPC's arithmetic" to "checks an anchored, parent-linked,
proof-carrying segment"; it does not make dregg a Mina light client. What this gate CONTRIBUTES to
one is the `sg` bit `MinaForkChoiceGate.headAdvance` requires: fork choice presupposes both tips are
VALID, and `rollHead_fails_closed_without_the_segment` proves an unaccepted segment moves nothing.

⚑ UPDATED 2026-07-29. Samasika chain selection is no longer unformalized: `Bridge.MinaChainSelection`
implements `select` / `is_short_range` / the relative minimum window density against the daemon
(`proof_of_stake.ml:2951,2971,1221`), proves determinism, irreflexivity, asymmetry and
ties-only-on-equal-keys, PROVES that the rule is not transitive (two 3-cycles), and is differentialed
against openmina on 57 real-state vectors. ⚑ **UPDATED AGAIN 2026-07-30: it IS exported now.** The 07-29
note here read "deliberately NOT exported yet, and the reason is concrete: the long-range branch
needs `sub_window_densities`, and `subWindowDensities` is not a field of the public GraphQL
`ConsensusState`, so the deployed `mina_observer` physically cannot supply the input." That was a
DATA-SOURCE blocker and it is closed: `Bridge.MinaBinprot` decodes the binprot
`Protocol_state.Value` — where the array is an ordinary positional field — and
`Bridge.MinaForkChoiceGate` exports `dregg_mina_better_tip` / `dregg_mina_head_advance` over it.
`Bridge.MinaBinprotRealBlock` drives both on 1,544 bytes of a real devnet block pulled over
`coda/rpcs/0.0.1`. The scope limit on THIS gate is unchanged and real — it decides an anchored
segment, not fork choice — but it is no longer the tree's limit.
-/
import Dregg2.Bridge.LightClientMina

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Dregg2.Bridge.LightClientMinaGate

open Dregg2.Bridge.LightClientMina

/-! ## §1 — THE REFINEMENT TIE: the exported scalar decision IS `minaVerify`. -/

/-- `minaProjectedDecision` feeds `minaVerifyDecision` the eight true projections of an update under
a trusted state. -/
def minaProjectedDecision (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L) : Bool :=
  minaVerifyDecision u.blocks.length ts.anchorHeight u.submittedHeight
    (witnessedDepth ts u) ts.confirmationDepth
    (linkOk L ts u) (picklesOk L u) (canonOk L u)

/-- **THE TRANSLATION-VALIDATION THEOREM.** Fed an update's true projections, the exported scalar
decision is DEFINITIONALLY the proven gate `minaVerify L ts u`. So gating a deployed observer on
`dregg_mina_lc_verify` gates it, definitionally, on the decision `mina_no_forgery` is proven over. -/
theorem minaVerifyDecision_refines (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L) :
    minaProjectedDecision L ts u = minaVerify L ts u := rfl

/-- **THE PAYOFF: acceptance by the EXPORTED scalar decision entails Mina anchored validity.** -/
theorem minaVerifyDecision_no_forgery (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L)
    (h : minaProjectedDecision L ts u = true) : MinaValidAt L ts u :=
  mina_no_forgery L ts u ((minaVerifyDecision_refines L ts u) ▸ h)

/-- **AND THE DEPTH IS WITNESSED.** Acceptance by the exported decision entails the confirmation
depth is backed by that many exhibited, parent-linked, Pickles-proved blocks — the property the
deployed observer's height subtraction does not have. -/
theorem minaVerifyDecision_depth_witnessed (L : MinaLeaf) (ts : MinaTrustedState L)
    (u : MinaUpdate L) (h : minaProjectedDecision L ts u = true) :
    ts.confirmationDepth ≤ u.blocks.length :=
  (minaVerifyDecision_no_forgery L ts u h).depthWitnessed

/-! ## §2 — THE WIRE GATE + `@[export]`. Same `String → String` C-ABI shape as
`dregg_eth_lc_verify` / `dregg_tm_lc_verify`. Fail-closed on any malformed wire (`"ERR"` ⇒ the caller
treats it as REJECT). -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- **`decodeMinaWire`** — parse the `INPUT` grammar into the eight projections. Fail-closed (`none`)
on any deviation.

```
INPUT := "sl=" Nat ";ah=" Nat ";sh=" Nat ";wd=" Nat ";rd=" Nat ";lk=" BIT ";pk=" BIT ";cn=" BIT
BIT   := "0" | "1"
```
(`sl`=exhibited segment length, `ah`=pinned anchor height, `sh`=settlement submitted height,
`wd`=WITNESSED confirmation depth, `rd`=required Samasika depth, `lk`=Poseidon parent-linkage fold
result, `pk`=per-block Pickles Wrap-proof result, `cn`=state-row canonicality result.) -/
def decodeMinaWire (s : String) : Option (Nat × Nat × Nat × Nat × Nat × Bool × Bool × Bool) :=
  match s.splitOn ";" with
  | [p0, p1, p2, p3, p4, p5, p6, p7] => do
      let sl ← (parseField? "sl" p0).bind String.toNat?
      let ah ← (parseField? "ah" p1).bind String.toNat?
      let sh ← (parseField? "sh" p2).bind String.toNat?
      let wd ← (parseField? "wd" p3).bind String.toNat?
      let rd ← (parseField? "rd" p4).bind String.toNat?
      let lk ← (parseField? "lk" p5).bind parseBit?
      let pk ← (parseField? "pk" p6).bind parseBit?
      let cn ← (parseField? "cn" p7).bind parseBit?
      some (sl, ah, sh, wd, rd, lk, pk, cn)
  | _ => none

/-- **`minaLcVerifyGate`** — THE GATE. Decode the wire, run the VERIFIED `minaVerifyDecision`
(refined to `minaVerify`, over which `mina_no_forgery` is proven), and encode `"1"` (ACCEPT) / `"0"`
(REJECT). A malformed wire returns `"ERR"` (fail-closed: the caller treats it as REJECT). -/
def minaLcVerifyGate (s : String) : String :=
  match decodeMinaWire s with
  | some (sl, ah, sh, wd, rd, lk, pk, cn) =>
      if minaVerifyDecision sl ah sh wd rd lk pk cn then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_lc_verify]` — the C-ABI entry `dregg-lean-ffi` calls. The
Mina observer computes the Base58Check state-hash decode, the linkage fold and the Pickles results,
and the archive renders the verdict. -/
@[export dregg_mina_lc_verify]
def dregg_mina_lc_verify (s : String) : String := minaLcVerifyGate s

/-- **`minaLcVerifyGate_eq_decision`** — the gate string IS the verified decision, by construction. -/
theorem minaLcVerifyGate_eq_decision (s : String) (sl ah sh wd rd : Nat) (lk pk cn : Bool)
    (hd : decodeMinaWire s = some (sl, ah, sh, wd, rd, lk, pk, cn)) :
    minaLcVerifyGate s = (if minaVerifyDecision sl ah sh wd rd lk pk cn then "1" else "0") := by
  unfold minaLcVerifyGate
  rw [hd]

/-! ## §3 — NON-VACUITY: the DECISION DISCRIMINATES, kernel-clean.

The scalar decision is pure `Nat`/`Bool`, so `decide` reduces it in the kernel. (The STRING wire
layer uses well-founded recursion the kernel cannot reduce under `decide`; the `#guard`s below run it
in the interpreter at build time, and `minaLcVerifyGate_eq_decision` ties the string surface to THIS
decision without needing to reduce the parser.) -/

theorem mina_decision_discriminates :
    -- a genuine 290-deep anchored segment above anchor height 1000, settled at 1000
    minaVerifyDecision 290 1000 1000 290 290 true true true = true
    -- an EMPTY segment (the Nomad zero-evidence probe)
    ∧ minaVerifyDecision 0 1000 1000 290 290 true true true = false
    -- ⚑ the deployed observer's shape: a settlement claimed BELOW the pinned anchor, so the
    --   "depth" comes from outside the exhibited evidence. REFUSED here.
    ∧ minaVerifyDecision 1 1000 0 1001 290 true true true = false
    -- depth one short
    ∧ minaVerifyDecision 289 1000 1000 289 290 true true true = false
    -- the Poseidon linkage fold failed (an unlinked block set)
    ∧ minaVerifyDecision 290 1000 1000 290 290 false true true = false
    -- a Pickles Wrap proof failed
    ∧ minaVerifyDecision 290 1000 1000 290 290 true false true = false
    -- a state row is non-canonical (the `+p` anchor-substitution family)
    ∧ minaVerifyDecision 290 1000 1000 290 290 true true false = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **THE EXPORTED DECISION ACCEPTS THE MODEL GOOD UPDATE, end-to-end**, through the projection
pipeline (crypto results included) rather than at hand-picked scalars. -/
theorem mina_gate_accepts_model_good :
    minaProjectedDecision demoLeaf ts0 genuineUpdate = true :=
  (minaVerifyDecision_refines demoLeaf ts0 genuineUpdate).trans mina_gate_discriminates.1

-- The wire layer, in the interpreter: a genuine wire ACCEPTS, each tamper REJECTS, and a malformed
-- wire is `"ERR"` (fail-closed), including a truncated field list and a non-bit flag.
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=1" == "1"
#guard minaLcVerifyGate "sl=0;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=1" == "0"
#guard minaLcVerifyGate "sl=1;ah=1000;sh=0;wd=1001;rd=290;lk=1;pk=1;cn=1" == "0"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=289;rd=290;lk=1;pk=1;cn=1" == "0"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=0;pk=1;cn=1" == "0"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=0;cn=1" == "0"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=0" == "0"
#guard minaLcVerifyGate "garbage" == "ERR"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1" == "ERR"
#guard minaLcVerifyGate "sl=290;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=2" == "ERR"
#guard minaLcVerifyGate "sl=x;ah=1000;sh=1000;wd=290;rd=290;lk=1;pk=1;cn=1" == "ERR"

/-! ## §4 — axiom hygiene. -/

#assert_axioms minaVerifyDecision_refines
#assert_axioms minaVerifyDecision_no_forgery
#assert_axioms minaVerifyDecision_depth_witnessed
#assert_axioms minaLcVerifyGate_eq_decision
#assert_axioms mina_decision_discriminates
#assert_axioms mina_gate_accepts_model_good

#print axioms minaVerifyDecision_refines
#print axioms minaVerifyDecision_depth_witnessed

end Dregg2.Bridge.LightClientMinaGate
