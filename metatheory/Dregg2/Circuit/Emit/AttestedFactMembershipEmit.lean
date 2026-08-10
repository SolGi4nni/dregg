/-
# Dregg2.Circuit.Emit.AttestedFactMembershipEmit — the ATTESTED-FACT-MEMBERSHIP descriptor
(the third-party rung of the predicate stack)

## The hole this closes

`PredicatesArithmeticEmit.predicateArithDesc` (and its Gt/Lt/Le/Neq twins) prove, at
`pi = [threshold, fact_commitment]`:

> "∃ value, fact_hash, blinding: `fact_hash = hash_fact(pred_sym, [value, t1, t2])`,
>  `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`, and `value ≥ threshold`."

That is the value↔fact WELD (`factHashLookup` ∘ `factCommitLookup`), and it is real: whatever
commitment is presented, the compared value IS the one it covers. What the weld CANNOT say — by
construction, because `fact_hash` is a hidden column with nothing above it — is that the fact is a
fact of the PRESENTED TOKEN rather than one the prover invented. A prover picks any
`(pred_sym, value, t1, t2)` it likes, hashes it, blinds it, proves a TRUE statement about it, and
publishes the resulting `fact_commitment` as `pi[1]`.

The verifier's only defence was to DERIVE `pi[1]` itself from a fact it already trusts
(`sdk/src/verify.rs::verify_disclosure_presentation_against_state`). That closes the chain for an
ISSUER / AUDITOR / POLICY RE-EVALUATOR — someone who already holds the value. It does nothing for a
THIRD PARTY, who by hypothesis does not know the value and therefore has NO sound source for the
expected commitment. So `verify_disclosure_presentation` FAILS CLOSED on every predicate proof: an
honest verdict, but one that means a third party simply cannot verify a predicate proof at all.

`attestedFactMembershipDesc` supplies the missing rung. It proves, at
`pi = [fact_commitment, facts_root, state_root]`:

> "∃ fact_hash, blinding, path: `fact_hash ∈ tree(facts_root)` (a 4-ary Poseidon2 Merkle path), and
>  `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`."

`fact_commitment` is a PI of BOTH descriptors, and both compute it by the IDENTICAL
`chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]` absorb
(`PredicatesArithmeticEmit.factCommitLookup` @192). So the two proofs JOIN on that felt, and the
conjunction says exactly what a third party needs:

> "some fact of the token committed at `facts_root` has a value satisfying the threshold."

The commitment's provenance is now the ATTESTED `facts_root`, not the prover's say-so. `facts_root`
rides into the verifier as a public input of the presentation — the same rung `revealed_facts_commitment`
and `final_root` already ride (the named derivation leaf / recursion `ProofBind`), which is the point:
the predicate leg now reaches the SAME rung the revealed leg has always had, instead of dangling
below it.

## Why MEMBERSHIP and not RE-DERIVE (the brute-force leak, closed)

The re-derive path needs the `blinding` to travel with the proof as a DECOMMITMENT, so the verifier
can recompute `hash_4_to_1([fact_hash(trusted_value), state_root, blinding, 0])` and compare. A
proof-holder can then BRUTE-FORCE a low-entropy value: guess `v`, hash, compare (a driven falsifier
recovers `age = 37` in 130 tries). Membership needs no decommitment at all — `blinding` stays a
HIDDEN witness column, exactly as it is here (`BLINDING`, never PI-bound). Nothing to grind against.

This is also why the blinding must stay hidden for UNLINKABILITY: two showings of the SAME fact draw
two fresh blindings and publish two DIFFERENT `fact_commitment`s, each a genuine Poseidon2 image of
the SAME `fact_hash` proven under the SAME public `facts_root` — the property
`BlindedMembershipEmit.blindedMembershipDesc` delivers for issuers, delivered here for facts.

## Constraint map

| statement                                                        | IR-v2 constraint                       |
|------------------------------------------------------------------|----------------------------------------|
| `parent0 = hash_4_to_1(fact_hash, sib0a, sib0b, sib0c)`           | `.lookup ⟨poseidon2, …⟩` (`level0Lookup`) |
| `facts_root = hash_4_to_1(cur1, sib1a, sib1b, sib1c)`             | `.lookup ⟨poseidon2, …⟩` (`level1Lookup`) |
| `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])` | `.lookup ⟨poseidon2, …⟩` (`commitLookup`) |
| `cur1 = parent0` (level tie)                                      | `.base (.gate …)` + `.base (.boundary .last …)` |
| `facts_root` is the public PI                                     | `.base (.piBinding .first PARENT1 1)` |
| `fact_commitment` is the public PI (THE JOIN)                     | `.base (.piBinding .first FACT_COMMITMENT 0)` |
| `state_root` is the public PI                                     | `.base (.piBinding .first STATE_ROOT 2)` |

## What is NOT closed here (honest scope)

`facts_root`'s own binding to the issuer's derivation is the SAME named leaf the rest of the
presentation rides (fold-chain continuity + derivation-root binding = recursion `ProofBind`; issuer
Merkle membership = a STARK sub-proof) — see `PresentationEmit.lean` §"The NAMED gates". This
descriptor does not lift that leaf; it makes the predicate leg reach it. A verifier who does not
trust `facts_root` gains nothing from this descriptor, exactly as a verifier who does not trust
`revealed_facts_commitment` gains nothing from the revealed-facts check.

The leftmost-child convention of `BlindedMembershipEmit` applies here too: the member is always the
slot-0 input at each level (depth 2). Position-general / depth-general trees need the generalized
family, not a change here.

## Axiom hygiene

Definitional descriptor + a byte-pinned `#guard` on its wire string + genuinely-proven, non-vacuous
semantic lemmas. `#assert_axioms` ⊆ {}. NEW file; imports read-only.
-/
import Dregg2.Circuit.Emit.AirNormalForm
import Dregg2.Circuit.Emit.EffectLowerCertified

namespace Dregg2.Circuit.Emit.AttestedFactMembershipEmit

open Dregg2.Circuit (Assignment Constraint Expr)
open Dregg2.Exec.CircuitEmit (EmittedExpr emitExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg)
open Dregg2.Circuit.Emit.EffectLower (lowerAir lowerConstraint)
open Dregg2.Circuit.Emit.AirNormalForm
  (liftTuple wLinLoc gateBody gateBody_zero_iff normalFormOk)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId chipLookupTuple CHIP_RATE CHIP_OUT_LANES
   emitVmJson2)

set_option autoImplicit false

/-! ## §1 — the trace column layout (a single logical row, repeated to a power-of-two height).

The depth-2 4-ary Merkle path sits first — its LEAF column IS the hidden `fact_hash`, the same felt
`PredicatesArithmeticEmit.FACT_HASH` holds in the predicate proof. Past it sit the commitment
witness/PI columns and the three Poseidon2 chip lane blocks. -/

/-- Merkle level-0 path element = the hidden `fact_hash` (ALSO the commitment tooth's input 0).
This is the felt `PredicatesArithmeticEmit.factHashLookup` binds to `hash_fact(pred, [INPUT, …])`;
here it is bound to a member of `facts_root`. It is HIDDEN in both — publishing it would make two
showings of one fact linkable. -/
def FACT_HASH : Nat := 0
/-- Level-0 siblings (the three other children of the fact's parent; HIDDEN). -/
def SIB0A : Nat := 1
def SIB0B : Nat := 2
def SIB0C : Nat := 3
/-- Level-0 parent digest = `hash_4_to_1(fact_hash, sib0a, sib0b, sib0c)` (chip out0; HIDDEN). -/
def PARENT0 : Nat := 4
/-- Level-1 path element (the chained input; the continuity gate forces `CUR1 = PARENT0`; HIDDEN). -/
def CUR1 : Nat := 5
/-- Level-1 siblings (HIDDEN). -/
def SIB1A : Nat := 6
def SIB1B : Nat := 7
def SIB1C : Nat := 8
/-- Level-1 parent digest = the `facts_root` = `hash_4_to_1(cur1, sib1…)`; pinned to `ROOT_PI`. -/
def PARENT1 : Nat := 9
/-- **The blinding factor** — fresh per presentation; HIDDEN, and NEVER PI-bound.

Its hiddenness is what makes two showings of one fact unlinkable, and — the delta over the
re-derive path — it is what means NO DECOMMITMENT TRAVELS. The re-derive verifier needed this felt
published so it could recompute the commitment for a value it trusted; that publication is what a
brute-force attacker grinds against on a low-entropy value. A membership verifier needs no such
thing: the tooth below proves the commitment opens to a member of `facts_root` WITHOUT anyone
outside the prover ever learning `fact_hash` or `blinding`. -/
def BLINDING : Nat := 10
/-- **THE JOIN** — `fact_commitment = hash_4_to_1([fact_hash, state_root, blinding, 0])`; pinned to
`FACT_COMMITMENT_PI`. Byte-identical in construction to
`PredicatesArithmeticEmit.factCommitLookup`'s out0, so THIS felt and the predicate proof's `pi[1]`
are the same object: the conjunction of the two proofs is a statement about ONE fact. -/
def FACT_COMMITMENT : Nat := 11
/-- The token state root the fact commitment covers (the commitment tooth's input 1); PUBLIC, pinned
to `STATE_ROOT_PI`. It is public in the predicate path too (a shared parameter of the showing), and
publishing it here is what lets a third party check that both proofs speak of the same token state. -/
def STATE_ROOT : Nat := 12

/-- The seven exposed permutation lane columns 1..7 of each chip lookup (out0 is the digest above). -/
def LEVEL0_LANES : List Nat := [13, 14, 15, 16, 17, 18, 19]
def LEVEL1_LANES : List Nat := [20, 21, 22, 23, 24, 25, 26]
def COMMIT_LANES : List Nat := [27, 28, 29, 30, 31, 32, 33]

/-- Total main-trace width: 13 base columns + 7·3 chip lane blocks. -/
def ATTESTED_WIDTH : Nat := 34

/-- PI slot 0: the published `fact_commitment` — THE JOIN with the predicate proof's `pi[1]`. -/
def FACT_COMMITMENT_PI : Nat := 0
/-- PI slot 1: the public `facts_root` the presentation attests. -/
def ROOT_PI : Nat := 1
/-- PI slot 2: the public token `state_root`. -/
def STATE_ROOT_PI : Nat := 2
/-- Number of public inputs: `[fact_commitment, facts_root, state_root]`. -/
def PI_COUNT : Nat := 3

/-! ## §2 — the constraint list (Merkle chip chain · commitment chip lookup · pins · continuity). -/

/-- Level-0 `child → parent`: arity-4 `Poseidon2Chip` lookup absorbing
`[fact_hash, sib0a, sib0b, sib0c]`, binding out0 to `PARENT0`. -/
def level0Leg : LookupLeg :=
  { table := TableId.poseidon2
  , tuple := liftTuple (chipLookupTuple [.var FACT_HASH, .var SIB0A, .var SIB0B, .var SIB0C] PARENT0 LEVEL0_LANES) }
def level0Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, level0Leg.tuple.map emitExpr⟩

/-- Level-1 `child → parent`: arity-4 `Poseidon2Chip` lookup absorbing `[cur1, sib1a, sib1b, sib1c]`,
binding out0 to `PARENT1` (the `facts_root`). -/
def level1Leg : LookupLeg :=
  { table := TableId.poseidon2
  , tuple := liftTuple (chipLookupTuple [.var CUR1, .var SIB1A, .var SIB1B, .var SIB1C] PARENT1 LEVEL1_LANES) }
def level1Lookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, level1Leg.tuple.map emitExpr⟩

/-- **THE COMMITMENT TOOTH (the join)** — an arity-4 `TID_P2` Poseidon2 lookup absorbing
`[fact_hash, state_root, blinding, 0]`, binding out0 to `FACT_COMMITMENT`.

This tuple is CHARACTER-FOR-CHARACTER the shape of `PredicatesArithmeticEmit.factCommitLookup`
(`[.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]` → out0), differing only in which
column indices the descriptor happens to use. That is the whole design: the same absorb, computed
over a `fact_hash` that THIS descriptor proves is a member of `facts_root`, so a `fact_commitment`
accepted here and accepted there is a commitment to a REAL fact of the token whose value satisfies
the predicate. `fact_hash` and `blinding` never leave the witness. -/
def commitLeg : LookupLeg :=
  { table := TableId.poseidon2
  , tuple := liftTuple
      (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
        FACT_COMMITMENT COMMIT_LANES) }
def commitLookup : VmConstraint2 :=
  .lookup ⟨TableId.poseidon2, commitLeg.tuple.map emitExpr⟩

/-- The chain-continuity gate body: `CUR1 - PARENT0` (the next level's path input equals this
level's parent). -/
def contSrc : Constraint := ⟨.var CUR1, .var PARENT0⟩
/-- …and the body the COMPILER renders for it. -/
def contBody : EmittedExpr := gateBody contSrc
/-- The same residual on the WINDOW rail, canonically rendered. -/
def contWindow : Dregg2.Circuit.DescriptorIR2.WindowExpr := wLinLoc [(1, CUR1), (-1, PARENT0)] 0

/-- The chain-continuity Base gate — a `when_transition` constraint (vacuous on the LAST row). -/
def continuityGate : VmConstraint2 := lowerConstraint contSrc

/-- **The last-row continuity fix** (`adjLastOrderFix` shape): a `.boundary VmRow.last` counterpart
so the level-tie `CUR1 = PARENT0` holds on EVERY row. Without it the deployed single-logical-row
trace leaves `CUR1` free of `PARENT0`, and a non-member chains `fact_hash → junk` while
independently hashing the real root preimage — the `MerkleMembershipRung2` forgery class, which
would hand back exactly the prover-chosen commitment this descriptor exists to refuse. -/
def continuityLastFix : VmConstraint2 := .base (.boundary VmRow.last contBody)

/-- The root pin: `PARENT1` equals the public `facts_root` PI on the first row. -/
def rootPin : VmConstraint2 := .base (.piBinding VmRow.first PARENT1 ROOT_PI)

/-- The commitment pin: `FACT_COMMITMENT` equals the published `fact_commitment` PI — the felt the
predicate proof also pins. -/
def factCommitmentPin : VmConstraint2 :=
  .base (.piBinding VmRow.first FACT_COMMITMENT FACT_COMMITMENT_PI)

/-- The state-root pin: `STATE_ROOT` equals the public `state_root` PI. -/
def stateRootPin : VmConstraint2 := .base (.piBinding VmRow.first STATE_ROOT STATE_ROOT_PI)

/-- **`attestedFactMembershipDesc`** — the attested-fact-membership descriptor.
PIs `[fact_commitment, facts_root, state_root]`; hidden witnesses for `fact_hash`, `blinding`, and
the whole Merkle path. The chip table (`TID_P2`) is IMPLICITLY present (Presence-detected from the
lookups), so `tables` is empty exactly as `blindedMembershipDesc` leaves it. -/
def attestedFactMembershipAir : EffectAir :=
  { legs := [ .lookup level0Leg
            , .lookup level1Leg
            , .lookup commitLeg
            , .gate contSrc
            , .pin ⟨VmRow.first, PARENT1, ROOT_PI⟩
            , .pin ⟨VmRow.first, FACT_COMMITMENT, FACT_COMMITMENT_PI⟩
            , .pin ⟨VmRow.first, STATE_ROOT, STATE_ROOT_PI⟩
            , .window ⟨.last, contWindow⟩ ] }

/-- ⚑ **THE COMPILER ACCEPTS EVERY LEG** — `mainRailOk` is the decidable verdict that each leg has
a deployed main-rail image. Named rather than `#guard`ed: a `#guard` checks one closed instance,
leaves no term for the `TiedAir` below to be HANDED, and is invisible to `#assert_axioms`. -/
theorem attestedFactMembershipAir_mainRailOk : attestedFactMembershipAir.mainRailOk = true := by decide

/-- ⚑ **EVERY PUBLISHED COLUMN IS DERIVED BY ANOTHER LEG** — `EffectAir.pinsTied`, the verdict that
makes a DECORATIVE pin unrepresentable rather than merely detectable. -/
theorem attestedFactMembershipAir_pinsTied : attestedFactMembershipAir.pinsTied = true := by decide

/-- ⚑ **THE TIED SOURCE** — `attestedFactMembershipAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def attestedFactMembershipTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air  := attestedFactMembershipAir
  ok   := attestedFactMembershipAir_mainRailOk
  tied := attestedFactMembershipAir_pinsTied

def attestedFactMembershipDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-attested-fact-membership::v1" ATTESTED_WIDTH PI_COUNT [] attestedFactMembershipTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem attestedFactMembershipDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines attestedFactMembershipDesc [] attestedFactMembershipAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-attested-fact-membership::v1" ATTESTED_WIDTH PI_COUNT [] attestedFactMembershipTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem attestedFactMembershipDesc_eq_lowerAir :
    attestedFactMembershipDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-attested-fact-membership::v1" ATTESTED_WIDTH PI_COUNT [] attestedFactMembershipAir := rfl

/-- ⚑ The compiler's output IS that constraint list, by `rfl`. -/
theorem attestedFactMembershipDesc_constraints :
    attestedFactMembershipDesc.constraints
      = [level0Lookup, level1Lookup, commitLookup, continuityGate, rootPin,
         factCommitmentPin, stateRootPin, continuityLastFix] := rfl

-- ⚑ THE CORPUS INVARIANT, DECIDED on this descriptor: every arithmetic body is canonical.
#guard normalFormOk attestedFactMembershipDesc == true

/-! ## §3 — the byte-pinned wire golden (the Rust decoder ingests THIS string).

Written verbatim to `circuit/descriptors/by-name/attested-fact-membership.json`;
`parse_vm_descriptor2` ingests it. A drift on either side breaks THIS `#guard`. -/

#guard emitVmJson2 attestedFactMembershipDesc ==
  "{\"name\":\"dregg-attested-fact-membership::v1\",\"ir\":2,\"trace_width\":34,\"public_input_count\":3,\"challenges\":0,\"tables\":[],\"constraints\":[{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":1},{\"t\":\"var\",\"v\":2},{\"t\":\"var\",\"v\":3},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":4},{\"t\":\"var\",\"v\":13},{\"t\":\"var\",\"v\":14},{\"t\":\"var\",\"v\":15},{\"t\":\"var\",\"v\":16},{\"t\":\"var\",\"v\":17},{\"t\":\"var\",\"v\":18},{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":5},{\"t\":\"var\",\"v\":6},{\"t\":\"var\",\"v\":7},{\"t\":\"var\",\"v\":8},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":9},{\"t\":\"var\",\"v\":20},{\"t\":\"var\",\"v\":21},{\"t\":\"var\",\"v\":22},{\"t\":\"var\",\"v\":23},{\"t\":\"var\",\"v\":24},{\"t\":\"var\",\"v\":25},{\"t\":\"var\",\"v\":26}]},{\"t\":\"lookup\",\"table\":1,\"tuple\":[{\"t\":\"const\",\"v\":4},{\"t\":\"var\",\"v\":0},{\"t\":\"var\",\"v\":12},{\"t\":\"var\",\"v\":10},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"const\",\"v\":0},{\"t\":\"var\",\"v\":11},{\"t\":\"var\",\"v\":27},{\"t\":\"var\",\"v\":28},{\"t\":\"var\",\"v\":29},{\"t\":\"var\",\"v\":30},{\"t\":\"var\",\"v\":31},{\"t\":\"var\",\"v\":32},{\"t\":\"var\",\"v\":33}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":9,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":11,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":12,\"pi_index\":2},{\"t\":\"boundary\",\"row\":\"last\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":4}}}}],\"hash_sites\":[],\"ranges\":[]}"

/-! ## §4 — genuinely-proven, non-vacuous semantic lemmas + shape pins + axiom hygiene. -/

/-- The continuity gate body is zero EXACTLY when the levels chain (`CUR1 = PARENT0`). -/
theorem continuity_body_zero_iff (a : Assignment) :
    contBody.eval a = 0 ↔ a CUR1 = a PARENT0 := by
  simp only [contBody]; rw [gateBody_zero_iff]; simp [contSrc, Expr.eval]

/-- The commitment chip tuple has the canonical chip width `1 + CHIP_RATE + CHIP_OUT_LANES` (arity
tag, the rate-padded 4-input preimage, out0 = the fact commitment, and the 7 lanes). -/
theorem commitLookup_tuple_width :
    (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
      FACT_COMMITMENT COMMIT_LANES).length = 1 + CHIP_RATE + CHIP_OUT_LANES := by
  simp [chipLookupTuple, Dregg2.Circuit.DescriptorIR2.padToE, CHIP_RATE, CHIP_OUT_LANES,
        COMMIT_LANES]

-- Non-vacuity witnesses: the gate ACCEPTS a chained assignment and REJECTS an unchained one.
#guard decide (contBody.eval (fun i => if i = CUR1 ∨ i = PARENT0 then 7 else 0) = 0)
#guard decide (¬ (contBody.eval (fun i => if i = CUR1 then 7 else 0) = 0))

-- Shape pins.
#guard attestedFactMembershipDesc.traceWidth == ATTESTED_WIDTH
#guard attestedFactMembershipDesc.piCount == PI_COUNT
#guard attestedFactMembershipDesc.constraints.length == 8
#guard attestedFactMembershipDesc.tables.length == 0
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT COMMIT_LANES).length
         == 1 + CHIP_RATE + CHIP_OUT_LANES
-- The commitment tooth is an ARITY-4 absorb — the same arity tag `PredicatesArithmeticEmit`'s
-- `factCommitLookup` carries. A drift here silently unjoins the two proofs.
#guard (chipLookupTuple [.var FACT_HASH, .var STATE_ROOT, .var BLINDING, .const 0]
                        FACT_COMMITMENT COMMIT_LANES).head? == some (.const 4)
-- `BLINDING` and `FACT_HASH` are real columns of the trace, and NEITHER is PI-bound: no
-- decommitment travels, and the fact itself never leaves the witness.
#guard BLINDING < ATTESTED_WIDTH
#guard FACT_HASH < ATTESTED_WIDTH

#assert_axioms continuity_body_zero_iff
#assert_axioms commitLookup_tuple_width

end Dregg2.Circuit.Emit.AttestedFactMembershipEmit
