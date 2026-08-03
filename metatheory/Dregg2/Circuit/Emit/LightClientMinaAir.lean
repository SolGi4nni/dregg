/-
# Dregg2.Circuit.Emit.LightClientMinaAir — the MINA light-client VERIFY-DECISION, COMPILED to an AIR,
and the object a dregg state transition can be REFUSED by.

## What this file IS, and the gap it closes

Mina was the ONE peer chain with a `@[export]`ed, PROVEN verify decision
(`Dregg2.Bridge.LightClientMinaGate.minaLcVerifyGate` / `dregg_mina_lc_verify`, tied to
`LightClientMina.minaVerify` by `minaVerifyDecision_refines` and hence to `mina_no_forgery`) and NO
emitted AIR. Eth, Tendermint, Solana and Midnight each have one
(`LightClient{Eth,Tendermint,Solana,Midnight}Air.lean`, routed through `EmitByName.lean` and
`circuit/src/descriptor_by_name.rs`); Mina had none — measured 2026-08-02, `grep -l LightClient.*Air`
over `Dregg2/Circuit/Emit/` returns four files and Mina is not among them. So the whole Mina→dregg
arc (binprot decode → challenges → `ft_eval0` → Samasika fork choice → the anchored candidate set)
terminated in a Lean `Bool` **rendered by running Lean on the node's own machine**. Nothing portable,
and — the sharper half — nothing a dregg TURN could be refused by.

This file is the missing rung, and it is deliberately more than the fifth copy of the peer-wrap
pattern: the descriptor's public inputs ARE the dregg state write, so a state transition that
records `(mina_state_hash, blockchain_length, anchor)` and a verification of that head are ONE
object, not a record beside a claim.

## ⚑ HOUSE LAW #1, in its endpoint form: this AIR is COMPILED, not hand-written

`minaLcVerifyDesc` is `EffectLower.lowerAir` applied to `minaHeadAir` (§3), an `EffectAir` source in
the widened vocabulary (`Circuit/EffectAirIR.lean`). There is **no hand-written `VmConstraint2` list
in this file** — eight `.gate` legs, three `.lookup` legs against a declared range table, twenty
`.pin` legs, and the `VmConstraint2`s are the compiler's business. It is the second deployed
descriptor in the tree authored this way (`DfaRoutingTableEmit.tableRoutingDesc` was the first,
2026-08-01) and the first authored that way from scratch rather than by fusing a hand-written twin.

The vocabulary was ADEQUATE: `EffectAir.mainRailOk` is `true` by `rfl` (`minaHeadAir_mainRailOk`), so
no leg lowered to `EffectLower.refuseConstraints`. Nothing had to be added to `EffectAirIR` and
nothing had to be hand-written around it. That is the finding, stated plainly as §3 asks.

## ⚑ THE TOOTH: `blockchain_length` and the witnessed depth are DERIVED, not witnessed

The wound this AIR exists to close is the one the `mina-tip` lane measured: a peer's reply was read
at 1,544 of 61,193 bytes, `tip.proof` was dropped, and *"what survived was `blockchain_length`, the
one field a liar sets for free."* An AIR that PUBLISHES `blockchain_length` as a free witness column
reproduces that defect in circuit form. So it is not a witness here:

    G1   BLOCK_LEN  =  ANCHOR_H + SEG_LEN            -- the published height IS anchor + evidence
    G2   WIT_DEPTH + SUBMIT_H  =  BLOCK_LEN          -- the depth IS measured to the derived tip

A prover that exhibits `n` blocks above the pinned anchor can publish exactly `anchorH + n` and
nothing else. Claiming a taller chain requires exhibiting the blocks, and every exhibited block is
under the `LINK_OK` / `PICKLES_OK` / `CANON_OK` carriers.

Symmetrically, `LightClientMina.witnessedDepth_unbounded_without_anchor_bound` exhibits the deployed
observer's arithmetic (`tip_height.saturating_sub(submitted_height)`) witnessing depth **1001 from a
one-block segment** when the anchor sits at 1000 and the submitted height at 0. That row is REFUSED
here by an explicit witness (`observer_arithmetic_refused`, §7): `ANCH_SLACK = 0 − 1000 = −1000` is
outside `[0, 2^32)` and the range lookup has no satisfying table row.

## The three slack teeth (the ≤ relations, wrap-free)

Field elements have no order, so each `≤` rides as a non-negative SLACK pinned into `[0, 2^32)` by a
lookup against the declared range table — the same shape `LightClientEthAir`'s quorum tooth uses.

    G3  SEG_SLACK   + 1         = SEG_LEN     +  range(SEG_SLACK)     ⟹  0 < segLen
    G4  ANCH_SLACK  + ANCHOR_H  = SUBMIT_H    +  range(ANCH_SLACK)    ⟹  anchorH ≤ submittedH
    G5  DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH   +  range(DEPTH_SLACK)   ⟹  reqDepth ≤ witDepth

32 bits is the honest width: Mina's `blockchain_length` is a `u32` on the wire, so every height,
depth and slack this AIR reads is representable, and no legal value is excluded by the interval.

## NAMED verified CARRIERS (and what they are NOT)

`LINK_OK` / `PICKLES_OK` / `CANON_OK` are witnessed boolean columns forced `= 1`, and they are the
SAME three results `LightClientMinaGate`'s wire gate already takes as `lk` / `pk` / `cn`. They are
NOT re-derived in-AIR here:

  * `LINK_OK`    — the Poseidon parent-linkage fold over the exhibited segment. DERIVED (not
    trusted) one module over, in `Circuit/Emit/LightClientMinaHashFold.lean`.
  * `PICKLES_OK` — the per-block Pickles/Kimchi Wrap-proof result. The IPA/FRI arc;
    `Circuit/Emit/MinaRealBlockGate.lean` renders it on a real devnet block.
  * `CANON_OK`   — the state-row canonicality result, derived from the Lean-authored width gate
    `LightClientMinaHashFold.minaRowWidthGates`.

⚠ So a STARK over this descriptor proves the ANCHORING / DEPTH / HEIGHT-DERIVATION logic given those
three results — precisely the guarantee `minaVerifyDecision` gives, now portable and now bindable to
a state write. Folding the three carriers into their own bound sub-proofs is the next rung; the PI
anchors below are the hook it attaches to. This is stated as a residual, not as a caveat that ends
the work.

## Public inputs — ⚑ these ARE the dregg state write

    PI[0..8]   ANCHOR_STATE[i]  — the OPERATOR-PINNED weak-subjectivity anchor state hash, as nine
                                  radix-2^31 MSB-first limbs (⌈255/31⌉ = 9; a Pasta `Fp` is ~255
                                  bits). The trust root the whole acceptance is relative to.
    PI[9..17]  TIP_STATE[i]     — the VERIFIED head's Mina protocol-state hash, nine limbs.
    PI[18]     BLOCK_LEN        — the verified head's `blockchain_length` (DERIVED by G1).
    PI[19]     REQ_DEPTH        — the Samasika confirmation depth `k` the acceptance met (290 on
                                  mainnet). Published so a verifier sees WHICH depth policy was met
                                  rather than trusting the prover picked a real one.

Nine limbs, not one felt, and for the reason the repo already paid for once: a single BabyBear anchor
felt binds a **31-bit projection** of a 255-bit hash, so two distinct Mina heads agreeing in 31 bits
would both verify (`LightClientEthAir`'s felt-width close, same disease). `31 * 9 = 279 ≥ 255`.

⚠ NAMED and NOT closed here: the limbs are PI-bound but not arithmetically tied to the `LINK_OK`
fold's terminal digest inside this AIR. That tie is `LightClientMinaHashFold`'s object and the
`proofBind` recursion seam; until it lands, `TIP_STATE` is bound to the trace and to the state write
but its equality with the fold's output is enforced by the witness generator, not by a gate here.
Say it that way, always.

## Both polarities, on the EMITTED object (§6, §7)

* ACCEPT — `minaLcAir_complete`: an honest row over a genuinely accepted update satisfies
  `airAccepts`; and `minaLcAir_no_forgery` carries acceptance all the way to `MinaValidAt`.
* REFUSE — four named refusing witnesses, each a CONCRETE assignment, each `¬ airAccepts`:
  `losing_fork_refused` (a shallower fork), `bent_proof_word_refused` (`PICKLES_OK = 0`),
  `forged_height_refused` (the free-`blockchain_length` liar), `observer_arithmetic_refused` (the
  deployed observer's unanchored subtraction). A refusal that some assignment satisfies is
  decoration; these are exhibited, not asserted.

## Scope — do NOT overclaim

⚠ NOT "machine-checked Mina validity" and NOT "Mina-valid". `PICKLES_OK` rides the undischarged
IPA/FRI floor via `MinaLeaf.picklesSound`, and a STARK over this descriptor inherits the
undischarged FRI/STARK floor on the dregg side. What is proved is a refinement over the EMITTED
object: `airAccepts` ⟹ `minaVerifyDecision` ⟹ (`mina_no_forgery`) ⟹ `MinaValidAt`.

⚠ And the scope limit `LightClientMinaGate` already names is UNCHANGED: this decides an ANCHORED
SEGMENT, not fork choice. Two `k`-deep proved segments under DIFFERENT anchors are indistinguishable
to this AIR; what distinguishes them is `MinaForkChoiceGate` / `dregg_mina_better_tip`, and the
anchor this AIR pins is `PI[0..8]` — an operator's or a serving peer's, and the descriptor cannot
tell you which. A verifier reads `ANCHOR_STATE` and decides whether it trusts it.

## Axiom hygiene

Compiled descriptor + non-vacuous per-gate `iff` lemmas + the load-bearing `minaLcAir_sound` /
`minaLcAir_no_forgery` refinement + four exhibited refusals. Every asserted fact is a NAMED THEOREM
(`metatheory/docs/GUARD-DISCIPLINE.md`); this file contains no `#guard`. NEW file; imports
read-only.
-/
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Bridge.LightClientMinaGate

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientMinaAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg)
open Dregg2.Bridge.LightClientMina
open Dregg2.Bridge.LightClientMinaGate

/-! ## §1 — the trace column layout (one logical row) and the PI slots.

Columns 0..10 are the verify-logic projections + the three slack witnesses + the three named
carriers; column 11 is the DERIVED published height; columns 12..29 are the two nine-limb state-hash
anchors. -/

/-- `SEG_LEN` — the number of blocks EXHIBITED above the pinned anchor. Witness. -/
def SEG_LEN : Nat := 0
/-- `ANCHOR_H` — the pinned weak-subjectivity anchor's blockchain length. Witness. -/
def ANCHOR_H : Nat := 1
/-- `SUBMIT_H` — the height the settlement being finalized was submitted at. Witness. -/
def SUBMIT_H : Nat := 2
/-- `WIT_DEPTH` — the WITNESSED confirmation depth. ⚑ DERIVED by G2 from `BLOCK_LEN − SUBMIT_H`,
never a free witness: a free depth column is the deployed observer's defect in circuit form. -/
def WIT_DEPTH : Nat := 3
/-- `REQ_DEPTH` — the Samasika confirmation depth `k` required (290 on mainnet). PI-bound, so the
verifier sees WHICH depth policy the acceptance met. -/
def REQ_DEPTH : Nat := 4
/-- `SEG_SLACK = SEG_LEN − 1`; the range tooth forces it into `[0, 2^32)`, i.e. `0 < SEG_LEN`. -/
def SEG_SLACK : Nat := 5
/-- `ANCH_SLACK = SUBMIT_H − ANCHOR_H`; ranged ⟹ `ANCHOR_H ≤ SUBMIT_H`. ⚑ This is the exact
conjunct the deployed observer does not have. -/
def ANCH_SLACK : Nat := 6
/-- `DEPTH_SLACK = WIT_DEPTH − REQ_DEPTH`; ranged ⟹ `REQ_DEPTH ≤ WIT_DEPTH`. -/
def DEPTH_SLACK : Nat := 7
/-- **CARRIER** — the Poseidon parent-linkage fold RESULT over the exhibited segment; forced `= 1`.
Derived (not trusted) in `LightClientMinaHashFold`. Witness. -/
def LINK_OK : Nat := 8
/-- **CARRIER** — the per-block Pickles/Kimchi Wrap-proof RESULT; forced `= 1`. Rides the
undischarged IPA/FRI floor. Witness. -/
def PICKLES_OK : Nat := 9
/-- **CARRIER** — the state-row canonicality RESULT; forced `= 1`. Derived from the Lean-authored
width gate `LightClientMinaHashFold.minaRowWidthGates`. Witness. -/
def CANON_OK : Nat := 10

/-- **PUBLIC / STATE-WRITE** — the verified head's `blockchain_length`. ⚑ DERIVED by G1 from
`ANCHOR_H + SEG_LEN`, so the one field a liar sets for free is not settable at all. PI-bound. -/
def BLOCK_LEN : Nat := 11

/-- The number of ~31-bit limbs a Pasta `Fp` state hash is exposed as: `⌈255/31⌉ = 9`. A SINGLE
BabyBear felt would bind a 31-bit projection, and two heads agreeing in 31 bits would both verify. -/
def STATE_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the operator-pinned weak-subjectivity anchor state hash, radix
`2^31`, MOST-SIGNIFICANT-limb-first. Columns 12..20, PI slots 0..8. -/
def ANCHOR_STATE (i : Nat) : Nat := 12 + i

/-- **PUBLIC / STATE-WRITE (limb `i`)** — the VERIFIED head's Mina protocol-state hash, radix
`2^31`, MSB-first. Columns 21..29, PI slots 9..17. -/
def TIP_STATE (i : Nat) : Nat := 12 + STATE_LIMBS + i

/-- Total main-trace width: 11 logic/carrier columns + the derived height + two nine-limb anchors. -/
def MINA_LC_WIDTH : Nat := 12 + 2 * STATE_LIMBS

/-- PI slot of anchor-state limb `i` (slots 0..8). -/
def PI_ANCHOR_STATE (i : Nat) : Nat := i
/-- PI slot of tip-state limb `i` (slots 9..17). -/
def PI_TIP_STATE (i : Nat) : Nat := STATE_LIMBS + i
/-- PI slot 18: the verified head's `blockchain_length`. -/
def PI_BLOCK_LEN : Nat := 2 * STATE_LIMBS
/-- PI slot 19: the Samasika depth policy met. -/
def PI_REQ_DEPTH : Nat := 2 * STATE_LIMBS + 1
/-- Number of public inputs: two nine-limb hashes + the height + the depth policy. -/
def MINA_PI_COUNT : Nat := 2 * STATE_LIMBS + 2

/-- The slack range width. Mina's `blockchain_length` is a `u32` on the wire, so 32 bits admits
every legal height, depth and slack and excludes no honest value. -/
def MINA_RANGE_BITS : Nat := 32

/-! ## §2 — the SOURCE constraints, in the framework's own gate algebra (`Circuit.Expr`).

These are `Constraint`s (`lhs = rhs`), NOT `VmConstraint2`s. The compiler normalizes each through
`AirBuilder.Head` and emits the residual `lhs − rhs`; nothing in this file writes a gate body. -/

/-- **G1 — the published height is DERIVED**: `BLOCK_LEN = ANCHOR_H + SEG_LEN`. -/
def blockLenC : Constraint :=
  ⟨.var BLOCK_LEN, .add (.var ANCHOR_H) (.var SEG_LEN)⟩

/-- **G2 — the witnessed depth is DERIVED**: `WIT_DEPTH + SUBMIT_H = BLOCK_LEN`. -/
def witDepthC : Constraint :=
  ⟨.add (.var WIT_DEPTH) (.var SUBMIT_H), .var BLOCK_LEN⟩

/-- **G3 — the segment slack identity**: `SEG_SLACK + 1 = SEG_LEN`. Ranged ⟹ `0 < SEG_LEN`. -/
def segSlackC : Constraint :=
  ⟨.add (.var SEG_SLACK) (.const 1), .var SEG_LEN⟩

/-- **G4 — the anchor slack identity**: `ANCH_SLACK + ANCHOR_H = SUBMIT_H`. Ranged ⟹
`ANCHOR_H ≤ SUBMIT_H`, the conjunct the deployed observer lacks. -/
def anchSlackC : Constraint :=
  ⟨.add (.var ANCH_SLACK) (.var ANCHOR_H), .var SUBMIT_H⟩

/-- **G5 — the depth slack identity**: `DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH`. Ranged ⟹
`REQ_DEPTH ≤ WIT_DEPTH`. -/
def depthSlackC : Constraint :=
  ⟨.add (.var DEPTH_SLACK) (.var REQ_DEPTH), .var WIT_DEPTH⟩

/-- **G6 — the linkage carrier**: `LINK_OK = 1`. -/
def linkC : Constraint := ⟨.var LINK_OK, .const 1⟩
/-- **G7 — the Pickles carrier**: `PICKLES_OK = 1`. -/
def picklesC : Constraint := ⟨.var PICKLES_OK, .const 1⟩
/-- **G8 — the canonicality carrier**: `CANON_OK = 1`. -/
def canonC : Constraint := ⟨.var CANON_OK, .const 1⟩

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT.

Eight `.gate` legs, three `.lookup` legs against the declared range table, and twenty `.pin` legs,
in emission order. `EffectAir`'s vocabulary was ADEQUATE — nothing here needed a word
`Circuit/EffectAirIR.lean` did not already have, and `minaHeadAir_mainRailOk` decides that on the
emitted predicate rather than by eye. -/

/-- The declared range table carrying the three slack teeth. -/
def minaRangeTable : TableDef := rangeTableDef MINA_RANGE_BITS

/-- A range query on one wire, in the source vocabulary. -/
def rangeLeg (col : Nat) : AirLeg :=
  .lookup { table := TableId.range, tuple := [Expr.var col] }

/-- The nine anchor-state PI pins (cols 12..20 → PI 0..8), written out so the emission pin below
reduces with no fold. -/
def anchorStatePins : List AirLeg :=
  [ .pin ⟨VmRow.first, ANCHOR_STATE 0, PI_ANCHOR_STATE 0⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 1, PI_ANCHOR_STATE 1⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 2, PI_ANCHOR_STATE 2⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 3, PI_ANCHOR_STATE 3⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 4, PI_ANCHOR_STATE 4⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 5, PI_ANCHOR_STATE 5⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 6, PI_ANCHOR_STATE 6⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 7, PI_ANCHOR_STATE 7⟩
  , .pin ⟨VmRow.first, ANCHOR_STATE 8, PI_ANCHOR_STATE 8⟩ ]

/-- The nine tip-state PI pins (cols 21..29 → PI 9..17) — ⚑ the dregg state write's hash half. -/
def tipStatePins : List AirLeg :=
  [ .pin ⟨VmRow.first, TIP_STATE 0, PI_TIP_STATE 0⟩
  , .pin ⟨VmRow.first, TIP_STATE 1, PI_TIP_STATE 1⟩
  , .pin ⟨VmRow.first, TIP_STATE 2, PI_TIP_STATE 2⟩
  , .pin ⟨VmRow.first, TIP_STATE 3, PI_TIP_STATE 3⟩
  , .pin ⟨VmRow.first, TIP_STATE 4, PI_TIP_STATE 4⟩
  , .pin ⟨VmRow.first, TIP_STATE 5, PI_TIP_STATE 5⟩
  , .pin ⟨VmRow.first, TIP_STATE 6, PI_TIP_STATE 6⟩
  , .pin ⟨VmRow.first, TIP_STATE 7, PI_TIP_STATE 7⟩
  , .pin ⟨VmRow.first, TIP_STATE 8, PI_TIP_STATE 8⟩ ]

/-- ⚑ **THE SOURCE.** The Mina anchored-head verify AIR in the `EffectAir` vocabulary. Nothing below
is in the deployed IR's language: `AirLeg`, `LookupLeg` and `PiPinLeg` are the source, and the
`VmConstraint2`s are what `EffectLower.lowerAir` produces. -/
def minaHeadAir : EffectAir :=
  { tables := [minaRangeTable]
  , legs   :=
      [ .gate blockLenC
      , .gate witDepthC
      , .gate segSlackC
      , rangeLeg SEG_SLACK
      , .gate anchSlackC
      , rangeLeg ANCH_SLACK
      , .gate depthSlackC
      , rangeLeg DEPTH_SLACK
      , .gate linkC
      , .gate picklesC
      , .gate canonC ]
      ++ anchorStatePins ++ tipStatePins
      ++ [ .pin ⟨VmRow.first, BLOCK_LEN, PI_BLOCK_LEN⟩
         , .pin ⟨VmRow.first, REQ_DEPTH, PI_REQ_DEPTH⟩ ] }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE.** Every leg is main-rail expressible, decided on the emitted
predicate — so no leg lowered to `EffectLower.refuseConstraints` and nothing was hand-written around
the compiler. This is the §3 finding stated as a theorem rather than a sentence. -/
theorem minaHeadAir_mainRailOk : minaHeadAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem minaHeadAir_pinsFit : minaHeadAir.pinsFit MINA_PI_COUNT = true := by rfl

/-- The source carries 31 legs: 8 gates + 3 range lookups + 20 PI pins. -/
theorem minaHeadAir_leg_count : minaHeadAir.legs.length = 31 := by rfl

/-- **`minaLcVerifyDesc` — COMPILER OUTPUT.** The Mina anchored-head light-client verify decision as
an IR-v2 AIR. Not modelled beside a hand-written twin; there is no twin.

⚠ `lowerAir`, not `lowerEffect`: this descriptor is not a full-state effect and has no digest wires,
so the framework's `PIBindsDigests` surface would emit a descriptor nobody deployed. The two entry
points share the normalizer, the leg lowerings and the emission order and differ ONLY in that
surface. -/
def minaLcVerifyDesc : EffectVmDescriptor2 :=
  Dregg2.Circuit.Emit.EffectLower.lowerAir
    "dregg-mina-lightclient-verify::v1" MINA_LC_WIDTH MINA_PI_COUNT [] minaHeadAir

/-! ### §3a — the emission pins: what the compiler produced, against a hand-written expectation.

`rfl`, and therefore GATES rather than decoration — a change to the leg lowerings, the leg ORDER or
`assemble` moves one of these and it goes red here, one module above the compiler where the
descriptor is actually deployed from. The gate BODIES are deliberately not transcribed: their normal
form is the normalizer's business, and §4/§5 pin their MEANING through
`EffectLower.lowerConstraint_holdsAt_iff`, which is stronger than a transcribed tree. -/

theorem minaLcVerifyDesc_name : minaLcVerifyDesc.name = "dregg-mina-lightclient-verify::v1" := rfl
theorem minaLcVerifyDesc_width : minaLcVerifyDesc.traceWidth = MINA_LC_WIDTH := rfl
theorem minaLcVerifyDesc_piCount : minaLcVerifyDesc.piCount = MINA_PI_COUNT := rfl
theorem minaLcVerifyDesc_tables : minaLcVerifyDesc.tables = [minaRangeTable] := rfl
theorem minaLcVerifyDesc_hashSites : minaLcVerifyDesc.hashSites = [] := rfl
theorem minaLcVerifyDesc_ranges : minaLcVerifyDesc.ranges = [] := rfl

/-- The compiler emitted exactly one constraint per source leg — nothing vanished and nothing was
invented. (`EffectLower.lowerLeg_ne_nil` is the general statement; this is it at this descriptor.) -/
theorem minaLcVerifyDesc_constraint_count : minaLcVerifyDesc.constraints.length = 31 := rfl

/-- ⚑ **THE THREE SLACK LOOKUPS, AT THEIR EMITTED POSITIONS.** `rfl` on a slice of the compiler's
output: constraint 3 is the segment tooth, 5 the anchor tooth, 7 the depth tooth. A leg that lowered
to `EffectLower.refuseConstraints` would emit a `.boundary` pair here instead and this goes red. -/
theorem minaLcVerifyDesc_slack_lookups :
    (minaLcVerifyDesc.constraints.drop 3).take 1
        = [.lookup ⟨TableId.range, [.var SEG_SLACK]⟩]
      ∧ (minaLcVerifyDesc.constraints.drop 5).take 1
        = [.lookup ⟨TableId.range, [.var ANCH_SLACK]⟩]
      ∧ (minaLcVerifyDesc.constraints.drop 7).take 1
        = [.lookup ⟨TableId.range, [.var DEPTH_SLACK]⟩] :=
  ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE TWENTY PI PINS, AS THE COMPILER EMITTED THEM** — the addressing layer AND the dregg state
write, in one `rfl`. Nine pinned-anchor limbs, nine verified-tip limbs, the DERIVED height, the depth
policy met. A reordering, a dropped pin or a re-indexed slot moves this. -/
theorem minaLcVerifyDesc_pins :
    minaLcVerifyDesc.constraints.drop 11 =
      [ .base (.piBinding VmRow.first (ANCHOR_STATE 0) (PI_ANCHOR_STATE 0))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 1) (PI_ANCHOR_STATE 1))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 2) (PI_ANCHOR_STATE 2))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 3) (PI_ANCHOR_STATE 3))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 4) (PI_ANCHOR_STATE 4))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 5) (PI_ANCHOR_STATE 5))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 6) (PI_ANCHOR_STATE 6))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 7) (PI_ANCHOR_STATE 7))
      , .base (.piBinding VmRow.first (ANCHOR_STATE 8) (PI_ANCHOR_STATE 8))
      , .base (.piBinding VmRow.first (TIP_STATE 0) (PI_TIP_STATE 0))
      , .base (.piBinding VmRow.first (TIP_STATE 1) (PI_TIP_STATE 1))
      , .base (.piBinding VmRow.first (TIP_STATE 2) (PI_TIP_STATE 2))
      , .base (.piBinding VmRow.first (TIP_STATE 3) (PI_TIP_STATE 3))
      , .base (.piBinding VmRow.first (TIP_STATE 4) (PI_TIP_STATE 4))
      , .base (.piBinding VmRow.first (TIP_STATE 5) (PI_TIP_STATE 5))
      , .base (.piBinding VmRow.first (TIP_STATE 6) (PI_TIP_STATE 6))
      , .base (.piBinding VmRow.first (TIP_STATE 7) (PI_TIP_STATE 7))
      , .base (.piBinding VmRow.first (TIP_STATE 8) (PI_TIP_STATE 8))
      , .base (.piBinding VmRow.first BLOCK_LEN PI_BLOCK_LEN)
      , .base (.piBinding VmRow.first REQ_DEPTH PI_REQ_DEPTH) ] := rfl

/-- Layout sanity, as theorems rather than guards: the two nine-limb anchors are contiguous, disjoint
and inside the declared width, and nine radix-`2^31` limbs cover a 255-bit Pasta `Fp`. -/
theorem mina_layout_wellformed :
    ANCHOR_STATE 0 = 12 ∧ ANCHOR_STATE 8 = 20 ∧ TIP_STATE 0 = 21 ∧ TIP_STATE 8 = 29
      ∧ TIP_STATE 8 < MINA_LC_WIDTH ∧ BLOCK_LEN < ANCHOR_STATE 0
      ∧ PI_TIP_STATE 8 < PI_BLOCK_LEN ∧ PI_REQ_DEPTH < MINA_PI_COUNT
      ∧ 31 * STATE_LIMBS ≥ 255 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The three carriers are real hidden trace columns and none is PI-bound: a carrier a verifier could
set from outside the proof would be no carrier at all. -/
theorem mina_carriers_hidden :
    LINK_OK < MINA_LC_WIDTH ∧ PICKLES_OK < MINA_LC_WIDTH ∧ CANON_OK < MINA_LC_WIDTH
      ∧ LINK_OK < BLOCK_LEN ∧ PICKLES_OK < BLOCK_LEN ∧ CANON_OK < BLOCK_LEN := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §4 — non-vacuous per-gate lemmas (the SOURCE constraints bite, both directions).

Each is an `iff` on the constraint's own `holds`, so a gate that stopped saying what its name says
goes red here. The compiler carries these to the emitted bodies through
`EffectLower.lowerConstraint_holdsAt_iff` + `AirBuilder.headToExpr_eval` (§5). -/

theorem blockLenC_holds_iff (a : Assignment) :
    blockLenC.holds a ↔ a BLOCK_LEN = a ANCHOR_H + a SEG_LEN := Iff.rfl

theorem witDepthC_holds_iff (a : Assignment) :
    witDepthC.holds a ↔ a WIT_DEPTH + a SUBMIT_H = a BLOCK_LEN := Iff.rfl

theorem segSlackC_holds_iff (a : Assignment) :
    segSlackC.holds a ↔ a SEG_SLACK + 1 = a SEG_LEN := Iff.rfl

theorem anchSlackC_holds_iff (a : Assignment) :
    anchSlackC.holds a ↔ a ANCH_SLACK + a ANCHOR_H = a SUBMIT_H := Iff.rfl

theorem depthSlackC_holds_iff (a : Assignment) :
    depthSlackC.holds a ↔ a DEPTH_SLACK + a REQ_DEPTH = a WIT_DEPTH := Iff.rfl

theorem linkC_holds_iff (a : Assignment) : linkC.holds a ↔ a LINK_OK = 1 := Iff.rfl

theorem picklesC_holds_iff (a : Assignment) : picklesC.holds a ↔ a PICKLES_OK = 1 := Iff.rfl

theorem canonC_holds_iff (a : Assignment) : canonC.holds a ↔ a CANON_OK = 1 := Iff.rfl

/-! ## §5 — `airAccepts`: the descriptor's acceptance predicate on one row.

The eight gate residuals vanish and the three slacks lie in the range interval `[0, 2^32)` — the
denotation `DescriptorIR2.range_row_mem_iff` connects the emitted lookups to. This is "the descriptor
accepts this row"; the twenty PI pins are the addressing / state-write layer around it. -/

/-- The range interval one slack column must fall in. -/
def inRange (a : Assignment) (col : Nat) : Prop :=
  0 ≤ a col ∧ a col < (2 : ℤ) ^ MINA_RANGE_BITS

/-- **`airAccepts a`** — the emitted verify logic accepts row `a`. -/
def airAccepts (a : Assignment) : Prop :=
  blockLenC.holds a
  ∧ witDepthC.holds a
  ∧ segSlackC.holds a ∧ inRange a SEG_SLACK
  ∧ anchSlackC.holds a ∧ inRange a ANCH_SLACK
  ∧ depthSlackC.holds a ∧ inRange a DEPTH_SLACK
  ∧ linkC.holds a ∧ picklesC.holds a ∧ canonC.holds a

/-- **THE RANGE TOOTH IS THE EMITTED ONE.** A slack column in `inRange` is exactly a column whose
singleton row is in the declared range table — so `airAccepts`'s interval is the emitted lookup's
denotation, not a second private notion of "in range". -/
theorem inRange_iff_mem_rangeRows (a : Assignment) (col : Nat) :
    inRange a col ↔ [a col] ∈ rangeRows MINA_RANGE_BITS :=
  (range_row_mem_iff (a col) MINA_RANGE_BITS).symm

/-- **THE COMPILER CARRIES THE MEANING.** Each emitted gate holds on a transition row exactly when its
SOURCE constraint holds mod `p`. Stated over an arbitrary source constraint (the general lemma is
`EffectLower.lowerConstraint_holdsAt_iff`); the eight `iff`s of §4 then say what each emitted gate
bites on. This is why no gate BODY is transcribed in §3a — the normal form is the compiler's, the
MEANING is what is pinned. -/
theorem emitted_gate_means_source (hash : List ℤ → ℤ)
    (tf : Dregg2.Circuit.DescriptorIR2.TraceFamily)
    (env : Dregg2.Circuit.Emit.EffectVmEmit.VmRowEnv) (isFirst : Bool) (c : Constraint) :
    (Dregg2.Circuit.Emit.EffectLower.lowerConstraint c).holdsAt hash tf env isFirst false
      ↔ (c.lhs.eval env.loc ≡ c.rhs.eval env.loc [ZMOD Dregg2.Circuit.Emit.EffectLower.P]) :=
  Dregg2.Circuit.Emit.EffectLower.lowerConstraint_holdsAt_iff hash tf env isFirst c

/-! ## §6 — THE REFINEMENT: acceptance ⟹ `minaVerifyDecision` ⟹ `MinaValidAt`. -/

/-- **SOUNDNESS.** Fed a row whose witness columns read an update's true projections — the segment
length, the pinned anchor height, the submitted height and the required depth as felts, the three
carriers as `if · then 1 else 0` — if the emitted verify logic accepts, then the exported scalar
decision `minaVerifyDecision` accepts, at the depth the AIR DERIVED rather than one the prover chose.

⚑ Note what is NOT a hypothesis: `witDepth`. It is forced by G1+G2 to `(anchorH + segLen) − submitH`,
and the conclusion is stated at that value. A prover cannot supply a depth. -/
theorem minaLcAir_sound (a : Assignment) (segLen anchorH submitH reqDepth : Nat)
    (linkB picklesB canonB : Bool)
    (hsl : a SEG_LEN = (segLen : ℤ)) (hah : a ANCHOR_H = (anchorH : ℤ))
    (hsh : a SUBMIT_H = (submitH : ℤ)) (hrd : a REQ_DEPTH = (reqDepth : ℤ))
    (hlk : a LINK_OK = (if linkB then (1 : ℤ) else 0))
    (hpk : a PICKLES_OK = (if picklesB then (1 : ℤ) else 0))
    (hcn : a CANON_OK = (if canonB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    minaVerifyDecision segLen anchorH submitH (anchorH + segLen - submitH) reqDepth
      linkB picklesB canonB = true := by
  obtain ⟨hbl, hwd, hss, ⟨hss0, _⟩, has, ⟨has0, _⟩, hds, ⟨hds0, _⟩, hlkC, hpkC, hcnC⟩ := hacc
  rw [blockLenC_holds_iff] at hbl
  rw [witDepthC_holds_iff] at hwd
  rw [segSlackC_holds_iff] at hss
  rw [anchSlackC_holds_iff] at has
  rw [depthSlackC_holds_iff] at hds
  rw [linkC_holds_iff] at hlkC
  rw [picklesC_holds_iff] at hpkC
  rw [canonC_holds_iff] at hcnC
  -- The published height is the pinned anchor plus the exhibited segment. NOT a free witness.
  have hblZ : a BLOCK_LEN = (anchorH : ℤ) + (segLen : ℤ) := by rw [hbl, hah, hsl]
  -- The witnessed depth is measured to that DERIVED tip.
  have hwdZ : a WIT_DEPTH = (anchorH : ℤ) + (segLen : ℤ) - (submitH : ℤ) := by
    have h := hwd; rw [hblZ, hsh] at h; linarith
  have hssZ : a SEG_SLACK = (segLen : ℤ) - 1 := by
    have h := hss; rw [hsl] at h; linarith
  have hasZ : a ANCH_SLACK = (submitH : ℤ) - (anchorH : ℤ) := by
    have h := has; rw [hah, hsh] at h; linarith
  have hdsZ : a DEPTH_SLACK = (anchorH : ℤ) + (segLen : ℤ) - (submitH : ℤ) - (reqDepth : ℤ) := by
    have h := hds; rw [hwdZ, hrd] at h; linarith
  -- Tooth 1: the segment is non-empty.
  have hseg : 0 < segLen := by
    have h : (1 : ℤ) ≤ (segLen : ℤ) := by rw [hssZ] at hss0; linarith
    exact_mod_cast h
  -- Tooth 2: the submitted height is AT OR ABOVE the pinned anchor.
  have hanch : anchorH ≤ submitH := by
    have h : (anchorH : ℤ) ≤ (submitH : ℤ) := by rw [hasZ] at has0; linarith
    exact_mod_cast h
  -- Tooth 3: the required depth is met, at the DERIVED witnessed depth.
  have hsum : reqDepth + submitH ≤ anchorH + segLen := by
    have h : (reqDepth : ℤ) + (submitH : ℤ) ≤ (anchorH : ℤ) + (segLen : ℤ) := by
      rw [hdsZ] at hds0; linarith
    exact_mod_cast h
  have hdep : reqDepth ≤ anchorH + segLen - submitH := by omega
  -- The three named carriers.
  have hlk' : linkB = true := by
    rw [hlk] at hlkC; cases linkB with | true => rfl | false => simp at hlkC
  have hpk' : picklesB = true := by
    rw [hpk] at hpkC; cases picklesB with | true => rfl | false => simp at hpkC
  have hcn' : canonB = true := by
    rw [hcn] at hcnC; cases canonB with | true => rfl | false => simp at hcnC
  unfold minaVerifyDecision
  simp only [hlk', hpk', hcn', Bool.and_eq_true, decide_eq_true_eq, Bool.and_true, and_true]
  exact ⟨⟨hseg, hanch⟩, hdep⟩

/-- **THE PAYOFF: a satisfying AIR row ENTAILS Mina anchored validity.** If a row reads update `u`'s
true projections under trusted state `ts` and the emitted verify logic accepts, then `u` is
Mina-ANCHORED-VALID relative to `ts` — every exhibited block genuinely proved, the segment
parent-linked and height-contiguous from the pinned anchor, and the confirmation depth BACKED by that
many exhibited blocks rather than asserted by subtracting two claimed heights.

⚠ Inherits `MinaLeaf.picklesSound`, the undischarged IPA/FRI floor. ⚠ Not fork choice — see the
header's scope note. -/
theorem minaLcAir_no_forgery (L : MinaLeaf) (ts : MinaTrustedState L) (u : MinaUpdate L)
    (a : Assignment)
    (hsl : a SEG_LEN = (u.blocks.length : ℤ))
    (hah : a ANCHOR_H = (ts.anchorHeight : ℤ))
    (hsh : a SUBMIT_H = (u.submittedHeight : ℤ))
    (hrd : a REQ_DEPTH = (ts.confirmationDepth : ℤ))
    (hlk : a LINK_OK = (if linkOk L ts u then (1 : ℤ) else 0))
    (hpk : a PICKLES_OK = (if picklesOk L u then (1 : ℤ) else 0))
    (hcn : a CANON_OK = (if canonOk L u then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    MinaValidAt L ts u := by
  have hdec := minaLcAir_sound a u.blocks.length ts.anchorHeight u.submittedHeight
    ts.confirmationDepth (linkOk L ts u) (picklesOk L u) (canonOk L u)
    hsl hah hsh hrd hlk hpk hcn hacc
  -- The AIR-DERIVED depth IS `witnessedDepth` (`tipHeight = anchorHeight + blocks.length`), so what
  -- the AIR proved is literally `minaVerify`.
  have hmv : minaVerify L ts u = true := hdec
  exact mina_no_forgery L ts u hmv

/-- **COMPLETENESS (the non-vacuity partner).** An honest prover CAN fill the row: for any update the
exported decision accepts, the row that reads its true projections and fills the three slacks with
their genuine values satisfies `airAccepts` — given that the heights fit the declared 32-bit interval
(every Mina `blockchain_length` does) and that the settlement was submitted at or below the witnessed
tip (`hsub`, which is what "the settlement is in this segment's past" means).

Without this, "the descriptor refuses forgeries" would be satisfied by a descriptor that refuses
everything. -/
theorem minaLcAir_complete (a : Assignment) (segLen anchorH submitH reqDepth : Nat)
    (linkB picklesB canonB : Bool)
    (hsl : a SEG_LEN = (segLen : ℤ)) (hah : a ANCHOR_H = (anchorH : ℤ))
    (hsh : a SUBMIT_H = (submitH : ℤ)) (hrd : a REQ_DEPTH = (reqDepth : ℤ))
    (hblk : a BLOCK_LEN = (anchorH : ℤ) + (segLen : ℤ))
    (hwd : a WIT_DEPTH = (anchorH : ℤ) + (segLen : ℤ) - (submitH : ℤ))
    (hss : a SEG_SLACK = (segLen : ℤ) - 1)
    (has : a ANCH_SLACK = (submitH : ℤ) - (anchorH : ℤ))
    (hds : a DEPTH_SLACK = (anchorH : ℤ) + (segLen : ℤ) - (submitH : ℤ) - (reqDepth : ℤ))
    (hlk : a LINK_OK = (if linkB then (1 : ℤ) else 0))
    (hpk : a PICKLES_OK = (if picklesB then (1 : ℤ) else 0))
    (hcn : a CANON_OK = (if canonB then (1 : ℤ) else 0))
    (hfit : anchorH + segLen < 2 ^ MINA_RANGE_BITS)
    (hsub : reqDepth + submitH ≤ anchorH + segLen)
    (hdecT : minaVerifyDecision segLen anchorH submitH (anchorH + segLen - submitH) reqDepth
      linkB picklesB canonB = true) :
    airAccepts a := by
  unfold minaVerifyDecision at hdecT
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdecT
  obtain ⟨⟨⟨⟨⟨hseg, hanch⟩, _hdep⟩, hlk1⟩, hpk1⟩, hcn1⟩ := hdecT
  have hfitZ : (anchorH : ℤ) + (segLen : ℤ) < (2 : ℤ) ^ MINA_RANGE_BITS := by exact_mod_cast hfit
  have hanchZ : (anchorH : ℤ) ≤ (submitH : ℤ) := by exact_mod_cast hanch
  have hsegZ : (1 : ℤ) ≤ (segLen : ℤ) := by exact_mod_cast hseg
  have hsubZ : (reqDepth : ℤ) + (submitH : ℤ) ≤ (anchorH : ℤ) + (segLen : ℤ) := by
    exact_mod_cast hsub
  have hrd0 : (0 : ℤ) ≤ (reqDepth : ℤ) := Int.natCast_nonneg reqDepth
  have hsh0 : (0 : ℤ) ≤ (submitH : ℤ) := Int.natCast_nonneg submitH
  have hah0 : (0 : ℤ) ≤ (anchorH : ℤ) := Int.natCast_nonneg anchorH
  have hseg0 : (0 : ℤ) ≤ (segLen : ℤ) := Int.natCast_nonneg segLen
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [blockLenC_holds_iff, hblk, hah, hsl]
  · rw [witDepthC_holds_iff, hwd, hsh, hblk]; ring
  · rw [segSlackC_holds_iff, hss, hsl]; ring
  · rw [hss]; linarith
  · rw [hss]; linarith
  · rw [anchSlackC_holds_iff, has, hah, hsh]; ring
  · rw [has]; linarith
  · rw [has]; linarith
  · rw [depthSlackC_holds_iff, hds, hrd, hwd]; ring
  · rw [hds]; linarith
  · rw [hds]; linarith
  · rw [linkC_holds_iff, hlk, hlk1]; norm_num
  · rw [picklesC_holds_iff, hpk, hpk1]; norm_num
  · rw [canonC_holds_iff, hcn, hcn1]; norm_num

/-! ## §7 — ⚑ THE REFUSING WITNESSES. Both polarities, exhibited, not asserted.

Each row is a CONCRETE assignment and each refusal is a proof that `airAccepts` FAILS on it. A refusal
nothing witnesses is decoration; these are the four shapes this campaign actually names — a shallower
losing fork, a bent proof word, a forged `blockchain_length`, and the deployed observer's own
unanchored subtraction. -/

/-- A row from its twelve logic-column values, index-ordered (`SEG_LEN` … `BLOCK_LEN`). Columns above
`BLOCK_LEN` are the PI anchors and read `0` here — the refusals below are about the LOGIC, and the
pins are the addressing layer around it. -/
def rowOf (vs : List ℤ) : Assignment := fun w => vs.getD w 0

/-- **THE HONEST ROW.** Anchor pinned at height 1000; 300 exhibited, linked, proof-carrying blocks;
the settlement submitted at 1010; Samasika `k = 290`. Derived tip 1300, derived witnessed depth 290 —
the requirement met exactly. All three carriers true. ACCEPTED. -/
def honestRow : Assignment := rowOf [300, 1000, 1010, 290, 290, 299, 10, 0, 1, 1, 1, 1300]

theorem honest_row_accepted : airAccepts honestRow := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
      depthSlackC_holds_iff, linkC_holds_iff, picklesC_holds_iff, canonC_holds_iff,
      honestRow, rowOf, SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
      DEPTH_SLACK, LINK_OK, PICKLES_OK, CANON_OK, BLOCK_LEN, MINA_RANGE_BITS, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;> norm_num

/-- ⚑ **REFUSED — A LOSING FORK.** The same pinned anchor and the same submitted height, but only 295
exhibited blocks against the honest 300: derived tip 1295, derived depth 285, five short of `k = 290`.
The prover fills every column honestly, so every GATE holds; `DEPTH_SLACK = −5` is outside `[0, 2^32)`
and the range lookup has no satisfying table row.

⚑ This is the shallower branch of a genuine disagreement refused by the DESCRIPTOR, not by an
off-chain comparison. -/
def losingForkRow : Assignment := rowOf [295, 1000, 1010, 285, 290, 294, 10, -5, 1, 1, 1, 1295]

theorem losing_fork_refused : ¬ airAccepts losingForkRow := by
  intro h
  have hds0 := h.2.2.2.2.2.2.2.1.1
  simp only [losingForkRow, rowOf, DEPTH_SLACK, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hds0
  norm_num at hds0

/-- ⚑ **REFUSED — A BENT PROOF WORD.** Every height, depth and slack is the honest row's; only the
Pickles carrier is `0`, which is what a block whose Wrap proof fails to verify AT ITS OWN state hash
produces. The `PICKLES_OK = 1` gate refuses it. -/
def bentProofRow : Assignment := rowOf [300, 1000, 1010, 290, 290, 299, 10, 0, 1, 0, 1, 1300]

theorem bent_proof_word_refused : ¬ airAccepts bentProofRow := by
  intro h
  have hpk := h.2.2.2.2.2.2.2.2.2.1
  rw [picklesC_holds_iff] at hpk
  simp only [bentProofRow, rowOf, PICKLES_OK, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hpk
  norm_num at hpk

/-- ⚑ **REFUSED — THE FREE `blockchain_length`.** The exact shape the `mina-tip` lane measured: the
liar exhibits FIVE blocks above the anchor but publishes `blockchain_length = 1300` as though it had
300, and fills the depth columns to match its claim. Every carrier is `1`, every slack is
non-negative, and the depth requirement is "met" — G2, G3, G4, G5 ALL HOLD on this row.

G1 (`BLOCK_LEN = ANCHOR_H + SEG_LEN`) is the only thing that refuses it: `1300 ≠ 1000 + 5`. Without
G1 this row passes, and the published height — the one field the truncated 1,544-byte reply left
standing — is a free witness again. -/
def forgedHeightRow : Assignment := rowOf [5, 1000, 1010, 290, 290, 4, 10, 0, 1, 1, 1, 1300]

theorem forged_height_refused : ¬ airAccepts forgedHeightRow := by
  intro h
  have hbl := h.1
  rw [blockLenC_holds_iff] at hbl
  simp only [forgedHeightRow, rowOf, BLOCK_LEN, ANCHOR_H, SEG_LEN, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hbl
  norm_num at hbl

/-- ⚑ **REFUSED — THE DEPLOYED OBSERVER'S OWN ARITHMETIC.**
`LightClientMina.witnessedDepth_unbounded_without_anchor_bound` exhibits the wound as a theorem: with
the anchor at 1000 and the submitted height at 0, a ONE-BLOCK segment "witnesses" depth 1001, and
`mina_observer::observe_settlement`'s `tip_height.saturating_sub(submitted_height)` accepts it.

Here `ANCH_SLACK = SUBMIT_H − ANCHOR_H = −1000` is outside `[0, 2^32)`. The descriptor refuses the
deployed observer's own accepting input. -/
def unanchoredRow : Assignment := rowOf [1, 1000, 0, 1001, 290, 0, -1000, 711, 1, 1, 1, 1001]

theorem observer_arithmetic_refused : ¬ airAccepts unanchoredRow := by
  intro h
  have has0 := h.2.2.2.2.2.1.1
  simp only [unanchoredRow, rowOf, ANCH_SLACK, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at has0
  norm_num at has0

/-- ⚑ **THE POLARITY PAIR, AS ONE STATEMENT.** The emitted logic DISCRIMINATES: it accepts the honest
anchored head and refuses all four forgery shapes. A descriptor that accepted everything, or refused
everything, fails this. -/
theorem mina_air_discriminates :
    airAccepts honestRow
      ∧ ¬ airAccepts losingForkRow
      ∧ ¬ airAccepts bentProofRow
      ∧ ¬ airAccepts forgedHeightRow
      ∧ ¬ airAccepts unanchoredRow :=
  ⟨honest_row_accepted, losing_fork_refused, bent_proof_word_refused, forged_height_refused,
   observer_arithmetic_refused⟩

end Dregg2.Circuit.Emit.LightClientMinaAir
