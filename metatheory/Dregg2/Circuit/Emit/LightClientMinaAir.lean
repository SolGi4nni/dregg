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
in this file** — eight `.gate` legs, three `.lookup` legs against a declared range table, **two
`.limbs` legs and two narrow-table `.lookup` legs for the canonicality rung**, twenty `.pin` legs,
and the `VmConstraint2`s are the compiler's business. It is the second deployed descriptor in the
tree authored this way (`DfaRoutingTableEmit.tableRoutingDesc` was the first, 2026-08-01) and the
first authored that way from scratch rather than by fusing a hand-written twin.

The vocabulary was ADEQUATE, twice: `EffectAir.mainRailOk` is `true` by `rfl`
(`minaHeadAir_mainRailOk`), so no leg lowered to `EffectLower.refuseConstraints`. ⚑ The canonicality
rung needed the `.limbs` leg that landed for the peer-chain tallies — a nine-lane Pasta element is
exactly "a quantity no felt can hold", the construct that leg exists for — and needed **nothing
else**: no new `AirLeg` constructor, no new lowering, no hand-written gate. That is the finding,
stated plainly as §3 asks.

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
outside `[0, 2^24)` and the range lookup has no satisfying table row.

## The three slack teeth (the ≤ relations, wrap-free)

Field elements have no order, so each `≤` rides as a non-negative SLACK pinned into `[0, 2^32)` by a
lookup against the declared range table — the same shape `LightClientEthAir`'s quorum tooth uses.

    G3  SEG_SLACK   + 1         = SEG_LEN     +  range(SEG_SLACK)     ⟹  0 < segLen
    G4  ANCH_SLACK  + ANCHOR_H  = SUBMIT_H    +  range(ANCH_SLACK)    ⟹  anchorH ≤ submittedH
    G5  DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH   +  range(DEPTH_SLACK)   ⟹  reqDepth ≤ witDepth

⚑ The width is **24 bits, and the ceiling is the FIELD, not the wire.** The obvious choice —
32, because Mina's `blockchain_length` is a `u32` — is VACUOUS: `p = 2013265921 < 2^32`, so every
field element is already in `[0, 2^32)` and the lookup refuses nothing. A slack of `−5` IS the field
element `p − 5`, and refusing it is the entire job. `mina_wrapped_slack_is_outside_the_range` states
the gap as a theorem; `MINA_RANGE_BITS` documents the arithmetic.

## NAMED verified CARRIERS — ⚑ ONE OF THE THREE IS NO LONGER A WITNESS

`LINK_OK` / `PICKLES_OK` / `CANON_OK` are the three results `LightClientMinaGate`'s wire gate takes
as `lk` / `pk` / `cn`. They shipped here as witnessed boolean columns forced `= 1` — pinned to the
statement, so BENDING one is refused, but with **nothing in the circuit computing them**. §1a and §5a
change that for the third:

  * `LINK_OK`    — the Poseidon parent-linkage fold over the exhibited segment. STILL A WITNESS
    HERE. Derived one module over (`Circuit/Emit/LightClientMinaHashFold.lean`) at a Poseidon over
    **Pasta `Fp`**, which at BabyBear is non-native arithmetic; and the fold is a per-BLOCK object
    while this descriptor is one row, so it is not a lane away.
  * `PICKLES_OK` — the per-block Pickles/Kimchi Wrap-proof result. STILL A WITNESS, and it is the
    expensive one by three orders of magnitude — see §1b. `Circuit/Emit/MinaRealBlockGate.lean`
    renders it on a real devnet block, natively.
  * `CANON_OK`   — ⚑ **DERIVED, for the two `Fp` elements this descriptor publishes.** Eighteen
    lookups on the lane columns it already carried, no new column and no gate: `canonAccepts`,
    `mina_anchor_and_tip_are_canonical`. `shifted_anchor_old_admits_new_rejects` exhibits the row
    the witnessed bit waved through and the emitted descriptor now refuses.

⚠ **Say the residual exactly.** `LightClientMina.canonOk` quantifies over EVERY exhibited block's
four state-row field elements; this descriptor's columns hold the ANCHOR and the TIP and nothing
else, so what is derived is canonicality of those two — which is precisely what the anchor-substitution
attack on the record (`stateChain_anchor_shift_collides`) needs, and precisely not the whole per-block
predicate. The per-block half stays witnessed, and it stays witnessed because the descriptor is
SINGLE-ROW, not because the vocabulary is short (§3's `mainRailOk` is still `true`).

⚠ **And what the replaced gate was.** `LightClientMinaHashFold.minaRowWidthGates` is the tree's Mina
canonicality AIR: four 254-bit `StakeWidthRange.widthGate`s, 1020 constraints per state row, with a
forcing lemma stated over `Assignment = Nat → ℤ`. The deployed denotation is mod `p`, and at
`P = 2013265921` a 254-bit recomposition reaches every residue — the gate refuses nothing, and it
gates a 255-bit Pasta element in one 30.9-bit column besides. It is in no descriptor and cannot be.
§1a is its replacement at the representation BabyBear actually has: nine lanes.

⚠ So a STARK over this descriptor proves the ANCHORING / DEPTH / HEIGHT-DERIVATION logic AND the
canonicality of the two published field elements, given `LINK_OK` and `PICKLES_OK`.

## ⚑ §1b — WHAT AN IN-AIR PICKLES VERIFIER WOULD COST (measured, so the next rung is priced)

Counted off the Lean verifier this tree already carries (`KimchiVerify`, `MinaWrap*`,
`PastaPoseidon`), for ONE Wrap verification: **131 × 255-bit curve scalar multiplications** (40
`public_comm` Lagrange terms + 1 `f_comm` + 9 `ft_comm` + 47 ξ-aggregate + 34 opening, of which 30
are the 15 IPA rounds' L/R), **106 Poseidon-over-Pasta permutations** (55 full rounds, width 3,
x^7), and ≈1,500 field multiplications in the scalar formulas — **≈1.06 M Pasta-field
multiplications** in total, ≈935 K of them inside the curve ladders. The `sg == ⟨s, srs.g⟩` leg is a
**32,768-term SRS MSM** on top and is not discharged in-kernel anywhere.

⚑ **The felts-per-`Fp` figure is TWO different numbers, and conflating them is how this gets
underpriced.** For STORAGE it is **9 lanes at 29 bits** — the encoding this file already uses, and
29 is the last wrap-free width (`RangeFieldContainment.wrap_free_iff_le_29`). For MULTIPLICATION it
is not: a limb product must not wrap, so `2b + log₂(k) < 30.9`, which at `k = ⌈255/b⌉` forces
**b ≈ 13 and k ≈ 20 limbs**. A 29-bit limb cannot be multiplied at BabyBear at all — its square is
`2^58`.

So one non-native Pasta multiplication is schoolbook `k² = 400` limb products, `2k − 1 = 39`
accumulator columns, a modular reduction of the same order, and ~40 carry rungs each with a range
lookup: **≈10³ BabyBear constraints per Pasta multiplication**, and the carry chain is exactly the
`LimbTally` shape, so the vocabulary exists.

**One Wrap verification is then ≈10⁹ constraints.** At a generous ~100 constraints packed per row
that is **~10⁷ rows ≈ 2^23.3**, and a trace of 2^23 rows × ~10² columns is ~10⁹ felts ≈ 4 GB
committed — before the 32,768-term SRS MSM leg, which multiplies it again. Against this descriptor's
**49 constraints and 8 rows**, that is seven orders of magnitude.

⚑ **So: not a week and not a season at this construction.** The number says the construction is
wrong, not that the schedule is long — the reachable shapes are RECURSION (verify the Pasta proof on
the Pasta side once, as `MinaShrinkPartition`/the shrink terminal already do, and carry a small
statement across) or a proof system over a field that can hold `Fp`. `CANON_OK` was landed instead
because it is the one carrier whose content is arithmetic BabyBear can actually hold: an inequality
on nine lanes, which costs 18 lookups.

## Public inputs — ⚑ these ARE the dregg state write

    PI[0..8]   ANCHOR_STATE[i]  — the OPERATOR-PINNED weak-subjectivity anchor state hash, as its
                                  nine `Faithful9` KEY LANES. The trust root the whole acceptance
                                  is relative to.
    PI[9..17]  TIP_STATE[i]     — the VERIFIED head's Mina protocol-state hash, nine lanes.
    PI[18]     BLOCK_LEN        — the verified head's `blockchain_length` (DERIVED by G1).
    PI[19]     REQ_DEPTH        — the Samasika confirmation depth `k` the acceptance met (290 on
                                  mainnet). Published so a verifier sees WHICH depth policy was met
                                  rather than trusting the prover picked a real one.

⚑ NINE LANES, NOT ONE FELT, and NOT nine 31-bit slices either. The repo has paid for both mistakes:
a single BabyBear anchor felt binds a ~31-BIT PROJECTION of a 256-bit hash, so two distinct Mina
heads agreeing in 31 bits would both verify; and a "radix-2^31" slicing is not representable at all,
since BabyBear's `p = 2013265921 < 2^31` means a 31-bit limb can exceed the modulus and alias. The
encoding is the tree's own PROVEN one — `Faithful9::from_key_lanes9` / Lean `keyToLanes9`: the 32
bytes as one little-endian 256-bit number in its NINE base-`2^29` digits, lanes 0..=7 below `2^29`
and lane 8 below `2^24`, `8·29 + 24 = 256` EXACTLY, so the image is exactly `2^256` and the encoding
loses nothing. Injectivity is machine-checked (`lanes9ToField_fieldToLanes9`,
`fieldToLanes9_injective`, `nine_lanes_is_the_minimum : P^8 < 2^256 ≤ P^9`).

⚠ TWO NAMED residuals on the anchors, and they are different:
  1. This AIR PI-binds the eighteen lane columns but carries NO GATE relating them to a 32-byte
     value. The lane-vector ↔ head equality is enforced by the CONSUMER
     (`turn/src/executor/mina_head_verifier.rs::check_head_binding`, which refuses the turn), not
     in-circuit. That is a real refusal, and it is an executor check.
  2. `TIP_STATE` is not arithmetically tied to the `LINK_OK` fold's terminal digest inside this AIR
     either. That tie is `LightClientMinaHashFold`'s object and the `proofBind` recursion seam;
     until it lands, the equality is the witness generator's, not a gate's. Say it that way.

## Both polarities, on the EMITTED object (§6, §7)

* ACCEPT — `honest_row_accepted` on the REAL devnet genesis anchor and the REAL block-539508 tip
  (`honest_anchor_lanes_decode_the_devnet_genesis` pins the lanes against the Base58Check decimal);
  `minaLcAir_complete` is the general statement; `minaLcAir_no_forgery` carries acceptance all the
  way to `MinaValidAt`.
* REFUSE — FIVE named refusing witnesses, each a CONCRETE assignment, each `¬ airAccepts`:
  `losing_fork_refused` (a shallower fork), `bent_proof_word_refused` (`PICKLES_OK = 0`),
  `forged_height_refused` (the free-`blockchain_length` liar), `observer_arithmetic_refused` (the
  deployed observer's unanchored subtraction), and ⚑ `shifted_anchor_refused` — the `+p` ANCHOR
  SUBSTITUTION, which `shifted_anchor_old_admits_new_rejects` shows the PRE-RUNG predicate accepted
  with `CANON_OK` witnessed `1`. A refusal that some assignment satisfies is decoration; these are
  exhibited, not asserted.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

`dregg-mina-lightclient-verify::v1` changes shape: **31 → 49 constraints**, **1 → 3 declared
tables** (adding `range_w29` at wire id 98 and `range_w22` at wire id 91). `traceWidth` (30) and
`piCount` (20) are UNCHANGED, so `turn/src/executor/mina_head_verifier.rs`'s `MINA_LC_PI_COUNT` and
the PI layout are untouched. **Re-emit** `circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json`
(`EmitByName.lean`) and **rotate the VK** for this descriptor. Any previously produced proof over the
old shape now fails to verify, which is the intent: the old shape accepted the shifted anchor.
⚠ A witness generator that leaves the eighteen lane columns unfilled now produces an UNSAT row —
`mina_head_verifier.rs` must write the anchor's and the tip's nine `Faithful9` lanes, which is the
same decomposition `check_head_binding` already computes.

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
import Dregg2.Circuit.LimbTally
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Bridge.LightClientMinaGate

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientMinaAir

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId TableDef rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LookupLeg PiPinLeg LimbsLeg)
open Dregg2.Circuit.LimbTally (limbValue LimbsInRange limbValue_nonneg limbValue_lt)
open Dregg2.Circuit.Emit.PastaField (pN)
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

/-- The number of lanes a 32-byte Mina state hash is exposed as: NINE, the tree's proven
`Faithful9` key encoding (`8·29 + 24 = 256` exactly, image exactly `2^256`). A SINGLE BabyBear felt
would bind a ~31-bit PROJECTION, and two heads agreeing in it would both verify. -/
def STATE_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (lane `i`)** — the operator-pinned weak-subjectivity anchor state hash, as its
`Faithful9` key lanes (base `2^29`, least-significant first). Columns 12..20, PI slots 0..8. -/
def ANCHOR_STATE (i : Nat) : Nat := 12 + i

/-- **PUBLIC / STATE-WRITE (lane `i`)** — the VERIFIED head's Mina protocol-state hash, as its
`Faithful9` key lanes. Columns 21..29, PI slots 9..17. -/
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

/-- The slack range width. ⚑ **24, AND THE CEILING IS THE FIELD, NOT THE WIRE.**

The obvious choice is 32 — Mina's `blockchain_length` is a `u32` — and it is **VACUOUS**. BabyBear's
`p = 2013265921 < 2^31 < 2^32`, so EVERY field element already lies in `[0, 2^32)` and a 32-bit
range lookup constrains nothing at all. A slack of `−5` is the field element `p − 5`, and the whole
point of the tooth is that `p − 5` must be REFUSED.

So the interval has to sit strictly inside the field with room to spare: `2^24 = 16,777,216`, while
the smallest wrapped negative is `p − 2^24 = 1,996,488,705`, two orders of magnitude above the
ceiling (`mina_wrapped_slack_is_outside_the_range`). And 2^24 excludes no honest value — at Mina's
~3-minute blocks, height 16.7M is roughly 95 years of chain. -/
def MINA_RANGE_BITS : Nat := 24

/-! ## §1a — ⚑ THE CANONICALITY CARRIER, DERIVED: `CANON_OK`'s content on the two `Fp` elements this
descriptor actually carries, as lookups on the lane columns it already has.

## The defect this closes, and why the existing gate could not close it

`LightClientMinaHashFold.minaRowWidthGates` is the tree's canonicality AIR for Mina: four
`StakeWidthRange.widthGate`s at 254 bits — `4 × (254 + 1) = 1020` constraints per state row — with a
forcing lemma `minaRowWidthGates_forces`. ⚠ **That lemma is stated over `Assignment = Nat → ℤ`, and
the deployed denotation is mod `p`.** Its recomposition gate is `v − Σ_{i<254} 2^i·bᵢ = 0`; over
BabyBear (`P = 2013265921`) the 254 free bits can hit EVERY residue, so every field element has a
satisfying bit assignment and the gate refuses nothing — the `range_vacuous_at_or_above_31` class in
bit-decomposition clothing. It is worse than vacuous: it gates a 255-bit Pasta element sitting in ONE
BabyBear column, and no such column exists. `minaRowWidthGates` is not, and cannot be, part of any
emitted descriptor; it is a free-floating `List VmConstraint2` no `EffectVmDescriptor2` carries.

## What replaces it — and it costs NO new columns and NO gates

At BabyBear a Pasta `Fp` element is not a felt, it is the NINE LANES this descriptor already
publishes (`ANCHOR_STATE`, `TIP_STATE`). So canonicality is a statement about a limb vector, and it
is TWO WIDTHS OF LOOKUP and nothing else — the shape `KeyCanonicity9Emit` established for the key
nonet, at the Pasta threshold instead of the byte-window one:

    lanes 0..7  <  2^29     -- eight lookups, the `.limbs` leg (`MINA_LANE_BITS`)
    lane  8     <  2^22     -- ONE lookup, on a NARROWER table (`MINA_TOP_LANE_BITS`)

⚑ `2^22 · 2^232 = 2^254` EXACTLY, and `2^254 < pN` (`pow254_lt_mina_p`), so the two legs force the
denoted value below the Pasta modulus: `mina_lane_canon_forces_canonical`. Both widths are wrap-free
(`≤ 29`, `RangeFieldContainment.wrap_free_iff_le_29`), so unlike the 254-bit gate they BITE at the
deployed field.

⚠ The completeness cost, said out loud: `< 2^254` REFUSES the canonical band `[2^254, pN)`, which is
`pN − 2^254 = 45560315531419706090280762371685220353 ≈ 2^125.1` wide — a `2^-129` fraction of the
field. `LightClientMinaHashFold` already took this trade (`MINA_FIELD_BITS = 254`); both real devnet
state hashes are in the window and proved so there.

## Why the top lane at 22 and not the encoder's 24

`Faithful9`/`KeyLanes9` pins lane 8 below `2^24` because the encoder's image is exactly `2^256`. That
is the 32-BYTE-STRING canonicity, and it is strictly weaker than the FIELD one: the anchor-substitution
witness `DEVNET_GENESIS_STATE_HASH + pN` is a perfectly legal nonet with lane 8 = 5514899 — below
`2^24`, so the encoder's own gate ADMITS it — and it chains to the identical tip state hash
(`LightClientMinaHashFold.stateChain_anchor_shift_collides`). Only the 22-bit table refuses it. -/

/-- The lane width of the nine-lane Pasta-`Fp` encoding: base `2^29`, the maximum wrap-free width at
BabyBear (`RangeFieldContainment.wrap_free_iff_le_29`). -/
def MINA_LANE_BITS : Nat := 29

/-- ⚑ **The TOP lane's width, and it is the whole canonicality gate: 22, not the encoder's 24.**
`8 · 29 = 232` and `22 + 232 = 254`, so `lane 8 < 2^22` is EXACTLY `value < 2^254`, which is
EXACTLY canonicality (`2^254 < pN`). At 24 the nonet is merely a well-formed 32-byte string and the
`+pN`-shifted anchor passes. -/
def MINA_TOP_LANE_BITS : Nat := 22

/-- The wire-id base for width-tagged range tables, the same convention `EffectVmEmitV2.rangeTidW`
and `FaithfulNoteSpendDescriptorPlan.rangeTid` carry (Rust: `descriptor_ir2.rs`'s
`RANGE_W_TID_BASE = 64`, wire base 69). Re-stated locally rather than imported, as
`FaithfulNoteSpendDescriptorPlan` also does; `mina_range_table_wire_ids` pins the arithmetic. -/
def RANGE_W_TID_BASE : Nat := 64

/-- A width-tagged range table id. -/
def minaRangeTid (bits : Nat) : TableId := .custom (RANGE_W_TID_BASE + bits)

/-- The 29-bit LANE table (lanes 0..7 of each nine-lane state hash). -/
def minaLaneTable : TableDef :=
  ⟨minaRangeTid MINA_LANE_BITS, "range_w29", 1, .rangeLimb MINA_LANE_BITS⟩

/-- ⚑ The 22-bit TOP-LANE table — the narrower one, and the only leg that separates a canonical
Pasta element from a merely well-formed 32-byte nonet. -/
def minaTopLaneTable : TableDef :=
  ⟨minaRangeTid MINA_TOP_LANE_BITS, "range_w22", 1, .rangeLimb MINA_TOP_LANE_BITS⟩

/-- The eight LOW lane columns of the pinned anchor state hash (cols 12..19). -/
def anchorLowLanes : List Nat :=
  [ANCHOR_STATE 0, ANCHOR_STATE 1, ANCHOR_STATE 2, ANCHOR_STATE 3,
   ANCHOR_STATE 4, ANCHOR_STATE 5, ANCHOR_STATE 6, ANCHOR_STATE 7]

/-- The eight LOW lane columns of the verified tip state hash (cols 21..28). -/
def tipLowLanes : List Nat :=
  [TIP_STATE 0, TIP_STATE 1, TIP_STATE 2, TIP_STATE 3,
   TIP_STATE 4, TIP_STATE 5, TIP_STATE 6, TIP_STATE 7]

/-- The FULL nine-lane column vector of a state hash, least-significant lane first — the vector whose
`LimbTally.limbValue` at radix `2^29` IS the `Fp` element. -/
def nonetOf (low : List Nat) (top : Nat) : List Nat := low ++ [top]

/-- **The `Fp` element a nine-lane column vector denotes**, in the limb vocabulary the compiler's
`.limbs` leg is defined against (`LimbTally.limbValue`) rather than a private sum. -/
def stateValue (a : Assignment) (low : List Nat) (top : Nat) : ℤ :=
  limbValue MINA_LANE_BITS a (nonetOf low top)

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

/-- ⚑ **The eight LOW lanes of a state hash, as ONE `.limbs` leg** — the (e) capability
`EffectAirIR` gained for the peer-chain tallies, used here for what it was built for: a quantity no
felt can hold, checked as `k` lookups at a width the field enforces. Lowers to eight range queries
against the 29-bit table (`EffectLower.lowerLimbsLeg`). -/
def lowLanesLeg (cols : List Nat) : AirLeg :=
  .limbs { cols := cols, bits := MINA_LANE_BITS, table := minaRangeTid MINA_LANE_BITS }

/-- ⚑ **The TOP lane, on the NARROW table** — one lookup, and the entire difference between "this
nonet decodes a 32-byte string" and "this nonet denotes a canonical Pasta field element". -/
def topLaneLeg (col : Nat) : AirLeg :=
  .lookup { table := minaRangeTid MINA_TOP_LANE_BITS, tuple := [Expr.var col] }

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
  { tables := [minaRangeTable, minaLaneTable, minaTopLaneTable]
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
      , .gate canonC
      -- ⚑ §1a — the DERIVED canonicality of the two `Fp` elements this descriptor carries.
      , lowLanesLeg anchorLowLanes
      , topLaneLeg (ANCHOR_STATE 8)
      , lowLanesLeg tipLowLanes
      , topLaneLeg (TIP_STATE 8) ]
      ++ anchorStatePins ++ tipStatePins
      ++ [ .pin ⟨VmRow.first, BLOCK_LEN, PI_BLOCK_LEN⟩
         , .pin ⟨VmRow.first, REQ_DEPTH, PI_REQ_DEPTH⟩ ] }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE.** Every leg is main-rail expressible, decided on the emitted
predicate — so no leg lowered to `EffectLower.refuseConstraints` and nothing was hand-written around
the compiler. This is the §3 finding stated as a theorem rather than a sentence. -/
theorem minaHeadAir_mainRailOk : minaHeadAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem minaHeadAir_pinsFit : minaHeadAir.pinsFit MINA_PI_COUNT = true := by rfl

/-- The source carries 35 legs: 8 gates + 3 slack lookups + 2 `.limbs` + 2 top-lane lookups + 20 PI
pins. ⚑ A `.limbs` leg is ONE leg and EIGHT constraints — `minaLcVerifyDesc_constraint_count` is the
number a dropped lane moves, and this one is not. -/
theorem minaHeadAir_leg_count : minaHeadAir.legs.length = 35 := by rfl

/-- ⚑ **THE LIMBED QUANTITIES ARE COUNTED, AND A DROPPED LANE MOVES A NUMBER.** Two nine-lane state
hashes ⟹ two `.limbs` legs lowering to `8 + 8 = 16` per-limb range lookups (`totalRangeLookups`; this
descriptor declares no one-wire `RangeLeg`s, so the 16 are exactly the lane queries). The capacity a
single limbed quantity reaches is `29 · 8 = 232` bits — the LOW half of an `Fp` element, with lane 8
gated separately and MORE NARROWLY, which is the whole gadget. -/
theorem minaHeadAir_limbs_shape :
    minaHeadAir.limbsCount = 2 ∧ minaHeadAir.totalRangeLookups = 16
      ∧ minaHeadAir.maxLimbedCapacityBits = 232 := by
  refine ⟨rfl, rfl, rfl⟩

/-- ⚑ **THE WIRE IDS THE DESCRIPTOR COMMITS**, so the Rust reader's width recovery
(`descriptor_ir2.rs::range_bits_for`, `bits = tid − RANGE_W_TID_WIRE_BASE` with wire base 69) lands
on 29 and 22 and not on some other width. A forger cannot loosen either bound without changing these
bytes, hence the VK. -/
theorem mina_range_table_wire_ids :
    (minaRangeTid MINA_LANE_BITS).wireId = 98 ∧ (minaRangeTid MINA_TOP_LANE_BITS).wireId = 91
      ∧ TableId.range.wireId = 2 := by
  refine ⟨rfl, rfl, rfl⟩

/-- Both declared lane widths are WRAP-FREE at BabyBear, so neither lookup is the vacuous kind three
shipped descriptors were. (`RangeFieldContainment.wrap_free_iff_le_29` is the general statement; this
is it at the two widths this descriptor declares.) -/
theorem mina_lane_widths_are_wrap_free :
    Dregg2.Circuit.RangeFieldContainment.Wrapfree MINA_LANE_BITS
      ∧ Dregg2.Circuit.RangeFieldContainment.Wrapfree MINA_TOP_LANE_BITS := by
  refine ⟨?_, ?_⟩ <;>
    rw [Dregg2.Circuit.RangeFieldContainment.wrap_free_iff_le_29] <;> decide

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
theorem minaLcVerifyDesc_tables :
    minaLcVerifyDesc.tables = [minaRangeTable, minaLaneTable, minaTopLaneTable] := rfl
theorem minaLcVerifyDesc_hashSites : minaLcVerifyDesc.hashSites = [] := rfl
theorem minaLcVerifyDesc_ranges : minaLcVerifyDesc.ranges = [] := rfl

/-- The compiler emitted 49 constraints from 35 legs: one per leg, except the two `.limbs` legs which
lower to EIGHT lookups each. ⚑ A dropped lane moves this number and nothing else does — which is why
the count is pinned separately from the leg count. (`EffectLower.lowerLeg_ne_nil` is the general
statement that no leg can vanish; this is the exact arithmetic at this descriptor.) -/
theorem minaLcVerifyDesc_constraint_count : minaLcVerifyDesc.constraints.length = 49 := rfl

/-- ⚑ **THE SIXTEEN LANE LOOKUPS AND THE TWO TOP-LANE LOOKUPS, AT THEIR EMITTED POSITIONS.** `rfl` on
a slice of the compiler's output: constraints 11..18 are the anchor's low lanes at 29 bits, 19 is the
anchor's TOP lane on the NARROW table, 20..27 the tip's low lanes, 28 the tip's top lane. A leg that
lost a lane, or a top-lane query that drifted onto the wide table, moves this. -/
theorem minaLcVerifyDesc_canon_lookups :
    (minaLcVerifyDesc.constraints.drop 11).take 18 =
      [ .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (ANCHOR_STATE 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (ANCHOR_STATE 8)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 0)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 1)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 2)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 3)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 4)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 5)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 6)]⟩
      , .lookup ⟨minaRangeTid MINA_LANE_BITS, [.var (TIP_STATE 7)]⟩
      , .lookup ⟨minaRangeTid MINA_TOP_LANE_BITS, [.var (TIP_STATE 8)]⟩ ] := rfl

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
    minaLcVerifyDesc.constraints.drop 29 =
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

/-- Layout sanity, as theorems rather than guards: the two nine-lane anchors are contiguous,
disjoint and inside the declared width, and nine base-`2^29` lanes cover a 256-bit value exactly
(`8·29 + 24 = 256`). -/
theorem mina_layout_wellformed :
    ANCHOR_STATE 0 = 12 ∧ ANCHOR_STATE 8 = 20 ∧ TIP_STATE 0 = 21 ∧ TIP_STATE 8 = 29
      ∧ TIP_STATE 8 < MINA_LC_WIDTH ∧ BLOCK_LEN < ANCHOR_STATE 0
      ∧ PI_TIP_STATE 8 < PI_BLOCK_LEN ∧ PI_REQ_DEPTH < MINA_PI_COUNT
      ∧ 29 * (STATE_LIMBS - 1) + 24 = 256 := by
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

/-- ⚑ **`verifyAccepts a` — THE PRE-RUNG PREDICATE, AND IT IS KEPT ONLY AS THE FALSIFIER'S LEFT
HALF.** This is verbatim what `airAccepts` was before the canonicality legs landed: eight gate
residuals and three slack ranges, with `CANON_OK` a witnessed bit and the eighteen lane columns free.
It is NOT a compatibility surface and nothing but §7 reads it — `shifted_anchor_old_admits_new_rejects`
exhibits a row this predicate ACCEPTS and `airAccepts` REFUSES, which is the whole claim of the rung
and is unstateable without naming the thing that was refuted. -/
def verifyAccepts (a : Assignment) : Prop :=
  blockLenC.holds a
  ∧ witDepthC.holds a
  ∧ segSlackC.holds a ∧ inRange a SEG_SLACK
  ∧ anchSlackC.holds a ∧ inRange a ANCH_SLACK
  ∧ depthSlackC.holds a ∧ inRange a DEPTH_SLACK
  ∧ linkC.holds a ∧ picklesC.holds a ∧ canonC.holds a

/-- **One nine-lane state hash's canonicality legs**, as the emitted lookups denote them: the eight
low lanes in `[0, 2^29)` (the `.limbs` leg, one query per lane) and the top lane in `[0, 2^22)` (the
narrow table). -/
def laneCanon (a : Assignment) (low : List Nat) (top : Nat) : Prop :=
  LimbsInRange MINA_LANE_BITS a low
    ∧ 0 ≤ a top ∧ a top < (2 : ℤ) ^ MINA_TOP_LANE_BITS

/-- **`canonAccepts a`** — ⚑ THE DERIVED CARRIER. Both `Fp` elements this descriptor publishes are
canonical Pasta field elements, forced by eighteen lookups and no gate. -/
def canonAccepts (a : Assignment) : Prop :=
  laneCanon a anchorLowLanes (ANCHOR_STATE 8) ∧ laneCanon a tipLowLanes (TIP_STATE 8)

/-- The canonicality legs are DECIDABLE on a concrete row — so "the emitted descriptor accepts this
real devnet head" is a computation, not a sentence a reader checks by eye. -/
instance decLaneCanon (a : Assignment) (low : List Nat) (top : Nat) :
    Decidable (laneCanon a low top) := by unfold laneCanon; infer_instance

instance decCanonAccepts (a : Assignment) : Decidable (canonAccepts a) := by
  unfold canonAccepts; infer_instance

/-- **`airAccepts a`** — the emitted logic accepts row `a`: the verify arithmetic AND the derived
canonicality of the anchor and tip state hashes. -/
def airAccepts (a : Assignment) : Prop := verifyAccepts a ∧ canonAccepts a

/-- Acceptance is strictly stronger than the pre-rung predicate. (The converse is FALSE, and §7
exhibits the witness rather than asserting it.) -/
theorem airAccepts_imp_verifyAccepts {a : Assignment} (h : airAccepts a) : verifyAccepts a := h.1

/-- **THE RANGE TOOTH IS THE EMITTED ONE.** A slack column in `inRange` is exactly a column whose
singleton row is in the declared range table — so `airAccepts`'s interval is the emitted lookup's
denotation, not a second private notion of "in range". -/
theorem inRange_iff_mem_rangeRows (a : Assignment) (col : Nat) :
    inRange a col ↔ [a col] ∈ rangeRows MINA_RANGE_BITS :=
  (range_row_mem_iff (a col) MINA_RANGE_BITS).symm

/-- ⚑ **THE RANGE TOOTH IS NOT VACUOUS — the interval sits strictly inside the deployed field.**
`2^24 < p`. At 31 or 32 bits this is FALSE and the lookup refuses nothing, because every BabyBear
element is already below `2^31`. This is the whole reason `MINA_RANGE_BITS` is 24. -/
theorem mina_range_is_inside_the_field :
    (2 : ℤ) ^ MINA_RANGE_BITS < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [MINA_RANGE_BITS, Dregg2.Circuit.Emit.EffectLower.P]

/-- ⚑ **AND THE WRAP IS REFUSED.** A slack the prover wanted to be `−k` for any `0 < k ≤ 2^24` is,
in the deployed mod-`p` reading, the element `p − k` — and `p − k ≥ p − 2^24 = 1996488705`, far above
the interval ceiling. So "the slack is non-negative" is enforced with NO field-wrap escape, which is
exactly what makes G3/G4/G5 the `≤` relations they are named for.

⚠ This statement is FALSE at `MINA_RANGE_BITS = 31` (`p − 1 < 2^31`): the wrapped value would land
INSIDE the interval and every one of the three teeth would admit its own negation. -/
theorem mina_wrapped_slack_is_outside_the_range (k : ℤ) (hk : 0 < k)
    (hk' : k ≤ (2 : ℤ) ^ MINA_RANGE_BITS) :
    ¬ (0 ≤ Dregg2.Circuit.Emit.EffectLower.P - k
        ∧ Dregg2.Circuit.Emit.EffectLower.P - k < (2 : ℤ) ^ MINA_RANGE_BITS) := by
  rintro ⟨_, hlt⟩
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  have hb : ((2 : ℤ) ^ MINA_RANGE_BITS) = 16777216 := by norm_num [MINA_RANGE_BITS]
  rw [hp, hb] at hlt
  rw [hb] at hk'
  omega

/-! ## §5a — ⚑ THE CANONICALITY DERIVATION: eighteen lookups ⟹ two canonical Pasta elements.

No gate, no auxiliary column, no hash. The whole argument is that a nine-lane vector whose low eight
lanes are below `2^29` and whose top lane is below `2^22` denotes a value below `2^29·8+22 = 2^254`,
and `2^254 < p`. -/

/-- Splitting a limb vector splits its value — the one lemma the nine-lane bound needs, and it is
about `LimbTally.limbValue` rather than a private sum, so the bound below is a statement about the
quantity the `.limbs` leg denotes. -/
theorem limbValue_append (bits : Nat) (a : Assignment) :
    ∀ (l m : List Nat), limbValue bits a (l ++ m)
      = limbValue bits a l + (2 : ℤ) ^ (bits * l.length) * limbValue bits a m := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons c cs ih =>
      intro m
      have hsplit : (2 : ℤ) ^ (bits * (cs.length + 1))
          = (2 : ℤ) ^ bits * (2 : ℤ) ^ (bits * cs.length) := by
        rw [← pow_add]; ring_nf
      simp only [List.cons_append, Dregg2.Circuit.LimbTally.limbValue_cons, ih m,
        List.length_cons, hsplit]
      ring

/-- Appending the top lane is one more radix step: the nonet's value is the low half plus
`2^232 · lane₈`. -/
theorem stateValue_split (a : Assignment) (low : List Nat) (top : Nat) (hlen : low.length = 8) :
    stateValue a low top
      = limbValue MINA_LANE_BITS a low + (2 : ℤ) ^ 232 * a top := by
  have h := limbValue_append MINA_LANE_BITS a low [top]
  rw [hlen] at h
  have htop : limbValue MINA_LANE_BITS a [top] = a top := by
    simp [Dregg2.Circuit.LimbTally.limbValue]
  rw [htop] at h
  unfold stateValue nonetOf
  rw [h]
  norm_num [MINA_LANE_BITS]

/-- ⚑ **THE BOUND: the two lookup widths force the denoted `Fp` element below `2^254`.**
`8 · 29 = 232` and `232 + 22 = 254`, so the window is EXACT — a top lane one bit wider would admit
`2^255`. Both directions of the arithmetic are visible: the low half contributes at most `2^232 − 1`
(`LimbTally.limbValue_lt` at eight limbs) and the top lane at most `(2^22 − 1)·2^232`. -/
theorem laneCanon_value_bounds {a : Assignment} {low : List Nat} {top : Nat}
    (hlen : low.length = 8) (h : laneCanon a low top) :
    0 ≤ stateValue a low top ∧ stateValue a low top < (2 : ℤ) ^ 254 := by
  obtain ⟨hlow, htop0, htoplt⟩ := h
  have hsplit := stateValue_split a low top hlen
  have hlo0 : 0 ≤ limbValue MINA_LANE_BITS a low := limbValue_nonneg hlow
  have hlolt : limbValue MINA_LANE_BITS a low < (2 : ℤ) ^ 232 := by
    have := limbValue_lt hlow
    rwa [hlen, show MINA_LANE_BITS * 8 = 232 from rfl] at this
  have hpow : (0 : ℤ) < (2 : ℤ) ^ 232 := by positivity
  have htop' : a top ≤ (2 : ℤ) ^ MINA_TOP_LANE_BITS - 1 := by linarith
  have hmul : (2 : ℤ) ^ 232 * a top ≤ (2 : ℤ) ^ 232 * ((2 : ℤ) ^ MINA_TOP_LANE_BITS - 1) :=
    mul_le_mul_of_nonneg_left htop' (le_of_lt hpow)
  have hcap : (2 : ℤ) ^ 232 * (2 : ℤ) ^ MINA_TOP_LANE_BITS = (2 : ℤ) ^ 254 := by
    rw [← pow_add]; norm_num [MINA_TOP_LANE_BITS]
  constructor
  · rw [hsplit]; nlinarith
  · rw [hsplit]; nlinarith

/-- **`2^254 < p`** — the arithmetic fact the exactness rests on (`p` is a 255-bit prime just above
`2^254`; `LightClientMinaHashFold.pow254_lt_pN` is the same fact at that module's own abbreviation). -/
theorem pow254_lt_mina_p : 2 ^ 254 < pN := by decide

/-- ⚑ **THE CARRIER'S CONTENT, DERIVED.** A row satisfying the eighteen lane lookups publishes two
CANONICAL Pasta field elements. This is what the witnessed `CANON_OK` bit asserted about these two
values and what the emitted constraints now force. -/
theorem mina_lane_canon_forces_canonical {a : Assignment} {low : List Nat} {top : Nat}
    (hlen : low.length = 8) (h : laneCanon a low top) :
    0 ≤ stateValue a low top ∧ stateValue a low top < (pN : ℤ) := by
  obtain ⟨h0, hlt⟩ := laneCanon_value_bounds hlen h
  have hp : ((2 : ℕ) ^ 254 : ℤ) < (pN : ℤ) := by exact_mod_cast pow254_lt_mina_p
  push_cast at hp
  exact ⟨h0, lt_trans hlt hp⟩

/-- The two published `Fp` elements of an accepted row are canonical — the descriptor-level form. -/
theorem mina_anchor_and_tip_are_canonical {a : Assignment} (h : airAccepts a) :
    stateValue a anchorLowLanes (ANCHOR_STATE 8) < (pN : ℤ)
      ∧ stateValue a tipLowLanes (TIP_STATE 8) < (pN : ℤ) :=
  ⟨(mina_lane_canon_forces_canonical rfl h.2.1).2,
   (mina_lane_canon_forces_canonical rfl h.2.2).2⟩

/-- ⚑ **THE `+k·p` ALIAS FAMILY COLLAPSES**, at the lane encoding rather than at a `Nat`. Poseidon's
`absorbAt` enters every input through `(state + x) % p`, so the sponge cannot distinguish `v` from
`v + k·p` (`LightClientMinaHashFold.stateChain_anchor_shift_collides` turns that into an ANCHOR
SUBSTITUTION against a real devnet anchor). Under the emitted lane lookups only `k = 0` is
witnessable: one period already leaves the `2^254` window. -/
theorem mina_alias_collapses_under_lane_gates {a : Assignment} {low : List Nat} {top : Nat}
    (hlen : low.length = 8) (h : laneCanon a low top) (v : ℤ) (k : Nat) (hv : 0 ≤ v)
    (hval : stateValue a low top = v + (k : ℤ) * (pN : ℤ)) : k = 0 := by
  by_contra hk
  have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
  have hp0 : (0 : ℤ) < (pN : ℤ) := by norm_num [pN]
  have hkp : (pN : ℤ) ≤ (k : ℤ) * (pN : ℤ) := le_mul_of_one_le_left (le_of_lt hp0) hk1
  have hlt := (laneCanon_value_bounds hlen h).2
  have hp : ((2 : ℕ) ^ 254 : ℤ) < (pN : ℤ) := by exact_mod_cast pow254_lt_mina_p
  push_cast at hp
  rw [hval] at hlt
  linarith

/-- ⚑ **THE LANE LOOKUPS ARE THE EMITTED ONES.** A lane column in the acceptance predicate's interval
is exactly a column whose singleton row is in the declared table — so `canonAccepts` is the emitted
lookups' denotation and not a second private notion of "in range". -/
theorem lane_in_table_iff (a : Assignment) (col : Nat) :
    (0 ≤ a col ∧ a col < (2 : ℤ) ^ MINA_LANE_BITS) ↔ [a col] ∈ rangeRows MINA_LANE_BITS :=
  (range_row_mem_iff (a col) MINA_LANE_BITS).symm

/-- …and the same for the narrow top-lane table. -/
theorem top_lane_in_table_iff (a : Assignment) (col : Nat) :
    (0 ≤ a col ∧ a col < (2 : ℤ) ^ MINA_TOP_LANE_BITS) ↔ [a col] ∈ rangeRows MINA_TOP_LANE_BITS :=
  (range_row_mem_iff (a col) MINA_TOP_LANE_BITS).symm

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
  obtain ⟨hbl, hwd, hss, ⟨hss0, _⟩, has, ⟨has0, _⟩, hds, ⟨hds0, _⟩, hlkC, hpkC, hcnC⟩ := hacc.1
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
  simp only [hlk', hpk', hcn', Bool.and_eq_true, decide_eq_true_eq, Bool.and_true]
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
their genuine values satisfies `airAccepts` — given that the heights fit the declared 24-bit interval
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
    (hcanon : canonAccepts a)
    (hdecT : minaVerifyDecision segLen anchorH submitH (anchorH + segLen - submitH) reqDepth
      linkB picklesB canonB = true) :
    airAccepts a := by
  refine ⟨?_, hcanon⟩
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

/-- A row from its column values, index-ordered from `SEG_LEN`. A list shorter than the trace width
reads `0` above its end — the four LOGIC refusals below leave the lane columns at `0` (which is a
canonical `Fp` element, so they are refused by the logic and not incidentally by the lane gates). -/
def rowOf (vs : List ℤ) : Assignment := fun w => vs.getD w 0

/-- The base-`2^29` lanes of Mina devnet **genesis**'s state hash
`3NL93SipJfAMNDBRfQ8Uo8LPovC74mnJZfZYB5SK7mTtkL72dsPx` — the natural weak-subjectivity anchor for a
devnet light client. ⚑ Provenance: `LightClientMinaHashFold.DEVNET_GENESIS_STATE_HASH`, itself a
Base58Check decode with a VERIFIED checksum that `bridge/src/mina_observer.rs::decode_state_hash`
reproduces. `honest_anchor_lanes_decode_the_devnet_genesis` pins the recomposition against that
decimal, so these nine digits are a GATE on the decode and not a transcription. -/
def GENESIS_ANCHOR_LANES : List ℤ :=
  [317368465, 122552485, 518650043, 481937944, 112457995, 488503206, 390747624, 350427965, 1320595]

/-- The lanes of devnet block **539508**'s state hash — the block whose Wrap proof o1-labs'
`kimchi::verifier::verify` accepts (`MinaRealBlockGate`). Used as the verified TIP. -/
def DEVNET_TIP_LANES : List ℤ :=
  [148400356, 2288994, 332868807, 237767070, 530455789, 507531490, 336317945, 425818875, 3793778]

/-- ⚑ **THE SHIFTED ANCHOR'S LANES** — the SAME devnet genesis anchor plus ONE Pasta modulus. This is
the input `LightClientMinaHashFold.stateChain_anchor_shift_collides` proves chains to the IDENTICAL
tip state hash, i.e. the anchor substitution the Poseidon sponge's `(state + x) % p` absorb permits.
`shifted_anchor_is_the_genesis_plus_p` proves the `+p` relation rather than asserting it. -/
def SHIFTED_ANCHOR_LANES : List ℤ :=
  [317368466, 280463373, 304627617, 166445611, 112458544, 488503206, 390747624, 350427965, 5514899]

/-- The twelve logic-column values shared by the honest row and the shifted-anchor row: anchor pinned
at height 1000; 300 exhibited, linked, proof-carrying blocks; the settlement submitted at 1010;
Samasika `k = 290`. Derived tip 1300, derived witnessed depth 290 — the requirement met exactly. ⚑ All
three carriers, INCLUDING `CANON_OK`, read `1`. -/
def honestLogicCols : List ℤ := [300, 1000, 1010, 290, 290, 299, 10, 0, 1, 1, 1, 1300]

/-- **THE HONEST ROW** — the logic columns above, the pinned anchor's nine lanes, the verified tip's
nine lanes. ACCEPTED. -/
def honestRow : Assignment := rowOf (honestLogicCols ++ GENESIS_ANCHOR_LANES ++ DEVNET_TIP_LANES)

/-- ⚑ **THE SHIFTED-ANCHOR ROW** — byte-for-byte the honest row except that the pinned anchor's lanes
are the `+p` alias. Every gate holds, every slack is in range, and every carrier bit reads `1`. -/
def shiftedAnchorRow : Assignment :=
  rowOf (honestLogicCols ++ SHIFTED_ANCHOR_LANES ++ DEVNET_TIP_LANES)

/-- The row's logic columns, unfolded — shared by every §7 proof so the `List.getD` walk happens
once per column rather than once per theorem. -/
private theorem honest_verify_cols :
    verifyAccepts honestRow ∧ verifyAccepts shiftedAnchorRow := by
  constructor <;>
  · refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;>
      simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
        depthSlackC_holds_iff, linkC_holds_iff, picklesC_holds_iff, canonC_holds_iff,
        honestRow, shiftedAnchorRow, honestLogicCols, GENESIS_ANCHOR_LANES, SHIFTED_ANCHOR_LANES,
        DEVNET_TIP_LANES, rowOf,
        SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
        DEPTH_SLACK, LINK_OK, PICKLES_OK, CANON_OK, BLOCK_LEN, MINA_RANGE_BITS, List.getD,
        List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
      norm_num

/-- ⚑ **THE HONEST ROW IS ACCEPTED — on real devnet lanes.** The verify arithmetic AND the eighteen
canonicality lookups. Without this the rung would be satisfied by a descriptor that refuses
everything, and the two real state hashes are exactly the values the gate must not refuse. -/
theorem honest_row_accepted : airAccepts honestRow :=
  ⟨honest_verify_cols.1, by decide⟩

/-- The honest anchor's nine lanes recompose to the devnet genesis state hash — the decimal
`LightClientMinaHashFold.DEVNET_GENESIS_STATE_HASH` records and `bridge/src/mina_observer.rs` decodes.
Two independent spellings of one value; a drift in either goes red here. -/
theorem honest_anchor_lanes_decode_the_devnet_genesis :
    stateValue honestRow anchorLowLanes (ANCHOR_STATE 8)
      = 9114416221768123787477325283664893678899335531281108607736543138013422200977 := by
  decide

/-- …and the verified tip's lanes recompose to devnet block 539508's state hash. -/
theorem honest_tip_lanes_decode_the_devnet_block :
    stateValue honestRow tipLowLanes (TIP_STATE 8)
      = 26183698926150821166089117776323498226609958862529648923082869093695686732004 := by
  decide

/-- ⚑ **THE FORGED ANCHOR IS THE HONEST ONE PLUS EXACTLY ONE PASTA MODULUS.** Proved on the lane
vectors, so "this is the `+p` alias" is arithmetic rather than a claim in a comment. -/
theorem shifted_anchor_is_the_genesis_plus_p :
    stateValue shiftedAnchorRow anchorLowLanes (ANCHOR_STATE 8)
      = stateValue honestRow anchorLowLanes (ANCHOR_STATE 8) + (pN : ℤ) := by
  decide

/-- ⚑ **REFUSED — A LOSING FORK.** The same pinned anchor and the same submitted height, but only 295
exhibited blocks against the honest 300: derived tip 1295, derived depth 285, five short of `k = 290`.
The prover fills every column honestly, so every GATE holds; `DEPTH_SLACK = −5` is outside `[0, 2^24)`
and the range lookup has no satisfying table row.

⚑ This is the shallower branch of a genuine disagreement refused by the DESCRIPTOR, not by an
off-chain comparison. -/
def losingForkRow : Assignment := rowOf [295, 1000, 1010, 285, 290, 294, 10, -5, 1, 1, 1, 1295]

theorem losing_fork_refused : ¬ airAccepts losingForkRow := by
  intro h
  have hds0 := h.1.2.2.2.2.2.2.2.1.1
  simp only [losingForkRow, rowOf, DEPTH_SLACK, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at hds0
  norm_num at hds0

/-- ⚑ **REFUSED — A BENT PROOF WORD.** Every height, depth and slack is the honest row's; only the
Pickles carrier is `0`, which is what a block whose Wrap proof fails to verify AT ITS OWN state hash
produces. The `PICKLES_OK = 1` gate refuses it. -/
def bentProofRow : Assignment := rowOf [300, 1000, 1010, 290, 290, 299, 10, 0, 1, 0, 1, 1300]

theorem bent_proof_word_refused : ¬ airAccepts bentProofRow := by
  intro h
  have hpk := h.1.2.2.2.2.2.2.2.2.2.1
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
  have hbl := h.1.1
  rw [blockLenC_holds_iff] at hbl
  simp only [forgedHeightRow, rowOf, BLOCK_LEN, ANCHOR_H, SEG_LEN, List.getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] at hbl
  norm_num at hbl

/-- ⚑ **REFUSED — THE DEPLOYED OBSERVER'S OWN ARITHMETIC.**
`LightClientMina.witnessedDepth_unbounded_without_anchor_bound` exhibits the wound as a theorem: with
the anchor at 1000 and the submitted height at 0, a ONE-BLOCK segment "witnesses" depth 1001, and
`mina_observer::observe_settlement`'s `tip_height.saturating_sub(submitted_height)` accepts it.

Here `ANCH_SLACK = SUBMIT_H − ANCHOR_H = −1000` is outside `[0, 2^24)`. The descriptor refuses the
deployed observer's own accepting input. -/
def unanchoredRow : Assignment := rowOf [1, 1000, 0, 1001, 290, 0, -1000, 711, 1, 1, 1, 1001]

theorem observer_arithmetic_refused : ¬ airAccepts unanchoredRow := by
  intro h
  have has0 := h.1.2.2.2.2.2.1.1
  simp only [unanchoredRow, rowOf, ANCH_SLACK, List.getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some] at has0
  norm_num at has0

/-- ⚑⚑ **REFUSED — THE ANCHOR SUBSTITUTION, AND THIS IS THE RUNG.** The pinned weak-subjectivity
anchor is the real devnet genesis hash PLUS ONE PASTA MODULUS
(`shifted_anchor_is_the_genesis_plus_p`), which `LightClientMinaHashFold.stateChain_anchor_shift_collides`
proves chains to the IDENTICAL tip state hash — so the forger presents a genuine-looking segment under
an anchor nobody pinned, and every Poseidon step agrees.

Its top lane is `5514899`: BELOW `2^24`, so it is a perfectly legal nine-lane encoding of a 32-byte
string and the `Faithful9`/`KeyLanes9` nonet gate admits it. It is refused ONLY by the 22-bit
top-lane table — the one leg that separates "well-formed nonet" from "canonical Pasta element". -/
theorem shifted_anchor_refused : ¬ airAccepts shiftedAnchorRow := by
  intro h
  have htop := h.2.1.2.2
  revert htop
  decide

/-- ⚑⚑⚑ **OLD ADMITS, NEW REJECTS — the rung stated as one theorem.** The very same row that the
PRE-RUNG predicate ACCEPTS (`verifyAccepts`: every gate, every slack, and `CANON_OK` witnessed `1` by
a prover who simply set it) is REFUSED by the emitted descriptor. Nothing about the row changed; the
carrier stopped being a bit somebody wrote down.

This is the object the whole `PICKLES_OK`/`LINK_OK`/`CANON_OK` question is about, at the one carrier
whose content the descriptor's own columns can express. -/
theorem shifted_anchor_old_admits_new_rejects :
    verifyAccepts shiftedAnchorRow ∧ ¬ airAccepts shiftedAnchorRow :=
  ⟨honest_verify_cols.2, shifted_anchor_refused⟩

/-- ⚑ **AND THE REFUSAL IS THE NARROW TABLE'S, NOT THE ENCODER'S.** The forged top lane passes the
32-byte nonet width (`< 2^24`, `KeyLanes9.KTOP`) and fails the Pasta-canonical width (`< 2^22`), while
the honest anchor's passes both. So the 22-bit leg is load-bearing and the 24-bit one would have been
decoration — `MINA_TOP_LANE_BITS` is not a free parameter. -/
theorem the_top_lane_width_is_load_bearing :
    shiftedAnchorRow (ANCHOR_STATE 8) < (2 : ℤ) ^ 24
      ∧ ¬ (shiftedAnchorRow (ANCHOR_STATE 8) < (2 : ℤ) ^ MINA_TOP_LANE_BITS)
      ∧ honestRow (ANCHOR_STATE 8) < (2 : ℤ) ^ MINA_TOP_LANE_BITS := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- ⚑ **THE POLARITY PAIR, AS ONE STATEMENT.** The emitted logic DISCRIMINATES: it accepts the honest
anchored head on REAL devnet lanes and refuses all five forgery shapes. A descriptor that accepted
everything, or refused everything, fails this. -/
theorem mina_air_discriminates :
    airAccepts honestRow
      ∧ ¬ airAccepts losingForkRow
      ∧ ¬ airAccepts bentProofRow
      ∧ ¬ airAccepts forgedHeightRow
      ∧ ¬ airAccepts unanchoredRow
      ∧ ¬ airAccepts shiftedAnchorRow :=
  ⟨honest_row_accepted, losing_fork_refused, bent_proof_word_refused, forged_height_refused,
   observer_arithmetic_refused, shifted_anchor_refused⟩

/-! ## §8 — axiom hygiene, on the canonicality rung's load-bearing facts. -/

#assert_axioms limbValue_append
#assert_axioms stateValue_split
#assert_axioms laneCanon_value_bounds
#assert_axioms pow254_lt_mina_p
#assert_axioms mina_lane_canon_forces_canonical
#assert_axioms mina_anchor_and_tip_are_canonical
#assert_axioms mina_alias_collapses_under_lane_gates
#assert_axioms mina_lane_widths_are_wrap_free
#assert_axioms honest_row_accepted
#assert_axioms honest_anchor_lanes_decode_the_devnet_genesis
#assert_axioms shifted_anchor_is_the_genesis_plus_p
#assert_axioms shifted_anchor_refused
#assert_axioms shifted_anchor_old_admits_new_rejects
#assert_axioms the_top_lane_width_is_load_bearing
#assert_axioms mina_air_discriminates
#assert_axioms minaLcAir_sound
#assert_axioms minaLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientMinaAir
