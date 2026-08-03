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

## ⚑ THE TALLY REPAIR (2026-08-03): SOLANA'S STAKE NEVER FIT A COLUMN, AT ANY DECLARED WIDTH

This descriptor shipped `bits: 128` on its range table. Over BabyBear (`p = 2013265921 < 2^31 < 2^128`)
**every field element was already in the declared interval**, so both lookups refused NOTHING
(`RangeFieldContainment.range_vacuous_at_or_above_31`). Narrowing to 29 — the maximum wrap-free width
— bought the teeth back, and in doing so it EXPOSED the limit the vacuous width had been hiding:
`ROOTED_STK` and `TOTAL_STK` were ONE COLUMN EACH, and one BabyBear felt holds 30.9 bits.

⚑ **MEASURED LIVE, 2026-08-03**, `getVoteAccounts` on `api.mainnet-beta.solana.com` (epoch 1011, slot
436,909,708; 689 current + 14 delinquent vote accounts): mainnet-beta ACTIVE stake is

    432,650,183,925,625,587 lamports  =  432.650M SOL  =  2^58.586

and `getSupply` puts total supply at 631,503,420,149,974,995 lamports (2^59.13) — re-sampled from the
same endpoint while authoring this file and agreeing to eight significant figures (631,503,394,549,607,495,
a drift of ~26 SOL over the intervening minutes), which is the corroboration the headline number gets.
The wire type is `u64`. **None of that ever fit a column** — not at 128 bits, not at 29, not at any
width, because a width declares an INTERVAL and the wire is one field element. The 128-bit declaration
did not make the tally fit; it made the shortfall invisible, and the 29-bit repair made it VISIBLE and
no smaller.

Both tallies are now **four 16-bit limbs each, LEAST-significant first — exactly a `u64`**. The
arithmetic, its soundness and its refusal live in `Dregg2.Circuit.LimbTally`; this file instantiates
that theory twice and GENERATES the gates from it.

## ⚑ THE FIDELITY NOTE: THE REFERENCE IMPLEMENTATION COMPARES A FLOAT RATIO

agave's threshold constant is `pub const VOTE_THRESHOLD_SIZE: f64 = 2f64 / 3f64;`
(`runtime/src/commitment.rs:9`, read at source 2026-08-03), and the comparison it drives is
`(*stake as f64 / total_stake as f64) > self.threshold_size` (`core/src/consensus.rs`,
`Tower::is_slot_confirmed`, line 1041 on master at that date). **That is a float ratio, and a circuit
cannot evaluate it** — so the integer form is a choice this AIR makes, and saying which choice is part
of the fidelity claim rather than a decoration:

  * `2f64 / 3f64` is the double `0.666666666666666629659…`, which is strictly BELOW 2/3. So agave's
    STRICT `>` against it already admits ratios that a strict `> 2/3` would reject.
  * At live scale the operands are not even representable: `432650183925625587` as `f64` is
    `432650183925625600` — 13 lamports off, with a 64-lamport ULP at 2^58. agave's threshold is
    accurate to about a ULP there.

This AIR carries the **NON-STRICT** integer form `3·rooted ≥ 2·total` (`solVerifyDecision`'s
`2 * totalStk ≤ 3 * rootedStk`), i.e. chain parameters `α = 3, β = 2, γ = 0`. It is UNCHANGED by this
work — the strictness is the existing semantics, and the two bullets above are why non-strict is the
defensible reading of a float comparison against a double that sits below the true ratio, not a
loosening. ⚠ It is still NOT a bit-for-bit model of agave's float arithmetic; nothing in a prime field
is.

## The crypto boundary: IN-AIR logic vs NAMED verified carriers

  * IN-AIR (arithmetic gates over the trace — the stake TALLY logic, the Nomad-class bug locus):
      - the ≥2/3 supermajority `3·rooted ≥ 2·total` as a LIMBED comparison: four rungs of an offset
        carry chain over the two `u64` limb vectors, five range-checked difference limbs, `α = 3,
        β = 2, γ = 0`;
      - the `EmptyStakeTable` floor `total ≥ 1` as a SECOND limbed chain over the SAME total-stake
        limb vector, `α = 1, β = 0, γ = 1`;
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

## ⚑ WHAT THE EMPTY-STAKE-TABLE FLOOR COST, AND WHY ITS NEW REFUSAL IS BETTER

`TPOS = TOTAL_STK − 1 ≥ 0` is the `EmptyStakeTable` floor, and it is the check that FAILED. At
`TOTAL_STK = 0` the slack filled to `−1`, which in the deployed mod-`p` reading rides as
`p − 1 = 2013265920`, and the 128-bit table CONTAINED it. **The empty stake table passed its own
emptiness floor** — and with `ROOTED_STK = TOTAL_STK = 0` the quorum slack `3·0 − 2·0 = 0` passed too,
so a block signed by nobody satisfied both teeth.

The 29-bit narrowing refused it because `p − 1 ∉ [0, 2^29)`: a fact about the FIELD SIZE, false at 30
and catastrophically false at the 128 that shipped. The limbed floor refuses it because a limb vector
of non-negative limbs denotes a non-negative value and `1 ≤ 0` is false — a fact about limb vectors,
true at EVERY width in EVERY field (`solLcAir_refuses_the_empty_stake_table`,
`sol_empty_stake_refusal_is_field_independent`). Widening the representable tally by 2^33× does not
re-admit it; it removes the field size from the refusal's premises.

## The two declared range tables, and the one that is GONE

The tally rides at 16 bits and its carries at 8, on WIDTH-TAGGED CUSTOM tables (`.custom (64 + b)`,
wire ids 85 and 77) — the same mechanism the deployed availability-weld uses for its 15-bit borrow
limbs. Rust resolves each lookup's width from the DECLARED table (`descriptor_ir2.rs`
`range_bits_for`), realizes every width as the same byte-limb decomposition, and shares ONE byte table
across all of them.

⚑ **The 29-bit `range` table (wire id 2) is NO LONGER DECLARED.** It carried exactly two lookups —
`QDIFF` and `TPOS` — and BOTH are now limbed chains, so nothing queries it. Declaring a table no
constraint reads is a table whose width nothing checks; it is dropped rather than left standing.
`RANGE_BITS` survives only as the subject of the HISTORICAL record theorems in §3b (the value the
128-bit table admitted and the 29-bit table refused), and `sol_range_table_is_not_declared` is the
tripwire that reds if a felt-width slack is ever re-introduced.

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
(named residual, identical to the ETH slice, UNCHANGED by the tally work): the anchors are published
but not yet arithmetically bound to the carrier bits (that binding IS the in-AIR-crypto iteration —
`ED_OK` derived from the vote message built on `BANK_ROOT`+`SLOT`, `STAKE_TABLE_OK` derived from the
table fold into `ANCHOR_ROOT`).

## The mod-p ↔ ℤ reading

`airAccepts` reads the emitted gate bodies as ℤ equalities and the limb lookups as ℤ intervals. For the
CHAIN gates that bridge is DISCHARGED rather than named — but ⚠ **at THIS AIR's constants, not by
citing a sibling's**. `LimbTally.rung_no_alias_at_deployed_constants` is stated at `α = 3, β = 2,
γ = 1` (Tendermint's STRICT threshold); neither of Solana's chains has those constants. So the two
instances are proved here, from the parametric `LimbTally.rung_value_bounds`:
`sol_qdiff_rung_no_alias` (`α = 3, β = 2, γ = 0`) and `sol_tpos_rung_no_alias` (`α = 1, β = 0,
γ = 1`). Each bounds every rung gate's ℤ value, on any assignment respecting the DECLARED ranges,
strictly inside `(−p, p)` — so `body ≡ 0 (mod p)` IS `body = 0` over ℤ there, and §3's recomposition
transfers to the deployed denotation. `LimbTally.rung_alias_reachable_at_24_bits` exhibits a reachable
failure eight bits above the deployed limb width, so the constant has a measured margin AND a measured
failure point.

## What this file BREAKS (say the flag day out loud)

Trace width `19 → 41`, constraints `19 → 51`, declared tables `[range@29] → [range_w16, range_w8]`,
and the emitted descriptor bytes therefore change — so `dregg-solana-lightclient-verify::v1`'s VK
ROTATES and `circuit/descriptors/by-name/dregg-solana-lightclient-verify-v1.json` is RE-EMITTED. Any
Rust witness filler for this descriptor must now fill limb vectors and two carry chains instead of two
felt slacks; the old 19-column row REFUSES to satisfy the new descriptor (its columns are not even the
same quantities). Nothing else in the tree consumes this AIR yet.

## Axiom hygiene
Definitional descriptor + non-vacuous per-gate `iff` lemmas (`omega`) + the load-bearing
`solLcAir_sound` / `solLcAir_no_forgery` refinement to `solVerifyDecision` / `sol_no_forgery`.
`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. Imports read-only.
-/
import Dregg2.Circuit.DescriptorIR2
import Dregg2.Circuit.RangeFieldContainment
import Dregg2.Circuit.LimbTally
import Dregg2.Bridge.LightClientSolana

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Dregg2.Circuit.Emit.LightClientSolanaAir

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 Lookup TableId rangeTableDef emitVmJson2 rangeRows
   range_row_mem_iff)
open Dregg2.Bridge.LightClientSolana

/-! ## §1 — the trace column layout (one logical row).

Columns 0..3 are the four boolean carrier/gate projections `solVerifyDecision` composes over.
Columns 4..29 are the TALLY BLOCK: the two `u64` stake vectors as four 16-bit limbs each, and the two
comparison chains (five difference limbs + four offset carries apiece). Columns 30..40 are the
published PUBLIC anchors: `ANCHOR_ROOT` (30), the NINE bank-root limbs `BANK_ROOT 0..8` (cols 31..39 —
the full 256-bit bank hash, radix-`2^31`, MSB-first), and `SLOT_COL` (40). -/

/-- **CARRIER** — the aggregate ed25519 verify RESULT (counted authorized voters signed the bank hash at
the slot); forced `= 1`. NAMED verified-FFI carrier. Witness. -/
def ED_OK : Nat := 0
/-- **CARRIER** — the stake-table-root compare RESULT (derived table binds the pinned WS anchor root);
forced `= 1`. NAMED carrier (the HOLE-2 denominator pin). Witness. -/
def STAKE_TABLE_OK : Nat := 1
/-- **GATE** — the ROOTED flag (every counted vote's tower root reaches the slot — HOLE-1); forced `= 1`. -/
def ROOTED_OK : Nat := 2
/-- **GATE** — the AUTHORIZED-voter binding (every counted signer is the on-chain authorized voter —
BR-2-A); forced `= 1`. -/
def AUTH_OK : Nat := 3

/-! ### ⚑ THE STAKE TALLIES, AS LIMB VECTORS — the capability this AIR did not have.

`ROOTED_STK` and `TOTAL_STK` used to be ONE COLUMN EACH. A column is one BabyBear felt and a felt holds
30.9 bits, so the deployed client could not represent mainnet-beta's active stake at all: measured live
2026-08-03, `432650183925625587` lamports = 2^58.586, which is 214.9 MILLION times the modulus. The
128-bit range declaration did not make that fit; it made the shortfall invisible, and the 29-bit repair
that closed the vacuity made it VISIBLE and no smaller.

They are now **four 16-bit limbs each, LEAST-significant first — exactly a `u64`**, which is exactly
Solana's own wire type for lamport stake. -/

/-- The tally limb width. `SOL_TALLY_LIMBS · SOL_LIMB_BITS = 64`. -/
def SOL_LIMB_BITS : Nat := LimbTally.TALLY_LIMB_BITS
/-- The number of tally limbs — four 16-bit limbs are a `u64`. -/
def SOL_TALLY_LIMBS : Nat := LimbTally.TALLY_LIMBS
/-- The carry width for the difference chains (the prover's own byte bus). -/
def SOL_CARRY_BITS : Nat := LimbTally.TALLY_CARRY_BITS

/-- **Limb `i` of the total ACTIVE stake** (`total_stake()`, the 2/3 denominator), LSB-first.
Columns 4..7. Witness. -/
def TOTAL_STK_LIMB (i : Nat) : Nat := 4 + i
/-- **Limb `i` of the counted rooted authorized voting stake** (`voted_stake`), LSB-first.
Columns 8..11. Its ed25519 provenance is the `ED_OK` carrier. Witness. -/
def ROOTED_STK_LIMB (i : Nat) : Nat := 8 + i

/-- **Limb `i` of the QUORUM difference `3·rooted − 2·total`**, LSB-first. FIVE limbs (columns
12..16), one more than the operands: `3·A` needs two bits beyond `A`. Every limb carries its own
16-bit range lookup, and THAT is the quorum tooth — a limb vector of non-negative limbs denotes a
non-negative value, so a sub-quorum (whose difference is negative) has no representation at all. -/
def QDIFF_LIMB (i : Nat) : Nat := 12 + i
/-- **Offset carry `i` of the quorum chain** (columns 17..20); denotes `col − 128`, since a difference
chain BORROWS and a field wire has no sign. Range-checked at 8 bits for the mod-`p` bridge ONLY —
`LimbTally.chain_recomposes` needs no bound on it whatsoever. -/
def QDIFF_CARRY (i : Nat) : Nat := 17 + i

/-- **Limb `i` of the EMPTY-STAKE-TABLE floor difference `total − 1`**, LSB-first. FIVE limbs
(columns 21..25) — the generator emits `k + 1` difference limbs for `k` rungs regardless of `α`, and
at `α = 1` the top limb is simply always zero on an honest fill. -/
def TPOS_LIMB (i : Nat) : Nat := 21 + i
/-- **Offset carry `i` of the floor chain** (columns 26..29). -/
def TPOS_CARRY (i : Nat) : Nat := 26 + i

/-- **PUBLIC ANCHOR** — the pinned WS stake-table root (the governance trust anchor). PI-bound. -/
def ANCHOR_ROOT : Nat := 30

/-- The number of ~31-bit limbs the FULL 256-bit rooted bank hash is exposed as: `⌈256 / 31⌉ = 9`.
Eight 31-bit limbs cover 248 bits; the ninth (most-significant) limb carries the remaining 8 bits.
This is the felt-width close — a SINGLE anchor felt bound only a 31-bit PROJECTION of the 256-bit bank
hash (two roots agreeing in 31 bits both verified); nine limbs bind the WHOLE root. -/
def BANK_ROOT_LIMBS : Nat := 9

/-- **PUBLIC ANCHOR (limb `i`)** — the claimed rooted bank/state root B as its radix-`2^31`,
MOST-SIGNIFICANT-limb-first decomposition. Limb `i` is trace column `31 + i` (cols 31..39); limb `0` is
the MSB (its top carries only 8 bits). PI-bound to slot `1 + i`, so the peer-wrap's radix-`2^31`
MSB-first pack over `PI[1..9]` recomposes the 256-bit bank hash exactly before its 128-bit split. -/
def BANK_ROOT (i : Nat) : Nat := 31 + i

/-- **PUBLIC ANCHOR** — the rooted slot S (epoch/slot). PI-bound. -/
def SLOT_COL : Nat := 31 + BANK_ROOT_LIMBS

/-- Total main-trace width: 4 carrier/gate columns + 4 total-stake limbs + 4 rooted-stake limbs +
5 quorum-difference limbs + 4 quorum carries + 5 floor-difference limbs + 4 floor carries +
1 anchor-root + 9 bank-root limbs + 1 slot anchor = 41.

⚑ It was 19. The +22 is the tally becoming REPRESENTABLE: two `u64` operands and TWO comparison
chains (the quorum and the emptiness floor), each with its own difference vector and borrow chain.
That is what mainnet-beta's stake costs in columns, and it is the honest price of the capability —
the previous 19 bought a client that could not hold it. -/
def SOL_LC_WIDTH : Nat := 41

/-- PI slot 0: the pinned WS anchor root. -/
def PI_ANCHOR_ROOT : Nat := 0
/-- PI slot of bank-root limb `i` (slots 1..9), MSB-first. -/
def PI_BANK_ROOT (i : Nat) : Nat := 1 + i
/-- PI slot of the rooted slot (slot 10). -/
def PI_SLOT : Nat := 1 + BANK_ROOT_LIMBS
/-- Number of public inputs: anchor root + 9 bank-root limbs + slot. -/
def PI_COUNT : Nat := 11

/-- ⚑ **THE HISTORICAL FELT-SLACK WIDTH — NO LONGER DECLARED BY THIS DESCRIPTOR.**

This was `128` (the `u128` width the Rust `is_supermajority` tally uses — a number that describes the
WIRE and says nothing about the domain the constraint is evaluated in), then `29` (the maximum
wrap-free width at BabyBear, `RangeFieldContainment.wrap_free_iff_le_29`). It is now the subject of the
RECORD theorems in §3b and NOTHING ELSE: both slacks that queried the `range` table are limbed chains,
so the descriptor declares no table at this width (`sol_range_table_is_not_declared`).

Kept rather than deleted because the pair it names — `p − 1` ADMITTED at 128, REFUSED at 29 — is the
measurement that made the narrowing a repair, and the limbed refusal that superseded it is only
legible against it. -/
def RANGE_BITS : Nat := 29

/-! ## §2 — the emitted gate bodies (the descriptor's OWN constraint polynomials).

### ⚑ The two comparisons, GENERATED rather than transcribed.

`LightClientMinaAir` set the bar — `EffectLower.lowerAir`-authored, no hand-written `VmConstraint2`.
Each comparison used to be ONE hand-written gate body plus ONE lookup, because a single-felt slack is
one gate. A limbed comparison is five gates and between nine and seventeen lookups (five difference
limbs, four carries, plus whichever operand limbs a sibling chain has not already checked), and
hand-writing those would be exactly the drift House Law #1 exists to stop.

`LimbTally.chainBodies` GENERATES them from the rung list, and `LimbTally.chainBodies_zero_iff` ties
what it generates back to `ChainOk` — so §5's soundness is about the bodies that ship. -/

/-- **The four rungs of the QUORUM difference chain**, LSB-first: at radix position `i` the
rooted-stake limb (the `α = 3` operand), the total-stake limb (the `β = 2` operand), the difference
limb and the offset carry out.

Written as an explicit literal (rather than `List.range`-mapped) so the byte-golden `#guard` reduces to
the exact wire string with no fold — the same discipline `bankRootPins` follows. -/
def qdiffRungs : List LimbTally.Rung :=
  [ ⟨ROOTED_STK_LIMB 0, TOTAL_STK_LIMB 0, QDIFF_LIMB 0, QDIFF_CARRY 0⟩
  , ⟨ROOTED_STK_LIMB 1, TOTAL_STK_LIMB 1, QDIFF_LIMB 1, QDIFF_CARRY 1⟩
  , ⟨ROOTED_STK_LIMB 2, TOTAL_STK_LIMB 2, QDIFF_LIMB 2, QDIFF_CARRY 2⟩
  , ⟨ROOTED_STK_LIMB 3, TOTAL_STK_LIMB 3, QDIFF_LIMB 3, QDIFF_CARRY 3⟩ ]

/-- The quorum difference vector's TOP limb — the chain's closure column. -/
def QDIFF_TOP : Nat := QDIFF_LIMB 4

/-- **The four rungs of the EMPTY-STAKE-TABLE FLOOR chain**, LSB-first, over the SAME total-stake limb
vector the quorum chain reads as its `β` operand.

⚠ **`bCol` POINTS AT `aCol` ON PURPOSE — this is not a copy-paste bug.** `LimbTally.Rung` carries a
`bCol` field at every rung because the general comparison is `α·A − β·B − γ`. Here `β = 0`, so the
emitted term is literally `.mul (.const 0) (.var (TOTAL_STK_LIMB i))` — a constant-zero factor, whose
value is zero whatever column it names — and `LimbTally.cmp_sound`'s conclusion is
`γ ≤ α·A − 0·B = α·A`. Pointing it at the total-stake limb costs nothing and needs no dedicated
zero column, which a fresh column would have had to be pinned to zero by yet another gate. -/
def tposRungs : List LimbTally.Rung :=
  [ ⟨TOTAL_STK_LIMB 0, TOTAL_STK_LIMB 0, TPOS_LIMB 0, TPOS_CARRY 0⟩
  , ⟨TOTAL_STK_LIMB 1, TOTAL_STK_LIMB 1, TPOS_LIMB 1, TPOS_CARRY 1⟩
  , ⟨TOTAL_STK_LIMB 2, TOTAL_STK_LIMB 2, TPOS_LIMB 2, TPOS_CARRY 2⟩
  , ⟨TOTAL_STK_LIMB 3, TOTAL_STK_LIMB 3, TPOS_LIMB 3, TPOS_CARRY 3⟩ ]

/-- The floor difference vector's TOP limb — the chain's closure column. -/
def TPOS_TOP : Nat := TPOS_LIMB 4

/-- The emitted QUORUM gate bodies: `α = 3` on rooted stake, `β = 2` on total stake, `γ = 0` for
Solana's NON-STRICT `≥ 2/3` (contrast Tendermint's `γ = 1`). Five bodies from four rungs (one per rung
plus the closure gate). -/
def qdiffChainBodies : List EmittedExpr :=
  LimbTally.chainBodies SOL_LIMB_BITS 3 2 0 LimbTally.TALLY_CARRY_OFF QDIFF_TOP qdiffRungs

/-- The emitted FLOOR gate bodies: `α = 1`, `β = 0`, `γ = 1` — i.e. `total − 1 ≥ 0`, the
`EmptyStakeTable` refusal. Five bodies from four rungs. -/
def tposChainBodies : List EmittedExpr :=
  LimbTally.chainBodies SOL_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs

/-- `ED_OK − 1` — zero iff the ed25519 carrier bit is set. -/
def edBody : EmittedExpr := .add (.var ED_OK) (.const (-1))
/-- `STAKE_TABLE_OK − 1` — zero iff the stake-table-root carrier bit is set. -/
def stakeBody : EmittedExpr := .add (.var STAKE_TABLE_OK) (.const (-1))
/-- `ROOTED_OK − 1` — zero iff the rooted-flag gate bit is set. -/
def rootedBody : EmittedExpr := .add (.var ROOTED_OK) (.const (-1))
/-- `AUTH_OK − 1` — zero iff the authorized-voter-binding gate bit is set. -/
def authBody : EmittedExpr := .add (.var AUTH_OK) (.const (-1))

/-! ## §3 — the constraint list + descriptor.

### The two declared range tables, and the one that is gone.

The tally rides at 16 and its carries at 8, on WIDTH-TAGGED CUSTOM tables (`.custom (64 + b)`), which
is the mechanism the deployed availability-weld already uses for its 15-bit borrow limbs. The shared
`range` table at `RANGE_BITS` is NOT declared: both of its former lookups are limbed chains now, and a
declared table no constraint reads is a width nothing checks. -/

/-- The tally-limb range table: wire id `5 + 64 + 16 = 85`. -/
def TID_TALLY_LIMB : TableId := .custom (64 + SOL_LIMB_BITS)
/-- The chain-carry range table: wire id `5 + 64 + 8 = 77`. -/
def TID_TALLY_CARRY : TableId := .custom (64 + SOL_CARRY_BITS)

/-- ⚑ **THE TEETH: one range lookup PER LIMB, on BOTH chains.**

Eighteen 16-bit lookups (four total-stake limbs, four rooted-stake limbs, five quorum-difference
limbs, five floor-difference limbs) and eight 8-bit carry lookups. The load-bearing ones are the TEN
on the two differences: they are what forces `3·rooted − 2·total ≥ 0` and `total − 1 ≥ 0`, because a
limb vector of non-negative limbs denotes a non-negative value (`LimbTally.limbValue_nonneg`).

⚠ The eight OPERAND lookups are not part of that argument (`LimbTally.cmp_sound` does not use them);
they are there for the mod-`p` ↔ `ℤ` bridge (`LimbTally.rung_no_alias_at_deployed_constants`), which
needs every limb in `[0, 2^16)`. Two different jobs, said apart rather than blurred.

⚠ The total-stake limbs are looked up ONCE, not twice: both chains read the same four columns, and a
second identical lookup would be a duplicate constraint, not a second check. -/
def tallyRangeLookups : List VmConstraint2 :=
  [ .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TOTAL_STK_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (ROOTED_STK_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (QDIFF_LIMB 4)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 0)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 1)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 2)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 3)]⟩
  , .lookup ⟨TID_TALLY_LIMB, [.var (TPOS_LIMB 4)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 0)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 1)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 2)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (QDIFF_CARRY 3)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 0)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 1)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 2)]⟩
  , .lookup ⟨TID_TALLY_CARRY, [.var (TPOS_CARRY 3)]⟩ ]

/-- The generated QUORUM gates, wrapped into the target's constraint constructor. GENERATED — there is
no hand-written `VmConstraint2` in this block. -/
def qdiffChainGates : List VmConstraint2 :=
  qdiffChainBodies.map (fun b => .base (.gate b))

/-- The generated EMPTY-STAKE-TABLE FLOOR gates. GENERATED, from the same `LimbTally.chainBodies`
call at `α = 1, β = 0, γ = 1`. -/
def tposChainGates : List VmConstraint2 :=
  tposChainBodies.map (fun b => .base (.gate b))

def edGate : VmConstraint2 := .base (.gate edBody)
def stakeGate : VmConstraint2 := .base (.gate stakeBody)
def rootedGate : VmConstraint2 := .base (.gate rootedBody)
def authGate : VmConstraint2 := .base (.gate authBody)
/-- Published-anchor pin: the pinned WS anchor root is `PI[0]`. -/
def anchorRootPin : VmConstraint2 :=
  .base (.piBinding VmRow.first ANCHOR_ROOT PI_ANCHOR_ROOT)
/-- Published-anchor pins: the NINE rooted-bank-root limbs are `PI[1..9]` (MSB-first). Each limb rides
its own PI slot, so the peer-wrap's radix-`2^31` pack over `PI[1..9]` recovers the FULL 256-bit bank
hash — not a 31-bit projection. Written as an explicit literal (limb `i` → col `31+i` → PI `1+i`) so
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
nine radix-`2^31` MSB-first limbs, not a 31-bit projection); the two `u64` stake tallies as 16-bit limb
vectors with their two GENERATED comparison chains, the four crypto/logic results as carrier bits. Two
declared range tables (16-bit limbs, 8-bit carries); the shared 29-bit `range` table is gone with the
felt slacks that queried it. -/
def solLcVerifyDesc : EffectVmDescriptor2 :=
  { name        := "dregg-solana-lightclient-verify::v1"
  , traceWidth  := SOL_LC_WIDTH
  , piCount     := PI_COUNT
  , tables      := [⟨TID_TALLY_LIMB,  "range_w16", 1, .rangeLimb SOL_LIMB_BITS⟩
                   , ⟨TID_TALLY_CARRY, "range_w8",  1, .rangeLimb SOL_CARRY_BITS⟩]
  , constraints := tallyRangeLookups ++ qdiffChainGates ++ tposChainGates
                   ++ [edGate, stakeGate, rootedGate, authGate, anchorRootPin]
                   ++ bankRootPins ++ [slotPin]
  , hashSites   := []
  , ranges      := [] }

/-! ## §3b — ⚑ THE HISTORICAL RECORD: what a felt-width slack could and could not refuse.

A narrowed constant is a constant. What made a range tooth an `≤` relation was exactly this pair: the
interval sits strictly INSIDE the field, and a slack the prover wanted negative lands OUTSIDE it. Both
were FALSE at `RANGE_BITS = 128`.

⚠ **These theorems no longer describe a table this descriptor declares** — §3c is where the live
refusal lives. They are kept because the value they exhibit, `p − 1`, is the exact deployed encoding of
the empty stake table's `TPOS = −1`, and it is the reason the repair happened. -/

/-- **THE INTERVAL WAS INSIDE THE FIELD.** `2^29 = 536870912 < p = 2013265921`. -/
theorem sol_range_is_inside_the_field :
    (2 : ℤ) ^ RANGE_BITS < Dregg2.Circuit.Emit.EffectLower.P := by
  norm_num [RANGE_BITS, Dregg2.Circuit.Emit.EffectLower.P]

/-- ⚑ **AND THE WRAP WAS REFUSED.** A slack the prover wanted to be `−k`, for any magnitude
`0 < k ≤ 2^29`, is in the deployed mod-`p` reading the element `p − k ≥ p − 2^29 = 1476395009` —
nearly three times the interval ceiling. ⚠ FALSE at 30, and catastrophically false at the shipped
128, where `p − 1` sat inside and every negative slack was admitted. -/
theorem sol_wrapped_slack_is_outside_the_range (k : ℤ) (hk : 0 < k)
    (hk' : k ≤ (2 : ℤ) ^ RANGE_BITS) :
    ¬ (0 ≤ Dregg2.Circuit.Emit.EffectLower.P - k
        ∧ Dregg2.Circuit.Emit.EffectLower.P - k < (2 : ℤ) ^ RANGE_BITS) := by
  rintro ⟨_, hlt⟩
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  have hb : ((2 : ℤ) ^ RANGE_BITS) = 536870912 := by norm_num [RANGE_BITS]
  rw [hp, hb] at hlt
  rw [hb] at hk'
  omega

/-- ⚑ **THE ADMITTED VALUE, EXHIBITED — AND IT IS THE EMPTY STAKE TABLE.** `2013265920` is `p − 1`,
the deployed encoding of `TPOS = TOTAL_STK − 1 = −1`, which is what `TOTAL_STK = 0` fills. The
shipped 128-bit table CONTAINED it, so the `EmptyStakeTable` floor admitted a stake table with no
stake in it. -/
theorem sol_empty_stake_table_was_admitted_at_128 :
    ([2013265920] : List ℤ) ∈ rangeRows 128 := by
  rw [range_row_mem_iff]; norm_num

/-- …and the 29-bit table REFUSED it. One value, admitted then refused — the pair that made the
narrowing a repair rather than a renumbering.

⚠ Note what this refusal RESTS ON: `2013265920 ≥ 2^29`, a fact about the FIELD SIZE. It is false at 30
and catastrophically false at 128. §3c's replacement rests on nothing of the kind. -/
theorem sol_empty_stake_table_was_refused_at_29_bits :
    ([2013265920] : List ℤ) ∉ rangeRows RANGE_BITS := by
  rw [range_row_mem_iff]; norm_num [RANGE_BITS]

/-- **THE LIMB TOOTH IS THE EMITTED ONE.** The interval `airAccepts` reads for every difference and
operand limb (§5) is exactly membership in the declared 16-bit table's rows — not a second, private
notion of "in range" that could be narrowed here while the descriptor keeps shipping the old one. -/
theorem sol_limb_inRange_iff_mem_rangeRows (v : ℤ) :
    (0 ≤ v ∧ v < (2 : ℤ) ^ SOL_LIMB_BITS) ↔ [v] ∈ rangeRows SOL_LIMB_BITS :=
  (range_row_mem_iff v SOL_LIMB_BITS).symm

/-- …and the tables the descriptor DECLARES are the two the teeth query, by `rfl` on the emitted
object: the 16-bit tally-limb table and the 8-bit chain-carry table. -/
theorem sol_declared_tables :
    solLcVerifyDesc.tables = [⟨TID_TALLY_LIMB, "range_w16", 1, .rangeLimb SOL_LIMB_BITS⟩
      , ⟨TID_TALLY_CARRY, "range_w8", 1, .rangeLimb SOL_CARRY_BITS⟩] := rfl

/-- ⚑ **AND THE SHARED `range` TABLE IS NOT AMONG THEM, NOR AMONG THE LOOKUPS.** Both former felt
slacks are limbed chains, so the 29-bit table would be declared-but-unqueried. This is the tripwire: a
future felt-width slack re-introduced on `TableId.range` reds here. -/
theorem sol_range_table_is_not_declared :
    (∀ t ∈ solLcVerifyDesc.tables, t.id ≠ TableId.range)
      ∧ TableId.range ∉ (solLcVerifyDesc.constraints.filterMap
          (fun c => match c with | .lookup l => some l.table | _ => none)) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The width-tagged wire ids the Rust decoder reads, pinned: `.custom n` serializes as `5 + n`, so
the 16-bit table is id 85 and the 8-bit table is id 77, and `range_bits_for` recovers each width from
its own declaration. A drift in either id changes the descriptor bytes and therefore the VK. -/
theorem sol_tally_table_wire_ids :
    TID_TALLY_LIMB.wireId = 85 ∧ TID_TALLY_CARRY.wireId = 77 := by decide

/-! ### ⚑ §3c — THE LIMBED COMPARISONS: the capability, and the teeth that survived it.

Everything in §3b is about a `rangeRows` interval over ONE felt. Neither comparison lives there any
more. These are the facts about the LIMBED versions, and the last two are the reason widening the
representable tally by 2^33× did not re-admit anything. -/

/-- ⚑ **THE CAPABILITY, AS THE MEASURED NUMBER.** Four 16-bit limbs represent every value in
`[0, 2^64)`, which contains mainnet-beta's LIVE active stake — `432650183925625587` lamports, measured
2026-08-03 via `getVoteAccounts` at epoch 1011 / slot 436,909,708 — and Solana's total supply
(`631503420149974995`) besides. -/
theorem sol_tally_capacity_holds_live_active_stake :
    (432650183925625587 : ℤ) < (2 : ℤ) ^ (SOL_LIMB_BITS * SOL_TALLY_LIMBS)
      ∧ (631503420149974995 : ℤ) < (2 : ℤ) ^ (SOL_LIMB_BITS * SOL_TALLY_LIMBS) := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [SOL_LIMB_BITS, SOL_TALLY_LIMBS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_LIMBS]

/-- ⚑ …and the SAME value does not fit one felt, at any declared width. This is the pair that makes
the widening a capability and not a preference: live active stake is **214.9 MILLION** BabyBear
moduli (`432650183925625587 / 2013265921 = 214899670.9`), so no `bits:` — 29, 30, 64 or the 128 that
shipped — ever made it representable. A width declares an interval; the wire is one field element. -/
theorem sol_live_active_stake_does_not_fit_a_felt :
    (214899670 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 432650183925625587
      ∧ (432650183925625587 : ℤ) < 214899671 * Dregg2.Circuit.Emit.EffectLower.P := by
  refine ⟨?_, ?_⟩ <;>
    norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- ⚑ **THE QUORUM REFUSAL NO LONGER MENTIONS THE FIELD.** If the true tallies fail the non-strict
`≥ 2/3` threshold, NO assignment satisfies the emitted quorum chain together with the
difference-limb containment — for EVERY limb width, including the widths at which the old single-felt
tooth was vacuous (`≥ 31`) and the width at which it was merely leaky (30). -/
theorem sol_quorum_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 3 * LimbTally.limbValue bits a (LimbTally.aCols qdiffRungs)
      - 2 * LimbTally.limbValue bits a (LimbTally.bCols qdiffRungs) < 0) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 3 2 0 LimbTally.TALLY_CARRY_OFF QDIFF_TOP qdiffRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **AND SO DOES THE EMPTY-STAKE-TABLE REFUSAL — the check that actually FAILED.** At `total = 0`
the floor difference is `−1`; no limb vector of non-negative limbs denotes `−1`. Quantified over
EVERY limb width, so this is not "the wrapped value lands outside an interval at 29 bits". -/
theorem sol_empty_stake_refusal_is_field_independent (a : Assignment) (bits : Nat)
    (hfail : 1 * LimbTally.limbValue bits a (LimbTally.aCols tposRungs)
      - 0 * LimbTally.limbValue bits a (LimbTally.bCols tposRungs) < 1) :
    ¬ (LimbTally.BodiesVanish a
        (LimbTally.chainBodies bits 1 0 1 LimbTally.TALLY_CARRY_OFF TPOS_TOP tposRungs)
      ∧ LimbTally.LimbsInRange bits a (LimbTally.diffCols tposRungs TPOS_TOP)) :=
  LimbTally.emitted_chain_refuses hfail

/-- ⚑ **THE FLOOR CHAIN READS THE QUORUM CHAIN'S DENOMINATOR — the same four columns, by `rfl`.**

Without this the two chains could bound two DIFFERENT quantities while both looking correct: a prover
could satisfy `total ≥ 1` on one vector and `3·rooted ≥ 2·total` on another. `LimbTally.aCols
tposRungs` and `LimbTally.bCols qdiffRungs` are literally the same column list, so `total` means one
thing in this AIR. -/
theorem sol_tpos_reads_the_quorum_denominator :
    LimbTally.aCols tposRungs = LimbTally.bCols qdiffRungs := by decide

/-! ### ⚑ §3d — the mod-`p` ↔ `ℤ` bridge, DISCHARGED AT **THESE** CONSTANTS.

⚠ `LimbTally.rung_no_alias_at_deployed_constants` is stated at `α = 3, β = 2, γ = 1` — CometBFT's
STRICT supermajority. **Neither of Solana's two chains has those constants** (the quorum is non-strict,
`γ = 0`; the floor is `α = 1, β = 0`). Citing it here would be a claim about a sibling AIR's gates, so
the two instances this descriptor actually emits are proved below from the PARAMETRIC
`LimbTally.rung_value_bounds`.

Both intervals are far inside the field, and the numbers are worth reading rather than taking on the
word "inside": the quorum rung's ℤ image sits in `(−16973952, 8585472)` and the floor rung's in
`(−16842881, 8454400)`, against `p = 2013265921`. So a body that is `0 mod p` on a range-respecting
assignment IS `0` over `ℤ`, and `LimbTally.chain_recomposes` transfers to the deployed denotation. -/

/-- **NO ALIAS ON THE QUORUM CHAIN** (`α = 3, β = 2, γ = 0`, `coff = 128`, limbs 16, carries 8). -/
theorem sol_qdiff_rung_no_alias (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ SOL_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ SOL_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ SOL_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 3 * x - 2 * y + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
    ∧ 3 * x - 2 * y + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
        < Dregg2.Circuit.Emit.EffectLower.P := by
  obtain ⟨hlo, hhi⟩ := LimbTally.rung_value_bounds SOL_LIMB_BITS SOL_CARRY_BITS 3 2 0
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  simp only [SOL_LIMB_BITS, SOL_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [hp] at hlo hhi ⊢
  constructor <;> linarith

/-- **NO ALIAS ON THE EMPTY-STAKE-TABLE FLOOR CHAIN** (`α = 1, β = 0, γ = 1`). The `β = 0` operand
term contributes nothing to the interval, which is why pointing `bCol` at `aCol` cannot widen it. -/
theorem sol_tpos_rung_no_alias (x y d cin cout : ℤ)
    (hx : 0 ≤ x ∧ x < (2 : ℤ) ^ SOL_LIMB_BITS) (hy : 0 ≤ y ∧ y < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hd : 0 ≤ d ∧ d < (2 : ℤ) ^ SOL_LIMB_BITS)
    (hcin : 0 ≤ cin ∧ cin < (2 : ℤ) ^ SOL_CARRY_BITS)
    (hcout : 0 ≤ cout ∧ cout < (2 : ℤ) ^ SOL_CARRY_BITS) :
    -Dregg2.Circuit.Emit.EffectLower.P
        < 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
    ∧ 1 * x - 0 * y - 1 + (cin - LimbTally.TALLY_CARRY_OFF) - d
          - (cout - LimbTally.TALLY_CARRY_OFF) * (2 : ℤ) ^ SOL_LIMB_BITS
        < Dregg2.Circuit.Emit.EffectLower.P := by
  obtain ⟨hlo, hhi⟩ := LimbTally.rung_value_bounds SOL_LIMB_BITS SOL_CARRY_BITS 1 0 1
    LimbTally.TALLY_CARRY_OFF x y d cin cout (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [LimbTally.TALLY_CARRY_OFF]) hx hy hd hcin hcout
  have hp : (Dregg2.Circuit.Emit.EffectLower.P : ℤ) = 2013265921 := rfl
  simp only [SOL_LIMB_BITS, SOL_CARRY_BITS, LimbTally.TALLY_LIMB_BITS, LimbTally.TALLY_CARRY_BITS,
    LimbTally.TALLY_CARRY_OFF] at hlo hhi ⊢
  norm_num [hp] at hlo hhi ⊢
  constructor <;> linarith

/-! ## §4 — non-vacuous per-gate lemmas (the emitted bodies bite, both directions). -/

/-- **THE QUORUM CHAIN'S GENERATED BODIES ARE EXACTLY `ChainOk`** — this module's instance of
`LimbTally.chainBodies_zero_iff`, so the soundness below is about the bodies that SHIP rather than a
private predicate resembling them. (The replacement for the old `qDiff_body_zero_iff`, which said the
same thing about the ONE hand-written felt gate.) -/
theorem sol_qdiff_chain_zero_iff (a : Assignment) :
    LimbTally.BodiesVanish a qdiffChainBodies
      ↔ LimbTally.ChainOk SOL_LIMB_BITS 3 2 LimbTally.TALLY_CARRY_OFF a QDIFF_TOP qdiffRungs 0 0 :=
  LimbTally.chainBodies_zero_iff SOL_LIMB_BITS 3 2 0 LimbTally.TALLY_CARRY_OFF a QDIFF_TOP qdiffRungs

/-- **THE FLOOR CHAIN'S GENERATED BODIES ARE EXACTLY `ChainOk`** — the replacement for the old
`tPos_body_zero_iff`. -/
theorem sol_tpos_chain_zero_iff (a : Assignment) :
    LimbTally.BodiesVanish a tposChainBodies
      ↔ LimbTally.ChainOk SOL_LIMB_BITS 1 0 LimbTally.TALLY_CARRY_OFF a TPOS_TOP tposRungs 1 0 :=
  LimbTally.chainBodies_zero_iff SOL_LIMB_BITS 1 0 1 LimbTally.TALLY_CARRY_OFF a TPOS_TOP tposRungs

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

/-- **`airAccepts a`** — the emitted verify-logic gates all vanish on row `a`, and each of the two
comparisons' difference limbs lies in `[0, 2^16)` (the denotation `range_row_mem_iff` connects the
emitted lookups to). The published-anchor pins are the addressing layer, orthogonal to the logic.

⚑ Each single-felt slack conjunct became a PAIR: the generated chain's bodies vanish, and the
difference limb vector is contained. Together those are the inequality at ANY tally a `u64` holds —
see `LimbTally.cmp_sound`. -/
def airAccepts (a : Assignment) : Prop :=
  LimbTally.BodiesVanish a qdiffChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)
  ∧ LimbTally.BodiesVanish a tposChainBodies
  ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)
  ∧ edBody.eval a = 0
  ∧ stakeBody.eval a = 0
  ∧ rootedBody.eval a = 0
  ∧ authBody.eval a = 0

/-- **THE REFINEMENT (soundness): a satisfying AIR witness ENTAILS `solVerifyDecision` accept.** Fed a
row `a` whose columns read the update's true projections (the honest-witness relation — the two stakes
as 16-bit LIMB VECTORS, the carrier/gate bits as `if · then 1 else 0`), if the emitted verify-logic
gates accept, then the exported scalar decision `solVerifyDecision` accepts.

⚑ The quorum chain discharges the `≥ 2/3` threshold and the floor chain discharges `total > 0`, and
NEITHER hypothesis bounds a tally: `LimbTally.emitted_chain_sound` reads the five generated gates and
the five difference-limb containments and returns the inequality over the LIMB VALUES. That bound was
the whole capability limit, and it is gone. -/
theorem solLcAir_sound (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hr : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs) = (rootedStk : ℤ))
    (ht : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs) = (totalStk : ℤ))
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true := by
  obtain ⟨hqBodies, hqLimbs, htBodies, htLimbs, hedB, hstkB, hrootedB, hauthB⟩ := hacc
  -- ⚑ Threshold: `0 ≤ 3·rooted − 2·total`, AT ANY TALLY MAGNITUDE.
  have hthr : 2 * totalStk ≤ 3 * rootedStk := by
    have hcmp := LimbTally.emitted_chain_sound hqBodies hqLimbs
    rw [hr, ht] at hcmp
    have : 2 * (totalStk : ℤ) ≤ 3 * (rootedStk : ℤ) := by linarith
    exact_mod_cast this
  -- ⚑ Total positivity (the `EmptyStakeTable` floor): `1 ≤ 1·total − 0·total`.
  have hpos : 0 < totalStk := by
    have hcmp := LimbTally.emitted_chain_sound htBodies htLimbs
    rw [sol_tpos_reads_the_quorum_denominator, ht] at hcmp
    have hposZ : (1 : ℤ) ≤ (totalStk : ℤ) := by linarith
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
proof of Solana rooted finality — now at LIVE mainnet-beta stake magnitude rather than at tallies below
1.8e8. -/
theorem solLcAir_no_forgery (L : SolLeaf) (hcr : L.stakeTableCR)
    (ts : SolTrustedState L) (u : SolUpdate L) (a : Assignment)
    (hr : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs)
      = (rootedStake L u : ℤ))
    (ht : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs)
      = (totalStake L u : ℤ))
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

/-- **Completeness (the honest prover CAN fill the row).** For any decision-accepting projections, an
honest row that fills the two comparison chains with their true limbs and carries and the carrier/gate
bits with the true results is accepted by the emitted logic. The non-vacuity partner of soundness: the
AIR is satisfiable EXACTLY on accepted updates, not vacuously empty.

⚑ **WHAT IS NO LONGER A HYPOTHESIS, AND IT IS THE POINT OF THIS WHOLE CHANGE.** The previous version
required `3·rootedStk < 2^RANGE_BITS` AND `totalStk < 2^RANGE_BITS` — bounds on the TALLY, at 2^29 —
because each slack was one felt. Mainnet-beta's live active stake is `432650183925625587` (2^58.586);
it never satisfied either, at 29 bits or at the 128 that shipped, because a felt holds 30.9 bits
either way. **Both hypotheses are gone**, and no tally bound replaces them.

What replaces them is the honest chains themselves (`hQdiffChain`/`hQdiffLimbs`,
`hTposChain`/`hTposLimbs`), which an honest prover constructs by `LimbTally.fillDigit` /
`LimbTally.fillCarry` at ANY magnitude a `u64` holds — and `solLcAir_accepts_at_live_active_stake`
(§7) exhibits exactly that, cell for cell, at the measured live stake. -/
theorem solLcAir_complete (a : Assignment)
    (rootedStk totalStk : Nat) (edB stakeB rootedB authB : Bool)
    (hed : a ED_OK = (if edB then (1 : ℤ) else 0))
    (hstk : a STAKE_TABLE_OK = (if stakeB then (1 : ℤ) else 0))
    (hrooted : a ROOTED_OK = (if rootedB then (1 : ℤ) else 0))
    (hauth : a AUTH_OK = (if authB then (1 : ℤ) else 0))
    (hQdiffChain : LimbTally.BodiesVanish a qdiffChainBodies)
    (hQdiffLimbs :
      LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP))
    (hTposChain : LimbTally.BodiesVanish a tposChainBodies)
    (hTposLimbs : LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP))
    (hdec : solVerifyDecision rootedStk totalStk edB stakeB rootedB authB = true) :
    airAccepts a := by
  unfold solVerifyDecision at hdec
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdec
  obtain ⟨⟨⟨⟨⟨_hpos, _hthr⟩, hedB⟩, hstkB⟩, hrootedB⟩, hauthB⟩ := hdec
  refine ⟨hQdiffChain, hQdiffLimbs, hTposChain, hTposLimbs, ?_, ?_, ?_, ?_⟩
  · rw [ed_body_zero_iff, hed]; simp [hedB]
  · rw [stake_body_zero_iff, hstk]; simp [hstkB]
  · rw [rooted_body_zero_iff, hrooted]; simp [hrootedB]
  · rw [auth_body_zero_iff, hauth]; simp [hauthB]

/-! ## §6 — the emitted wire JSON (byte-pinned golden) + shape pins. -/

-- The Rust decoder ingests THIS string (`parse_vm_descriptor2`); byte-pinned golden (a drift on either
-- side breaks this `#guard`). ⚑ RE-EMITTED 2026-08-03 for the limbed tallies: trace width 19 → 41,
-- constraints 19 → 51, the ONE 29-bit range table replaced by TWO width-tagged tables (16 / 8), and
-- the two hand-written felt slacks + their two lookups replaced by TEN GENERATED chain gates and
-- twenty-six per-limb lookups. Captured from this module's own `emitVmJson2`.
#guard emitVmJson2 solLcVerifyDesc ==
  "{\"name\":\"dregg-solana-lightclient-verify::v1\",\"ir\":2,\"trace_width\":41,\"public_input_count\":11,\"tables\":[{\"id\":85,\"name\":\"range_w16\",\"arity\":1,\"sem\":\"range\",\"bits\":16},{\"id\":77,\"name\":\"range_w8\",\"arity\":1,\"sem\":\"range\",\"bits\":8}],\"constraints\":[{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":4}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":5}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":6}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":7}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":8}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":9}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":10}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":11}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":12}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":13}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":14}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":15}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":16}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":21}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":22}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":23}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":24}]},{\"t\":\"lookup\",\"table\":85,\"tuple\":[{\"t\":\"var\",\"v\":25}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":17}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":18}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":19}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":20}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":26}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":27}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":28}]},{\"t\":\"lookup\",\"table\":77,\"tuple\":[{\"t\":\"var\",\"v\":29}]},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":8}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":12}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":17}}},\"r\":{\"t\":\"const\",\"v\":8388608}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":9}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":13}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":18}}},\"r\":{\"t\":\"var\",\"v\":17}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":10}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":14}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":19}}},\"r\":{\"t\":\"var\",\"v\":18}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":3},\"r\":{\"t\":\"var\",\"v\":11}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-2},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":15}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":20}}},\"r\":{\"t\":\"var\",\"v\":19}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":20},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":16}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":4}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":4}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":21}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":26}}},\"r\":{\"t\":\"const\",\"v\":8388607}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":5}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":5}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":22}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":27}}},\"r\":{\"t\":\"var\",\"v\":26}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":6}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":6}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":23}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":28}}},\"r\":{\"t\":\"var\",\"v\":27}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":1},\"r\":{\"t\":\"var\",\"v\":7}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":0},\"r\":{\"t\":\"var\",\"v\":7}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":24}}},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-65536},\"r\":{\"t\":\"var\",\"v\":29}}},\"r\":{\"t\":\"var\",\"v\":28}},\"r\":{\"t\":\"const\",\"v\":8388480}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":29},\"r\":{\"t\":\"mul\",\"l\":{\"t\":\"const\",\"v\":-1},\"r\":{\"t\":\"var\",\"v\":25}}},\"r\":{\"t\":\"const\",\"v\":-128}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":0},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":1},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":2},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"gate\",\"body\":{\"t\":\"add\",\"l\":{\"t\":\"var\",\"v\":3},\"r\":{\"t\":\"const\",\"v\":-1}}},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":30,\"pi_index\":0},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":31,\"pi_index\":1},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":32,\"pi_index\":2},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":33,\"pi_index\":3},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":34,\"pi_index\":4},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":35,\"pi_index\":5},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":36,\"pi_index\":6},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":37,\"pi_index\":7},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":38,\"pi_index\":8},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":39,\"pi_index\":9},{\"t\":\"pi_binding\",\"row\":\"first\",\"col\":40,\"pi_index\":10}],\"hash_sites\":[],\"ranges\":[]}"

/-- Shape pins (robust; a layout drift moves these). Converted from `#guard` per
`metatheory/docs/GUARD-DISCIPLINE.md` — a `#guard` is the same unsafe evaluation with the name, the
term and the axiom record deleted, and `decide` here is strictly stronger than the guard was. -/
theorem sol_shape_pins :
    solLcVerifyDesc.traceWidth = SOL_LC_WIDTH
      ∧ solLcVerifyDesc.piCount = PI_COUNT
      ∧ solLcVerifyDesc.constraints.length = 51
      ∧ solLcVerifyDesc.tables.length = 2 := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  decide

/-- ⚑ **THE TALLY IS TWENTY-SIX LOOKUPS, NOT TWO.** Eighteen 16-bit limb checks plus eight 8-bit carry
checks, where the two single-felt slacks carried exactly ONE each. A re-emission that dropped a limb
moves this number; the old shape had no number to move. -/
theorem sol_tally_lookup_count : tallyRangeLookups.length = 26 := by decide

/-- …and each chain is FIVE generated gates for four rungs — one per rung plus the closure gate that
forces the final carry into the top difference limb. Without the closure gate the prover could dump a
residue into a carry nothing reads, and the recomposition would be off by `2^64`. -/
theorem sol_chain_gate_counts :
    qdiffChainGates.length = 5 ∧ tposChainGates.length = 5 := by decide

/-- The two crypto carriers and the two logic gates are real trace columns and none is PI-bound (the
results ride hidden). -/
theorem sol_carriers_are_hidden_columns :
    ED_OK < SOL_LC_WIDTH ∧ STAKE_TABLE_OK < SOL_LC_WIDTH
      ∧ ROOTED_OK < SOL_LC_WIDTH ∧ AUTH_OK < SOL_LC_WIDTH := by decide

/-- The tally block occupies columns 4..29 contiguously, below the published anchors: four total-stake
limbs, four rooted-stake limbs, five quorum-difference limbs, four quorum carries, five floor-difference
limbs, four floor carries. -/
theorem sol_tally_block_layout :
    TOTAL_STK_LIMB 0 = 4 ∧ TOTAL_STK_LIMB 3 = 7
      ∧ ROOTED_STK_LIMB 0 = 8 ∧ ROOTED_STK_LIMB 3 = 11
      ∧ QDIFF_LIMB 0 = 12 ∧ QDIFF_TOP = 16
      ∧ QDIFF_CARRY 0 = 17 ∧ QDIFF_CARRY 3 = 20
      ∧ TPOS_LIMB 0 = 21 ∧ TPOS_TOP = 25
      ∧ TPOS_CARRY 0 = 26 ∧ TPOS_CARRY 3 = 29
      ∧ TPOS_CARRY 3 < ANCHOR_ROOT := by decide

/-- The widened rooted-bank-root anchor is unchanged by the tally work, only shifted: nine limbs,
contiguous cols 31..39 → PI 1..9, MSB-first, `⌈256/31⌉ = 9` covering the full 256 bits. -/
theorem sol_bank_root_anchor_layout :
    BANK_ROOT_LIMBS = 9 ∧ bankRootPins.length = BANK_ROOT_LIMBS
      ∧ BANK_ROOT 0 = 31 ∧ BANK_ROOT 8 = 39
      ∧ SLOT_COL = 40 ∧ PI_SLOT = 10
      ∧ PI_BANK_ROOT 0 = 1 ∧ PI_BANK_ROOT 8 = 9 ∧ PI_BANK_ROOT 8 < PI_SLOT
      ∧ BANK_ROOT 8 < SLOT_COL
      ∧ 31 * BANK_ROOT_LIMBS ≥ 256 := by decide

/-! ## §7 — ⚑ THE MEASUREMENT: MAINNET-BETA'S LIVE ACTIVE STAKE, AT THE QUORUM BOUNDARY.

This is the section the whole change exists for. Everything below is a NAMED THEOREM over an explicit
row of the emitted descriptor — the same row, cell for cell, a Rust trace filler hands the deployed
prover.

`totalStk = 432650183925625587` is mainnet-beta's ACTIVE stake, MEASURED LIVE 2026-08-03 via
`getVoteAccounts` on `api.mainnet-beta.solana.com` (689 current + 14 delinquent vote accounts, epoch
1011, slot 436,909,708): 432.650M SOL, `2^58.586`, 214.9 million times the BabyBear modulus. It never
fit a column.

⚑ And the two cases below differ by **ONE LAMPORT OUT OF 4.3e17**: `rootedStk = 288433455950417058` is
the SMALLEST value satisfying Solana's non-strict `3·rooted ≥ 2·total`; `288433455950417057` is one
below it and must be REJECTED. The first ACCEPTS, the second has no satisfying assignment. -/

/-- The honest row at live mainnet-beta scale, as the cell vector a Rust harness fills. Written as a
LIST so the Lean row and the Rust trace row are literally the same 41 numbers in the same order — a
divergence between the two is a diff on one object, not a comparison of two readings.

⚑ Note the QUORUM CARRIES: `[127, 127, 130, 128]` is `[−1, −1, +2, 0]` offset by 128. The quorum
difference limbs are all zero (live active stake happens to be divisible by 3, so the minimal quorum
hits `3·S − 2·T = 0` exactly) but the CHAIN IS NOT trivially satisfied — two rungs BORROW and one
carries `+2`. The all-zero difference is the boundary, not a degenerate row. -/
def solMaxScaleCells : List ℤ :=
  [ 1, 1, 1, 1                       -- ED_OK, STAKE_TABLE_OK, ROOTED_OK, AUTH_OK
  , 62195, 52452, 5388, 1537         -- TOTAL_STK  limbs = 432650183925625587 (live active stake)
  , 19618, 13123, 47283, 1024        -- ROOTED_STK limbs = 288433455950417058 (minimal quorum)
  , 0, 0, 0, 0, 0                    -- QDIFF      limbs = 3·R − 2·T = 0
  , 127, 127, 130, 128               -- QDIFF carries, offset (honest carries −1, −1, +2, 0)
  , 62194, 52452, 5388, 1537, 0      -- TPOS       limbs = T − 1 = 432650183925625586
  , 128, 128, 128, 128               -- TPOS carries, offset (honest carry 0 rides as 128)
  , 11111                            -- ANCHOR_ROOT
  , 1, 2, 3, 4, 5, 6, 7, 8, 9        -- BANK_ROOT limbs 0..8
  , 436909708 ]                      -- SLOT_COL (the measured live slot)

/-- The row is exactly as wide as the descriptor. -/
theorem solMaxScaleCells_width : solMaxScaleCells.length = SOL_LC_WIDTH := by decide

/-- The row as an `Assignment`. -/
def solMaxScaleRow : Assignment := fun i => solMaxScaleCells.getD i 0

/-- ⚑ **THE TALLY THE ROW DENOTES IS MAINNET-BETA'S LIVE ACTIVE STAKE.** Four 16-bit limbs, read by
`limbValue`, recompose to `432650183925625587` exactly. -/
theorem solMaxScaleRow_total_is_live_active_stake :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.bCols qdiffRungs)
      = 432650183925625587 := by decide

/-- …and the rooted stake is the SMALLEST non-strict `≥ 2/3` quorum of it. -/
theorem solMaxScaleRow_rooted_is_minimal_quorum :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.aCols qdiffRungs)
      = 288433455950417058 := by decide

/-- …which really is minimal: `3·R ≥ 2·T` holds at `R`, and FAILS one lamport below. -/
theorem minimal_quorum_is_minimal :
    2 * 432650183925625587 ≤ 3 * 288433455950417058
      ∧ ¬ (2 * 432650183925625587 ≤ 3 * 288433455950417057) := by decide

/-- …and the floor chain's difference vector denotes `total − 1`, so the `EmptyStakeTable` floor is
carrying the same denominator the quorum does. -/
theorem solMaxScaleRow_floor_difference_is_total_minus_one :
    LimbTally.limbValue SOL_LIMB_BITS solMaxScaleRow (LimbTally.diffCols tposRungs TPOS_TOP)
      = 432650183925625586 := by decide

/-- ⚑⚑ **THE DELIVERABLE: THE EMITTED AIR ACCEPTS A VALIDATOR SET AT MAINNET-BETA'S LIVE STAKE.**

Every gate of `solLcVerifyDesc` vanishes on this row and every limb tooth admits it. At a single felt
this update could not be REPRESENTED, let alone accepted: `3·rootedStk = 865300367851251174` is 429.8
million times the BabyBear modulus, so no declared width — 29, 30, 64, or the 128 that shipped — ever
made it provable. -/
theorem solLcAir_accepts_at_live_active_stake : airAccepts solMaxScaleRow := by
  refine ⟨?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide⟩
  · decide
  · decide
  · decide
  · decide

/-- ⚑ **AND THE QUORUM TOOTH SURVIVED THE WIDENING, AT THE SAME SCALE.** One lamport below the minimal
quorum (`rootedStk = 288433455950417057`) the true difference is `−3`, and
`LimbTally.emitted_chain_refuses` gives: NO assignment of difference limbs and carries satisfies the
chain together with the containments. Not "the wrapped value lands outside an interval" — there is no
limb vector of non-negative limbs denoting `−3`.

⚠ This is the exact failure mode to watch for — a wider representation re-admitting the sub-quorum. It
does not, and the reason is structural rather than arithmetic-on-`p`. -/
theorem solLcAir_refuses_sub_quorum_at_live_active_stake (a : Assignment)
    (hTotal : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.bCols qdiffRungs)
      = 432650183925625587)
    (hRooted : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols qdiffRungs)
      = 288433455950417057) :
    ¬ (LimbTally.BodiesVanish a qdiffChainBodies
        ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols qdiffRungs QDIFF_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal, hRooted]; norm_num

/-- ⚑⚑ **THE EMPTY STAKE TABLE IS REFUSED — the check that FAILED, closed for a reason that does not
mention the field.**

At `totalStk = 0` the floor difference is `1·0 − 0·0 − 1 = −1`, and no limb vector of non-negative
limbs denotes `−1`. The 128-bit table ADMITTED this (`sol_empty_stake_table_was_admitted_at_128`: the
slack rode as `p − 1 = 2013265920`, inside `[0, 2^128)`), so a stake table with no stake in it passed
its own emptiness floor and — with `rootedStk = 0` too, giving quorum slack `0` — a block signed by
nobody satisfied both teeth. The 29-bit narrowing refused it because `p − 1 ≥ 2^29`, a fact about the
FIELD. This refuses it because `1 ≤ 0` is false. -/
theorem solLcAir_refuses_the_empty_stake_table (a : Assignment)
    (hTotal : LimbTally.limbValue SOL_LIMB_BITS a (LimbTally.aCols tposRungs) = 0) :
    ¬ (LimbTally.BodiesVanish a tposChainBodies
        ∧ LimbTally.LimbsInRange SOL_LIMB_BITS a (LimbTally.diffCols tposRungs TPOS_TOP)) := by
  refine LimbTally.emitted_chain_refuses ?_
  rw [hTotal]; norm_num

/-- …and the HONEST side of that same floor is admitted at live scale: the row above satisfies the
floor chain and its containments, at `total = 432650183925625587`. Both polarities on one tooth. -/
theorem solLcAir_admits_the_nonempty_stake_table :
    LimbTally.BodiesVanish solMaxScaleRow tposChainBodies
      ∧ LimbTally.LimbsInRange SOL_LIMB_BITS solMaxScaleRow
          (LimbTally.diffCols tposRungs TPOS_TOP) := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- ⚑ **THE CAPACITY PAIR, AS THE TWO NUMBERS THAT MATTER.** Live active stake fits a `u64` — that is
what four 16-bit limbs buy — and exceeds the BabyBear modulus by a factor of **214,899,670**, which is
what one column never could. Both halves stated together so the flattering one cannot be quoted
alone. -/
theorem sol_live_stake_capacity_pair :
    (432650183925625587 : ℤ) < (2 : ℤ) ^ 64
      ∧ (214899670 : ℤ) * Dregg2.Circuit.Emit.EffectLower.P < 432650183925625587 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Dregg2.Circuit.RangeFieldContainment.babybear_modulus]

/-- Carriers / gates: a set bit accepts; a cleared (forged / optimistic / imposter) bit is refused.
Converted from four `#guard` pairs into one named theorem with both polarities. -/
theorem sol_carrier_bits_discriminate :
    (edBody.eval (fun i => if i = ED_OK then 1 else 0) = 0 ∧ edBody.eval (fun _ => 0) ≠ 0)
      ∧ (stakeBody.eval (fun i => if i = STAKE_TABLE_OK then 1 else 0) = 0
          ∧ stakeBody.eval (fun _ => 0) ≠ 0)
      ∧ (rootedBody.eval (fun i => if i = ROOTED_OK then 1 else 0) = 0
          ∧ rootedBody.eval (fun _ => 0) ≠ 0)
      ∧ (authBody.eval (fun i => if i = AUTH_OK then 1 else 0) = 0
          ∧ authBody.eval (fun _ => 0) ≠ 0) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩⟩

/-! ## §8 — axiom hygiene. -/

#assert_axioms sol_qdiff_chain_zero_iff
#assert_axioms sol_tpos_chain_zero_iff
#assert_axioms ed_body_zero_iff
#assert_axioms stake_body_zero_iff
#assert_axioms rooted_body_zero_iff
#assert_axioms auth_body_zero_iff
#assert_axioms sol_limb_inRange_iff_mem_rangeRows
#assert_axioms sol_carriers_are_hidden_columns
#assert_axioms solLcAir_sound
#assert_axioms solLcAir_no_forgery
#assert_axioms solLcAir_complete
-- The HISTORICAL width record: both direction theorems + the exhibited admitted-then-refused value.
#assert_axioms sol_range_is_inside_the_field
#assert_axioms sol_wrapped_slack_is_outside_the_range
#assert_axioms sol_empty_stake_table_was_admitted_at_128
#assert_axioms sol_empty_stake_table_was_refused_at_29_bits
-- ⚑ The limbed tallies: capability, the field-free refusals, the emitted shape.
#assert_axioms sol_tally_capacity_holds_live_active_stake
#assert_axioms sol_live_active_stake_does_not_fit_a_felt
#assert_axioms sol_quorum_refusal_is_field_independent
#assert_axioms sol_empty_stake_refusal_is_field_independent
#assert_axioms sol_tpos_reads_the_quorum_denominator
#assert_axioms sol_qdiff_rung_no_alias
#assert_axioms sol_tpos_rung_no_alias
#assert_axioms sol_declared_tables
#assert_axioms sol_range_table_is_not_declared
#assert_axioms sol_tally_table_wire_ids
#assert_axioms sol_shape_pins
#assert_axioms sol_tally_lookup_count
#assert_axioms sol_chain_gate_counts
#assert_axioms sol_tally_block_layout
#assert_axioms sol_bank_root_anchor_layout
-- ⚑ THE MEASUREMENT.
#assert_axioms solMaxScaleCells_width
#assert_axioms solMaxScaleRow_total_is_live_active_stake
#assert_axioms solMaxScaleRow_rooted_is_minimal_quorum
#assert_axioms minimal_quorum_is_minimal
#assert_axioms solMaxScaleRow_floor_difference_is_total_minus_one
#assert_axioms solLcAir_accepts_at_live_active_stake
#assert_axioms solLcAir_refuses_sub_quorum_at_live_active_stake
#assert_axioms solLcAir_refuses_the_empty_stake_table
#assert_axioms solLcAir_admits_the_nonempty_stake_table
#assert_axioms sol_live_stake_capacity_pair
#assert_axioms sol_carrier_bits_discriminate

#print axioms solLcAir_sound
#print axioms solLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientSolanaAir
