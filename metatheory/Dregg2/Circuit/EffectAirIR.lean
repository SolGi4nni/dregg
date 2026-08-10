/-
# `Dregg2.Circuit.EffectAirIR` — the vocabulary `EffectSpec2` was missing.

## The measured finding this file answers

Phase 1 (`Dregg2/Circuit/Emit/EffectLower.lean`, `docs/LOGIC-COMPILER-ASSESSMENT.md` §P1.5) built
`lowerEffect : EffectSpec2 → EffectVmDescriptor2` and then MEASURED that its output reaches only
**12 of the 76** checked-in `circuit/descriptors/by-name/*.json`, because `EffectSpec2` carries
exactly one kind of arithmetic — a flat `ConstraintSystem` of `lhs = rhs` over `Circuit.Expr` — and
the deployed descriptors carry five kinds. The capability ladder, cumulative, over those 76:

    gate + first-row PI                    12 / 76      ← what `EffectSpec2` could say
    + window / boundary / last-row PI       25 / 76
    + LOOKUPS and declared TABLES           76 / 76      ← +51, the whole unlock

**51 of the 76 carry a lookup/table leg and `EffectSpec2` had no name for one.** The gap was never
in the emitter; it was that the SOURCE LANGUAGE could not say the thing. This file is the
vocabulary, and `EffectSpec2` gains ONE field (`air : EffectAir := {}`) that carries it.

## It is TableAirIR's vocabulary, deliberately — not a fourth private copy

`Dregg2/Circuit/TableAirIR.lean` cured the identical disease one layer down (the shared auxiliary
tables had no IR, so every one was hand-authored Rust algebra). Its four hard-won distinctions are
REUSED here rather than re-derived:

  * **`RowSel`** (`.all/.first/.last/.transition`) — the p3 row filter a gate is asserted under.
    `TableGate.transition_weakens` proves re-scoping is a REAL weakening, invisible to any check
    that reads the body alone.
  * **`WindowExpr`** — the current-AND-next-row leaf. ⚠ With TableAirIR's refusal: a `nxt` read is
    only meaningful under `.transition`.
  * **The multiplicity EXPRESSION on a bus interaction** — `Ir2Air::Main` hardcodes multiplicity
    `1`; a padded or conditional query cannot be said without one.
  * **`BusOp.provide` vs `.query`** — the two SIDES of a lookup bus. A table that queries what it
    should serve is unsatisfiable one way and vacuous the other, so this is a constructor, never a
    negated `query`.

## ⚑ WHAT THE MAIN RAIL REFUSES, AND WHY THAT IS THE POINT

`EffectAir` can SAY strictly more than `EffectVmDescriptor2`'s main-instance constraint set can
take, and the two gaps are named here rather than silently dropped:

  1. **A non-unit multiplicity.** `DescriptorIR2.Lookup` is `⟨table, tuple⟩` — no `mult` field at
     all, because `Ir2Air::Main` pushes every declared lookup at multiplicity 1 (a main row is
     unconditionally real). A `LookupLeg` with `mult ≠ 1` has no main-rail image.
  2. **The serving side.** `.provide`/`.receive`/`.send` are the shared-TABLE side of a bus. A main
     descriptor only ever QUERIES. A `LookupLeg` with `op ≠ .query` has no main-rail image.
  3. **A `nxt` read outside `.transition`.** Under `.all` this is TableAirIR's refusal verbatim (on
     the last row p3's `next` is the WRAP row). Under `.first`/`.last` the reason is STRONGER and
     rail-specific: those lower to `VmConstraint.boundary`, whose body is an `EmittedExpr` read
     against `env.loc` ONLY — the target constructor cannot read the next row at all.

`EffectAir.mainRailOk` is the DECIDABLE verdict, so "this spec is expressible on the deployed main
rail" is a `decide`-able claim about the emitted object rather than a sentence a reader checks by
eye. `EffectLower` lowers an ill-formed leg to an UNSATISFIABLE boundary pair — a descriptor that
REFUSES rather than one that quietly asserts less. That direction is the whole discipline: dropping
a leg accepts strictly more, which is the failure a byte-golden cannot see.

The legs that a main descriptor refuses are exactly the legs a `TableAir` takes. That is not a hole
in this file; it is the seam between the two rails, and it is where a padded shared table goes.

## What this file does NOT claim

It is SYNTAX. `EffectAir` has no denotation here: a lookup leg's meaning is the LogUp multiset
balance of the assembled instance (`Satisfied2`'s table legs), a range leg's is `VmRange.holds`, a
window leg's is `WindowConstraint.holdsAt`. All three live with the target IR, and the lowering in
`EffectLower` is where a leg acquires meaning. Carrying a leg does not make an AIR right; it makes
the AIR SAYABLE from the spec, which is the thing that was missing.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom. Imports read-only; ADDITIVE (the one consumer edit is
`EffectSpec2`'s new defaulted field, which leaves every existing instance compiling).
-/
import Dregg2.Circuit.TableAirIR

namespace Dregg2.Circuit.EffectAirIR

open Dregg2.Circuit (Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (TableId TableDef WindowExpr ChalExpr PROOF_BIND_MIN_LANES)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.TableAirIR (BusOp RowSel readsNext)

set_option autoImplicit false

/-! ## §1 — the four leg shapes, and the ORDERED list that carries them. -/

/-- **A LOOKUP leg** — the +51 capability. The queried table, the tuple (expressions in the
framework's OWN gate AST `Circuit.Expr`, so a spec author writes the same language the guard gates
are written in), the per-row MULTIPLICITY expression, and which SIDE of the bus this is.

`mult` and `op` are TableAirIR's two fields, carried here even though the deployed MAIN rail takes
neither: a source language that cannot say "this query is conditional" cannot describe a padded
row, and the honest response is a REFUSAL at the lowering (`mainRailOk`), not a vocabulary that
pretends the distinction does not exist. -/
structure LookupLeg where
  table : TableId
  tuple : List Expr
  /-- Per-row multiplicity. `.const 1` is the unconditional case the main rail hardcodes. -/
  mult  : Expr := .const 1
  /-- Which side of the bus. A main descriptor only ever `.query`s. -/
  op    : BusOp := .query

/-- **A ROW-SELECTED gate leg** — TableAirIR's `RowSel` over its `WindowExpr`. This is the (c)
capability: `EffectSpec2` was single-row, so `.transition` continuity, first/last-row boundary
fixes, and two-row window gates were all unsayable. -/
structure WindowLeg where
  sel  : RowSel
  body : WindowExpr

/-- ⚑ **A CHALLENGE leg** (2026-08-05) — the (f) capability, and the one the sound Pasta multiply
was BLOCKED on.

`PastaFieldSound.lean` recorded the block as a finding: *"The cheap escape from `O(limbs²)` is a
randomized-challenge identity … **It is not expressible in this IR.** … Adding a challenge leaf is a
change to the IR and the prover, not to a descriptor."* This is the source-language half of that
change; `DescriptorIR2.ChalExpr` is the target half.

A `ChalLeg` is a `WindowLeg` whose body may additionally read `chal i` — the `i`-th Fiat–Shamir
value the VERIFIER draws, after the main trace is committed. `sel` carries the same `RowSel`
vocabulary and the same refusals: only `.transition` and `.all` have deployed images, because the
target's `chalGate` is a two-row form with an `onTransition` flag and no first/last variant.

⚠ It declares its own challenge requirement implicitly (the largest `chal` index in the body); the
descriptor's `"challenges"` header is derived from it, and `check_descriptor2` refuses a body that
reads past what the instance's lookup contexts supply. -/
structure ChalLeg where
  sel  : RowSel
  body : ChalExpr

/-- **A RANGE leg** — the (b) capability: a wire pinned into `[0, 2^bits)`. The field-soundness
tooth (`VmRange.holds`); transfer's deployed v1 descriptor carries two and `EffectSpec2` could name
neither.

⚠ **ONE wire, ONE width — and that is exactly its limit.** A `RangeLeg` can pin a quantity only up
to one field element's worth of magnitude, because the wire IS one field element. It cannot say
"this quantity is `Σ limbᵢ · 2^(bits·i)`". See `LimbsLeg`. -/
structure RangeLeg where
  wire : Nat
  bits : Nat
  deriving Repr, DecidableEq

/-- ⚑ **A LIMBED-QUANTITY leg — the (e) capability, and the one the peer-chain light clients were
BLOCKED on.**

## The measured gap (2026-08-03, `1dcebacf8` and its own docblock)

Three light-client verify AIRs declared range widths of 64 and 128 over BabyBear, where the interval
already contains the whole field, so eight lookups refused nothing. All three were narrowed to 29 —
the maximum wrap-free width (`RangeFieldContainment.wrap_free_iff_le_29`). That was correct AND it
exposed the limit the vacuous widths had been hiding, in the repair's own words:

> Real Tendermint allows `MaxTotalVotingPower ≈ 2^60` and real Solana total stake is ≈2^58. **Those
> tallies never fit a BabyBear column at ANY declared width** — `TOTAL_POW` is one felt and one felt
> holds 30.9 bits. The wide declarations did not make them fit, they made the shortfall invisible.
> Full-width tallies need limb decomposition OF THE TALLY, which `EffectAirIR`'s range leg cannot
> express (one `.lookup`, one `.var`, one width). **That is the IR-expressibility finding.**

`RangeLeg` is `⟨wire, bits⟩`. A tally is a LIST. This leg is that list: `cols` are the limb columns
LEAST-significant first, and the quantity they denote is `Σᵢ a colsᵢ · 2^(bits·i)`
(`Dregg2.Circuit.LimbTally.limbValue`, where the arithmetic and its soundness live).

Sourced maxima this exists to reach (measured live 2026-08-03): CometBFT `MaxTotalVotingPower =
int64(math.MaxInt64)/8 = 2^60 − 1` (`types/validator_set.go:27`); Solana mainnet-beta active stake
`432650183925625587` lamports (2^58.59) against a `u64` type ceiling; Midnight GRANDPA authority
weight, which is **1 per seat** and totals 130 live (`pallet-grandpa` emits `(k, 1)`), against the
same `u64` type ceiling. -/
structure LimbsLeg where
  /-- Trace columns holding the limbs, **LEAST-significant first**. -/
  cols  : List Nat
  /-- Per-limb width; the radix is `2^bits`. Each limb gets its own range lookup at this width. -/
  bits  : Nat
  /-- Which declared range table the per-limb checks query. Defaults to the shared `.range`; a
  descriptor mixing widths routes the narrow one through a width-tagged `.custom` table (the
  `rangeTidW` family the deployed avail-weld already carries). -/
  table : TableId := .range
  deriving Repr, DecidableEq

/-- The number of range lookups this leg lowers to: one per limb. -/
def LimbsLeg.lookupCount (l : LimbsLeg) : Nat := l.cols.length

/-- The magnitude this leg can represent: `2^(bits · limbs)`. -/
def LimbsLeg.capacityBits (l : LimbsLeg) : Nat := l.bits * l.cols.length

/-- ⚑ **A RECURSION-BIND leg — the (g) capability** (2026-08-05), and the one the Mina light client
was BLOCKED on.

`DescriptorIR2.ProofBind` is the target's recursion seam: a row declares that its `commit` column is
the public-input commitment of a VERIFYING external sub-proof whose program VK is its `vk` column,
and (since 2026-08-04) carries two DECLARED halves the row-local gate checks those columns against —
`vkPin`, the program literal, and `bound`, the row expression the commitment must equal.

⚠ Until this leg existed, **no COMPILED descriptor could emit one**: `AirLeg` had no constructor for
it, so the only `proofBind`s in the tree were in hand-written `VmConstraint2` lists. A light client
that wants its carrier to be the output of a sub-proof rather than a bit could therefore either give
up the compiler (house law #1) or give up the seam. This is the source-language half.

⚑ **AND IT REFUSES THE DECLARATIVE SHAPE.** `BindLeg.mainRailOk` is FALSE when `vkPin` is `none`
AND `bound` is a PORT (2026-08-10: `bound`'s `none` became a NAMED port) — the shape `ProofBind.isDeclarative` counts and `proofBindDeclarative` exists to
ratchet down. A compiled AIR cannot say "bound to a verifying proof of SOME program about SOMETHING";
the unpinned form remains reachable only from the hand-written Custom descriptor, whose whole job is
to dispatch an arbitrary registered cell program. A leg that named neither would lower to the
UNSATISFIABLE pair, never to silence.

⚑ **AND IT IS A LANE VECTOR (2026-08-05).** `commit`/`vk`/`bound` were ONE expression each while
the objects they tie are eight felts, so a compiled seam was worth `2^31`. They are lane lists now,
and `mainRailOk` refuses a seam narrower than `DescriptorIR2.PROOF_BIND_MIN_LANES` as flatly as it
refuses the unpinned shape — the containment cannot be re-shipped through the compiler. -/
structure BindLeg where
  /-- The selector column/expression; the seam forces it boolean. -/
  guard  : Expr
  /-- The row's sub-proof public-input commitment LANES, low limb first. -/
  commit : List Expr
  /-- The row's sub-proof program-VK LANES, low limb first; same length as `commit`. -/
  vk     : List Expr
  /-- ⚑ The DECLARED program VK LANES this row recursion-binds to, as literals. ⚠ Still an
  `Option`, and still the same defect the `bound` half shed on 2026-08-10 — see
  `DescriptorIR2.ProofBind.vkPin`. -/
  vkPin  : Option (List ℤ)
  /-- ⚑ What holds the `commit` lanes — row-local expressions, or a NAMED port
  (`DescriptorIR2.CommitBinding` — read its docblock for the flag day). -/
  bound  : DescriptorIR2.CommitBindingOf Expr

/-- ⚑ **The main rail's verdict on ONE bind leg** — two refusals, and both are the same lesson.

*Shape*: a bind that pins NEITHER the program nor the commitment is `ProofBind.isDeclarative`, whose
existential quantifies over every program and every statement.

*Width*: a bind narrower than `PROOF_BIND_MIN_LANES` ties a LIMB of the object it names — `2^31` a
lane against a ~124-bit bar — and a pin that names fewer lanes than the vector it pins is a
truncation. The source cannot say either.

⚑ **2026-08-06 — `commit` AND `vk` ARE MEASURED SEPARATELY, and the coupling that was here was an
artifact.** This predicate required `vk.length == commit.length`. That is true of the Custom effect,
where both objects are eight felts (`custom_proof_pi_commitment` and `bytes32_to_8_limbs`), and it
was read off that pair rather than derived — with the consequence that **a seam could never name a
statement wider than a program fingerprint.** The two lengths measure different things: `commit` is
the width of the SENTENCE the sub-proof proves, `vk` the width of the PROGRAM identity. A Mina
state-hash seam names SIX `Fp` elements (the salt's three sponge lanes, the parent, the body hash
and the block hash = 54 lanes) against a nine-lane `Faithful9` fingerprint, and under the old
conjunct the only way to say it was to widen the fingerprint to 54 lanes — i.e. to lie about the
program's identity in order to state the sentence. Both floors still bite; neither is relaxed. -/
def BindLeg.mainRailOk (b : BindLeg) : Bool :=
  !(b.vkPin.isNone && b.bound.isPort)
    && decide (PROOF_BIND_MIN_LANES ≤ b.commit.length)
    && decide (PROOF_BIND_MIN_LANES ≤ b.vk.length)
    && (match b.vkPin with | none => true | some vs => vs.length == b.vk.length)
    && (match b.bound with
        | .port c   => c.namesOk
        | .bound bs => bs.length == b.commit.length)

/-- **A PI-PIN leg** — the (d) capability. `EffectSpec2`'s lowering could pin only FIRST-row PIs
(the `PIBindsDigests` surface); a deployed boundary contract pins both ends. -/
structure PiPinLeg where
  row : VmRow
  col : Nat
  idx : Nat
  deriving Repr, DecidableEq

/-- **One leg of an effect's AIR** — ⚑ ONE ORDERED LIST, not four parallel ones.

`EffectVmDescriptor2.constraints` is a SINGLE ordered `List VmConstraint2`, and the deployed
descriptors interleave freely (`merkle-membership-depth2.json` is lookup · lookup · gate ·
pi_binding · boundary). A source that held four parallel lists could only ever emit
gates-then-lookups-then-windows-then-pins, so it could not say what the target admits — the same
class of defect this whole phase exists to close, one level down. Measured over the 76 by-name
descriptors: **4 are byte-reachable with parallel lists, 8 with this ordered list.**

`gate` rides here too (not only in the spec's own `guardGates`) so a spec can place a gate
BETWEEN two lookups. -/
inductive AirLeg where
  /-- A flat `lhs = rhs`, lowered through the `Head` NORMALIZER like every other spec gate. -/
  | gate   (c : Constraint)
  | lookup (l : LookupLeg)
  | window (w : WindowLeg)
  | pin    (p : PiPinLeg)
  /-- ⚑ A LIMBED QUANTITY — a range-checked limb VECTOR, the vocabulary a tally needs. -/
  | limbs  (l : LimbsLeg)
  /-- ⚑ A CHALLENGE GATE — a two-row body that may read the verifier's drawn randomness. -/
  | chal   (c : ChalLeg)
  /-- ⚑ A RECURSION BIND — the row's claim about an external sub-proof, with the program and the
  commitment DECLARED so the claim is checkable. -/
  | bind   (b : BindLeg)

/-- **`EffectAir` — the AIR block an `EffectSpec2` carries beyond its flat guard gates.**

`legs` is ordered because the target's constraint array is. `tables` and `ranges` are separate
because the target's `tables` and `ranges` are separate JSON arrays, not constraints.

Every field defaults to empty, which is what makes the widening ADDITIVE: an existing
`EffectSpec2` instance that names none of these is unchanged, and `lowerEffect` on it emits
byte-identically to Phase 1 (`EffectLower.lowerEffect_air_empty`). -/
structure EffectAir where
  /-- Tables this effect DECLARES (an `exactPublicRows` roster, a chip, a range limb table…). -/
  tables  : List TableDef := []
  /-- The constraint legs, IN EMISSION ORDER. -/
  legs    : List AirLeg   := []
  ranges  : List RangeLeg := []
  /-- PI slots this air block claims BEYOND the framework's own `PIBindsDigests` surface. -/
  extraPi : Nat           := 0

/-! ## §2 — the DECIDABLE main-rail verdict.

Three refusals, each naming the target constructor that cannot hold the source leg. -/

/-- Is this expression the literal constant `1`? (The one multiplicity `Ir2Air::Main` implements.) -/
def exprIsOne : Expr → Bool
  | .const k => k == 1
  | _        => false

/-- ⚑ **The main rail's verdict on ONE lookup leg.** `DescriptorIR2.Lookup` is `⟨table, tuple⟩`:
there is no multiplicity field and no side field, so a leg with either is not expressible. -/
def LookupLeg.mainRailOk (l : LookupLeg) : Bool :=
  (l.op == BusOp.query) && exprIsOne l.mult

/-- ⚑ **The main rail's verdict on ONE window leg**, and the two reasons are different:

* `.transition` — the ONLY scope where `nxt` is the genuine successor. Anything goes.
* `.all` — TableAirIR's refusal: on the last row p3's `next` is the WRAP row.
* `.first` / `.last` — these lower to `VmConstraint.boundary`, whose body evaluates against
  `env.loc` alone. The target has no next-row leaf at all. -/
def WindowLeg.mainRailOk (w : WindowLeg) : Bool :=
  match w.sel with
  | .transition => true
  | .all        => !readsNext w.body
  | .first      => !readsNext w.body
  | .last       => !readsNext w.body

/-- Does a `ChalExpr` read the NEXT row? (The `.all` refusal below, and TableAirIR's reason for it:
on the last row p3's `next` is the WRAP row, so an every-row body that reads `nxt` says something
different there than it says everywhere else.) -/
def chalReadsNext : ChalExpr → Bool
  | .nxt _ => true
  | .loc _ | .const _ | .chal _ => false
  | .add a b | .mul a b => chalReadsNext a || chalReadsNext b

/-- ⚑ **The main rail's verdict on ONE challenge leg.** Same shape as `WindowLeg.mainRailOk` and
for the same reasons — except that `.first` and `.last` are refused OUTRIGHT rather than
conditionally, because the target's `chalGate` has only the two-row form: there is no
`boundary`-with-challenges constructor to lower a first/last challenge gate into, and lowering one
into an every-row gate would change WHERE it fires. A refusal, not a reinterpretation. -/
def ChalLeg.mainRailOk (c : ChalLeg) : Bool :=
  match c.sel with
  | .transition => true
  | .all        => !chalReadsNext c.body
  | .first      => false
  | .last       => false

/-- ⚑ **The main rail's verdict on ONE limbs leg — and it is the one place this IR REFUSES A WIDTH.**

Two refusals, and each names a way the leg would be a decoration rather than a check:

* **An EMPTY limb vector.** `limbValue` of `[]` is `0` and it range-checks nothing, so a leg with no
  columns would silently assert `0 ≥ 0` — a quantity that is not there. This is the same shape as a
  dropped lookup: it accepts strictly more, invisibly.
* **A width at or above 30.** ⚑ This is the CENSUS, structural. `RangeFieldContainment` proved a
  range table at `≥ 31` bits contains the whole BabyBear field (refuses nothing) and that 30 is not
  wrap-free either (`not_wrap_free_at_30`; `wrap_free_iff_le_29`). Three shipped descriptors had to
  be found by an audit and repaired by hand. A limbed quantity is exactly the construct that removes
  any reason to want a wide limb — you add limbs, you do not widen them — so this IR refuses the
  width class outright rather than leaving it to a future census. -/
def LimbsLeg.mainRailOk (l : LimbsLeg) : Bool :=
  !l.cols.isEmpty && 0 < l.bits && l.bits ≤ 29

/-- ⚑ **The main rail's verdict on ONE leg.** A `gate` and a `pin` always have an image; a
`lookup`, a `window`, a `limbs`, a `chal` and a `bind` may not. -/
def AirLeg.mainRailOk : AirLeg → Bool
  | .gate _   => true
  | .pin _    => true
  | .lookup l => l.mainRailOk
  | .window w => w.mainRailOk
  | .limbs l  => l.mainRailOk
  | .chal c   => c.mainRailOk
  | .bind b   => b.mainRailOk

/-- Every declared PI pin indexes a slot the descriptor actually declares. A pin past `piCount`
is a wire-format defect the Rust decoder would read as an out-of-range public input. -/
def EffectAir.pinsFit (air : EffectAir) (piCount : Nat) : Bool :=
  air.legs.all (fun l => match l with | .pin p => p.idx < piCount | _ => true)

/-- **`EffectAir.mainRailOk`** — the decidable verdict that this air block is expressible as
constraints of a deployed MAIN `EffectVmDescriptor2`. -/
def EffectAir.mainRailOk (air : EffectAir) : Bool := air.legs.all AirLeg.mainRailOk

/-! ## §3 — shape counts, so a re-emission that DROPS a leg moves a number.

`TableAirIR.busCount`/`gateCountSel` exist for exactly this reason: a lost bus leg is invisible to
a denotation that quantifies over gates only. Same discipline, same shape. -/

/-- The leg's kind tag — the discriminator the per-kind counts filter on. -/
def AirLeg.kind : AirLeg → String
  | .gate _ => "gate" | .lookup _ => "lookup" | .window _ => "window" | .pin _ => "pin"
  | .limbs _ => "limbs" | .chal _ => "chal" | .bind _ => "bind"

/-- Kind tags are collision-free: the tag determines the constructor's arm. -/
theorem AirLeg.kind_of (l : AirLeg) :
    (l.kind = "gate") ∨ (l.kind = "lookup") ∨ (l.kind = "window") ∨ (l.kind = "pin")
      ∨ (l.kind = "limbs") ∨ (l.kind = "chal") ∨ (l.kind = "bind") := by
  cases l <;> simp [AirLeg.kind]

def EffectAir.kindCount   (air : EffectAir) (k : String) : Nat :=
  (air.legs.filter (fun l => l.kind == k)).length
def EffectAir.lookupCount (air : EffectAir) : Nat := air.kindCount "lookup"
def EffectAir.windowCount (air : EffectAir) : Nat := air.kindCount "window"
def EffectAir.gateCount   (air : EffectAir) : Nat := air.kindCount "gate"
def EffectAir.pinCount    (air : EffectAir) : Nat := air.kindCount "pin"
def EffectAir.limbsCount  (air : EffectAir) : Nat := air.kindCount "limbs"
/-- ⚑ The number of RECURSION BINDS the air block declares — the count a re-emission that dropped a
sub-proof obligation would move while every other shape count sat still. -/
def EffectAir.bindCount   (air : EffectAir) : Nat := air.kindCount "bind"
def EffectAir.rangeCount  (air : EffectAir) : Nat := air.ranges.length
def EffectAir.tableCount  (air : EffectAir) : Nat := air.tables.length

/-- ⚑ **The total number of range lookups the air block lowers to** — the one-wire `ranges` array
PLUS one per limb of every limbed quantity. A limbed tally is not one lookup; a re-emission that
dropped a limb would move this number while `rangeCount` sat still. -/
def EffectAir.totalRangeLookups (air : EffectAir) : Nat :=
  air.ranges.length
    + (air.legs.map (fun l => match l with | .limbs q => q.lookupCount | _ => 0)).sum

/-- The largest magnitude (in bits) any single limbed quantity in this block can represent. `0` when
the block carries none — which is what every descriptor emitted before this widening carried. -/
def EffectAir.maxLimbedCapacityBits (air : EffectAir) : Nat :=
  (air.legs.map (fun l => match l with | .limbs q => q.capacityBits | _ => 0)).foldl max 0

/-- The window legs under a given selector — so a pin names WHICH scope lost a gate
(`TableAirIR.gateCountSel`'s counterpart). -/
def EffectAir.windowCountSel (air : EffectAir) (s : RowSel) : Nat :=
  (air.legs.filter (fun l => match l with | .window w => w.sel == s | _ => false)).length

/-- The PI pins on a given row — first-row and last-row pins are different contracts. -/
def EffectAir.pinCountRow (air : EffectAir) (r : VmRow) : Nat :=
  (air.legs.filter (fun l => match l with | .pin p => p.row == r | _ => false)).length

/-- Total legs plus the two separately-carried arrays. `0` exactly on the empty air block. -/
def EffectAir.legCount (air : EffectAir) : Nat :=
  air.legs.length + air.rangeCount + air.tableCount

/-- Per-kind counts never exceed the leg total: a per-kind pin is a refinement of the whole. -/
theorem EffectAir.kindCount_le (air : EffectAir) (k : String) :
    air.kindCount k ≤ air.legs.length := by
  simpa [EffectAir.kindCount] using (air.legs.length_filter_le (fun l => l.kind == k))

/-- **The DEFAULT air block is empty** — the additivity fact the widening rests on. Every
`EffectSpec2` instance that names no air legs carries this, so its lowering is unchanged. -/
theorem EffectAir.default_legCount : ({} : EffectAir).legCount = 0 := rfl

/-- …and the empty block is trivially main-rail expressible (no leg, no refusal). -/
theorem EffectAir.default_mainRailOk : ({} : EffectAir).mainRailOk = true := rfl

/-! ## §4 — tripwires. Both polarities of every refusal, on the EMITTED predicate. -/

/-- An unconditional query — the shape a main descriptor takes. -/
def demoQuery : LookupLeg := ⟨.custom 30, [.var 0, .var 1, .var 2], .const 1, .query⟩

/-- The SAME tuple served rather than asked. No main-rail image: `Lookup` has no side field. -/
def demoProvide : LookupLeg := { demoQuery with op := .provide }

/-- The same query at a CONDITIONAL multiplicity (a padded row sends nothing). No main-rail
image: `Ir2Air::Main` hardcodes multiplicity 1. -/
def demoConditional : LookupLeg := { demoQuery with mult := .var 3 }

#guard demoQuery.mainRailOk == true
#guard demoProvide.mainRailOk == false
#guard demoConditional.mainRailOk == false

/-- A transition continuity leg reading the next row — the legal `nxt` scope. -/
def demoCont : WindowLeg := ⟨.transition, .add (.nxt 0) (.mul (.const (-1)) (.loc 2))⟩

/-- The SAME body re-scoped to `.all`. Byte-identical algebra, and REFUSED: on the last row p3's
`next` is the wrap row. This is `TableGate.transition_weakens` seen from the source side. -/
def demoContAll : WindowLeg := { demoCont with sel := .all }

/-- A row-local boundary fix — no `nxt`, so `.last` is fine. -/
def demoLastFix : WindowLeg := ⟨.last, .add (.loc 5) (.mul (.const (-1)) (.loc 4))⟩

#guard demoCont.mainRailOk == true
#guard demoContAll.mainRailOk == false
#guard demoLastFix.mainRailOk == true
#guard (WindowLeg.mk .first (.nxt 0)).mainRailOk == false

/-- An air block exercising every leg kind, with a `gate` INTERLEAVED between two lookups — the
shape four parallel lists could not express. -/
def demoAir : EffectAir :=
  { tables  := [⟨.custom 30, "dfa_transition_table", 3, .exactPublicRows [[0, 1, 1]]⟩]
  , legs    := [ .lookup demoQuery
                , .gate ⟨.var 4, .const 0⟩
                , .window demoCont
                , .window demoLastFix
                , .pin ⟨.first, 0, 0⟩
                , .pin ⟨.last, 2, 1⟩ ]
  , ranges  := [⟨7, 30⟩]
  , extraPi := 2 }

#guard demoAir.mainRailOk == true
#guard demoAir.legCount == 8
#guard demoAir.legs.length == 6
#guard demoAir.lookupCount == 1
#guard demoAir.gateCount == 1
#guard demoAir.windowCount == 2
#guard demoAir.pinCount == 2
#guard demoAir.windowCountSel .transition == 1
#guard demoAir.windowCountSel .last == 1
#guard demoAir.windowCountSel .all == 0
#guard demoAir.pinCountRow .first == 1
#guard demoAir.pinCountRow .last == 1
#guard demoAir.pinsFit 2 == true
#guard demoAir.pinsFit 1 == false

-- ⚑ THE REFUSAL POLE: one `.provide` leg turns the WHOLE block inexpressible. A verdict that
-- cannot go red is decoration; this is the red.
#guard ({ demoAir with legs := [.lookup demoProvide] } : EffectAir).mainRailOk == false
#guard ({ demoAir with legs := [.window demoContAll] } : EffectAir).mainRailOk == false

-- The default block, both facts, executed rather than asserted.
#guard ({} : EffectAir).legCount == 0
#guard ({} : EffectAir).mainRailOk == true

/-! ### §4b — the LIMBED leg's tripwires, as NAMED THEOREMS.

⚠ `metatheory/docs/GUARD-DISCIPLINE.md`: a `#guard` produces no term, is invisible to
`#assert_axioms`, and is the case-testing this repo forbids in Rust. The legs above predate the
policy; nothing added here uses one. -/

/-- A four-limb `u64` tally at the deployed limb width — the shape a real validator set takes. -/
def demoTally : LimbsLeg := { cols := [9, 10, 11, 12], bits := 16 }

/-- **It is main-rail expressible**, and it lowers to four range lookups rather than one. -/
theorem demoTally_mainRailOk : demoTally.mainRailOk = true := by decide

/-- ⚑ **AND IT REPRESENTS 64 BITS** — the capability that did not exist. The `RangeLeg` it replaces
tops out at one field element, and BabyBear is 30.9 bits. -/
theorem demoTally_capacity : demoTally.capacityBits = 64 := by decide

/-- One lookup per limb, so a dropped limb moves a number. -/
theorem demoTally_lookupCount : demoTally.lookupCount = 4 := by decide

/-- ⚑ **THE FIRST REFUSAL POLE: an EMPTY limb vector.** It would denote `0` and check nothing —
a quantity that is not there, asserted as if it were. -/
theorem empty_limb_vector_is_refused : ({ demoTally with cols := [] } : LimbsLeg).mainRailOk = false := by
  decide

/-- ⚑ **THE SECOND REFUSAL POLE, AND IT IS THE CENSUS MADE STRUCTURAL.** A limb at 31 bits — the
width class `RangeFieldContainment.range_vacuous_at_or_above_31` proved refuses nothing over
BabyBear, and the class three shipped descriptors sat in until an audit found them — is refused by
the IR's own verdict. It cannot be authored, so it cannot be emitted. -/
theorem vacuous_limb_width_is_refused :
    ({ demoTally with bits := 31 } : LimbsLeg).mainRailOk = false := by decide

/-- …and the refusal starts one bit BELOW containment, at the wrap-free ceiling: 30 is refused too.
30-bit range tables are not vacuous, but they admit negatives of magnitude `> p − 2^30`
(`large_negative_admitted_at_30`), and a limbed quantity has no reason to want one — you add a limb.
The last ADMITTED width is 29. -/
theorem non_wrap_free_limb_width_is_refused :
    ({ demoTally with bits := 30 } : LimbsLeg).mainRailOk = false := by decide

/-- The boundary, both sides, so the constant is a real edge and not a taste. -/
theorem limb_width_boundary_is_29 :
    ({ demoTally with bits := 29 } : LimbsLeg).mainRailOk = true
      ∧ ({ demoTally with bits := 30 } : LimbsLeg).mainRailOk = false := by decide

/-- ⚑ **ONE BAD LIMBS LEG TURNS THE WHOLE BLOCK INEXPRESSIBLE** — the verdict propagates, exactly as
it does for a `.provide` lookup. A verdict that cannot go red is decoration. -/
theorem air_with_vacuous_limbs_is_refused :
    ({ demoAir with legs := [.limbs { demoTally with bits := 64 }] } : EffectAir).mainRailOk
      = false := by decide

/-- An air block carrying a limbed tally counts it, and reports the range lookups it really lowers
to — four, not one. `totalRangeLookups` is the number a dropped limb moves. -/
theorem air_with_tally_counts :
    (({ legs := [.limbs demoTally, .gate ⟨.var 0, .const 0⟩], ranges := [⟨7, 29⟩] } : EffectAir)
      |> fun air => (air.limbsCount, air.totalRangeLookups, air.maxLimbedCapacityBits))
      = (1, 5, 64) := by decide

/-- **ADDITIVITY IS PRESERVED**: the default air block still carries no limbed quantity, so every
descriptor emitted before this widening is unchanged. -/
theorem default_carries_no_limbs :
    ({} : EffectAir).limbsCount = 0 ∧ ({} : EffectAir).totalRangeLookups = 0
      ∧ ({} : EffectAir).maxLimbedCapacityBits = 0 := by decide

#assert_axioms AirLeg.kind_of
#assert_axioms EffectAir.kindCount_le
#assert_axioms EffectAir.default_legCount
#assert_axioms EffectAir.default_mainRailOk
-- The limbed-quantity widening: capability, both refusal poles, propagation, additivity.
#assert_axioms demoTally_mainRailOk
#assert_axioms demoTally_capacity
#assert_axioms empty_limb_vector_is_refused
#assert_axioms vacuous_limb_width_is_refused
#assert_axioms non_wrap_free_limb_width_is_refused
#assert_axioms limb_width_boundary_is_29
#assert_axioms air_with_vacuous_limbs_is_refused
#assert_axioms air_with_tally_counts
#assert_axioms default_carries_no_limbs

end Dregg2.Circuit.EffectAirIR
