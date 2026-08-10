/-
# `Dregg2.Circuit.Emit.LightClientAnchorConnectivity` — WHICH light clients relate their claimed block
to the evidence they check. Measured on all seven served descriptors, as named theorems.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this file authors NO AIR. It reads seven already-emitted
`EffectVmDescriptor2` values and states decidable facts about them. Nothing here changes a shipped
object, so nothing here rotates a VK or re-genesises anything.

## The measurement, and why it is a measurement and not an opinion

A `pi_binding` ties one trace column to one public input. It ties it to **nothing else**. So build the
COLUMN-CONNECTIVITY GRAPH of an emitted descriptor — two columns adjacent iff they co-occur in one
constraint that RELATES them: a gate body, a boundary body, a window-gate body, a lookup tuple, a
transition pair, a hash site, a mem/map/umem/proof bus op — and read off the connected components.

**A PI-bound column whose component is a SINGLETON is related to nothing the circuit checks.** The
proof carries its value; no gate is about it. `decorativeAnchors` computes exactly that list, and the
six theorems below pin it, per descriptor, to an explicit literal.

`loc c` and `nxt c` are the SAME column: a window gate relating `loc 9` to `nxt 0` is a genuine edge
`9—0`. That is how `dregg-mina-lightclient-link::v1` earns its `[]`.

⚠ **AN ARITY-1 RANGE LOOKUP READS A COLUMN AND RELATES IT TO NOTHING.** It bounds a shape; it does
not tie a value to the evidence. Counting a 29-bit lane bound as "bound" is exactly the laundering
this file refuses — so `relatedCols` returns a constraint's columns and the predicate additionally
demands there be **two of them**. `LightClientSolanaAir`'s §6b `constraintCols` does not draw that
line (its anchors carry no lookups at all, so it never had to); `minaLcVerifyDesc`'s eighteen state
limbs DO carry lane lookups, and they are decorative all the same.

## ⚑ THE ANSWER, IN THE REGISTER THE MEASUREMENT SUPPORTS

⚑⚑ **2026-08-08 — THE INSTRUMENT WAS COMPLICIT, AND THIS HEADER'S NUMBERS MOVED WHEN IT STOPPED.**
`relatedCols`' `.proofBind` arm unioned a seam's `commit`/`vk` DECLARATIONS into the connectivity
graph unconditionally, while `descriptor_ir2.rs` emits polynomials over `commit` only under
`if let Some(b) = &p.bound` and over `vk` only under a `vk_pin` — and every served seam is
`bound := none`. So the census counted columns that appear in NO emitted constraint as joined, and
its `18 → 9` was quoted as gate coverage. The arm is now emission-faithful (one entry per emitted
polynomial of arity ≥ 2); the DECLARATION reading survives as `declaredCols`, under a name that
says what it counts. Where a bullet below describes a seam "joining" its commitment, read it
through that split: the vk half is emitted polynomials; the commit half is a DECLARED PORT whose
forcing is a named off-row weld — covered for the verify rung's anchor, tip and chainlink blocks
(`MinaSeams`: the `headTipSeam` object; REFUSAL 4), and ⚑ since 2026-08-08 for its conjunction
block (REFUSAL 15, `check_conjunction_binding` — DEAD CODE for the two days before, wired the day
this census counted it) and for the link rung's body columns (REFUSAL 16,
`check_body_chain_binding` — the seventeen-slot executor weld against the body chain's root).

Seven served descriptors. **Three of them relate their published values to anything, and only one of
those two relates them to something the prover did not choose.**

* the Mina LINK rung joins twenty published columns to a chain of WITNESSED lane values;
* ⚑ the Solana STAKE-TABLE FOLD (2026-08-04) joins twelve to the output columns of two deployed
  Poseidon2 chip absorbs. Its published root is the IMAGE of the exhibited rows, not a value equal
  to another witness — which is the distinction this file's `minaLink_decorative_anchors` caveat was
  written to keep visible, now on the other side of it;
* ⚑⚑ and **the Solana VERIFY rung**, which absorbed that fold the same day: twelve of its
  twenty-two published columns are the fold's, and the ten that are not are the bank root and the
  slot.

⚑⚑ **2026-08-04, SECOND PASS: THE SOLANA VERIFY RUNG ABSORBED THE FOLD, AND THREE THEOREMS IN THIS
FILE WENT RED SAYING SO** (`sol_decorative_anchors`, `sol_anchors_are_unread`, the census). That is
the mechanism, not a defect in it. Solana is `19 → 10` and the census `71 → 62`; the nine `.first`
anchor-root limbs are gone and the light client's trust anchor is the fold's eight `.last` output
lanes. A fourth, `sol_pinned_denominator_is_not_decorative`, stayed GREEN while ceasing to be about
the denominator — its columns `[4,5,6,7]` are now `ROOT_IN 4..7` — and repointing it at `[37,38,39,40]`
is the repair that a red would not have prompted.

**The other four VERIFY descriptors are unchanged: fifty-two decorative anchors, none of their
literals moved.** What repairing them costs is the same shape as what repairing Solana's cost: pick a
commitment the prover can afford, and derive the anchor instead of publishing it.

* **`dregg-eth-lightclient-verify::v1`** — `{0} / {1..3}{9} / {4} / {5} / {6} / {7} / {8} / {10}…{20}`.
  ELEVEN of eleven anchors inert, and UNREAD: no constraint of any kind names them, not even a width
  lookup. *The prover exhibited a participation count between 342 and 512 against a committee size it
  also pinned to 512, set three bits to 1, chose a branch depth from `{6,7}` and one equal to 4, and
  separately exhibited eleven public field elements.* Nothing relates the claimed sync-committee root
  or the nine finalized-state-root limbs to the count.

* **`dregg-tm-lightclient-verify::v1`** — `{0..1} / {2..3} / {4..11} / {12} / {13} / {14} / {15..49} /
  {50}…{60}`. ELEVEN of eleven inert and UNREAD. *The prover exhibited two voting-power limb vectors
  satisfying `1 ≤ total`, `signed ≤ total` and `3·signed > 2·total`, exhibited five more numbers
  standing in a time-window relation with three range-checked slacks, asserted that two columns it
  chose are equal and that two others differ by one, set three bits to 1, and separately exhibited
  eleven public field elements.* ⚑ Sharpest here: the chain-id equality holds between **two witnessed
  columns** (`CHAIN_ID` 0, `TS_CHAIN_ID` 1) while the PUBLIC chain-id domain is column 60, in no gate.
  The circuit checks that the prover agreed with itself about which chain this is.

* **`dregg-midnight-lightclient-verify::v1`** — `{0} / {1} / {2} / {3} / {4..38} / {39}…{50}`. TWELVE
  of twelve inert and UNREAD. *The prover exhibited two weight limb vectors satisfying `1 ≤ total`,
  `signed ≤ total` and `3·signed > 2·total`, set four bits to 1, and separately exhibited twelve
  public field elements.* ⚑ `ROUND_OK` (col 2) and `ERA_OK` (col 3) are forced bits; the PUBLISHED
  round and era are columns 49 and 50 and appear in no gate. Nothing relates the bit that is named
  "this precommit names the claimed round" to the claimed round.

* **`dregg-solana-lightclient-verify::v1`** — ⚑ **THE ONE THAT MOVED (2026-08-04).** It read
  `{0}{1}{2}{3} / {4..29} / {30}…{40}`, eleven of eleven inert and UNREAD. It now reads
  `{0}{1}{2}{3} / {4..29} / {30}…{48}`, and the tally component `{4..29}` CONTAINS FOUR PI-BOUND
  COLUMNS — the total-stake limbs 4..7 (`LightClientSolanaAir.totalStakePins`). *The prover exhibits a
  `(total, rooted)` pair clearing `total ≥ 1` and `3·rooted > 2·total`, sets four bits to 1, and
  exhibits nineteen public values — **but `total` is no longer one of the numbers it gets to choose**;
  it is in the public statement, supplied by the light client from its weak-subjectivity anchor.* The
  nineteen decorative anchors are the nine `ANCHOR_ROOT` limbs (widened from ONE 31-bit column in the
  same commit — a 256-bit SHA-256 root that had been bound at 31 bits), the nine `BANK_ROOT` limbs and
  `SLOT_COL`. ⚠ The denominator is pinned; the stake TABLE is not (`LightClientSolanaAir` §6c prices
  the fold that would).

* ⚑⚑ **`dregg-mina-lightclient-verify::v1` — THE RUNG WHOSE "HALVING" WAS THE INSTRUMENT'S, AND
  WHOSE PORTS ARE NOW OBJECTS (2026-08-08).** It read `{0..7}{11} / {8} / {9} / {10} / {12}…{29}`,
  eighteen of twenty inert; the 2026-08-05 declaration of the `LINK_OK`-guarded `proofBind` was
  scored as a join and the literal "halved" to nine. Emission-faithful it carries **THIRTY-SIX**:
  the anchor nonet, the tip nonet, and the two nine-lane sub-proof-commitment blocks. *The prover
  exhibits a segment length, an anchor height, a submission height and three range-checked slacks
  in an additive relation; publishes the derived block length, the required depth and the anchor
  height; sets four bits to 1; and publishes twenty-seven lanes of tip and sub-proof commitments
  that no emitted polynomial names beside another column — while the three seams' vk halves force
  twenty-seven PROGRAM lanes to descriptor literals under genuinely-joined guards.*
  ⚑ The three commit blocks are DECLARED PORTS: the tip covered elementwise against the link
  sub-proof (REFUSAL 13, called and both-polarity tested, now also the emitted `headTipSeam`
  object), the chainlink commitment by digest recompute (REFUSAL 4, `check_transcript_binding`,
  called and tested) — and, since 2026-08-08, the conjunction commitment by the SAME shape
  (REFUSAL 15, `check_conjunction_binding`, called and tested). ⚑ That weld was DEAD CODE for the
  two days before — defined, never called, no wire field, no test — counted while it stood by
  `MinaSeams.the_conjunction_commitment_port_has_no_live_weld = 1`.
  ⚠ And the caveat that governs is the one `minaLink_decorative_anchors` already carries: the bound
  sub-proof chains WITNESSED lane values. The tip is the last element of a committed chain whose
  SHAPE is gated; its HASH derivation rides sibling sub-proofs no node yet requires.
  ⚑ Corrections the measurement forced, ONE OF WHICH IS NOW REPAIRED (2026-08-05):
  - ✅ the anchor HEIGHT (`ANCHOR_H`, col 1) WAS a free witness — not PI-bound, not range-looked-up,
    and pinned to no constant, while `LightClientMinaAir` called it "the pinned weak-subjectivity
    anchor's blockchain length". It is now **PI-bound at slot 29**
    (`minaVerify_anchor_height_is_published`), so the consumer can refuse it against the height the
    operator pinned instead of seeing only the sum;
  - ⚠ **STILL OPEN, and the pin did not touch it:** the anchor STATE HASH (cols 12..20) and the
    anchor HEIGHT (col 1) share no constraint at all, because a `piBinding` contributes no edge by
    construction. "The published height is the pinned anchor plus the exhibited segment" is now a
    relation among two prover-chosen numbers and one PUBLISHED one, and nothing in-circuit says the
    published height is the height OF the published hash
    (`minaVerify_anchor_height_shares_no_constraint_with_the_hash`).
  The lane bounds are real and strictly stronger than canonicality (`8·29 + 22 = 254`,
  `2^254 < p_Pasta`) — but they bound each lane of a value tied to nothing.

* ⚑ **`dregg-solana-stake-table-fold::v1`** — `{0..43}`, ONE component, **zero of twelve anchors
  decorative**. *The prover exhibits a sequence of rows, each absorbing the running eight-lane state
  and its own pubkey lanes into an arity-16 Poseidon2 chip row, then that result and its own stake
  limbs into a second — and publishes the LAST row's state as the table's commitment and the LAST
  row's four-limb accumulator as the active-stake denominator.* ⚑ The two publications come from the
  SAME rows, which is what makes a swapped validator set with an IDENTICAL tally move the root
  (`FoldScheme.same_tally_moves_the_root`; on the deployed prover,
  `circuit/tests/solana_stake_table_fold.rs`, 11/11 release).
  ⚠ It binds the DENOMINATOR's provenance and nothing else: `ED_OK` is still a witnessed carrier in
  the sibling rung, the numerator is still a witnessed projection, and the join between the two rungs
  is at the PUBLIC STATEMENT (the verifier compares four felts), not inside one proof.

* **`dregg-mina-lightclient-link::v1`** — `{0}{9} / {1}{10} / … / {8}{17} / {18}{21} / {19..20}`,
  plus seventeen body columns. **The twenty chain columns are related; the seventeen body-flag-day
  columns are DECLARED and UNWELDED — the one uncovered port surface in this census.** *The prover
  exhibited a sequence of rows in which each row's nine-lane `OWNHASH` equals the next row's
  nine-lane `PARENT`, the heights tick by one from a first-row anchor height, a boolean `IS_REAL`
  is monotone and its running sum is published as the segment length — and the anchor and tip it
  publishes are the two ends of that chain.*
  ⚑ **2026-08-06/08 — `OWNHASH`, RE-SAID AT EMISSION RESOLUTION.** The state-hash `proof_bind`
  against `dregg-pasta-fp-absorb::v1` DECLARES `salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH` per row and
  emits only its nine `HASH_VK` forcings
  (`minaLink_state_hash_seam_declares_the_row_and_emits_only_the_program_pin`); the derivation is
  the absorb sub-proofs the declaration names, welded today by tests, required by no node. Every
  lane pair is still its own island for the CHAINING gates — lane `j` chains to lane `j` and never
  crosses.
  ⚠ **AND THE BINDING TO MINA IS AN EXECUTOR WELD, NOT A CONSTRAINT.** `BODYHASH` is PUBLISHED
  (PI 20..28, with the chain's 8-lane accumulator at 29..36) so a fold can reach it — and none
  does; what reads the seventeen since 2026-08-08 is `turn`'s `check_body_chain_binding`
  (REFUSAL 16): `BODY_ACC` elementwise against `MinaStateBodyHashChain`'s root `transcript_acc`,
  `BODYHASH` against the `Faithful9` re-limbing of its squeezed lane 0, the chain head against
  the `MinaProtoStateBody` salt, under a second operator-pinned recursion anchor.
  `minaLink_decorative_anchors` still counts the seventeen — an executor weld adds no emitted
  polynomial — and `MinaSeams.the_link_body_ports_are_weld_covered` names the cover (it stood as
  `…_have_no_registered_cover = 2` until the weld landed). **Connectivity is co-occurrence, not
  derivation — and a declaration is neither.**

## ⚑ WHY THESE ARE THEOREMS AND NOT A COMMENT — they are meant to go RED

The in-AIR-crypto iteration is exactly the change that makes an anchor column appear beside another
column in a gate: `BLS_OK` derived from `COMMITTEE_ROOT`, `STAKE_TABLE_OK` from the table fold into
`ANCHOR_ROOT`, `AUTHSET_OK` from the set fold, `LINK_OK` from the Poseidon chain. **The day any of
them lands, the corresponding theorem below FAILS.** Shrinking its literal is then the correct move;
weakening the statement is not. A comment saying the same thing rots silently.

The predicate is SATISFIABLE, REFUTABLE and NOT PROVABLE in general
(`feedback-prove-the-floor-false`): `solStakeFold_decorative_anchors` exhibits `[]`, the others
exhibit non-empty lists, and no lemma here derives either from the shape of a descriptor.

Companion gate: `scripts/check-descriptor-anchor-inertness.py` runs the same decomposition over all
84 served descriptors as a ratchet (`scripts/descriptor-anchor-inertness-baseline.txt`), so a NEW
descriptor cannot be served with unbound public inputs without moving a committed number.
-/
import Dregg2.Circuit.Emit.LightClientEthAir
import Dregg2.Circuit.Emit.LightClientTendermintAir
import Dregg2.Circuit.Emit.LightClientMidnightAir
import Dregg2.Circuit.Emit.LightClientSolanaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
import Dregg2.Circuit.Emit.LightClientSolStakeFoldAir

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- ⚑ 2026-08-05: `minaVerify_anchor_height_shares_no_constraint_with_the_hash` decides a nested
-- quantifier over (nine columns × every constraint of the Mina head descriptor), and the segment
-- bind took that descriptor to 63 constraints — one past the default depth. `set_option` does not
-- cross an import, so it is stated here rather than inherited from `LightClientMinaAir`.
set_option maxRecDepth 4000

namespace Dregg2.Circuit.Emit.LightClientAnchorConnectivity

open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2

/-! ## §1 — the graph. Which columns does one constraint RELATE? -/

/-- Duplicate-free `cons` — keeps the column lists small enough that the arity test below is a
length test rather than a set comparison. -/
def nub : List Nat → List Nat
  | []      => []
  | c :: cs => let r := nub cs; if c ∈ r then r else c :: r

/-- The trace columns a row-local `EmittedExpr` reads. -/
def exprCols : EmittedExpr → List Nat
  | .var c   => [c]
  | .const _ => []
  | .add l r => exprCols l ++ exprCols r
  | .mul l r => exprCols l ++ exprCols r

/-- The trace columns a two-row `WindowExpr` reads. ⚑ `loc c` and `nxt c` are the SAME column: the
question is which columns a constraint JOINS, and a window gate relating `loc 9` to `nxt 0` joins
columns 9 and 0. -/
def windowCols : WindowExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .add l r => windowCols l ++ windowCols r
  | .mul l r => windowCols l ++ windowCols r

/-- ⚑ **THE COLUMNS A CHALLENGE BODY NAMES** (2026-08-05). `ChalExpr` is `WindowExpr` plus a `chal i`
leaf, and that leaf is **NOT A COLUMN**: it is a value the VERIFIER draws after the trace is
committed. Folding it in as a column would make every challenge gate join every other one through a
phantom node and silently connect anchors that share nothing — the exact laundering this file exists
to refuse. So `chal` contributes `[]`.

⚠ This replaces `windowCols w.body` in the `.chalGate` arm, which did not typecheck (`w.body` is a
`ChalExpr`) and left the whole module red once `TableAirIR` was rebuilt against the widened
`VmRowEnv`. -/
def chalCols : ChalExpr → List Nat
  | .loc c   => [c]
  | .nxt c   => [c]
  | .const _ => []
  | .chal _  => []
  | .add l r => chalCols l ++ chalCols r
  | .mul l r => chalCols l ++ chalCols r

/-- ⚑ **THE COLUMNS ONE CONSTRAINT RELATES.** A `piBinding` contributes NOTHING on purpose: it ties a
column to a PUBLIC INPUT, not to another column, so it cannot connect an anchor to the evidence. That
asymmetry is the whole thing being measured. Every OTHER form contributes all the columns it reads —
including the bus ops, so a descriptor that grows one cannot slip past this as a silent `[]`. -/
def relatedCols : VmConstraint2 → List Nat
  | .base (.gate b)          => nub (exprCols b)
  | .base (.boundary _ b)    => nub (exprCols b)
  | .base (.transition hi lo) => nub [hi, lo]
  | .base (.piBinding _ _ _) => []
  | .lookup l                => nub (l.tuple.flatMap exprCols)
  | .windowGate w            => nub (windowCols w.body)
  | .chalGate w              => nub (chalCols w.body)
  | .memOp m                 => nub ((exprCols m.guard) ++ (exprCols m.addr) ++ (exprCols m.value) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .umemOp m                => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.present) ++
                                     (exprCols m.value) ++ (exprCols m.prevPresent) ++
                                     (exprCols m.prevValue) ++ (exprCols m.prevSerial))
  | .mapOp m                 => nub ((exprCols m.guard) ++ (exprCols m.key) ++ (exprCols m.value) ++
                                     ((List.ofFn m.root).flatMap exprCols) ++
                                     ((List.ofFn m.newRoot).flatMap exprCols))
  -- ⚑⚑ **EMISSION-FAITHFUL SINCE 2026-08-08 — this arm counts POLYNOMIALS, not IR fields.**
  --
  -- Until today it unioned `guard ++ commit ++ vk ++ bound` UNCONDITIONALLY, while
  -- `descriptor_ir2.rs`'s `proofBind` arm emits polynomials over `commit` only under
  -- `if let Some(b) = &p.bound` and over `vk` only under `if let Some(pin) = &p.vk_pin`. Every
  -- seam served today declares `bound := none`, so **every `commit` lane the old walker scored as
  -- JOINED appeared in no emitted constraint at all** — and the `18 → 9` decorative-anchor census
  -- was quoted as gate coverage while measuring declarations. A census that counts declarations
  -- and reports coverage is worse than no census; this is the repair, not a relabel.
  --
  -- What the deployed evaluator emits (`descriptor_ir2.rs`, `VmConstraint2::ProofBind`;
  -- Lean `ProofBind.holdsAt` is the same `1 + n + n`):
  --
  --     guard·(guard − 1)                    always      — names the guard's columns only
  --     guard·(vkᵢ − vkPinᵢ)     per lane,   iff vkPin   — names guard ∪ vkᵢ
  --     guard·(commitᵢ − boundᵢ) per lane,   iff bound   — names guard ∪ commitᵢ ∪ boundᵢ
  --
  -- Each POLYNOMIAL relates its own columns, and only if it names two distinct ones: a vk-pin
  -- lane under a `.const 1` guard is `1·(vkᵢ − pin)` — a one-column forcing, the same arity-1
  -- shape as `ED_OK − 1`, and it joins nothing. The per-polynomial `poly` filter below is that
  -- rule; without it a constant-guarded seam would join its vk lanes to each other through a
  -- flat union no polynomial justifies.
  --
  -- ⚠ The DECLARATION-level reading (which columns does the seam NAME, forced or not) is still a
  -- real question — it is what a port declaration covers — and it moved to `declaredCols` below,
  -- under a name that says what it counts. Theorems that need it say so.
  | .proofBind m             =>
      let g := exprCols m.guard
      let poly : List Nat → List Nat := fun cs => if 2 ≤ (nub cs).length then cs else []
      let pinPolys : List Nat :=
        match m.vkPin with
        | none => []
        | some _ => m.vk.flatMap (fun lane => poly (g ++ exprCols lane))
      let boundPolys : List Nat :=
        match m.bound with
        -- ⚑ A PORT emits nothing over `commit`, exactly as the retired `none` did. The difference
        -- the 2026-08-10 flag day bought is upstream: the port NAMES its cover, so a reader can
        -- resolve what forces these columns instead of inferring silence.
        | .port _ => []
        | .bound bs => (m.commit.zip bs).flatMap
            (fun cb => poly (g ++ exprCols cb.1 ++ exprCols cb.2))
      nub (poly g ++ pinPolys ++ boundPolys)

/-- ⚑ **THE DECLARATION-LEVEL READER** — which columns a constraint NAMES, whether or not any
emitted polynomial forces them. Identical to `relatedCols` except at `.proofBind`, where it returns
the seam's whole IR surface: guard, every commit lane, every vk lane, every bound lane. This is the
old `.proofBind` arm of `relatedCols`, moved here under a name that says what it counts — a
`proofBind` with `bound := none` DECLARES its commit lanes (a port surface a weld must cover) and
FORCES none of them, and the two readings must never share a name again. Used by the
`…_is_declared_…` theorems below; never by `decorativeAnchors`. -/
def declaredCols : VmConstraint2 → List Nat
  | .proofBind m => nub ((exprCols m.guard) ++ (m.commit.flatMap exprCols) ++
                         (m.vk.flatMap exprCols) ++
                         (m.bound.lanes.flatMap exprCols))
  | c            => relatedCols c

/-- A constraint RELATES iff it names at least two distinct columns. ⚑ An arity-1 range lookup and a
one-column forcing gate (`ED_OK − 1`) both fail this, and both should: neither joins anything. -/
def joins (c : VmConstraint2) : Bool := 2 ≤ (relatedCols c).length

/-- Column `col` is PI-bound in `d`. -/
def isPiBound (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun
    | .base (.piBinding _ c _) => c == col
    | _                        => false

/-- Column `col` is READ by some constraint — any constraint, including an arity-1 range lookup. -/
def isRead (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun c => col ∈ relatedCols c

/-- Column `col` is RELATED: some constraint names it alongside another column. This is adjacency in
the connectivity graph, i.e. `col`'s component is not a singleton. -/
def isRelated (d : EffectVmDescriptor2) (col : Nat) : Bool :=
  d.constraints.any fun c => joins c && col ∈ relatedCols c

/-- ⚑⚑ **THE DECORATIVE ANCHORS OF `d`**, ascending: every PI-bound column that no constraint joins
to any other column. The proof carries these values; nothing in the circuit is about them. -/
def decorativeAnchors (d : EffectVmDescriptor2) : List Nat :=
  (List.range d.traceWidth).filter fun col => isPiBound d col && !isRelated d col

/-! ## §2 — the six served descriptors, each pinned to its exact list.

Every theorem below FAILS the day an anchor column enters a gate beside another column. That is the
point of them. -/

/-- ⚑ **ETHEREUM: all eleven published anchors are decorative.** Columns 10..20 —
`COMMITTEE_ROOT`, the nine `FIN_STATE_ROOT` limbs, `DOMAIN_GVR`. ⚠ TRIPWIRE: `BLS_OK` derived from
`COMMITTEE_ROOT`, or `EXEC_OK` from the execution branch fold, reds this. -/
theorem eth_decorative_anchors :
    decorativeAnchors LightClientEthAir.ethLcVerifyDesc = [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by
  decide

/-- …and Ethereum's are not merely unjoined, they are UNREAD: no constraint of any kind names them,
not even a width lookup. So the nine "radix-`2^31` MSB-first limbs" carry no limb-width bound either;
a prover may write any field element into each. -/
theorem eth_anchors_are_unread :
    ∀ col ∈ [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
      isRead LightClientEthAir.ethLcVerifyDesc col = false := by
  decide

/-- ⚑ **TENDERMINT: all eleven published anchors are decorative.** Columns 50..60 —
`TRUSTED_NEXT_VALS_ROOT`, the nine `COMMITTED_APP_HASH` limbs, `CHAIN_ID_DOMAIN`. -/
theorem tm_decorative_anchors :
    decorativeAnchors LightClientTendermintAir.tmLcVerifyDesc = [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60] := by
  decide

/-- …and unread, so the app-hash widening from one felt to nine limbs added nine columns and no
constraint. -/
theorem tm_anchors_are_unread :
    ∀ col ∈ [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60],
      isRead LightClientTendermintAir.tmLcVerifyDesc col = false := by
  decide

/-- ⚑ **AND THE CHAIN-ID EQUALITY IS BETWEEN TWO WITNESSES.** `CHAIN_ID` (0) and `TS_CHAIN_ID` (1) are
joined to each other and to nothing else; the PUBLIC `CHAIN_ID_DOMAIN` (60) is joined to nothing. So
the cross-chain-replay gate compares the prover's two copies of a number the verifier never sees. -/
theorem tm_chain_id_domain_is_not_the_chain_id_gate :
    isRelated LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID = true ∧
    isRelated LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.TS_CHAIN_ID = true ∧
    isPiBound LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID = false ∧
    isPiBound LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.TS_CHAIN_ID = false ∧
    isRead LightClientTendermintAir.tmLcVerifyDesc LightClientTendermintAir.CHAIN_ID_DOMAIN = false := by
  decide

/-- ⚑ **MIDNIGHT: all twelve published anchors are decorative.** Columns 39..50 — `ANCHOR_ROOT`, the
nine `TARGET_ROOT` limbs, `ROUND_COL`, `ERA_COL`. -/
theorem mid_decorative_anchors :
    decorativeAnchors LightClientMidnightAir.midLcVerifyDesc = [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50] := by
  decide

/-- …and unread. -/
theorem mid_anchors_are_unread :
    ∀ col ∈ [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50],
      isRead LightClientMidnightAir.midLcVerifyDesc col = false := by
  decide

/-- ⚑ **AND `ROUND_OK` / `ERA_OK` ARE NOT ABOUT THE PUBLISHED ROUND AND ERA.** The two bits are
columns 2 and 3, each forced `= 1` by a gate naming only itself; the published round and era are
columns 49 and 50 and are read by nothing. `LightClientMidnightAir:198-202` calls these the
"cross-round" and "stale-authority-set" bindings. They bind nothing. -/
theorem mid_round_and_era_bits_are_not_joined_to_the_published_round_and_era :
    isRead LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ROUND_COL = false ∧
    isRead LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ERA_COL = false ∧
    isRelated LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ROUND_OK = false ∧
    isRelated LightClientMidnightAir.midLcVerifyDesc LightClientMidnightAir.ERA_OK = false := by
  decide

/-- ⚑⚑⚑ **SOLANA — THIS LITERAL FIRED TWICE IN ONE DAY, AND THE SECOND TIME IT SHRANK BY NINE.**

Three readings, in order, because only the sequence makes the last one legible:

  * `[30 … 40]` — ELEVEN of eleven anchors decorative, every published column a singleton.
  * `[30 … 48]` — NINETEEN. `totalStakePins` took four columns OUT of the decorative set (the first
    columns in this census ever to leave it) while `ANCHOR_ROOT` widened from ONE 31-bit column to
    nine limbs, putting eight unrelated ones IN. *A raw count is the wrong summary of that change*,
    and the baseline header says so at length.
  * ⚑ **`[69 … 78]` — TEN, and this time the count and the meaning move together.** The nine
    `.first` anchor-root limbs are GONE — replaced by the stake-table fold's eight `.last` output
    lanes, which sit in the one component that contains the whole trace — and the denominator is the
    fold's accumulator. What remains decorative is the bank root (cols 69..77) and the slot (78).

*The prover exhibits a sequence of stake-table rows, absorbing each into an arity-16 Poseidon2 chip
row and accumulating its lamports; publishes the LAST row's eight-lane state as the light client's
weak-subjectivity anchor and the LAST row's four-limb accumulator as the denominator; exhibits a
rooted-stake numerator clearing `3·rooted > 2·total` against THAT denominator; sets three bits to 1;
and separately exhibits ten public field elements.* The ten are what is left. -/
theorem sol_decorative_anchors :
    decorativeAnchors LightClientSolanaAir.solLcVerifyDesc
      = [69, 70, 71, 72, 73, 74, 75, 76, 77, 78] := by
  decide

/-- …and those ten are unread: no constraint of any kind names them, not even a width lookup. -/
theorem sol_anchors_are_unread :
    ∀ col ∈ [69, 70, 71, 72, 73, 74, 75, 76, 77, 78],
      isRead LightClientSolanaAir.solLcVerifyDesc col = false := by
  decide

/-- ⚑⚑ **THE PUBLISHED TRUST ANCHOR IS RELATED — and this is the first anchor ROOT in the census that
is.** Each of the eight `ANCHOR_ROOT` lanes (cols 29..36) is PI-bound, READ, and RELATED, so none is
decorative. Mina-link's twenty joined columns were chained WITNESSES; these eight are the OUTPUT
columns of a deployed Poseidon2 chip absorb whose input tuple carries the stake rows.

⚠ The standing caveat still binds — connectivity is co-occurrence, not derivation. What upgrades
THESE eight is `DescriptorIR2.chip_lookup_sound_N` at the emitted tuple plus
`LightClientSolStakeFoldAir.FoldScheme.tableRoot_binds_or_collides`, and the number that governs is
`2^123.63` (birthday, over `8 · 30.906891 = 247.26` bits) — **not** the `2^247.3` second-preimage
figure for the same object. -/
theorem sol_published_anchor_root_is_not_decorative :
    ∀ col ∈ [29, 30, 31, 32, 33, 34, 35, 36],
      isPiBound LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRead LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRelated LightClientSolanaAir.solLcVerifyDesc col = true ∧
      col ∉ decorativeAnchors LightClientSolanaAir.solLcVerifyDesc := by
  decide

/-- ⚑ **AND SO IS THE DENOMINATOR — at the FOLD'S ACCUMULATOR COLUMNS, which is where the literal
had to move.** It read `[4, 5, 6, 7]`, the dedicated total-stake block. Those columns are now
`ROOT_IN 4..7` and are read and related for a completely different reason, so the old statement stayed
**TRUE while ceasing to be about the denominator** — the quietest way a tripwire dies. The
denominator is cols 37..40. -/
theorem sol_pinned_denominator_is_not_decorative :
    ∀ col ∈ [37, 38, 39, 40],
      isPiBound LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRead LightClientSolanaAir.solLcVerifyDesc col = true ∧
      isRelated LightClientSolanaAir.solLcVerifyDesc col = true ∧
      col ∉ decorativeAnchors LightClientSolanaAir.solLcVerifyDesc := by
  decide

/-- ⚑⚑ **THE STATEMENT THE VERIFY RUNG COULD NOT MAKE UNTIL TODAY: its published anchor and its
evidence are in ONE constraint together.** Every published root lane co-occurs, in a SINGLE
constraint, with a pubkey lane and a stake limb — the second chip absorb's tuple. This is
`solStakeFold_root_shares_a_constraint_with_the_stake_rows`, now true of the LIGHT CLIENT and not only
of the standalone fold rung, because the light client absorbed the fold's legs. -/
theorem sol_anchor_root_shares_a_constraint_with_the_stake_rows :
    ∀ j ∈ [29, 30, 31, 32, 33, 34, 35, 36],
      LightClientSolanaAir.solLcVerifyDesc.constraints.any (fun c =>
        j ∈ relatedCols c
          && LightClientSolanaAir.VOTER 8 ∈ relatedCols c
          && LightClientSolanaAir.STAKE 0 ∈ relatedCols c) = true := by
  decide

/-- ⚑⚑⚑ **MINA VERIFY — THE LITERAL THAT HALVED ON A DECLARATION, RESTORED ON THE EMISSION.
THIRTY-SIX, NOT NINE.**

The history, kept because the sequence is the lesson:

  * `[12 … 29]` — anchor and tip, eighteen lanes joined to nothing.
  * `[12 … 20]` — NINE, 2026-08-05: the tip lanes "left" when the §2c `proofBind` named them —
    but that shrink was measured by an instrument that unioned `commit` UNCONDITIONALLY, while
    `descriptor_ir2.rs` emits polynomials over `commit` only under `if let Some(b) = &p.bound`,
    and every served seam is `bound := none`. **The 18 → 9 was quoted as gate coverage while
    measuring an IR field.**
  * ⚑ `[12 … 29] ++ [40 … 48] ++ [68 … 76]` — THIRTY-SIX, 2026-08-08, the instrument fixed:
    the anchor's nine, the tip's nine, the nine `SUB_PI` sub-proof-commitment lanes and the nine
    `CONJ_PI` conjunction-commitment lanes. Every one is PI-bound and **appears in no emitted
    polynomial that names a second column.** The three `proofBind`s force their guard bits and
    their `vk` lanes (real polynomials, counted below); their `commit` vectors they DECLARE.

⚠ **THIRTY-SIX DECORATIVE ANCHORS IS NOT THIRTY-SIX WOUNDS — BUT IT IS NINE MORE THAN THE COVERS
CLAIMED, AND SAYING WHICH IS THE POINT.** These blocks are the seams' PORT SURFACES, declared in
`MinaSeams` §8b: the anchor and tip ports are covered by the emitted head↔link seam (`headTipSeam`
— the executor's REFUSAL 13/14 as an object, both polarities tested), the chainlink-commitment
port by the named, CALLED, tested weld `check_transcript_binding` (REFUSAL 4), and ⚑ since
2026-08-08 the conjunction-commitment port by `check_conjunction_binding` (REFUSAL 15) — which was
DEAD CODE for the two days before: defined, documented, called by nothing, no wire field, no test,
the "constructed zero times" class, counted while it stood by
`MinaSeams.the_conjunction_commitment_port_has_no_live_weld = 1` and retired by the wiring
(`MinaSeams.conjPiWeld`; wire fields REQUIRED so old blobs refuse to decode; both polarities in
`turn`'s REFUSAL-15 suite).
This literal reds the day any of the four blocks enters an emitted polynomial, at which point the
honest move is to shrink it and retire the corresponding port. -/
theorem minaVerify_decorative_anchors :
    decorativeAnchors LightClientMinaAir.minaLcVerifyDesc
      = [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29,
         40, 41, 42, 43, 44, 45, 46, 47, 48, 68, 69, 70, 71, 72, 73, 74, 75, 76] := by
  decide

/-- ⚑ **AND THIS IS THE CASE `constraintCols` ALONE WOULD MISS — restored to the EIGHTEEN state
lanes.** The anchor and tip lane columns ARE read — each by an arity-1 range lookup at 29 or 22
bits — and joined to nothing an emitted polynomial names beside them. A width bound is a fact about
a value's SHAPE; it is not a tie to the evidence, and a census that counted "appears in a lookup
tuple" as bound would have scored all eighteen as connected.

⚑ This theorem narrowed from `[12 … 29]` to the anchor nine on 2026-08-05 when the segment bind's
DECLARATION was scored as a join; with the instrument emission-faithful it covers the eighteen
again. The tip half is a covered PORT (`MinaSeams.headTipSeam`), not an oversight — see the
decorative literal's docblock for the split. -/
theorem minaVerify_state_lanes_are_read_but_never_joined :
    ∀ col ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29],
      isRead LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRelated LightClientMinaAir.minaLcVerifyDesc col = false := by
  decide

/-- ⚑⚑⚑ **THE TIP, SAID AT THE RESOLUTION THE EMISSION SUPPORTS: PUBLISHED AND DECLARED, NOT
JOINED.** Each of the nine `TIP_STATE` lanes is PI-bound (a real emitted `piBinding` forces the
column to the statement, so a consumer can refuse a tip against the link sub-proof it verifies),
READ (a width lookup), NOT related by any emitted polynomial — and DECLARED, all nine, by the
`LINK_OK`-guarded `proofBind` whose `vkPin` is `dregg-mina-lightclient-link::v1`'s fingerprint.

This theorem was named `…_published_and_joined` until 2026-08-08 and asserted `isRelated = true`,
which was TRUE ABOUT THE WRONG OBJECT: the instrument scored the seam's `commit` DECLARATION as a
join while `bound := none` emits no polynomial over these columns. The declaration is real and load-
bearing — it is the port surface `MinaSeams.headTipSeam` covers, and the executor's REFUSAL 13
discharges elementwise (`8·29 + 24 = 256` bits, no digest, no birthday bound) — but it is a PORT,
and the fourth conjunct now says so in the language the emission supports. -/
theorem minaVerify_tip_lanes_are_published_and_declared :
    ∀ col ∈ [21, 22, 23, 24, 25, 26, 27, 28, 29],
      isPiBound LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRead LightClientMinaAir.minaLcVerifyDesc col = true ∧
      isRelated LightClientMinaAir.minaLcVerifyDesc col = false ∧
      LightClientMinaAir.minaLcVerifyDesc.constraints.any
        (fun c => col ∈ declaredCols c
          && LightClientMinaAir.LINK_OK ∈ declaredCols c
          && LightClientMinaAir.LINK_VK 0 ∈ declaredCols c
          && LightClientMinaAir.LINK_VK 8 ∈ declaredCols c) = true := by
  decide

/-- ⚑⚑ **AND THE SEAM'S EMITTED POLYNOMIALS ARE THE PROGRAM PIN — a REAL join, at the vk half.**
The `LINK_OK`-guarded seam emits `guard·(guard−1)` and nine `guard·(LINK_VK i − pin_i)` — so the
carrier and the nine attested-program columns ARE in emitted polynomials together, and `LINK_OK`
costs a prover nine lane congruences against a descriptor literal, not one felt. What the seam does
NOT emit is any polynomial over its `commit` lanes; that half is the covered port above. This split
— vk half forced, commit half ported — is the whole shape of a `bound := none` seam, stated where
the census can keep it honest. -/
theorem minaVerify_link_seam_forces_the_program_pin_not_the_tip :
    (∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8],
      isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.LINK_VK i) = true) ∧
    isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.LINK_OK = true ∧
    (∀ i ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8],
      isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.TIP_STATE i) = false) := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### ⚑⚑ THE RECURSION RUNG, MEASURED HERE RATHER THAN ASSUMED — RE-MEASURED 2026-08-08.

`dregg-mina-lightclient-verify::v1` grew its recursion shape in two steps (width 30 → 49 → 77, PIs
20 → 29 → 39) as `PICKLES_OK` became `WRAP_FS_PROVED` + `FINALIZE_XI_B_PROVED` and their
`proof_bind` legs. The 2026-08-05/06 reading — *"every added commitment lane lands JOINED, because
a `proof_bind` relates its guard, its commitment and its vk column"* — was the INSTRUMENT's
reading, not the emission's: with `bound := none` the deployed evaluator emits nothing over a
`commit` lane, so the eighteen commitment lanes are published, DECLARED, and forced off-row by the
named executor welds. The theorems below say exactly that split:

* the vk halves are REAL emitted polynomials — guard·(vkᵢ − pinᵢ) — so both carriers and all
  eighteen program lanes are genuinely joined;
* the commit halves are PORTS: `check_transcript_binding` (REFUSAL 4) recomputes the chainlink
  sub-proof's PI digest and refuses lanes 20..28; `check_conjunction_binding` (REFUSAL 15) the
  conjunction's at 30..38. Both welds carry both polarities in `turn`'s release tests, and
  `MinaSeams` declares the two ports with those welds as their covers. -/

/-- ⚑⚑ **THE NINE SUB-PROOF COMMITMENT LANES ARE PUBLISHED AND DECLARED — and NOT joined by any
emitted polynomial.** PI-bound (so the executor weld can reach them), declared by the
`WRAP_FS_PROVED`-guarded seam, and decorative under the emission-faithful census — the port state,
counted rather than narrated. The piCount and decorative-count conjuncts pin the descriptor's whole
published surface at the same moment so a shape drift cannot hide in this theorem's blind spot. -/
theorem minaVerify_subproof_commitment_is_published_and_declared :
    ((List.range 9).all fun i =>
        isPiBound LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_PI i)
          && !(isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_PI i))
          && LightClientMinaAir.minaLcVerifyDesc.constraints.any
               (fun c => LightClientMinaAir.SUB_PI i ∈ declaredCols c
                 && LightClientMinaAir.WRAP_FS_PROVED ∈ declaredCols c)) = true
      ∧ LightClientMinaAir.minaLcVerifyDesc.piCount = 39
      ∧ (decorativeAnchors LightClientMinaAir.minaLcVerifyDesc).length = 36 := by
  refine ⟨by decide, rfl, by decide⟩

/-- ⚑⚑ **AND THE NINE FINALIZE-CONJUNCTION COMMITMENT LANES, SAME SPLIT** (declared 2026-08-06,
re-measured 2026-08-08). The commit lanes are published and declared, not joined; the guard is
genuinely joined — to the nine `CONJ_VK` columns its seam forces to the conjunction descriptor's
fingerprint, which is what `FINALIZE_XI_B_PROVED = 1` costs in-circuit. `FINALIZE_XI_B_PROVED` is
NOT PI-bound, for the reason `WRAP_FS_PROVED` is not: a carrier a verifier could set from outside
the proof would be no carrier. -/
theorem minaVerify_conjunction_commitment_is_published_and_declared :
    ((List.range 9).all fun i =>
        isPiBound LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_PI i)
          && !(isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_PI i))) = true
      ∧ isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.FINALIZE_XI_B_PROVED = false
      ∧ isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.FINALIZE_XI_B_PROVED = true
      ∧ ((List.range 9).all fun i =>
          isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.CONJ_VK i)) = true := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- ⚑ **AND THE GUARD IS IN THE SAME COMPONENT AS THE PROGRAM IT PINS** — one bind, nine vk lanes,
each `guard·(vkᵢ − pinᵢ)` an emitted polynomial joining the carrier to a program column, so the
recursion carrier is not a bit sitting on its own island. This survives the 2026-08-08 instrument
fix because the vk half of a seam IS emitted; only the commit half was declaration. `WRAP_FS_PROVED`
is NOT PI-bound (a carrier a verifier could set from outside the proof would be no carrier), which is
why it never appears in the decorative census at all. -/
theorem minaVerify_recursion_guard_is_joined_and_hidden :
    isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.WRAP_FS_PROVED = false
      ∧ isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.WRAP_FS_PROVED = true
      ∧ ((List.range 9).all fun i =>
          isRelated LightClientMinaAir.minaLcVerifyDesc (LightClientMinaAir.SUB_VK i)) = true := by
  refine ⟨by decide, by decide, by decide⟩

/-- ⚑ **THE ANCHOR HEIGHT IS NOW PUBLISHED** — the flip of the former
`minaVerify_anchor_height_is_pinned_to_nothing`, on the emitted bytes (2026-08-05).

`ANCHOR_H` (col 1) is PI-bound at slot `PI_ANCHOR_H` and related, so it is neither hidden nor
decorative: a consumer holding the operator's anchor can compare the height the proof used against
the height it pinned, which is `dregg_turn::executor::mina_head_verifier`'s REFUSAL 2. Before this
leg the only published consequence of `ANCHOR_H` was the SUM `BLOCK_LEN`, and a prover picked the
summands.

⚠ **This is a PUBLICATION result, NOT a connectivity one** — see
`minaVerify_anchor_height_shares_no_constraint_with_the_hash` immediately below, which is the part
that did NOT change and is the honest residual. -/
theorem minaVerify_anchor_height_is_published :
    isPiBound LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = true ∧
    isRelated LightClientMinaAir.minaLcVerifyDesc LightClientMinaAir.ANCHOR_H = true := by
  refine ⟨by decide, by decide⟩

/-- ⚑⚑ **AND THE HEIGHT STILL SHARES NO CONSTRAINT WITH THE HASH. THIS IS THE RESIDUAL.**

`relatedCols` returns `[]` for a `piBinding` deliberately — a pin ties a column to a PUBLIC INPUT,
not to another column — so the 2026-08-05 pin above bought publication and bought **zero** edges.
IN-CIRCUIT, "the anchor" is still two unrelated prover choices: the height (col 1) and the state
hash (cols 12..20) appear in no common constraint. Nothing in this descriptor says the height is
the height OF that hash.

That join is a Mina-state lookup this descriptor does not perform, and it is not closed by anything
here. What closes the *consumer's* exposure is that both halves are refused against cell-program
state off-row; what would close the *circuit's* is a constraint that does not exist yet. Kept as a
theorem, in the affirmative, so it reds the day someone builds it — at which point the honest move
is to delete this and state the join. -/
theorem minaVerify_anchor_height_shares_no_constraint_with_the_hash :
    (∀ col ∈ [12, 13, 14, 15, 16, 17, 18, 19, 20],
      ∀ c ∈ LightClientMinaAir.minaLcVerifyDesc.constraints,
        col ∈ relatedCols c → LightClientMinaAir.ANCHOR_H ∉ relatedCols c) := by
  decide

/-- ⚑⚑ **THE MINA LINK RUNG: THE CHAIN'S TWENTY ARE JOINED; THE BODY FLAG DAY'S SEVENTEEN ARE
DECLARED, NOT JOINED.** The original twenty PI-bound columns remain genuinely connected — the nine
anchor lanes to the nine own-hash lanes by the per-lane continuity window gates, the anchor height
to the first row's height, the segment length to the `IS_REAL` accumulator. **The seventeen that
arrived on the 2026-08-08 publication flag day — nine `BODYHASH` lanes and eight `BODY_ACC` lanes —
appear in no emitted polynomial beside another column.** Both seams that name them carry
`bound := none` and a `.const 1` guard, so their emitted content is nine one-column vk forcings
each; the commit vectors are declarations.

⚑⚑ **AND SINCE 2026-08-08 THESE SEVENTEEN HAVE THEIR PRODUCTION COVER.** They stood as the one
port surface in this file with none — slot constants, a folded body-hash chain, and NO comparison
between the two that any node performed
(`MinaSeams.the_link_body_ports_have_no_registered_cover = 2`, the loud version of "publication
buys reachability, not the weld"). The weld is `turn`'s `check_body_chain_binding` (REFUSAL 16,
both polarities tested; the wire REQUIRES the body-chain root so an old blob refuses to decode),
censused as `MinaSeams.bodyHashWeld`/`bodyAccWeld` with
`the_link_body_ports_are_weld_covered = []`. ⚠ This literal does NOT shrink for it: an executor
weld adds no emitted polynomial, and the day a fold `cb.connect`s these slots in-circuit is the
day this literal moves. -/
theorem minaLink_decorative_anchors :
    decorativeAnchors LightClientMinaLinkAir.minaLinkDesc
      = [22, 23, 24, 25, 26, 27, 28, 29, 30, 40, 41, 42, 43, 44, 45, 46, 47] := by
  decide

/-- ⚑ **THE TWENTY CHAIN COLUMNS STAY JOINED — the flip side, so a disconnect cannot hide in the
literal above.** This is the residue of the retired `minaLink_decorative_anchors = []`: the anchor
nonet, the own-hash nonet at the tip pin, the height and the count are all still related by real
window gates, and this reds if someone disconnects a lane — the shape `broken_link_refused` exists
to catch, stated on the emitted object. -/
theorem minaLink_chain_columns_are_joined :
    ∀ col ∈ (List.range 9).flatMap (fun j => [j, 9 + j]) ++ [18, 20, 21],
      isRelated LightClientMinaLinkAir.minaLinkDesc col = true := by
  decide

/-- ⚑⚑⚑ **THE STATE-HASH SEAM, AT THE RESOLUTION THE EMISSION SUPPORTS: IT DECLARES THE PREIMAGE
AND THE IMAGE; IT EMITS ONLY THE PROGRAM PIN.**

Until 2026-08-08 this theorem read `relatedCols` off constraint 51 and concluded the seam *"names,
in ONE constraint, all thirty-six columns … one component"* — the instrument's reading of a
DECLARATION. The emission: the seam's guard is `.const 1` (booleanity trivially zero), its `vkPin`
emits nine ONE-COLUMN forcings `1·(HASH_VK i − pin_i)`, and its 54-lane commit vector —
`salt ‖ PARENT ‖ BODYHASH ‖ OWNHASH` — enters **no polynomial at all** (`bound := none`,
`descriptor_ir2.rs`'s `if let Some(b) = &p.bound` arm). So in emitted algebra the seam pins a
program identity and declares a per-row claim; the derivation `OWNHASH = Poseidon_salt(PARENT,
BODYHASH)` lives in the absorb sub-proofs the declaration names, welded today by TESTS
(`mina_statehash_seam_proves.rs`), by no node. Both facts below are `decide`d on the served bytes:
the declaration names all thirty-six columns; the emission relates none of them. -/
theorem minaLink_state_hash_seam_declares_the_row_and_emits_only_the_program_pin :
    (∀ col ∈ (List.range 9).flatMap (fun j => [j, 9 + j, 22 + j, 31 + j]),
      col ∈ (((LightClientMinaLinkAir.minaLinkDesc.constraints.drop 51).take 1).flatMap
        declaredCols)) ∧
    (((LightClientMinaLinkAir.minaLinkDesc.constraints.drop 51).take 1).flatMap
        relatedCols) = [] := by
  refine ⟨by decide, by decide⟩

/-- ⚑⚑⚑ **REPORT: THE RE-AIMED TRIPWIRE FIRED, AND THAT IS THE MECHANISM WORKING.**

The history, because only the sequence makes this legible:

  * The ORIGINAL trigger was *"it reds the day `state_body_hash` acquires its own sub-proof."* That
    rung landed on 2026-08-07 (`Circuit.Emit.MinaStateBodyHashChain` — 25 links of the deployed
    `dregg-pasta-fp-chainlink::v1` from the pinned `MinaProtoStateBody` salt) and **every literal
    here was unchanged**, because the derivation was a SIBLING CHAIN welded executor-side rather
    than a constraint in this descriptor. ⚠ **A watcher aimed at the right column and the wrong
    event.**
  * It was RE-AIMED the same day at `isPiBound = false`, with the trigger stated as the flag day:
    *"This reds the day `BODYHASH` is PI-bound, which is exactly the flag day … piCount 20 → 37."*
  * ⚑ **2026-08-08: THAT FLAG DAY LANDED AND THE RE-AIMED TRIPWIRE WENT RED.** `isPiBound` is now
    `true` on all nine columns and the old theorem's third conjunct is FALSE. This theorem is its
    replacement — RENAMED rather than annotated, because a theorem whose name says
    `is_joined_but_not_published` about a published column is a theorem about the wrong object.

⚑ **What the flag day bought, measured rather than described:** the nine `BODYHASH` columns are
PI-bound (slots 20..28) and the body-hash chain's EIGHT-lane ordered accumulator with them (40..47 →
slots 29..36), and both nonets are named by the body-chain `proofBind` whose `vkPin` is
`dregg-pasta-fp-chainlink::v1`'s fingerprint. A recursion fold reads `air_public_targets`, so the
weld to the chain's root is now REACHABLE — which is precisely what the unpublished shape forbade.

⚠ **AND WHAT THE WELD IS, in the same breath — re-measured 2026-08-08 with the instrument
fixed.** This theorem asserted `isRelated = true` off the seam's DECLARATION; the emission relates
none of these columns (`bound := none`, guard `.const 1`). Publication is reachability, not the
weld — and the weld that exists since the same day is the EXECUTOR's, not a fold's: no
`cb.connect` touches these 17 slots; `turn`'s `check_body_chain_binding` (REFUSAL 16) compares
them against the chain root's claim. The port surface stays measured decorative — an executor
weld adds no emitted polynomial (`minaLink_decorative_anchors`,
`MinaSeams.the_link_body_ports_are_weld_covered`). -/
theorem minaLink_body_hash_is_published_and_declared_not_joined :
    ∀ col ∈ [22, 23, 24, 25, 26, 27, 28, 29, 30],
      isRead LightClientMinaLinkAir.minaLinkDesc col = true ∧
      isRelated LightClientMinaLinkAir.minaLinkDesc col = false ∧
      isPiBound LightClientMinaLinkAir.minaLinkDesc col = true := by
  decide

/-- ⚑⚑⚑ **THE FIRING, AS A TERM.** `minaLink_body_hash_is_joined_but_not_published`'s third
conjunct was `isPiBound = false` on all nine columns; this says that claim is now REFUTABLE. A
tripwire that is merely *deleted* when its trigger arrives leaves no evidence it ever fired, which
is the failure the 08-07 re-aiming was itself a response to — so the firing is recorded as a theorem
rather than as a commit message. -/
theorem the_unpublished_body_hash_claim_is_now_refuted :
    ¬ (∀ col ∈ [22, 23, 24, 25, 26, 27, 28, 29, 30],
        isPiBound LightClientMinaLinkAir.minaLinkDesc col = false) := by decide

/-- ⚑⚑ **AND THE ACCUMULATOR IS PUBLISHED AND DECLARED TOO — which is the anti-vacuity half of the
DECLARATION.** `LightClientMinaLinkAir` §2c: *"a bind of `(salt, BODYHASH)` alone would be VACUOUS
… `perm` is a permutation, so 25 links from a fixed head with free absorbed inputs reach every
field element. Naming the stream is the whole content."* These eight columns ARE the stream,
ordered — the `seg_poseidon_commit` fold the chain's 25-leaf recursion publishes as
`transcript_acc`. Re-measured 2026-08-08: named by the seam, forced by nothing emitted — the same
port state as the `BODYHASH` nonet, and the same absent weld.

⚠ **AND THE EIGHT ARE NOT MERELY UNJOINED — THEY ARE UNREAD.** The `BODYHASH` nonet at least
carries per-lane width lookups; the accumulator lanes appear in NO constraint of any kind — not a
lookup, not a gate — the exact shape `eth_anchors_are_unread` names. The instrument fix surfaced
this: the old walker scored them "related" through the seam's declaration, which also hid that
nothing so much as bounds their width. A prover may write any field element into each.

⚠ **TRIPWIRE, AND SAY WHAT WOULD FIRE IT:** `minaLink_body_hash_is_named_by_the_body_chain_seam`
below reds the day the accumulator leaves the seam's commitment — exactly the shape a
"simplification" back to `(salt, BODYHASH)` would take; THIS one reds the day a constraint first
reads an accumulator lane, at which point say what reads it and shrink. -/
theorem minaLink_body_chain_accumulator_is_published_and_declared :
    ∀ col ∈ [40, 41, 42, 43, 44, 45, 46, 47],
      isRead LightClientMinaLinkAir.minaLinkDesc col = false ∧
      isRelated LightClientMinaLinkAir.minaLinkDesc col = false ∧
      isPiBound LightClientMinaLinkAir.minaLinkDesc col = true := by
  decide

/-- ⚑ **THE DECLARATION, STATED SO ITS SHAPE IS A TERM.** The nine body-hash columns and the eight
accumulator columns are named by the SAME `proof_bind` — the body-chain seam — so what a fold would
connect to and what the seam attests are one declared surface. `declaredCols`, and the name says
so: no emitted polynomial relates any of these seventeen
(`minaLink_state_hash_seam_declares_the_row_and_emits_only_the_program_pin` is the same fact for
the sibling seam). -/
theorem minaLink_body_hash_is_named_by_the_body_chain_seam :
    ∀ col ∈ [22, 23, 24, 25, 26, 27, 28, 29, 30, 40, 41, 42, 43, 44, 45, 46, 47],
      col ∈ (((LightClientMinaLinkAir.minaLinkDesc.constraints.drop 61).take 1).flatMap
        declaredCols) := by
  decide

/-- …and the count is exactly the thirty-seven the descriptor declares, so the `[]` above is a
statement about thirty-seven joined columns and not about an empty PI set. ⚑ **20 → 37 on the
2026-08-08 publication flag day**, and the seventeen that arrived are the nine `BODYHASH` lanes and
the eight body-chain accumulator lanes. -/
theorem minaLink_has_thirty_seven_pi_bound_columns :
    ((List.range LightClientMinaLinkAir.minaLinkDesc.traceWidth).filter
      fun col => isPiBound LightClientMinaLinkAir.minaLinkDesc col).length = 37 ∧
    LightClientMinaLinkAir.minaLinkDesc.piCount = 37 := by
  decide

/-- ⚑⚑⚑ **THE SOLANA STAKE-TABLE FOLD: NO DECORATIVE ANCHORS — AND, FOR THE FIRST TIME IN THIS
CENSUS, THE PUBLISHED VALUES ARE DERIVED RATHER THAN CHAINED.**

`dregg-solana-stake-table-fold::v1` publishes twelve values on its LAST row: the eight lanes of the
table's Poseidon2 commitment and the four limbs of the `u64` active-stake denominator. All twelve are
joined, and the component they sit in is the WHOLE TRACE.

⚠ Read the difference from `minaLink_decorative_anchors` carefully, because it is the whole point of
this rung. That descriptor earns its `[]` by chaining WITNESSED lane values with equality gates —
this file's own caveat says so: *"its evidence is numbers the prover chose."* Here the joining
constraints are two arity-16 chip lookups on the deployed Poseidon2 bus, whose eight output columns
are FORCED by `DescriptorIR2.chip_lookup_sound_N` against the chip table the genuine permutation
serves. The published root is not equal to a witness; it is the image of one. -/
theorem solStakeFold_decorative_anchors :
    decorativeAnchors LightClientSolStakeFoldAir.solStakeFoldDesc = [] := by
  decide

/-- …and the `[]` is a statement about TWELVE joined columns, not about an empty PI set. -/
theorem solStakeFold_has_twelve_pi_bound_columns :
    ((List.range LightClientSolStakeFoldAir.solStakeFoldDesc.traceWidth).filter
      fun col => isPiBound LightClientSolStakeFoldAir.solStakeFoldDesc col).length = 12 ∧
    LightClientSolStakeFoldAir.solStakeFoldDesc.piCount = 12 := by decide

/-- ⚑⚑ **THE STATEMENT NO OTHER DESCRIPTOR IN THIS CENSUS CAN MAKE: the published anchor and the
evidence are in ONE constraint together.**

Every published root lane co-occurs, in a SINGLE constraint, with a pubkey lane and with a stake
limb — the second chip absorb's tuple is `[16, MID₀…MID₇, VOTER₈, STAKE₀…STAKE₃, 0, 0, 0,
ROOT_OUT₀…ROOT_OUT₇]`, so the root columns and the row's own evidence columns are adjacent, not
merely in the same component by a long walk. And every published denominator limb co-occurs with the
row's stake limbs through the accumulator window gates.

⚠ Connectivity is still co-occurrence, not derivation — this file's standing caveat, and it binds
here too. What upgrades this from co-occurrence to derivation is not measured here: it is
`chip_lookup_sound_N` at the emitted tuple, and `LightClientSolStakeFoldAir.FoldScheme`'s
`tableRoot_binds_or_collides` / `same_tally_moves_the_root` over the fold the tuples compute. -/
theorem solStakeFold_root_shares_a_constraint_with_the_stake_rows :
    ∀ j ∈ [0, 1, 2, 3, 4, 5, 6, 7],
      LightClientSolStakeFoldAir.solStakeFoldDesc.constraints.any (fun c =>
        LightClientSolStakeFoldAir.ROOT_OUT j ∈ relatedCols c
          && LightClientSolStakeFoldAir.VOTER 8 ∈ relatedCols c
          && LightClientSolStakeFoldAir.STAKE 0 ∈ relatedCols c) = true := by
  decide

/-- …and the DENOMINATOR limbs are joined to the per-row stake limbs, so the number the sibling
verify rung's quorum divides by is the number these rows add up. -/
theorem solStakeFold_denominator_shares_a_constraint_with_the_row_stakes :
    ∀ i ∈ [0, 1, 2, 3],
      LightClientSolStakeFoldAir.solStakeFoldDesc.constraints.any (fun c =>
        LightClientSolStakeFoldAir.ACC i ∈ relatedCols c
          && LightClientSolStakeFoldAir.STAKE i ∈ relatedCols c) = true := by
  decide

/-! ## §3 — the census, as one number. -/

/-- ⚑ **THE ANSWER TO "HOW MANY OF OUR LIGHT CLIENTS RELATE THEIR CLAIMED BLOCK TO THE EVIDENCE THEY
CHECK?"** Eighty decorative anchors across the five VERIFY descriptors; seventeen on the LINK rung;
zero on the FOLD rung.

⚑ **THE SEQUENCE, BECAUSE A SINGLE NUMBER IS A BAD SUMMARY AND THIS FILE HAS SAID SO FOUR TIMES.**
`63 → 71 → 62 → 53 → 80 (+17)`. The rise to 71 was Solana's `ANCHOR_ROOT` widening from ONE 31-bit
column standing for a 256-bit SHA-256 root to nine radix-`2^31` limbs: eight more published columns,
none of them read. The fall to 62 is those nine limbs being DELETED and replaced by the stake-table
fold's eight `.last` output lanes, which are in the same component as the rows they commit to.

⚑⚑ **AND THE RISE TO 80 IS THE INSTRUMENT CONFESSING, NOT THE DESCRIPTORS REGRESSING — 2026-08-08.**
Not one descriptor byte moved. The falls to 53 and to 0-on-the-link were measured by a walker that
unioned a `proofBind`'s `commit` DECLARATION into the connectivity graph while `bound := none`
seams emit no polynomial over those lanes — declarations quoted as gate coverage. Emission-faithful,
the tip, the two sub-proof-commitment blocks and the link's seventeen body columns return to the
decorative set, WHERE THEY BELONG: they are PORT SURFACES. Mina-verify's thirty-six split as
covered ports (anchor + tip: the emitted `headTipSeam`; the chainlink block: REFUSAL 4, called and
tested; the conjunction block: REFUSAL 15 — dead code when this was first measured, wired the
same day, `MinaSeams.conjPiWeld`); the link's seventeen carry the REFUSAL-16 executor weld
(`MinaSeams.bodyHashWeld`/`bodyAccWeld`, `the_link_body_ports_are_weld_covered = []`, having
stood at `= 2` uncovered).

⚠ Anyone tightening this gate should count BITS-OF-PUBLIC-STATEMENT-UNBOUND, or the decorative
SHARE, not columns — and must never again let a count of DECLARATIONS stand in for a count of
CONSTRAINTS. Solana's `[69 … 78]` caveat stands: zero decorative anchors is the floor, not the
ceiling; its bank root and slot are still carried by no gate, `ED_OK` is still a witnessed carrier
and its numerator a witnessed projection. -/
theorem the_five_verify_descriptors_carry_eighty_decorative_anchors :
    (decorativeAnchors LightClientEthAir.ethLcVerifyDesc).length
      + (decorativeAnchors LightClientTendermintAir.tmLcVerifyDesc).length
      + (decorativeAnchors LightClientMidnightAir.midLcVerifyDesc).length
      + (decorativeAnchors LightClientSolanaAir.solLcVerifyDesc).length
      + (decorativeAnchors LightClientMinaAir.minaLcVerifyDesc).length = 80 ∧
    (decorativeAnchors LightClientMinaLinkAir.minaLinkDesc).length = 17 := by
  decide

/-! ## §4 — axiom hygiene. Named theorems, `#assert_axioms`, no `#guard`. -/

#assert_axioms eth_decorative_anchors
#assert_axioms eth_anchors_are_unread
#assert_axioms tm_decorative_anchors
#assert_axioms tm_anchors_are_unread
#assert_axioms tm_chain_id_domain_is_not_the_chain_id_gate
#assert_axioms mid_decorative_anchors
#assert_axioms mid_anchors_are_unread
#assert_axioms mid_round_and_era_bits_are_not_joined_to_the_published_round_and_era
#assert_axioms sol_decorative_anchors
#assert_axioms sol_anchors_are_unread
#assert_axioms sol_pinned_denominator_is_not_decorative
#assert_axioms sol_published_anchor_root_is_not_decorative
#assert_axioms sol_anchor_root_shares_a_constraint_with_the_stake_rows
#assert_axioms minaVerify_decorative_anchors
#assert_axioms minaVerify_subproof_commitment_is_published_and_declared
#assert_axioms minaVerify_conjunction_commitment_is_published_and_declared
#assert_axioms minaVerify_recursion_guard_is_joined_and_hidden
#assert_axioms minaVerify_state_lanes_are_read_but_never_joined
#assert_axioms minaVerify_tip_lanes_are_published_and_declared
#assert_axioms minaVerify_link_seam_forces_the_program_pin_not_the_tip
#assert_axioms minaVerify_anchor_height_is_published
#assert_axioms minaVerify_anchor_height_shares_no_constraint_with_the_hash
#assert_axioms minaLink_decorative_anchors
#assert_axioms minaLink_chain_columns_are_joined
#assert_axioms minaLink_state_hash_seam_declares_the_row_and_emits_only_the_program_pin
#assert_axioms minaLink_body_hash_is_published_and_declared_not_joined
#assert_axioms the_unpublished_body_hash_claim_is_now_refuted
#assert_axioms minaLink_body_chain_accumulator_is_published_and_declared
#assert_axioms minaLink_body_hash_is_named_by_the_body_chain_seam
#assert_axioms minaLink_has_thirty_seven_pi_bound_columns
#assert_axioms solStakeFold_decorative_anchors
#assert_axioms solStakeFold_has_twelve_pi_bound_columns
#assert_axioms solStakeFold_root_shares_a_constraint_with_the_stake_rows
#assert_axioms solStakeFold_denominator_shares_a_constraint_with_the_row_stakes
#assert_axioms the_five_verify_descriptors_carry_eighty_decorative_anchors

end Dregg2.Circuit.Emit.LightClientAnchorConnectivity
