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
in this file** — nine `.gate` legs, four `.lookup` legs against a declared range table, **two
`.limbs` legs and two narrow-table `.lookup` legs for the canonicality rung**, thirty-nine `.pin`
legs and **three nine-lane `.bind` legs**, and the `VmConstraint2`s are the compiler's business
(`minaHeadAir_leg_count = 60`, `minaLcVerifyDesc_constraint_count = 74`). It is the second deployed
descriptor in the
tree authored this way (`DfaRoutingTableEmit.tableRoutingDesc` was the first, 2026-08-01) and the
first authored that way from scratch rather than by fusing a hand-written twin.

The vocabulary was ADEQUATE, twice: `EffectAir.mainRailOk` is `true` by `rfl`
(`minaHeadAir_mainRailOk`), so no leg lowered to `EffectLower.refuseConstraints`. ⚑ The canonicality
rung needed the `.limbs` leg that landed for the peer-chain tallies — a nine-lane Pasta element is
exactly "a quantity no felt can hold", the construct that leg exists for — and needed **nothing
else**: no new `AirLeg` constructor, no new lowering, no hand-written gate. That is the finding,
stated plainly as §3 asks.

## ⚑ `blockchain_length` is a FUNCTION OF TWO WITNESSES here — the tooth is one module over

⚠ This heading used to read *"THE TOOTH: `blockchain_length` and the witnessed depth are DERIVED,
not witnessed"*, and the body below already retracts it. A heading a reader takes away unread is
the same claim as a paragraph; it is corrected here rather than left to be refuted three lines
down.

The wound this AIR exists to close is the one the `mina-tip` lane measured: a peer's reply was read
at 1,544 of 61,193 bytes, `tip.proof` was dropped, and *"what survived was `blockchain_length`, the
one field a liar sets for free."* An AIR that PUBLISHES `blockchain_length` as a free witness column
reproduces that defect in circuit form. So it is not a witness here:

    G1   BLOCK_LEN  =  ANCHOR_H + SEG_LEN            -- the published height IS anchor + evidence
    G2   WIT_DEPTH + SUBMIT_H  =  BLOCK_LEN          -- the depth IS measured to the derived tip

⚠ **CORRECTED 2026-08-03 — read G1 for what it says.** This section used to conclude *"a prover that
exhibits `n` blocks above the pinned anchor can publish exactly `anchorH + n` and nothing else."*
**That does not hold of THIS descriptor, and the reason is structural: `SEG_LEN` is column 0, a FREE
WITNESS, and this descriptor is SINGLE-ROW — it has no exhibited blocks at all.** The only thing
constraining `SEG_LEN` here is G3 (`SEG_SLACK + 1 = SEG_LEN`, `SEG_SLACK` ranged into `[0, 2^24)`),
so `SEG_LEN` is free in `[1, 2^24]` and `BLOCK_LEN` is free with it. G1 makes `BLOCK_LEN` a
*function of two witnesses* rather than a third independent one — which is real, and is strictly
less than "not settable at all". `minaLcAir_no_forgery` is honest about it in the only place it can
be: `hsl : a SEG_LEN = u.blocks.length` is a HYPOTHESIS the witness generator discharges, not a gate.

The tooth the sentence described now EXISTS, one module over:
`Circuit/Emit/LightClientMinaLinkAir.lean` is multi-row, one row per exhibited block, and its
`PI_SEG_LEN` is the LAST row's `REAL_COUNT` — so `link_seg_len_counts_the_real_rows` proves
`PI_SEG_LEN ≤ rows.length` from the committed trace. A claimed depth is paid for in rows there.

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

## NAMED verified CARRIERS — ⚑ ONE OF THE THREE IS NO LONGER A WITNESS, AND THE THIRD HAS BEEN SPLIT
TWICE

`LINK_OK` / `PICKLES_OPENING_WITNESSED` / `CANON_OK` are the three results `LightClientMinaGate`'s
wire gate takes as `lk` / `pk` / `cn`. They shipped here as witnessed boolean columns forced `= 1` —
pinned to the statement, so BENDING one is refused, but with **nothing in the circuit computing
them**. §1a and §5a change that for the third; §2b, §2c and §2d have since carved THREE more carriers
out of the residue, none of which is a bit:

    LINK_OK                    guard of the SEGMENT bind          (§2c, 2026-08-05)
    WRAP_FS_PROVED             guard of the CHAINLINK bind        (§2b, 2026-08-05, col 30)
    FINALIZE_XI_B_PROVED       guard of the CONJUNCTION bind      (§2d, 2026-08-06, col 58)
    PICKLES_OPENING_WITNESSED  the residue, STILL A BIT           (§1, col 9)
    CANON_OK                   DERIVED by eighteen lookups        (§1a/§5a)

  * `LINK_OK`    — ⚑⚑ **NO LONGER A BARE `= 1`, AS OF 2026-08-05 (§2c).** It was a forcing gate on
    a witnessed column and nothing else; it is now the GUARD of a nine-lane `proofBind` pinning
    `dregg-mina-lightclient-link::v1` and declaring the row's nine published `TIP_STATE` lanes to be
    that sub-proof's public-input commitment. The gate stays — it is what stops a prover setting the
    guard to `0` to switch the seam off (`mina_link_guard_cannot_be_disarmed`).
    ⚑ **SPLIT 2026-08-03, and the split is exactly what the seam now buys.**
    `LightClientMina.chainLinked` is three conjuncts per block — (i) `h.parent = prev`, (ii)
    `h.height = ph + 1`, (iii) `prev′ := blockHash h`. (i) and (ii) are EQUALITY and ADDITION; only
    (iii) is Poseidon over Pasta `Fp`.
    `Circuit/Emit/LightClientMinaLinkAir.lean` emits (i)+(ii) as a MULTI-ROW compiled descriptor —
    nine `.transition` lane-continuity gates per link, the height tick, and the segment length as a
    counted row total — and names (iii) as `LinkHashResidual`, still witnessed. So the honest
    statement is not "`LINK_OK` derived" but "the segment's SHAPE derived, its HASH still witnessed".
    ⚠ Note what the seam does NOT buy: a prover free to choose each row's `OWNHASH` can fabricate a
    consistent chain of any length. What it removes is the freedom to be INCONSISTENT, the freedom to
    claim a depth without committing rows for it, and — new today — the freedom to publish a tip that
    is not that chain's last element.
  * `PICKLES_OPENING_WITNESSED` — ⚑⚑ **RENAMED 2026-08-06, AND THE NAME NOW ENUMERATES THE RESIDUE.**
    It was `PICKLES_WITNESSED`, and before that `PICKLES_OK`: the whole per-block Pickles/Kimchi
    Wrap-proof result as one witnessed bit. What is left in it after §2d is **exactly three things**:
    the **IPA opening** (not in circuit anywhere, and `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free`
    proves the closing check ACCEPTS AT EVERY VALUE while `sg` is a free witness, so an opening leg
    over a free `sg` would narrow nothing), **`cipCorrect`**, and **`plonkChecksPassed`**.
    ⚠ The last two are **ABSENT BY CONSTRUCTION, NOT STUBBED**: `MinaWrapConjunctionAir`
    §"WHAT THIS OBJECT FORCES" states that a gate comparing `cip` against a ξ-fold with a FREE
    `ft_eval0` column forces nothing at all, and that `∃`-image vacuity has shipped in this repo
    before. STILL A WITNESS, and still the expensive one by three orders of magnitude — see §1b.
    `Circuit/Emit/MinaRealBlockGate.lean` renders the whole verdict on a real devnet block, natively.
  * `FINALIZE_XI_B_PROVED` — ⚑⚑⚑ **NEW 2026-08-06 (§1d, §2d), and NOT a bit.** The guard of a
    nine-lane `proofBind` pinning `dregg-mina-wrap-conjunction::v1` and PI-publishing that
    sub-proof's commitment. What it carries is **TWO of `finalize_other_proof`'s FOUR conjuncts** —
    `xiCorrect` and `bCorrect` against `PastaIPA.bEval` itself — plus the per-round
    challenge/inverse reciprocity weld and the opening residual's non-free coefficients.
    ⚠ **NOT "finalize proved" and NOT "Pickles verified".** Read §1d before quoting it, including
    what the bind does NOT buy: ξ is a FREE column in the conjunction AIR.
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
canonicality of the two published field elements, given `LINK_OK` and `PICKLES_OPENING_WITNESSED`.

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
    PI[20..28] SUB_PI[i]        — the CHAINLINK sub-proof's public-input commitment, nine lanes (§2b).
    PI[29]     ANCHOR_H         — the pinned anchor's blockchain length (2026-08-05).
    PI[30..38] CONJ_PI[i]       — ⚑⚑ the CONJUNCTION sub-proof's public-input commitment, nine lanes
                                  (§2d, 2026-08-06). APPENDED: no slot below 30 moved.

⚑ NINE LANES, NOT ONE FELT, and NOT nine 31-bit slices either. The repo has paid for both mistakes:
a single BabyBear anchor felt binds a ~31-BIT PROJECTION of a 256-bit hash, so two distinct Mina
heads agreeing in 31 bits would both verify; and a "radix-2^31" slicing is not representable at all,
since BabyBear's `p = 2013265921 < 2^31` means a 31-bit limb can exceed the modulus and alias. The
encoding is the tree's own PROVEN one — `Faithful9::from_key_lanes9` / Lean `keyToLanes9`: the 32
bytes as one little-endian 256-bit number in its NINE base-`2^29` digits, lanes 0..=7 below `2^29`
and lane 8 below `2^24`, `8·29 + 24 = 256` EXACTLY, so the image is exactly `2^256` and the encoding
loses nothing. Injectivity is machine-checked (`lanes9ToField_fieldToLanes9`,
`fieldToLanes9_injective`, `nine_lanes_is_the_minimum : P^8 < 2^256 ≤ P^9`).

⚠ TWO NAMED residuals on the anchors — ⚑ **ONE OF THEM CLOSED 2026-08-05, THE OTHER NOT, AND THEY
ARE DIFFERENT:**
  1. ⚠ **STILL OPEN.** This AIR PI-binds the eighteen lane columns but carries NO GATE relating them
     to a 32-byte value. The lane-vector ↔ head equality is enforced by the CONSUMER
     (`turn/src/executor/mina_head_verifier.rs::check_head_binding`, which refuses the turn), not
     in-circuit. That is a real refusal, and it is an executor check.
  2. ✅ **CLOSED for the TIP, by §2c.** This read: *"`TIP_STATE` is not arithmetically tied to the
     `LINK_OK` fold's terminal digest inside this AIR either … until it lands, the equality is the
     witness generator's, not a gate's."* It has landed, though NOT as a digest tie — the segment
     bind's `commit` vector IS the nine `TIP_STATE` columns, so an emitted constraint names them
     beside the guard and nine pinned program lanes, and the sub-proof they are the commitment of is
     one the consumer verifies. Nine `Faithful9` lanes, 256 bits, elementwise, no digest and
     therefore no birthday bound.
     ⚠ **AND THE ANCHOR HALF IS UNMOVED.** `ANCHOR_STATE`'s nine lanes are still PI-bound, still
     read by one arity-1 lookup each, and still joined to nothing
     (`LightClientAnchorConnectivity.minaVerify_anchor_lanes_are_read_but_never_joined`). A second
     bind could not fix that: `ProofBind`'s `commit` is the ONLY vector that names off-row evidence
     and there is one `piCommit` per engine, so two binds against one program with DIFFERENT
     commitments are incoherent, not merely redundant. The anchor's nine lanes are refused against
     the link sub-proof's own anchor block AT THE CONSUMER (REFUSAL 14), elementwise. Say it that
     way and do not call it a tie.

## Both polarities, on the EMITTED object (§6, §7)

* ACCEPT — `honest_row_accepted` on the REAL devnet genesis anchor and the REAL block-539508 tip
  (`honest_anchor_lanes_decode_the_devnet_genesis` pins the lanes against the Base58Check decimal);
  `minaLcAir_complete` is the general statement; `minaLcAir_no_forgery` carries acceptance all the
  way to `MinaValidAt`.
* REFUSE — EIGHT named refusing witnesses, each a CONCRETE assignment, each `¬ airAccepts`:
  `losing_fork_refused` (a shallower fork), `bent_proof_word_refused` (`PICKLES_OPENING_WITNESSED = 0`),
  `forged_height_refused` (the free-`blockchain_length` liar), `observer_arithmetic_refused` (the
  deployed observer's unanchored subtraction), ⚑ `shifted_anchor_refused` — the `+p` ANCHOR
  SUBSTITUTION, which `shifted_anchor_old_admits_new_rejects` shows the PRE-RUNG predicate accepted
  with `CANON_OK` witnessed `1` — and the three seams' own program-lane forgeries
  (`forged_program_refused`, `forged_link_program_refused`, ⚑⚑ `forged_conj_program_refused`), each
  paired with an `old_admits_new_rejects` twin over a DEFINED pre-rung predicate. A refusal that some
  assignment satisfies is decoration; these are exhibited, not asserted.

## ⚑ WHAT THIS BREAKS (flag day, stated so it is findable)

⚑⚑⚑ **2026-08-06, THE FINALIZE BIND (§1d, §2d) — the current flag day, and it MOVES `piCount`.**
`dregg-mina-lightclient-verify::v1` changes shape:

    traceWidth   58 → 77    (+1 carrier `FINALIZE_XI_B_PROVED`, +9 `CONJ_VK`, +9 `CONJ_PI`)
    piCount      30 → 39    (+9, APPENDED at 30..38; NO existing slot moves)
    constraints  63 → 74    (+1 gate, +1 `proof_bind`, +9 PI pins)
    legs         49 → 60
    proof_binds   2 → 3

**Re-emit** `circuit/descriptors/by-name/dregg-mina-lightclient-verify-v1.json` and **ROTATE THE VK**
for this descriptor. Any previously produced head proof fails to verify — intended: the old shape
carried four of upstream's conjuncts as one felt. ⚠ `mina_head_predicate_vk()` is blake3 over the
descriptor NAME, which does not move, so cell programs keep their pinned predicate vk and nothing
re-genesises.

⚠ **A WITNESS GENERATOR THAT LEAVES `CONJ_VK 0..8` UNFILLED NOW PRODUCES AN UNSAT ROW.** It must
write the nine `Faithful9` lanes of `dregg-mina-wrap-conjunction::v1`'s semantic fingerprint, set
`FINALIZE_XI_B_PROVED = 1`, publish a commitment in `CONJ_PI 0..8` / PI 30..38, and hold a verifying
STARK over that 16-row, 2 536-column descriptor.

⚠ **NEW COUPLING, the third of its kind:** re-emitting `mina-wrap-conjunction.json` moves
`CONJ_VK_LANES` and therefore **re-emits and re-VKs THIS descriptor** — exactly as
`dregg-mina-lightclient-link-v1.json` does through `LINK_VK_LANES` and `pasta-fq-chainlink.json` does
through `CHAINLINK_VK_LANES`. Three sub-programs, three fingerprints, three flag days.

⚠ **AND WHAT IS OWED IN RUST AND HAS NOT LANDED — named as undone work, not as a caveat.** This lane
touched only this file and the emitted descriptor. Each of the following is now WRONG at HEAD and is
work, not commentary:
  * `turn/src/executor/mina_head_verifier.rs` — `MINA_LC_PI_COUNT` is `30` and must become `39`; and
    there is no `check_conj_program_pin` / conjunction-commitment recomputation beside the existing
    `check_subproof_program_pin`. Until one exists, `CONJ_PI` is a published block nothing refuses,
    and `CONJ_PI_LANES` in §7 is a labelled ZERO PLACEHOLDER rather than a measured digest.
  * `turn/tests/mina_anchored_head_lands.rs` — `const MINA_LC_WIDTH: usize = 58`.
  * `circuit/tests/mina_lightclient_carrier_proves.rs` — the 58-wide row and `PICKLES_WITNESSED = 9`.
  * `circuit/tests/mina_transcript_carrier_binding.rs` — the fingerprint gate has two sub-programs
    and needs the third, which is the ONLY thing that makes `CONJ_VK_LANES` a gate rather than a
    literal (`feedback-a-pin-against-its-own-definition-is-decoration`).
  * `circuit/src/descriptor_by_name.rs` and `circuit-prove/tests/mina_link_segment_multirow.rs` —
    prose naming `PICKLES_WITNESSED`.

⚑⚑ **2026-08-05, THE SEGMENT BIND (§2c).** `dregg-mina-lightclient-verify::v1`
changed shape: **`traceWidth` 49 → 58** (nine `LINK_VK` columns), **62 → 63 constraints** (one
`proof_bind`), **49 legs**. **`piCount` STAYED 30** and no PI slot moved — the seam's commitment is the
tip block the descriptor already published, so `mina_head_verifier.rs`'s `MINA_LC_PI_COUNT` and every
PI offset were untouched.

⚠ A witness generator that leaves `LINK_VK 0..8` unfilled produces an UNSAT row: it must write
the nine `Faithful9` lanes of `dregg-mina-lightclient-link::v1`'s semantic fingerprint, and it must
hold a verifying STARK over that descriptor whose published tip block is this row's `TIP_STATE`.
⚠ **COUPLING:** re-emitting `dregg-mina-lightclient-link-v1.json` moves `LINK_VK_LANES` and
therefore re-emits and re-VKs THIS descriptor, exactly as `pasta-fq-chainlink.json` already does
through `CHAINLINK_VK_LANES`.

**2026-08-05, EARLIER — the canonicality rung.** `31 → 49 constraints`, `1 → 3 declared tables`
(adding `range_w29` at wire id 98 and `range_w22` at wire id 91). A witness generator that leaves the
eighteen lane columns unfilled produces an UNSAT row; `mina_head_verifier.rs` must write the anchor's
and the tip's nine `Faithful9` lanes, the same decomposition `check_head_binding` already computes.

## Scope — do NOT overclaim

⚠ NOT "machine-checked Mina validity" and NOT "Mina-valid". `PICKLES_OPENING_WITNESSED` rides the
undischarged IPA/FRI floor via `MinaLeaf.picklesSound`, and a STARK over this descriptor inherits the
undischarged FRI/STARK floor on the dregg side. What is proved is a refinement over the EMITTED
object: `airAccepts` ⟹ `minaVerifyDecision` ⟹ (`mina_no_forgery`) ⟹ `MinaValidAt`.

⚠ **AND NOT "finalize proved", which is the phrase §2d exists to make unwritable.** The finalize
carrier covers TWO of `finalize_other_proof`'s FOUR conjuncts, at a ξ THIS descriptor does not weld
to the block's transcript (§1d, both halves). `cipCorrect` and `plonkChecksPassed` are absent by
construction; the IPA opening is not in circuit anywhere.

⚠ And the scope limit `LightClientMinaGate` already names is UNCHANGED: this decides an ANCHORED
SEGMENT, not fork choice. Two `k`-deep proved segments under DIFFERENT anchors are indistinguishable
to this AIR; what distinguishes them is `MinaForkChoiceGate` / `dregg_mina_better_tip`, and the
anchor this AIR pins is `PI[0..8]` — an operator's or a serving peer's, and the descriptor cannot
tell you which. A verifier reads `ANCHOR_STATE` and decides whether it trusts it.

## Axiom hygiene

Compiled descriptor + non-vacuous per-gate `iff` lemmas + the load-bearing `minaLcAir_sound` /
`minaLcAir_no_forgery` refinement + EIGHT exhibited refusals. Every asserted fact is a NAMED THEOREM
(`metatheory/docs/GUARD-DISCIPLINE.md`); this file contains no `#guard`. Imports read-only.
-/
import Dregg2.Circuit.Emit.EffectLowerCore
import Dregg2.Circuit.LimbTally
import Dregg2.Circuit.Emit.PastaField
import Dregg2.Bridge.LightClientMinaGate
import Dregg2.Circuit.Emit.EffectLowerCertified

set_option autoImplicit false
set_option maxHeartbeats 1600000
-- ⚑ 2026-08-05: the leg list grew from 36 to 55 (the recursion carrier, nine `.bind` legs, nine
-- sub-proof PI pins), and the shape counts fold over it. `set_option` does not cross an import, so
-- this is stated here, in the file whose `rfl`s need it.
set_option maxRecDepth 4000

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
/-- `ANCHOR_H` — the weak-subjectivity anchor's blockchain length.

⚑ **PI-BOUND AT SLOT 29 SINCE 2026-08-05, AND READ THE NEXT PARAGRAPH BEFORE CALLING THAT A FIX.**
Until then this column was PUBLISHED BY NOTHING: not PI-bound, no range lookup, no gate equating it
to a literal — it appeared only in G1 and G4, joined to `SEG_LEN`/`BLOCK_LEN` and to
`ANCH_SLACK`/`SUBMIT_H`. So "the published height is the PINNED anchor plus the exhibited segment"
related THREE numbers the prover chose, and a prover who wanted a head to read 1 000 000 blocks high
picked `ANCHOR_H` to make G1 come out. `minaVerify_anchor_height_is_published` is the flip of the old
`minaVerify_anchor_height_is_pinned_to_nothing`, on the emitted bytes.

⚠ **WHAT THE PIN DOES AND DOES NOT DO, because a PI pin adds NO graph edge.**
`LightClientAnchorConnectivity.relatedCols` returns `[]` for a `piBinding` ON PURPOSE — a pin ties a
column to a PUBLIC INPUT, not to another column. So this leg does **not** connect the height to the
anchor STATE lanes (cols 12..20), and `minaVerify_anchor_height_shares_no_constraint_with_the_hash`
still holds. In-circuit, the height and the hash of "the anchor" remain two unrelated prover choices.

What the pin buys is that the choice is now **EXHIBITED**: `ANCHOR_H` leaves the proof as PI 29 where
a consumer can refuse it against a value it holds independently. That consumer half is
`dregg_turn::executor::mina_head_verifier`'s REFUSAL 2 — it compares PI 29 against the anchor HEIGHT
the cell program pinned, which travels inside the predicate commitment beside the anchor hash. A pin
whose only witness is the descriptor's own definition would be decoration; the second, independent
source is the cell program. -/
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
/-- **CARRIER — AND SINCE 2026-08-05 IT IS NOT A BARE BIT.** The exhibited segment's linkage result;
forced `= 1` by G6.

⚑ **WHAT CHANGED.** Until today `linkC` was the whole of it: `⟨.var LINK_OK, .const 1⟩`, a forcing
gate on a witnessed column, costing a prover one felt. It is now additionally the GUARD of the §2c
`proofBind` leg, so `LINK_OK = 1` forces nine program-lane congruences against the pinned fingerprint
of `dregg-mina-lightclient-link::v1` AND declares the row's nine published `TIP_STATE` lanes to be
the public-input commitment of a verifying sub-proof of that program. The gate did not go away — it
is what stops a prover setting the guard to `0` to switch the seam off
(`mina_link_guard_cannot_be_disarmed`).

⚠ **AND THE OVERCLAIM IN THE OLD NAME IS STILL HALF-TRUE, SO READ THE SPLIT.**
`LightClientMina.chainLinked` is three conjuncts per block — (i) `h.parent = prev`, (ii)
`h.height = ph + 1`, (iii) `prev′ := blockHash h`. The bound sub-proof emits (i) and (ii) as gates
over committed rows and names (iii) as `LinkHashResidual`, **still witnessed**. So what a satisfied
`LINK_OK` now buys is *"the segment's SHAPE derived, its HASH still witnessed"* — not "the Poseidon
fold verified". A prover free to choose each row's `OWNHASH` can still fabricate a consistent chain;
what it can no longer do is be INCONSISTENT, claim a depth without committing rows for it, or publish
a tip that is not that chain's last element. -/
def LINK_OK : Nat := 8
/-- **CARRIER, AND THE NAME NAMES THE THREE THINGS IT IS THE RESIDUE OF** — a witnessed bit, forced
`= 1`. ⚑ **RENAMED 2026-08-06 from `PICKLES_WITNESSED`, which was itself the 2026-08-05 rename of
`PICKLES_OK`.** Each rename NARROWED the name to what was left after a carrier split; this one
narrows it to the last three conjuncts, and they are enumerable.

⚑ **WHAT IS STILL TESTIMONY HERE, EXHAUSTIVELY — three things and no others.**

1. **The IPA OPENING.** It is **not in circuit**, in this descriptor or in any of the sub-proofs the
   two §2b/§2c/§2d seams name. `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free` is a THEOREM
   that the closing check **accepts at EVERY value** of everything else while `sg` is a free
   witness — so an opening leg written today over a free `sg` would not narrow this bit by one
   assignment. What removes it is a `sg == ⟨s, srs.g⟩` MSM leg (§1b prices the SRS MSM at 32 768
   terms and does not discharge it in-kernel anywhere).
2. **`cipCorrect`** — `dv.combinedInnerProduct` against `cipActualOf`.
3. **`plonkChecksPassed`** — the same shape at `permScalarR`, and smaller.

⚑ **(2) AND (3) ARE ABSENT BY CONSTRUCTION, NOT STUBBED, AND THE REASON IS ARITHMETIC.**
`MinaWrapConjunctionAir` §"WHAT THIS OBJECT FORCES" states it: `cipActualOf`'s `ft_eval0` slot is
K5's gate linearization, and **a gate comparing `cip` against a ξ-fold with a FREE `ft_eval0` column
forces nothing at all** — a free `ft_eval0` makes the fold's value free, so the comparison accepts
every `cip`. That is the `∃`-image vacuity this repo has SHIPPED ONCE
(`minted-exists-image-vacuity-class`), and an emitted-but-vacuous `cipCorrect` leg would be strictly
worse than this bit: it would read as a check. The missing two are LOCATED — the K5 linearization
chain — not hand-waved.

⚠ **AND WHAT IS NO LONGER IN THIS BIT, so the name is not read too wide.** Two of upstream
`finalize_other_proof`'s four conjuncts — `xiCorrect` and `bCorrect` against `PastaIPA.bEval`
itself — left this column on 2026-08-06 and became §2d's `FINALIZE_XI_B_PROVED`, whose `= 1` is
unsatisfiable unless the row names a verifying dregg STARK over `dregg-mina-wrap-conjunction::v1`.
Nothing in this descriptor computes a Pickles verification and nothing ever will at this
construction — §1b prices it at ≈10⁹ BabyBear constraints. -/
def PICKLES_OPENING_WITNESSED : Nat := 9
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

/-- ⚑ **CARRIER — AND THE ONE THAT IS NOT A BIT** (col 30, added 2026-08-05). See §1c.

`WRAP_FS_PROVED = 1` is the guard of NINE `proofBind` legs. Under it the descriptor forces the nine
`SUB_VK` columns to the nine `Faithful9` lanes of the SEMANTIC FINGERPRINT of
`dregg-pasta-fq-chainlink::v1` — literals in these emitted bytes, so not the prover's to choose — and
the row's declared sub-proof commitment is the nine PI-BOUND `SUB_PI` lanes, which the consumer
checks against the public inputs of a STARK it actually verifies. A row that sets this to 1 without a
verifying chainlink proof is refused: in-AIR by the vk congruences if it names the wrong program, and
at the consumer if it names no proof at all. -/
def WRAP_FS_PROVED : Nat := 30

/-- **The pinned sub-proof PROGRAM lane `i`** (cols 31..39) — a prover column, forced by the
`proofBind` leg's `vkPin` to a descriptor literal. ⚑ It is a COLUMN and not a constant expression on
purpose: a constant compared against its own definition is decoration
(`feedback-a-pin-against-its-own-definition-is-decoration`); here the two sides are the witness
generator's value and the emitted descriptor's bytes, which are independent sources. -/
def SUB_VK (i : Nat) : Nat := 31 + i

/-- **The declared sub-proof PUBLIC-INPUT COMMITMENT lane `i`** (cols 40..48, PI slots 20..28) — the
nine `Faithful9` lanes of the digest of the chainlink sub-proof's 256 public inputs. PI-bound, so the
commitment the recursion existential quantifies over is a PUBLIC value and not a free column. -/
def SUB_PI (i : Nat) : Nat := 31 + STATE_LIMBS + i

/-- ⚑⚑ **THE ATTESTED SEGMENT PROGRAM's lane `i`** (cols 49..57, added 2026-08-05) — a prover column
forced by the `LINK_OK`-guarded `proofBind` leg's `vkPin` to a descriptor literal, exactly as
`SUB_VK` is for the chainlink. See §2c.

⚑ It is a COLUMN and not a constant expression for the reason `SUB_VK` is: a constant compared
against its own definition is decoration (`feedback-a-pin-against-its-own-definition-is-decoration`);
the two independent sources here are the witness generator's value and the emitted bytes. -/
def LINK_VK (i : Nat) : Nat := 31 + 2 * STATE_LIMBS + i

/-! ## §1d — ⚑⚑⚑ THE FINALIZE CARRIER, 2026-08-06: what `FINALIZE_XI_B_PROVED` MEANS, stated at this
tree's resolution and not at the name's.

## The claim, named exactly, before any theorem — and DO NOT WIDEN IT

`dregg-mina-wrap-conjunction::v1` (`Circuit/Emit/MinaWrapConjunctionAir.lean`) is a **16-row threaded
AIR** — 15 IPA rounds as 15 `.transition` rows plus one terminal row that reads the finished
register, `2 536` columns FLAT in the round count — which, as of 2026-08-06, publishes **160 public
inputs**: ξ, ζ, ζω, the evalscale `r`, and the claimed `b0`, five 32-limb blocks (`CJ_PI_COUNT`,
§9b). A verifying STARK over it establishes this and **NOTHING WIDER**:

> **Two of Pickles' `finalize_other_proof` FOUR conjuncts — `xiCorrect` (`op.xiSqueeze = dv.xi`) and
> `bCorrect` against `PastaIPA.bEval` ITSELF (`dv.b ≡ bEval ζ chals + r · bEval ζω chals (mod q)`,
> where `chals` is the vector the trace's own rows supplied) — plus the per-round challenge/inverse
> reciprocity weld (`chal · chalinv ≡ 1`) and the opening residual's non-free coefficients
> (`c·cip − z1·b0`, `−z1`, `−z2`, `c·chal`, `c·chalinv`), each computed by a sound core.**

⚠ **UPSTREAM'S CONJUNCTION IS A FOUR-WAY AND WITH THE OPENING; THIS IS A TWO-WAY AND.**
`cipCorrect` and `plonkChecksPassed` are **ABSENT BY CONSTRUCTION, NOT STUBBED**, and the reason is
`MinaWrapConjunctionAir` §"WHAT THIS OBJECT FORCES"'s, verbatim in substance: `cipActualOf`'s
`ft_eval0` slot is K5's gate linearization, and **a gate comparing `cip` against a ξ-fold with a FREE
`ft_eval0` column forces nothing at all** — a free `ft_eval0` makes the fold's value free, so the
comparison accepts every `cip`. That is the `∃`-image vacuity this repo has already shipped once, and
an emitted-but-vacuous `cipCorrect` would be strictly worse than the bit it replaced, because it
would READ as a check. `plonkChecksPassed`'s `permScalarR` is the same shape and smaller. The missing
two are LOCATED — the K5 linearization chain — not hand-waved.

⚠ **AND THE OPENING IS STILL NOT IN CIRCUIT.** `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free`
is a theorem that the closing check accepts at EVERY value while `sg` is a free witness.
`PICKLES_OPENING_WITNESSED` (§1, col 9) is the residue and is still a bit.

**So: do NOT write "finalize proved". Do NOT write "Pickles verified". Do NOT write anything implying
the IPA opening is checked.** Two of four conjuncts, a reciprocity weld, and a coefficient seam.

## ⚑⚑ WHAT THE BIND DOES NOT BUY — `ξ` IS A FREE COLUMN IN THE SUB-PROOF

Read this before quoting `xiCorrect`. In the conjunction AIR `ξ` appears in `eqBlock XI_SQ XI_CL`, in
`globalThread`'s hold legs, and in the input range lookups — **and in NO SOUND CORE.** Nothing
derives it from a transcript. So a conjunction proof ALONE runs the b-polynomial fold **at any ξ the
prover likes**, and `xiCorrect` degenerates to *"the two columns I wrote down agree"*.

What welds ξ to the block's own transcript is the RECURSION FOLD:
`circuit-prove/src/mina_wrap_finalize_fold.rs::fold_endo_into_finalize` verifies both children
in-circuit and then issues **32 in-circuit `cb.connect`s** tying `dregg-mina-xi-endo-lift::v1`'s
published output limbs to this sub-proof's published ξ limbs — a prover whose conjunction read a
different ξ has no satisfying assignment in the aggregation circuit, so there is no root.

⚠ **That fold is a CONSUMER CHECK HERE, NOT A CONSTRAINT OF THIS DESCRIPTOR** — exactly the status
`turn/src/executor/mina_head_verifier.rs::check_chain_root_binding` has for `WRAP_FS_PROVED`, and the
status the eleven uncovered link PIs have for `LINK_OK` (§2c). This descriptor's §2d leg says WHICH
PROGRAM and WHICH COMMITMENT; it does not say AT WHICH ξ. A consumer that verifies the conjunction
leaf WITHOUT the endo fold has accepted a fold at a prover-chosen ξ. Say it that way and do not call
it a tie. -/

/-- ⚑⚑⚑ **CARRIER — THE FINALIZE CONJUNCT PAIR** (col 58, added 2026-08-06). See §1d for the claim
and §2d for the leg. NOT a bit: `FINALIZE_XI_B_PROVED = 1` is the GUARD of a nine-lane `proofBind`
naming `dregg-mina-wrap-conjunction::v1`, so a row that sets it without holding a verifying STARK
over that program has no satisfying assignment in-AIR (wrong program lanes) and is refused at the
consumer (no proof at all). ⚠ What it carries is TWO of finalize's FOUR conjuncts, at a ξ this
descriptor does not weld — §1d, both halves. -/
def FINALIZE_XI_B_PROVED : Nat := 58

/-- ⚑⚑ **THE CONJUNCTION PROGRAM's lane `i`** (cols 59..67, added 2026-08-06) — a prover column
forced by the §2d `proofBind` leg's `vkPin` to a descriptor literal, exactly as `SUB_VK` is for the
chainlink and `LINK_VK` for the segment.

⚑ It is a COLUMN and not a constant expression for the reason the other two are: a constant compared
against its own definition is decoration (`feedback-a-pin-against-its-own-definition-is-decoration`);
the two independent sources here are the witness generator's value and the emitted bytes. -/
def CONJ_VK (i : Nat) : Nat := 58 + 1 + i

/-- ⚑⚑ **THE CONJUNCTION SUB-PROOF'S PUBLIC-INPUT COMMITMENT lane `i`** (cols 68..76, PI slots
30..38, added 2026-08-06) — the nine `Faithful9` lanes of a commitment to that sub-proof's 160
declared public inputs. PI-bound, so the commitment §2d's existential quantifies over is a PUBLIC
value and not a free column, which is exactly what lets `bound` be `none` (§2d). -/
def CONJ_PI (i : Nat) : Nat := 58 + 1 + 9 + i

/-- Total main-trace width: 11 logic/carrier columns + the derived height + two nine-limb anchors
+ ⚑ the recursion carrier and its two nine-lane blocks + ⚑ the segment sub-proof's nine program
lanes + ⚑⚑ the finalize carrier and its two nine-lane blocks (2026-08-06).

⚑ Written additively rather than as `77` so each term names the rung that bought it: `31 + 3·9` is
the pre-2026-08-06 width, `+ 1` is `FINALIZE_XI_B_PROVED`, `+ 2·9` is `CONJ_VK ++ CONJ_PI`. -/
def MINA_LC_WIDTH : Nat := 31 + 3 * STATE_LIMBS + 1 + 2 * STATE_LIMBS

/-- PI slot of anchor-state limb `i` (slots 0..8). -/
def PI_ANCHOR_STATE (i : Nat) : Nat := i
/-- PI slot of tip-state limb `i` (slots 9..17). -/
def PI_TIP_STATE (i : Nat) : Nat := STATE_LIMBS + i
/-- PI slot 18: the verified head's `blockchain_length`. -/
def PI_BLOCK_LEN : Nat := 2 * STATE_LIMBS
/-- PI slot 19: the Samasika depth policy met. -/
def PI_REQ_DEPTH : Nat := 2 * STATE_LIMBS + 1
/-- ⚑ PI slots 20..28: the chainlink sub-proof's public-input commitment lanes. -/
def PI_SUB_PI (i : Nat) : Nat := 2 * STATE_LIMBS + 2 + i
/-- ⚑ PI slot 29: the weak-subjectivity anchor's blockchain length (`ANCHOR_H`, col 1).

**APPENDED, not inserted at 20.** Giving the height slot 20 would have shifted `PI_SUB_PI` to 21..29
and moved `PI_SUB_COMMIT_BASE` in every consumer — a re-index whose only benefit is that the slots
read in column order. The pin's CONSTRAINT is emitted next to the other pins (right after
`PI_REQ_DEPTH`); its SLOT is the last one. Emission order and slot order are independent. -/
def PI_ANCHOR_H : Nat := 3 * STATE_LIMBS + 2

/-- ⚑⚑ PI slots 30..38: the CONJUNCTION sub-proof's public-input commitment lanes (2026-08-06).

**APPENDED, and every slot below 30 is UNMOVED** — the same discipline `PI_ANCHOR_H`'s own docstring
states and for the same reason. `PI_ANCHOR_H` stays at **29**, `PI_SUB_PI` stays at 20..28,
`PI_BLOCK_LEN` at 18, `PI_REQ_DEPTH` at 19, the two nine-lane hashes at 0..17. A consumer's
`PI_SUB_COMMIT_BASE`, `PI_ANCHOR_H` and every anchor/tip offset therefore read the same slot after
this rung as before it; what changes is that nine MORE slots exist and `MINA_LC_PI_COUNT` must grow
to admit them. Emission order and slot order are independent, and the pin's CONSTRAINT is emitted
last (§3) while its SLOTS are the last nine. -/
def PI_CONJ_PI (i : Nat) : Nat := 3 * STATE_LIMBS + 3 + i

/-- Number of public inputs: two nine-limb hashes + the height + the depth policy + ⚑ the nine-lane
chainlink sub-proof commitment + ⚑ the anchor height + ⚑⚑ the nine-lane CONJUNCTION sub-proof
commitment (2026-08-06). Written additively so the last term names the rung that bought it. -/
def MINA_PI_COUNT : Nat := 3 * STATE_LIMBS + 3 + STATE_LIMBS

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

/-- **G6 — the linkage carrier**: `LINK_OK = 1`. ⚑ Since 2026-08-05 this gate has CONTENT for the
same reason G9 does: it is the guard of the §2c `proofBind`, so it cannot be set to `0` to switch the
segment seam off. It is no longer the whole of what `LINK_OK` costs. -/
def linkC : Constraint := ⟨.var LINK_OK, .const 1⟩
/-- **G7 — the witnessed OPENING residue**: `PICKLES_OPENING_WITNESSED = 1`. ⚑ A bare `= 1` on a
witnessed column, and it stays one: what it now carries is the IPA opening, `cipCorrect` and
`plonkChecksPassed`, and §1's docstring on the column says why none of the three can be emitted here
without shipping an `∃`-image vacuity. -/
def openingWitnessedC : Constraint := ⟨.var PICKLES_OPENING_WITNESSED, .const 1⟩
/-- **G8 — the canonicality carrier**: `CANON_OK = 1`. -/
def canonC : Constraint := ⟨.var CANON_OK, .const 1⟩
/-- **G9 — ⚑ the RECURSION carrier**: `WRAP_FS_PROVED = 1`. Unlike G7 this one has content: it is
the guard of the nine `proofBind` legs of §2b, so setting it forces the row to name a verifying
sub-proof of a PINNED program and to publish that sub-proof's commitment. -/
def wrapFsC : Constraint := ⟨.var WRAP_FS_PROVED, .const 1⟩
/-- **G10 — ⚑⚑ the FINALIZE-CONJUNCT carrier**: `FINALIZE_XI_B_PROVED = 1`. Like G9 and unlike G7
this one has content: it is the guard of the §2d `proofBind` leg, so setting it forces the row to
name a verifying sub-proof of `dregg-mina-wrap-conjunction::v1` and to publish that sub-proof's
public-input commitment. -/
def finalizeXiBC : Constraint := ⟨.var FINALIZE_XI_B_PROVED, .const 1⟩

/-! ## §2b — ⚑⚑ THE RECURSION BIND: what `WRAP_FS_PROVED` costs a prover.

## The claim, named exactly, before any theorem

`dregg-pasta-fq-chainlink::v1` (`Circuit/Emit/MinaPhase2Chain.lean`) is a dregg AIR over the
2 048-instruction Kimchi-`fq_kimchi` sponge program. What a verifying STARK over it establishes is
this and nothing wider:

> **The final absorption of a phase-2 (`fq_kimchi`-over-Fq) Kimchi transcript — starting from the
> incoming three-lane sponge state its public inputs pin, absorbing the single element its public
> inputs pin, and permuting once through the 55 `fq_kimchi` rounds whose constants are cells of that
> descriptor — lands on the THREE output lanes its public inputs pin.**

For the fixture instance those pins are **Mina devnet block 539508's own 46th and last link**: the
incoming state is derived (never typed) from that block's 91-element phase-2 tape, and outgoing lanes
0 and 1's low 128 bits ARE the `v′`/`u′` `proof.oracles(…)` returned on it —
`MinaPhase2Chain.the_chain_ends_at_the_blocks_challenges`, itself resting on
`MinaBlockFqTranscript.the_machine_squeezes_the_real_blocks_v_and_u` against a tape the extractor
read from a proof `kimchi::verifier::verify::<Pallas,…>` accepts.

⚑ **WHY THREE LANES AND NOT TWO — the difference this rung was re-pointed for.** A Poseidon state is
three lanes (`the_outgoing_lanes_are_registers_4_5_0`). `MinaBlockFqTranscript.linkPins` published
two of them, and the consumer's fold weld therefore compared 64 of a 96-limb sponge state and left
the third lane compared to nothing. `MinaPhase2Chain.chainPins` publishes all three, so the weld is
whole-state. It is also the descriptor the 46-leaf fold is BUILT on
(`circuit-prove/src/mina_phase2_chain_leaf.rs`), which is what makes this bind about the same object
the root proves rather than a sibling permutation beside it.

⚠ **AND WHAT IT DOES NOT ESTABLISH — say it here, not in a footnote.**
1. **NOT that the Pickles proof is valid.** The opening is not in circuit, and
   `MinaWrapOpeningGate.opening_is_vacuous_when_sg_is_free` says a free `sg` makes the closing check
   accept at every value. `PICKLES_OPENING_WITNESSED` is the residue and it is still a bit.
2. **NOT that the transcript is THIS row's tip's.** The 45 upstream permutations that determine the
   incoming state are the sub-proof's WITNESSES, pinned as its public inputs, not its gates — 74 250
   further emitted rows ≈ 203 MB of witness, which is the whole reason one of the 46 permutations is
   emitted. Nothing in THIS descriptor gates `TIP_STATE` against the sub-proof's commitment either:
   the two are published side by side. ⚑ NARROWED, not closed, by the re-point: the CONSUMER now
   welds the fold root's whole outgoing state to this link, so the sub-proof's incoming state is no
   longer a free prover choice — but nothing yet relates either object to `TIP_STATE`, which still
   needs the Fp phase-1 leg.
3. **NOT the accumulator.** `bridge/examples/mina_accumulator_discharge.rs` discharges it NATIVELY on
   7 real block proofs; it is not part of this bind.

So the honest sentence is *"a dregg STARK checked one absorption of the Fq transcript whose challenge
outputs this row's sub-proof commitment covers"*, and the carrier is named `WRAP_FS_PROVED`
(Fiat–Shamir), not `PICKLES_OPENING_WITNESSED`.

## The mechanism: ONE leg, NINE LANES

⚑ **2026-08-05 — the widening landed, and this descriptor is its first consumer.** What stood here
read: *"`ProofBind`'s `vkPin`/`bound`/`commit` are ONE FELT EACH … so the program is pinned lane by
lane: nine `proofBind` legs … This is NOT a substitute for widening `ProofBindSpec` itself — that
widening is a separate lane's."* The widening is done. `ProofBind` carries LANE VECTORS, so the nine
legs are ONE leg whose `vk` is the nine `SUB_VK` columns and whose `vkPin` is the nine `Faithful9`
lanes of the sub-proof descriptor's semantic fingerprint — `8·29 + 24 = 256` bits exactly, the
encoding machine-checked injective (`fieldToLanes9_injective`). A forger must still match all nine;
what changed is that the descriptor SAYS SO IN ONE DECLARATION, and that a leg pinning a PREFIX of
those lanes is now refused (`BindLeg.mainRailOk`) rather than being nine independent legs of which
eight could quietly go missing.

⚑ Note the FLOOR is eight and this object is NINE: eight BabyBear lanes cannot injectively carry 32
bytes (247.26 bits against 256), so `Faithful9` is the honest encoding and the seam binds the width
of ITS object, not of the custom commitment's.

⚑ **`bound` is `none`, and that is the STRONGER choice here, not a laxer one.** `bound` forces the
`commit` EXPRESSION to equal a row-local expression, and exists because the deployed `customProofBind`
carries `commit` as a FREE column. Here `commit` is `.var (SUB_PI i)` — a **PI-BOUND** column. A
`bound` congruence could only compare it to itself, which is decoration
(`feedback-a-pin-against-its-own-definition-is-decoration`). The commitment is public, which is
strictly more than being tied to another witness. -/

/-- ⚑ **THE SUB-PROOF'S PROGRAM IDENTITY, AS NINE LANES — a real value, never a fabricated one.**

These are the nine `Faithful9` key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-pasta-fq-chainlink::v1)` — blake3 (derive-key,
context `EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT`) over the descriptor's CANONICAL bytes. In this
tree the descriptor IS the verifying key: `verify_vm_descriptor2(&desc, &proof, &pis)` takes no other
key material, so the semantic fingerprint of the descriptor is exactly the program identity a
recursion bind should name.

⚑⚑ **2026-08-05 — RE-POINTED FROM THE SEVEN-BLOCK WRAPLINK TO THE EIGHT-BLOCK CHAINLINK, and the
difference is a whole sponge lane.** `MinaBlockFqTranscript.linkPins` pins SEVEN blocks
(`in(3) ++ absorbed(2) ++ out(2)`, 224 PIs) and therefore exposes **two of a Poseidon state's three**
outgoing lanes; `MinaPhase2Chain.chainPins` pins EIGHT (`in(3) ++ out(3) ++ absorbed(2)`, 256 PIs)
and exposes all three (`the_outgoing_lanes_are_registers_4_5_0`). Both descriptors are the SAME
`programAir qLimb absorbProg` (`the_chain_air_extends_the_program_air`), so this is not a different
machine — it is the same machine with its third outgoing lane published instead of left free.

What that buys the CONSUMER is exact: `turn/src/executor/mina_head_verifier.rs`'s weld
(`check_chain_root_binding`, refusal 10) compares the 46-link fold root's outgoing sponge state to
this sub-proof's pinned outgoing block. Against the wraplink that comparison covered 64 of the
claim's 96 limbs and the third lane was compared to nothing. Against the chainlink it is all 96.
And the chainlink is the descriptor the 46-leaf fold is actually built on
(`circuit-prove/src/mina_phase2_chain_leaf.rs`), so `WRAP_FS_PROVED` now attests a permutation of
the chain the root proves rather than a sibling permutation beside it.

⚠ **FLAG DAY, and it is a real coupling:** re-emitting `pasta-fq-chainlink.json` moves this literal
and therefore re-emits and re-VKs THIS descriptor. That is intended — a light client must not keep
accepting sub-proofs of a program that changed shape. `circuit/tests/mina_transcript_carrier_binding.rs`
recomputes the fingerprint from the sibling descriptor's own bytes and asserts these nine numbers, so
a drift is a RED and not a silence: two independent sources, which is what makes it a gate.

⚑⚑ **AND THAT GATE HAD ALREADY GONE RED AND STAYED RED — say it, because it is the reason the
consumer now checks this at RUNTIME too.** `7a4b8ab00` wrote the wraplink fingerprint here
correctly; `75df624cf` ("140 served descriptors were not the Lean object") re-emitted
`pasta-fq-wraplink.json` and moved its bytes, and this literal did not follow. Measured 2026-08-05:
the emitted `dregg-mina-lightclient-verify-v1.json` pinned
`[460719650, 491018495, …]` while `pasta-fq-wraplink.json` fingerprinted to
`[172082222, 381973190, …]` — **the bind named a program no descriptor in this tree has.** The test
said so and nothing else did, so `MinaAnchoredHeadStarkVerifier::verify` now recomputes the
dispatched sub-proof's fingerprint and REFUSES the head on a mismatch. A pin whose only reader is a
test is a pin a node can drift past. -/
def CHAINLINK_VK_LANES : List ℤ :=
  [40589529, 494773874, 527776693, 373808410, 118028044, 372824034, 512521559, 25478361, 4577485]

/-- The `i`-th pinned program lane, as the `vkPin` literal the leg carries. -/
def chainlinkVkLane (i : Nat) : ℤ := CHAINLINK_VK_LANES.getD i 0

/-- ⚑ **THE RECURSION-BIND LEG — ONE LEG, NINE LANES.** Guard `WRAP_FS_PROVED`; the declared
commitment is the nine PI-bound `SUB_PI` columns; the attested program is the nine `SUB_VK` columns,
pinned to the nine descriptor-fingerprint literals.

⚑ Until 2026-08-05 this was `wrapBindLeg (i : Nat)` and NINE legs, because the IR's `commit`/`vk`/
`vkPin` were one felt each. The lane vector is the same nine columns and the same nine literals; the
difference is that the seam declares them as ONE object, and `BindLeg.mainRailOk` refuses a pin that
names fewer lanes than the vector it pins. -/
def wrapBindLeg : AirLeg :=
  .bind { guard := .var WRAP_FS_PROVED
        , commit := (List.range 9).map (fun i => .var (SUB_PI i))
        , vk := (List.range 9).map (fun i => .var (SUB_VK i))
        , vkPin := some CHAINLINK_VK_LANES
        , bound := none }

/-- The bind legs — now exactly one. -/
def wrapBindLegs : List AirLeg := [wrapBindLeg]

/-- The nine sub-proof-commitment PI pins (cols 40..48 → PI 20..28). -/
def subPiPins : List AirLeg :=
  [ .pin ⟨VmRow.first, SUB_PI 0, PI_SUB_PI 0⟩
  , .pin ⟨VmRow.first, SUB_PI 1, PI_SUB_PI 1⟩
  , .pin ⟨VmRow.first, SUB_PI 2, PI_SUB_PI 2⟩
  , .pin ⟨VmRow.first, SUB_PI 3, PI_SUB_PI 3⟩
  , .pin ⟨VmRow.first, SUB_PI 4, PI_SUB_PI 4⟩
  , .pin ⟨VmRow.first, SUB_PI 5, PI_SUB_PI 5⟩
  , .pin ⟨VmRow.first, SUB_PI 6, PI_SUB_PI 6⟩
  , .pin ⟨VmRow.first, SUB_PI 7, PI_SUB_PI 7⟩
  , .pin ⟨VmRow.first, SUB_PI 8, PI_SUB_PI 8⟩ ]

/-! ## §2c — ⚑⚑⚑ THE SEGMENT BIND: `TIP_STATE` STOPS BEING DECORATION, AND `LINK_OK` STOPS BEING A
BARE `= 1`.

## The two defects this closes, both measured on the emitted bytes

1. **`LightClientAnchorConnectivity.minaVerify_state_lanes_are_read_but_never_joined`** proved, by
   `decide` over the served descriptor, that cols 12..29 — the anchor's nine lanes and the TIP's
   nine — are READ (each by one arity-1 range lookup) and RELATED TO NOTHING. Their only other leg
   was a `.pin`, and `relatedCols` returns `[]` for a `piBinding` *deliberately*: a pin ties a column
   to a PUBLIC INPUT, not to another column. So the head's published tip was a number the prover
   wrote down, bounded in width and tied to no evidence. **A width bound is a fact about a value's
   SHAPE; it is not a tie to the evidence.**
2. **`linkC` was `⟨.var LINK_OK, .const 1⟩`** — a bare forcing gate on a witnessed column, the same
   shape §1 called *"STILL A WITNESS HERE"*. Setting it cost a prover one felt.

Both are closed by ONE leg, and it is the mechanism `SUB_PI` already uses — `relatedCols`'
`.proofBind` arm, which returns the guard, the commitment lanes, the vk lanes and the bound lanes.

## What the leg says, exactly

`LINK_OK = 1` is now the GUARD of a `proofBind` whose declared commitment IS the row's nine
`TIP_STATE` lanes and whose attested program is pinned, lane by lane, to the semantic fingerprint of
`dregg-mina-lightclient-link::v1`. Row-locally (`ProofBind.holdsAt`) that is: the guard is a bit, and
under it every `LINK_VK` column equals its pinned literal. Off-row (`Satisfied2Custom.proofBound`) it
is: **there exists a verifying sub-proof of that program whose public-input commitment is these nine
lanes.**

⚑ **WHY THE COMMITMENT IS THE TIP BLOCK AND NOT A DIGEST — the choice is forced, and it is the
stronger one.** `ProofBind`'s `commit` is the ONLY vector that names off-row evidence, and `bound`
is defined to be *equal* to it; so the only way a `proofBind` can join `TIP_STATE` at all is for
`TIP_STATE` to BE the commitment. That is not a workaround — it is the elementwise weld the phase-1
leg landed on the same day (`MinaPhase1Chain.the_wire_blocks_are_equal`, 32/32 felts): **nine lanes,
`8·29 + 24 = 256` bits exactly, no digest, therefore NO BIRTHDAY BOUND.** A nine-lane `Faithful9`
commitment is exact equality of a 256-bit value, not a `2^123.6` collision bar and not the `2^31` a
one-felt tie would have been.

## What the sub-proof establishes — and it is the SHAPE, not the HASH

`dregg-mina-lightclient-link::v1` is the multi-row companion (`LightClientMinaLinkAir`): one row per
exhibited block, nine `.transition` lane-continuity gates per link, the height ticking by one from a
first-row anchor, and `PI_SEG_LEN` the LAST row's `REAL_COUNT` — so `link_seg_len_counts_the_real_rows`
proves a claimed depth is PAID FOR IN COMMITTED ROWS. `LightClientAnchorConnectivity.minaLink_decorative_anchors`
is `[]`: all twenty of its published columns are joined.

⚠ **AND ITS OWN CAVEAT BINDS HERE TOO, VERBATIM.** `OWNHASH` is a free witness; nothing forces it to
be `Poseidon(stateRow)` (`LinkHashResidual`, priced at ~5·10⁵ BabyBear constraints per block hash).
So the honest sentence is **not** "the tip is derived" but *"the tip is the last element of a chain
of rows this proof commits to, whose shape is gated and whose hashes are still the prover's."* That
is strictly more than the eighteen-lookups-and-nothing it had this morning, and strictly less than
derivation. `LINK_OK`'s docstring says the same thing and is not restated here.

## The eleven public inputs the seam does NOT cover, and where they are refused

The link sub-proof publishes twenty values; this seam's commitment is nine of them (PI 9..17, the
tip). The other eleven — the anchor's nine lanes (PI 0..8), the anchor height (PI 18) and the
segment length (PI 19) — are refused **at the consumer**, elementwise, against values this head
descriptor publishes or derives from what it publishes:

    link PI[0..8]  ==  head PI[0..8]                    (the same pinned anchor)
    link PI[18]    ==  head PI[29]                      (the same anchor height)
    link PI[19]    ==  head PI[18] − head PI[29]        (BLOCK_LEN − ANCHOR_H, i.e. SEG_LEN)

⚑ The third is the one worth reading twice. `SEG_LEN` is column 0 and a FREE WITNESS in `[1, 2^24]`
(§"CORRECTED 2026-08-03" says so at length), but G1 makes it a *function of two PUBLISHED values*, so
a consumer can recompute it without the prover's help — and the link proof must then exhibit that
many rows. `dregg_turn::executor::mina_head_verifier`'s REFUSALS 13 and 14.

⚠ Say which half is which: the nine-lane tip weld is IN-CIRCUIT; the other eleven are an EXECUTOR
CHECK. Both are real refusals; only the first is a constraint. -/

/-- ⚑ **THE SEGMENT SUB-PROOF'S PROGRAM IDENTITY, AS NINE LANES.** The `Faithful9` key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-mina-lightclient-link::v1)` — blake3 (derive-key,
context `EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT`) over that descriptor's CANONICAL bytes. In this
tree the descriptor IS the verifying key.

⚠ **FLAG DAY, and it is the same real coupling `CHAINLINK_VK_LANES` carries:** re-emitting
`dregg-mina-lightclient-link-v1.json` moves this literal and therefore re-emits and re-VKs THIS
descriptor. `circuit/tests/mina_transcript_carrier_binding.rs` recomputes the fingerprint from the
sibling descriptor's own bytes and asserts these nine numbers, and
`mina_head_verifier::check_subproof_program_pin` recomputes it again AT VERIFY TIME — because the
wraplink drift proved a pin whose only reader is a test is a pin a node can drift past. -/
def LINK_VK_LANES : List ℤ :=
  -- ⚑ MOVED 2026-08-08 with the link descriptor's `piCount` 20 → 37 publication flag day
  -- (`trace_width` 40 → 57, constraints 72 → 99). Recomputed from the emitted bytes with
  -- `cargo run -p dregg-circuit --release --example conj_fingerprint -- \
  --   circuit/descriptors/by-name/dregg-mina-lightclient-link-v1.json`, never transcribed
  -- from a docblock. THIS descriptor re-emits and re-VKs with it; every previously produced
  -- `MinaHeadProofWire` fails to verify.
  [485689086, 477622751, 46091945, 410308945, 235143973, 391260395, 78649260, 413048609, 30212]

/-- The `i`-th pinned segment-program lane, as the `vkPin` literal the leg carries. -/
def linkVkLane (i : Nat) : ℤ := LINK_VK_LANES.getD i 0

/-- ⚑⚑ **THE SEGMENT-BIND LEG — the one that gives `TIP_STATE` an in-circuit edge.** Guard
`LINK_OK`; the declared commitment is the row's own nine PUBLISHED tip lanes; the attested program is
the nine `LINK_VK` columns, pinned to the link descriptor's fingerprint.

⚑ `bound := none` and it is the STRONGER choice, for exactly the reason §2b gives for the chainlink
seam: `bound` forces the `commit` expression to equal a row-local expression, and here `commit` is
already `.var (TIP_STATE i)` — a **PI-BOUND** column. A `bound` congruence could only compare it to
itself, which is decoration. The commitment being PUBLIC is strictly more than its being tied to
another witness. -/
def linkBindLeg : AirLeg :=
  .bind { guard := .var LINK_OK
        , commit := (List.range 9).map (fun i => .var (TIP_STATE i))
        , vk := (List.range 9).map (fun i => .var (LINK_VK i))
        , vkPin := some LINK_VK_LANES
        , bound := none }

/-- The segment-bind legs — exactly one. -/
def linkBindLegs : List AirLeg := [linkBindLeg]

/-! ## §2d — ⚑⚑⚑ THE FINALIZE BIND: TWO of `finalize_other_proof`'s FOUR conjuncts stop being
testimony, and `PICKLES_OK`'s residue narrows for the second time.

## ⚑ THE CLAIM IS §1d's, AND IT IS NOT RESTATED HERE

§1d names, exactly, what a verifying STARK over `dregg-mina-wrap-conjunction::v1` establishes (two of
four conjuncts, the reciprocity weld, the opening's non-free coefficients), what is ABSENT BY
CONSTRUCTION and why (`cipCorrect` / `plonkChecksPassed`, the free-`ft_eval0` vacuity), and what the
bind does NOT buy (ξ is a free column in the sub-proof; the weld is
`mina_wrap_finalize_fold.rs::fold_endo_into_finalize`'s 32 `cb.connect`s, a CONSUMER check). This
section is the MECHANISM only. **Do not quote this section without §1d.**

## The two defects this closes, both measurable on the emitted bytes

1. **`PICKLES_WITNESSED` carried four conjuncts as one felt.** Setting it cost a prover nothing, and
   the tree's own sentence about it was *"dregg does not verify Mina's proof; it accepts a boolean
   saying someone did."* Two of the four now cost a 16-row, 2 536-column sub-proof.
2. **Nothing in the LIGHT-CLIENT path named the conjunction descriptor.** It proves, and
   `circuit-prove/src/mina_wrap_finalize_fold.rs` embeds its bytes for the aggregation circuit — but
   the head descriptor did not, so a re-emit could change its shape without moving a single byte of
   `dregg-mina-lightclient-verify-v1.json`. This leg puts its fingerprint IN those bytes, which is
   what turns a shape change into a flag day rather than a silence.

## The mechanism: ONE leg, NINE LANES — the shape §2b and §2c already have

Guard `FINALIZE_XI_B_PROVED`; the attested program is the nine `CONJ_VK` columns pinned lane by lane
to the conjunction descriptor's semantic fingerprint; the declared commitment is the nine PI-bound
`CONJ_PI` columns. `8·29 + 24 = 256` bits exactly, the encoding machine-checked injective
(`fieldToLanes9_injective`), and `BindLeg.mainRailOk` refuses a pin that names a PREFIX of the lanes.

⚑ **`bound` is `none`, and that is the STRONGER choice here, not a laxer one — the same reason
`linkBindLeg` gives.** `bound` forces the `commit` EXPRESSION to equal a row-local expression, and it
exists because the deployed `customProofBind` carries `commit` as a FREE column. Here `commit` is
`.var (CONJ_PI i)` — a **PI-BOUND** column (slots 30..38). A `bound` congruence could only compare it
to itself, which is decoration (`feedback-a-pin-against-its-own-definition-is-decoration`). The
commitment being PUBLIC is strictly more than its being tied to another witness. -/

/-- ⚑⚑ **THE CONJUNCTION SUB-PROOF'S PROGRAM IDENTITY, AS NINE LANES — measured, never invented.**
The `Faithful9` key lanes of
`effect_vm_descriptor2_semantic_fingerprint(dregg-mina-wrap-conjunction::v1)` — blake3 (derive-key,
context `EFFECT_VM_DESCRIPTOR2_FINGERPRINT_CONTEXT`) over that descriptor's CANONICAL bytes. In this
tree the descriptor IS the verifying key: `verify_vm_descriptor2(&desc, &proof, &pis)` takes no other
key material, so the semantic fingerprint of the descriptor is exactly the program identity a
recursion bind should name.

⚠ **FLAG DAY, and it is the same real coupling `CHAINLINK_VK_LANES` and `LINK_VK_LANES` carry:**
re-emitting `mina-wrap-conjunction.json` MOVES THIS LITERAL and therefore **re-emits and re-VKs THIS
descriptor**. That is intended — a light client must not keep accepting sub-proofs of a program that
changed shape. And it has already bitten once at this exact seam class: `75df624cf` re-emitted
`pasta-fq-wraplink.json`, the pinned literal here did not follow, and for a day the bind named a
program no descriptor in this tree had. The two independent sources are what make a pin a gate, so
this one needs its Rust reader too — see the flag-day section of this file's header for what is owed
and has NOT yet landed.

⚑ **PROVENANCE, so this is a MEASUREMENT and not a transcription.** Measured 2026-08-06 by
`circuit/examples/conj_fingerprint.rs` over the SERVED artifact, twice and independently (two lanes,
identical output), against the file on disk rather than a re-emit:

    $ cargo run -p dregg-circuit --release --example conj_fingerprint -- \
        circuit/descriptors/by-name/mina-wrap-conjunction.json
    … dregg-mina-wrap-conjunction::v1  w=2536  pi=160  cons=4317
      fp=dc26ae9a7ad4e174e230cf6296c82f8ab22b418fb94b9b3e949205f2535d9008
      lanes=[447620828, 118399956, 332150941, 529607877, 314255522, 98355104, 173079149,
             176046258, 561245]

`w=2536 / pi=160 / cons=4317` is the shape `MinaWrapConjunctionAir` §9b's own flag day states, so the
bytes fingerprinted here are the post-`piCount` object and not the 0-PI one that preceded it. Lane 8
is `561245 < 2^24`, as `Faithful9` requires. -/
def CONJ_VK_LANES : List ℤ :=
  [447620828, 118399956, 332150941, 529607877, 314255522, 98355104, 173079149, 176046258, 561245]

/-- The `i`-th pinned conjunction-program lane, as the `vkPin` literal the leg carries. -/
def conjVkLane (i : Nat) : ℤ := CONJ_VK_LANES.getD i 0

/-- ⚑⚑⚑ **THE FINALIZE-BIND LEG.** Guard `FINALIZE_XI_B_PROVED`; the declared commitment is the nine
PI-bound `CONJ_PI` columns; the attested program is the nine `CONJ_VK` columns, pinned to the
conjunction descriptor's fingerprint. `bound := none` — see §2d for why that is the stronger choice
and not a laxer one. -/
def conjBindLeg : AirLeg :=
  .bind { guard := .var FINALIZE_XI_B_PROVED
        , commit := (List.range 9).map (fun i => .var (CONJ_PI i))
        , vk := (List.range 9).map (fun i => .var (CONJ_VK i))
        , vkPin := some CONJ_VK_LANES
        , bound := none }

/-- The finalize-bind legs — exactly one. -/
def conjBindLegs : List AirLeg := [conjBindLeg]

/-- The nine conjunction-commitment PI pins (cols 68..76 → PI 30..38), written out in the same shape
as `subPiPins` rather than folded, so the emission slice below reduces with no fold. -/
def conjPiPins : List AirLeg :=
  [ .pin ⟨VmRow.first, CONJ_PI 0, PI_CONJ_PI 0⟩
  , .pin ⟨VmRow.first, CONJ_PI 1, PI_CONJ_PI 1⟩
  , .pin ⟨VmRow.first, CONJ_PI 2, PI_CONJ_PI 2⟩
  , .pin ⟨VmRow.first, CONJ_PI 3, PI_CONJ_PI 3⟩
  , .pin ⟨VmRow.first, CONJ_PI 4, PI_CONJ_PI 4⟩
  , .pin ⟨VmRow.first, CONJ_PI 5, PI_CONJ_PI 5⟩
  , .pin ⟨VmRow.first, CONJ_PI 6, PI_CONJ_PI 6⟩
  , .pin ⟨VmRow.first, CONJ_PI 7, PI_CONJ_PI 7⟩
  , .pin ⟨VmRow.first, CONJ_PI 8, PI_CONJ_PI 8⟩ ]

/-! ## §3 — ⚑ THE SOURCE AIR, and the descriptor as the COMPILER'S OUTPUT.

Nine `.gate` legs, four `.lookup` legs against the declared range table, two `.limbs` legs, two
narrow-table lookups, thirty-nine `.pin` legs and three nine-lane `.bind` legs, in emission order.
`EffectAir`'s vocabulary was ADEQUATE — nothing here needed a word `Circuit/EffectAirIR.lean` did
not already have, and `minaHeadAir_mainRailOk` decides that on the emitted predicate rather than by
eye.

⚑ **EMISSION ORDER IS CONSTRAINT ORDER, AND EVERY RUNG SINCE 2026-08-05 HAS APPENDED.** The
`WRAP_FS_PROVED` block lands at 51..61, the segment bind at 62, and the finalize block at 63..73 —
so a `rfl` slice written against an earlier rung still addresses the constraint it was written for. -/

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
      -- ⚑⚑ ADDED 2026-08-03 — the leg that makes `SUBMIT_H ≤ BLOCK_LEN` a GATE rather than a
      -- verifier convention. `REQ_DEPTH` carried NO range lookup: it was PI-pinned and otherwise
      -- free, so a prover could put a NEGATIVE required depth on the wire, meet G5's
      -- `DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH` with a non-negative slack, and drive `WIT_DEPTH` — and
      -- therefore `BLOCK_LEN − SUBMIT_H` — negative. A settlement submitted ABOVE the verified tip
      -- satisfied every emitted constraint. The only thing that caught it was a verifier that read
      -- `PI[19]` and compared it to 290 by hand, which is a convention and not a check.
      --
      -- One lookup closes it, on the table already declared, with NO new column and no width change:
      -- `0 ≤ REQ_DEPTH` plus `0 ≤ DEPTH_SLACK` gives `0 ≤ WIT_DEPTH` from G5, and G2 turns that into
      -- `SUBMIT_H ≤ BLOCK_LEN` (`minaLcAir_forces_submit_within_the_segment`).
      , rangeLeg REQ_DEPTH
      , .gate linkC
      , .gate openingWitnessedC
      , .gate canonC
      -- ⚑ §1a — the DERIVED canonicality of the two `Fp` elements this descriptor carries.
      , lowLanesLeg anchorLowLanes
      , topLaneLeg (ANCHOR_STATE 8)
      , lowLanesLeg tipLowLanes
      , topLaneLeg (TIP_STATE 8) ]
      ++ anchorStatePins ++ tipStatePins
      ++ [ .pin ⟨VmRow.first, BLOCK_LEN, PI_BLOCK_LEN⟩
         , .pin ⟨VmRow.first, REQ_DEPTH, PI_REQ_DEPTH⟩
         -- ⚑ 2026-08-05 — the anchor HEIGHT leaves the proof. Before this leg G1's
         -- `BLOCK_LEN = ANCHOR_H + SEG_LEN` related three prover-chosen numbers and the consumer
         -- could see only the sum. See `ANCHOR_H`'s docstring for what a pin does NOT do.
         , .pin ⟨VmRow.first, ANCHOR_H, PI_ANCHOR_H⟩ ]
      -- ⚑⚑ §2b — THE RECURSION CARRIER AND ITS NINE BINDS. The first leg in this file whose `= 1`
      -- a prover cannot simply write down.
      ++ [.gate wrapFsC] ++ wrapBindLegs ++ subPiPins
      -- ⚑⚑⚑ §2c, 2026-08-05 — THE SEGMENT BIND, APPENDED LAST ON PURPOSE. Emission order is
      -- constraint order, and every `rfl` slice in §3a addresses a constraint by INDEX; appending
      -- leaves 0..61 exactly where they were and puts the new seam at 62. A leg inserted mid-list
      -- would have moved eighteen canonicality lookups and twenty-one pins under their own pins,
      -- which is churn no reader can check.
      ++ linkBindLegs
      -- ⚑⚑⚑ §2d, 2026-08-06 — THE FINALIZE BIND, APPENDED AFTER IT, FOR THE SAME REASON. The gate
      -- lands at 63, the bind at 64 and the nine commitment pins at 65..73; constraints 0..62 —
      -- including the segment bind at 62 — do not move, so every `rfl` slice above addresses the
      -- constraint it was written against. The nine PI SLOTS are appended too (30..38), so
      -- `PI_ANCHOR_H` stays at 29 and no consumer offset is re-indexed.
      ++ [.gate finalizeXiBC] ++ conjBindLegs ++ conjPiPins }

/-- ⚑ **THE VOCABULARY WAS ADEQUATE.** Every leg is main-rail expressible, decided on the emitted
predicate — so no leg lowered to `EffectLower.refuseConstraints` and nothing was hand-written around
the compiler. This is the §3 finding stated as a theorem rather than a sentence. -/
theorem minaHeadAir_mainRailOk : minaHeadAir.mainRailOk = true := by rfl

/-- Every declared PI pin indexes a slot the descriptor declares. -/
theorem minaHeadAir_pinsFit : minaHeadAir.pinsFit MINA_PI_COUNT = true := by rfl

/-- The source carries 60 legs: 8 gates + 3 slack lookups + ⚑ the `REQ_DEPTH` lookup + 2 `.limbs` +
2 top-lane lookups + ⚑ 21 PI pins (the 21st is `ANCHOR_H`, 2026-08-05) + ⚑ the `WRAP_FS_PROVED` gate
+ ⚑ ONE nine-lane `.bind` leg (was nine one-felt legs before the widening) + 9 sub-proof PI pins
+ ⚑ ONE nine-lane `.bind` leg for the SEGMENT sub-proof (2026-08-05, §2c)
+ ⚑⚑ the `FINALIZE_XI_B_PROVED` gate, ONE nine-lane `.bind` leg for the CONJUNCTION sub-proof and 9
conjunction-commitment PI pins (2026-08-06, §2d) — eleven more legs than yesterday.
⚑ A `.limbs` leg is ONE leg and EIGHT constraints — `minaLcVerifyDesc_constraint_count` is the
number a dropped lane moves, and this one is not. -/
theorem minaHeadAir_leg_count : minaHeadAir.legs.length = 60 := by rfl

/-- ⚑⚑ **ONE RECURSION BIND, NINE LANES, AND NOT THE DECLARATIVE SHAPE.** `bindCount` is the number
a re-emission that dropped the sub-proof obligation would move while every other shape count sat
still; `mainRailOk` (already `true` above) additionally decides that the leg is neither the unpinned
shape nor a narrow one — since the widening `BindLeg.mainRailOk` is FALSE on `vkPin = none ∧ bound =
none`, on fewer lanes than `PROOF_BIND_MIN_LANES`, and on a pin that names fewer lanes than its
vector. A `true` verdict on this air block IS the statement that its recursion seam names a program
AT ITS FULL WIDTH. -/
theorem minaHeadAir_bind_shape :
    minaHeadAir.bindCount = 3
      ∧ ((wrapBindLegs ++ linkBindLegs ++ conjBindLegs).all
          Dregg2.Circuit.EffectAirIR.AirLeg.mainRailOk) = true := by
  refine ⟨rfl, rfl⟩

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

/-- ⚑ **THE TIED SOURCE** — `minaHeadAir` carrying its two decidable verdicts in its TYPE:
`mainRailOk` (main-rail expressible) and `pinsTied` (every published column is DERIVED by another
leg). A `TiedAir` cannot be built for a block that publishes a column nothing else constrains, so a
decorative pin is unrepresentable here rather than detectable by a census afterwards. -/
def minaHeadTiedAir : Dregg2.Circuit.Emit.EffectLower.TiedAir where
  air := minaHeadAir

/-- **`minaLcVerifyDesc` — COMPILER OUTPUT.** The Mina anchored-head light-client verify decision as
an IR-v2 AIR. Not modelled beside a hand-written twin; there is no twin.

⚠ `lowerAir`, not `lowerEffect`: this descriptor is not a full-state effect and has no digest wires,
so the framework's `PIBindsDigests` surface would emit a descriptor nobody deployed. The two entry
points share the normalizer, the leg lowerings and the emission order and differ ONLY in that
surface. -/
def minaLcVerifyDesc : EffectVmDescriptor2 :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-lightclient-verify::v1" MINA_LC_WIDTH MINA_PI_COUNT [] minaHeadTiedAir).val

/-- ⚑ **THE CERTIFICATE, produced by the emit.** Every leg of the source is FORCED by the emitted
descriptor's constraints on any row window that satisfies them — `AirLeg.forces`, stated in the
SOURCE's vocabulary and never mentioning the lowering, so it is not `P → P`. Not re-derived here.

**Zero bytes move**: `lowerTiedAir … |>.val` is `lowerAir …` by `rfl`. -/
theorem minaLcVerifyDesc_certified :
    Dregg2.Circuit.Emit.EffectLower.CertifiedRefines minaLcVerifyDesc [] minaHeadAir :=
  (Dregg2.Circuit.Emit.EffectLower.lowerTiedAir
    "dregg-mina-lightclient-verify::v1" MINA_LC_WIDTH MINA_PI_COUNT [] minaHeadTiedAir).property

/-- ⚑ **THE ZERO.** The certified lowering emits the term the bare lowering emitted, by `rfl` — so
the migration changed what this definition PROVES, not what it PRODUCES. No re-emit, no VK rotation.
Also the unfolding lemma for the cost/shape proofs below, which reason through `lowerAir`. -/
theorem minaLcVerifyDesc_eq_lowerAir :
    minaLcVerifyDesc = Dregg2.Circuit.Emit.EffectLower.lowerAir "dregg-mina-lightclient-verify::v1" MINA_LC_WIDTH MINA_PI_COUNT [] minaHeadAir := rfl

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

/-- The compiler emitted 74 constraints from 60 legs: one per leg, except the two `.limbs` legs which
lower to EIGHT lookups each (`60 + 2·7 = 74`). ⚑ A dropped lane moves this number and nothing else
does — which is why the count is pinned separately from the leg count.
(`EffectLower.lowerLeg_ne_nil` is the general statement that no leg can vanish; this is the exact
arithmetic at this descriptor.) ⚑ **63 → 74 on 2026-08-06:** the `FINALIZE_XI_B_PROVED` gate, the
finalize `proofBind`, and nine conjunction-commitment PI pins. -/
theorem minaLcVerifyDesc_constraint_count : minaLcVerifyDesc.constraints.length = 74 := rfl

/-- ⚑⚑ **THE `proofBind` CONSTRAINT, AS THE COMPILER EMITTED IT** — the whole recursion declaration,
on the bytes, at its emitted position (52; 51 is the `WRAP_FS_PROVED` gate).
⚑ It was NINE constraints at 52..60 until the 2026-08-05 widening; it is ONE constraint carrying the
same nine columns and nine literals as LANE VECTORS, and the eight positions it freed shift every
constraint after it down by eight.

This is the object the carrier's content IS. A leg that lost a `vkPin` lane, or whose `vk` drifted
onto another column, or whose declared commitment stopped being the PI-bound lane, moves this
`rfl`. -/
theorem minaLcVerifyDesc_proof_binds :
    (minaLcVerifyDesc.constraints.drop 52).take 1 =
      [ .proofBind ⟨.var WRAP_FS_PROVED
                   , [.var (SUB_PI 0), .var (SUB_PI 1), .var (SUB_PI 2), .var (SUB_PI 3)
                     , .var (SUB_PI 4), .var (SUB_PI 5), .var (SUB_PI 6), .var (SUB_PI 7)
                     , .var (SUB_PI 8)]
                   , [.var (SUB_VK 0), .var (SUB_VK 1), .var (SUB_VK 2), .var (SUB_VK 3)
                     , .var (SUB_VK 4), .var (SUB_VK 5), .var (SUB_VK 6), .var (SUB_VK 7)
                     , .var (SUB_VK 8)]
                   , some CHAINLINK_VK_LANES, none⟩ ] := rfl

/-- ⚑ **AND NOT ONE OF THEM IS DECLARATIVE, MEASURED ON THE EMITTED DESCRIPTOR.**
`proofBindDeclarative` is the tree's census of recursion seams that pin neither program nor
commitment — the shape whose existential quantifies over every program and every statement. This
descriptor contributes THREE binds and ZERO to that census. -/
theorem minaLcVerifyDesc_no_declarative_binds :
    (Dregg2.Circuit.DescriptorIR2.proofBindsOf minaLcVerifyDesc).length = 3
      ∧ Dregg2.Circuit.DescriptorIR2.proofBindDeclarative minaLcVerifyDesc = 0 := by
  refine ⟨rfl, rfl⟩

/-- ⚑⚑⚑ **THE SEGMENT BIND, AS THE COMPILER EMITTED IT** — the whole §2c declaration, on the bytes,
at its emitted position (62; it was the LAST constraint until §2d appended eleven more on
2026-08-06, and it did not move, which is what appending is for). Its `commit` is the row's nine PUBLISHED
`TIP_STATE` columns and nothing else, which is the entire content of "the head's claimed tip is tied
to the evidence": a leg whose commitment drifted onto a free column, or whose `vkPin` lost a lane,
moves this `rfl`. -/
theorem minaLcVerifyDesc_link_bind :
    (minaLcVerifyDesc.constraints.drop 62).take 1 =
      [ .proofBind ⟨.var LINK_OK
                   , [.var (TIP_STATE 0), .var (TIP_STATE 1), .var (TIP_STATE 2), .var (TIP_STATE 3)
                     , .var (TIP_STATE 4), .var (TIP_STATE 5), .var (TIP_STATE 6), .var (TIP_STATE 7)
                     , .var (TIP_STATE 8)]
                   , [.var (LINK_VK 0), .var (LINK_VK 1), .var (LINK_VK 2), .var (LINK_VK 3)
                     , .var (LINK_VK 4), .var (LINK_VK 5), .var (LINK_VK 6), .var (LINK_VK 7)
                     , .var (LINK_VK 8)]
                   , some LINK_VK_LANES, none⟩ ] := rfl

/-- ⚑⚑⚑ **THE FINALIZE BIND, AS THE COMPILER EMITTED IT** — the whole §2d declaration, on the bytes,
at its emitted position (64; 63 is the `FINALIZE_XI_B_PROVED` gate, 65..73 the nine commitment pins).
A leg whose `vkPin` lost a lane, or whose `vk` drifted onto another column, or whose declared
commitment stopped being the PI-bound `CONJ_PI` lane, moves this `rfl`. -/
theorem minaLcVerifyDesc_conj_bind :
    minaLcVerifyDesc.constraints.drop 64 =
      [ .proofBind ⟨.var FINALIZE_XI_B_PROVED
                   , [.var (CONJ_PI 0), .var (CONJ_PI 1), .var (CONJ_PI 2), .var (CONJ_PI 3)
                     , .var (CONJ_PI 4), .var (CONJ_PI 5), .var (CONJ_PI 6), .var (CONJ_PI 7)
                     , .var (CONJ_PI 8)]
                   , [.var (CONJ_VK 0), .var (CONJ_VK 1), .var (CONJ_VK 2), .var (CONJ_VK 3)
                     , .var (CONJ_VK 4), .var (CONJ_VK 5), .var (CONJ_VK 6), .var (CONJ_VK 7)
                     , .var (CONJ_VK 8)]
                   , some CONJ_VK_LANES, none⟩ ]
      ++ [ .base (.piBinding VmRow.first (CONJ_PI 0) (PI_CONJ_PI 0))
         , .base (.piBinding VmRow.first (CONJ_PI 1) (PI_CONJ_PI 1))
         , .base (.piBinding VmRow.first (CONJ_PI 2) (PI_CONJ_PI 2))
         , .base (.piBinding VmRow.first (CONJ_PI 3) (PI_CONJ_PI 3))
         , .base (.piBinding VmRow.first (CONJ_PI 4) (PI_CONJ_PI 4))
         , .base (.piBinding VmRow.first (CONJ_PI 5) (PI_CONJ_PI 5))
         , .base (.piBinding VmRow.first (CONJ_PI 6) (PI_CONJ_PI 6))
         , .base (.piBinding VmRow.first (CONJ_PI 7) (PI_CONJ_PI 7))
         , .base (.piBinding VmRow.first (CONJ_PI 8) (PI_CONJ_PI 8)) ] := rfl

/-- ⚑⚑ **AND THE TIP LANES ARE THE COMMITMENT — the statement the connectivity census reads.**
Every published tip column appears in the segment bind's `commit` vector, so the emitted constraint
NAMES all nine of them beside the guard and the nine pinned program lanes. This is the object
`LightClientAnchorConnectivity.minaVerify_tip_lanes_are_published_and_joined` measures from the other
side; stating it here too means a re-point that quietly moved the commitment off `TIP_STATE` reds in
the file that authored it, not only in the census. -/
theorem mina_link_bind_commits_the_tip_lanes :
    ((Dregg2.Circuit.DescriptorIR2.proofBindsOf minaLcVerifyDesc).getD 1
        ⟨.const 0, [], [], none, none⟩).commit
      = (List.range 9).map (fun i => Dregg2.Exec.CircuitEmit.EmittedExpr.var (TIP_STATE i)) := rfl

/-- ⚑ **AND THE SEAM DECLARES NINE LANES ON BOTH HALVES, PINNED ON EVERY ONE.** The width verdict on
the emitted object: `commit` and `vk` agree in length, the length is at or above the floor, and the
`vkPin` names EXACTLY as many lanes as `vk` — a prefix pin would be refused here and unsatisfiable in
the AIR. -/
theorem minaLcVerifyDesc_bind_is_nine_lanes :
    ((Dregg2.Circuit.DescriptorIR2.proofBindsOf minaLcVerifyDesc).all
        (fun m => m.widthOk && m.commit.length == 9)) = true := by
  rfl

/-- ⚑ **THE PROGRAM PIN IS NINE LANES WIDE, AND THE NUMBER IS SAID OUT LOUD.** A single-felt tie is
worth `2^31`; nine `Faithful9` lanes cover `8·29 + 24 = 256` bits exactly, and the lanes are
DISTINCT columns so a forger must match all nine. This states the width as arithmetic rather than as
a sentence in a docblock: the nine pinned literals are pairwise on distinct columns, every lane is a
canonical `Faithful9` digit, and the reconstruction is the fingerprint's 256-bit value. -/
theorem mina_program_pin_is_nine_lanes :
    CHAINLINK_VK_LANES.length = 9
      ∧ ((List.range 8).all fun i => decide (CHAINLINK_VK_LANES.getD i 0 < 2 ^ 29)) = true
      ∧ CHAINLINK_VK_LANES.getD 8 0 < 2 ^ 24
      ∧ (List.range 9).map SUB_VK = [31, 32, 33, 34, 35, 36, 37, 38, 39]
      ∧ (List.range 9).map SUB_PI = [40, 41, 42, 43, 44, 45, 46, 47, 48] := by
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  decide

/-- ⚑ **AND THE SEGMENT PROGRAM PIN IS NINE LANES TOO — the same arithmetic, said again rather than
inherited.** Nine canonical `Faithful9` digits on nine DISTINCT columns, so a forger must match all
nine of `dregg-mina-lightclient-link::v1`'s fingerprint lanes; a single-felt tie would have been
worth `2^31`. ⚠ The two pins must NOT be equal — a seam that pinned the chainlink fingerprint for
both sub-proofs would be one bind wearing two names, and the last conjunct is what refuses it. -/
theorem mina_link_program_pin_is_nine_lanes :
    LINK_VK_LANES.length = 9
      ∧ ((List.range 8).all fun i => decide (LINK_VK_LANES.getD i 0 < 2 ^ 29)) = true
      ∧ LINK_VK_LANES.getD 8 0 < 2 ^ 24
      ∧ (List.range 9).map LINK_VK = [49, 50, 51, 52, 53, 54, 55, 56, 57]
      ∧ LINK_VK_LANES ≠ CHAINLINK_VK_LANES := by
  refine ⟨rfl, rfl, ?_, rfl, ?_⟩ <;> decide

/-- ⚑⚑ **AND THE CONJUNCTION PROGRAM PIN IS NINE LANES TOO — the same arithmetic, said a third time
rather than inherited.** Nine canonical `Faithful9` digits on nine DISTINCT columns, so a forger must
match all nine of `dregg-mina-wrap-conjunction::v1`'s fingerprint lanes; a single-felt tie would have
been worth `2^31`. ⚠ The three pins must be PAIRWISE DISTINCT — a seam that pinned one fingerprint for
several sub-proofs would be one bind wearing three names, and the last two conjuncts refuse it.

⚑ **AND THE FIRST CONJUNCT IS WHAT CATCHES AN UNMEASURED LITERAL.** `CONJ_VK_LANES` is a MEASURED
fingerprint, not a hand-written one; a placeholder nonet of zeros — the shape a lane leaves behind
when it drafts the seam before running the emitter — fails `conjVkLane 0 ≠ 0` here and cannot ship. -/
theorem mina_conj_program_pin_is_nine_lanes :
    conjVkLane 0 ≠ 0
      ∧ CONJ_VK_LANES.length = 9
      ∧ ((List.range 8).all fun i => decide (CONJ_VK_LANES.getD i 0 < 2 ^ 29)) = true
      ∧ CONJ_VK_LANES.getD 8 0 < 2 ^ 24
      ∧ (List.range 9).map CONJ_VK = [59, 60, 61, 62, 63, 64, 65, 66, 67]
      ∧ (List.range 9).map CONJ_PI = [68, 69, 70, 71, 72, 73, 74, 75, 76]
      ∧ CONJ_VK_LANES ≠ CHAINLINK_VK_LANES
      ∧ CONJ_VK_LANES ≠ LINK_VK_LANES := by
  refine ⟨?_, rfl, rfl, ?_, rfl, rfl, ?_, ?_⟩ <;> decide

/-- ⚑ **THE SIXTEEN LANE LOOKUPS AND THE TWO TOP-LANE LOOKUPS, AT THEIR EMITTED POSITIONS.** `rfl` on
a slice of the compiler's output: constraints 12..19 are the anchor's low lanes at 29 bits, 20 is the
anchor's TOP lane on the NARROW table, 21..28 the tip's low lanes, 29 the tip's top lane.
⚑ Each index is ONE HIGHER than before 2026-08-03: the `REQ_DEPTH` range leg is emitted at 8. A leg that
lost a lane, or a top-lane query that drifted onto the wide table, moves this. -/
theorem minaLcVerifyDesc_canon_lookups :
    (minaLcVerifyDesc.constraints.drop 12).take 18 =
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
output: constraint 3 is the segment tooth, 5 the anchor tooth, 7 the depth-slack tooth and ⚑ **8 the
`REQ_DEPTH` tooth added 2026-08-03**. A leg that lowered
to `EffectLower.refuseConstraints` would emit a `.boundary` pair here instead and this goes red. -/
theorem minaLcVerifyDesc_slack_lookups :
    (minaLcVerifyDesc.constraints.drop 3).take 1
        = [.lookup ⟨TableId.range, [.var SEG_SLACK]⟩]
      ∧ (minaLcVerifyDesc.constraints.drop 5).take 1
        = [.lookup ⟨TableId.range, [.var ANCH_SLACK]⟩]
      ∧ (minaLcVerifyDesc.constraints.drop 7).take 1
        = [.lookup ⟨TableId.range, [.var DEPTH_SLACK]⟩]
      ∧ (minaLcVerifyDesc.constraints.drop 8).take 1
        = [.lookup ⟨TableId.range, [.var REQ_DEPTH]⟩] :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- ⚑ **THE TWENTY-ONE PI PINS, AS THE COMPILER EMITTED THEM** — the addressing layer AND the dregg
state write, in one `rfl`. Nine pinned-anchor limbs, nine verified-tip limbs, the DERIVED height, the
depth policy met, ⚑ and the anchor HEIGHT (2026-08-05, PI slot 29). A reordering, a dropped pin or a
re-indexed slot moves this. -/
theorem minaLcVerifyDesc_pins :
    (minaLcVerifyDesc.constraints.drop 30).take 21 =
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
      , .base (.piBinding VmRow.first REQ_DEPTH PI_REQ_DEPTH)
      , .base (.piBinding VmRow.first ANCHOR_H PI_ANCHOR_H) ] := rfl

/-- ⚑ **THE NINE SUB-PROOF-COMMITMENT PINS** (constraints 53..61; they were 61..69 before the
2026-08-05 widening collapsed nine one-felt binds into one nine-lane bind). Without these the commitment the
recursion existential quantifies over would be a hidden column and the consumer would have nothing to
compare a sub-proof's public inputs against. -/
theorem minaLcVerifyDesc_subpi_pins :
    (minaLcVerifyDesc.constraints.drop 53).take 9 =
      [ .base (.piBinding VmRow.first (SUB_PI 0) (PI_SUB_PI 0))
      , .base (.piBinding VmRow.first (SUB_PI 1) (PI_SUB_PI 1))
      , .base (.piBinding VmRow.first (SUB_PI 2) (PI_SUB_PI 2))
      , .base (.piBinding VmRow.first (SUB_PI 3) (PI_SUB_PI 3))
      , .base (.piBinding VmRow.first (SUB_PI 4) (PI_SUB_PI 4))
      , .base (.piBinding VmRow.first (SUB_PI 5) (PI_SUB_PI 5))
      , .base (.piBinding VmRow.first (SUB_PI 6) (PI_SUB_PI 6))
      , .base (.piBinding VmRow.first (SUB_PI 7) (PI_SUB_PI 7))
      , .base (.piBinding VmRow.first (SUB_PI 8) (PI_SUB_PI 8)) ] := rfl

/-- Layout sanity, as theorems rather than guards: the two nine-lane anchors are contiguous,
disjoint and inside the declared width, and nine base-`2^29` lanes cover a 256-bit value exactly
(`8·29 + 24 = 256`). -/
theorem mina_layout_wellformed :
    ANCHOR_STATE 0 = 12 ∧ ANCHOR_STATE 8 = 20 ∧ TIP_STATE 0 = 21 ∧ TIP_STATE 8 = 29
      ∧ TIP_STATE 8 < MINA_LC_WIDTH ∧ BLOCK_LEN < ANCHOR_STATE 0
      ∧ PI_TIP_STATE 8 < PI_BLOCK_LEN ∧ PI_REQ_DEPTH < MINA_PI_COUNT
      ∧ SUB_PI 8 < MINA_LC_WIDTH ∧ PI_SUB_PI 8 < MINA_PI_COUNT
      -- ⚑ 2026-08-05, §2c: nine more columns and NOT ONE more public input. The segment seam's
      -- commitment is the tip block the descriptor ALREADY published, so the statement did not
      -- widen — an existing publication became load-bearing.
      ∧ LINK_VK 0 = 49 ∧ LINK_VK 8 = 57 ∧ LINK_VK 8 < MINA_LC_WIDTH
      -- ⚑⚑ 2026-08-06, §2d: nineteen more columns and NINE more public inputs. Unlike the segment
      -- seam, the finalize seam's commitment is NOT a block this descriptor already published, so
      -- the statement DID widen — and the nine new slots are APPENDED at 30..38, leaving
      -- `PI_ANCHOR_H` at 29 and every earlier offset exactly where a consumer already reads it.
      ∧ FINALIZE_XI_B_PROVED = 58 ∧ CONJ_VK 0 = 59 ∧ CONJ_VK 8 = 67
      ∧ CONJ_PI 0 = 68 ∧ CONJ_PI 8 = 76 ∧ CONJ_PI 8 < MINA_LC_WIDTH
      ∧ PI_ANCHOR_H = 29 ∧ PI_CONJ_PI 0 = 30 ∧ PI_CONJ_PI 8 = 38 ∧ PI_CONJ_PI 8 < MINA_PI_COUNT
      ∧ MINA_LC_WIDTH = 77 ∧ MINA_PI_COUNT = 39
      ∧ 29 * (STATE_LIMBS - 1) + 24 = 256 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, ?_,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_, rfl, rfl, ?_⟩ <;> decide

/-- The five carriers are real hidden trace columns and none is PI-bound: a carrier a verifier could
set from outside the proof would be no carrier at all. ⚑ `WRAP_FS_PROVED` is hidden for the same
reason, and its CONTENT is elsewhere — the nine `proofBind` legs it guards. -/
theorem mina_carriers_hidden :
    LINK_OK < MINA_LC_WIDTH ∧ PICKLES_OPENING_WITNESSED < MINA_LC_WIDTH ∧ CANON_OK < MINA_LC_WIDTH
      ∧ WRAP_FS_PROVED < MINA_LC_WIDTH
      ∧ LINK_OK < BLOCK_LEN ∧ PICKLES_OPENING_WITNESSED < BLOCK_LEN ∧ CANON_OK < BLOCK_LEN
      ∧ ¬ (∃ i < STATE_LIMBS, WRAP_FS_PROVED = SUB_PI i)
      -- ⚑ …and the SEGMENT seam's program lanes are hidden columns disjoint from the chainlink
      -- seam's, so the two binds cannot be one bind read twice.
      ∧ ¬ (∃ i < STATE_LIMBS, ∃ j < STATE_LIMBS, LINK_VK i = SUB_VK j)
      ∧ ¬ (∃ i < STATE_LIMBS, ∃ j < STATE_LIMBS, LINK_VK i = SUB_PI j)
      -- ⚑⚑ …and the FINALIZE seam's carrier and program lanes are hidden and disjoint from BOTH,
      -- so the three binds cannot be one bind read three times. Its COMMITMENT lanes are the one
      -- half that is deliberately public, which is the whole reason `bound` can be `none` (§2d).
      ∧ FINALIZE_XI_B_PROVED < MINA_LC_WIDTH
      ∧ ¬ (∃ i < STATE_LIMBS, FINALIZE_XI_B_PROVED = CONJ_PI i)
      ∧ ¬ (∃ i < STATE_LIMBS, ∃ j < STATE_LIMBS, CONJ_VK i = SUB_VK j)
      ∧ ¬ (∃ i < STATE_LIMBS, ∃ j < STATE_LIMBS, CONJ_VK i = LINK_VK j)
      ∧ ¬ (∃ i < STATE_LIMBS, ∃ j < STATE_LIMBS, CONJ_PI i = SUB_PI j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

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

theorem openingWitnessedC_holds_iff (a : Assignment) :
    openingWitnessedC.holds a ↔ a PICKLES_OPENING_WITNESSED = 1 := Iff.rfl

theorem canonC_holds_iff (a : Assignment) : canonC.holds a ↔ a CANON_OK = 1 := Iff.rfl

theorem wrapFsC_holds_iff (a : Assignment) : wrapFsC.holds a ↔ a WRAP_FS_PROVED = 1 := Iff.rfl

theorem finalizeXiBC_holds_iff (a : Assignment) :
    finalizeXiBC.holds a ↔ a FINALIZE_XI_B_PROVED = 1 := Iff.rfl

/-! ## §5 — `airAccepts`: the descriptor's acceptance predicate on one row.

The nine gate residuals vanish and the three slacks lie in the range interval `[0, 2^24)` — the
denotation `DescriptorIR2.range_row_mem_iff` connects the emitted lookups to. This is "the descriptor
accepts this row"; the thirty-nine PI pins are the addressing / state-write layer around it. -/

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
  -- ⚑ THE DEPTH-POLICY TOOTH, added 2026-08-03: `REQ_DEPTH` carried no lookup at all, and that is
  -- exactly why `SUBMIT_H ≤ BLOCK_LEN` was unforced.
  ∧ inRange a REQ_DEPTH
  ∧ linkC.holds a ∧ openingWitnessedC.holds a ∧ canonC.holds a
  -- ⚑ G9, 2026-08-05: the recursion carrier. Its content is `bindAccepts`, not this gate — what
  -- this gate buys is that the guard cannot be set to `0` to switch the nine seams off.
  ∧ wrapFsC.holds a
  -- ⚑⚑ G10, 2026-08-06: the FINALIZE carrier, APPENDED so every conjunct index above is unmoved.
  -- Its content is `conjBindAccepts`; this gate is what stops the guard being `0`.
  ∧ finalizeXiBC.holds a

/-- ⚑ **THE PREDICATE AS IT WAS BEFORE THE `REQ_DEPTH` LOOKUP** — kept for exactly one purpose: to
state, as a theorem rather than a claim, that a row with a NEGATIVE required depth used to be
accepted and is now refused (`mina_negative_req_depth_old_admits_new_rejects`). It is not a
compatibility surface and nothing else reads it. -/
def verifyAcceptsWithoutDepthPolicyRange (a : Assignment) : Prop :=
  blockLenC.holds a
  ∧ witDepthC.holds a
  ∧ segSlackC.holds a ∧ inRange a SEG_SLACK
  ∧ anchSlackC.holds a ∧ inRange a ANCH_SLACK
  ∧ depthSlackC.holds a ∧ inRange a DEPTH_SLACK
  ∧ linkC.holds a ∧ openingWitnessedC.holds a ∧ canonC.holds a

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

/-- ⚑⚑ **`bindAccepts a` — THE RECURSION SEAM'S ROW-LOCAL CONTENT**, exactly as
`DescriptorIR2.ProofBind.holdsAt` denotes the nine emitted `proofBind` constraints: the guard is a
bit, and under it every attested program lane equals the descriptor's pinned fingerprint lane.

⚠ What this is NOT: evidence that a sub-proof exists or verifies. No row-local polynomial of any
shape can see that — it is `Satisfied2Custom.proofBound`'s existential, off-row by construction, and
the consumer's obligation (`turn/src/executor/mina_head_verifier.rs`, which VERIFIES a STARK over
`dregg-pasta-fq-chainlink::v1` and refuses without one). What this IS: the row's claim about that
sub-proof made CHECKABLE — the program is not the prover's to choose, and the commitment is public. -/
def bindAccepts (a : Assignment) : Prop :=
  (a WRAP_FS_PROVED * (a WRAP_FS_PROVED - 1) = 0)
    ∧ ∀ i ∈ List.range STATE_LIMBS,
        a WRAP_FS_PROVED * (a (SUB_VK i) - chainlinkVkLane i) = 0

instance decBindAccepts (a : Assignment) : Decidable (bindAccepts a) := by
  unfold bindAccepts; infer_instance

/-- ⚑⚑⚑ **`linkBindAccepts a` — THE SEGMENT SEAM'S ROW-LOCAL CONTENT**, exactly as
`DescriptorIR2.ProofBind.holdsAt` denotes the emitted §2c constraint: the guard is a bit, and under
it every attested segment-program lane equals the descriptor's pinned fingerprint lane.

⚠ Read what is and is not here, because the ASYMMETRY is the whole point of this seam. The
`commit` half — that the sub-proof's public-input commitment is this row's nine `TIP_STATE` lanes —
is **not a row-local congruence at all** and cannot be: `bound` is `none`, so `holdsAt`'s third
conjunct is `True`. The commitment's content lives in `Satisfied2Custom.proofBound`'s existential,
off-row by construction, discharged by the consumer that VERIFIES a STARK over
`dregg-mina-lightclient-link::v1` and compares its published tip block.

⚑ What the row-local half nevertheless BUYS, and it is exactly what this campaign was for: the nine
`TIP_STATE` columns are now NAMED BY A CONSTRAINT alongside the guard and nine pinned literals. They
were, until today, columns that appeared in one arity-1 range lookup each and in no relation with
anything (`LightClientAnchorConnectivity.minaVerify_state_lanes_are_read_but_never_joined`, now
retired). -/
def linkBindAccepts (a : Assignment) : Prop :=
  (a LINK_OK * (a LINK_OK - 1) = 0)
    ∧ ∀ i ∈ List.range STATE_LIMBS,
        a LINK_OK * (a (LINK_VK i) - linkVkLane i) = 0

instance decLinkBindAccepts (a : Assignment) : Decidable (linkBindAccepts a) := by
  unfold linkBindAccepts; infer_instance

/-- ⚑⚑⚑ **`conjBindAccepts a` — THE FINALIZE SEAM'S ROW-LOCAL CONTENT**, exactly as
`DescriptorIR2.ProofBind.holdsAt` denotes the emitted §2d constraint: the guard is a bit, and under
it every attested conjunction-program lane equals the descriptor's pinned fingerprint lane.

⚠ The SAME asymmetry the segment seam has, and it is worth reading twice at this seam because the
name is the most inviting one in the file. The `commit` half — that the sub-proof's public-input
commitment is this row's nine `CONJ_PI` lanes — is **not a row-local congruence at all** and cannot
be: `bound` is `none`, so `holdsAt`'s third conjunct is `True`. Its content lives in
`Satisfied2Custom.proofBound`'s existential, off-row by construction, discharged by a consumer that
VERIFIES a STARK over `dregg-mina-wrap-conjunction::v1` and compares its 160 declared public inputs.

⚠ And even discharged in full it is TWO of finalize's FOUR conjuncts at a ξ this descriptor does not
weld to anything (§2d). -/
def conjBindAccepts (a : Assignment) : Prop :=
  (a FINALIZE_XI_B_PROVED * (a FINALIZE_XI_B_PROVED - 1) = 0)
    ∧ ∀ i ∈ List.range STATE_LIMBS,
        a FINALIZE_XI_B_PROVED * (a (CONJ_VK i) - conjVkLane i) = 0

instance decConjBindAccepts (a : Assignment) : Decidable (conjBindAccepts a) := by
  unfold conjBindAccepts; infer_instance

/-- **`airAccepts a`** — the emitted logic accepts row `a`: the verify arithmetic, the derived
canonicality of the anchor and tip state hashes, ⚑ the recursion seam's nine program-lane
congruences, ⚑⚑ the SEGMENT seam's nine, AND ⚑⚑⚑ the FINALIZE seam's nine. -/
def airAccepts (a : Assignment) : Prop :=
  verifyAccepts a ∧ canonAccepts a ∧ bindAccepts a ∧ linkBindAccepts a ∧ conjBindAccepts a

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
  ⟨(mina_lane_canon_forces_canonical rfl h.2.1.1).2,
   (mina_lane_canon_forces_canonical rfl h.2.1.2).2⟩

/-! ## §5b — ⚑⚑ THE RECURSION CARRIER'S CONTENT, FROM THE TRACE.

Not a refinement over a witness relation: these read the emitted `proofBind` congruences and
conclude a fact about the columns. -/

/-- ⚑⚑ **AN ACCEPTED ROW ATTESTS THE PINNED PROGRAM, LANE BY LANE.** The gate `WRAP_FS_PROVED = 1`
turns each seam's `guard·(vk − vkPin) = 0` into an EQUALITY, so all nine `SUB_VK` columns are the
`Faithful9` lanes of `dregg-pasta-fq-chainlink::v1`'s semantic fingerprint. A row that names any other
program — including one differing in a single lane — has no satisfying assignment.

⚠ Read the scope: this says the row's DECLARED program is that one. That a sub-proof of it exists and
verifies is off-row and is the consumer's check (`mina_head_verifier.rs`, fail-closed). -/
theorem mina_bind_attests_the_pinned_program {a : Assignment} (h : airAccepts a) :
    ∀ i ∈ List.range STATE_LIMBS, a (SUB_VK i) = chainlinkVkLane i := by
  intro i hi
  have hg : a WRAP_FS_PROVED = 1 := h.1.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hb := h.2.2.1.2 i hi
  rw [hg] at hb
  linarith

/-- ⚑⚑⚑ **AND AN ACCEPTED ROW ATTESTS THE SEGMENT PROGRAM, LANE BY LANE.** G6 (`LINK_OK = 1`) turns
each `guard·(vk − vkPin) = 0` into an EQUALITY, so all nine `LINK_VK` columns are the `Faithful9`
lanes of `dregg-mina-lightclient-link::v1`'s semantic fingerprint. A row that names any other
segment program — including one differing in a single lane — has no satisfying assignment.

⚠ Same scope note as the chainlink's twin: this says the row's DECLARED segment program is that one.
That a sub-proof of it exists, verifies, and publishes THESE nine tip lanes is off-row
(`Satisfied2Custom.proofBound`) and is `mina_head_verifier`'s REFUSALS 11-14. -/
theorem mina_link_bind_attests_the_pinned_program {a : Assignment} (h : airAccepts a) :
    ∀ i ∈ List.range STATE_LIMBS, a (LINK_VK i) = linkVkLane i := by
  intro i hi
  have hg : a LINK_OK = 1 := by
    have hlk := h.1.2.2.2.2.2.2.2.2.2.1
    rwa [linkC_holds_iff] at hlk
  have hb := h.2.2.2.1.2 i hi
  rw [hg] at hb
  linarith

/-- ⚑⚑⚑ **AND AN ACCEPTED ROW ATTESTS THE CONJUNCTION PROGRAM, LANE BY LANE.** G10
(`FINALIZE_XI_B_PROVED = 1`) turns each `guard·(vk − vkPin) = 0` into an EQUALITY, so all nine
`CONJ_VK` columns are the `Faithful9` lanes of `dregg-mina-wrap-conjunction::v1`'s semantic
fingerprint. A row that names any other program — including one differing in a single lane — has no
satisfying assignment.

⚠ Same scope note as its two siblings, plus the one that is specific to this seam: this says the
row's DECLARED conjunction program is that one. That a sub-proof of it exists and verifies is off-row
(`Satisfied2Custom.proofBound`); that its ξ is the block's own is neither in this AIR nor in that
sub-proof — it is `mina_wrap_finalize_fold.rs::fold_endo_into_finalize`'s 32 `cb.connect`s, a
CONSUMER check (§2d). -/
theorem mina_conj_bind_attests_the_pinned_program {a : Assignment} (h : airAccepts a) :
    ∀ i ∈ List.range STATE_LIMBS, a (CONJ_VK i) = conjVkLane i := by
  intro i hi
  have hg : a FINALIZE_XI_B_PROVED = 1 := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hb := h.2.2.2.2.2 i hi
  rw [hg] at hb
  linarith

/-- ⚑⚑ **AND THE FINALIZE SEAM'S GUARD CANNOT BE SWITCHED OFF.** A prover who would rather not name a
conjunction sub-proof cannot set `FINALIZE_XI_B_PROVED = 0` to make all nine congruences hold
vacuously — G10 forces it to `1`. Stated because a seam whose guard is free is a seam that is never
active, the quietest way a recursion declaration becomes decoration. -/
theorem mina_conj_guard_cannot_be_disarmed {a : Assignment} (h : airAccepts a) :
    a FINALIZE_XI_B_PROVED = 1 := h.1.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- ⚑ **AND THE SEGMENT SEAM'S GUARD CANNOT BE SWITCHED OFF EITHER.** A prover who would rather not
name a segment sub-proof cannot set `LINK_OK = 0` to make all nine congruences hold vacuously — G6
forces it to `1`. This is the conjunct that turns the former bare `= 1` into an obligation. -/
theorem mina_link_guard_cannot_be_disarmed {a : Assignment} (h : airAccepts a) :
    a LINK_OK = 1 := by
  have hlk := h.1.2.2.2.2.2.2.2.2.2.1
  rwa [linkC_holds_iff] at hlk

/-- ⚑ **AND THE ATTESTATION IS NOT VACUOUS: the guard cannot be switched off.** A prover who would
rather not name a sub-proof cannot set `WRAP_FS_PROVED = 0` — G9 forces it to `1`. Stated because a
seam whose guard is free is a seam that is never active, which is the quietest way a recursion
declaration becomes decoration. -/
theorem mina_bind_guard_cannot_be_disarmed {a : Assignment} (h : airAccepts a) :
    a WRAP_FS_PROVED = 1 := h.1.2.2.2.2.2.2.2.2.2.2.2.2.1

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
    (hpk : a PICKLES_OPENING_WITNESSED = (if picklesB then (1 : ℤ) else 0))
    (hcn : a CANON_OK = (if canonB then (1 : ℤ) else 0))
    (hacc : airAccepts a) :
    minaVerifyDecision segLen anchorH submitH (anchorH + segLen - submitH) reqDepth
      linkB picklesB canonB = true := by
  obtain ⟨hbl, hwd, hss, ⟨hss0, _⟩, has, ⟨has0, _⟩, hds, ⟨hds0, _⟩, ⟨hrd0c, _⟩,
    hlkC, hpkC, hcnC, -, -⟩ := hacc.1
  rw [blockLenC_holds_iff] at hbl
  rw [witDepthC_holds_iff] at hwd
  rw [segSlackC_holds_iff] at hss
  rw [anchSlackC_holds_iff] at has
  rw [depthSlackC_holds_iff] at hds
  rw [linkC_holds_iff] at hlkC
  rw [openingWitnessedC_holds_iff] at hpkC
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
    (hpk : a PICKLES_OPENING_WITNESSED = (if picklesOk L u then (1 : ℤ) else 0))
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
    (hpk : a PICKLES_OPENING_WITNESSED = (if picklesB then (1 : ℤ) else 0))
    (hcn : a CANON_OK = (if canonB then (1 : ℤ) else 0))
    (hfit : anchorH + segLen < 2 ^ MINA_RANGE_BITS)
    (hsub : reqDepth + submitH ≤ anchorH + segLen)
    (hcanon : canonAccepts a)
    -- ⚑ THE NEW COMPLETENESS COST, NAMED: an honest prover must ALSO hold a verifying STARK over
    -- `dregg-pasta-fq-chainlink::v1` and fill the nine `SUB_VK` lanes with its fingerprint. That is
    -- a real obligation on the witness generator and it is stated as a hypothesis rather than
    -- quietly assumed — `mina_wrap_fs_row_is_fillable` exhibits it discharged on the honest row.
    (hwf : a WRAP_FS_PROVED = 1)
    (hvk : ∀ i ∈ List.range STATE_LIMBS, a (SUB_VK i) = chainlinkVkLane i)
    -- ⚑⚑ THE SEGMENT SEAM'S COMPLETENESS COST, NAMED (2026-08-05, §2c): an honest prover must ALSO
    -- hold a verifying STARK over `dregg-mina-lightclient-link::v1` whose published tip block is
    -- this row's `TIP_STATE`, and fill the nine `LINK_VK` lanes with that program's fingerprint.
    -- `hlk` (below, via `linkB = true`) already forces the guard; this is the lane obligation, and
    -- `mina_link_row_is_fillable` exhibits it discharged on the honest row.
    (hlvk : ∀ i ∈ List.range STATE_LIMBS, a (LINK_VK i) = linkVkLane i)
    -- ⚑⚑⚑ THE FINALIZE SEAM'S COMPLETENESS COST, NAMED (2026-08-06, §2d): an honest prover must ALSO
    -- hold a verifying STARK over `dregg-mina-wrap-conjunction::v1`, fill the nine `CONJ_VK` lanes
    -- with that program's fingerprint, and publish that sub-proof's commitment in `CONJ_PI`. This is
    -- the most expensive of the three — the conjunction leaf is 2 536 columns × 16 rows — and it is
    -- stated as a hypothesis rather than quietly assumed. `mina_conj_row_is_fillable` exhibits it
    -- discharged on the honest row.
    (hcf : a FINALIZE_XI_B_PROVED = 1)
    (hcvk : ∀ i ∈ List.range STATE_LIMBS, a (CONJ_VK i) = conjVkLane i)
    (hdecT : minaVerifyDecision segLen anchorH submitH (anchorH + segLen - submitH) reqDepth
      linkB picklesB canonB = true) :
    airAccepts a := by
  have hbind : bindAccepts a := by
    refine ⟨by rw [hwf]; ring, ?_⟩
    intro i hi
    rw [hwf, hvk i hi]; ring
  have hlink1 : a LINK_OK = 1 := by
    have h1 : linkB = true := by
      unfold minaVerifyDecision at hdecT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hdecT
      exact hdecT.1.1.2
    rw [hlk, h1]; norm_num
  have hlbind : linkBindAccepts a := by
    refine ⟨by rw [hlink1]; ring, ?_⟩
    intro i hi
    rw [hlink1, hlvk i hi]; ring
  have hcbind : conjBindAccepts a := by
    refine ⟨by rw [hcf]; ring, ?_⟩
    intro i hi
    rw [hcf, hcvk i hi]; ring
  refine ⟨?_, hcanon, hbind, hlbind, hcbind⟩
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
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
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
  -- ⚑ THE NEW TOOTH's completeness half: the required depth is a `Nat` on the wire, so it is
  -- non-negative for free, and it fits the declared interval because it is at most the derived
  -- witnessed depth, which `hfit` bounds.
  · rw [hrd]; exact hrd0
  · rw [hrd]; linarith
  · rw [linkC_holds_iff, hlk, hlk1]; norm_num
  · rw [openingWitnessedC_holds_iff, hpk, hpk1]; norm_num
  · rw [canonC_holds_iff, hcn, hcn1]; norm_num
  · rw [wrapFsC_holds_iff, hwf]
  · rw [finalizeXiBC_holds_iff, hcf]

/-! ## §6b — ⚑⚑ `SUBMIT_H ≤ BLOCK_LEN`, FROM THE TRACE. The relation the AIR did not force.

Every theorem in §6 is a refinement, taking a witness relation that names which column carries which
projection. These take none: they read the emitted gates and the emitted lookups and conclude a fact
about the columns.

⚠ **WHY IT WAS OPEN, precisely.** `SEG_SLACK` and `ANCH_SLACK` and `DEPTH_SLACK` were each ranged
independently and never compared, and `REQ_DEPTH` carried **NO RANGE LOOKUP AT ALL** — it was
PI-pinned (`PI[19]`) and otherwise a free witness. G5 (`DEPTH_SLACK + REQ_DEPTH = WIT_DEPTH`) then
bought nothing about the SIGN of `WIT_DEPTH`: a sufficiently negative `REQ_DEPTH` is met by a
non-negative `DEPTH_SLACK` at a negative witnessed depth, and G2 turns that into a settlement
submitted ABOVE the verified tip. It was catchable only by a verifier that read `PI[19]` and compared
it to 290 by hand — a convention, not a gate. One lookup on the already-declared table closes it. -/

/-- ⚑⚑ **THE WITNESSED DEPTH IS NON-NEGATIVE, FROM THE TRACE.** `0 ≤ DEPTH_SLACK` (its own tooth) and
`0 ≤ REQ_DEPTH` (the tooth added 2026-08-03) with G5 give it. Before the second lookup, only the
first held and this was FALSE — see `mina_negative_req_depth_old_admits_new_rejects`. -/
theorem minaLcAir_forces_nonneg_witnessed_depth (a : Assignment) (hacc : airAccepts a) :
    0 ≤ a WIT_DEPTH := by
  obtain ⟨-, -, -, -, -, -, hds, ⟨hds0, -⟩, ⟨hrd0, -⟩, -, -, -, -, -⟩ := hacc.1
  rw [depthSlackC_holds_iff] at hds
  linarith

/-- ⚑⚑ **AND THEREFORE `SUBMIT_H ≤ BLOCK_LEN`** — the settlement being finalized was submitted at or
below the height this proof verifies, which is the Mina instance of the class the three peer-chain
tallies belong to (`signed ≤ total`) and the ETH client's `PC ≤ BL`.

G2 (`WIT_DEPTH + SUBMIT_H = BLOCK_LEN`) plus a non-negative witnessed depth. No hypothesis about the
update at all. -/
theorem minaLcAir_forces_submit_within_the_segment (a : Assignment) (hacc : airAccepts a) :
    a SUBMIT_H ≤ a BLOCK_LEN := by
  have hd := minaLcAir_forces_nonneg_witnessed_depth a hacc
  obtain ⟨-, hwd, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hacc.1
  rw [witDepthC_holds_iff] at hwd
  linarith

/-- ⚑ **AND `minaLinkAir` DOES NOT ALREADY COVER THIS — checked at source, not assumed.**

`LightClientMinaLinkAir.link_seg_len_counts_the_real_rows` says the LINK descriptor's `SEG_LEN`
column equals the number of exhibited block rows: it closes the count relation for the multi-row
companion, over `SEG_LEN` and the row list. It says nothing about `SUBMIT_H`, `REQ_DEPTH` or
`BLOCK_LEN`, which are columns of THIS descriptor and are not in the link AIR at all. The two
statements are about different objects; the overlap is zero.

Stated here as the two columns' membership rather than as prose, so the disjointness is checkable. -/
theorem mina_submit_relation_is_not_the_link_count :
    SUBMIT_H < MINA_LC_WIDTH ∧ REQ_DEPTH < MINA_LC_WIDTH ∧ BLOCK_LEN < MINA_LC_WIDTH
      ∧ SUBMIT_H ≠ REQ_DEPTH ∧ REQ_DEPTH ≠ BLOCK_LEN := by decide

/-! ## §7 — ⚑ THE REFUSING WITNESSES. Both polarities, exhibited, not asserted.

Each row is a CONCRETE assignment and each refusal is a proof that `airAccepts` FAILS on it. A refusal
nothing witnesses is decoration; these are the four shapes this campaign actually names — a shallower
losing fork, a bent proof word, a forged `blockchain_length`, and the deployed observer's own
unanchored subtraction. -/

/-- A row from its column values, index-ordered from `SEG_LEN`. A list shorter than the trace width
reads `0` above its end — the four LOGIC refusals below leave the lane columns at `0` (which is a
canonical `Fp` element, so they are refused by the logic and not incidentally by the lane gates). -/
def rowOf (vs : List ℤ) : Assignment := fun w => vs.getD w 0

/-! ## §6c — ⚑ THE FALSIFIER, BOTH POLARITIES, ON ONE ROW.

A repair that only shows the new tooth refusing a value has not shown the value was ever admitted.
This row differs from an honest one in exactly the columns a forger controls. -/

/-- ⚑ **THE ROW THAT PROVED BEFORE THE `REQ_DEPTH` LOOKUP.** Anchor at 1000, a five-block segment, so
the DERIVED tip is 1005 — and the settlement claims to have been submitted at **2000**, five hundred
blocks ABOVE the verified tip. `WIT_DEPTH = 1005 − 2000 = −995`; the forger publishes
`REQ_DEPTH = −1000`, and G5's slack comes out `−995 − (−1000) = 5`, comfortably inside `[0, 2^24)`.

G1, G2, G3, G4, G5 ALL HOLD. Every carrier is `1`. Every slack that HAD a lookup is non-negative. -/
def negativeReqDepthRow : Assignment :=
  rowOf [5, 1000, 2000, -995, -1000, 4, 1000, 5, 1, 1, 1, 1005]

/-- ⚑ **BEFORE: the pre-2026-08-03 predicate ACCEPTS it.** Not "would have accepted" — the predicate
is defined (`verifyAcceptsWithoutDepthPolicyRange`) and this is a proof over it. -/
theorem mina_negative_req_depth_was_admitted :
    verifyAcceptsWithoutDepthPolicyRange negativeReqDepthRow := by
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp only [negativeReqDepthRow, rowOf, blockLenC, witDepthC, segSlackC, anchSlackC,
      depthSlackC, linkC, openingWitnessedC, canonC, Dregg2.Circuit.Constraint.holds, Expr.eval,
      SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK, DEPTH_SLACK,
      LINK_OK, PICKLES_OPENING_WITNESSED, CANON_OK, BLOCK_LEN, MINA_RANGE_BITS, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;> norm_num

/-- ⚑⚑ **AFTER: the served descriptor REFUSES it**, on the `REQ_DEPTH` tooth — `−1000 ∉ [0, 2^24)`.
The pair is the claim: one row, admitted then refused, differing only in whether the lookup exists. -/
theorem mina_negative_req_depth_is_refused : ¬ airAccepts negativeReqDepthRow := by
  intro h
  have hrd0 := h.1.2.2.2.2.2.2.2.2.1.1
  simp only [negativeReqDepthRow, rowOf, REQ_DEPTH] at hrd0
  norm_num at hrd0

/-- …and on the SAME row the relation the tooth exists to force is visibly violated:
`SUBMIT_H = 2000 > 1005 = BLOCK_LEN`. So the refusal is of the thing it is named for and not of some
incidental other defect. -/
theorem mina_negative_req_depth_row_submits_above_the_tip :
    negativeReqDepthRow BLOCK_LEN < negativeReqDepthRow SUBMIT_H := by
  simp only [negativeReqDepthRow, rowOf, BLOCK_LEN, SUBMIT_H]
  norm_num

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

/-- ⚑ **THE SUB-PROOF COMMITMENT THE HONEST ROW PUBLISHES** — the nine `Faithful9` lanes of the
digest of `dregg-pasta-fq-chainlink::v1`'s **256 public inputs on the block-539508 instance's 46th
and last link** (`circuit/tests/fixtures/pasta-fq-chainlink-pis.txt`, line 46): blake3, derive-key
context `dregg.mina-lightclient.chainlink-subproof-pi-commitment.v1`, the arity absorbed first and
then each public input as its canonical `u32` little-endian.

⚑ The CONTEXT string moved with the descriptor (`wraplink-` → `chainlink-`). The arity already goes
in first, so a 224-PI commitment was never a prefix of a 256-PI one; the rename is the other half —
a commitment minted for the seven-block program cannot be re-read as one for the eight-block program
even at equal arity. There is no accepted second form.

⚠ These nine numbers are NOT constrained by any gate of this descriptor — they are PI-BOUND, which is
the whole point: the consumer recomputes them from the sub-proof's own declared public inputs and
refuses on a mismatch. They appear here so the honest row is a COMPLETE row and the emitted PI vector
in `circuit/tests/mina_transcript_carrier_binding.rs` has something to be checked against.
The Rust gate recomputes both this digest and the fingerprint above from the sibling descriptor's
bytes; a drift in either is a RED. -/
def CHAINLINK_PI_LANES : List ℤ :=
  [76470648, 44150818, 361910605, 443692671, 242143308, 490185822, 240590146, 360276303, 4019771]

/-- The nineteen columns the recursion carrier adds to a row: the guard, the nine pinned program
lanes, and the nine published commitment lanes. -/
def wrapBindCols : List ℤ := [1] ++ CHAINLINK_VK_LANES ++ CHAINLINK_PI_LANES

/-- ⚠⚠ **THE CONJUNCTION SUB-PROOF'S COMMITMENT LANES ON THE HONEST ROW — AND THESE ARE A ROW
FIXTURE, NOT A MEASURED DIGEST. SAY IT FIRST, BECAUSE `CHAINLINK_PI_LANES` DIRECTLY ABOVE *IS* ONE.**

`CHAINLINK_PI_LANES` is blake3 over a real fixture (`pasta-fq-chainlink-pis.txt` line 46) under a
named derive-key context that `circuit/tests/mina_transcript_carrier_binding.rs` recomputes. The
conjunction seam has the FIXTURE (`circuit/tests/fixtures/mina-wrap-conjunction-pis.txt`, the 160
PIs of the block-539508 instance) and **neither a context string nor a consumer** — the Rust half of
§2d (a `check_conj_program_pin` and a commitment recomputation in
`turn/src/executor/mina_head_verifier.rs`) is UNDONE WORK, named in this file's flag-day section as
undone. Minting a digest-shaped literal here under a context string no code implements, and letting
it read as a measurement, is exactly the sin `minted-identity-carrier-vacuity` is about. So these are
ZEROS and are labelled as such, and the day the context lands they become a measurement.

⚠ Nothing in this descriptor gates them — `CONJ_PI` is PI-BOUND and §2d's `bound` is `none` — so
every acceptance and refusal theorem below is INDEPENDENT of their value. That is why a placeholder
is admissible here and would not be admissible in `CONJ_VK_LANES`, which is pinned by the emitted
bytes and is measured (`mina_conj_program_pin_is_nine_lanes` refuses a zero lane 0). -/
def CONJ_PI_LANES : List ℤ := [0, 0, 0, 0, 0, 0, 0, 0, 0]

/-- The nineteen columns the FINALIZE carrier adds to a row: the guard, the nine pinned program
lanes, and the nine published commitment lanes. Same shape as `wrapBindCols`. -/
def conjBindCols : List ℤ := [1] ++ CONJ_VK_LANES ++ CONJ_PI_LANES

/-- **THE HONEST ROW** — the logic columns above, the pinned anchor's nine lanes, the verified tip's
nine lanes, ⚑ the recursion carrier's nineteen, ⚑⚑ the segment seam's nine program lanes, ⚑⚑⚑ and the
FINALIZE seam's nineteen (2026-08-06). ACCEPTED.

⚑ Note what the segment seam did NOT add and the finalize seam DID: the segment seam's commitment is
`TIP_STATE`, already in this row and already published, which is why it cost `MINA_PI_COUNT` nothing.
The finalize seam commits to a DIFFERENT object — the conjunction sub-proof's 160 public inputs — so
it brings its own nine-lane commitment block and nine new PI slots (30..38). -/
def honestRow : Assignment :=
  rowOf (honestLogicCols ++ GENESIS_ANCHOR_LANES ++ DEVNET_TIP_LANES ++ wrapBindCols
          ++ LINK_VK_LANES ++ conjBindCols)

/-- ⚑ **THE SHIFTED-ANCHOR ROW** — byte-for-byte the honest row except that the pinned anchor's lanes
are the `+p` alias. Every gate holds, every slack is in range, and every carrier bit reads `1`. -/
def shiftedAnchorRow : Assignment :=
  rowOf (honestLogicCols ++ SHIFTED_ANCHOR_LANES ++ DEVNET_TIP_LANES ++ wrapBindCols
          ++ LINK_VK_LANES ++ conjBindCols)

/-- The row's logic columns, unfolded — shared by every §7 proof so the `List.getD` walk happens
once per column rather than once per theorem. -/
private theorem honest_verify_cols :
    verifyAccepts honestRow ∧ verifyAccepts shiftedAnchorRow := by
  constructor <;>
  · refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
        depthSlackC_holds_iff, linkC_holds_iff, openingWitnessedC_holds_iff, canonC_holds_iff,
        wrapFsC_holds_iff, finalizeXiBC_holds_iff,
        honestRow, shiftedAnchorRow, honestLogicCols, GENESIS_ANCHOR_LANES, SHIFTED_ANCHOR_LANES,
        DEVNET_TIP_LANES, wrapBindCols, CHAINLINK_VK_LANES, CHAINLINK_PI_LANES,
        LINK_VK_LANES, conjBindCols, CONJ_VK_LANES, CONJ_PI_LANES, rowOf,
        SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
        DEPTH_SLACK, LINK_OK, PICKLES_OPENING_WITNESSED, CANON_OK, WRAP_FS_PROVED,
        FINALIZE_XI_B_PROVED, BLOCK_LEN,
        MINA_RANGE_BITS, List.getD,
        List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
      norm_num

/-- ⚑ **THE HONEST ROW IS ACCEPTED — on real devnet lanes.** The verify arithmetic AND the eighteen
canonicality lookups. Without this the rung would be satisfied by a descriptor that refuses
everything, and the two real state hashes are exactly the values the gate must not refuse. -/
theorem honest_row_accepted : airAccepts honestRow :=
  ⟨honest_verify_cols.1, by decide, by decide, by decide, by decide⟩

/-- ⚑⚑ **THE COMPLETENESS COST OF THE RECURSION CARRIER IS PAYABLE — exhibited, not assumed.**
`minaLcAir_complete` now takes `hwf`/`hvk` as hypotheses; a rung whose completeness hypotheses no
honest row discharges is a rung that refuses everything. This is them, discharged, on the row that
carries the real devnet lanes. -/
theorem mina_wrap_fs_row_is_fillable :
    honestRow WRAP_FS_PROVED = 1
      ∧ ∀ i ∈ List.range STATE_LIMBS, honestRow (SUB_VK i) = chainlinkVkLane i := by
  refine ⟨by decide, ?_⟩
  decide

/-- ⚑⚑ **AND THE SEGMENT SEAM'S COMPLETENESS COST IS PAYABLE TOO — exhibited, not assumed.**
`minaLcAir_complete`'s new `hlvk` hypothesis, discharged on the row that carries the real devnet
lanes. A seam whose completeness hypothesis no honest row discharges is a seam that refuses
everything, which is the cheapest way to look sound. -/
theorem mina_link_row_is_fillable :
    honestRow LINK_OK = 1
      ∧ ∀ i ∈ List.range STATE_LIMBS, honestRow (LINK_VK i) = linkVkLane i := by
  refine ⟨by decide, ?_⟩
  decide

/-- ⚑⚑⚑ **AND THE FINALIZE SEAM'S COMPLETENESS COST IS PAYABLE — exhibited, not assumed.**
`minaLcAir_complete`'s new `hcf`/`hcvk` hypotheses (2026-08-06), discharged on the row that carries
the real devnet lanes. ⚠ What this exhibits is that the ROW is fillable; the OBLIGATION it stands
for — holding a verifying STARK over a 2 536-column, 16-row conjunction AIR — is a prover cost this
theorem does not pay and does not pretend to. -/
theorem mina_conj_row_is_fillable :
    honestRow FINALIZE_XI_B_PROVED = 1
      ∧ ∀ i ∈ List.range STATE_LIMBS, honestRow (CONJ_VK i) = conjVkLane i := by
  refine ⟨by decide, ?_⟩
  decide

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
produces. The `PICKLES_OPENING_WITNESSED = 1` gate refuses it. -/
def bentProofRow : Assignment := rowOf [300, 1000, 1010, 290, 290, 299, 10, 0, 1, 0, 1, 1300]

theorem bent_proof_word_refused : ¬ airAccepts bentProofRow := by
  intro h
  -- ⚠ ONE `.2` DEEPER than before 2026-08-03: `inRange REQ_DEPTH` sits between the depth tooth
  -- and the three carriers in `verifyAccepts`.
  have hpk := h.1.2.2.2.2.2.2.2.2.2.2.1
  rw [openingWitnessedC_holds_iff] at hpk
  simp only [bentProofRow, rowOf, PICKLES_OPENING_WITNESSED, List.getD, List.getElem?_cons_zero,
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
  have htop := h.2.1.1.2.2
  revert htop
  decide

/-! ### ⚑⚑ THE RECURSION CARRIER'S OWN FALSIFIER — a row that names the WRONG PROGRAM.

A refusal that only shows the new tooth refusing has not shown the value was ever admitted. This row
differs from the honest one in **one lane of one number**: `SUB_VK 0` is the chainlink fingerprint's
lane 0 PLUS ONE. Every gate of the verify logic holds, every slack is in range, both state hashes are
canonical, and all five carriers read `1` — the row is honest in every column the descriptor carried
before 2026-08-05. -/

/-- The forged program lanes: the real fingerprint with lane 0 bumped by one. -/
def FORGED_VK_LANES : List ℤ :=
  [40589530, 494773874, 527776693, 373808410, 118028044, 372824034, 512521559, 25478361, 4577485]

/-- ⚑ **THE ROW THAT NAMES A DIFFERENT PROGRAM.** -/
def forgedProgramRow : Assignment :=
  rowOf (honestLogicCols ++ GENESIS_ANCHOR_LANES ++ DEVNET_TIP_LANES
          ++ ([1] ++ FORGED_VK_LANES ++ CHAINLINK_PI_LANES) ++ LINK_VK_LANES ++ conjBindCols)

/-- ⚑ **BEFORE: everything this descriptor checked before the bind ACCEPTS it.** The pre-bind
predicate is `verifyAccepts ∧ canonAccepts` — literally `airAccepts` minus the seam — and it is
satisfied. So the forged program lane was, in the strict sense, admitted. -/
theorem forged_program_was_admitted :
    verifyAccepts forgedProgramRow ∧ canonAccepts forgedProgramRow := by
  refine ⟨?_, by decide⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
      depthSlackC_holds_iff, linkC_holds_iff, openingWitnessedC_holds_iff, canonC_holds_iff,
      wrapFsC_holds_iff, finalizeXiBC_holds_iff,
      forgedProgramRow, honestLogicCols, GENESIS_ANCHOR_LANES, DEVNET_TIP_LANES,
      FORGED_VK_LANES, CHAINLINK_PI_LANES, LINK_VK_LANES, conjBindCols, CONJ_VK_LANES,
      CONJ_PI_LANES, rowOf,
      SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
      DEPTH_SLACK, LINK_OK, PICKLES_OPENING_WITNESSED, CANON_OK, WRAP_FS_PROVED,
      FINALIZE_XI_B_PROVED, BLOCK_LEN,
      MINA_RANGE_BITS, List.getD,
      List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
    norm_num

/-- ⚑⚑ **AFTER: the emitted descriptor REFUSES it**, on the lane-0 `proofBind` congruence and nothing
else. One lane of the program identity is enough — which is the point of pinning nine of them. -/
theorem forged_program_refused : ¬ airAccepts forgedProgramRow := by
  intro h
  have hb := h.2.2.1.2 0 (by decide)
  revert hb
  decide

/-- ⚑⚑⚑ **OLD ADMITS, NEW REJECTS — the recursion rung stated as one theorem.** The row every
pre-2026-08-05 conjunct accepts is refused by the seam. This is the carrier stopping being a bit. -/
theorem forged_program_old_admits_new_rejects :
    (verifyAccepts forgedProgramRow ∧ canonAccepts forgedProgramRow)
      ∧ ¬ airAccepts forgedProgramRow :=
  ⟨forged_program_was_admitted, forged_program_refused⟩

/-! ### ⚑⚑⚑ THE SEGMENT SEAM'S OWN FALSIFIER — a row that names the WRONG SEGMENT PROGRAM.

The same discipline the chainlink seam's falsifier follows, at the leg that landed today. This row
differs from the honest one in **one lane of one number**: `LINK_VK 0` is the link descriptor's
fingerprint lane 0 PLUS ONE. Every gate of the verify logic holds, every slack is in range, both
state hashes are canonical, all four pre-existing carriers read `1`, and the CHAINLINK seam is
satisfied in full — the row is honest in every column the descriptor carried this morning.

⚠ **AND THE TAMPER TARGET IS CHECKED, NOT ASSUMED.** A drafted falsifier on the phase-1 lane was
refuted by `decide` for moving a zero into a zero; `the_forged_link_lane_moves_a_real_value` states
that lane 0 is non-zero and that the forgery actually moves it, so a lane that silently became `0`
could not keep this pair green. -/

/-- The forged segment-program lanes: the real fingerprint with lane 0 bumped by one.

⚑⚑ **RE-DERIVED 2026-08-06, AND SAY WHY, BECAUSE THE DEFECT IS THE ONE THIS FILE ALREADY NAMES.**
`LINK_VK_LANES` moved (the link descriptor was re-emitted) and this vector did NOT follow — it stayed
the `+1` of the PREVIOUS fingerprint, `[76100771, …]`. The pair still went green: the stale vector
differs from the honest one in all nine lanes, so `forged_link_program_refused` still refused and
every conjunct of `the_forged_link_lane_moves_a_real_value` still held. **What died was the CLAIM, not
the gate** — "differs in one lane of one number" became "differs in nine", and a one-lane forgery, the
thing the seam is supposed to refuse, was no longer being exhibited at all. That is
`minted-a-falsifier-that-stopped-falsifying` with the polarity flipped: the adversary got WEAKER while
every assertion stayed true.

So the "one lane" claim is now a THEOREM (`the_forged_link_lane_moves_a_real_value`'s last two
conjuncts), not a sentence in this docstring. A future re-emit that moves `LINK_VK_LANES` and leaves
this vector behind goes RED. -/
def FORGED_LINK_VK_LANES : List ℤ :=
  -- ⚑ FOLLOWS `LINK_VK_LANES`, 2026-08-08: lane 0 + 1, tail identical. The 08-06 note above is
  -- exactly this maintenance, and `the_forged_link_lane_moves_a_real_value` went RED when the
  -- literal moved and this one did not — the falsifier caught its own staleness.
  [485689087, 477622751, 46091945, 410308945, 235143973, 391260395, 78649260, 413048609, 30212]

/-- ⚑ **THE ROW THAT NAMES A DIFFERENT SEGMENT PROGRAM.** -/
def forgedLinkProgramRow : Assignment :=
  rowOf (honestLogicCols ++ GENESIS_ANCHOR_LANES ++ DEVNET_TIP_LANES ++ wrapBindCols
          ++ FORGED_LINK_VK_LANES ++ conjBindCols)

/-- ⚑ **THE FORGERY MOVES A REAL VALUE — AND MOVES EXACTLY ONE LANE OF IT.** Lane 0 is non-zero, the
forged lane differs from it, and the two lane vectors differ — so this pair cannot go green by moving
nothing.

⚑⚑ **THE LAST TWO CONJUNCTS ARE NEW ON 2026-08-06 AND THEY ARE THE POINT.** `FORGED_LINK_VK_LANES`
had gone stale against a re-emitted `LINK_VK_LANES` and the three conjuncts above did NOT notice: a
vector differing in all nine lanes satisfies every one of them. Pinning `lane 0 = honest + 1` and
`tail = honest tail` is what makes this a ONE-LANE forgery as a fact rather than as a docstring — and
it is the whole content of "one lane of the program identity is enough". -/
theorem the_forged_link_lane_moves_a_real_value :
    linkVkLane 0 ≠ 0
      ∧ forgedLinkProgramRow (LINK_VK 0) ≠ honestRow (LINK_VK 0)
      ∧ FORGED_LINK_VK_LANES ≠ LINK_VK_LANES
      ∧ FORGED_LINK_VK_LANES.getD 0 0 = LINK_VK_LANES.getD 0 0 + 1
      ∧ FORGED_LINK_VK_LANES.tail = LINK_VK_LANES.tail := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **BEFORE: everything this descriptor checked before the segment seam ACCEPTS it.** The
pre-seam predicate is `verifyAccepts ∧ canonAccepts ∧ bindAccepts` — literally `airAccepts` minus
`linkBindAccepts` — and it is satisfied. So the forged segment-program lane was, in the strict sense,
admitted. -/
theorem forged_link_program_was_admitted :
    verifyAccepts forgedLinkProgramRow ∧ canonAccepts forgedLinkProgramRow
      ∧ bindAccepts forgedLinkProgramRow := by
  refine ⟨?_, by decide, by decide⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
      depthSlackC_holds_iff, linkC_holds_iff, openingWitnessedC_holds_iff, canonC_holds_iff,
      wrapFsC_holds_iff, finalizeXiBC_holds_iff,
      forgedLinkProgramRow, honestLogicCols, GENESIS_ANCHOR_LANES, DEVNET_TIP_LANES,
      wrapBindCols, CHAINLINK_VK_LANES, CHAINLINK_PI_LANES, FORGED_LINK_VK_LANES,
      conjBindCols, CONJ_VK_LANES, CONJ_PI_LANES, rowOf,
      SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
      DEPTH_SLACK, LINK_OK, PICKLES_OPENING_WITNESSED, CANON_OK, WRAP_FS_PROVED,
      FINALIZE_XI_B_PROVED, BLOCK_LEN,
      MINA_RANGE_BITS, List.getD,
      List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
    norm_num

/-- ⚑⚑ **AFTER: the emitted descriptor REFUSES it**, on the segment seam's lane-0 congruence and
nothing else. One lane of the program identity is enough — which is the point of pinning nine. -/
theorem forged_link_program_refused : ¬ airAccepts forgedLinkProgramRow := by
  intro h
  have hb := h.2.2.2.1.2 0 (by decide)
  revert hb
  decide

/-- ⚑⚑⚑ **OLD ADMITS, NEW REJECTS — the segment rung stated as one theorem.** The row every
pre-§2c conjunct accepts is refused by the seam. This is `LINK_OK` stopping being a bare `= 1`. -/
theorem forged_link_program_old_admits_new_rejects :
    (verifyAccepts forgedLinkProgramRow ∧ canonAccepts forgedLinkProgramRow
        ∧ bindAccepts forgedLinkProgramRow)
      ∧ ¬ airAccepts forgedLinkProgramRow :=
  ⟨forged_link_program_was_admitted, forged_link_program_refused⟩

/-! ### ⚑⚑⚑ THE FINALIZE SEAM'S OWN FALSIFIER — a row that names the WRONG CONJUNCTION PROGRAM.

The same discipline the other two seams' falsifiers follow, at the leg that landed 2026-08-06. This
row differs from the honest one in **one lane of one number**: `CONJ_VK 0` is the conjunction
descriptor's fingerprint lane 0 PLUS ONE. Every gate of the verify logic holds, every slack is in
range, both state hashes are canonical, all five carriers read `1`, and the CHAINLINK and SEGMENT
seams are satisfied in full — the row is honest in every column the descriptor carried yesterday.

⚠ **AND THE TAMPER TARGET IS CHECKED, NOT ASSUMED**, for the reason
`the_forged_link_lane_moves_a_real_value` exists: a mutation that becomes a no-op leaves a gate that
can still go red while its ADVERSARY is dead (`minted-a-falsifier-that-stopped-falsifying`). Here it
does double duty — `CONJ_VK_LANES` is a MEASURED fingerprint, and a lane 0 of `0` would mean the
literal was never measured, so `the_forged_conj_lane_moves_a_real_value` is also the tripwire on a
placeholder. -/

/-- The forged conjunction-program lanes: the real fingerprint with lane 0 bumped by one. -/
def FORGED_CONJ_VK_LANES : List ℤ :=
  [447620829, 118399956, 332150941, 529607877, 314255522, 98355104, 173079149, 176046258, 561245]

/-- ⚑ **THE ROW THAT NAMES A DIFFERENT CONJUNCTION PROGRAM.** -/
def forgedConjProgramRow : Assignment :=
  rowOf (honestLogicCols ++ GENESIS_ANCHOR_LANES ++ DEVNET_TIP_LANES ++ wrapBindCols
          ++ LINK_VK_LANES ++ ([1] ++ FORGED_CONJ_VK_LANES ++ CONJ_PI_LANES))

/-- ⚑ **THE FORGERY MOVES A REAL VALUE — and the same statement refuses an UNMEASURED literal.**
Lane 0 is non-zero (so `CONJ_VK_LANES` is not the zero placeholder a lane leaves behind when it
drafts the seam before running the emitter), the forged lane differs from it, and the two lane
vectors differ. This pair cannot go green by moving nothing. -/
theorem the_forged_conj_lane_moves_a_real_value :
    conjVkLane 0 ≠ 0
      ∧ forgedConjProgramRow (CONJ_VK 0) ≠ honestRow (CONJ_VK 0)
      ∧ FORGED_CONJ_VK_LANES ≠ CONJ_VK_LANES
      -- ⚑⚑ …and the forgery is ONE LANE, as a fact. The segment seam's twin went stale against a
      -- re-emitted fingerprint on this very day and stayed green while its adversary weakened from a
      -- one-lane forgery to a nine-lane one; these two conjuncts are what refuse that here.
      ∧ FORGED_CONJ_VK_LANES.getD 0 0 = CONJ_VK_LANES.getD 0 0 + 1
      ∧ FORGED_CONJ_VK_LANES.tail = CONJ_VK_LANES.tail := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ⚑ **BEFORE: everything this descriptor checked before the finalize seam ACCEPTS it.** The
pre-seam predicate is `verifyAccepts ∧ canonAccepts ∧ bindAccepts ∧ linkBindAccepts` — literally
`airAccepts` minus `conjBindAccepts` — and it is satisfied. So the forged conjunction-program lane
was, in the strict sense, admitted. -/
theorem forged_conj_program_was_admitted :
    verifyAccepts forgedConjProgramRow ∧ canonAccepts forgedConjProgramRow
      ∧ bindAccepts forgedConjProgramRow ∧ linkBindAccepts forgedConjProgramRow := by
  refine ⟨?_, by decide, by decide, by decide⟩
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [blockLenC_holds_iff, witDepthC_holds_iff, segSlackC_holds_iff, anchSlackC_holds_iff,
      depthSlackC_holds_iff, linkC_holds_iff, openingWitnessedC_holds_iff, canonC_holds_iff,
      wrapFsC_holds_iff, finalizeXiBC_holds_iff,
      forgedConjProgramRow, honestLogicCols, GENESIS_ANCHOR_LANES, DEVNET_TIP_LANES,
      wrapBindCols, CHAINLINK_VK_LANES, CHAINLINK_PI_LANES, LINK_VK_LANES,
      FORGED_CONJ_VK_LANES, CONJ_PI_LANES, rowOf,
      SEG_LEN, ANCHOR_H, SUBMIT_H, WIT_DEPTH, REQ_DEPTH, SEG_SLACK, ANCH_SLACK,
      DEPTH_SLACK, LINK_OK, PICKLES_OPENING_WITNESSED, CANON_OK, WRAP_FS_PROVED,
      FINALIZE_XI_B_PROVED, BLOCK_LEN,
      MINA_RANGE_BITS, List.getD,
      List.cons_append, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some] <;>
    norm_num

/-- ⚑⚑ **AFTER: the emitted descriptor REFUSES it**, on the finalize seam's lane-0 congruence and
nothing else. One lane of the program identity is enough — which is the point of pinning nine. -/
theorem forged_conj_program_refused : ¬ airAccepts forgedConjProgramRow := by
  intro h
  have hb := h.2.2.2.2.2 0 (by decide)
  revert hb
  decide

/-- ⚑⚑⚑ **OLD ADMITS, NEW REJECTS — the finalize rung stated as one theorem.** The row every
pre-§2d conjunct accepts is refused by the seam. ⚠ Read what this pair is and is not: it shows the
SEAM bites, i.e. that a row cannot name a program other than `dregg-mina-wrap-conjunction::v1`. It
does NOT show that finalize is proved — that is two of four conjuncts, at a ξ this descriptor does
not weld (§2d). -/
theorem forged_conj_program_old_admits_new_rejects :
    (verifyAccepts forgedConjProgramRow ∧ canonAccepts forgedConjProgramRow
        ∧ bindAccepts forgedConjProgramRow ∧ linkBindAccepts forgedConjProgramRow)
      ∧ ¬ airAccepts forgedConjProgramRow :=
  ⟨forged_conj_program_was_admitted, forged_conj_program_refused⟩

/-- ⚑⚑⚑ **OLD ADMITS, NEW REJECTS — the rung stated as one theorem.** The very same row that the
PRE-RUNG predicate ACCEPTS (`verifyAccepts`: every gate, every slack, and `CANON_OK` witnessed `1` by
a prover who simply set it) is REFUSED by the emitted descriptor. Nothing about the row changed; the
carrier stopped being a bit somebody wrote down.

This is the object the whole `PICKLES_OPENING_WITNESSED`/`LINK_OK`/`CANON_OK` question is about, at the one carrier
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
anchored head on REAL devnet lanes and refuses all EIGHT forgery shapes. A descriptor that accepted
everything, or refused everything, fails this. -/
theorem mina_air_discriminates :
    airAccepts honestRow
      ∧ ¬ airAccepts losingForkRow
      ∧ ¬ airAccepts bentProofRow
      ∧ ¬ airAccepts forgedHeightRow
      ∧ ¬ airAccepts unanchoredRow
      ∧ ¬ airAccepts shiftedAnchorRow
      ∧ ¬ airAccepts forgedProgramRow
      ∧ ¬ airAccepts forgedLinkProgramRow
      ∧ ¬ airAccepts forgedConjProgramRow :=
  ⟨honest_row_accepted, losing_fork_refused, bent_proof_word_refused, forged_height_refused,
   observer_arithmetic_refused, shifted_anchor_refused, forged_program_refused,
   forged_link_program_refused, forged_conj_program_refused⟩

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
-- ⚑⚑ THE RECURSION RUNG, 2026-08-05: `PICKLES_OK` was a bit and is now two objects — a witnessed
-- residue named `PICKLES_OPENING_WITNESSED`, and `WRAP_FS_PROVED`, whose `= 1` forces nine `proofBind`
-- congruences against the pinned fingerprint of a sub-proof descriptor that EXISTS and PROVES.
#assert_axioms minaHeadAir_bind_shape
#assert_axioms minaLcVerifyDesc_proof_binds
#assert_axioms minaLcVerifyDesc_no_declarative_binds
#assert_axioms minaLcVerifyDesc_subpi_pins
#assert_axioms mina_program_pin_is_nine_lanes
#assert_axioms mina_bind_attests_the_pinned_program
#assert_axioms mina_bind_guard_cannot_be_disarmed
#assert_axioms mina_wrap_fs_row_is_fillable
#assert_axioms forged_program_was_admitted
#assert_axioms forged_program_refused
#assert_axioms forged_program_old_admits_new_rejects
-- ⚑⚑⚑ THE SEGMENT RUNG, 2026-08-05: `LINK_OK` was a BARE `= 1` on a witnessed column and the nine
-- `TIP_STATE` lanes were PI-bound, width-checked and joined to NOTHING. One `.bind` leg makes the
-- carrier the guard of a pinned recursion seam whose declared commitment IS those nine lanes.
#assert_axioms minaLcVerifyDesc_link_bind
#assert_axioms mina_link_bind_commits_the_tip_lanes
#assert_axioms mina_link_program_pin_is_nine_lanes
#assert_axioms mina_link_bind_attests_the_pinned_program
#assert_axioms mina_link_guard_cannot_be_disarmed
#assert_axioms mina_link_row_is_fillable
#assert_axioms the_forged_link_lane_moves_a_real_value
#assert_axioms forged_link_program_was_admitted
#assert_axioms forged_link_program_refused
#assert_axioms forged_link_program_old_admits_new_rejects
-- ⚑⚑⚑ THE FINALIZE RUNG, 2026-08-06: `PICKLES_WITNESSED` carried FOUR of upstream's conjuncts as a
-- single witnessed bit. Two of them — `xiCorrect` and `bCorrect` against `PastaIPA.bEval` — are now
-- `FINALIZE_XI_B_PROVED`, the guard of a `proofBind` against `dregg-mina-wrap-conjunction::v1`. The
-- residue is `PICKLES_OPENING_WITNESSED`: the IPA opening, `cipCorrect`, `plonkChecksPassed`, and
-- nothing else. ⚠ Two of four, at a ξ this descriptor does not weld — the weld is the consumer's
-- `fold_endo_into_finalize`.
#assert_axioms minaLcVerifyDesc_conj_bind
#assert_axioms mina_conj_program_pin_is_nine_lanes
#assert_axioms mina_conj_bind_attests_the_pinned_program
#assert_axioms mina_conj_guard_cannot_be_disarmed
#assert_axioms mina_conj_row_is_fillable
#assert_axioms the_forged_conj_lane_moves_a_real_value
#assert_axioms forged_conj_program_was_admitted
#assert_axioms forged_conj_program_refused
#assert_axioms forged_conj_program_old_admits_new_rejects
-- ⚑⚑ THE CLOSURE, 2026-08-03: `SUBMIT_H ≤ BLOCK_LEN` was unforced because `REQ_DEPTH` carried NO
-- range lookup. One leg on the already-declared table closes it, and the falsifier is exhibited
-- both ways over a DEFINED pre-repair predicate rather than a remembered one.
#assert_axioms minaLcAir_forces_nonneg_witnessed_depth
#assert_axioms minaLcAir_forces_submit_within_the_segment
#assert_axioms mina_submit_relation_is_not_the_link_count
#assert_axioms mina_negative_req_depth_was_admitted
#assert_axioms mina_negative_req_depth_is_refused
#assert_axioms mina_negative_req_depth_row_submits_above_the_tip
#assert_axioms minaLcAir_sound
#assert_axioms minaLcAir_no_forgery

end Dregg2.Circuit.Emit.LightClientMinaAir
