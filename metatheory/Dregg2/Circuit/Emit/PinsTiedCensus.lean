/-
# `Dregg2.Circuit.Emit.PinsTiedCensus` — ⚑ THE FOURTEEN DESCRIPTORS THAT FAIL THE TIE VERDICT,
each classified DECORATIVE or FAITHFUL, with the reason and the evidence that settled it.

⚑ SUBSTRATE, SAID OUT LOUD (House Law #1): this file authors NO AIR. It reads already-emitted
`EffectVmDescriptor2` values and states decidable facts about them, plus two `EffectAir` source
verdicts. Nothing here changes a shipped object, so nothing here rotates a VK or re-genesises.

## What was measured, and by what

`EffectLowerCertified.EffectAir.pinsTied` is the SECOND verdict: **every column published by a
`pi_binding` must be READ by some other leg.** A pin whose column nothing reads is a claim
`loc col ≡ pub idx` about a column the prover chooses on both sides — the refinement
`lowerAirCertified` proves is faithful and worthless.

Measured 2026-08-06 over the 111 emitted descriptors in `circuit/descriptors/by-name/`, with the
emitted-object analogue (`LightClientAnchorConnectivity.isPiBound` ∧ ¬`isRead`, which is `pinsTied`
one rail down — the source's `AirLeg.readCols` and the emitted `relatedCols` are the same walk):

  * **97 of 111 pass unchanged.**
  * **14 fail, on 157 pins between them.**

⚑⚑ **RE-MEASURED 2026-08-08 — 95 pass / 16 fail on 183 pins.** The walker's `.bind`/`.proofBind`
arm was complicit (it read declarations, not emitted polynomials); the two rows the fix moved are
both Mina light-client rungs, classified in §2's dated confession below. The 2026-08-06 numbers
above are kept as what THAT instrument measured; they refuse to reproduce because the code
producing them is deleted.

⚠ And the STRICTER reading (`pinsJoined` / `decorativeAnchors`, which additionally demands the
reading constraint name a SECOND column) fails **22 descriptors on 420 pins** — the gap between the
two is the unary-thread class of `EffectLowerCertified` §7a. This file is about the 14.

## ⚑ THE FOURTEEN, CLASSIFIED

**DECORATIVE (8 descriptors, 81 pins)** — published, and constrained by nothing anywhere. For each,
what would bind it is named; none of them is waiting on a decision.

1. **`dregg-eth-lightclient-verify::v1`** — 11/11 untied (cols 10..20: `COMMITTEE_ROOT`, nine
   `FIN_STATE_ROOT` limbs, `DOMAIN_GVR`). Already PROVED unread by
   `LightClientAnchorConnectivity.eth_anchors_are_unread`; not even a width lookup names them.
   BIND: derive `BLS_OK` from `COMMITTEE_ROOT`, or `EXEC_OK` from the execution-branch fold.
2. **`dregg-tm-lightclient-verify::v1`** — 11/11 (cols 50..60). `tm_anchors_are_unread`. ⚑ The
   chain-id equality holds between two WITNESSED columns while the published chain-id domain (col
   60) is in no gate: the circuit checks that the prover agreed with itself.
3. **`dregg-midnight-lightclient-verify::v1`** — 12/12 (cols 39..50). `mid_anchors_are_unread`.
   `ROUND_OK`/`ERA_OK` are forced bits joined to nothing; the published round and era are cols 49
   and 50.
4. **`dregg-solana-lightclient-verify::v1`** — 10/22 (cols 69..78: the nine `BANK_ROOT` limbs and
   `SLOT_COL`). `sol_anchors_are_unread`. ⚑ This one is the PROOF THE REPAIR IS ORDINARY: it was
   19/19 until 2026-08-04, when the stake-table fold was absorbed and twelve anchors became the
   fold's output lanes. Same move again for the bank root.
5. **`dregg-presentation-freshness::summary-v1`** — 19/20 (cols 0..18). The descriptor's entire read
   set is `{19,20,21,22}`. ⚠ And worse than the pins: `NOT_AFTER` (col 20) is read by the freshness
   gates and pinned by NOTHING, while the one tied pin's slot (`verifier_block_height`, PI 19) is
   never compared against the server's real height (`wire/src/server.rs:120-150` checks the action
   binding and nothing else) — so the prover picks BOTH operands of `diff = not_after − verifier`
   and an expired token satisfies the whole gadget.
   BIND: re-derive cols 0 and 11..18 verifier-side the way slots 1..8 already are, force col 10 to
   the Poseidon2 image its sibling already forces (`BoundPresentationEmit.tagLookup`), and compare
   PI 19 against the verifier's own height.
6. **`dregg-temporal-predicate-gte::dsl-v1`** — 2/4 (col 37 `STATE_ROOT`, pinned first AND last).
   No gate, window or boundary reads col 37, and no window gate threads it — so the first-row and
   last-row values are two INDEPENDENT free felts and the descriptor cannot even relate them to each
   other. ⚠ Note the trap this instantiates: pinning a column on two rows is not a cross-row tie; a
   tie across rows needs a `window .transition`, which is exactly what is missing.
   BIND: thread the root and chain it to `VALUE` per step (`root_next = H(root_loc, value_loc)`), or
   delete col 37 and leave the roots as host policy metadata.
7. **`dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1`** — 8/24 (cols 45..52,
   `guard_table_commitment`). The read set is `{0..44}`; the guard identity is in no preimage and no
   output-lane group, so the published guard is 8 free felts attachable to any hole commitment.
   BIND: absorb the guard lanes in the stage-1 fold so `hole_commit` commits to the guard identity.
8. **`private-book-bfv-threshold-terminal-q0-b80::exact-limb-v1`** — 8/14 (cols 40..47,
   `TERM_CONTEXT`). Computed in Rust (`circuit-prove/src/private_book_bfv_terminal.rs:279-323`),
   memcpy'd into the row, and recomputed verifier-side by NOBODY; also outside every range table, so
   not even width-bounded. BIND: the fused sibling already does it —
   `circuit-prove/src/private_book_bfv_terminal/fused.rs:445-451` drops these pins and re-pins the
   same columns to the slice's in-proof key-chain `public_key_root`.

**FAITHFUL (6 descriptors, 76 pins)** — the pin reproduces a shape the rung is not supposed to
close, and the binding is a NAMED object one rung up. Each is recorded with WHERE.

9. **`dregg-descent-custody-census-fixed8-v2`** — 16/86 (cols 0..15, `STATE_BASE`/`STATE_SPAN`, the
   `[old8 ‖ new8]` custom-PI state prefix). The readable trace begins exactly at
   `PATH_BASE = STATE_BASE + STATE_SPAN = 16` — the prefix is a DOOR, not a witness. Welded per lane
   by `circuit-prove/src/joint_turn_recursive.rs:751-758` ("THE STATE TOOTH: the sub-proof's
   declared pre/post roots == the leg's real roots"), reached from
   `circuit-prove/src/ivc_turn_chain.rs:4361-4418`. The census's OWN contribution
   (`post_fields_root8`, pi 16..23) is AIR-derived and tied.
10. **`private-graph-rewrite-cell-4x2::injective-swapnet-poseidon2-v1`** — 17/45: cols 310..325 are
    the same 16-felt Custom-VK state door (`CELL_OLD_COMMIT_BASE`/`CELL_NEW_COMMIT_BASE`), welded by
    `circuit-prove/src/joint_turn_recursive.rs:264`
    (`prove_custom_binding_node_state_segmented`, per-lane, with
    `every_state_prefix_lane_is_bound_by_the_state_fold` at `:1824`); col 309 is `INDEX`.
11. **`private-graph-rewrite-4x2::injective-swapnet-poseidon2-v1`** — 1/29: col 309 `INDEX`, the
    SAME layout constant (`Dregg2/Crypto/PrivateGraphRewriteDescriptor.lean:80`, used twice in the
    file: the `def` and the pin). Bound by a PROTOCOL predicate over adjacent public statements, not
    an AIR equation: `Dregg2/Crypto/GraphRewriteHistory.lean:100` `nextIndex`, refusal theorem
    `wrong_index_refused` at `:139`. ⚑ Its absence from the roots is LOAD-BEARING:
    `graphRootInputExprs` absorbs exactly 16 lanes (full Poseidon2-W16 arity, no room), and step
    `i`'s `newRoot` must be byte-identical to step `i+1`'s `oldRoot` — absorbing an index would
    destroy that reuse. Honest residue: `nextIndex` enforces relative contiguity, never absolute
    position.
12. **`private-preference-cell-n4k4::score2-wide-poseidon2-v1`** — 16/27 (cols 118..133), the same
    Custom-VK door, same fold, leaf minted by
    `circuit-prove/src/custom_leaf_adapter.rs:1168`.
13. **`faithful-note-spend-v2::exact-note16-root8-hiding`** — 8/44 (cols 1014..1021,
    `SUCCESSOR_NULLIFIER_ROOT_BASE`). Host-planned frontier: the executor recomputes it from its own
    nullifier set and refuses before verifying (`turn/src/executor/apply.rs:1709-1730`), and the
    rung that DOES prove it in-circuit exists — `faithful-note-spend-exact-v3` joins those same eight
    columns to sponge lanes and has ZERO untied pins.
14. **`dregg-bound-presentation::v1`** — 18/20 (cols 0..9, 11..18). ⚠ The most arguable of the six,
    and it is FAITHFUL only because the deployed verifiers re-derive these from ground truth they
    hold independently and REFUSE on mismatch: `federation_root` at `sdk/src/verify.rs:264`, the 8
    action-binding felts at `sdk/src/verify.rs:267-272` and `bridge/src/present.rs:2170-2180`, the 8
    revealed-facts felts at `sdk/src/verify.rs:378-386`. **Except col 9 `TIMESTAMP`, which has no
    in-circuit reader and no consumer in `sdk/`, `bridge/` or `wire/` — that one is DECORATIVE and
    should be checked against a freshness window or dropped.**

## ⚑ THE OVER-CLAIMS THE CENSUS TURNED UP — the part worth more than the counts

A decorative pin is cheap to find once you look. A doc-comment that says it is bound is not.

* `BoundPresentationEmit.lean:112-114` — *"…are ALL PiBinding-CONSTRAINED verified public inputs (no
  carried-but-not-asserted felt; parity with `presentationFreshnessDesc`)"*. Eighteen of the
  nineteen are exactly carried-but-not-asserted felts by the same file's own definition of the
  defect at `:12-14`. Echoed downstream: `sdk/src/verify.rs:346-347` calls the revealed-facts PIs
  *"constrained in-circuit"*.
* `Market/PrivateBookBfvButterflyAir.lean:717-720` — *"Eight public context lanes bind the proof to
  the exact transform carrier…; they do not by themselves prove that carrier's still-open committed
  LogUp relation."* The caveat disclaims the WRONG gap: it concedes the LogUp relation and asserts
  the binding, and the binding is what does not exist.
* `TemporalPredicateEmit.lean:81` — *"the per-step state root (bound to the IVC chain at the
  boundary)"*. There is no IVC chain that consumes or produces it. And `:36-40`'s stated residual
  ("pins only the FIRST and LAST state roots; interior roots are unbound") UNDERSTATES it: the first
  and last are unbound too.
* `GuardedHidingSpanGuardWeld.lean:41-45` — *"…are bound (mod `p`) to the WIDE commitment
  `guardTableCommit8 absorb tbl`…"*. Conclusion 2 of `guardedHidingSpan_refines_parse_grounded`
  derives that from the hypothesis `hgtc` — an assumption of the very equality claimed, transported
  onto the lane by the pin. The same file lists `hgtc` as a standing residual at `:72-74`.
* `PresentationEmit.lean:71` names two mutation canaries that *"each bite a distinct constraint"*;
  both bite only against a FIXED trace, so a prover re-emitting the trace satisfies any summary PI
  and the canary cannot go red for the adversary it names.

## ⚠ What was NOT done, said plainly

`TiedAir` was **not weakened** to admit any of the 14 — no descriptor here carries the certified
lowering, and the six FAITHFUL ones stay outside it until the door is expressed as something the
verdict can see. (⚑ 2026-08-08: the two Mina rows the emission-faithful walker added DID carry
`lowerTiedAir`; they were demoted to `lowerAirCertified` — identical bytes, refinement kept, tie
verdict honestly dropped — rather than the verdict being widened to keep them.) The discriminator that would admit them honestly is not "read by a constraint" but
"declared as an externally-welded ABI lane", which the tree already names in prose
(`ParamComposeEmit.lean:554-555`) and could carry as a FIELD on the descriptor. That is a design
fork, not a repair, and it is left standing rather than guessed at.

## Axiom hygiene
No `sorry`, no `native_decide`, no new axiom, no `#guard`. NEW file; imports read-only; ADDITIVE.
-/
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.Emit.LightClientAnchorConnectivity
import Dregg2.Circuit.Emit.PresentationEmit
import Dregg2.Circuit.Emit.BoundPresentationEmit
import Dregg2.Circuit.Emit.TemporalPredicateEmit

namespace Dregg2.Circuit.Emit.PinsTiedCensus

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.LightClientAnchorConnectivity (isPiBound isRead)

set_option autoImplicit false
set_option maxRecDepth 8000

/-! ## §1 — the emitted-object form of `pinsTied`'s failure set.

`EffectAir.pinsTied` is a verdict on the SOURCE. Only three of the fourteen have a source `EffectAir`
at all (the other eleven are hand-written descriptor literals), so the census is stated one rail
down, on the emitted object — where `isRead` walks exactly the constraint forms `AirLeg.readCols`
walks legs. -/

/-- ⚑ **THE UNTIED PINS OF `d`**, ascending: every PI-bound column that NO constraint reads. This is
`EffectAir.pinsTied = false`'s witness set, at the emitted object.

⚠ Strictly weaker than `decorativeAnchors`, and deliberately: that one demands the reading
constraint name a SECOND column, so it also catches the unary thread. A column here is read by
nothing at all — not even an arity-1 range lookup. -/
def untiedPins (d : EffectVmDescriptor2) : List Nat :=
  (List.range d.traceWidth).filter fun col => isPiBound d col && !isRead d col

/-! ## §2 — the SOURCE verdicts, for the three of the fourteen that are `lowerAir`-authored.

These are the ones that could have carried `TiedAir` and do not. Each is `pinsTied = FALSE`, decided
on the source — so the day someone binds the anchors, the theorem goes red and this file has to be
re-read rather than quietly outlived. -/

/-- ⚑ Ethereum's head AIR REFUSES the tie verdict. -/
theorem ethHeadAir_untied : LightClientEthAir.ethHeadAir.pinsTied = false := by decide

/-- ⚑ Solana's verify AIR REFUSES it. ⚠ It also passed with 19 untied anchors before 2026-08-04 and
now has 10: this verdict falling is what repair looks like, and it is not a flag day. -/
theorem solLcVerifyAir_untied : LightClientSolanaAir.solLcVerifyAir.pinsTied = false := by decide

/-- ⚑ The presentation-freshness summary AIR REFUSES it — nineteen of twenty pins. -/
theorem presentationFreshnessAir_untied :
    PresentationEmit.presentationFreshnessAir.pinsTied = false := by decide

/-! ### ⚑⚑ 2026-08-08 — TWO ROWS MOVED FROM THE PASS COLUMN TO THE FAIL COLUMN, WITH NO
DESCRIPTOR BYTE HAVING CHANGED: THE INSTRUMENT CONFESSED, NOT THE DESCRIPTORS.

`the_tied_neighbours_pass` stood here asserting `minaHeadAir.pinsTied = true ∧
minaLinkAir.pinsTied = true ∧ solStakeFoldAir.pinsTied = true`. The first two were true only
because `AirLeg.readCols` returned a `.bind` leg's whole DECLARATION — guard ∪ commit ∪ vk ∪
bound — while `descriptor_ir2.rs` emits polynomials over `commit` only under a `bound` and over
`vk` only under a `vkPin`, and every served Mina seam is `bound := none`. So the two Mina airs'
commitment/body pins were scored as tied by the very seam declarations whose forcing was the
question. Emission-faithful (`EffectLowerCertified` §1a, same day as
`LightClientAnchorConnectivity.relatedCols`' identical confession one rail down), both go FALSE;
the old theorem's numbers refuse to reproduce because the code producing them is deleted. The
header's 2026-08-06 measurement (97 pass / 14 fail on 157 pins) was taken at the emitted rail
with the then-complicit walker; emission-faithful the census is **95 pass / 16 fail on 183
pins** — the two rows below are the delta, each with its classification:

15. **`dregg-mina-lightclient-verify::v1`** — 18/39 untied (cols 40..48 `SUB_PI`, 68..76
    `CONJ_PI`). FAITHFUL-BY-HOST-WELD: digest-shaped ports whose forcing is the executor's
    REFUSAL 4 (`check_transcript_binding`) and REFUSAL 15 (`check_conjunction_binding` — wired
    2026-08-08, dead code the two days before), censused as `MinaSeams.subPiWeld`/`conjPiWeld`,
    both-polarity tested in `mina_head_verifier.rs`.
16. **`dregg-mina-lightclient-link::v1`** — 8/46 untied (cols 40..47 `BODY_ACC`). Same class:
    the forcing is REFUSAL 16 (`check_body_chain_binding`, landed 2026-08-08 — these eight lanes
    had NO reader of any kind before it), censused as `MinaSeams.bodyAccWeld`. ⚠ No in-AIR width
    lookup exists or is owed: a BabyBear digest lane fills its column, and a 29-bit table would
    refuse honest witnesses — a full-width lookup would be decoration.

Their `TiedAir`s are DEMOTED to `lowerAirCertified` at identical bytes (the refinement
certificate survives; the tie verdict is no longer claimed); the per-file reds are
`minaHeadAir_pinsTied_is_false` / `the_untied_pins_are_exactly_the_commitment_blocks` and
`minaLinkAir_pinsTied_is_false` / `the_untied_pins_are_exactly_the_body_acc`. -/

/-- ⚑ The Mina head verify AIR now REFUSES the tie verdict — see the dated section above. -/
theorem minaHeadAir_untied : LightClientMinaAir.minaHeadAir.pinsTied = false := by decide

/-- ⚑ The Mina link AIR now REFUSES it too. -/
theorem minaLinkAir_untied : LightClientMinaLinkAir.minaLinkAir.pinsTied = false := by decide

/-- …and the neighbour that still carries `TiedAir` passes, so the verdicts above are a
discrimination and not a constant. (Until 2026-08-08 this theorem asserted the two Mina airs pass;
that assertion is the one the confession above retires.) -/
theorem the_tied_neighbours_pass :
    LightClientSolStakeFoldAir.solStakeFoldAir.pinsTied = true :=
  LightClientSolStakeFoldAir.solStakeFoldAir_pinsTied

/-! ## §3 — the emitted census, per descriptor, pinned to its exact literal.

Each theorem FAILS the day one of these columns enters any constraint. That is the point: a
classification that cannot go red is a note, not a census. -/

/-- **Ethereum: eleven, all of them.** -/
theorem eth_untied_pins :
    untiedPins LightClientEthAir.ethLcVerifyDesc
      = [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20] := by decide

/-- **Tendermint: eleven, all of them.** -/
theorem tm_untied_pins :
    untiedPins LightClientTendermintAir.tmLcVerifyDesc
      = [50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60] := by decide

/-- **Midnight: twelve, all of them.** -/
theorem mid_untied_pins :
    untiedPins LightClientMidnightAir.midLcVerifyDesc
      = [39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50] := by decide

/-- **Solana: ten of twenty-two** — the nine `BANK_ROOT` limbs and `SLOT_COL`. The twelve that left
this list on 2026-08-04 are the stake-table fold's output lanes. -/
theorem sol_untied_pins :
    untiedPins LightClientSolanaAir.solLcVerifyDesc
      = [69, 70, 71, 72, 73, 74, 75, 76, 77, 78] := by decide

/-- **Presentation freshness: nineteen of twenty.** Only `VERIFIER` (col 19) is read. -/
theorem presentationFreshness_untied_pins :
    untiedPins PresentationEmit.presentationFreshnessDesc
      = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18] := by decide

/-- **Bound presentation: eighteen of twenty.** `PRESENTATION_TAG` (col 10) left this list when the
tag lookup landed — the one column of the twenty that a constraint forces. -/
theorem boundPresentation_untied_pins :
    untiedPins BoundPresentationEmit.boundPresentationDesc
      = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18] := by decide

/-- **Temporal predicate: one column, pinned twice.** ⚑ `STATE_ROOT` (37) is pinned on the first row
AND the last row; two pins, one untied column. A pin is a claim about ONE ROW, so this is not a
cross-row tie and the two published roots are independent free felts. -/
theorem temporalPredicate_untied_pins :
    untiedPins TemporalPredicateEmit.temporalPredicateDesc = [37] := by decide

/-- **Mina head verify: eighteen of thirty-nine** — the two digest-shaped commitment ports
(`SUB_PI` 40..48, `CONJ_PI` 68..76), row 15 of the dated confession. Forced by executor welds
(REFUSAL 4/15), not by any emitted polynomial; the anchor and tip nonets stay READ (lane
lookups), so they are absent here while present in `decorativeAnchors`' 36. -/
theorem minaVerify_untied_pins :
    untiedPins LightClientMinaAir.minaLcVerifyDesc
      = [40, 41, 42, 43, 44, 45, 46, 47, 48, 68, 69, 70, 71, 72, 73, 74, 75, 76] := by decide

/-- **Mina link: eight of forty-six** — the `BODY_ACC` island (cols 40..47), row 16 of the
dated confession. The eight lanes NO constraint of any kind reads; forced by REFUSAL 16's
executor weld since 2026-08-08 and by nothing before it. -/
theorem minaLink_untied_pins :
    untiedPins LightClientMinaLinkAir.minaLinkDesc
      = [40, 41, 42, 43, 44, 45, 46, 47] := by decide

/-! ⚠ **`dregg-guarded-hiding-span-m0::wide-blinded-commit-blind5-v1` is classified above but NOT
pinned here.** Its module chain (`GuardedHidingSpanEmit` → `BlindedMembershipWideEmit`) was mid-flag-day
on 2026-08-06 — a sibling's `GateExpr` collapse had `bitBinaryBody_eq` unresolved — and importing a
red module to state one `decide` would have made this census hostage to that repair. The measurement
stands (cols 45..52, the whole `guard_table_commitment` group, read set `{0..44}`); the theorem is the
one line to add when that chain settles. Naming the gap beats a green file that quietly dropped it. -/

/-! ### §3a — ⚑ the one that is worse than its pins.

`NOT_AFTER` is READ by the freshness gates and pinned by NOTHING, so it is invisible to a census of
pins — and it is the operand that makes the gadget vacuous. Stated here because the instrument that
found the fourteen is structurally blind to it. -/

/-- ⚑ **THE FRESHNESS GADGET'S OTHER OPERAND IS A FREE WITNESS.** `NOT_AFTER` (col 20) is read by
`diff = not_after − verifier` and is bound to no public input at all. Together with PI 19 never
being compared against the verifier's own height (`wire/src/server.rs:120-150`), the prover chooses
both sides of the freshness inequality. -/
theorem presentationFreshness_notAfter_is_read_but_unpinned :
    isRead PresentationEmit.presentationFreshnessDesc PresentationEmit.NOT_AFTER = true
      ∧ isPiBound PresentationEmit.presentationFreshnessDesc PresentationEmit.NOT_AFTER = false := by
  decide

/-! ## §4 — axiom hygiene. Named theorems, `#assert_axioms`, no `#guard`. -/

#assert_axioms ethHeadAir_untied
#assert_axioms solLcVerifyAir_untied
#assert_axioms presentationFreshnessAir_untied
#assert_axioms minaHeadAir_untied
#assert_axioms minaLinkAir_untied
#assert_axioms the_tied_neighbours_pass
#assert_axioms minaVerify_untied_pins
#assert_axioms minaLink_untied_pins
#assert_axioms eth_untied_pins
#assert_axioms tm_untied_pins
#assert_axioms mid_untied_pins
#assert_axioms sol_untied_pins
#assert_axioms presentationFreshness_untied_pins
#assert_axioms boundPresentation_untied_pins
#assert_axioms temporalPredicate_untied_pins
#assert_axioms presentationFreshness_notAfter_is_read_but_unpinned

end Dregg2.Circuit.Emit.PinsTiedCensus
