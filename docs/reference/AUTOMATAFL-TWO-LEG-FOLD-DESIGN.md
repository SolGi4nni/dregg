# AUTOMATAFL — THE TWO-LEG FOLD: making the match proof cover the PLAYERS' MOVES

**Status:** phases 0–9 LANDED in the working tree (2026-07-23), UNPROVEN on the deployed prover.
Every file:line below is `@HEAD` (`2ea221d99f`) unless marked NEW; the landed code has moved some
of them.

What is in the tree: `BoardWindowBinding` + slice extractors
(`circuit/src/effect_vm/custom_state_binding.rs`), the 46-lane board-window leaf
(`custom_leaf_adapter.rs::prove_custom_leaf_descriptor_with_board_window`), the 47-lane node
(`joint_turn_recursive.rs::prove_custom_binding_node_state_and_board_segmented`), the merge seam
(`ivc_turn_chain.rs::board_window_connects` / `segment_combine_expose_with_board_window`, with the
combine mode DERIVED from the children's own exposed shapes rather than a caller flag), the host
mirror (`board_window_of_chain`), the verifier/artifact/lightclient extension, Leg A's `NAX/NAY`
PIs (the step descriptor now publishes 38), and `AutomataflMatch::round_leaves` emitting Leg R then
Leg A per round.

⚠ **A LIVE BLOCKER FOUND BY THE CANARIES.** Every path that MINTS a leg — `round_leaves`,
`build_match_turns`, and therefore the host mirror `board_window_of_chain` — currently panics in
`dregg_multiway_tug::fold::mint_custom_leg`'s wide `Custom` leg:
`compact_e1_columns: customVmDescriptor2R24 row width 1627 < E1 band end 1675`. That is the E1
dead-column compaction cutover (`bd21266e6b`) disagreeing with the wide custom generator's row
width; it is unrelated to the board window, and no fast test covered it (`dregg-multiway-tug`'s 39
lib tests pass; its leg-minting tests are `#[ignore]`d). Until it is reconciled, the two-leg fold
cannot run at all. The seam canaries that need a minted leg are `#[ignore]`d as BLOCKED, naming it.

What is NOT: **no real two-leg fold has been run.** The acceptance gate is
`dreggnet-game-board/tests/two_leg_board_window.rs::a_mismatched_mid_does_not_fold_on_the_deployed_prover`
(`#[ignore]`d, tens of minutes). Note §8's phase-8 gate names
`mismatched_mid_fold_probe_11x11` — that test is on the RUST-AIR path
(`descriptor_state_leaf: None`, no window declared) and this seam does not reach it; the gate is
the new twin. Also not landed: the gated step (§6.2), Leg R's move PIs and Leg S (§4, §11–13), and
`match_anchor`'s board-window pinning (§7.1's last bullet — the anchor still pins cell anchors
only).

**The substrate, said out loud:** every constraint object named here — the resolve descriptor, the
step descriptor, the gated-step change, the appended PI families, the hold/reveal legs — is
**Lean-authored AIR** (`metatheory/Dregg2/Circuit/Emit/Automatafl*.lean`, emitted through
`metatheory/EmitByName.lean:107-114` into `circuit/descriptors/by-name/`). Rust in this design
**fills traces and drives the fold**. It authors zero constraints. `dregg-automatafl/src/air.rs`,
`moves.rs`, `builder.rs` are **DEBT**: they are read here as a *computation oracle* for
witness-generation values, never extended as an AIR.

---

## 0. The gap, stated exactly

The deployed automatafl match (`dreggnet-game-board/src/lib.rs:311` `AutomataflMatch::leaves`) folds
**one leaf per turn**: the D1 automaton step, and since `2ea221d99f` that leaf proves through the
PROVEN Lean descriptor `automataflStepDescN 11`
(`dregg-automatafl/src/witness.rs`, `circuit/descriptors/by-name/automatafl-step-n11.json`,
678 cols / 36 PIs / 1070 gates, zero lookups).

Three things are therefore **not** attested by a ranked leaderboard entry today:

| # | Un-attested | Why |
|---|---|---|
| **G1** | the players' moves are legal and were resolved correctly | the RESOLVE leg is emitted + proven in Lean (`automataflResolveDescN 11`, `resolve_sat_imp_roundBoardN`) but **never folded** |
| **G2** | the boards form a **trajectory** | nothing connects turn `i`'s `packed_new` PIs to turn `i+1`'s `packed_old` PIs. The only cross-turn tooth is CELL rotated-root continuity, which is a nonce bump and is **content-independent** |
| **G3** | the match started at the stock opening / ended at the claimed position | the artifact's `genesis_root`/`final_root` are the *cell* anchors, not the board |

G2 is not a new discovery of this design — it is already **pinned by a live test**:
`dregg-automatafl/tests/prove_11x11.rs:216`
`mismatched_mid_diverges_board_roots_but_not_cell_continuity_11x11` demonstrates at PI level that a
forged mid diverges the board roots and that the deployed cross-turn tooth does not see it. The
`#[ignore]`d `mismatched_mid_fold_probe_11x11` (line ~550) exists precisely to *record* that the
fold accepts it.

So: **all three gaps close with ONE mechanism** — a fold-enforced equality between the *board*
public inputs of adjacent leaves. That mechanism is what the Lean whole-turn capstone was built to
consume.

---

## 1. The proven seam (what we must feed, verbatim)

`metatheory/Dregg2/Circuit/Emit/AutomataflTurnCapstone.lean:284`

```lean
theorem turn_sat_imp_roundStep_pi
    (hsatR : Satisfied2 hashR (automataflResolveDescN 11) … tR) (hcR) (hlenR)
    (hsatA : Satisfied2 hashA (automataflStepDescN 11)     … tA) (hcA) (hlenA)
    (hclean …) (hfresh …) (hres …)
    (hseamPack  : ∀ j, j < feltCount 11 → tR.pub (16 + feltCount 11 + j) = tA.pub (16 + j))
    (hseamAutoX : tR.pub (Resolve.AUTO_PI_BASE 11)     = tA.pub (Step.AUTO_PI_BASE 11))
    (hseamAutoY : tR.pub (Resolve.AUTO_PI_BASE 11 + 1) = tA.pub (Step.AUTO_PI_BASE 11 + 1)) :
    ∀ x y, x < 11 → y < 11 →
      codeToParticle ((envAt tA 0).loc (Step.NGen.new 11 (y*11+x)))
        = (outcomeBoard (roundStep ⟨.column⟩ g (openRound (boardDecodeOldN 11 (envAt tR 0)) seats)
             [moveDecodeN 11 (envAt tR 0) 0, moveDecodeN 11 (envAt tR 0) 1])).cellAt ⟨x,y⟩
```

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}. **No hash. No chip-table soundness. No
un-emitted hypothesis.** The engine of the cell half is `pack_injective_modp` (base-4 positional
decode, `packed < 4^15 < p`), so the pack equality *is* board equality — not a collision-resistance
assumption.

### The concrete PI geometry (`feltCount 11 = 9`; both descriptors publish 36 PIs)

Both legs share an identical, already-emitted layout — `AutomataflResolveEmit.lean:1725`
(`AUTO_PI_BASE n = 16 + 2*RFC n`) and `witness.rs`'s ABI table:

```
        PI[0 .. 16)     door prefix  [old8 ‖ new8]  — FREE descriptor PIs; the FOLD binds them
        PI[16 .. 25)    pack_in  (9 felts, base-4, injective)
        PI[25 .. 34)    pack_out (9 felts)
        PI[34], PI[35]  ax, ay   (the automaton coordinate of the leg's OLD board)

  Leg R (automataflResolveDescN 11, 1273 cols / 1618 gates / 0 lookups):
        pack_in  = pack(old)     pack_out = pack(cMidV4)   ax,ay = old's automaton
  Leg A (automataflStepDescN 11,   678 cols / 1070 gates / 0 lookups):
        pack_in  = pack(old)     pack_out = pack(new)      ax,ay = old's automaton
```

Only **20 of the 36 PIs are `pi_binding`-constrained** (9+9+2); the 16 door lanes are free by
design. The seam is therefore exactly **11 lanes**:

```
  hseamPack   :  R.pub[25 .. 34)  ==  A.pub[16 .. 25)      9 lanes
  hseamAutoX/Y:  R.pub[34], R.pub[35]  ==  A.pub[34], A.pub[35]   2 lanes
```

**Design law (the anti-drift rule for the whole build):** the capstone quotes *absolute* indices
`16 + fc + j`, `16 + j`, `AUTO_PI_BASE`. Every descriptor change below is therefore **APPEND-ONLY**
past PI 35. Nothing re-indexes 0..35. A re-layout would invalidate a proven theorem for cosmetic
tidiness; refuse it.

---

## 2. THE TURN AS TWO LEGS — how they chain

### 2.1 What a `FinalizedTurn` can hold

`circuit-prove/src/ivc_turn_chain.rs:583` — a `FinalizedTurn` carries **exactly one**
`DescriptorParticipant`, which carries exactly one `RotatedParticipantLeg`, which carries **at most
one** `CarrierWitness`. There is no 2-sub-proof turn. So a round is **two chained turns**, not one
turn with two carriers:

```
  round i  →  turn 2i    = Leg R  (adjudicate the two moves: old → mid)
              turn 2i+1  = Leg A  (step the automaton:      mid → new)
```

This is the shape `dregg-automatafl/tests/prove_11x11.rs` already drives at the Rust-AIR level
(`honest_11x11_two_subturn_folds_and_lightclient_accepts`) — the two legs as two turns on the same
cell lineage, nonce `n → n+1 → n+2`.

### 2.2 What already chains them (and what does not)

* **Cell continuity — chains, but says nothing about the board.** `mint_turn`
  (`dregg-multiway-tug/src/fold.rs:~390`) mints leg `i` over `producer_cell(1000, i) →
  producer_cell(1000, i+1)`; `prove_chain_core_rotated` enforces `prev.new_root8 ==
  next.old_root8` in-circuit at every merge (`segment_combine_expose`). This sequences the legs.
  It is **content-independent** — a nonce bump commits nothing about the board.
* **The state-binding node — binds a leaf to its own leg, not to its neighbour.**
  `prove_custom_binding_node_state_segmented` (dispatched at `ivc_turn_chain.rs:3244-3320`) connects
  (1) leg's claimed `custom_proof_commitment` == leaf's in-circuit PI commitment, (2) leaf's
  `pis[0..16]` == leg's real rotated roots. Both are *intra*-turn.

> **Precise answer to design question (2): NO. The seam is NOT a consequence of the existing
> connects.** The existing per-turn node re-exposes **only the segment**
> (`joint_turn_recursive.rs:617-620`, `let seg: Vec<Target> = (0..SEG_WIDTH).map(|k| ev[k])`), so
> the sub-proof's board PIs are *dropped* before the tree ever sees them. Two adjacent turns'
> board PIs are, in the fold, unrelated numbers. Hand-waving "the state node connects them" would
> void the whole-turn theorem: `hseamPack` would be unproven and `turn_sat_imp_roundStep_pi` would
> not apply. **An explicit PI-equality connect is required.**

### 2.3 THE BOARD SEGMENT — one uniform mechanism for all three gaps

Give every automatafl leaf an **11-lane IN window** and an **11-lane OUT window**, and fold them up
the tree exactly the way the chain segment is folded:

```
  per leaf:   IN  = pack_in(9)  ‖ auto_in(2)          OUT = pack_out(9) ‖ auto_out(2)
  Leg R:      IN  = pub[16..25) ‖ pub[34..36)         OUT = pub[25..34) ‖ pub[34..36)
  Leg A:      IN  = pub[16..25) ‖ pub[34..36)         OUT = pub[25..34) ‖ pub[36..38)   ← NEW PIs
```

Leg R's `auto_out == auto_in` by construction (resolution never moves the automaton — Lean:
`resolveMoves_automaton`, `AutomataflTurnCapstone.lean:94`), so it costs zero new lanes there.
Leg A needs the **new** automaton coordinate published; see §2.5.

Then the **only** cross-leaf rule in the whole design is:

```
  BOARD CONTINUITY:   left.OUT  ==  right.IN     (11 per-lane connects)
```

and it instantiates all three gaps at once:

| instance | what it becomes |
|---|---|
| `R_i.OUT == A_i.IN` | **exactly** `hseamPack` ∧ `hseamAutoX` ∧ `hseamAutoY` — the whole-turn theorem fires |
| `A_i.OUT == R_{i+1}.IN` | the inter-round board carry (**G2**) — the match becomes a trajectory |
| root's exposed `[first.IN ‖ last.OUT]` | the genesis/final board (**G3**), readable by the light client |

Because the pack is **injective** (`pack_injective_modp`), the root's 9-felt window *is* the board —
a light client can decode the final position in the clear and check the win condition with no extra
circuit (§7).

### 2.4 The three Rust pieces (all additive; nothing else changes shape)

**(a) A slice-list leaf exposure.** Generalize `AppRootBinding`
(`circuit/src/effect_vm/custom_state_binding.rs:196`, one contiguous `(offset,len)`) to a
`BoardWindowBinding { in_slices: Vec<(usize,usize)>, out_slices: Vec<(usize,usize)> }`. Leg R's
window is contiguous (`[25..36)`); Leg A's is **not** (`[16..25)` and `[34..36)` with the new pack in
between) — hence a slice *list*, not a single range. NEW adapter beside
`prove_custom_leaf_descriptor_with_state_commitment`
(`circuit-prove/src/custom_leaf_adapter.rs:759`), exposing

```
  [ commitment(8) ‖ pis[0..16] ‖ IN(11) ‖ OUT(11) ]      = 46 lanes
```

built the same way (`incircuit_custom_pi_commitment` over the leaf's real bound PI targets, so what
is exposed IS what is proven). This is a *copy* of the app-root leaf shape
(`custom_app_root_claim_len`, line 860), not a new trust surface.

**(b) A board-window binding node.** NEW
`prove_custom_binding_node_state_and_board_segmented(leg_dual, custom_leaf, config)` beside
`prove_custom_binding_node_state_segmented`: identical commitment + state connects, but re-exposes
`[segment(25) ‖ IN(11) ‖ OUT(11)]` = 47 lanes instead of `[segment(25)]`. Fail-closed on a leaf that
exposes fewer than 46 claim lanes — the same `cs_lanes < cs_want` discipline as
`joint_turn_recursive.rs:539-553`, and for the same reason stated there: *"Refusing rather than
degrading"*. A conditional connect would be the forger's dodge.

**(c) A board-window merge.** `merge_two_segment_proofs`
(`circuit-prove/src/ivc_turn_chain.rs:4089`) is the ONE farmable merge primitive that `aggregate_tree`
(4154), `aggregate_tree_streaming`, and `merge_pool` all drain. Do **not** edit it — parameterize:

```rust
enum SegmentCombine { Plain, WithBoardWindow { lanes: usize } }   // NEW
```

`Plain` is byte-identical to today (every other game/chain unaffected — a hard requirement, since
the ordered digest is shape-sensitive: `ordered_digest_combine_is_not_associative`).
`WithBoardWindow{11}` additionally emits `cb.connect(left[SEG_WIDTH+11+k], right[SEG_WIDTH+k])` for
`k<11` and re-exposes `[combined_segment ‖ left.IN ‖ right.OUT]`.

Threading: `prove_chain_core_rotated_with_fold` takes the combine mode; `compute_root_segment` gains
a host-side twin `compute_root_board_window` that folds the same windows and **fails closed before
any proving** if a mismatch exists (mirroring the existing streaming-schedule guard at
`ivc_turn_chain.rs:3115`). Cost of a bad mid: milliseconds, not hours.

### 2.5 The one Lean emission change this needs (Leg A)

Leg A must publish its **new** automaton coordinate. The step descriptor already carries `ox`/`oy`
offset columns (`AutomataflStepEmit.lean:773-793`, `A_CHOOSE_BASE + 55/56`) and the target head
`ax + ox` / `ay + oy` (line 552-553). So:

* two appended columns `NAX`, `NAY` pinned by the **degree-2 mask gates**
  `NAX − AX − M·OX == 0`, `NAY − AY − M·OY == 0`, where `M` is the step block's OWN move-mask
  column (`A_STEP_BASE n + 34 + 2n`, `= 637` at `n = 11`);
* two appended `.piBinding`s at **PI 36, 37** (append-only — 0..35 untouched);
* two transport theorems mirroring `astep_autoX_pi_of_sat` / `astep_autoY_pi_of_sat`
  (`AutomataflCommitRefine.astep_newAuto_pin_of_sat`), lifted to the FULL semantics by
  `AutomataflTurnCapstone.astep_newAuto_pi_of_sat`:
  `PI[36], PI[37] = (automatonStepCfg ⟨.column⟩ (decoded old board)).automaton`.

  **The mask is not decoration — an earlier revision of this section specified the degree-1 pin
  `NAX − (AX + OX) == 0`, and that pin cannot carry the statement the seam needs.** The reference
  `automatonStep` moves only when its guard fires
  (`.automaton = if m = 1 then (ax+ox, ay+oy) else (ax, ay)`), so `ax + ox` agrees with it on ONE
  branch of that `if`. The strongest transport statable over the degree-1 pin was therefore the
  COLUMN-level `PI = ax + ox`; lifting it to `PI = (automatonStepCfg …).automaton` would have
  needed a reachability lemma about the reference — that a nonzero sensed offset always targets an
  in-bounds vacuum cell — which nothing in the descriptor or the capstone had. `M·OX` collapses to
  `0` exactly on the `m = 0` branch, so the mask pin discharges the case split AT THE GATE and the
  transport is unconditional. Degree 2, well inside the degree-7 budget.

  **Honest scope of the fix.** That reachability lemma is in fact TRUE of the reference: every arm
  of `evaluate_axis` that yields a nonzero offset carries a `dist > 1` guard (or picks the farther
  of two repulsors), so the first cell in the chosen direction is in-bounds and vacuum. So the
  degree-1 pin was not rejecting reachable honest trajectories — the `m = 0`-with-nonzero-offset
  state does not arise from the reference. The defect was in the GUARANTEE, not a demonstrated live
  rejection, and the fix buys the full-semantics transport without paying for that lemma.
  Canaries: `AutomataflTurnCapstone.astep_newAuto_blocked_is_old` (Lean, the gate-level fact) and
  `dregg-automatafl/src/witness.rs::the_new_auto_pin_is_the_degree_2_mask_form` +
  `a_nonzero_sensed_offset_always_targets_an_in_bounds_vacuum_cell` (Rust).

Golden regen: `automatafl-step-n11.json` (+ `automatafl-step.json` at n=2), logged in
`docs/VK-REGEN-LOG.md`.

### 2.6 The 24-lane state claim and commitment coherence — unchanged

`bundle.public_inputs` remains the **single** source for both the leg's claimed
`custom_proof_commitment` (`custom_proof_pi_commitment`) and the leaf's state prefix
(`joint_turn_aggregation.rs:219-232`'s invariant), so a board-window leaf cannot disagree with its
leg's commitment. The `[commitment8 ‖ old8 ‖ new8]` prefix of the exposed claim is byte-identical to
the state leaf's; the board window is strictly appended. The state node's two teeth are untouched.

---

## 3. THE SEAM ENFORCEMENT — precisely

The connect chain, end to end, with the reason each link holds:

```
1.  R's trace satisfies automataflResolveDescN 11        ← in-circuit FRI verify of the leaf, folded
2.  R.pub[25+j] = pack(cMidV4)_j                          ← EMITTED transport resolve_midPack_pi_of_sat
                                                             (the .piBinding at 16+RFC+j, gate-forced)
3.  R.pub[25+j] = A.pub[16+j]                             ← cb.connect in the board-window merge  ★
4.  A.pub[16+j] = pack(A's decoded old board)_j           ← EMITTED transport astep_oldPack_pi_of_sat
5.  ⇒ pack(cMidV4) = pack(A.old) ⇒ boards equal cellwise  ← pack_injective_modp (base-4, < p; NO hash)
6.  R.pub[34,35] = A.pub[34,35]                           ← cb.connect  ★
7.  ⇒ A.old.automaton = R.old.automaton                   ← seamAuto_of_pi (both .piBindings emitted)
8.  ⇒ turn_sat_imp_roundStep_pi fires: A's new board IS roundStep's outcome board
```

★ = the two things the fold must add. Everything else is already emitted and proven.

**Where the connect lives, and why it is sound there.** `cb.connect(a, b)` inside an aggregation
node's `expose` closure is a circuit equality between two targets read out of the two children's
**verified** `air_public_targets` — the same primitive the deployed state tooth uses
(`joint_turn_recursive.rs:601-612`) and the same primitive the chain's own continuity uses. A
disagreeing pair is a per-lane conflict ⇒ the node is UNSAT ⇒ no proof ⇒ no root ⇒ the light client
never receives a verifying artifact. The child's circuit identity is pinned in-band by its
preprocessed commitment (`batch_to_pinned_input`, `ivc_turn_chain.rs:4053`), so the parent cannot be
handed a proof of a *different* circuit that happens to expose 47 lanes.

**Fail-closed on shape.** The root's exposed claim is compared for **exact equality** against the
carried claim (`ivc_turn_chain.rs:4453`, `if exposed != expected`). A board-window root exposes
`25 + 22 = 47` lanes; today's verifier builds a 25-lane `expected` and would **reject** it. That is
the right default: it forces the artifact/verifier extension in §7 rather than silently shipping
lanes nobody checks. Symmetrically, a fold run *without* the window cannot claim one.

**What the seam does NOT give you.** `turn_sat_imp_roundStep_pi` still takes three *spec-side*
hypotheses about the DECODED moves, none of which the seam discharges:

* `hclean` — the round has no clash (closed structurally by §6's gated step);
* `hfresh` — both submissions are seat-fresh and `moveLegalB`-legal against `marks = []`;
* `hres` — `resolvableB`.

`hfresh`/`hres` are §5's work. Calling the seam alone "the whole turn is proven" would be exactly
the over-claim this design exists to avoid.

---

## 4. THE MOVES AS INPUT — public, committed, or revealed?

### 4.1 Today: the moves are *neither* public nor committed — they are free witness

`moveDecodeN` (`AutomataflResolveRefine.lean:3785`):

```lean
def moveDecodeN (n : Nat) (e : VmRowEnv) (which : Nat) : Move :=
  Move.mk 0                                              -- ← `who` is HARD-CODED 0
    ⟨(e.loc (NGen.cFx n (NGen.mvBase n which))).toNat, (e.loc (NGen.cFy n …)).toNat⟩
    ⟨(e.loc (NGen.cTx n …)).toNat,                      (e.loc (NGen.cTy n …)).toNat⟩
```

The moves live in **trace columns** `cFx/cFy/cTx/cTy` at `mvBase n which`, and there is no seat
column at all. So a folded resolve leaf today says:

> "∃ two rook-aligned, in-bounds, distinct moves whose resolution yields this mid board."

That is a real and useful statement — it is what makes the *board transition* legal — but it is
**not** "the players' submitted moves". A prover can invent the pair. **This is the actual
completeness boundary of "the proof covers the game", and folding resolve alone does not cross it.**

### 4.2 The already-emitted answer: **Leg S**, the sealed-move reveal

`metatheory/Dregg2/Circuit/Emit/AutomataflRevealEmit.lean` is a Lean-authored, 11×11 reveal leg with
41 PIs:

```
  PI[0 .. 16)   door prefix
  PI[16 .. 25)  pack(old board)          — the SAME 9-felt injective pack Legs R/A publish
  PI[25 .. 32)  seat A opening: fx, fy, tx, ty, seat, nonce, commit
  PI[32 .. 39)  seat B opening: fx, fy, tx, ty, seat, nonce, commit
  PI[39 .. 41)  contiguous copy of the two commitment felts (shaped for the app-root weld)
```

with `commit = hash_4_to_1([frm, to, seat, nonce])` served by a Poseidon2 chip row, seat pinned
A=0/B=1, and every coordinate range-gated to `[0,11)`.
`AutomataflRevealJoin.lean` states the join theorem against the deployed `AppRootBinding`
(`app_root_pi_offset = 39`, `app_root_len = 2`, `field_key = 2`, welding to the cell's `a_commit`/
`b_commit` registers 5/6) **and** names its own blockers as theorems (lines 184-207):
`live_host_seal_lane0_is_not_injective`, `one_felt_commitment_cardinality_window`,
`current_field_octet_too_short_for_old_pack`, `fixed_n11_descriptor_is_not_live_game_shape`.

The clear-side commit-reveal surface already exists and is a real turn-per-phase executor:
`dregg-automatafl/src/surface.rs` (select → commit → reveal → resolve, per-seat fog, monotone
commit/reveal counters, `SealedMove::commit(n)` in `moves.rs:1043`).

### 4.3 The design: **three legs per round**, joined by the same PI-equality mechanism

```
  turn 3i     Leg S   reveal    : the two openings match the two committed seals
  turn 3i+1   Leg R   resolve   : old → mid, adjudicating THOSE moves
  turn 3i+2   Leg A   step      : mid → new  (gated, §6)
```

Two new seams, both the same `cb.connect` primitive:

* **S→R move seam (8 lanes).** Leg R must **publish its move columns**: append 8 `.piBinding`s at
  PI 36..44 (`cFx,cFy,cTx,cTy` for `which ∈ {0,1}` — append-only, 0..35 untouched) plus 8 transport
  theorems in the exact shape of `resolve_autoX_pi_of_sat`. Then connect
  `S.pub[25+k] == R.pub[36+k]` (k<4) and `S.pub[32+k] == R.pub[40+k]` (k<4).
  New Lean lemma `seamMoves_of_pi : moveDecodeN 11 (envAt tR 0) w = revealDecode (envAt tS 0) w` —
  a verbatim clone of `seamAuto_of_pi`'s two-transports-plus-PI-equality argument.
* **S→R board seam (9 lanes).** `S.pub[16..25) == R.pub[16..25)` — the reveal opened against *this*
  old board. Free: Leg S already publishes the same pack.

Then the moves entering the fold are **committed-and-revealed**, not invented, and `who` finally
exists (Leg S's pinned `seat` lanes), which is what `hfresh`'s `seats.contains m.who` needs.

### 4.4 Two REAL blockers on Leg S, both must be fixed before it is load-bearing

1. **The commitment is ONE felt (~31 bits).** `one_felt_commitment_cardinality_window` is a
   felt-width wound of exactly the class in `docs/WOUND-felt-width-boundaries-2026-07-19.md`: a seat
   can find a second `(frm,to,seat,nonce)` opening under the same 1-felt commitment in ~2^15.5 work
   and *change its move after seeing the opponent's*. **Widen the published commitment to ≥ 4 lanes**
   (the descriptor already allocates seven Poseidon output lanes per seat — the lanes are there,
   only the publication is narrow) and widen the app-root weld to `app_root_len = 8` over two
   4-lane commitments, or move the commit pair out of the 8-lane field octet entirely.
2. **The live host seal is a truncated 63-bit BLAKE3 `u64`**, not the Poseidon2 felt Leg S opens
   (`live_host_seal_lane0_is_not_injective`). `surface.rs`'s seal must be re-pointed to the same
   Poseidon2 preimage the descriptor hashes, at the widened lane count.

Until (1) and (2) land, Leg S is **shaped** but not **sound-to-weld**, and the honest description of
a two-leg (R+A only) fold is: *"the board transition is a legal resolution of SOME valid move pair,
carried into the automaton step"* — G1 partially closed, the *provenance* of the moves still open.

### 4.5 Privacy: what a folded match leaks

The moves are never in the artifact — they are trace columns and (with Leg S) intra-recursion PIs.
The root exposes only `first.IN` and `last.OUT`, i.e. **the opening and final positions**;
intermediate boards and every move stay inside the recursion. Same honest caveat as the rest of the
stack: the STARK is *succinct*, not *hiding* — this is data-availability privacy
(`dreggnet-game-board/src/lib.rs:69-71`), not a cryptographic hiding claim.

---

## 5. THE RESOLVE WITNESS-GEN — mirror the step pattern, and scope it

### 5.1 The pattern to mirror

`dregg-automatafl/src/witness.rs` is the template: (i) load the descriptor by name, (ii) fail-closed
on any layout disagreement (`public_input_count`, `trace_width`), (iii) fill the row, (iv) assemble
PIs, (v) gate on `ir2_eval_accepts_i64` **before** the leaf is ever handed to the prover
(`step_trace_accepts`). Its tamper canary (`tampered_tail_is_rejected`) is the shape to copy.

### 5.2 Why resolve is genuinely harder than step

The step witness-gen reused the Rust `Builder` fill for columns `0..A_BACK_TAIL` byte-identically.
**That reuse does not transfer wholesale.** `AutomataflResolveEmit.lean:1-60` states that the Lean
Leg R is *not* a transcription of `emit_resolution`: it converts two compile-time bakes into
**witnessed** columns the Rust does not have (the automaton row×column one-hot, the move-direction
bit `iv`), and it appends a whole **STAGED-ADDITIVE correction chain** (`INCL`, `NL`, `RESR`, `CV2`,
`MIDV2`, `V3`, `MIDV3`, `V4`, `MIDV4`) with no Rust counterpart at all — the occlusion / 2-cycle
corrections that make `cMidV4`, not `mid`, the roundStep board.

**Design against the SHAPE-INDEPENDENT interface**, per the concurrent cutover shrinking the
descriptor (dead `cMidV2`/`cMidV3` families being removed — `AutomataflResolveMovesCapstone.lean` is
already −396 lines in the working tree):

* **Never hardcode a column index.** Add `dregg-automatafl/src/resolve_layout.rs` (NEW): a Rust
  mirror of `AutomataflResolveEmit.NGen` (`AutomataflResolveEmit.lean:1498-1726`) computing every
  family base from `n` by the **same formulas** — `KK`, `COORD_RBITS`, `AUTO_BLOCK_WIDTH`,
  `MV_BLOCK_WIDTH`, `mvBase`, `OCC_BLOCK_WIDTH`, `occBase`, `FT0`, `WR0`, `MH0`, `packOldFelt`,
  `packMidFelt`, `INCL0`, `NL0`, `RESR0`, `CV2_0`, `MIDV2_0`, `V3_0`, `MIDV3_0`, `V4_0`, `MIDV4_0`,
  `R_WIDTH`. One fail-closed assertion — `layout.width(n) == desc.trace_width` — turns the cutover
  from a silent mis-fill into a compile-time-visible `Err`.
* **Bind to the FAMILY, not the offset.** The witness-gen writes `layout.c_mid_v4(c)`, never `1445`.
  When V2/V3 are deleted the mirror shrinks and every call site is correct by construction.
* **Bind PIs to the ABI, not the number.** `pack_in = 16`, `pack_out = 16 + RFC`,
  `auto = 16 + 2*RFC` — derived, with `desc.public_input_count == 16 + 2*RFC + 2 (+ appended
  families)` checked.

### 5.3 Step 0 — the highest-leverage 10 lines in this whole document

`circuit/src/descriptor_ir2.rs:1836` `ir2_eval_accepts_i64` returns **`bool`**. Filling 1273 columns
against 1618 gates with a yes/no oracle is blind debugging. **Add
`ir2_first_failing_constraint(desc, rows, pis) -> Option<(usize, &VmConstraint2)>`** (a trivial
variant of the same loop) before writing a single column of the fill. With it, each family lands in
minutes: fill → run → "gate 1483 fails" → read the Lean gate → fix. Without it, this is the item
that eats the week.

### 5.4 Deliverables and effort

| item | file | ~lines | notes |
|---|---|---|---|
| per-gate failure reporter | `circuit/src/descriptor_ir2.rs` | 15 | do this first |
| layout mirror | `dregg-automatafl/src/resolve_layout.rs` (NEW) | 150 | pure formulas + width assert |
| front-end fill (board, auto one-hot, 2× move block, 2× occlusion block, `anz/bnz`, eq/fork/collide/`cSurv`, carries, `ft_a/ft_b`, `write_mid_witnessed`, write one-hots) | `dregg-automatafl/src/resolve_witness.rs` (NEW) | 400 | **reuse `moves.rs::emit_resolution`'s VALUE computations** (`probe_occlusion`, `chain_endpoint`, `conflict_resolve`, `occluded`) as the oracle — never its constraints |
| correction chain (`INCL`, `NL`, `RESR`, `CV4`, `MIDV4`, 2-cycle) | same | 250 | Lean-only; must be read off `AutomataflResolveEmit.lean` §2.4–2.7 gate-by-gate. Shrinks with the cutover |
| pack tail + PI assembly | same | 40 | identical to `witness.rs::pack_board` |
| tests: n=11 stock + a real legal turn; clash turn; forged-mid rejection; tamper canary; **golden-shape canary** (`desc.trace_width == layout.width(11)`) | `dregg-automatafl/src/resolve_witness.rs` tests | 150 | gate on `ir2_eval_accepts_i64`, not on proving |

**Estimate: ~1000 lines, 2–4 focused days with the reporter, indefinite without it.** Fannable as
three lanes (front-end / occlusion / correction-chain) sharing the reporter as an oracle, since each
family's gates are disjoint and row-local.

Two registration items ride along:
* `circuit/src/descriptor_by_name.rs:159-160` — add `("dregg-automatafl-resolve-n11",
  AUTOMATAFL_RESOLVE_N11_JSON)`; the golden already exists on disk and is already emitted by
  `metatheory/EmitByName.lean:113`, it is simply **not dispatchable by name** yet.
* **Measure the leaf.** 1273 cols × 1618 gates is 1.9× the step leaf and has never been proven.
  Measure a single Leg-R leaf prove (time + peak RSS) at `ir2_leaf_wrap_config` **before** designing
  the fold schedule around it; `MAX_TRACE_WIDTH = 1024` is a *DSL* cap (`circuit/src/dsl/circuit.rs:691`)
  and does not apply to the direct-IR2 path, so the gate here is cost, not admissibility.

---

## 6. THE CLASH ROUND

**Spec.** `AutomataflRules.roundStep` (`metatheory/Dregg2/Games/AutomataflRules.lean:617`): if
`clashCoords ≠ []` (or the round is unresolvable) it returns `.again` with the board **unchanged**,
the conflicted coordinates added to `marks`, the surviving moves `locked`, and the clashing seats
back in `waiting`. **No automaton step happens.**

**What is already proven.** `resolve_sat_imp_roundBoardN`
(`AutomataflResolveMovesCapstone.lean:3768`) is **unconditional** and covers both branches:
`cMidV4 = old` on a clash, `= resolveMoves old ms` otherwise. And the descriptor's `cSurv` column
(`AutomataflResolveEmit.lean:1589`) is constrained to be exactly `clashCoords = []`
(`surv_iff_clash_empty_of_sat`). So the clash/clean **verdict is already forced in-circuit** — it is
simply not published and not consumed.

### 6.1 The wrong answer: a data-dependent round shape

"Clash rounds fold one leg, clean rounds fold two" makes the **number of leaves a prover choice**.
A prover facing an unfavourable automaton step would declare a clash, emit only Leg R, and the fold
would happily accept — nothing forces the shape. It also makes the tree shape data-dependent, and
the ordered digest is shape-sensitive, so the host mirror and the streaming schedule would both
need per-match schedules. **Reject.**

### 6.2 The right answer: THE GATED STEP (uniform 2 legs, always)

Make Leg A's automaton step **conditional on a published, constrained bit**:

* Leg R appends one `.piBinding` publishing `cSurv` at **PI 44** (after §4.3's move PIs), plus a
  transport theorem `resolve_surv_pi_of_sat`.
* Leg A appends one **input** PI `surv` at **PI 38** and gates its board update:
  the automaton gadget writes an internal `stepped[c]` family (unchanged gates, renamed target),
  and the published `new` becomes the **degree-2 blend**

  ```
      new[c] − ( surv·stepped[c] + (1 − surv)·old[c] )  ==  0
  ```

  plus `gBin(surv)`. Degree-2 only: the existing automaton gates keep their current degree, so no
  degree-budget risk. `auto_out` blends the same way, on top of the mask that is already there:
  `NAX = AX + surv·M·OX` (degree 3, still inside the budget) — the clash gate multiplies the
  SAME offset term the move mask already gates, it does not replace it.
* The fold connects `R.pub[44] == A.pub[38]` — one more lane on the same seam.

**What this buys, beyond plumbing.** With the gated step, `automatonStepGated surv b = if surv then
automatonStepCfg cfg b else b`, and on a clash `roundStep`'s outcome board is `bR = cMidV4 = old =
new`. So the composition holds on **both** branches and
`turn_sat_imp_roundStep`'s `hclean` hypothesis is **discharged** — the whole-turn theorem becomes
unconditional in the clash dimension. That is a genuine proof win, not a workaround, and it is why
this is the recommended path.

Lean cost: a `stepped`-family rename + one blend gate family + `gBin` in `AutomataflStepEmit`, and
a `astep_sat_imp_automatonStepCfgN_gated` variant threading the blend through the existing proof
(the automaton half is untouched; only the final cell equality gains a two-branch case split).
Golden regen for `automatafl-step*.json`.

### 6.3 What a clash round still does NOT attest

`roundStep`'s `.again` also produces `marks`, `locked`, `waiting`. Round `k+1`'s legality is
`moveLegalB rs.board rs.marks m` with `marks ≠ []`, while the capstone's `hfresh` is stated at
`marks = []`. **The proven whole-turn statement therefore covers a turn's FIRST round only.**
Multi-round turns (any turn containing a clash) need a `marks`/`locked` carrier — appended PIs on
Legs S/R plus a `marks`-parametric `hfresh` — and are **out of scope** for the first landing. Say
this in the leaderboard copy; do not let "the clash round folds" become "multi-round turns are
attested".

---

## 7. WHAT A LIGHT CLIENT VERIFIES END-TO-END — and what remains un-attested

### 7.1 The artifact/verifier extension (required, and fail-closed by construction)

`verify_turn_chain_recursive_from_parts` compares the root's exposed claim for **exact** equality
against the carried claim (`ivc_turn_chain.rs:4442-4460`). So:

* `WholeChainProof` gains `board_window: Option<[BabyBear; 22]>`;
* the verifier appends it to `expected` when present (and refuses a 47-lane exposure with no carried
  window, and a carried window with a 25-lane exposure — both directions fail-closed);
* `AttestedHistory` (`lightclient/src/lib.rs:134`) gains `board_genesis: [BabyBear; 11]`,
  `board_final: [BabyBear; 11]`;
* `ugc_dregg::ProofAnchor` (pinned by `match_anchor`, `dreggnet-game-board/src/lib.rs:509`) gains the
  pinned genesis/final board windows, so the board operator pins *"from the stock 11×11 opening to a
  win position"*, not merely *"from cell-anchor X to cell-anchor Y"*.

### 7.2 With all of the above landed, an O(1) light-client accept means

1. K turns executed, ordered, temporally chained (today's four teeth — unchanged);
2. every RESOLVE leaf satisfied the **Lean-proven** `automataflResolveDescN 11` ⇒ its `cMidV4` IS
   `AutomataflRules.roundStep`'s resolve board for the decoded moves (`resolve_sat_imp_roundBoardN`,
   unconditional, both branches);
3. every STEP leaf satisfied the **Lean-proven** `automataflStepDescN 11` ⇒ its `new` IS the
   (gated) `automatonStepCfg ⟨.column⟩` of its old board;
4. the mid seam held ⇒ each round's composed pair IS `roundStep` (`turn_sat_imp_roundStep_pi`);
5. the board carry held ⇒ the rounds form ONE trajectory, no board substitution between rounds;
6. the trajectory **started** at the pinned genesis window and **ended** at the pinned final window;
   and since the pack is injective, a verifier can **decode the 9-felt final window into the actual
   11×11 board in the clear** and check the goal-corner win condition with no circuit at all;
7. with Leg S widened and welded: those moves were the **committed, revealed** submissions of the
   two seats — i.e. the proof covers the *players*, not just the *rules*.

### 7.3 Un-attested after all of it (state these; do not let them drift)

* **hfresh / hres.** `moveLegalB` and `resolvableB` are still spec-side hypotheses on the decoded
  moves. The circuit proves its own `MoveValid` (`validMoveN_of_sat`,
  `AutomataflResolveRefine.lean:3790`) and its own `cResolvable`, but **no `MoveValid → moveLegalB`
  bridge lemma exists** and the `cResolvable ↔ resolvableB` biconditional is explicitly noted as
  *false* in the current form (`AutomataflResolveMovesCapstone.lean:2355`). Two named Lean items;
  until they land the whole-turn theorem is conditional on them.
* **Multi-round turns** (`marks`/`locked`/`waiting` carry) — §6.3.
* **The win.** `winOnEntry` is not in any descriptor. §7.2(6) checks it *off-circuit* from the
  decoded final board, which is honest and sufficient for a leaderboard, but it is not an in-fold
  tooth.
* **Seat ↔ identity.** Leg S pins seat ∈ {0,1}; nothing binds a seat to a *player account*. The
  leaderboard's "who played" is host-attested.
* **The fixture cell.** `mint_turn` still folds automatafl legs over the `pk[0]=7` fixture
  (`fold.rs:~390`), not a real WorldCell — the `*_over_cell` twins exist for tug only. The board
  window makes the *board* real; the *cell* is still a nonce bump.
* ~~**n = 5.**~~ **CLOSED (2026-07-24): the live game moved to 11×11.** `dregg-automatafl/src/game.rs`
  now sets `N = 11`, `opening_board() = reference::stock_two_player()` and the four-corner
  `GOAL_CORNERS_2P` win check, so the PLAYED board is the emitted-descriptor board. The surface
  additionally RECORDS the move history (`AutomataflSession::rounds` / `start_board`), so
  `crown.rs::played_automatafl` folds `AutomataflMatch::played(start, rounds)` — the two-leg chain
  that attests the players' moves — instead of `automaton_only`, which attests none. Gate:
  `dreggnet-game-board/tests/played_surface_folds.rs` (a round played on the real offering lowers to
  both n=11 descriptors, traces accept, mid seam holds) and
  `game.rs::the_played_board_size_has_both_emitted_lean_descriptors`.
  The n=5 route stays **blocked-not-faked** for any caller that still hands one in
  (`matches.rs::n5_has_no_descriptor_blocked_not_faked`).
  RESIDUAL: only CLEAN rounds fold. A round the seats clashed on is played and recorded but REFUSED
  by name (`MatchError::ConflictingRound`) — the surface drops clashing moves while the ruleset
  marks the square and re-enters the round (Leg C, §6.3), and a descriptor/oracle mid disagreement
  (the occupancy-blind 2-cycle detector) is refused as `MatchError::MidDiverges`.
* **The floors.** Everything above sits on the deployed FRI posture
  (`docs/`/memory: 57 calculator bits, `project-fri-soundness-reality`) and on the
  witness-generation perimeter (`project-witness-gen-assurance-perimeter`) — the STARK proves the
  TRACE, and the Rust trace generator is TRUSTED. The pack seam is deliberately hash-free, which
  removes Poseidon2 from *this* seam but changes nothing about those two floors.

---

## 8. THE ORDERED BUILD PLAN

Each phase is independently landable and independently *meaningful*. Phases 1–3 need no Lean change.

| # | phase | touches | gate that proves it landed |
|---|---|---|---|
| **0** | `ir2_first_failing_constraint` reporter | `circuit/src/descriptor_ir2.rs` | a deliberately corrupted step row reports the exact failing gate index |
| **1** | register `dregg-automatafl-resolve-n11` by name | `circuit/src/descriptor_by_name.rs` | `descriptor_by_name(...)` returns 1273 w / 36 PIs |
| **2** | `resolve_layout.rs` mirror + width assertion | NEW | `layout.width(11) == desc.trace_width`; survives the V2/V3 cutover with a one-line edit |
| **3** | **`resolve_witness.rs`** — the Leg-R witness-gen (§5) | NEW | honest 11×11 turn (`prove_11x11.rs::turn()`) satisfies the descriptor under `ir2_eval_accepts_i64`; a forged mid does not; tamper canary red |
| **4** | measure ONE Leg-R leaf prove | test, `#[ignore]` | wall-clock + peak RSS recorded; fold schedule sized from it |
| **5** | slice-list leaf exposure + board-window binding node (§2.4a,b) | `custom_leaf_adapter.rs`, `joint_turn_recursive.rs` | leaf exposes 46 lanes; node re-exposes 47; a 24-lane leaf is REFUSED, not degraded |
| **6** | `SegmentCombine` parameterization + host board-window mirror (§2.4c) | `ivc_turn_chain.rs`, `merge_pool.rs` | `Plain` root is **byte-identical** to today for tug; host mirror rejects a bad mid in ms |
| **7** | verifier + artifact + anchor extension (§7.1) | `ivc_turn_chain.rs`, `lightclient`, `ugc-dregg` | a 47-lane root with no carried window is REFUSED; a carried window with a 25-lane root is REFUSED |
| **8** | **the two-leg match**: `AutomataflMatch { start, rounds: Vec<(Move,Move)> }` emitting R,A per round | `dreggnet-game-board/src/lib.rs` | **THE HARD GATE:** honest match folds + `verify_history` ACCEPTS; **`mismatched_mid_fold_probe_11x11` now REJECTS** (the test that today records the hole becomes the test that proves it closed) |
| **9** | Leg A `NAX/NAY` PIs + transports (§2.5) | Lean + golden regen | inter-round carry connects; a substituted board between rounds is UNSAT |
| **10** | **gated step** + `cSurv` PI (§6.2) | Lean + golden regen | a clash round folds as 2 legs with `new == old`; `hclean` discharged in `turn_sat_imp_roundStep` |
| **11** | Leg R move PIs + `seamMoves_of_pi` (§4.3) | Lean + golden regen | R's decoded moves == S's opened moves, in-fold |
| **12** | **widen the reveal commitment to ≥4 lanes + re-point the host seal** (§4.4) | Lean + `surface.rs` | `one_felt_commitment_cardinality_window` / `live_host_seal_lane0_is_not_injective` retired, not narrated |
| **13** | fold Leg S; register + witness-gen it | Lean + NEW Rust | the match proof covers the **committed** moves |
| **14** | `MoveValid → moveLegalB` and a sound `cResolvable` bridge | Lean | `hfresh`/`hres` discharged from the descriptor, not assumed |
| **15** | multi-round turns: `marks`/`locked` carrier | Lean + fold | a turn containing a clash is attested end-to-end |

**The one-line summary of the plan:** phases 0–8 make the match proof cover *the rules* (legal
resolution ∘ automaton step, chained into a real trajectory with pinned endpoints); phases 9–13 make
it cover *the players*; phases 14–15 discharge the remaining spec-side hypotheses.

**Phase 8 is the milestone worth naming publicly**, and its acceptance criterion is a *sign flip on
an existing test*, not a new green: `mismatched_mid_fold_probe_11x11` today exists to record that
the fold accepts a forged mid. When it rejects, the seam is real.
