/-
# Dregg2.Bridge.MinaCheckpoint — **the per-CHECKPOINT Mina verification loop.**

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. It is a DECISION FUNCTION over
already-decoded consensus states — the same substrate as `MinaForkChoiceGate`, `@[export]`ed over
the C ABI. Rust hex-encodes bytes and stores what came back.

## The insight this file is built on, and how it resizes the problem

**Mina's Pickles proof is recursive: block N's Step proof verifies block N−1's Wrap proof.**
Verifying ONE block's Wrap proof therefore attests the VALIDITY of the whole chain behind it —
every transition, every in-circuit density update, every leader-election check, back to genesis.

So a client does not need a per-block Wrap verification at Mina's 180 s block cadence. It needs a
**per-CHECKPOINT** verification at whatever cadence it chooses, and the cost of a longer cadence is
**latency and liveness — not safety**, provided one thing holds: *nothing that a longer cadence
leaves unverified is ever allowed to move the ratchet.* That proviso is this file's whole content.

## The two tiers, and why the split is the safety argument

| tier | runs | checks | may move |
|---|---|---|---|
| **PROVISIONAL** | every block (~180 s) | binprot decode + canonicality, carried-constants pin, `previous_state_hash` link, the density window RE-DERIVED from the parent, `select` | the `tip` only |
| **CHECKPOINT** | every `C` blocks | all of the above **plus the Wrap proof's arithmetic** | the `verified` head, and therefore `finalized` |

`provisional_never_ratchets` is the theorem that makes the split safe: a provisional step is
*definitionally* unable to raise `finalized`. Combined with `MinaChainSelection.beats_not_transitive`
— `select` has genuine 3-cycles at real mainnet constants — this says the tournament's cycles are
CONTAINED to a tier that decides nothing. A peer that controls presentation order can walk the tip
around a cycle all day (`head_can_be_walked_in_a_cycle`) and the finalized point does not move.

## ⚑ What the recursion buys, and what it does NOT — because the difference is the design

**Buys:** chain VALIDITY, transitively. A checkpoint every 20 blocks verifies those 20 blocks and
everything before them, at the cost of one verification. In particular it buys the **density window**
— `min_window_density` is updated in-circuit by the blockchain SNARK's transition function, so a
verified tip's density is a verified density, all the way back. That is why a checkpoint does **not**
need consecutive headers.

**Does not buy:** WHICH chain. Every valid fork — including a long private low-density one — has a
valid Pickles proof. Choosing between them is Samasika `select`, which is not in the SNARK. And
`select` is only meaningful when *both* tips are valid, so **the checkpoint cadence is exactly the
cadence at which fork choice is meaningful at all.** Between checkpoints the tip is a guess.

**The interaction the two facts produce** — and it inverts the obvious worry that "a checkpoint every
20 blocks does not give you consecutive-header density":

  * At a **checkpoint** the density needs no consecutive headers, because the proof covers it.
  * **Between** checkpoints there is no proof, so the density must come from somewhere else — and
    `MinaSlidingWindow.step` recomputes it from the PARENT, which is exactly a two-consecutive-header
    check. `densityFollowsParent` below is that check, and it is why the provisional tier consumes
    a parent rather than a lone tip.

So the cheap check and the expensive check discharge the SAME obligation by different means. The
cheap one runs continuously; the expensive one re-anchors and does not need the cheap one's history.
`docs/MINA-LIGHT-CLIENT.md` row 7 carried "checkable from two consecutive headers and nothing else …
the head currently consumes a *served* window and bound-checks it rather than re-deriving it from the
parent" as an open row. This closes it for the provisional tier.

## ⚑ What stays TRUSTED at every cadence — naming it, because a cadence table hides nothing

1. **The Wrap verifier index** (`MinaWrapIndexParams::DEVNET_BLOCKCHAIN`, the 56 `VK_INDEX`
   elements). The largest trusted object under the whole proof story. Nothing derives it from the
   chain; P8/P9 is not started. A wrong VK makes every checkpoint a verification of the wrong claim.
2. **`state_hash` is not re-derived anywhere.** `hash`/`ch` on this wire are SUPPLIED by the peer's
   framing. `previous_state_hash` IS decoded and IS a real parent link, so a *run* is checkable; a
   tip's own identity is not.
3. **Leader election is not checkable by any verifier.** `vrf_output` needs the delegator's secret
   scalar; Mina ships no standalone VRF verifier. A client that verifies the Pickles proof
   INHERITS the threshold check — which is how Mina itself works, and is not a defect of this design.
4. **The SRS** — that `srs.g` and `srs.h` are what they claim.
5. **The byte source**, for availability only. Withholding is not defensible by any light client.

## Fail closed

`checkpointRoll` takes the Wrap verdict as a required conjunct. An unavailable prover, an absent
archive and a refused proof all supply `false`, and `checkpoint_without_the_wrap_verdict_moves_nothing`
proves that is a no-op. There is no `allow_unverified`, no stale-checkpoint grace, and no arm where a
long run without a checkpoint starts deciding on its own: past `runCap` the provisional tier itself
REFUSES (`a_stale_run_refuses_to_move_the_tip`), converting a liveness failure into a refusal rather
than into a silently-unverified head.

NOT imported by the `Dregg2` root; rooted in `Dregg2/FFI.lean` so the `@[export]` reaches an archive.
⚑ That distinction is layer 1 of `Dregg2/FFI.lean` §4 and it is why five Mina gates were dark.
-/
import Dregg2.Bridge.MinaForkChoiceGate
import Dregg2.Bridge.MinaSlidingWindow

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaCheckpoint

open Dregg2.Bridge.MinaChainSelection
open Dregg2.Bridge.MinaForkChoiceGate

/-! ## §1 — The density window, RE-DERIVED from the parent.

This is the between-checkpoint substitute for the blockchain SNARK. `MinaSlidingWindow` replayed
849 real consecutive canonical devnet transitions from one seed and the slot sequence alone with
zero mismatches, so the function is reality-gated; what was missing was a caller. -/

/-- The three window fields of a consensus state, as `MinaSlidingWindow` wants them. -/
def windowOf (c : ConsensusState) : MinaSlidingWindow.WindowState :=
  { slot := c.currGlobalSlot
    minWindowDensity := c.minWindowDensity
    subWindowDensities := c.subWindowDensities }

/-- **`densityFollowsParent`** — the child's SERVED window is exactly what
`update_min_window_density` produces from the PARENT's window at the child's slot.

⚑ This is strictly stronger than the bound check `MinaBinprot.decodeProtocolStateChecked` applies
(`every density ≤ slots_per_sub_window`, `min_window_density ≤ slots_per_window`). A bound check
admits any well-sized fabrication; this admits exactly one value. The strict slot increase is part
of it: `MinaSlidingWindow` proves `step` yields a degenerate 8 at mainnet constants absent it. -/
def densityFollowsParent (C : Constants) (parent child : ConsensusState) : Bool :=
  let w := MinaSlidingWindow.step C (windowOf parent) child.currGlobalSlot
  decide (parent.currGlobalSlot < child.currGlobalSlot)
    && w.minWindowDensity == child.minWindowDensity
    && w.subWindowDensities == child.subWindowDensities

/-- **`linkedToParent`** — the child names the parent, over DECODED field elements, plus the height
step. `previous_state_hash` is the one genuine link a served header carries. -/
def linkedToParent (parentHash : Nat) (parent child : ConsensusState)
    (childPrevHash : Nat) : Bool :=
  childPrevHash == parentHash && child.blockchainLength == parent.blockchainLength + 1

/-- **`cheapOk`** — the whole PROVISIONAL-tier verdict on one candidate, given its parent.

Everything here is a decode, a comparison or a `Nat` fold: no group element is touched, no sponge
is run. This is what a client can afford every 180 s. -/
def cheapOk (C : Constants) (parentHash : Nat) (parent child : ConsensusState)
    (childPrevHash : Nat) : Bool :=
  linkedToParent parentHash parent child childPrevHash && densityFollowsParent C parent child

/-! ## §2 — THE TWO-TIER HEAD. -/

/-- The client's persisted state.

`verified` is the last CHECKPOINT — a tip whose Wrap proof was actually verified — and its
`finalized` field is the ONLY ratchet in this file. `tipCs`/`tipHash` are the PROVISIONAL head: what
the client currently believes on cheap checks alone. `run` counts blocks since the last checkpoint
and is what turns a stalled checkpoint into a refusal instead of an ever-longer unverified prefix. -/
structure CheckpointHead where
  /-- The last VERIFIED checkpoint, carrying the ratchet. -/
  verified : Head
  /-- The provisional tip's consensus state. Decides NOTHING. -/
  tipCs : ConsensusState
  /-- The provisional tip's state hash (SUPPLIED — `state_hash` is re-derived nowhere). -/
  tipHash : Nat
  /-- Blocks accepted onto the tip since the last checkpoint. -/
  run : Nat
deriving Repr, DecidableEq

/-- **`provisionalRoll`** — one block, cheap tier. The tip moves iff the candidate passes the cheap
checks, is inside the run cap, and WINS `select` against the current tip.

⚑ PAIRWISE, against the CURRENT tip. Never a fold, never a `max_by`: `beats_not_transitive` proves
`select` has real 3-cycles, so "the best of a set" is not a function of the set. -/
def provisionalRoll (runCap : Nat) (h : CheckpointHead) (ok : Bool)
    (c : ConsensusState) (ch : Nat) : CheckpointHead :=
  if ok && decide (h.run < runCap) && minaBetterTip mainnet h.tipCs c h.tipHash ch then
    { h with tipCs := c, tipHash := ch, run := h.run + 1 }
  else h

/-- **`checkpointRoll`** — the expensive tier. `wrapOk` is the per-block Wrap ARITHMETIC verdict
(`Dregg2.Bridge.MinaWrapChallenges` derives the challenges; the opening relation and the `⟨s,srs.g⟩`
leg close it). It is a required conjunct, and an unavailable prover supplies `false`.

The verified head rolls through `MinaForkChoiceGate.rollHead`, so the ratchet is the one
`rollHead_finalized_monotone` is about — there is no second ratchet in this tree. On an advance the
tip RE-ANCHORS to the checkpoint and the run resets: a verified checkpoint discards a provisional
guess rather than being reconciled with it. -/
def checkpointRoll (h : CheckpointHead) (wrapOk ok : Bool)
    (c : ConsensusState) (ch : Nat) : CheckpointHead :=
  if headAdvance (wrapOk && ok) h.verified c ch then
    { verified := rollHead h.verified (wrapOk && ok) c ch, tipCs := c, tipHash := ch, run := 0 }
  else h

/-! ## §3 — WHAT THE SPLIT GUARANTEES. -/

/-- ⚑⚑ **THE PAYOFF, and the whole reason a longer cadence is safe.** A provisional step cannot
touch the verified head — not "does not in practice", but definitionally: `verified` is not in the
updated record. Every block between checkpoints is therefore free of safety consequence. -/
theorem provisional_never_ratchets (runCap : Nat) (h : CheckpointHead) (ok : Bool)
    (c : ConsensusState) (ch : Nat) :
    (provisionalRoll runCap h ok c ch).verified = h.verified := by
  unfold provisionalRoll; split <;> rfl

/-- …and in particular the finalized height is untouched by any provisional run, of any length,
under any presentation order. -/
theorem provisional_never_finalizes (runCap : Nat) (h : CheckpointHead) (ok : Bool)
    (c : ConsensusState) (ch : Nat) :
    (provisionalRoll runCap h ok c ch).verified.finalized = h.verified.finalized := by
  rw [provisional_never_ratchets]

/-- **THE RATCHET SURVIVES THE SPLIT.** A checkpoint never lowers the finalized height, on any
input. Inherited from `rollHead_finalized_monotone` rather than re-proved: there is one ratchet. -/
theorem checkpointRoll_finalized_monotone (h : CheckpointHead) (wrapOk ok : Bool)
    (c : ConsensusState) (ch : Nat) :
    h.verified.finalized ≤ (checkpointRoll h wrapOk ok c ch).verified.finalized := by
  unfold checkpointRoll
  split
  · exact rollHead_finalized_monotone h.verified (wrapOk && ok) c ch
  · exact Nat.le_refl _

/-- ⚑ **FAIL CLOSED ON THE WRAP VERDICT.** An unverified — or unverifiable — Wrap proof moves
NOTHING, including the tip. This is the arm that a "the prover was busy, carry on" fallback would
open, and there is no such arm. -/
theorem checkpoint_without_the_wrap_verdict_moves_nothing (h : CheckpointHead) (ok : Bool)
    (c : ConsensusState) (ch : Nat) :
    checkpointRoll h false ok c ch = h := by
  simp [checkpointRoll, headAdvance]

/-- …and symmetrically, a Wrap proof that verifies over a candidate that failed the CHEAP checks —
a broken parent link, a fabricated density — also moves nothing. Both conjuncts are load-bearing. -/
theorem checkpoint_without_the_cheap_checks_moves_nothing (h : CheckpointHead) (wrapOk : Bool)
    (c : ConsensusState) (ch : Nat) :
    checkpointRoll h wrapOk false c ch = h := by
  simp [checkpointRoll, headAdvance]

/-- ⚑ **A STALLED CHECKPOINT BECOMES A REFUSAL, NOT A LONGER GUESS.** Once `run` reaches the cap
the provisional tier stops moving the tip. A peer that withholds checkpoint evidence cannot walk the
client arbitrarily far on cheap checks alone; it can only stall it, which is the failure mode no
light client can be defended against. -/
theorem a_stale_run_refuses_to_move_the_tip (runCap : Nat) (h : CheckpointHead) (ok : Bool)
    (c : ConsensusState) (ch : Nat) (hstale : runCap ≤ h.run) :
    provisionalRoll runCap h ok c ch = h := by
  have hd : decide (h.run < runCap) = false := decide_eq_false (Nat.not_lt.mpr hstale)
  unfold provisionalRoll
  rw [hd]
  simp

/-- **NO SELF-CHURN.** Re-presenting the tip's own state does not move it, so a peer cannot inflate
`run` by replay. Rests on `select_irrefl` through `minaBetterTip_decides`. -/
theorem provisional_refuses_the_tip_itself (runCap : Nat) (h : CheckpointHead) (ok : Bool) :
    provisionalRoll runCap h ok h.tipCs h.tipHash = h := by
  simp [provisionalRoll, (minaBetterTip_decides mainnet h.tipCs h.tipCs h.tipHash h.tipHash).2]

/-- **A CHECKPOINT RE-ANCHORS.** When the verified head advances, the tip becomes the checkpoint and
the run resets — the provisional guess is DISCARDED, never merged. A design that reconciled the two
would let an unverified prefix survive a verification that did not cover it. -/
theorem an_advancing_checkpoint_reanchors_the_tip (h : CheckpointHead) (wrapOk ok : Bool)
    (c : ConsensusState) (ch : Nat)
    (hadv : headAdvance (wrapOk && ok) h.verified c ch = true) :
    (checkpointRoll h wrapOk ok c ch).tipCs = c
    ∧ (checkpointRoll h wrapOk ok c ch).tipHash = ch
    ∧ (checkpointRoll h wrapOk ok c ch).run = 0 := by
  unfold checkpointRoll; rw [if_pos hadv]; exact ⟨rfl, rfl, rfl⟩

/-! ### §3b — the ratchet over a SEQUENCE, which is the property a running client has.

A single-step monotonicity theorem says nothing about an adversary who interleaves. These fold the
two rolls over an arbitrary presentation and show the finalized height still never decreases. -/

/-- One step of a client's life: either tier, chosen by the caller (i.e. by the network). -/
inductive Step where
  /-- A cheap block: `(ok, candidate, hash)`. -/
  | prov : Bool → ConsensusState → Nat → Step
  /-- A checkpoint: `(wrapOk, ok, candidate, hash)`. -/
  | ckpt : Bool → Bool → ConsensusState → Nat → Step

/-- Run a presentation. -/
def runSteps (runCap : Nat) : CheckpointHead → List Step → CheckpointHead
  | h, [] => h
  | h, Step.prov ok c ch :: rest => runSteps runCap (provisionalRoll runCap h ok c ch) rest
  | h, Step.ckpt w ok c ch :: rest => runSteps runCap (checkpointRoll h w ok c ch) rest

/-- ⚑⚑ **THE RATCHET UNDER ANY INTERLEAVING.** For every presentation of provisional blocks and
checkpoints, in any order, of any length, the finalized height never decreases. This is the property
a light client actually needs and the one that survives `select` not being an order. -/
theorem runSteps_finalized_monotone (runCap : Nat) :
    ∀ (steps : List Step) (h : CheckpointHead),
      h.verified.finalized ≤ (runSteps runCap h steps).verified.finalized := by
  intro steps
  induction steps with
  | nil => intro h; exact Nat.le_refl _
  | cons s rest ih =>
    intro h
    cases s with
    | prov ok c ch =>
      have := ih (provisionalRoll runCap h ok c ch)
      rw [provisional_never_finalizes] at this
      exact this
    | ckpt w ok c ch =>
      exact Nat.le_trans (checkpointRoll_finalized_monotone h w ok c ch)
        (ih (checkpointRoll h w ok c ch))

/-- A run of PROVISIONAL steps only. -/
def runProvisional (runCap : Nat) :
    CheckpointHead → List (Bool × ConsensusState × Nat) → CheckpointHead
  | h, [] => h
  | h, (ok, c, ch) :: rest => runProvisional runCap (provisionalRoll runCap h ok c ch) rest

/-- ⚑ **A RUN WITH NO CHECKPOINT FINALIZES NOTHING.** However long the cheap tier runs, and whatever
the peer presents, the verified head — and therefore the finalized height — is exactly where it
started. The cost of a longer cadence is therefore *latency*, in the precise sense that the ratchet
WAITS, not that it moves on weaker evidence. -/
theorem a_checkpointless_run_finalizes_nothing (runCap : Nat) :
    ∀ (steps : List (Bool × ConsensusState × Nat)) (h : CheckpointHead),
      (runProvisional runCap h steps).verified = h.verified := by
  intro steps
  induction steps with
  | nil => intro h; rfl
  | cons s rest ih =>
    intro h
    obtain ⟨ok, c, ch⟩ := s
    show (runProvisional runCap (provisionalRoll runCap h ok c ch) rest).verified = h.verified
    rw [ih, provisional_never_ratchets]

/-! ## §4 — NON-VACUITY. The decisions DISCRIMINATE, kernel-clean.

Without these the theorems above are compatible with a function that never advances anything. -/

/-- A parent at slot 7212 with a real-looking window, and the child the daemon's own update
function produces one slot later. Built by RUNNING `step`, so the accept is not a transcription. -/
def parentCS : ConsensusState :=
  mkCS 1000 50 [6,5,5,5,5,5,5,6,6,6,7] [] 7212 7140 1044 0

/-- The genuine child: `blockchain_length + 1`, slot + 1, window = `step parentWindow`. -/
def childCS : ConsensusState :=
  let w := MinaSlidingWindow.step mainnet (windowOf parentCS) 7213
  { parentCS with
      blockchainLength := 1001, currGlobalSlot := 7213,
      minWindowDensity := w.minWindowDensity, subWindowDensities := w.subWindowDensities }

/-- ⚑ **THE DENSITY CHECK IS NOT A BOUND CHECK.** It accepts the genuine child and REFUSES a child
whose `min_window_density` is inflated by one — a value that passes every bound
`decodeProtocolStateChecked` applies. This is the difference between "a well-sized fabrication" and
"the one value the rule produces". -/
theorem density_admits_exactly_the_step :
    densityFollowsParent mainnet parentCS childCS = true
    ∧ densityFollowsParent mainnet parentCS
        { childCS with minWindowDensity := childCS.minWindowDensity + 1 } = false
    ∧ densityFollowsParent mainnet parentCS
        { childCS with subWindowDensities :=
            childCS.subWindowDensities.set 0 (childCS.subWindowDensities.getD 0 0 + 1) } = false
    -- …and a child that does not advance the slot is refused, which is the conjunct without which
    -- `step` degenerates (`MinaSlidingWindow` proves it yields 8 at mainnet constants).
    ∧ densityFollowsParent mainnet parentCS { childCS with currGlobalSlot := 7212 } = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The parent link discriminates: the right hash and height pass, a foreign hash and a skipped
height do not. -/
theorem link_discriminates :
    linkedToParent 777 parentCS childCS 777 = true
    ∧ linkedToParent 777 parentCS childCS 778 = false
    ∧ linkedToParent 777 parentCS { childCS with blockchainLength := 1002 } 777 = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- A head to drive the rolls with. -/
def h0 : CheckpointHead :=
  { verified := { cs := parentCS, hash := 777, finalized := 710 }
    tipCs := parentCS, tipHash := 777, run := 0 }

/-- ⚑ **BOTH TIERS ACTUALLY MOVE**, and they move DIFFERENT things. Without this the fail-closed
theorems above are satisfied by a function that refuses everything — the vacuity this repo keeps
finding. -/
theorem both_tiers_discriminate :
    -- the cheap tier moves the tip …
    (provisionalRoll 32 h0 true childCS 888).tipHash = 888
    -- … and leaves the ratchet exactly where it was
    ∧ (provisionalRoll 32 h0 true childCS 888).verified.finalized = 710
    -- a checkpoint moves the ratchet to `blockchain_length − k` = 1001 − 290
    ∧ (checkpointRoll h0 true true childCS 888).verified.finalized = 711
    -- … and re-anchors the tip
    ∧ (checkpointRoll h0 true true childCS 888).tipHash = 888
    -- an unverified checkpoint moves nothing at all
    ∧ checkpointRoll h0 false true childCS 888 = h0
    -- and a stale run refuses even the cheap move
    ∧ provisionalRoll 0 h0 true childCS 888 = h0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §5 — THE WIRE + `@[export]`.

```text
INPUT  := "md=" ("p"|"c") ";wk=" BIT ";fz=" Nat ";rn=" Nat ";rc=" Nat
          ";ph=" Nat ";th=" Nat ";vh=" Nat ";ch=" Nat
          ";p=" HEX ";t=" HEX ";v=" HEX ";c=" HEX
OUTPUT := "mv=" BIT ";adv=" BIT ";fin=" Nat ";rn=" Nat   |   "ERR"
```

  * `md` — which tier this call is: `p` provisional, `c` checkpoint.
  * `wk` — the Wrap ARITHMETIC verdict. Ignored on a provisional call; required on a checkpoint.
  * `fz` / `rn` / `rc` — the persisted finalized height, the run counter, the run cap.
  * `ph` / `th` / `vh` / `ch` — the state hashes of the candidate's PARENT, the tip, the verified
    checkpoint and the CANDIDATE. ⚑ SUPPLIED, and this is the one carrier on this wire: `state_hash`
    is re-derived nowhere in this tree (`docs/MINA-LIGHT-CLIENT.md` row 12).
  * `p` / `t` / `v` / `c` — the four binprot `Protocol_state.Value` prefixes, hex. A trailing
    remainder is fine; the decoder is a prefix decode and says how much it used.

Every side goes through `decodeProtocolStateChecked`, so carried constants that disagree with the
pin, an out-of-bounds density, a non-canonical field element or a wrong sub-window count are `"ERR"`
here and never reach a rule. `"ERR"` is a REFUSAL and every caller treats it as one. -/

/-- The four decoded sides plus their supplied hashes. -/
structure Sides where
  /-- The candidate's parent. -/
  parent : MinaBinprot.ProtocolState
  /-- The provisional tip. -/
  tip : MinaBinprot.ProtocolState
  /-- The last verified checkpoint. -/
  ver : MinaBinprot.ProtocolState
  /-- The candidate. -/
  cand : MinaBinprot.ProtocolState
  /-- `parent`'s supplied state hash. -/
  ph : Nat
  /-- `tip`'s supplied state hash. -/
  th : Nat
  /-- `ver`'s supplied state hash. -/
  vh : Nat
  /-- `cand`'s supplied state hash. -/
  ch : Nat

/-- Decode the eight tail fields. Strict: a missing key, a key in the wrong position, an odd-length
hex string or a byte string that is not a protocol state is `none`. -/
def decodeSides (parts : List String) : Option Sides :=
  match parts with
  | [a, b, c, d, e, f, g, i] =>
      match (parseField? "ph" a).bind String.toNat?,
            (parseField? "th" b).bind String.toNat?,
            (parseField? "vh" c).bind String.toNat?,
            (parseField? "ch" d).bind String.toNat?,
            (parseField? "p" e).bind decodeSide?,
            (parseField? "t" f).bind decodeSide?,
            (parseField? "v" g).bind decodeSide?,
            (parseField? "c" i).bind decodeSide? with
      | some ph, some th, some vh, some ch, some p, some t, some v, some cd =>
          some { parent := p, tip := t, ver := v, cand := cd, ph, th, vh, ch }
      | _, _, _, _, _, _, _, _ => none
  | _ => none

/-- A fully parsed wire. ⚑ `checkpoint` is a `Bool`, not the raw `"p"`/`"c"` string: the DECISION
below must never match on a string, so the mode's refusal happens once, in [`parseMode?`], and the
rendering is a plain `if`. -/
structure CheckpointWire where
  /-- `true` = a CHECKPOINT call, `false` = provisional. -/
  checkpoint : Bool
  /-- The Wrap ARITHMETIC verdict. Read only on a checkpoint call. -/
  wrapOk : Bool
  /-- The persisted finalized height. -/
  finalized : Nat
  /-- The persisted provisional run. -/
  run : Nat
  /-- The run cap. -/
  runCap : Nat
  /-- The four decoded sides. -/
  sides : Sides

/-- `md` — the ONLY place a mode string is interpreted. Anything but `"p"`/`"c"` is a refusal. -/
def parseMode? (s : String) : Option Bool :=
  if s == "p" then some false else if s == "c" then some true else none

/-- **`parseCheckpointWire`** — the WHOLE parse, as ONE function of the split parts.

⚑ Factored out deliberately, and the reason is a proof obligation rather than taste: a gate whose
body matches on the parts and then again on six parsed fields cannot be welded to its decision in one
rewrite — the outer matcher does not iota-reduce and the inner scrutinees stay buried. One scrutinee,
one rewrite, is the shape `MinaForkChoiceGate.minaBetterTipGate_eq_decision` uses and it is the shape
that makes `checkpointGate_renders_the_roll` a two-line proof instead of a `sorry`. -/
def parseCheckpointWire (parts : List String) : Option CheckpointWire :=
  match parts with
  | m :: w :: z :: n :: r :: rest =>
      match (parseField? "md" m).bind parseMode?,
            (parseField? "wk" w).bind parseBit?,
            (parseField? "fz" z).bind String.toNat?,
            (parseField? "rn" n).bind String.toNat?,
            (parseField? "rc" r).bind String.toNat?,
            decodeSides rest with
      | some md, some wk, some fz, some rn, some rc, some S =>
          some { checkpoint := md, wrapOk := wk, finalized := fz, run := rn, runCap := rc,
                 sides := S }
      | _, _, _, _, _, _ => none
  | _ => none

/-- The persisted head the wire describes. -/
def headOf (W : CheckpointWire) : CheckpointHead :=
  { verified := { cs := W.sides.ver.consensus, hash := W.sides.vh, finalized := W.finalized }
    tipCs := W.sides.tip.consensus, tipHash := W.sides.th, run := W.run }

/-- ⚑ **THE CHEAP VERDICT, COMPUTED HERE** — from the decoded parent, the decoded candidate and the
candidate's own `previous_state_hash`. Rust supplies no `ok` bit: a bit Rust computed and handed over
would be a carrier for a decision, and this is where the decision lives. -/
def okOf (W : CheckpointWire) : Bool :=
  cheapOk mainnet W.sides.ph W.sides.parent.consensus W.sides.cand.consensus
    W.sides.cand.previousStateHash

/-- Render one roll: what moved, what advanced, the new ratchet and the new run. -/
def renderStep (h h' : CheckpointHead) : String :=
  "mv=" ++ (if h'.tipHash == h.tipHash && h'.tipCs == h.tipCs then "0" else "1")
    ++ ";adv=" ++ (if h'.verified == h.verified then "0" else "1")
    ++ ";fin=" ++ toString h'.verified.finalized ++ ";rn=" ++ toString h'.run

/-- **`renderRoll`** — the decision on a parsed wire. Nothing else in this file decides. -/
def renderRoll (W : CheckpointWire) : String :=
  let h := headOf W
  let ok := okOf W
  let h' := if W.checkpoint then checkpointRoll h W.wrapOk ok W.sides.cand.consensus W.sides.ch
            else provisionalRoll W.runCap h ok W.sides.cand.consensus W.sides.ch
  renderStep h h'

/-- **`minaCheckpointGate`** — THE GATE. One scrutinee; every refusal is inside the parse. -/
def minaCheckpointGate (s : String) : String :=
  match parseCheckpointWire (s.splitOn ";") with
  | some W => renderRoll W
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_checkpoint_advance]` — the C-ABI entry `dregg-lean-ffi`
splices. Rust hex-encodes four protocol states and a Wrap verdict; the ARCHIVE decides. -/
@[export dregg_mina_checkpoint_advance]
def dregg_mina_checkpoint_advance (s : String) : String := minaCheckpointGate s

/-- **The gate string IS `renderRoll` of the parse** — the string layer adds no arm.

Stated the way `MinaForkChoiceGate.minaBetterTipGate_eq_decision` is: hypothesise the PARSE and
conclude about the DECISION, rather than trying to reduce 6 KB of hex in a proof term. -/
theorem checkpointGate_renders_the_roll (s : String) (W : CheckpointWire)
    (hp : parseCheckpointWire (s.splitOn ";") = some W) :
    minaCheckpointGate s = renderRoll W := by
  unfold minaCheckpointGate
  rw [hp]

/-- …and `renderRoll` IS the roll: `checkpointRoll` on a checkpoint call, `provisionalRoll`
otherwise, over the head the wire describes and the cheap verdict the gate itself computed.

Chained with the theorem above, this says the exported symbol renders `provisionalRoll` /
`checkpointRoll` and nothing else — so every property §3 states about those two functions is a
property of the thing Rust actually calls. -/
theorem renderRoll_is_the_roll (W : CheckpointWire) :
    renderRoll W = renderStep (headOf W)
      (if W.checkpoint then
         checkpointRoll (headOf W) W.wrapOk (okOf W) W.sides.cand.consensus W.sides.ch
       else
         provisionalRoll W.runCap (headOf W) (okOf W) W.sides.cand.consensus W.sides.ch) := rfl

/-- ⚑ **THE MODE IS THE ONLY THING THAT SELECTS A TIER**, and it is a `Bool` by the time the
decision sees it — so no string comparison sits between the wire and the roll. -/
theorem the_mode_selects_the_tier (W : CheckpointWire) :
    (W.checkpoint = false → renderRoll W = renderStep (headOf W)
        (provisionalRoll W.runCap (headOf W) (okOf W) W.sides.cand.consensus W.sides.ch))
    ∧ (W.checkpoint = true → renderRoll W = renderStep (headOf W)
        (checkpointRoll (headOf W) W.wrapOk (okOf W) W.sides.cand.consensus W.sides.ch)) := by
  constructor <;> intro h <;> rw [renderRoll_is_the_roll, h] <;> rfl

/-- `parseMode?` refuses anything but the two modes — the refusal that used to be a `!=` chain
inside the decision. -/
theorem parseMode_refuses_everything_else :
    parseMode? "p" = some false ∧ parseMode? "c" = some true
    ∧ parseMode? "x" = none ∧ parseMode? "" = none ∧ parseMode? "P" = none := by
  decide

/-! ### §5b — the wire REFUSES.

A malformed wire, a bad mode byte, an odd-length hex string and a byte string that is not a protocol
state are all `"ERR"` — a refusal, never a verdict computed from what did arrive. -/

#guard minaCheckpointGate "" == "ERR"
#guard minaCheckpointGate "garbage" == "ERR"
#guard minaCheckpointGate "md=x;wk=1;fz=0;rn=0;rc=32;ph=1;th=2;vh=3;ch=4;p=00;t=00;v=00;c=00"
       == "ERR"
#guard minaCheckpointGate "md=p;wk=2;fz=0;rn=0;rc=32;ph=1;th=2;vh=3;ch=4;p=00;t=00;v=00;c=00"
       == "ERR"
-- an odd-length hex string is a refusal, not a dropped nibble
#guard minaCheckpointGate "md=p;wk=1;fz=0;rn=0;rc=32;ph=1;th=2;vh=3;ch=4;p=0;t=00;v=00;c=00"
       == "ERR"
-- two bytes are not a protocol state
#guard minaCheckpointGate "md=p;wk=1;fz=0;rn=0;rc=32;ph=1;th=2;vh=3;ch=4;p=00;t=00;v=00;c=00"
       == "ERR"
-- a missing side is a refusal, never a default
#guard minaCheckpointGate "md=p;wk=1;fz=0;rn=0;rc=32;ph=1;th=2;vh=3;ch=4;p=00;t=00;v=00" == "ERR"

/-! ## §6 — axiom hygiene. -/

#assert_axioms provisional_never_ratchets
#assert_axioms provisional_never_finalizes
#assert_axioms checkpointRoll_finalized_monotone
#assert_axioms checkpoint_without_the_wrap_verdict_moves_nothing
#assert_axioms checkpoint_without_the_cheap_checks_moves_nothing
#assert_axioms a_stale_run_refuses_to_move_the_tip
#assert_axioms provisional_refuses_the_tip_itself
#assert_axioms an_advancing_checkpoint_reanchors_the_tip
#assert_axioms runSteps_finalized_monotone
#assert_axioms a_checkpointless_run_finalizes_nothing
#assert_axioms density_admits_exactly_the_step
#assert_axioms link_discriminates
#assert_axioms both_tiers_discriminate
#assert_axioms checkpointGate_renders_the_roll
#assert_axioms renderRoll_is_the_roll
#assert_axioms the_mode_selects_the_tier
#assert_axioms parseMode_refuses_everything_else

#print axioms runSteps_finalized_monotone
#print axioms provisional_never_ratchets
#print axioms density_admits_exactly_the_step

end Dregg2.Bridge.MinaCheckpoint
