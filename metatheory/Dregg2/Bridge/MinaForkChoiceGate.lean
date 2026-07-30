/-
# Dregg2.Bridge.MinaForkChoiceGate — the RUNTIME-CALLABLE Samasika FORK-CHOICE gates,
`@[export] dregg_mina_better_tip` and `@[export] dregg_mina_head_advance`, plus the ROLLING
VERIFIED HEAD they drive.

⚑ **SUBSTRATE, SAID OUT LOUD.** This file authors **NO AIR**. Fork choice is an OFF-CIRCUIT
DECISION PROCEDURE — what a node runs on two already-valid tips to pick one — and Mina never proves
it in a SNARK either. So this is pure `Nat`/`Bool` Lean, exactly as `MinaChainSelection` and
`LightClientMina` are. It is nonetheless **DECISION LOGIC**, so it is authored HERE and `@[export]`ed
over the C ABI; the Rust in `bridge/src/mina_p2p.rs` speaks the binprot wire, fills the eight
selection fields, and calls in. Rust decides nothing.

## Why this module exists

`Bridge.MinaChainSelection` landed `select` on 2026-07-29 and DELIBERATELY exported nothing, for a
reason that was correct at the time and is stated in its own §9: the long-range branch reads
`sub_window_densities`, and `subWindowDensities` is **not a field of the public GraphQL
`ConsensusState`** (probed live against `api.minascan.io/node/devnet`; the resolver list at
`proof_of_stake.ml:2440-2536` has no arm for it). An export the caller cannot feed is an UN-CALLED
GATE, and this repo has a named class for those.

That blocker was a DATA-SOURCE blocker, not a formalization one, and it is now closed on the Rust
side: `bridge/src/mina_p2p.rs` decodes the binprot `Protocol_state.Value` — where
`sub_window_densities` is an ordinary positional field — off Mina's peer-to-peer RPC
(`get_best_tip`/`get_transition_chain`, `/coda/rpcs/0.0.1`). So the gate can be fed, and here it is.

## What the two exports decide

  * **`dregg_mina_better_tip`** — `select` under the light client's naming: given the EXISTING tip's
    eight selection fields + state hash and a CANDIDATE's, is the candidate canonical? This is the
    decision that replaces asking a node's `bestChain` which chain it likes.
  * **`dregg_mina_head_advance`** — the ROLL: given the client's persisted verified head (its
    selection fields, its state hash, its finalized height) and a candidate tip whose anchored
    segment has ALREADY been accepted by `dregg_mina_lc_verify`, may the head move, and what is the
    new finalized height? A light client that only verifies segments handed to it is not following a
    chain; the thing that makes it follow one is a head it persists and rolls.

## ⚑ THE PAIRWISE SHAPE IS LOAD-BEARING. DO NOT FOLD IT.

`MinaChainSelection.beats_not_transitive` proves `select` has genuine 3-cycles at REAL mainnet
constants, `decide`-checked, by two independent mechanisms. So "the best of a candidate SET" is not a
function of the set — it depends on presentation order, and a peer controlling that order can walk a
node around the cycle. `headAdvance` is therefore a comparison of ONE candidate against the CURRENT
head, never a fold, and `head_can_be_walked_in_a_cycle` states the residual exposure as a THEOREM
rather than a caveat: three "advances" return the head to exactly where it started.

**And the guarantee that survives it**: `rollHead_finalized_monotone` — the FINALIZED height never
decreases, on any input, including around that cycle
(`the_cycle_moves_the_head_but_not_the_finalized_point`). That is the honest light-client property.
The head is a preference and it can cycle; the finalized point is a ratchet and it cannot.

## The constants are PINNED HERE, not carried on the wire — deliberately

`select`'s verdict depends on `grace_period_end` (2237, not the 1440 in the spec table AND in
openmina) and on `sub_windows_per_window`. If the caller supplied them, a hostile peer that also
supplies the states could supply the constants that make its fork win. They are `mainnet` and they
are fixed in this file. What the wire carries is exactly the eight fields
`select_reads_only_eight_fields` proves the verdict is a function of, per side, plus the state hash.

⚑ And the wire REQUIRES exactly `sub_windows_per_window = 11` densities and a 32-byte VRF digest per
side. A source that cannot supply `sub_window_densities` — i.e. the public GraphQL surface — gets
`"ERR"`, which the caller treats as a REFUSAL. There is no arm that proceeds without them.
-/
import Dregg2.Bridge.MinaChainSelection

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Dregg2.Bridge.MinaForkChoiceGate

open Dregg2.Bridge.MinaChainSelection

/-! ## §1 — THE PERSISTED VERIFIED HEAD, and the roll. -/

/-- The light client's persisted state: the tip it currently believes is canonical, and the height
below which it will never reorganise.

`finalized` is a RATCHET (`rollHead_finalized_monotone`); `cs`/`hash` are a PREFERENCE and can
cycle (`head_can_be_walked_in_a_cycle`). Keeping both, and knowing which is which, is the whole
difference between "verified a segment someone handed me" and "following a chain". -/
structure Head where
  /-- The head tip's consensus state (only the eight selection fields are ever read). -/
  cs : ConsensusState
  /-- The head tip's state hash, as the `Fp` element it is (numeric in `[0, p)`). -/
  hash : Nat
  /-- The greatest height this client has ever finalized. NEVER decreases. -/
  finalized : Nat
deriving Repr, DecidableEq

/-- **`headAdvance`** — may the persisted head move to this candidate?

TWO conjuncts, and both are necessary:
  * `segOk` — the candidate's anchored segment was ACCEPTED by `dregg_mina_lc_verify` (linked,
    Pickles-proved, canonical, `k`-deep from the pin). Fork choice presupposes both tips are VALID;
    `select` on an unvalidated tip is just believing a stranger's arithmetic.
  * `minaBetterTip` — `select` prefers the candidate over the CURRENT head. Pairwise. Never a fold. -/
def headAdvance (segOk : Bool) (h : Head) (c : ConsensusState) (ch : Nat) : Bool :=
  segOk && minaBetterTip mainnet h.cs c h.hash ch

/-- **`rollHead`** — the persisted head after one candidate is presented. The finalized height is
raised to `blockchain_length − k` of the new head whenever that is higher, and NEVER lowered. -/
def rollHead (h : Head) (segOk : Bool) (c : ConsensusState) (ch : Nat) : Head :=
  if headAdvance segOk h c ch then
    { cs := c, hash := ch, finalized := max h.finalized (c.blockchainLength - mainnet.k) }
  else h

/-! ## §2 — WHAT THE ROLL GUARANTEES. -/

/-- **THE RATCHET.** The finalized height never decreases — on ANY input, for ANY candidate, under
ANY presentation order. This is the property a light client actually needs, and it is the one that
survives `select` not being an order. -/
theorem rollHead_finalized_monotone (h : Head) (segOk : Bool) (c : ConsensusState) (ch : Nat) :
    h.finalized ≤ (rollHead h segOk c ch).finalized := by
  unfold rollHead
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_refl _

/-- **FAIL CLOSED.** An unverified segment moves nothing. The `segOk` bit is the anchored-segment
gate's verdict, and a source that is unavailable or refused supplies `false` — never a skip. -/
theorem rollHead_fails_closed_without_the_segment (h : Head) (c : ConsensusState) (ch : Nat) :
    rollHead h false c ch = h := by
  simp [rollHead, headAdvance]

/-- **NO SELF-REPLACEMENT.** Re-presenting the head's own tip does not move it (so a peer cannot
churn the head by replaying it). Rests on `select_irrefl`. -/
theorem rollHead_refuses_the_head_itself (h : Head) (segOk : Bool) :
    rollHead h segOk h.cs h.hash = h := by
  simp [rollHead, headAdvance, (minaBetterTip_decides mainnet h.cs h.cs h.hash h.hash).2]

/-- **PRESENTATION ORDER CANNOT MAKE BOTH SIDES WIN.** If the candidate displaces the head, then
presenting them the other way round does not. Rests on `select_asymm`. -/
theorem headAdvance_asymm (h : Head) (c : ConsensusState) (ch : Nat)
    (hadv : headAdvance true h c ch = true) :
    headAdvance true { cs := c, hash := ch, finalized := h.finalized } h.cs h.hash = false := by
  simp only [headAdvance, Bool.true_and] at hadv ⊢
  exact (minaBetterTip_decides mainnet h.cs c h.hash ch).1 hadv

/-! ## §3 — ⚑ THE RESIDUAL EXPOSURE, AS A THEOREM (not a caveat).

`MinaChainSelection.beats_not_transitive` proves `select` has 3-cycles. The consequence for a client
that rolls a head pairwise — which is what the daemon does, and what openmina does — is that a peer
controlling presentation order can walk the head around the cycle. Here it is, executed. -/

/-- The client starts with `lcycA` as its head, having already finalized height 710. -/
def headF : Head := { cs := lcycA, hash := 1, finalized := 710 }

/-- ⚑ **THE HEAD CAN BE WALKED IN A CIRCLE.** Three candidates, each of which `select` genuinely
prefers to the head it is presented against, return the head to EXACTLY its starting value. Every
step is a legitimate Samasika verdict; the cycle is a property of the rule, not of this code.

⚑ **AND THE FINALIZED POINT DOES NOT MOVE.** The head is a preference and it cycled; the ratchet is
a ratchet and it held at 710 throughout. That asymmetry is what makes a pairwise head safe to run:
the worst an order-controlling peer achieves is churning which tip we serve, never un-finalizing. -/
theorem the_cycle_moves_the_head_but_not_the_finalized_point :
    (rollHead headF true lcycB 2).hash = 2
    ∧ (rollHead (rollHead headF true lcycB 2) true lcycC 3).hash = 3
    ∧ (rollHead (rollHead (rollHead headF true lcycB 2) true lcycC 3) true lcycA 1) = headF := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- The same walk stated as the bare cyclicity fact, so no reader can take the theorem above as
"and therefore it is fine". Three accepted advances; net displacement zero. -/
theorem head_can_be_walked_in_a_cycle :
    headAdvance true headF lcycB 2 = true
    ∧ headAdvance true (rollHead headF true lcycB 2) lcycC 3 = true
    ∧ headAdvance true (rollHead (rollHead headF true lcycB 2) true lcycC 3) lcycA 1 = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## §4 — NON-VACUITY: the ratchet ADVANCES on a real advance. -/

/-- A tip that genuinely beats `lcycA`: same epoch and staking lock checkpoint (so the pair is
SHORT-range) and 1000 blocks long against `lcycA`'s zero. -/
def longTip : ConsensusState := mkCS 1000 10 [0,0,0,0,0,0,0,0,0,0,7] [] 7212 7140 1044 0

/-- **THE RATCHET IS NOT A CONSTANT.** Presented a genuinely longer short-range tip, the head moves
AND the finalized height rises to `1000 − k = 710`. (Together with §3, where it held at 710 across a
cycle, this pins the ratchet as a real function of the input rather than a frozen number.) -/
theorem rollHead_advances_the_finalized_point :
    (rollHead { cs := lcycA, hash := 1, finalized := 0 } true longTip 999).finalized = 710
    ∧ (rollHead { cs := lcycA, hash := 1, finalized := 0 } true longTip 999).hash = 999 := by
  refine ⟨?_, ?_⟩ <;> decide

/-- And the SHORT-range branch is genuinely the one taken there, so §4 is not secretly re-testing
the density path. -/
theorem longTip_beats_by_the_short_range_rule :
    isShortRange mainnet lcycA longTip = true
    ∧ minaBetterTip mainnet lcycA longTip 1 999 = true := by
  refine ⟨?_, ?_⟩ <;> decide

/-! ## §5 — THE WIRE. Same `String → String` C-ABI shape as `dregg_mina_lc_verify`.

Fail-closed on any deviation: a malformed wire is `"ERR"` and the caller treats it as REFUSE.

```text
SIDE(x) := "x" "l=" Nat ";" "x" "d=" Nat ";" "x" "w=" NatList11 ";" "x" "v=" ByteList32
         ";" "x" "g=" Nat ";" "x" "p=" Nat ";" "x" "s=" Nat ";" "x" "n=" Nat ";" "x" "h=" Nat
TIP     := SIDE("e") ";" SIDE("c")
```
with `l`=`blockchain_length`, `d`=`min_window_density`, `w`=`sub_window_densities` (EXACTLY 11,
oldest-relative-index-first), `v`=`Blake2b(last_vrf_output)` (EXACTLY 32 bytes), `g`=
`curr_global_slot.slot_number`, `p`=`curr_global_slot.slots_per_epoch`, `s`=
`staking_epoch_data.lock_checkpoint`, `n`=`next_epoch_data.lock_checkpoint`, `h`=the state hash as
its numeric field element. `e`=the EXISTING tip, `c`=the CANDIDATE. -/

/-- Parse a `key=value` field, fail-closed on a key mismatch or a missing `=`. -/
def parseField? (key part : String) : Option String :=
  match part.splitOn "=" with
  | [k, v] => if k == key then some v else none
  | _ => none

/-- Parse a single boolean flag (`"1"` / `"0"`), fail-closed on anything else. -/
def parseBit? (s : String) : Option Bool :=
  if s == "1" then some true else if s == "0" then some false else none

/-- Every element of a comma-split must be a `Nat`, or the whole list fails. -/
def parseNats? : List String → Option (List Nat)
  | [] => some []
  | s :: rest =>
      match s.toNat?, parseNats? rest with
      | some n, some r => some (n :: r)
      | _, _ => none

/-- A comma-separated `Nat` list of EXACTLY `n` entries. Length is checked, not truncated. -/
def parseNatList? (n : Nat) (s : String) : Option (List Nat) :=
  match parseNats? (s.splitOn ",") with
  | some xs => if xs.length == n then some xs else none
  | none => none

/-- A comma-separated BYTE list of exactly `n` entries — every entry `< 256`. The VRF digest is
compared BYTEWISE (`lexLt`), so an entry outside a byte is not a representable digest and must not
be silently admitted as a large `Nat` that then wins every comparison. -/
def parseByteList? (n : Nat) (s : String) : Option (List Nat) :=
  match parseNatList? n s with
  | some xs => if xs.all (· < 256) then some xs else none
  | none => none

/-- One side of the wire: the eight selection fields plus the state hash.

⚑ `slots_per_epoch` is REFUSED at zero. `currEpoch`/`currSlot` divide by the value's OWN
`slots_per_epoch` (`global_slot.ml:79` — an asymmetry the daemon really has), and Lean's `Nat`
division by zero is `0`, which would silently collapse every state into epoch 0 and make every pair
look same-epoch. -/
def decodeSide? (p : String) (parts : List String) : Option (ConsensusState × Nat) :=
  match parts with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8] =>
      match (parseField? (p ++ "l") a0).bind String.toNat?,
            (parseField? (p ++ "d") a1).bind String.toNat?,
            (parseField? (p ++ "w") a2).bind (parseNatList? mainnet.subWindowsPerWindow),
            (parseField? (p ++ "v") a3).bind (parseByteList? 32),
            (parseField? (p ++ "g") a4).bind String.toNat?,
            (parseField? (p ++ "p") a5).bind String.toNat?,
            (parseField? (p ++ "s") a6).bind String.toNat?,
            (parseField? (p ++ "n") a7).bind String.toNat?,
            (parseField? (p ++ "h") a8).bind String.toNat? with
      | some l, some d, some w, some v, some g, some sp, some s, some n, some hsh =>
          if sp == 0 then none else some (mkCS l d w v g sp s n, hsh)
      | _, _, _, _, _, _, _, _, _ => none
  | _ => none

/-- **`decodeTipPair`** — the 18-field `TIP` grammar into (existing, hash, candidate, hash). -/
def decodeTipPair (parts : List String) : Option (ConsensusState × Nat × ConsensusState × Nat) :=
  match parts with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, b0, b1, b2, b3, b4, b5, b6, b7, b8] =>
      match decodeSide? "e" [a0, a1, a2, a3, a4, a5, a6, a7, a8],
            decodeSide? "c" [b0, b1, b2, b3, b4, b5, b6, b7, b8] with
      | some (e, eh), some (c, ch) => some (e, eh, c, ch)
      | _, _ => none
  | _ => none

/-- **`minaBetterTipGate`** — THE FORK-CHOICE GATE. `"1"` means the CANDIDATE is canonical and the
existing tip must be dropped; `"0"` means keep the existing one; `"ERR"` is a malformed or
under-supplied wire (fail-closed). -/
def minaBetterTipGate (s : String) : String :=
  match decodeTipPair (s.splitOn ";") with
  | some (e, eh, c, ch) => if minaBetterTip mainnet e c eh ch then "1" else "0"
  | none => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_better_tip]` — the C-ABI entry `dregg-lean-ffi` calls.
Rust decodes binprot and fills the eight fields; the ARCHIVE renders the fork-choice verdict. -/
@[export dregg_mina_better_tip]
def dregg_mina_better_tip (s : String) : String := minaBetterTipGate s

/-- The gate string IS `minaBetterTip`, by construction. -/
theorem minaBetterTipGate_eq_decision (s : String) (e c : ConsensusState) (eh ch : Nat)
    (hd : decodeTipPair (s.splitOn ";") = some (e, eh, c, ch)) :
    minaBetterTipGate s = (if minaBetterTip mainnet e c eh ch then "1" else "0") := by
  unfold minaBetterTipGate
  rw [hd]

/-! ## §6 — THE HEAD-ADVANCE WIRE + `@[export]`.

```text
INPUT  := "sg=" BIT ";fz=" Nat ";" TIP        -- `e` = the persisted head, `c` = the candidate
OUTPUT := "adv=" BIT ";fin=" Nat  |  "ERR"
```
`sg` is the anchored-segment verdict (`dregg_mina_lc_verify` returned `"1"`), `fz` the persisted
finalized height. The output carries BOTH halves of the roll so the caller persists a decision it
did not make: `adv` says whether to replace the head, `fin` is the new finalized height. -/

/-- **`minaHeadAdvanceGate`** — THE ROLL GATE. -/
def minaHeadAdvanceGate (s : String) : String :=
  match s.splitOn ";" with
  | p0 :: p1 :: rest =>
      match (parseField? "sg" p0).bind parseBit?,
            (parseField? "fz" p1).bind String.toNat?,
            decodeTipPair rest with
      | some sg, some fz, some (e, eh, c, ch) =>
          let h : Head := { cs := e, hash := eh, finalized := fz }
          let adv := headAdvance sg h c ch
          let h' := rollHead h sg c ch
          "adv=" ++ (if adv then "1" else "0") ++ ";fin=" ++ toString h'.finalized
      | _, _, _ => "ERR"
  | _ => "ERR"

/-- **THE EXPORT.** `@[export dregg_mina_head_advance]`. -/
@[export dregg_mina_head_advance]
def dregg_mina_head_advance (s : String) : String := minaHeadAdvanceGate s

/-! ## §7 — NON-VACUITY: the decisions DISCRIMINATE, kernel-clean.

The scalar decisions are pure `Nat`/`Bool`, so `decide` reduces them in the kernel. The STRING wire
layer uses well-founded recursion the kernel cannot reduce under `decide`; the `#guard`s run it in
the interpreter at build time, and `minaBetterTipGate_eq_decision` ties the string surface to the
decision without needing to reduce the parser. -/

/-- The two branches of `select` are BOTH exercised by the exported decision, and the ratchet is a
real function of its inputs. -/
theorem fork_choice_discriminates :
    -- SHORT-range: strictly longer wins
    minaBetterTip mainnet lcycA longTip 1 999 = true
    -- and the reverse does not
    ∧ minaBetterTip mainnet longTip lcycA 999 1 = false
    -- LONG-range: the denser chain wins even at equal length
    ∧ minaBetterTip mainnet lcycB lcycC 2 3 = true
    -- a tip never displaces itself
    ∧ minaBetterTip mainnet lcycA lcycA 1 1 = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

-- The wire layer, in the interpreter. `W`/`V` are the 11 densities and the 32-byte VRF digest.
-- A genuine pair decides; a 10-entry density list, a 31-byte digest, a >255 digest byte, a zero
-- `slots_per_epoch` and a truncated field list are all `"ERR"` (fail-closed) rather than a verdict
-- computed from what did arrive.
#guard minaBetterTipGate
  ("el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "1"

#guard minaBetterTipGate
  ("el=1000;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=999;"
   ++ "cl=0;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=1") == "0"

-- ⚑ TEN densities, not eleven — this is what the PUBLIC GRAPHQL SURFACE can supply (nothing), and
-- what a truncated binprot decode looks like. REFUSED, not evaluated on the short-range branch.
#guard minaBetterTipGate
  ("el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "ERR"

-- A 31-byte VRF digest.
#guard minaBetterTipGate
  ("el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "ERR"

-- A digest "byte" of 256 — a `Nat` that is not a byte, which would otherwise win every `lexLt`.
#guard minaBetterTipGate
  ("el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=256,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "ERR"

-- `slots_per_epoch = 0` — Lean's `Nat` division would make it epoch 0 rather than fail.
#guard minaBetterTipGate
  ("el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=0;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "ERR"

#guard minaBetterTipGate "garbage" == "ERR"
#guard minaBetterTipGate "" == "ERR"

-- The ROLL gate: a genuine advance raises the ratchet to 710; the SAME wire with `sg=0` (the
-- anchored-segment gate refused, or was unavailable) advances nothing and keeps the old finalized
-- height. This is the fail-closed arm, exercised on the wire and not only at the scalars.
#guard minaHeadAdvanceGate
  ("sg=1;fz=0;"
   ++ "el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "adv=1;fin=710"

#guard minaHeadAdvanceGate
  ("sg=0;fz=0;"
   ++ "el=0;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=1;"
   ++ "cl=1000;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=999") == "adv=0;fin=0"

-- ⚑ THE RATCHET ON THE WIRE: a REFUSED advance still reports the OLD finalized height rather than
-- dropping it, and a shorter candidate cannot lower it either.
#guard minaHeadAdvanceGate
  ("sg=1;fz=710;"
   ++ "el=1000;ed=10;ew=0,0,0,0,0,0,0,0,0,0,7;ev=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "eg=7212;ep=7140;es=1044;en=0;eh=999;"
   ++ "cl=0;cd=10;cw=0,0,0,0,0,0,0,0,0,0,7;cv=0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0;"
   ++ "cg=7212;cp=7140;cs=1044;cn=0;ch=1") == "adv=0;fin=710"

#guard minaHeadAdvanceGate "sg=1;fz=0;garbage" == "ERR"
#guard minaHeadAdvanceGate "garbage" == "ERR"

/-! ## §8 — axiom hygiene. -/

#assert_axioms rollHead_finalized_monotone
#assert_axioms rollHead_fails_closed_without_the_segment
#assert_axioms rollHead_refuses_the_head_itself
#assert_axioms headAdvance_asymm
#assert_axioms the_cycle_moves_the_head_but_not_the_finalized_point
#assert_axioms head_can_be_walked_in_a_cycle
#assert_axioms rollHead_advances_the_finalized_point
#assert_axioms longTip_beats_by_the_short_range_rule
#assert_axioms minaBetterTipGate_eq_decision
#assert_axioms fork_choice_discriminates

#print axioms rollHead_finalized_monotone
#print axioms the_cycle_moves_the_head_but_not_the_finalized_point

end Dregg2.Bridge.MinaForkChoiceGate
