# THE MIRROR MAP

**21 adversarially-verified findings of ONE failure mode: a re-authored mirror standing in for the real
thing while docs/tests claim the seam is closed — the tests green BECAUSE they test the mirror.**

Swept 2026-07-15/16 against HEAD `c451eb1f2`. Every finding below already survived a refutation pass
(labeled-double / legitimate-abstraction / labeled-placeholder / live-path-uses-the-real-thing /
claim-misread were each tried and each failed). Severities are the CORRECTED ones from that pass, not
the reporters' openers.

This is a work order. §1 groups by variant with the claim and the fix. §2 ranks by severity and by
leverage. §3 is the structural analysis — why this shape keeps getting produced, and what makes each
variant *unrepresentable* rather than merely fixed. §4 is the honest coverage count.

## ID table

| ID | Where | Variant | Severity |
|----|-------|---------|----------|
| M01 | `dreggnet-faction/src/roster.rs:315` | twin-engine + harness-tests-own-mirror | **high** (soundness) |
| M02 | `dreggnet-gear/src/multislot.rs:115` | fixture-on-live-path + doc-claims-absent-seam | medium |
| M03 | `dreggnet-trade/src/lib.rs:445` | re-authored-peer + shared-constant | medium |
| M04 | `dreggnet-asset/src/lib.rs:59` | doc-claims-absent-seam + harness-tests-own-mirror | low |
| M05 | `dreggnet-adventure/src/lib.rs:282` | fixture-on-live-path | **high** |
| M06 | `dreggnet-guild/src/leaderboard.rs:76` | host-vs-proven | medium |
| M07 | `dregg-multiway-tug/src/surface.rs` | re-authored-peer / fresh-per-caller-world | **closed 2026-07-20** |
| M08 | `dregg-automatafl/src/surface.rs:864` | fixture-on-live-path | medium |
| M09 | `spween-dregg/src/world.rs:331` | host-vs-proven + doc-claims-absent-seam | medium |
| M10 | `dreggnet-telegram/tests/full_parity_through_telegram.rs:33` | harness-tests-own-mirror + re-authored-peer | medium |
| M11 | `protocol-tests/src/invariants/effect_vm_differential.rs:146` | harness-tests-own-mirror | **high** (soundness tripwire dead) |
| M12 | `cell/src/interface.rs:26` | doc-claims-absent-seam | low |
| M13 | `circuit/descriptors/by-name/predicate-arith.json` | lean-models-reauthored-shape | **CRITICAL** |
| M14 | `scripts/check-descriptor-drift.sh:86` | harness-tests-own-mirror | **high** |
| M15 | `dregg-dsl-differential/src/kimchi_sim.rs:79` | harness-tests-own-mirror | medium |
| M16 | `dregg-dsl-differential/src/plonky3_runner.rs:391` | doc-claims-absent-seam | **high** (harness-scope) |
| M17 | `dregg-dsl-tests/src/dregg_definitions.rs:194` | doc-claims-absent-seam | low-medium |
| M18 | `attested-dm/Cargo.toml:6` | doc-claims-absent-seam | low-medium |
| M19 | `dregg-governance/src/lib.rs:587` | twin-engine | medium |
| M20 | `node/src/turn_proving.rs:730` | re-authored-peer | medium |
| M21 | `metatheory/Dregg2/Substrate/VerbRegistry.lean:213` | lean-models-reauthored-shape | **high** |

---

# §1 — FINDINGS BY VARIANT

Each entry: **CLAIM** (what the tree says, verbatim, with the cite) · **TRUTH** (what the code does) ·
**LIVE?** (does the mirror sit on the path anyone runs) · **FIX** (executable) · **CANARY** (the test
that must be RED before the fix and GREEN after — without it the fix is unverified).

---

## VARIANT A — twin-engine
*Two programs meant to BE the same program at two resolutions; one is missing teeth the other's own
doc calls load-bearing. The tested one is not the deployed one.*

### M01 — the faction roster generates a toothless twin of `faction_compiled` · **high / soundness-hole**

- **CLAIM** — `dreggnet-faction/src/roster.rs:19-22`: "The generated program is deployed on the SAME
  WorldCell as the hand-authored feud, so a data-driven roster's standing is **exactly as
  executor-refereed as the inline example**: you cannot fake standing, content stays gated, a betrayal
  permanently seals." · `:310-311` "the data-driven twin of `crate::faction_compiled`" · `:136-138`
  "Proof the generator subsumes the hand-authored example: **the generated teeth are identical in
  shape**."
- **TRUTH** — `grep -c SlotChanged dreggnet-faction/src/roster.rs` → **0**. `lib.rs` → **9**.
  `lib.rs:390-439` pushes four slot-bound `TransitionCase`s (`SlotChanged{ember_quest}` →
  `FieldGte{rep_embers, REP_THRESHOLD}` + `FieldEquals{embers_betrayed,0}` + `WriteOnce`;
  `SlotChanged{tide_region}` same; `SlotChanged{rep_embers}` → `Monotonic`; `SlotChanged{rep_tide}` →
  `Monotonic`). `Roster::compile` (`roster.rs:315-365`) pushes NONE — it only calls `augment_case`
  (`lib.rs:263-273`), which matches `TransitionGuard::MethodIs{method: mm} if *mm == m`, so every gate
  binds to its AUTHORING METHOD. `spween-dregg/src/compiler.rs` emits only `MethodIs` (`:422`, `:454`,
  `:493`).
- **LIVE? YES, and INVERTED.** `dreggnet-quest/src/giver.rs:515-517` — `let roster =
  Roster::ashenmoor(); let faction = roster.deploy(FACTION_SEED);` — the sole cross-crate consumer
  (`FactionGatedGiverWorld`, the faction→quest gate) deploys the ROSTER. Repo-wide,
  `deploy_feud`/`faction_compiled` (the version WITH the teeth AND with the falsifiers
  `a_stapled_faction_unlock_cannot_ride_a_pledge` `lib.rs:801` and
  `a_rep_write_down_cannot_ride_a_nonpledge_method` `lib.rs:864`) is called only from the crate's own
  `#[cfg(test)]` mod and from `dreggnet-saga`. **The tested program is the one nothing outside the
  crate deploys; the deployed program is the one nothing tests.**
- **Consequence on the DEPLOYED program** — `world.apply_raw(&hall_method(lines.pledge),
  vec![SetField(rep,1), SetField(quest_slot,1)])` faces only the pledge case's `Monotonic{rep}` +
  `FieldLteOther{rep<=ceiling}`; neither mentions `quest_slot`; the unlock commits at rep 0, opening
  `{<key>_quest >= 1}` (`roster.rs:285-289`) and flipping `FactionStanding::unlocked`
  (`standing.rs:81`). Separately a stapled rep write-DOWN un-earns standing — so the crate headline
  "rep can rise but is never un-earned" (`lib.rs:22`) is **false on the only program anyone deploys**,
  and is strictly worse than `lib.rs`'s named residual (`lib.rs:423-430` scoped out only rep INFLATION
  past a moving ceiling, keeping the ratchet).
- **FIX** — the root cause is DRIFT, so fix the drift, not the symptom:
  1. Factor `pub(crate) fn push_slot_bound_faction_gates(program: &mut CellProgram, rep: u8, quest: u8,
     betrayed: u8, threshold: u64)` out of `lib.rs:390-439`, and call it from **both**
     `faction_compiled()` and `Roster::compile()` inside its `for (i, f) in
     self.factions.iter().enumerate()` loop. Requires importing `TransitionCase`/`TransitionGuard`/
     `CellProgram` into `roster.rs` and `if let CellProgram::Cases(cases) = &mut story.program`.
  2. Per-faction threshold is **`f.threshold`, NOT `crate::REP_THRESHOLD`** — the roster's whole point
     is per-faction bars.
  3. Add `SlotChanged{betrayed} → WriteOnce{betrayed}` (closes the betrayal-seal staple the roster is
     also open to; `lib.rs` omits it only because its recant/betray carry it per-method).
  4. Carry `lib.rs:423-430`'s rival-ceiling residual note across verbatim so the roster names the same
     residual instead of silently inheriting a worse one.
  5. Add `pub fn slot_case_constraints(story: &CompiledStory, index: u8) -> Vec<StateConstraint>`
     matching `SlotChanged{index: ii} if *ii == index`. `case_constraints` (`lib.rs:460-470`) is
     `MethodIs`-only and must STAY that way — that is why the harness is blind.
  6. `dreggnet-faction/tests/roster_integration.rs:90` (`generated_teeth_are_real_per_faction`) currently would pass
     byte-identically if every slot-bound gate in the crate were deleted. Extend it to assert
     per-faction `SlotChanged{quest}` carries `FieldGte(rep, f.threshold)` and `SlotChanged{rep}`
     carries `Monotonic(rep)`.
- **CANARY (introspection is not the gate — a DRIVEN staple is)** — port both falsifiers to
  `dreggnet-faction/tests/roster_integration.rs` against `Roster::ashenmoor().deploy(seed)` + `roster.lines("embers")`:
  `a_stapled_roster_unlock_cannot_ride_a_pledge` (apply_raw with `SetField{rep,1}, SetField{quest,1}`
  must be `Err(WorldError::Refused(_))`, `read_var(quest_var("embers")) == 0`, then two real pledges +
  the trial line still commit — the gate is a bar, not a ban) and
  `a_roster_rep_write_down_cannot_ride_a_nonpledge_method`. **Run both against the UNFIXED
  `Roster::compile` first and watch them fail.** Also run on `tri_roster`
  (`roster_integration.rs:18`), whose third unaligned faction exercises the `rival: None` path.
- **Fails smell test:** stapleable-slot hole class, live.

### M19 — `dregg-governance::CollectiveChoice` is a COLLIDING alias for the demoted host box · **medium**

- **CLAIM** — three:
  (1) `dregg-governance/src/lib.rs:578-586` — the aliases exist "only so out-of-lane consumers keep
  compiling. Nothing in this crate's governance or community face uses them; **new code should name
  `collective_choice::{CollectiveChoice, VoteEngine}`** (the verified engine) … **never these**."
  New code did exactly the forbidden thing.
  (2) `dregg-interchain-gov/examples/cross_chain_vote.rs:12-16` lists among *production* components
  "…the Lean-proven weight verdict, **the CollectiveChoice engine**"; and `:15-16` promises "What is
  fixture is SAID to be fixture, inline, when it prints."
  (3) `dregg-interchain-gov/Cargo.toml:27` — "weighted votes → **one cross-chain tally**,
  non-custodially"; `src/lib.rs:32-34` links the phrase to `dregg_governance::CollectiveChoice`.
- **TRUTH** — `dregg-governance/src/lib.rs:587` `pub type CollectiveChoice = HostBallotBox;` and `:591`
  `pub use self::HostVoteEngine as VoteEngine;`. `examples/cross_chain_vote.rs:67` `let mut engine =
  CollectiveChoice::new();` — **zero args, dispositive**: the real
  `collective_choice::CollectiveChoice::new(federation_id: [u8;32])` (`collective-choice/src/lib.rs:277`)
  requires one; only `HostBallotBox::new()` (`dregg-governance/src/lib.rs:409`) takes none. Its one-vote
  is `st.voted.contains(&block.voter)` on a HashSet (`lib.rs:511-516`) and its quorum a `>=` — versus
  the verified engine's `WriteOnce(VOTE)` + nullifier + in-cell `AffineLe`/`CountGe` (non-vacuity
  verified at `cell/src/program/eval.rs:1998-2046`). The collision is proven live: `dregg-pay/src/
  governance.rs:24,95` imports `CollectiveChoice` from `collective_choice` and calls
  `CollectiveChoice::new(federation_id)`. Same identifier, two crates, two engines.
- **The disclosure gap is the sharpest evidence:** the demo says "fixture" inline **five** times
  (`:93`, `:122`, `:132`, `:286`, `:358`) and discloses the ballot box **zero** times. The tally print
  (`:189-198`) prints `distinct_voters` — a `HostBallotBox` field — with no caveat.
- **LIVE?** Demo/tests only — `dregg-interchain-gov/src/lib.rs` contains only conversion functions. No
  shipping binary rides the box, no value at risk. The GRANT side is genuinely verified (real light
  clients, real signature schemes, Lean-proven `grantWeightCore`, fail-closed narrowing via
  `narrow_ballot_weight`, nullifier not burned on downstream refusal — `holding_weight.rs:960-1010`).
  Only the outcome-deciding box is host-side.
- **DO NOT "fix" by swapping in `collective_choice::CollectiveChoice` — it will not compile.**
  `VoteEngine::cast(&mut self, poll, ballot: &BallotCap, option: usize)` has **no weight parameter**,
  and `holding_weight.rs:987 foreign_grant_and_cast` is typed `engine: &mut HostBallotBox`. **There is
  no verified-engine variant of the weighted foreign-ballot path.** That is the real finding: dregg's
  cross-chain weighted tally has NO verified ballot box, and the alias is what conceals it.
- **FIX part 1 (same-day, `dregg-interchain-gov` only; `dregg-governance` needs no change):**
  1. `examples/cross_chain_vote.rs:27-29` + `dregg-interchain-gov/tests/cross_chain_governance.rs:45` — import
     `HostBallotBox, HostVoteEngine`. `examples:67` and `tests:463` → `HostBallotBox::new()`. Pure
     rename, zero behavior change (the alias IS the type) — it makes the use site read what it is.
  2. `examples/cross_chain_vote.rs:12-16` — strike "the CollectiveChoice engine" from the production
     list (the rest of the list is accurate; keep it).
  3. `examples/cross_chain_vote.rs:189-198` — honor the header's own inline-disclosure promise at the
     tally print: "ballot box: HostBallotBox — the DEMOTED host-side box. One-vote here is a HashSet
     and quorum a `>=`, NOT the executor's WriteOnce(VOTE) + nullifier + in-cell AffineLe/CountGe. The
     grant path above is production; the box that decides the outcome is not."
  4. `src/lib.rs:32-34` — retarget the doc link off `dregg_governance::CollectiveChoice`; say "one
     host-derivable `HostBallotBox` tally (light-client recomputable via `derive_tally`/`verify_tally`;
     NOT the executor-backed engine)". `Cargo.toml:27` → "one host-derived, light-client-recomputable
     cross-chain tally".
  5. **Turn the prose prohibition into a build failure:** `#[deprecated(note = "names the DEMOTED
     HostBallotBox; see collective_choice::CollectiveChoice")]` on `dregg-governance/src/lib.rs:587,591`
     + `#![deny(deprecated)]` in `dregg-interchain-gov`. Sweep other out-of-lane consumers FIRST or the
     deny breaks unrelated crates.
- **FIX part 2 (the closure lane the alias conceals):** extend the verified engine with a weighted
  ballot — carry the u64 weight into the ballot cell so the executor's `Monotonic` tally sums weight
  rather than counting heads, keeping `WriteOnce(VOTE)`+nullifier as the one-vote tooth and
  `AffineLe`/`CountGe` as quorum. Then retype `foreign_grant_and_cast` to the verified engine, point the
  demo at it, and **DELETE both aliases** — at which point the collision cannot recur. If weighting is
  deliberately out of scope, say so in a named residual and stop selling "one cross-chain tally" as
  verified anywhere.

---

## VARIANT B — re-authored-peer
*A second authoring of an object that already exists, built side-by-side with the real one and never
reconciled. Includes the shared-constant sub-shape: two identity systems bound only by a label string.*

### M07 — the tug surface deals a SECOND hand that is not the hand the round plays · **CLOSED**

**HEAD REPAIR — CLOSED 2026-07-20.** The engine now shuffles the 21 **distinct card ids** and
projects them through one shared `deck_guild`; `TugOffering` commits the engine's exact current
hand rather than fabricating `0..6` / `6..12`; every `ResolvedMove` reports all exact cards it
consumed (4/3/2/1), and the live root is rebuilt from the exact post-draw/post-play hand. The
terminal private fold record contains all ten cards actually entrusted to each seat and all ten
actual plays, and is unavailable through the public API until SCORE. The old finding below is
retained as the falsified historical counterexample and repair rationale. Canaries now compare
the commitment/render to `Engine::hand` (the independent source), require seed-dependent guilds,
and reject a forged peer commitment.

**FOLLOW-ON LIVE-ADMISSION CLOSURE — 2026-07-20.** The playable Offering now DEAL-pins each
seat's ten-card private round-inventory root. Every 4/3/2/1-card action supplies the opening and
Poseidon2 path for **every exact card it consumes** to arity-specific
`Witnessed{MerkleMembership}` cases; the proof-free `play` case is absent/default-denied. The
Lean-authored rules cell and the hidden-hand cell share one `EmbeddedExecutor`, and their two signed
actions are submitted in one atomic turn: a missing/fabricated/tampered/wrong-root witness refuses
the move and rolls the rules projection back with it. Fresh-seed `/verify` replays the accepted
inputs and compares both the public projection and private remaining-inventory commitments.

**Honest residual:** membership is checked against the static DEAL-pinned inventory root.
Exact-card duplicate consumption is prevented by the host's private remaining-inventory ratchet and
rechecked by fresh replay, not yet by a protocol-native dynamic-root/nullifier constraint. The live
admission weld and cross-cell atomicity are closed; the native nullifier/dynamic-root tooth and the
succinct whole-match lowering remain proof work.

- **CLAIM** — `dregg-multiway-tug/src/surface.rs:13-14`: "the viewer's OWN hand is revealed (**the card
  ids they hold**, sourced from the `crate::hidden_hand` committed `HandTree`)" · `:20-21` "**The two
  agree** (the surface reveals what the viewer legitimately holds under their committed root)" ·
  `:168-169` "The card ids are read off the committed `HandTree` — the hidden-hand **source**" · `:78-79`
  documents `TugSession.hands` as "Each seat's committed hidden hand".
- **TRUTH — two disjoint hands, built in the same struct literal, never reconciled.**
  `Engine::new` (`reference.rs:211-232`) builds the deck as GUILD ids (`for (g,&inf) in
  INFLUENCE.iter().enumerate() { for _ in 0..inf { deck.push(g as u8) } }`), Fisher-Yates shuffles with
  `SplitMix64(seed ^ 0xA5A5_5A5A_1234_9876)`, pops one favor out of play, deals 6+6 into
  `Engine.hands: [Vec<u8>; 2]` (`reference.rs:191`) — a real, seed-dependent shuffle.
  `deal_hidden_hands` (`surface.rs:266-285`) builds `HandTree`s over CARD ids `base + 0..HAND_SIZE`,
  i.e. `[hand_for(0), hand_for(6)]` — **ids 0..6 and 6..12 on EVERY session**; the seed enters only
  `nonce_of` (the per-card blind). Via `deck_guild` (`hidden_hand.rs:85-96`) over
  `INFLUENCE=[2,2,2,3,3,4,5]` the cumulative ranges are g0:0-1, g1:2-3, g2:4-5, g3:6-8, g4:9-11,
  g5:12-15, g6:16-20 — so **seat A's rendered hand is ALWAYS guilds [0,0,1,1,2,2] and seat B's ALWAYS
  [3,3,3,4,4,4]**, for every seed. `TugOffering::open` (`surface.rs:290-304`) constructs
  `engine: Engine::new(seed)` (`:292`) and `hands: deal_hidden_hands(seed)` (`:301`) side by side.
- **LIVE? YES — the only hand the offering has, shipped to four frontends.** `Offering::render_for`
  (`surface.rs:397-399`) → `surface_for` (`:224`) → `own_hand` (`:170`) prints `format!("  card #{id} ·
  guild {g} · w{w}")` (`:182`) from `self.hands[seat.idx()].card_ids()` (`:171`) — the fabricated ids.
  Meanwhile `advance` (`:359`) plays `session.engine.play_next()` → `pick_lowest`/`pick_highest`
  (`reference.rs:417-429`) sorting `self.hands[p.idx()]` — the OTHER hand. **The card a player is shown
  is not the card that gets played.** Frontends: `dreggnet-web/src/seated.rs:117` (the deployed hbox
  games devnet), `dreggnet-telegram/src/seated.rs:119`, `dreggnet-wechat/src/seated.rs:119`,
  `discord-bot/src/commands/portfolio.rs:144`.
- **The tooth is decorative too.** `advance` (`surface.rs:366-368`) removes the lowest surviving
  FABRICATED id, not the card `play_next` played — the remaining-hand root moves as bookkeeping over an
  unrelated multiset, so `hidden_hand.rs:26-29`'s "the crypto is the no-double-play tooth" does not
  reach this session.
- **The tests verify the mirror against itself.** `surface/tests.rs:52-55` `fn seat_card_ids(session,
  seat) -> session.hands[seat.idx()].card_ids()` — the same fabricated array `own_hand` prints.
  `viewer_sees_own_hand_only` and `public_render_is_fog_for_both` prove the fog is non-vacuous but never
  consult `session.engine`.
- **FIX — the hidden hand must BE the dealt hand: one hand, dealt once, in card-id space** (the fix
  `reference.rs` already half-wants — `hidden_hand.rs:80-84` says distinct ids exist precisely so two
  copies of a guild get independent leaves):
  1. `reference.rs` — deal CARD IDS. `Engine::new`: `deck: Vec<u8> = (0..DECK_SIZE as u8).collect()`
     (the guild partition IS `INFLUENCE` via `deck_guild`, so the multiset is unchanged and conservation
     stays green); keep the identical Fisher-Yates + `deck.pop()` removal + 6/6 deal.
  2. `pick_lowest`/`pick_highest` (`reference.rs:417-429`) — sort by `INFLUENCE[deck_guild(c) as usize]`
     (tiebreak `deck_guild(c)`, then `c`), truncate as today.
  3. `place()`/secret/Gift/Competition (`reference.rs:~390-411, 435-445`) — translate at SCORING:
     `self.place(p, deck_guild(card))`, keeping the score array indexed by guild. The projection must
     not change shape so executor genesis (`surface.rs:296`) and conservation (`:381`) stay green.
  4. Add `pub fn hand(&self, p: Player) -> &[u8]`, and make `play_next` return the played card id(s)
     (`ResolvedMove::played_cards() -> Vec<u8>`).
  5. `surface.rs` — delete `deal_hidden_hands`'s `base + i` invention. Replace with `fn
     commit_dealt_hands(engine: &Engine, seed: u64) -> [HandTree; 2]` doing per seat
     `HandTree::commit(engine.hand(seat).iter().map(|&c| (c as u64, nonce_of(seed, c as u64))).collect())`,
     keeping the existing splitmix `nonce_of` as the blind. `TugOffering::open` builds `let engine =
     Engine::new(seed);` then `hands: commit_dealt_hands(&engine, seed)` — **hands becomes a FUNCTION of
     engine, not a peer of it.**
  6. `advance` (`:366-368`) — remove the card ACTUALLY played: `for c in mv.played_cards() {
     session.hands[seat.idx()] = session.hands[seat.idx()].without(c as u64); }`. Gift/Competition play
     multiple cards; the removal must match the move's arity, and the secret's card is removed at play
     and revealed at score.
- **CANARY** — three tests in `surface/tests.rs`, the second of which falsifies today's code on the spot:
  `committed_hand_is_the_dealt_hand` (several seeds, `sorted(session.hands[seat].card_ids()) ==
  sorted(engine.hand(seat) as u64)` both seats); **`rendered_guilds_are_seed_dependent`** (open with
  seeds 7 and 8; the multiset of guilds read off A's rendered surface must DIFFER for at least one seed
  pair — currently `[0,0,1,1,2,2]` for every seed); `played_card_leaves_the_committed_hand`. Retarget
  `seat_card_ids` (`tests.rs:52-55`) to read `session.engine.hand(seat)` so the fog tests measure the
  render against the ROUND, not against itself.
- **Historical residual, subsequently closed by the follow-on above:** `HiddenHandLedger` / the
  executor-checked `Witnessed{MerkleMembership}` gate was not wired into `TugOffering`. It now is;
  retain this paragraph only as the original audit's repair trail, not as a HEAD claim.

### M03 — `TradeWorld::reclaim`'s depositor gate is `x != x`; the escrow party is a re-authored identity · **medium**

- **CLAIM** — `dreggnet-trade/src/lib.rs:32-36` "reclaim … the ghost defence. If a counterparty never
  deposits, the depositor reclaims its own leg" · `:440-444` "The sealed escrow permits it **only to the
  leg's depositor** and only while the leg is live (`reclaim_leg`), consuming it one-shot." · `:51-53`
  "scam-proofness is by construction". The one-shot half IS real; the "only to the leg's depositor" half
  cannot fire.
- **TRUTH — the callee supplies the value the gate compares against.** The real primitive
  `cell/src/escrow_sealed.rs:595-612` gates `if by != terms.requirement(side).party { return
  Err(EscrowError::NotYourLeg(side)) }`. `open_trade` (`lib.rs:329-332`) builds the terms from
  `party_cell(label)`; `reclaim` (`:445-451`) hands `reclaim_leg` that identical binding back
  (`let (label, spec, party) = { let b = trade.binding(side); (b.label.clone(), b.spec, b.party) };
  reclaim_leg(&mut trade.escrow, &trade.terms, side, party)?;`). The comparison is `x != x`.
  `reclaim(&mut self, trade: &mut Trade, side: Side)` **takes no caller identity**, so a wrong-party
  reclaim is not even EXPRESSIBLE from this crate. No test hits it; repo-wide `NotYourLeg` appears in
  `demo/`, `starbridge-apps/escrow-market/`, `dreggnet-guild/` — never in `dreggnet-trade`.
- **The shared-constant sub-shape** — two disjoint KDF contexts bound only by a label string:
  `dreggnet-trade/src/lib.rs:93` `blake3::derive_key("dreggnet-trade-party-v1", label)` vs the identity
  that ACTUALLY signs, `dreggnet-asset/src/lib.rs:298-310` `blake3::derive_key(
  "dreggnet-asset-holder-v1", label)` → the ed25519 pubkey (surfaced as `pubkey_of` at `:547`).
  **Nobody ever signs for a `party_cell`; it is unauthenticatable by construction.**
- **The sibling settles it.** `dreggnet-guild/src/treasury.rs:73-82` exposes `attempt_abscond(side,
  officer: CellId, to)` — the party comes FROM THE CALLER, so the gate fires, and `guild.rs:287` asserts
  the real `NotYourLeg(Side::A)` refusal with the non-vacuous contrast (the SAME reclaim succeeds for
  the depositor at `:91`). Same primitive, one rung higher — which kills the legitimate-abstraction and
  deliberate-placeholder refutations.
- **NOT a theft hole (severity corrected down).** `cross_leg` (`:425-437`) hardcodes the reclaim
  destination to `b.label`, the depositor's OWN label, so a reclaim cannot route value to a non-depositor
  regardless of caller. The exposure is **griefing/DoS**: any holder of `&mut TradeWorld` can cancel a
  live fully-deposited trade (both sides then reclaim, both made whole). `deposit`'s tooth is genuine
  (the `:374` owner-signed `AssetWorld::transfer`) — so the crate's auth model is "authority comes from
  the asset key gate", and **reclaim is the one live operation that opted out of it**.
- **FIX** — bind the escrow's party to the identity that actually signs, and plumb a caller through:
  1. `lib.rs:93-96` — delete the free fn; make it a method:
     `fn party_cell(&mut self, label: &str) -> CellId { CellId::from_bytes(blake3::derive_key(
     "dreggnet-trade-party-v1", &self.assets.pubkey_of(label))) }`. The escrow's party then IS the
     ed25519 pubkey that signs spends — one identity instead of two label-parallel derivations.
     `open_trade` (`:325-332`) already calls `self.assets.pubkey_of(a_label)`/`(b_label)` for exactly
     these labels, so this is local.
  2. `:445` — `pub fn reclaim(&mut self, trade: &mut Trade, side: Side, by: &str) -> Result<(),
     TradeError>`. Derive `let claimant = self.party_cell(by);` from the CALLER's own label and pass
     `claimant` (not `trade.binding(side).party`) to `reclaim_leg` at `:451`. Keep `cross_leg` pointed
     at the binding's label so even an authorized reclaim cannot re-point value. Mirror
     `dreggnet-guild/src/treasury.rs:73-96`.
  3. `:546` (buy's shortfall undo) — this is the executor unwinding its OWN step, a legitimate use, not
     a party acting. Route it to a private `fn reclaim_unchecked(&mut self, trade, side)` holding the
     current body; the new pub `reclaim` becomes the thin authenticated wrapper. (Or pass `&seller`,
     already cloned at `:539`.)
- **CANARY** — modelled on `dreggnet-guild/tests/guild.rs:287`, in `dreggnet-trade/tests/atomic_trade.rs`: after Alice
  deposits and Bob ghosts, `tw.reclaim(&mut trade, TradeSide::A, "bob")` must be
  `Err(TradeError::Escrow(EscrowError::NotYourLeg(Side::A)))` with NOTHING moved (Alice still not
  holding, leg still Deposited) — and the SAME call with `"alice"` succeeds. **Without the failing-side
  arm the gate is untested by construction.**
- **Residual to NAME** (`:56-63` says nothing about identity today): no caller signature over the
  reclaim request — the party CellId is still asserted, not proven, exactly as in guild.

### M20 — the node's v1 proving arm attests a fabricated zero-field cell · **medium**

- **CLAIM** — `node/src/turn_proving.rs:40-41`, under a heading literally reading "## Soundness scope
  (honest)": "`old_commit` is **the actor cell's** pre-execution `CellState::compute_commitment`" ·
  `:43-46` "the load-bearing commit-path leg the public claim rests on" ·
  `node/src/blocklace_sync.rs:4732-4737` "This is what makes the public **'every state transition is
  proven'** claim TRUE for the running node … re-verified against the actor cell's pre-state
  commitment." · `turn_proving.rs:4-6` promises "**one named exception** stated here at the headline
  rather than 70 lines downstream" — this is a second, unnamed one, stated 724 lines downstream.
- **TRUTH** — `turn_proving.rs:734` `None => CellState::new(pre_balance, pre_nonce as u32)` fabricates a
  cell sharing only (balance, nonce) with the ledger's real `dregg_cell::Cell`:
  `circuit/src/effect_vm/cell_state.rs:97` `let fields = [BabyBear::ZERO; 8];`, `:68`
  `empty_capability_root()[0]`, `:81` `empty_record_digest()`. `:751` pins `old_commit =
  wide_from_felt(initial_vm_state.state_commitment)` — the fiction's commitment — and `:752` reads
  `new_commit` from `pi` that `:739 generate_effect_vm_trace(&initial_vm_state, ...)` derived from that
  same fiction. `verify_full_turn` at `:766` therefore closes a loop the host drew both ends of.
  **Nothing ever compares the proven `new_commit` to the executor's real post-state cell**:
  `blocklace_sync.rs:5041-5042` only LOGS them, and `:6338` sets
  `execution_proof_new_commitment: None`.
- **The file names the exact hazard 20 lines above and fixes it only under `Some(rot)`** —
  `turn_proving.rs:722-726`: "`initial_vm_state` must carry the REAL cell's
  balance/nonce/fields[0..8]/cap_root, NOT a synthetic zero-field `CellState::new`, else a
  field-bearing / cap-holding cell's rotated OLD_COMMIT would attest **a fictional zero-field cell that
  a light client re-deriving from the real cell could never reproduce** (an ARGUS regression)".
- **LIVE? YES** (`blocklace_sync.rs:5018` is the live commit-path prover) — but NARROWER than first
  filed. Four routes to the `None` arm:
  1. `:5016 _ => None` with `full_turn_pre_cell` absent (`:4404`) — a genuinely fresh cell;
     `full_turn_pre_state` is `(0,0)` via `.or(Some((0,0)))` at `:4395`. **HONEST** — a fresh cell really
     is zero-field/empty-cap-root. Not a defect.
  2. `:5016` with `s.ledger.get(&signed_turn.turn.agent)` (`:5001`) absent POST-execution — a
     `CellDestroy` of a field-bearing/cap-holding cell. **REAL fiction.**
  3. `turn_proving.rs:456-460` balance/nonce disagreement — the inversion stated out loud: `:453-455`
     says a disagreeing capture "would mis-pin OLD_COMMIT, so refuse → the byte-identical v1 leg runs",
     routing the known-inconsistent capture to the leg that pins OLD_COMMIT from that very capture.
     Defensive gate, should never fire.
  4. `turn_proving.rs:486-492 !all_cohort` — **most reachable.** A `[NoOp]`-only projection (a
     cross-cell turn not touching the actor; `convert_effects_to_vm` injects the NoOp sentinel per
     `:694-696`). Over any field-bearing/cap-holding actor this publishes old/new commits of a fictional
     zero-field cell. `:700-704` defends the ROUTING without noticing it is proving a no-op of the WRONG
     CELL.
  **REFUTED premise:** "every non-graduated effect" is FALSE at HEAD —
  `circuit/src/effect_vm/trace_rotated.rs:2680-2683` ("The residue is EMPTY: every LIVE selector
  resolves above. NoOp and unknown selectors fail closed"); Custom and RevokeCapability were the last two
  to graduate (`:2671-2680`), SetField routes by index (`:2709`). Route 4 is NoOp-only.
- **Why not critical:** full-turn proving is OFF by default (`--prove-turns` / `DREGG_PROVE_TURNS=1`,
  `blocklace_sync.rs:4765-4769`), devnet-only; the fabricated commitments are inert downstream; and
  (balance, nonce) — the value-bearing scalars — ARE carried truthfully, so no false balance transition
  is provable. The fiction is in fields/cap_root/record_digest. **Unsound-as-documented rather than
  exploitable-for-value — and un-exploitable partly because it is inert, which is not the same as being
  correct.**
- **FIX** — the `Some(rot)` arm already does the right thing via `RotationTurnWitness::before_cell_state`
  (`sdk/src/full_turn_proof.rs:294-324`: balance from welded limbs, `fields` from `pre[4+i]` verbatim,
  `capability_root = pre[B_CAP_ROOT]`, `record_digest = pre[B_AUTHORITY_DIGEST]`). Mirror it:
  1. Add `pre_cell: Option<&dregg_cell::Cell>` to `prove_and_verify_finalized_turn`; pass
     `full_turn_pre_cell.as_ref()` at `blocklace_sync.rs:5018` — it is **already cloned pre-execution at
     `:4404` for exactly this purpose**, so no new capture is needed.
  2. `None` arm: when `pre_cell` is `Some(cell)`, build via
     `CellState::with_capability_root_and_record_digest(pre_balance, pre_nonce as u32,
     full_turn_pre_cap_root, dregg_cell::compute_authority_digest_felt(cell))` **and then populate
     `fields[0..8]` from the cell's real folded field felts** (`fold_bytes32_to_bb`, the same felts the
     rotated welds use per `:447-448`) — NOT the `[BabyBear::ZERO; 8]` that
     `with_capability_root_and_record_digest` leaves at `cell_state.rs:97`. `full_turn_pre_cap_root` is
     already captured at `blocklace_sync.rs:4422-4425`.
  3. Keep `CellState::new(pre_balance, pre_nonce)` ONLY where `pre_cell` is genuinely `None` (route 1,
     the fresh cell) — and say so in the comment.
  4. Close the verify loop: compare the proven `new_commit` against a commitment independently
     recomputed from the executor's REAL post-state cell (`s.ledger.get(...)` at `:5001`) and **gate
     acceptance on the match**.
  5. Docs: correct `:40-41` to say `old_commit` is the real cell's commitment ONLY on the rotated arm;
     add the v1-synthetic exception to the `:4-6` headline; soften `blocklace_sync.rs:4732-4737`; delete
     the stale gate comment at `blocklace_sync.rs:4996-4998` that `turn_proving.rs:449-455` superseded
     ("The gate therefore stops being 'is this cell PRISTINE?'").
- **CANARY** — alongside `flow_b_non_synthetic_cell_proves_rotated` (`turn_proving.rs:1723`): a
  field-bearing cell with a `[NoOp]`-only actor projection must produce an `old_commit` equal to the
  REAL cell's `compute_commitment`, asserting the light client's re-derivation reproduces it. **That
  test fails today.**

---

## VARIANT C — fixture-on-live-path
*The real primitive exists and is tested; the loop calls a faucet/self-read next to it.*

### M05 — the adventure loop mints its "loot" from a faucet while the real vault is driven only in a test · **HIGH**

- **CLAIM** — `dreggnet-adventure/src/lib.rs:34-35`, step 5 of THE LOOP: "the run's loot drops as owned
  **assets** (`dungeon_on_dregg::loot` — **a real fair draw bound to the run's committed day-seed**)" ·
  `loot_seed`'s doc `:239-240` "Used **both** as the fair-draw context for the `dungeon_on_dregg::loot`
  vault and as the mint seed of the forge's material drops" — the first conjunct is false on every path
  in the crate · `Cargo.toml` "`dungeon-on-dregg = { path = "../dungeon-on-dregg" } # loot.rs — the run's
  fair-drop loot as owned assets`" · `AdventureReport::summary_lines` (`:566`) prints "The loot forged a
  relic and traded to {}".
- **TRUTH** — `lib.rs:292-296` `let m1 = forge.mint_material(who.holder_label(), RELIC_MATERIAL_KIND,
  &loot_seed(run, 1)); let m2 = forge.mint_material(..., &loot_seed(run, 2));` — two materials conjured
  by an unearned faucet, then forged. No drop, no roll, no reverify. `LootVault`/`roll_drop`/
  `reverify_drop` appear exactly once outside tests: the `#[cfg(test)]` import at `lib.rs:906`. The only
  uses are `lib.rs:1169-1178`, where `vault` and `item` never leave the test — a second `AssetWorld`
  that dies at end of test while the live relic comes from the forge's ledger.
- **LIVE? YES** — `Adventure::play` → `forge_run_loot` (`lib.rs:808`), the crate's flagship public API.
  **The faucet is ON the live path; the real thing is what sits off it.**
- **The crate maintains a real placeholder register and this was filed on the wrong side of it.**
  `NAMED RECONCILIATIONS` (`lib.rs:64-77`) lists the aid cells vs. the Descent world-cell, and the tavern
  front. Loot is NOT there — it is in `WIRED + DRIVEN` (`lib.rs:57-62`): "the looted note crafting +
  trading as the SAME note-cell." That is the difference between a labeled inadequacy and a false claim.
- **THE FACT THAT SETTLES IT** — `CraftForge::mint_loot_material(player, kind, &LootDraw)` **already
  exists** at `dreggnet-craft/src/forge.rs:243-264` — same struct, same forge, **same ledger the live
  path already holds**. It calls `reverify_drop` and refuses a forged drop with `CraftError::ForgedLoot`
  before minting, and binds loot_seed + roll + rarity + chest into the material's content address. Its
  own doc: "so the material is provably a real dungeon drop, not a demo faucet. This is the input side
  wired to the real economy." Its only callers are `dreggnet-craft/tests/forge.rs:407-446`. **The real,
  fair-draw-gated loot input was BUILT, documented, and tested — and the flagship loop calls the faucet
  next to it.** This also kills the sympathetic reading that wiring was blocked on a cross-crate
  reconciliation: it is a two-line call swap into a method that already exists in a crate already in
  `Cargo.toml`.
- **FIX — point at `CraftForge::mint_loot_material`, NOT at `LootVault::claim`.** This correction
  matters: `LootVault` owns its own private `AssetWorld` and exposes no `into_assets()` (unlike
  `CraftForge::into_assets`, `forge.rs:223`), so wiring the test's vault in would mint in a SECOND ledger
  and break the object-identity spine `lib.rs:49-53` and the `forge.into_assets()` →
  `TradeWorld::with_assets` handoff at `lib.rs:809` depend on. `mint_loot_material` mints into the
  forge's OWN world, so the existing trade leg keeps working verbatim. In `forge_run_loot`
  (`lib.rs:282-307`):
  1. Non-test import: `use dungeon_on_dregg::loot::roll_drop;`
  2. Replace `lib.rs:293-294` with:
     ```rust
     let d1 = roll_drop(&run.day().seed, "boss:the-warden", 1);
     let d2 = roll_drop(&run.day().seed, "boss:the-warden", 2);
     let m1 = forge.mint_loot_material(who.holder_label(), RELIC_MATERIAL_KIND, &d1)
         .map_err(|e| format!("the run's first drop did not source: {e:?}"))?;
     let m2 = forge.mint_loot_material(who.holder_label(), RELIC_MATERIAL_KIND, &d2)
         .map_err(|e| format!("the run's second drop did not source: {e:?}"))?;
     ```
     `roll_drop(&run.day().seed, ..)` binds to the committed day-seed — exactly what `:34-35` claims.
     `mint_loot_material` runs `reverify_drop` internally, so **the refusal tooth now sits on the live
     path, not only in a test.**
  3. `forge_run_loot`'s own doc (`:276-281`) is candid today ("the fair-draw-seeded material faucet") —
     which is precisely why the crate-level claim reads as a lie: **the honest word existed and was not
     used where it counts.** Drop it once the drop is real.
  4. `loot_seed`'s doc (`:237-240`): `roll_drop` derives its own seed via `derive_loot_seed(run_seed,
     chest, seq)`, so `loot_seed` is NO LONGER the vault's fair-draw context. Narrow the doc to the
     craft-seed role it actually has, or delete `loot_seed` if step 2 leaves it unused. **Do not leave
     the "used both as" claim standing.**
- **CANARY** — retire the parallel-lane test: `the_runs_loot_drops_as_owned_assets` (`lib.rs:1166-1193`)
  must assert against the drop the LIVE path takes, not a vault it builds itself. Keep the forged-drop
  refusal leg (`:1186-1192`) but aim it at `forge.mint_loot_material` with a rewritten `roll`, so the
  tooth guards production. Add an assertion in the `Adventure::play` test that the relic's lineage
  traces to a `reverify_drop`-passing `LootDraw`.
- **If step 2 is not taken:** MOVE loot out of `WIRED + DRIVEN` into `NAMED RECONCILIATIONS`, strike the
  `dungeon_on_dregg::loot` path reference from `:34-35`, and say the forge mints materials from a
  run-bound seed. But `mint_loot_material` already exists and is already tested — there is no reason to
  take the doc fix over the real fix.

### M08 — automatafl's `Offering::verify` calls a host self-read "translation validation" · **medium**

- **CLAIM** — `dregg-automatafl/src/surface.rs:866-868`: "Re-verify the committed match: the executor's
  COMMITTED board must be exactly the reference board (**translation validation — the substrate
  reproduces the game**)."
- **TRUTH** — `surface.rs:325-326` (`state()`) sets `auto: self.board.auto, cells:
  self.board.cells.clone()`; `game.rs:377` (`commit_state`) lowers that to `SetField` effects;
  `game.rs:420-436` (`read_state`) reads those same slots back. So `verify`'s `committed.cells !=
  session.board.cells` (`surface.rs:872`) compares the cell's echo against the very Vec that produced it
  — **x == x modulo executor storage**. Failure modes are only (a) `SetField` losing data, or (b) an
  out-of-band `commit_raw` write via the pub `session.game()` accessor (`surface.rs:203` →
  `game.rs:382`), a narrow class no frontend exercises. The residual checks are likewise self-reads:
  `cells.iter().any(|&p| p > AUTO)` (`:878`) re-checks a tooth the executor already enforced on that same
  write (`board_particles`, `HeapAtom::MemberOf{0,1,2,3}`, `game.rs:158-166`); the one-automaton and
  automaton-placement checks read the host's own `apply_turn` output.
- **Three independent confirmations:**
  1. **The trait contract claims the real thing.** `dreggnet-offerings/src/lib.rs:485`: "Re-verify the
     session's committed chain (by replay / the offering's own proof)." The peer impl under the SAME
     trait, `dungeon.rs:348-358`, does exactly that: `verify_by_replay(deploy_keep(session.seed),
     &session.scene, &session.playthrough())` — a replay into a FRESH world from genesis
     (`spween-dregg/src/verify.rs:123-148`). Automatafl's verify never replays, never reaches genesis,
     never touches a receipt chain. **This impl diverges from its own trait's idiom.**
  2. **`game.rs`'s own module header refutes `surface.rs:866-868`.** `game.rs:29-31`: "The BOARD
     TRANSITION itself (`new == apply_turn(old, moves)`) is re-checked **off-circuit** by
     `crate::reference::apply_turn` … the executor teeth are the state discipline, the AIR is the
     transition proof." The deployed `CellProgram` (`game.rs:168-232`) is `Cases` of `StateConstraint`s
     (Immutable/StrictMonotonic/WriteOnce/MemberOf/FieldLte) — it never computes `apply_turn`. **The
     substrate STORES the game; it does not reproduce it.**
  3. **The session retains NO receipt chain.** Receipts are handed to the caller and dropped
     (`surface.rs:712, 759, 790, 840` — no field on `AutomataflSession`, `:136-167`). So
     `VerifyReport::ok(turns)` reports `session.turns`, a counter the host increments in its own arms,
     versus dungeon's `session.receipts_len()` (`dungeon.rs:349`). **The reported turn count is
     self-attestation too.**
- **LIVE? YES** — `host.rs:244` dispatches `Offering::verify`, and `host.rs:554` folds `report.verified`
  + `report.turns` into `commitment()`, the session fingerprint the resume closure asserts against.
- **The pinning nuance:** the phrase is EARNED at `tests.rs:445-450`, where `expect = apply_turn(&board,
  &[ma, mb])` is recomputed INDEPENDENTLY by the test and compared to `read_state()`. The phrase was then
  copied onto `verify`, where the second independent derivation is absent — `session.board` is the
  executor's INPUT, not a peer re-derivation.
- **FIX** — point `verify` at a REPLAY (mirror `dungeon.rs:348-358`):
  1. Give `AutomataflSession` a retained chain — the `TurnReceipt`s currently dropped at
     `surface.rs:712/759/790/840`, plus the per-turn (method, seat, action) log.
  2. `verify` re-derives **without ever reading `session.board`**: deploy a fresh
     `AutomataflGame::deploy(session.seed)` + seed genesis; re-drive every recorded action through the
     real executor in order (the teeth re-run on replay, so a spliced/reordered/ineligible action is
     refused — non-vacuous); recompute each resolution independently from `opening_board()` via
     `reference::apply_turn`, threading the replayed board forward; require the REPLAYED final cell state
     == the recorded committed state (**this is the comparison that is currently x == x; after the change
     the two sides have genuinely different provenance**); verify receipt-chain linkage
     (`prev_hash → turn_hash`) so a retconned turn breaks the chain.
  3. Reuse the existing machinery: `SessionMoveLog` + `OfferingHost::resume` (`host.rs ~540-570`) already
     replays a move log through the real executor and is fail-closed on tamper. Lean on that shape rather
     than inventing a second one.
  4. `VerifyReport::ok(turns)` must count the retained chain (`session.receipts.len()`), not
     `session.turns`.
  5. **Fix the doc now, regardless of when the above lands.** `surface.rs:866-868` must state what it
     checks, in the register `game.rs:29-31` already uses honestly: the executor's storage round-trips
     the committed write, and the reference's invariants hold on it — the TRANSITION proof is the AIR,
     the executor teeth are the state discipline. **Keep "translation validation" where it is earned:
     `tests.rs:445-450`.**
- **Scope discipline:** NOT a soundness hole in the substrate. The executor teeth, the AIR transition
  proof, and the host-level move-log replay in `resume` all carry real weight and are unaffected. What is
  false is the CLAIM on the attestation surface, and the near-vacuity of the check behind it.

### M02 — the multislot set bonus fires because the set is EQUIPPED, never because it is OWNED · **medium**

- **CLAIM** — `dreggnet-gear/src/multislot.rs:115`: "**Ownership is enforced at the asset layer when the
  set bonus is claimed.**" · `:25-27` "REAL + DRIVEN: the slot-distinct multi-piece loadout, the
  multi-peer set-bonus conjunction … and **per-piece owned-asset gear**." · `lib.rs:26-27` "Your loadout
  is provable and un-dupable; 'own AND equip to use' is enforced ACROSS cells by the kernel" (true of
  `gear::Loadout`, false of the multislot loadout).
- **TRUTH** — `prove_ownership` appears **zero** times in `multislot.rs`; every `Armory` reference in the
  file is inside `#[cfg(test)] mod tests` (`:388, :391, :416, :450, :487`) and only calls
  `armory.forge(...)`. `SetBonusGate::equip` (`:304-315`) stamps the gear cell with no ownership check;
  `use_set_bonus_with` (`:338-364`) composes set_field effects + `peer_finalized_witness` blobs and calls
  `issue` — zero asset-layer contact. **The promised deferred check does not exist at the promised
  place.**
- **THE STRUCTURAL PROOF (stronger than the grep): the check is not merely omitted, it is
  unreachable.** `MultiLoadout::equip_piece` (`:116`) takes `gear: Gear` by value with **no holder
  label**. `SetBonusGate` (`:257-265`) holds exec/cclerk/driver/slots/gear_cells/run_cell/gate_roots — no
  `Armory`, no holder identity. `SetBonusGate::deploy` (`:270`) takes only `Vec<(GearSlot, Gear)>`, and
  `Gear` (`gear.rs:98-104`) is a Copy `{asset_id, stats}` with no ledger handle. **Nothing in the
  multislot world can call `Armory::prove_ownership` even in principle.**
- **LIVE? The multislot path IS the mirror — it has no other.** `multislot` is `pub mod` at `lib.rs:36`,
  re-exported at `lib.rs:42`; `dreggnet-gear/tests/integration.rs:123-135` (`a_full_loadout_fires_its_set_bonus`) does
  `let gate = lo.deploy_set_bonus(); gate.equip(0/1/2); gate.use_set_bonus()` — the armory that forged
  the pieces is never consulted again. `multislot.rs:19-20` states it IS `gear.rs:48`'s named set-bonus
  residual "now built" — the delivered artifact, not scratch.
- **The strongest refutation, and why it fails:** `EquipGate::equip` (`gear.rs:436-446`) is ALSO
  ownership-free and public, and `Loadout.gate` is a pub field — so the bare inner tooth exists on the
  single-gear side too, **by design**, and `SetBonusGate::equip` is its faithful multi-cell analogue. The
  refutation dies on what is MISSING ABOVE it: gear.rs ships the **composing type** —
  `Loadout::equip` (`gear.rs:569-575`) does `prove_ownership(...).map_err(EquipError::NotOwner)?` THEN
  `self.gate.equip()`, proven non-vacuously in `a_non_owner_cannot_equip` (`gear.rs:648-679`: Mallory
  refused, ability stays locked, anti-ghost asserted). multislot ships **no such type, no
  `EquipError::NotOwner` analogue, and no non-owner test** — while `:115` asserts the composition
  happens anyway.
- **Provenance of the lie:** `gear.rs:225` carries "(Ownership is enforced at the ASSET layer, above.)"
  where it is TRUE, because `Loadout::equip` exists above it. `multislot.rs:115` inherited the sentence
  without the mechanism.
- **What IS real (do not touch):** the multi-peer `ObservedFieldEquals` conjunction (`:194-209, :338-364`)
  is genuinely fail-closed — partial-set refusal, stripped-witness fail-closed, divergent-value refusal
  at `:449-511`, all with anti-ghost assertions. Slot distinctness is real. **Only the OWNERSHIP leg is
  fictional.**
- **FIX — build multislot's missing composing type, pointing at the SAME tooth `gear.rs:569-575` uses**
  (reuse `gear::EquipError`; do not mint a parallel error):
  ```rust
  pub struct OwnedSet { pub armory: Armory, pub gate: SetBonusGate,
                        pieces: Vec<(GearSlot, Gear)>, holder: String }
  impl OwnedSet {
      pub fn deploy(armory: Armory, pieces: Vec<(GearSlot, Gear)>, holder: &str) -> Self { ... }
      /// Equip piece `which` as the holder — the "own AND equip" conjunction, exactly
      /// gear.rs:569-575's shape: prove asset ownership FIRST (a non-owner is refused
      /// cryptographically, nothing stamped), only THEN stamp the gear cell.
      pub fn equip(&mut self, which: usize) -> Result<TurnReceipt, EquipError> {
          self.armory.prove_ownership(&self.pieces[which].1, &self.holder)
              .map_err(EquipError::NotOwner)?;
          self.gate.equip(which).map_err(EquipError::GateRefused)
      }
      pub fn equip_all(&mut self) -> Result<(), EquipError> { ... }
  }
  ```
  `MultiLoadout::deploy_set_bonus` (`:151-153`) becomes `pub fn deploy_set_bonus(self, armory: Armory,
  holder: &str) -> OwnedSet` (consuming self; the pieces move into the owned set). Keep bare
  `SetBonusGate::deploy` as the un-owned inner layer with an explicit doc line ("the inner tooth; use
  `OwnedSet` for the own-AND-equip conjunction" — the same relationship `EquipGate` has to `Loadout`).
  Wire the drive path: `dreggnet-gear/tests/integration.rs:123-135` must go through `OwnedSet::equip`.
- **CANARY** — mirroring `a_non_owner_cannot_equip` (`gear.rs:648-679`):
  `a_non_owner_cannot_fire_the_set_bonus` — forge the 3-piece set to "alice", deploy `OwnedSet` with
  holder "mallory"; `matches!(set.equip(0), Err(EquipError::NotOwner(_)))`; `!set.gate.is_equipped(0)`
  (nothing stamped); `set.gate.use_set_bonus().is_err()`; `!set.gate.set_bonus_active()` (anti-ghost);
  then "alice" equips all 3 and `use_set_bonus()` commits — **the ownership the only pivot. Without that
  last arm the test is satisfied by the already-existing partial-set refusal and proves nothing new.**
- **DOCS (mandatory and immediate, ahead of the code):** `:115` DELETE the sentence → "This files a
  piece; it does NOT check ownership — nothing on the multislot path does (see the named residuals)."
  `:24-26` move ownership OFF the REAL + DRIVEN line ("the pieces are real forged assets, but no
  multislot path proves ownership — the own-AND-equip conjunction `gear.rs`'s `Loadout` performs has no
  multi-piece analogue yet"). `:26-29` add ownership as the **FIRST** named residual, ahead of the
  incremental re-pin and cross-node channel. `lib.rs:26-27` scope the sentence to the single-gear path.

---

## VARIANT D — host-vs-proven
*A host-side data structure or host-side evaluation standing where the doc says the executor's
re-checked gate stands.*

### M06 — the guild leaderboard's "cap set" is a `HashSet` · **medium**

- **CLAIM** — `dreggnet-guild/src/leaderboard.rs:19-21`: "And **the roster IS the cap set**: only a
  member's clears count. A clear recorded for a non-member is refused (`ClearError::NotAMember`)" ·
  `:36`/`:48-50` calls it "**the cap-set tooth, at the board**" · `lib.rs:8` headlines "**Membership IS
  the capability set**" (also the `Cargo.toml` description) · `dreggnet-guild/tests/guild.rs:169` comments "only the cap
  set counts" over an assertion that exercises a HashSet miss.
- **TRUTH** — `leaderboard.rs:76` `members: HashSet<DreggIdentity>`; the gates at `:109` and `:131` are
  `self.members.contains(who)` — a HashSet lookup. `leaderboard.rs:23-29` imports **no `World`, no
  `CellId`, no `capabilities`**; the string does not appear in the file. Populated solely by `pub fn
  enrol` (`:88-90`), whose only in-tree caller is `Guild::admit` (`lib.rs:167`) — **a sync maintained by
  convention, not by type.** The real tooth exists and is real: `lib.rs:162-164`
  `cell.capabilities.grant(self.guild_cell, AuthRequired::None)` is a genuine grant into the world
  ledger, `act_on_guild` (`lib.rs:200-216`) drives a real turn the executor re-checks, and
  `install_stranger` (`lib.rs:174-179`) yields a real `CapabilityNotHeld` refusal. **It just does not
  stand between anyone and the leaderboard.**
- **The board is a mirror of a mirror:** `Guild::is_member` (`lib.rs:182`) is ALSO a bare
  `self.members.contains_key(who)` HashMap hit. **Caps are consulted ONLY on `act_on_guild`.**
- **LIVE? The board is the live path for every aggregate.** `Guild::stats()` → `board.stats()`
  (`lib.rs:239`) is the key `rank_guilds` orders (`versus.rs:44-67`), and every composing crate reaches
  it via `board_mut()` — the same pub door that exposes `enrol` (`dreggnet-adventure/src/lib.rs:781,
  1221, 1488, 1540`; `dreggnet-saga/src/lib.rs:347, 589, 682`; `dreggnet-surfaces/src/guild.rs:184,
  190`). **The cap-checked `act_on_guild` path is exercised only by the guild's own test.**
- **NOT an escalation (severity corrected down).** `Guild::admit` (`lib.rs:156`) is an ungated `pub fn`,
  so any caller who can reach `board_mut().enrol(stranger)` can equally call `admit(&stranger)` and get a
  genuine cap grant. The divergence crosses no trust boundary `admit` does not already stand open on. The
  no-cheat tooth (`verify_completion`, `leaderboard.rs:114`) is real and genuinely gates the aggregate,
  so the sum only ever includes executor-re-verified clears. **What is broken is the headline claim plus
  a real API hole: two independent membership structures with a convention-only sync invariant, and a
  `pub enrol` reachable via `pub board_mut` that lets a caller put a cap-less identity on the counting
  roster. Every test passes because no test attempts the divergence.**
- **FIX — make the board's membership gate consult the SAME capability the executor re-checks:**
  1. **DELETE** `GuildBoard::members` (`:76`) and `pub fn enrol` (`:88-90`) outright. There is no fixing
     the HashSet in place: `GuildBoard` structurally cannot see the world.
  2. Move the membership verdict to where the caps live. Replace the `self.members.contains(who)` gates
     (`:109`, `:131`) with a `membership: bool` — better, a `Membership` **witness token** that
     `record_clear`/`record_survivor` receive as an argument and **cannot forge**, minted only by `Guild`.
  3. `Guild` derives that verdict from the REAL cap. **Best:** drive a genuine cap-bounded turn —
     `self.act_on_guild(member_cell)` — and mint the witness only on `CommandOutcome::Committed`,
     treating the `CapabilityNotHeld` refusal as `ClearError::NotAMember`. That makes the leaderboard's
     tooth literally the executor re-check the doc claims it is. **Weaker but acceptable:** look the cap
     up in the ledger — `self.world.ledger().get(&member_cell)` then scan `cell.capabilities.refs` for
     `target == self.guild_cell` (the grant at `lib.rs:162-164`; `CapabilitySet::grant` is
     `cell/src/capability.rs:345`, refs at `:362`).
  4. **Close the door.** Drop `pub fn board_mut` (`lib.rs:233`); give `Guild` delegating methods
     `Guild::record_clear(&mut self, who, universe, completion)` / `Guild::record_survivor(&mut self, who,
     sheet)`. Migrate the seven call sites listed above. Keep `pub fn board(&self)` for reads. Fix
     `Guild::is_member` (`lib.rs:182`) the same way, or rename it `is_on_roster` and stop calling the
     HashMap a cap check.
- **CANARY (without it none of this is verified)** — revoke / never grant the guild cap to a cell whose
  identity IS in `Guild::members`, record a GENUINELY verified winning completion for it, assert
  `stats().verified_clears` **does not move**. **That test must be RED against today's code.** It is the
  exact case the current suite never attempts. Add the falsifier that no path can add to the counting
  roster without a cap grant landing in the ledger.
- Until 1-5 land, the doc must describe current resolution and the divergence belongs in `lib.rs:51-63`'s
  named-residuals list — which is exactly where it should have been all along.

### M09 — `apply_choice` commits without ever evaluating the condition · **medium**

- **CLAIM** — `spween-dregg/src/world.rs:331-336`: "the whole thing is a single signed action **the real
  executor admits IFF the choice's installed gate case passes**. An ineligible or forged pick is a
  `WorldError::Refused` (nothing commits)." · `lib.rs:14-17` "advancing the story (`WorldCell::apply_choice`)
  is ONE verified turn that the real executor admits IFF the choice's gate passes. **Nobody can forge a
  move or take a choice they are not eligible for.**" · `lib.rs:34-36` lists as a TOOTH "a condition-gated
  choice is UNAVAILABLE when its gate fails — enforced as a cell-program predicate the executor
  re-checks". **All three unconditional.**
- **TRUTH** — `world.rs:340-349` `apply_choice` is three lines: `choice_method` → `choice_effects` →
  `commit`. **No condition is evaluated.** `commit` (`:484-497`) only does `make_action` →
  `submit_action` → federation route. The runtime is never touched, so `CellHandler::get_var`/`has`
  (`:546-597`) — the host-side overlay gate — **is not on this path at all**. And
  `compiler.rs:444-458` pushes the `TransitionCase` with `constraints` **regardless of `full`**; `full` is
  only recorded into the `fully_gated` map (`:451`). The bail-outs are real: `lower_clause` `:683-686`
  (`Delta::Overwritten => return None` — a gate var the same choice `Set`s), `:682`
  (`numeric_value(&c.value)?` — string/float RHS), `:673`/`:679` (unknown var), `:910`
  (`lift_defeated_by_clamp` under Or/Not), plus the cross-var negative-delta bail. A sole-clause failure
  gives literally `constraints: []` — **the executor's `MethodIs` case is satisfied by dispatch alone.**
- **The label EXISTS and is honest; the higher-altitude docs dropped it.** `compiler.rs:76-79`: "that
  clause is left to the runtime/handler gate and no executor constraint is emitted for it";
  `CompiledStory::fully_gated`'s doc (`:276-279`): "whether the gate lowered FULLY to executor constraints
  (`true`) or leans on the runtime/handler for some clause (`false`)". **A labeled placeholder that a
  higher-altitude doc asserts as closed is the sin, not the label.**
- **LIVE?** `Driver::advance` (`world.rs:787`) DOES run `select_choice` through the overlay, and
  `verify_by_replay` re-drives it, so the record-level tooth survives. But `apply_choice` is
  independently LIVE and **advertised as the referee**: `demo/real-dungeon-service/src/main.rs:103`
  "This service drives the executor directly via `apply_choice` (**the executor as sole referee**,
  bypassing the client runtime)" and `:309-313` "`apply_choice` is the primitive where the executor is
  the SOLE referee: an ineligible/forged pick is refused in-band by the installed `CellProgram` gate
  case, and nothing commits (anti-ghost)." Also driven at `dreggnet-offerings/src/daily_descent.rs:564`,
  `dreggnet-offerings/src/dungeon.rs:296`, `dreggnet-faction/src/lib.rs:512`,
  `dreggnet-quest/src/lib.rs:541`. **For a `fully_gated == false` choice every one of those comments is
  false.**
- **Corroboration that the author knows:** `dreggnet-offerings/tests/daily_descent_driven.rs:122-124`
  states outright "The live turn (`apply_choice`) **never evaluates the spween condition** — the executor
  checks the lifted tooth `FieldLte(heals_used, 1)` on the slot". `dungeon-on-dregg/src/lib.rs:1221-1225`
  hand-augments the vault program with "the two shapes the v0 compiler does not emit" (WriteOnce,
  FieldLteField) — **the gap is patched per-scene by the scene author, not structurally by the
  compiler.** `compiler.rs:909-911` even says "No consumer gates such a var behind an `Or`/`Not`" — an
  appeal to current scene content, not to an enforced invariant.
- **Severity is medium, NOT an exploitable bypass — verified by sweep.** Every gated choice in the tree
  (`grep -rhE '^\* \[[^]]*\] \{'`): `{alert <= 1 && cage_open >= 1}`, `{disposition >= 4}`,
  `{ember_quest >= 1}`, `{gold >= "$price"}`, `{gold >= 100}`, `{gold >= 50}`, `{hands >= 2}`,
  `{has_lantern >= 1}`, `{hp <= "$cap"}`, `{hp <= 20}`, `{hp >= 16}`, `{hp >= 21}`, `{hp >= 31}`,
  `{inventory.key}`, `{key_owner >= 1}`, `{passage_open >= 1}`, `{perception >= 10}`,
  `{r01 >= "$z_price"}`, `{relics.sigil}`, `{rep_embers < "$embers_ceiling"}`. **No `!=`, no string/float
  RHS, and no gated choice that `Set`s its own gate var** (the `~ key_owner = 1` / `~ relic_owner = 1` /
  `~ draughts_held = 1` Set-choices carry NO condition, so `lower_gate` hits the `condition.is_none()`
  arm at `:610-612` and returns `(vec![], true)` — trivially, correctly, fully gated). So the headline
  scenario (`* [Buy] { gold >= 50 } ~ gold = 0` commits on an empty purse) is **reachable through the
  public API and the demo service but not tripped by any shipped scene today. A false unconditional claim
  + a silent trapdoor that disarms the next author's gate with zero signal.**
- **FIX (PRIMARY — structural, fail-closed; `WorldCell` already holds the `Arc<CompiledStory>` and just
  never consults it):** in `apply_choice` (`:340`) and `apply_choice_certified` (`:361`):
  ```rust
  let method = choice_method(passage_name, choice_index);
  if self.story.fully_gated.get(&method) == Some(&false) {
      return Err(WorldError::UngatedChoice { method });   // new variant
  }
  let effects = self.choice_effects(choice)?;
  self.commit(&method, effects)
  ```
  `fully_gated` is `Absent ⇒ ungated` / `Some(true) ⇒ full teeth` / `Some(false) ⇒ handler-only` — only
  the third is the hazard. **`apply_choice` then admits a turn IFF the executor's installed case is the
  WHOLE gate, and the doc sentence becomes literally true.** A handler-only gate is forced onto the
  `Driver` path (`:787 select_choice`), the only path that actually evaluates it. Fail-closed, per the
  FAIL-OPEN LAW framing already used at `:487-495` for the federation seam.
- **CANARY** — a scene with `* [Buy] { gold >= 50 } ~ gold = 0` must (a) compile with
  `fully_gated[buy] == false` and (b) get `WorldError::UngatedChoice` from `apply_choice` **on a FULL
  purse** — i.e. the refusal is not incidentally caused by the empty purse.
- **SECONDARY (raise the resolution so fewer choices need refusing):** the `Delta::Overwritten` bail
  (`:683-686`) is over-conservative. When a choice `Set`s its gate var to a compile-time constant the
  pre-state gate is not liftable through the post-state, but IS expressible as a pre-state read if the
  constraint vocabulary has an old-state atom (the `FieldDelta`/`DeltaEquals` companion at `:60` already
  proves the executor can see pre-vs-post). A `FieldOldGte { index, value }` atom lowers
  `{ gold >= 50 } ~ gold = 0` to a real tooth and shrinks the `fully_gated == false` set toward empty.
  v1-compiler item; **the PRIMARY fix is what makes v0 honest.**
- **DOCS (mandatory if PRIMARY is deferred):** `world.rs:331-336` qualify ("A gate the v0 compiler cannot
  lift to a post-state predicate installs an EMPTY case: for such a choice — exactly those with
  `CompiledStory::fully_gated[method] == false` — this primitive commits WITHOUT checking the condition,
  and the gate exists only on the `Driver`/runtime path"); `lib.rs:14-17` drop "Nobody can forge a move
  or take a choice they are not eligible for"; `lib.rs:34-36` name `fully_gated` as the discriminator;
  `demo/real-dungeon-service/src/main.rs:309-311` "the executor is the SOLE referee" is true only because
  the Keep's gates all lower — say so, or let PRIMARY make it unconditionally true.

---

## VARIANT E — harness-tests-its-own-mirror
*The apparatus built to catch drift re-declares the artifact it is supposed to check. The single
highest-population variant, and the one that let the others ship.*

### M13 — the deployed `predicate-arith.json` is a 5-wide re-authoring of a 24-wide Lean descriptor, missing the fact weld · **CRITICAL**

- **CLAIM — three, at the dispatch site:**
  (a) `circuit/src/descriptor_by_name.rs:147` banner: "---- The byte-pinned emitted predicate-descriptor
  goldens (**verbatim from the Lean #guards**). ----"
  (b) `:169-173`: "The `>=` sibling above (`PREDICATE_ARITH_JSON`) **carries the Poseidon2 value↔fact
  weld**; these leaner comparison descriptors carry the same C1/C2/C3/C5/C6 comparison teeth with
  `fact_commitment` as the pass-through PI." — **a specific, load-bearing DISCRIMINATION whose sole
  purpose is to tell a reader ge is the welded one.**
  (c) `:34-40`: "Each predicate descriptor is emitted from Lean … and byte-pinned there by an
  `emitVmJson2` #guard; the identical string is proven+verified by its
  `circuit-prove/tests/*_emit_gate.rs`. The consts below embed those exact byte-pinned goldens
  (`circuit/descriptors/by-name/*.json`, **extracted verbatim**) … so a byte drift on either side breaks
  the Lean #guard, the emit-gate `assert_eq!`, or this module's `dispatch_names_decode_and_check` test."
- **TRUTH (verified at both ends; `python3 -c "import json; d=json.load(open('circuit/descriptors/by-name/predicate-arith.json')); print(d['trace_width'], len(d['constraints']))"` → `5 5`):**
  DEPLOYED bytes = `trace_width:5`, tables `[{id:2, range}]`, 5 constraints, **ZERO table-1 (Poseidon2
  chip) lookups**, 641 bytes:
  ```
  {"t":"pi_binding","row":"first","col":2,"pi_index":0}
  {"t":"pi_binding","row":"first","col":4,"pi_index":1}
  {"t":"gate",...}  // C3: slot_a - input = 0
  {"t":"gate",...}  // C5: diff - slot_a + threshold = 0
  {"t":"lookup","table":2,"tuple":[{"t":"var","v":3}]}   // C6: diff range
  ```
  LEAN `#guard` (`metatheory/Dregg2/Circuit/Emit/PredicatesArithmeticEmit.lean:183`) = `trace_width:24`,
  7 constraints, 1686 bytes — the same 5 PLUS the two weld lookups:
  ```
  {"t":"lookup","table":1,"tuple":[{"t":"const","v":7},{"t":"var","v":5},{"t":"var","v":0},...]}  // hash_fact(PREDICATE_SYM,[INPUT,..]) -> FACT_HASH
  {"t":"lookup","table":1,"tuple":[{"t":"const","v":2},{"t":"var","v":9},{"t":"var","v":8},...,{"t":"var","v":4},...]}  // hash_2_to_1(FACT_HASH, STATE_ROOT) -> col 4 = FACT_COMMITMENT
  ```
  `PRED_WIDTH := 24` (`:116`) is doc-derived as "5 predicate columns + 5 fact witness columns + 2×7 fact
  chip lanes"; `factHashLookup` (`:157`) and `factCommitLookup` (`:164`) carry the docstrings "**THE
  VALUE↔FACT WELD, leg 1 / leg 2**". The file contains exactly ONE `#guard emitVmJson2` and it is
  `predicateGeDesc`; `grep -rln predicate-arith-ge metatheory/` returns only this file. **No alternate,
  leaner Lean author of the 5-wide shape exists anywhere — the deployed bytes are Rust-side
  re-authorship.** Same wire name `dregg-predicate-arith-ge::threshold-v1` on both, so **the divergence
  is invisible by name.**
- **THE SOUNDNESS CONTENT, from the deployed constraint list itself.** Enumerate every constraint
  mentioning col 0 (INPUT) and col 4 (FACT_COMMITMENT): col 0 appears ONLY in the C3 gate (`var1 - var0`).
  col 4 appears ONLY in `{"t":"pi_binding","row":"first","col":4,"pi_index":1}`. **Their constraint sets
  are DISJOINT.** The deployed AIR is the free conjunction of (a) `col0 >= threshold`, proved via C3/C5 +
  the col-3 range lookup, and (b) `col4 == pi[1]`. **Nothing in the circuit relates col 4 to col 0.** A
  prover therefore satisfies `value >= threshold` on a value of its choosing while presenting the honest,
  verifier-expected `fact_commitment` for an UNRELATED value — even where the verifier sources `pi[1]`
  from trusted token state, the check only tests "this is the commitment I expected", never "this
  commitment covers the number that was compared". **The predicate proof does not bind to token state,
  and the docs at the dispatch site say it does.** The mitigation route is closed too:
  `compute_arithmetic_fact_commitment` is honest-prover Rust, not a constraint.
- **LIVE? YES — deployed.** `descriptor_by_name()` is the production predicate-dispatch registry
  (`descriptor_by_name.rs:9` calls itself "the production dispatch table"): `bridge/src/present.rs:1968`
  (`verify_wire_typed`, the fail-closed `UnknownAir` gate on the committed-wire verify path),
  `bridge/src/verifier.rs:38+135` (`verify_with_predicate`, documented as the "MIGRATED consumer
  contract … `descriptor_by_name(predicate)` → decode `postcard(Ir2BatchProof)` →
  `verify_vm_descriptor2` … NOT the legacy `stark::proof_from_bytes` path"), `wire/src/server.rs:33+4059`.
  `ge` is a registered `BridgePredicate` (`:267`). **The production witness builder
  `circuit/src/predicate_arith_witness.rs:63` hard-codes `pub const PRED_WIDTH: usize = 5;` — the LIVE
  prover/verifier pair is built against the mirror.** Cols 5..23 (PREDICATE_SYM, TERM1, TERM2, STATE_ROOT
  = col 8, FACT_HASH = col 9, FACTHASH_LANES 10-16, FACTCOMMIT_LANES 17-23) have **no Rust producer at
  all**.
- **THE HARNESS TESTS THE MIRROR'S OPPOSITE.** `circuit-prove/tests/predicates_arithmetic_emit_gate.rs:70`
  embeds its OWN literal `const GOLDEN_JSON: &str = r#"{..."trace_width":24...}"#` — a self-contained
  string; the file has **no `include_str!` and no `descriptor_by_name` reference** (every consumer is
  `parse_vm_descriptor2(GOLDEN_JSON)` at `:265, :312, :333, :361, :378, :396, :411, :428`). Its own
  `const PRED_WIDTH: usize = 24` (`:86`), `STATE_ROOT: usize = 8` (`:82`), `FACT_HASH: usize = 9` (`:83`)
  exist ONLY in the mirror's world; `:271 assert_eq!(decoded.trace_width, PRED_WIDTH)` compares 24 to 24.
  Its header (`:9-13`) claims "This test embeds that EXACT string … a byte drift on either side breaks
  this OR the Lean #guard" — **false as arithmetic: the deployed file is a THIRD side, pinned by
  neither.** It is green while exercising teeth the deployed descriptor does not have.
- **AND AN IN-CRATE TEST LOCKS THE MIRROR IN — the inverse of a canary.**
  `circuit/src/predicate_arith_witness.rs:157 predicate_arith_dispatches_with_expected_shape` reads the
  DISPATCHED descriptor and asserts `desc.trace_width == PRED_WIDTH` (5) and `range_lookups == 1` with
  the comment "the single diff range lookup (C6)". **This structurally RATIFIES the absence of the two
  chip lookups. Restoring the Lean descriptor turns this green test red — the mirror is defended by CI.**
  That same file's doc concedes the deployed truth ("There is no in-circuit hash tooth on
  FACT_COMMITMENT") while still claiming it "is dispatched … from the Lean-#guard-pinned golden" —
  **the two halves of one docstring contradict each other, and the second half is the false one.**
- **FIX — point the deployed bytes at the Lean #guard, then make every pin bite the deployed file:**
  1. **REGENERATE THE GOLDEN.** Replace `circuit/descriptors/by-name/predicate-arith.json` with the exact
     string from `#guard emitVmJson2 predicateGeDesc` (`PredicatesArithmeticEmit.lean:183-184`) —
     **emitted on the Lean host via `scripts/emit-descriptors.sh`, not hand-transcribed.**
     `descriptor_by_name.rs:168`'s `include_str!` then dispatches the real descriptor with zero call-site
     change. **This re-keys anything FP/VK-pinned to the stale bytes — route through the
     `DREGG_VK_REGEN_ACK` path in `docs/VK-REGEN-CONTROLS.md`.** The staged-registry TSVs are LFS-tracked
     (`circuit/descriptors/*staged*.tsv`); circuit-CI needs `lfs: true`.
  2. **LIFT THE PRODUCTION WITNESS BUILDER.** `predicate_arith_witness.rs:63` `PRED_WIDTH = 5` → 24; add
     the column consts mirroring Lean §1: `PREDICATE_SYM=5, TERM1=6, TERM2=7, STATE_ROOT=8, FACT_HASH=9,
     FACTHASH_LANES=10..=16, FACTCOMMIT_LANES=17..=23`. `predicate_arith_witness()` must take
     `(predicate_sym, term1, term2, state_root)` **instead of an opaque `fact_commitment: BabyBear`**,
     populate col 9 with the real arity-7 Poseidon2 chip image of `[PREDICATE_SYM, INPUT, TERM1, TERM2,
     0, FACT_MARK=64207, 1]` and cols 10..16 with its out-lanes 1..7, populate col 4 with the arity-2
     chip image of `[FACT_HASH, STATE_ROOT]` and cols 17..23 with its out-lanes, and RETURN
     `pis = [threshold, col4]`. **The fact commitment stops being an argument and becomes a computed
     output — which is the whole point.** Cross-check col 4 against
     `crate::dsl::predicates::arithmetic::compute_arithmetic_fact_commitment` with a KAT assert so the
     in-circuit chip image and the production out-of-circuit binding are proven equal.
  3. **FLIP THE IN-CRATE TEST FROM RATIFIER TO CANARY.** `predicate_arith_witness.rs:157`: assert
     `desc.trace_width == 24`, `range_lookups == 1` **AND `poseidon2_lookups == 2`** (filter on
     `TID_POSEIDON2`).
  4. **MAKE THE EMIT GATE PIN THE DEPLOYED FILE.** `predicates_arithmetic_emit_gate.rs:70`: delete the
     `r#"..."#` literal → `const GOLDEN_JSON: &str = include_str!("../../circuit/descriptors/by-name/predicate-arith.json");`.
     Its `:9-13` header claim only becomes TRUE once the string it decodes is the string production
     loads. Import its local `PRED_WIDTH`/`STATE_ROOT`/`FACT_HASH` from
     `dregg_circuit::predicate_arith_witness` rather than re-declaring, so the test cannot re-fork the
     layout.
  5. **ADD THE STRUCTURAL ANTI-FORK GATE.** In `descriptor_by_name.rs`'s
     `dispatch_names_decode_and_check`, assert for the `ge` name that the decoded descriptor carries
     `>= 1` `TID_POSEIDON2` lookup — **encode the `:171` doc claim as a check instead of prose.**
- **CANARY (the falsifier the mirror cannot pass and the real descriptor must)** — prove an honest witness
  for value=100/threshold=40 under state_root R, keep its (correct) pis, then re-prove with INPUT tampered
  to a different value while **holding col 4 at the original honest commitment** — assert REFUSED via the
  existing `rejects` helper. **Against today's deployed 5-wide bytes that test ACCEPTS; against the Lean
  descriptor it is UNSAT.**
- **DOCS, LAST — never as a substitute.** `:171` becomes true once (1) lands; leave it and let (5)
  enforce it. `predicate_arith_witness.rs:47-53`: DELETE the "There is no in-circuit hash tooth on
  FACT_COMMITMENT … no production hash-root a witness must reproduce byte-for-byte" paragraph — after (2)
  there is.
- **If (1)+(2) cannot land in one breath**, the honest interim is the REVERSE of today's state: keep the
  5-wide bytes but strike the false claims — rewrite `:171` to say the ge golden is a RE-AUTHORED 5-wide
  reduction that does NOT carry the Lean weld, drop "verbatim" at `:37` and `:147`, and file the gap where
  it will be seen. **Never leave the dispatch site advertising a tooth the deployed bytes lack.**

### M14 — the descriptor-drift gate never re-derives the by-name goldens it PASSes · **high**

*This is the mechanism that let M13 ship. Fix it in the same lane.*

- **CLAIM** — `scripts/check-descriptor-drift.sh:86` prints "**PASS — the Lean emission matches the
  checked-in descriptors**" with `GUARDED[0]="circuit/descriptors"` (**the whole tree**) ·
  `scripts/emit_descriptors.py:249` asserts the by-name goldens "are byte-pinned by Lean #guards +
  emit-gate tests" · `verify_provenance` (`:392-394`) prints "**PASS — N descriptor files … match the
  stamp**" counting `by_name_sha256`. **The script's own header (`:6-10`) disowns exactly this fallacy
  for the main set:** "a `sha256(bytes) == committed-FP` rehash proves only that a file matches the hash
  committed beside it (self-consistency) — it **CANNOT** catch a committed JSON gone stale while the Lean
  emission moved underneath it. **Re-deriving from Lean is the whole point.**" The by-name leg does
  precisely the thing the header disowns.
- **TRUTH — four mechanical facts:**
  1. `emit_descriptors.py:702` coverage-checks `DESC.iterdir()` filtered on `p.is_file()`; **`by-name/` is
     a DIRECTORY**, so it is silently exempt from the "every checked-in descriptor must have been
     re-emitted" gate. `written` never contains a by-name file — zero name overlap (69 main vs 25
     by-name; `comm -12` empty).
  2. `check-descriptor-drift.sh`'s `cp -R` → emit → `diff -ru` therefore leaves `by-name/`
     **byte-identical on BOTH sides ⇒ empty diff ⇒ unconditional PASS for any content whatsoever.**
  3. `emit_descriptors.py:248-259 collect_by_name_hashes()` reads bytes **FROM DISK**
     (`return { p.name: sha256_hex(p.read_bytes()) ... }`); `build_provenance:280` stores them as
     `by_name_sha256`; `verify_provenance:366-369` compares disk against a stamp computed from that same
     disk. **Pure self-consistency, sold under the same PASS.**
  4. The real chain is: Lean desc `==`(#guard, gated by `:32 lake build Dregg2`) Lean GOLDEN
     `==`(**HAND TRANSCRIPTION, UNGATED**) disk bytes. **Only `turn_chain_emit_gate.rs:47` `include_str!`s
     its disk file**; the other 24 emit-gate tests parse their own Rust `GOLDEN_JSON` literal and never
     read the bytes `descriptor_by_name()` serves. Worse,
     `circuit/src/presentation_descriptor_witness.rs:179` and `blinded_membership_witness.rs:347` define
     `GOLDEN_JSON` **AS** `include_str!` of the disk file — the "golden" IS the artifact, no Lean tie.
- **CORRECTED EVIDENCE (the original finding's supporting legs were partly wrong — do not repeat them):**
  the claim "5 by-name goldens have NO byte-pinning guard" is **FALSE for all 5**. Each is pinned via a
  **NAMED def** an inline-literal grep cannot see: `FieldDeltaRangeEmit.lean:71` `#guard emitVmJson2
  fieldDeltaRangeDescriptor == FIELD_DELTA_RANGE_GOLDEN` (the finding cited `:62-64` as "only structural"
  and stopped 7 lines short), plus `TURN_CHAIN_BINDING_GOLDEN` (`EffectVmEmitTurnChainBinding.lean:227/230`),
  `MEMBERSHIP_4ARY_GOLDEN` (`MerkleMembership4aryEmit.lean:57/60`), `GOLDEN_4ARY_DEPTH2`/`DEPTH8`
  (`BlindedMembershipEmit.lean:410-411`). All 5 MATCH disk today. A reported second drift on
  `note-spend-leaf.json` was a regex artifact — it matches byte-for-byte. **Every one of the 25 by-name
  files has a guard of some kind. Exactly ONE has drifted: `predicate-arith.json` (M13).**
- **LIVE? YES** — this is the CI/pre-commit gate that is supposed to protect the deployed descriptor
  surface, and the by-name goldens it fails to cover are the ones `descriptor_by_name()` serves to
  `bridge/` and `wire/` at verify time.
- **FIX — four parts, in order:**
  1. **FIX THE LIVE DRIFT FIRST** — this is a deployed-bytes bug, not just a gate bug. See M13 step 1.
  2. **CLOSE THE HOP THE RIGHT WAY — make `by-name/` genuinely Lean-derived** so the snapshot→emit→diff
     covers it like everything else. Add the by-name descriptors' Lean emitters to
     `emit_descriptors.py:85 EMITTERS` with a split routine routing each to
     `circuit/descriptors/by-name/<name>.json` into `written`; make the DESC coverage check at `:702`
     **recurse** (`DESC.rglob("*")` relative-keyed, not `DESC.iterdir()` + `p.is_file()`) so a by-name
     file no emitter reproduces is a routing-gap **FAILURE**; and **delete `collect_by_name_hashes()`**
     (`:248-259`), sourcing `by_name_sha256` at `:280` from the EMITTED content like `descriptor_sha256`
     at `:634`. Then `verify_provenance`'s by-name leg (`:366-369`) stops being self-referential because
     the stamp is minted from Lean bytes.
  3. **INTERIM GATE (~20 lines, ship today, keep even after 2)** — a CI check that extracts every
     `#guard emitVmJson2 <expr> == <golden>` from `metatheory/`, **resolving BOTH inline string literals
     AND `def X_GOLDEN : String := "..."` named indirections** (the named form pins 5 of the 25 and is
     what a naive grep misses), and byte-compares each against the matching
     `circuit/descriptors/by-name/*.json` by its JSON `"name"` field. Fail on mismatch AND on any by-name
     file no guard maps to. **This exact check catches `predicate-arith`.** Wire into the same CI job as
     `check-descriptor-drift.sh`.
  4. **STOP THE OVERCLAIM UNTIL 2 LANDS.** `check-descriptor-drift.sh:86` must not print "the Lean
     emission matches the checked-in descriptors" while `GUARDED` includes a subtree it never re-derives —
     scope the string to the re-derived set or print by-name's coverage separately. Same for
     `verify_provenance:392-394`. Correct `emit_descriptors.py:249`'s docstring: "byte-pinned by Lean
     #guards + emit-gate tests" is true of the **LEAN GOLDEN**, not of the disk bytes — **for 24 of 25
     files nothing ties the golden to the artifact.**

### M11 — the effect-VM differential invariant tests a hand-written third projector, and it is ALREADY STALE · **high**

- **CLAIM — three, and all three are false:**
  (1) `turn/src/executor/effect_vm_bridge.rs:40-42` — the executor and SDK projectors "agree byte-for-byte
  by construction (**asserted by the differential invariant in
  `protocol-tests/.../effect_vm_differential.rs`**)". **That assertion does not exist in that file.**
  (2) `effect_vm_differential.rs:28` — the module "verifies the *bridge* between **two independent
  implementations** of 'what does effect V do to cell state'". It verifies a **third, hand-written**
  implementation.
  (3) `effect_vm_differential.rs:140-143` — "Mirrors `TurnExecutor::convert_turn_effects_to_vm` (**which
  is module-private**). Kept inline here so the differential test is **independent of the executor
  crate**". **BOTH halves are factually false.**
- **TRUTH** — `turn/src/executor/mod.rs:736-737` is `mod effect_vm_bridge; pub use
  effect_vm_bridge::convert_turn_effects_to_vm;` under `pub mod executor;` (`turn/src/lib.rs:104`) — it
  is **public API**, and other tests already call it that way (`sdk/tests/wide_umem_weld_domain2_siblings.rs:220`,
  `sdk/tests/executor_cap_open_welded_commit.rs:165`). And the file **already imports the executor crate**
  at `:39-42` (`use dregg_turn::{Action, Authorization, CallForest, ComputronCosts, DelegationMode,
  Effect, TurnExecutor, turn::Turn};`) — every test constructs `TurnExecutor::new(ComputronCosts::zero())`
  and calls `.execute(&turn, &mut ledger)`. **The stated justification is factually impossible.** The
  sole projection call site is `air_claim` (`:368-370`) calling `project_turn_to_vm`;
  `convert_turn_effects_to_vm` appears in the file only in a comment at `:779`.
- **The false citation appears FOUR times:** `turn/src/executor/effect_vm_bridge.rs:40-42`,
  `sdk/src/cipherclerk.rs:6306-6309`, `sdk/src/cipherclerk.rs`'s `hash_to_8` comment (~`:6330`),
  `circuit/src/effect_vm/helpers.rs:160-162` ("Both the executor projector and the SDK projector call
  THIS function, so their per-effect felts agree byte-for-byte by construction"). **The shared *fold
  helper* is real; the asserted *invariant* is fiction.** No test anywhere compares the executor
  projector to the SDK projector (swept every `convert_effects_to_vm` call site tree-wide:
  `grain-turn/src/finalize.rs:77`, `tests/src/every_variant_roundtrip.rs:656/699`, `sdk/tests/*`).
- **THE DECISIVE FINDING — the mirror is ALREADY STALE and the staleness is structurally invisible.** The
  v13 FIELDS-OCTET lane moved SetField off the fold in BOTH real projectors:
  - `turn/src/executor/effect_vm_bridge.rs:61-63` — `field_element_to_bb(v) =
    dregg_circuit::effect_vm::field_limbs8(value)[0]` ("REPLACES the ~31-bit `fold_bytes32_to_bb`")
  - `sdk/src/cipherclerk.rs:6315-6317` — identical, same comment
  - `protocol-tests/.../effect_vm_differential.rs:154-156` — **STILL** `field_to_bb(v) =
    fold_bytes32_to_bb(v)`
  Per `circuit/src/effect_vm/helpers.rs:122-134`, `field_limbs8(b)[0] = u32::from_be_bytes([b[28], b[29],
  b[30], b[31]])`; per `:167-178`, `fold_bytes32_to_bb` is a Horner fold over **LE** 4-byte limbs.
  `differential_set_field` (`:693-740`) writes `v0` into `value[..4]` and asserts `claim.final_fields[idx]
  == BabyBear::new(v0 % P)`. **The mirror folds with limbs 1..7 zero, yielding exactly `v0` — the test is
  GREEN. The deployed bridge yields `be_u32(value[28..32])` = 0.** The harness asserts the AIR field takes
  `v0` on a turn where the real projector drives it to zero. **This is precisely the executor→AIR
  projection drift the module exists to catch, and it sailed through because the AIR trace is generated
  FROM the reconstruction** (`air_claim:388 generate_effect_vm_trace(&vm_initial, &vm_effects)`) — mirror
  vs a trace of the mirror. **A third dialect exists at `air_claim:382`**, which loads initial fields via
  `u32::from_le_bytes([f[0],f[1],f[2],f[3]])` — the historical 4-byte truncation both real projectors
  abandoned.
- **Strictly weaker, too:** the mirror's `_ => {}` at `:353` covers 12 arms where the bridge has ~30.
  **Burn, Mint, CellDestroy, AttenuateCapability, Refusal, CellSeal, CellUnseal, MakeSovereign,
  CreateCellFromFactory, ReceiptArchive, NoteSpend, NoteCreate, IncrementNonce all disappear into NoOp**
  rather than being compared. A bridge bug in any of them **cannot be caught here even in principle.**
- **LIVE (the real bridge, never instantiated by this module):** `turn/src/executor/proof_verify.rs:490`
  and `:586` both call `convert_turn_effects_to_vm(cell_id, turn)` inside the deployed sovereign
  proof-verification path (`verify_and_commit_proof_rotated`), then resolve cohort descriptors and
  reconstruct the PI vector from its output (`:1059, :1174, :1313`).
- **FIX:**
  1. **DELETE the mirror; point the harness at the real bridge.** Remove `fn project_turn_to_vm`
     (`:138-361`) entirely, including its private `hash_to_bb`/`field_to_bb`/`hash_to_8` helpers. In
     `air_claim` (`:370`) replace with `let vm_effects =
     dregg_turn::executor::convert_turn_effects_to_vm(&cell_id, turn);` (add it to the existing `use
     dregg_turn::{...}` at `:39-42`). **EXPECT `differential_set_field` TO GO RED** — the real bridge
     projects `field_limbs8(value)[0]` = BE bytes[28..32], so the test's `value[..4] = v0` fixture yields
     0, not v0. **That red is the correct answer and the proof the fix works; fix the FIXTURE** (write v0
     into `value[28..32]` big-endian, matching the faithful u64-lane lo32) **and the expectation, not the
     projector.**
  2. **Align `air_claim`'s initial-state load with the bridge's dialect.** `:380-385` must use
     `dregg_circuit::effect_vm::field_limbs8(f)[0]`, the same lane the rotated producer writes to limb
     `4 + slot` — **or before/after live in different domains and the field comparisons are
     meaningless.**
  3. **Make the cited invariant EXIST, or delete the citation.**
     ```rust
     #[test]
     fn executor_and_sdk_projectors_agree_byte_for_byte() {
         // per Effect variant fixture — reuse tests/src/every_variant_roundtrip.rs's
         // variant table so new variants are forced in:
         let via_executor = dregg_turn::executor::convert_turn_effects_to_vm(&cell_id, &turn);
         let via_sdk = AgentCipherclerk::convert_effects_to_vm(&cell_id, &effects);
         assert_eq!(via_executor, via_sdk, "projector drift on {variant:?}");
     }
     ```
     **Must be exhaustive over the `Effect` enum — drive it off a `match` with no `_` arm, so a new
     variant fails to COMPILE rather than silently passing.** This is what would have caught the v13
     SetField lane had it forgotten one side. Until it exists, **strike the false citation from all four
     sites**. "Both call the same fold helper" is true and worth saying; "asserted by the differential
     invariant" is not.
  4. `:27-28` becomes true only after (1) — land them together.

### M10 — the chat-surface parity "proof" hand-copies both sides · **medium**

- **CLAIM** — `dreggnet-telegram/tests/full_parity_through_telegram.rs:1-2` "**The driven FULL-PORTFOLIO
  parity proof — Telegram registers the SAME 18 offerings the web catalog does**" · `:31` "The full
  18-offering set the web catalog registers (`dreggnet_web::demo_host`)".
  `dreggnet-wechat/tests/full_parity_through_wechat.rs:31-51` is the third copy.
- **TRUTH** — the test never reads `dreggnet_web::demo_host`. **It cannot:** every `dreggnet_web`
  reference in both chat crates (14 occurrences, verified exhaustively) is inside a doc comment — **zero
  `use`, zero call sites** — and neither `dreggnet-telegram/Cargo.toml` nor `dreggnet-wechat/Cargo.toml`
  deps `dreggnet-web` in any section (telegram dev-deps = `dungeon-on-dregg` alone, `Cargo.toml:79-83`).
  `const EXPECTED_KEYS: [&str; 18]` (`:33`) is a hand-typed array checked against
  `telegram_default_host`'s hand-typed registrations (`src/host.rs:416-485`). **The test can only prove
  "Telegram registers these 18 string literals"; the word "SAME" is unbacked.**
- **CORRECTION to the original finding (do not repeat it):** "retypes all 18 registrations" is **FALSE**.
  **8 of 18 keys** (trade · inventory · cheevos · guild · craft · companion · tavern · party) ARE
  genuinely coupled — both chat hosts call the identical `dreggnet_surfaces::register_surfaces(&mut host)`
  (`telegram/src/host.rs:455`, `wechat/src/host.rs:529`) that `demo_host` calls at
  `dreggnet-web/src/lib.rs:2022`, commented "**the ONE call web makes, reused verbatim**". Only **10** are
  re-authored: the 5 games (incl. council's two `CandidateProposal`s + quorum 2) and the 5 non-game
  offerings. **This proves the right pattern already exists in-tree and was simply not applied to the
  other 10.** `seated.rs:14` in both crates self-describes as "a byte-for-byte peer of
  `dreggnet_web::seated`" — a third triplication, admitted in prose.
- **The correction does not save it.** Parity is TRUE today (web 5+8+5=18; telegram 5+8+5=18) but
  **UNENFORCED**. Rename `council`→`senate` in `catalog_default_host`, change quorum to 1, or add a 19th
  offering to `demo_host`, and all three suites stay green while parity breaks — **the identical drift the
  audit found (automatafl, tug, and the eight RPG keys ABSENT from the chat hosts) and this test was
  written to close.** The `contains` + `offs.len() >= EXPECTED_KEYS.len()` shape (`:78-89`) is
  one-directional and **cannot catch web-side additions even in principle.**
- **LIVE?** The live path is fine (both hosts really do register 18 real offerings). **What is a mirror is
  the PROOF.**
- **FIX part 1 (immediate — makes the test honest):** add `dreggnet-web = { path = "../dreggnet-web" }`
  to `[dev-dependencies]` of BOTH `dreggnet-telegram/Cargo.toml` and `dreggnet-wechat/Cargo.toml` —
  **acyclic, verified** (`dreggnet-web` deps neither chat crate). Delete `const EXPECTED_KEYS` in both
  tests and derive from the real catalog at runtime:
  ```rust
  let want: BTreeSet<String> = dreggnet_web::demo_host().list_offerings()
      .iter().map(|o| o.key.clone()).collect();
  assert_eq!(want, got);   // SET EQUALITY — not `contains` + `len() >= N`
  ```
  **Set-equality is what catches a web-side 19th offering or a rename, which the current one-directional
  shape cannot.** Then the doc comment's "the SAME 18 offerings the web catalog does" becomes a statement
  the test actually executes.
- **FIX part 2 (couple the LIVE path, not just the test):** hoist the 10 hand-retyped registrations into
  a shared crate (`dreggnet-portfolio`) exposing `register_games(&mut host, council_members: Vec<[u8;32]>)`
  and `register_non_game_offerings(&mut host)`, plus the triplicated `SeatedTug` adapter
  (`dreggnet-web/src/seated.rs` + its two self-admitted "byte-for-byte peer" copies). Then
  `dreggnet_web::catalog_default_host`/`demo_host`, `telegram_default_host` (`src/host.rs:416-485`), and
  `wechat_default_host` (`src/host.rs:~478-558`) ALL call it — **exactly the pattern all three already
  share for `register_surfaces`, which is why 8 of the 18 keys are the only ones not at risk.** Council's
  electorate stays a parameter (web derives blake3(username), Telegram from the chat id — a legitimate
  identity difference, not drift), but the two `CandidateProposal`s and quorum 2 move into the shared fn.
  **After that, parity is structural: a 19th offering lands on every surface by construction, and the test
  only guards the seam.**

### M15 — the kimchi simulator reads a coefficient at exactly ONE of seven shapes · **medium**

- **CLAIM** — `dregg-dsl-differential/src/lib.rs:33` asserts `gen_kimchi` is "**YES**" in the agreement
  set: "Generic-gate simulator that fills the canonical witness per IR shape and **asserts every gate's
  `c_i * w_i` polynomial evaluates to zero**." `kimchi_sim.rs:7-9` repeats it.
- **TRUTH** — `eval_generic` (`kimchi_sim.rs:202-212`) is the **only** code that reads `gate.coeffs`, and
  it has exactly ONE call site: `:88`, the `EqualU64` arm. The other six shapes never touch a
  coefficient — `NotEqualU64` (`:90-101`), `EqualBytes32` (`:102-107`), `NotEqualBytes32` (`:108-111`) call
  `assert_shape`, which checks only `gates.len()` and `gates[0].typ` (`:178-197`), then return `l != r` /
  `l == r` — **the IR-level truth, recomputed from the same inputs `gen_rust` receives.** `Membership`
  (`:112-122`) checks `g.typ == Poseidon` and returns `set.contains(element)`.
  **`check_range_burst` (`:126-176`) type-checks 66 gates then the ONLY decision is the host u64 compare
  at `:152`**; everything after is a tautology (`bit = ((diff >> i) & 1)` so `poly = -bit + bit*bit` is
  identically 0; `acc` re-sums the same bits with the same weights, so `acc != diff` at `:172` is
  unreachable). **Zero coefficients are read in the 66-gate burst.**
- **LIVE?** `harness.rs:56 kimchi_sim::evaluate(&handles.kimchi, &case.body.requirements)` → recorded as
  `BK_KIMCHI` at `:61`; `dregg-dsl-differential/tests/differential.rs:31 matrix.assert_all_agree()` gates the test. **Since the
  vote is re-derived from `case.body.requirements` — the same IR `gen_rust` evaluates — `BK_KIMCHI` cannot
  disagree with `BK_RUST` regardless of what coefficients `gen_kimchi` emits. The row is structurally
  green.**
- **PARTIAL REFUTATION (honest — do not fault this):** the Poseidon/membership half IS a disclosed
  limitation. `kimchi_sim.rs:15-21` states plainly that Poseidon gates "semantically delegate to the
  IR-level truth of `Requirement::Membership`" and that "this crate's value-add is cross-backend verdict
  agreement, not gate-level Poseidon soundness"; `lib.rs:33` carries "Poseidon gates (membership-only) are
  checked structurally." That is a labeled placeholder. **The Generic-gate half has no such label
  anywhere — the module header affirmatively claims the opposite.**
- **WHAT THE BLINDNESS HIDES (this is why it matters): a live emitter bug.**
  `dregg-dsl/src/gen_kimchi.rs:80-86` emits the range-burst "diff computation gate" as
  `coeffs: vec![1, -1, 0, 0, 0], wires: 2`. **A Kimchi Generic gate is an ASSERTION `c0*w0 + c1*w1 + c2*w2
  + c3*(w0*w1) + c4 = 0`, not an assignment.** On the canonical witness `(bigger, smaller)` that gate
  asserts `bigger - smaller == 0` — i.e. **EQUALITY, not a diff binding.** Binding a third wire to the
  difference requires `coeffs: [1, -1, -1, 0, 0], wires: 3`. Nothing binds the 64 bit-wires to diff
  either. **A simulator that actually evaluated the burst would fail on the first `LessEqualU64` case. The
  mirror is concealing a live emitter bug.**
- **FIX — two ends; do not fix only the doc:**
  1. `kimchi_sim.rs` — make `eval_generic` the **sole decision procedure** for every Generic gate. Give
     the sim a prime modulus (Pallas/Vesta base field, or any test prime) and evaluate mod p instead of in
     i128 — **this is what currently blocks the `NotEqualU64` arm** (`:97-99` admits it: "modular inverse
     isn't computed here because our gate evaluator works in i128"). With a modulus, compute
     `inv = (l-r).modpow(p-2, p)` and evaluate the emitted gate `c3*(diff*inv) + c4` — accept iff 0,
     reject when no inverse exists. **Delete the `if l == r { return Ok(false) }` shortcut; the gate must
     decide.**
  2. `check_range_burst` — build the witness (diff, the 64 bits, acc) and run `eval_generic` on all 66
     gates with the wires each gate actually names. **Delete the `if bigger < smaller { return Ok(false) }`
     host compare and the `poly = -bit + bit*bit` / `acc != diff` tautologies — reject must fall out of a
     gate evaluating non-zero, not out of a Rust `<`.**
  3. `EqualBytes32`/`NotEqualBytes32` — `gen_kimchi` emits ONE gate for 32 bytes, which cannot constrain 8
     limbs. Fix the **emitter** to emit 8 limb gates (and for `!=`, a limb-disjunction witness), then
     evaluate each limb gate on the limb witness. **Until the emitter is fixed, this arm must record
     `BackendVerdict::Error` or `Skip { reason }` — never a re-derived Accept.**
  4. Membership/Poseidon — keep the structural check, but record `Skip { reason: "Poseidon gate-level
     soundness covered by circuit/src/backends/kimchi_native/" }` rather than casting a re-derived
     Accept/Reject vote. **Same treatment `lib.rs:36-37` already gives `gen_midnight`/`gen_sp1` — it makes
     the disclosure structural instead of a comment.**
  5. `dregg-dsl/src/gen_kimchi.rs:80-86` — `coeffs: vec![1, -1, -1, 0, 0], wires: 3` so the third wire is
     bound to the difference. Add the wiring binding the 64 bit-wires to that diff wire (today only the
     single reconstruction gate at `:107-113` gestures at it, and `:104-106` admits it is a stand-in for a
     double-and-add chain).
  6. `lib.rs:33` + `kimchi_sim.rs:7-21` — true once (1) lands. If not, the roster entry must read in the
     same register as the midnight/sp1/emit_stark rows: "**PARTIAL** — only the `==` (u64) shape's gate
     polynomial is evaluated against emitted coefficients; all other shapes are checked for gate count and
     type only and the verdict is re-derived from the IR, **so this row cannot disagree with `gen_rust`.**"
- **CANARY** — mutate `gen_kimchi.rs:96`'s 64 boolean gates to `vec![0,0,0,0,0]` (deleting the range check
  — a genuine soundness hole in the emitted circuit) and `gen_kimchi.rs:133`'s NotEqual coeffs to
  `vec![7,7,7,7,7]`, and confirm `cross_backend_differential` goes **RED**. **It stays green today. If it
  stays green after the fix, the sim is still a mirror.**

---

## VARIANT F — lean-models-reauthored-shape
*Lean hand-transcribes a Rust object, the compiler proves totality over the TRANSCRIPTION, and a doc
narrates that as a proof about the Rust.*

*(M13 is also of this variant — a Lean-authored descriptor whose disk artifact is a Rust-side
re-authoring. It is filed under E because the harness blindness is what let it ship.)*

### M21 — `EffectTag` claims the Lean compiler gates the Rust `Effect` enum; it has already drifted 27 vs 33 · **high**

- **CLAIM** — `metatheory/Dregg2/Substrate/VerbRegistry.lean:14`: "the live **27-variant** `Effect` enum
  (`turn/src/action.rs`, post VERB-LOCKSTEP), reified as `EffectTag` — ONE constructor per current
  variant, so **the Lean compiler's exhaustiveness check IS the completeness proof: a new wire variant
  that is not classified will not compile**" · `metatheory/README.md:64` repeats it verbatim under
  **Completeness** · `metatheory/Dregg2/AssuranceCase.lean:147` makes it **load-bearing for guarantee A**:
  "the wire enum is **reconciled** against the registry (`Substrate.VerbRegistry.classify`, exhaustive by
  the compiler)". · `:223` "The complete roster of live tags … **Kept in sync with `EffectTag` by the same
  compiler that checks `classify`**" — i.e. in sync with itself.
- **TRUTH — the Lean compiler cannot see a Rust enum, and nothing reconciles them.** `grep` for
  `VerbRegistry`/`EffectTag` across all `*.rs`/`*.sh`/`*.py`/`*.yml`/`*.toml` yields exactly **two doc
  comments** (`cell/src/blueprint.rs:4`, `sdk/src/factories.rs:4`) and **zero code** — no emit step, no
  roster test, no CI check. The exhaustiveness check on `classify` proves only that the match covers
  `EffectTag`'s own constructors.
- **THE CLAIM HAS ALREADY BEEN FALSIFIED BY DRIFT.** Top-level variants of `Effect` (`turn/src/action.rs:1061`
  through `ShieldedTransfer`; `Declined`/`NoAuthority`/`WindowExpired`/`Custom` belong to the separate
  `RefusalReason` enum and do NOT count) number **33**. `EffectTag` (`:213-221`) has **27**. Set-diff =
  exactly **`Mint`, `SetProgram`, `ShieldedTransfer`, `Promise`, `Notify`, `React`** — all six live arms
  of the deployed dispatcher `apply_effect` (`turn/src/executor/apply.rs:124`): `Effect::SetProgram`
  `:213`, `Effect::Mint` `:358`, `Effect::Promise` `:391`, `Effect::Notify` `:404`, `Effect::React` `:419`,
  `Effect::ShieldedTransfer` `:425`. **They landed in Rust and Lean stayed green — exactly the event
  `:14` asserts cannot occur. The stated mechanism is falsified by its own tree.**
- **THE CORPUS REFUTES ITSELF — the sharpest evidence.**
  `metatheory/Dregg2/Circuit/ExecutorApplyDifferential.lean:10-16` states "`turn/src/executor/apply.rs:124
  pub(crate) fn apply_effect` … is a total `match` over the deployed `Effect` enum
  (`turn/src/action.rs:1061`), routing each of its **33** variants … The match is EXHAUSTIVE (no `_ =>`
  arm), so those 33 variants ARE the deployed effect set," and its `DeployedEffect` transcribes all 33.
  **Two Lean mirrors of one Rust enum disagree (27 vs 33) and both compile — conclusive that the compiler
  is not the reconciler.**
- **TWO SUB-CLAIMS TRIMMED (why high, not critical):**
  1. "`Mint` unclassified matters most" is **overstated**. `AssuranceCase.lean:140-141` does NOT rely on
     the registry for mint — it handles it separately: "PRODUCTION authority (mint) is not a cap-grant at
     all: it is gated on holding the ISSUER cell's cap (`Circuit.Spec.SupplyCreation.mintA_authorized`,
     pinned under guarantee B …)". What IS damaged is the closing sentence's **warrant**: "There is no
     other cap-conferring constructor in `FullActionA`; the wire enum is reconciled against the registry"
     — the exhaustiveness half of guarantee A cites a reconciliation that does not exist, over six live
     constructors it never examined. **`Promise`/`React` (`apply.rs:391/:419`, wake-turn-hash spend) are
     the genuinely unexamined ones.**
  2. `no_live_factory_tags` (`:295`) is **NOT falsified in substance** — none of the six drifted variants
     is an escrow/queue/inbox/pubsub/seal/sturdyref family member, so the doomed families really are gone.
     But its **SCOPE** is now a lie: it quantifies over `EffectTag`, which the docs (`:22`, `:33`) call
     "the live enum". **It proves a property of a 27-element Lean type and is narrated as a property of a
     33-variant Rust type.**
- **FIX — (1) and (2) are independent and BOTH required:**
  1. **RESYNC the mirror.** Add the six constructors to `EffectTag` (`:213`) and `allEffectTags` (`:225`)
     and classify each in `classify` (`:240`). Proposed, from reading the `apply.rs` arms: `SetProgram` ⇒
     `.survivor .write` (same authority surface as `SetVerificationKey`, applied LAST — `action.rs`'s own
     doc says a cell's program and VK are one authority surface); `ShieldedTransfer` ⇒
     `.survivor .shieldUnshield`; `Promise`/`React` ⇒ `.turnStructure .pipelining` (wake-turn-hash
     composition, alongside `PipelinedSend`); `Notify` ⇒ `.turnStructure .receiptLog` or `.pipelining`
     (**read `apply.rs:404` first**). **`Mint` ⇒ `.survivor .move` is the obvious dual of `Burn` (already
     `.survivor .move`) but is EMBER-GATED**: if mint is a distinct substance-law from move per DREGG3
     §2.2 it needs its own verb, and `minimality`/`each_verb_irreplaceable` must then be re-proved. **Do
     not let a lane pick this silently.** Update the count in `:223`, `:14`, and `README.md:64` from 27 to
     33. Re-run `no_live_factory_tags` (`:295`) on the wider type — that green then means something.
  2. **BUILD THE RECONCILER THE DOCS ALREADY CLAIM, or delete the claim.** Follow the existing
     staged-registry precedent (Lean-emitted TSV + `include_str!`):
     - **Lean side:** emit `allEffectTags` to `metatheory/emitted/effect-roster.tsv` from
       `scripts/emit-descriptors.sh`.
     - **Rust side:** a test in `turn/tests/` that builds the live roster via an exhaustive `match effect
       { Effect::SetField{..} => "SetField", … }` with **NO `_ =>` arm** — **the wildcard ban is what makes
       the RUST compiler the enforcer**: adding a variant to `Effect` then fails to compile until the
       roster names it — sorts it, and `assert_eq!`s against the `include_str!`'d Lean roster. Wire into
       circuit-CI (`lfs: true`).
     Then `:14` is earned: **the Rust compiler catches the new variant, the diff test catches the
     unclassified one.**
     **If (2) is not done in the same breath**, strike the mechanism claim at `:14`, `README.md:64`, and
     `AssuranceCase.lean:147` and replace with: "`EffectTag` is a HAND-TRANSCRIBED mirror of
     `turn/src/action.rs:1061` as of `<commit>`. Nothing mechanically enforces the correspondence; drift
     is possible **and has occurred**. The compiler proves `classify` total over `EffectTag`, not over the
     wire enum." **Do NOT ship the 27→33 resync alone with the false mechanism sentence intact — that
     repairs the instance and leaves the disease.**
  3. **COLLAPSE THE DOUBLE MIRROR.** `ExecutorApplyDifferential.lean`'s `DeployedEffect` (already 33,
     already correct, already anchored by name to `apply.rs:124`) and `VerbRegistry.EffectTag` are two
     transcriptions of one Rust enum, free to disagree — **and they did**. Make `DeployedEffect`
     canonical; have the registry import it and map onto it (`def tagOf : DeployedEffect → EffectTag`,
     registry theorems restated over `DeployedEffect`). **One mirror can be gated by (2); two mirrors
     cannot.**
  4. **Repair `AssuranceCase.lean:147` specifically:** guarantee A's "There is no other cap-conferring
     constructor in `FullActionA`" must either cite the reconciler from (2), or **explicitly enumerate the
     six previously-unexamined constructors and argue each is non-cap-conferring** — `Promise`/`React`
     (`apply.rs:391/:419`) and `ShieldedTransfer` (`:425`) are the ones that actually need the argument
     written; `Mint` already has its leg under guarantee B (`SupplyCreation.mintA_authorized`).

---

## VARIANT G — doc-claims-absent-seam
*The mildest shape and the most numerous: the mechanism was never built, and a doc asserts it anyway.
Cheap to fix, and the fix is mandatory even when the code fix is deferred — but note M16 hides a real
arithmetization bug behind its doc lie.*

### M16 — `prove_trivial` echoes the oracle on the exact boundary rows the suite advertises as its teeth · **high (harness-scope)**

- **CLAIM** — `dregg-dsl-differential/src/plonky3_runner.rs:391-401`, the doc comment and the function
  name both assert a circuit is built and proved: "**Build a tiny circuit that proves an inputless
  tautology.** Used when the real comparison would overflow the BabyBear-safe range; we still want the
  backend to report a verdict, and we trust the IR-level truth for out-of-range inputs." ·
  `lib.rs:34` names **ONLY membership** as the `gen_plonky3` SKIP carve-out — the out-of-range fallback is
  unmentioned, so the reader concludes every non-membership case round-trips · `lib.rs:35` asserts the
  retired hand-STARK's forge-detector poles "are carried by the curated comparison/equality cases **voted
  through `gen_plonky3`'s `prove_dsl_plonky3`/`verify_dsl_plonky3` round-trip** against the rust oracle in
  this harness."
- **TRUTH** — `:395-401` is literally `if ir_ok { Accept } else { Reject }`. **No `CircuitDescriptor`, no
  `DslCircuit::new`, no `prove_dsl_p3`, no `verify_dsl_p3`.** `ir_ok` is the rust oracle's own truth
  value, so `gen_plonky3` votes by echoing `gen_rust`. Its own doc comment's first sentence is false about
  the six lines directly beneath it.
- **LIVE, and it fires on the advertised teeth.** `harness.rs:64` calls
  `plonky3_runner::prove_and_verify` for every curated case; `:65-70` records Accept/Reject as a full
  vote, indistinguishable from a real round-trip vote. Three curated cases exceed the `1u64 << 30` guard
  (`:106-109` inequality, `:199-201` equality, `:237-239` non-equality): `predicates.rs:229`
  `("boundary-max", u64::MAX, u64::MAX)`, `:230` `("near-overflow-reject", u64::MAX-1, u64::MAX)`, `:273`
  `("max-zero", u64::MAX, 0)`. **`lib.rs:52` advertises exactly these as the boundary battery ("`u64::MAX`,
  near-overflow"). The matrix records the oracle agreeing with itself and reports a cross-validated
  backend.**
- **WORSE THAN REPORTED — THE IN-RANGE INEQUALITY CIRCUIT IS UNSOUND, NOT MERELY PLANTED.** The diff-le
  descriptor (`:120-174`) carries exactly three constraints: `Polynomial(bigger - smaller - diff = 0)`,
  `Binary(indicator)`, `Polynomial(1*indicator = 0)`. `circuit/src/dsl/dsl_p3_air.rs:477-481` lowers
  Polynomial to `assert_zero(Sum of coeff * product of local[ci])` **over BabyBear**; `:461` lowers Binary
  to `c*(c-1)`. **There is NO range check on `diff`, and NOTHING ties `indicator` to whether the
  subtraction wrapped — it is a free binary column.** So for `smaller=101, bigger=100` (**both in range**),
  a cheating prover supplies `(101, 100, p-1, 0)`: constraint 1 holds since `100 - 101 = p-1 mod p`,
  constraint 2 holds (0 is binary), constraint 3 holds (indicator = 0). **`prove` succeeds and `verify`
  ACCEPTS a false `101 <= 100`. The circuit does not prove the inequality at all.** Rejects only ever
  appear because `:178-182` plants the losing witness `(0, 1)` by construction, which `:20-22`
  misdescribes as "our prover's 'we can witness it' decision matches u64 arithmetic" — **that match is
  enforced by the harness's honesty, never by the AIR.**
- **NET:** the `gen_plonky3` leg has **no teeth on inequalities anywhere**. Out of range it echoes the
  oracle; in range the encoding is forgeable and only a deliberately-broken trace yields Reject.
  `lib.rs:35`'s claim that this leg inherits the dead hand-STARK's forge-detector poles is **false in both
  regimes.**
- **WHAT IS GENUINELY REAL (scoping, not refuting):** the `round_trip` repoint at `:358-362` onto the
  shipped `dregg_circuit::dsl::dsl_p3_air` (p3-batch-stark, what `shielded/spend_circuit.rs` and
  `attest.rs` actually use) is correct and honest work. The eq-u64 (`Equality` col_a/col_b) and neq-u64
  (`ConditionalNonzero` + inverse witness) encodings are **sound and do real prove+verify in range**, and
  `drive_equality_bytes`/`drive_nonequality_bytes` (`:331-353`) mask into the 30-bit range BEFORE
  delegating, so bytes cases always round-trip. **The membership Skip (`:77-90`) is a properly-reasoned,
  empirically-probed carve-out — a model of what the out-of-range carve-out should have looked like.**
- **FIX — THREE, and do not "quick fix" #1 alone (deleting the echo without fixing the encoding leaves
  the leg toothless in range too):**
  1. **`prove_trivial` MUST NOT VOTE — it must Skip.** Delete it (`:391-401`). At each of the three guards
     (`:106-109`, `:199-201`, `:237-239`) return the honest carve-out instead of a verdict:
     ```rust
     return Verdict::Skip {
         reason: "operand exceeds the 2^30 BabyBear-safe range: this descriptor encodes u64 \
                  comparison as single-felt field arithmetic, which is only sound below 2^30. \
                  No arithmetization exists to differ against — see the limb-decomposition lane.",
     };
     ```
     `Verdict::Skip` already flows correctly to `BackendVerdict::Skip` at `harness.rs:67`, so the matrix
     records a Skip (no vote) rather than the oracle agreeing with itself. Model the reason string on the
     membership Skip at `:77-90`.
  2. **FIX THE FORGEABLE diff-le ENCODING (the load-bearing one).** `:120-174`: add a bit-decomposition of
     `diff` — N `ColumnKind::Binary` columns `d_0..d_{N-1}` (N = 30 for the safe range), each with
     `ConstraintExpr::Binary`, plus one Polynomial recomposition constraint `diff - Sum(2^i * d_i) = 0`.
     **That makes `diff < 2^N` unforgeable, which is what actually decides the inequality — and it retires
     the free `indicator` column, whose third constraint proves nothing.** Then **delete the planted
     witness at `:178-182`** and let the prover compute `diff = bigger - smaller mod p`
     UNCONDITIONALLY, with the bits derived from that felt. When `smaller > bigger` the diff is p-1-ish,
     its bit-decomposition overflows N bits, recomposition fails, `prove` panics → `round_trip`'s
     `catch_unwind` (`:369-372`) yields Reject **HONESTLY. That is the forge-detector pole `lib.rs:35`
     claims to have, actually present.** Bonus: a 30-bit-clean encoding raises the guard from 2^30 to a
     real u64 comparison via 3× ~22-bit limbs, **retiring fix #1's Skip for boundary-max/near-overflow
     entirely** — that is the refine-up close; #1 is the honest interim.
  3. **CANARY — the adversarial test the harness never had.** New test in `dregg-dsl-differential/tests/`:
     build the diff-le descriptor for `(smaller=101, bigger=100)` and hand `prove_dsl_p3` the **CHEATING**
     witness `(101, 100, BabyBear::new(BABYBEAR_P - 1), 0)` — **prover TRIES to cheat, rather than the
     harness breaking the trace for it.** Assert `prove` panics or `verify` returns false. **Against
     today's descriptor this test FAILS (it verifies) — that is the falsifier proving the hole is real.**
     Then revert the range constraint and confirm it goes red.
  4. **RETRACT THE DOC CLAIMS until #2 and #3 land.** `lib.rs:34` name BOTH carve-outs ("…Membership shapes
     route to the Lean IR2 rail and are marked SKIP; operands >= 2^30 exceed the single-felt BabyBear
     encoding and are ALSO marked SKIP, casting no agreement vote."). **`lib.rs:35` is the sentence that
     must go** — until #3 exists the poles are carried by NOTHING; the honest text is that `emit_stark`'s
     probe (`tests/_probe_stark.rs`, incl. the inequality bit-decomposition tooth) died with stark-kill
     `f04b2dd1e` and its coverage is currently **UNREPLACED, with the replacement lane named**.
     `plonky3_runner.rs:20-22`'s "boolean indicator … matches u64 arithmetic" describes the harness's
     honesty, not a constraint — it dies with the indicator column in #2.

### M04 — `trait_root (E1 closed)` has no consumer; the "TCB workaround" it claims to replace IS the live path · **low (doc-only)**

- **CLAIM** — `dreggnet-asset/src/lib.rs:59-62`: "**`trait_root` (E1 closed)** — … A visual/stat layer
  (**the sprite / gear crates**) **reads it via `AssetWorld::trait_root_of`** and draws deterministic
  traits from the asset's *committed* identity, **instead of re-deriving from the raw `AssetId` bytes as a
  TCB workaround**." Echoed at `:155` ("the stable handle a visual / stat layer … draws deterministic
  traits from") and `:188-189` and `:760-764` ("**This is the E1 accessor**: a consumer reads … here
  instead of re-deriving").
- **TRUTH — zero consumers.** Repo-wide, `mint_with_traits`, `mint_soulbound_with_traits`,
  `trait_root_of`, `mint_batch` have **ZERO callers outside `dreggnet-asset/tests/asset_layer.rs`**
  (`:279, :296-301, :322, :376-383, :397`). Every real consumer —
  `dreggnet-craft/src/forge.rs:231,260,354`, `dreggnet-companion/src/lib.rs:798`,
  `dreggnet-cheevo/src/lib.rs:667` — calls plain `mint`/`mint_soulbound` (`:558`, `:585`), whose
  `trait_root` is `default_trait_root(asset_id) = blake3::derive_key("dregg-asset-trait-root-v1",
  &asset_id.0)` (`:190-192`) — **literally "re-deriving from the raw `AssetId` bytes", the TCB workaround
  the doc claims E1 replaced.**
- **BOTH named consumers refute the sentence from their own side, by name:**
  - `dreggnet-sprite/src/lib.rs:22-25`: "Traits are derived FROM the asset's existing content address —
    the AssetId bytes seed a real DrawStream … **No NoteDesc field is added this pass** (the AssetId
    derivation is TCB; **the first-class `trait_root` identity field is the named E1 follow-up**)." And
    `:42-44` lists "**E1** the first-class asset trait_root field" under **NAMED NEXT** — i.e. unbuilt.
    **The sprite crate flatly says E1 is open while dreggnet-asset says it is closed.**
  - `dreggnet-gear/src/gear.rs:149`: `let asset_id = self.world.mint(smith_label, &stats.traits_root());`
    — the StatBlock digest is the **MINT SEED**, not the trait_root field. `dreggnet-gear/src/lib.rs:8-10`
    is honest about this ("committed into the AssetId via the traits_root **mint seed**"). Gear never
    calls `trait_root_of`.
- **NOT a soundness or behavior defect (severity is low, deliberately).** The field is a genuine committed
  note field, gated `WriteOnce`, carried across the lineage (`:701`); `mint`'s own doc at `:554-555` is
  honest that plain mint uses `default_trait_root`; and the gear/craft artifacts really ARE bound to their
  content via the mint seed (`blake3(crafter_pk || craft_commitment)`, and `craft_commitment` includes
  `artifact.content_digest()`), so the item's content address does encode what was forged. **The falsehood
  is narrowly the "(E1 closed)" label plus the "the sprite / gear crates read it" sentence.** It is
  load-bearing for orientation precisely because a sibling crate's doc asserts the opposite.
- **FIX A (mandatory, doc-only):**
  1. `:59-64` — retitle "**`trait_root` (E1 closed)**" → "**`trait_root` (E1: the field is committed; no
     consumer reads it yet)**" and rewrite to the CURRENT resolution: the field is a first-class 32-byte
     root, committed in `note_digest`, carried `WriteOnce` across the lineage; `mint_with_traits` commits
     an explicit root; plain `mint` populates it with `default_trait_root(asset_id)`. **Then state plainly
     that NO consumer reads it today** — sprite still derives from raw `AssetId` bytes
     (`dreggnet-sprite/src/lib.rs:22-25`), gear binds its `StatBlock` via the MINT SEED
     (`dreggnet-gear/src/gear.rs:149`). **Delete the "instead of re-deriving from the raw AssetId bytes as
     a TCB workaround" clause — that workaround is still the live path.**
  2. Same edit at `:155`, `:188-189`, `:760-764`.
  3. Move `trait_root` out of the `:57` "First-class asset properties" list's closed framing into the
     `:86` **NAMED SEAMS (not built here)** list: "**a trait-root CONSUMER** — the field is committed and
     readable via `trait_root_of`, but the sprite/gear crates still derive from the AssetId; wiring them
     is the open leg of E1."
- **FIX B (the real close — makes the doc true rather than the doc weaker):**
  1. `dreggnet-gear/src/gear.rs:149` → `self.world.mint_with_traits(smith_label, &stats.traits_root(),
     stats.traits_root())`, so the gear asset's committed `trait_root` field IS the StatBlock digest
     (**keeping the mint seed as-is preserves the existing AssetId — non-breaking for the id**). Then
     `trait_root_of(gear.asset_id) == stats.traits_root()` — assert exactly that in a gear test.
  2. `dreggnet-craft/src/forge.rs:354` → `mint_with_traits(player, &commit,
     artifact.stats.traits_root())` (craft already computes that digest at `draw.rs:218` and folds it into
     the mint seed), so a crafted item's committed trait_root carries its stat content rather than a hash
     of its own id.
  3. `dreggnet-sprite` — add `render_*_from_trait_root(root: [u8;32])` seeding the `DrawStream` from the
     COMMITTED root via `trait_root_of`, making the AssetId-seeded path the explicit fallback for assets
     minted without an explicit root. Update `dreggnet-sprite/src/lib.rs:25` and `:42-44` to stop listing
     E1 as unbuilt.
  4. **Only after 1-3 land AND a test outside `dreggnet-asset/tests/asset_layer.rs` exercises
     `trait_root_of` may the "(E1 closed)" label go back on `:59`.**

### M12 — `InterfaceRef` — "the on-cell reference the Cell carries and the commitment binds" · **low**

- **CLAIM** — `cell/src/interface.rs:26-28` states the seam as fact, present tense: "4. `InterfaceRef` —
  **the on-cell reference the `crate::Cell` carries and the commitment binds**: the `interface_id` plus
  the method count (so a verifier sees WHICH interfaces a cell exposes and HOW MANY methods each
  declares)." · `:7-9` carries it in the opening paragraph too ("a first-class, **on-cell**, typed
  description of that interface **that the cell commitment binds** and a light client can witness").
- **TRUTH — verified at both ends, read not grepped:**
  1. **NO CELL FIELD.** `cell/src/cell.rs:249-300` read to the closing brace: id, public_key, state,
     permissions, verification_key, delegate, delegation, token_id, capabilities, program, mode,
     lifecycle, leaf_cache. **`Cell::interfaces` — the identifier the header names — does not exist.**
  2. **THE COMMITMENT DOES NOT BIND IT.** `compute_canonical_state_commitment`
     (`cell/src/commitment.rs:204-243`) hashes id, public_key, token_id, mode, state, permissions,
     verification_key, cap_root. **`grep -i interface cell/src/commitment.rs` returns ZERO hits across
     the entire file. The header's claim is not merely stale, it is unimplementable as written.**
  3. **ZERO CONSUMERS.** Repo-wide `InterfaceRef` = exactly 7 hits: the false header (`:26`), its own
     construction in `as_ref` (`:269-270`), its definition (`:457`), the re-export (`lib.rs:140`), the
     reference doc flagging it as stale (`docs/reference/services.md:38`), and the propagated lie
     (`deos-js-runtime/src/world.rs:215`).
  4. **THE LIVE PATH USES THE REAL THING.** `derive_replayable` reads `cell.program` only; its ~20
     consumers (`directory/src/service_factory.rs:90,212`; `dregg-payable/src/routing.rs:118,252`; the
     starbridge-apps service modules) never touch `InterfaceRef`. `dregg-payable/src/routing.rs:241` is
     honest: "reads only `cell.program`, no commitment."
- **Contradicted inside the same crate** at `lib.rs:42-45` ("A standalone, **NON-committed** type … the
  descriptor is **not folded into the cell commitment**") and by `docs/reference/services.md:33-40`, which
  states "**The interface is a USERSPACE object, NOT a committed cell field.** There is no
  `Cell::interfaces` field and the cell commitment does not bind the descriptor — the v9→v10 commitment
  bump that would have committed it was **backed out**," and explicitly names this module header as stale.
  **The reference doc wins by precedence** (`docs/reference/` at file:line@HEAD beats a stale header).
- **THE ROT IS BROADER THAN THE HEADER (not in the original finding):** the `InterfaceRef` struct doc at
  `:447-448` names the nonexistent field directly ("the value a `crate::Cell` carries in
  `Cell::interfaces` and the cell commitment binds"); **`:453-455` asserts a light-client property that
  cannot hold** — "change a method, the `interface_id` changes, **the cell commitment changes**" (the
  commitment cannot change; it never reads the interface); `as_ref`'s doc (`:267-268`) repeats it a third
  time.
- **Severity stays low but is not inert:** zero consumers ⇒ zero runtime consequence, but
  `deos-js-runtime/src/world.rs:215` **already copied the framing into a second crate**, sitting atop
  `publish_interface` whose real impl (`entry.interface = Some(descriptor)`, `world.rs:223`) stores the
  descriptor in the runtime's OWN cells map — **a userspace side table, which is the honest shape the
  comment misdescribes as a commitment mirror.**
- **FIX (PREFERRED — delete the dead surface; zero consumers ⇒ non-breaking):**
  1. Remove `pub struct InterfaceRef` (`:447-463`) and `InterfaceDescriptor::as_ref` (`:267-274`) —
     `as_ref`'s only purpose is constructing a type nothing reads.
  2. Drop `InterfaceRef` from the re-export list at `cell/src/lib.rs:140`.
  3. Delete header item 4 (`:26-28`). Items 1-3 (Semantics, MethodSig, InterfaceDescriptor) are accurate.
  4. `:7-9` → "a first-class, content-addressed, **typed** description of that interface, resolved in
     USERSPACE above the effectvm/commitment (the commitment does not bind it — see the `interface` module
     note in `lib.rs` and `docs/reference/services.md`)."
  5. `deos-js-runtime/src/world.rs:215` → "The descriptor is a userspace object held in this runtime's
     cap-table row (`entry.interface`); the cell commitment does not bind it."
- **IF `InterfaceRef` must be kept** (e.g. an intended S2 captp-handshake wire value), **RELABEL as
  unbuilt, not asserted:** "**A userspace reference to an InterfaceDescriptor** — the content-address +
  method count, for out-of-band resolution. **NOT an on-cell field and NOT commitment-bound**: there is no
  `Cell::interfaces`, and `compute_canonical_state_commitment` does not read the interface. The v9→v10
  bump that would have committed it was backed out. Currently unused; retained for the S2 captp
  handshake." **Delete the false light-client claim at `:453-455` outright — it is the load-bearing
  falsehood and must not survive in any form.**
- **CROSS-CHECK after the edit:** `grep -rn "InterfaceRef\|Cell::interfaces" --include="*.rs"
  --include="*.md" .` should return only intentional, correctly-labeled hits.
  `docs/reference/services.md:37-40` should then drop its "the module header still carries the earlier
  framing" parenthetical, since the superseded framing will be gone rather than merely flagged.

### M17 — the `*_equivalence_*` tests reconstruct their peer IN PROSE; the peer is not linkable · **low-medium**

- **CLAIM** — `dregg-dsl-tests/src/dregg_definitions.rs:4-8`: "These run ALONGSIDE (not replacing) the
  hand-written code in `token::dregg_caveats`. **The equivalence tests below verify that the DSL-generated
  evaluators produce the SAME results as the hand-written versions for matching inputs.**" ~30 tests named
  `test_*_equivalence_*` sell it.
- **TRUTH** — `grep -rn "token::" dregg-dsl-tests/` returns **exactly ONE hit in the whole crate: the doc
  comment at line 5 making the claim.** `dregg-dsl-tests/Cargo.toml` `[dependencies]` = blake3, dregg-dsl,
  dregg-dsl-runtime, dregg-circuit. **No `token`. The peer is not linkable, so the equivalence is
  unreachable, not merely unperformed.** Each test calls `{name}_check(..)` and narrates the peer's alleged
  behavior in a COMMENT (`:208-210`, `:253-254`, `:332`, `:507`):
  ```rust
  #[test]
  fn test_not_after_equivalence_pass() {
      assert!(not_after_check(100, 50).is_ok());
      assert!(not_after_check(100, 100).is_ok()); // boundary: equal is OK
      // Hand-written equivalent: verify_caveats with ValidityWindow(None, Some(100))
      // checks `now > not_after` => fail. So now=50, not_after=100 => pass. ... Matches DSL.
  }
  ```
  **Prose cannot drift-detect — the strongest possible form of a re-authored mirror.** If `verify_caveats`
  changed its boundary semantics tomorrow, all 30 stay green.
- **REFUTATION VECTORS TESTED, BOTH FAILED:** (1) the CAVEAT-level modeling IS scrupulously labeled
  (`TODO: needs Phase 3` at `:27, :35, :43, :80, :107, :113, :140, :146`; "This is a PLACEHOLDER" at
  `:111`; `:481` and `:492` explicitly named placeholder tests) — **honest labeled low-resolution work,
  not faulted. But it covers the modeling gaps, NOT the equivalence gate; lines 7-8 are a separate claim
  and carry no label.** (2) sibling `dregg-dsl-differential`'s description ("run every verifier we can run
  in-process, assert they agree") is the shape of the missing gate but is cross-**BACKEND**, not
  cross-**IMPLEMENTATION**, and also has no `token` dep (`grep -rn "verify_caveats|token::"
  dregg-dsl-differential/` = zero). No rescue.
- **SEVERITY CORRECTION THE FINDING MISSED — the nominated "real thing" is itself off the live path.**
  `verify_caveats` is **`#[deprecated]`** (`token/src/dregg_caveats.rs:384-387`) and its own doc at
  `:379-383` says it "uses imperative string-matching logic that is **NOT the canonical semantics**. Use
  `crate::datalog_verify::verify_token_datalog_full` instead, **which evaluates via Datalog (the ground
  truth for both trusted and trustless modes)**." Every caller is inside its own in-file unit tests
  (`:869-:1108`). **Neither side of the claimed equivalence gates a real authorization decision — and the
  implied fix "point the tests at `verify_caveats`" would wire a gate to a disowned oracle.**
- **FIX (1) — DELETE THE CLAIM (preferred; honest, cheap, matches current resolution):** strike
  `dregg_definitions.rs:7-8` and replace with what is true: these are DSL-side unit tests plus
  AIR-descriptor checks; **the hand-written peer is NOT linked from this crate and no cross-implementation
  equivalence is checked.** Rename `test_*_equivalence_*` → `test_*_semantics_*` (~30 tests) **so no test
  name sells a gate that does not exist.** Keep the prose comments at `:208, :253, :332, :507` but relabel
  them "modeling note (unchecked)" so they read as intent, not evidence.
- **FIX (2) — BUILD THE REAL GATE (only if the equivalence is actually wanted):** add
  `token = { path = "../token" }` to `[dev-dependencies]` (safe — `dregg-dsl-tests` is a leaf crate, no
  cycle). Make each test CALL the peer:
  ```rust
  let set = /* CaveatSet with DreggGrant::ValidityWindow { not_before: None, not_after: Some(100) } */;
  let req = /* AuthRequest { now: Some(50), .. } */;
  assert_eq!(not_after_check(100, 50).is_ok(), <peer>(&set, &req).is_ok());
  ```
  **CRITICAL — point `<peer>` at `token::datalog_verify::verify_token_datalog_full`
  (`token/src/datalog_verify.rs:1491`), NOT at `token::dregg_caveats::verify_caveats`
  (`token/src/dregg_caveats.rs:388`).** Wiring the gate to `verify_caveats` would freeze the DSL against an
  oracle the codebase has already disowned. **(2) is only honest for the caveats whose DSL form is not a
  declared placeholder — `confine_feature_glob` (`:109-115`) and `confine_ip_range` (`:142-148`) cannot be
  equivalence-tested at Phase 1-2 and must stay explicitly excluded, not silently passed.**

### M18 — `attested-dm/Cargo.toml` asserts "from a real model"; the crate contains no LLM · **low-medium**

- **CLAIM** — `attested-dm/Cargo.toml:6` — "`authentic` — **from a real model** (a genuine `/v1/messages`
  session), not forged;" · `:48-49` — "each narration carries a `verify_zkoracle`-checkable proof it is
  **from a real model** (authentic), well-formed, and injection-free".
- **TRUTH — the crate's own `lib.rs` was swept honest and the manifest was left behind, contradicting it
  head-on.** Live path: `DungeonMaster::recorded` (`lib.rs:1421-1422`) wires `RecordedDm` +
  `DmAttestationCarrier::default()`; `default` (`:204-207`) → `from_seed(&DEFAULT_DM_SEED)` →
  `FixtureNotary::from_seed` (`:213`); `attest_narration` (`:266`) → `attest_body_with_stark` (`:246`) →
  `build_anthropic_fixture(&self.notary, ...)` (`:248`). **The notary is a self-held key; there is no
  `/v1/messages` session and no model anywhere in the crate:** `[dependencies]` (`:47-76`) is
  dregg-zkoracle-prove, dregg-dice, blake3, dregg-node-target, serde, serde_json — **no dregg-narrator, no
  AWS SDK, no HTTP client.** `grep bedrock attested-dm/` hits ONLY doc prose pointing at
  `deos_hermes::attest::attest_turn_bedrock` (`lib.rs:32-34, 293-294`) — **the real-model path is
  explicitly ELSEWHERE.** The only `DmBrain` impl is `RecordedDm` (`lib.rs:1214-1226`), a `format!`
  string-formatter.
  Against that, `lib.rs` says: `:8-9` "authentic — the session leg (see PROVENANCE below — **the default
  path is a SELF-SIGNED test double, NOT proof of a real model**)"; `:21-26` "a **SELF-SIGNED FIXTURE** …
  it could mint any body it liked and every leg would still verify … proves the PRODUCE→VERIFY plumbing
  and **nothing whatever** about where the narration came from"; `:37` "*provably came from a real model*
  **holds only on the Bedrock path**"; `:73-74` "Because the default `authentic` leg is a fixture, entry
  forgery is prevented by the chain-link + receipt-id binding + head anchor, **not by attestation
  authenticity**".
- **REFUTED — `Cargo.toml:41` (the published `description`, "a confined + **attested LLM narrator**") is
  NOT a lie relative to the file it is accused of contradicting.** It is the SAME headline register
  `lib.rs:3` still uses today — "A **confined + attested LLM** narrates an on-chain interactive world" —
  before its PROVENANCE caveat at `:15-37`. **It is not a line left behind by the sweep. DO NOT EDIT IT
  in isolation** — that would just move the inconsistency. If the intent is to drop the headline, that is
  a separate decision that must change `lib.rs:3` and `Cargo.toml:41` (and probably `:3`) **together**.
- **TWO MORE THINGS THAT NARROW THIS:** (1) the manifest is not uniformly lying — `Cargo.toml:18-28`
  already says "the **modeled** ed25519 authentic carrier + the JSON CFG parse-cert + the injection
  matcher" and "The real local MPC-TLS 2PC roundtrip is behind `tlsn-live`". **The defect is an INTERNAL
  self-contradiction inside one file (line 6 vs lines 22-26), not a crate-wide misrepresentation.**
  (2) `DmBrain` (`lib.rs:1200-1207`) is a **legitimate trait abstraction with a real impl one crate over**
  — `deos-hermes/Cargo.toml:92` wires `dregg-narrator` (Bedrock Claude/Nova → Ollama → scripted) into
  `narrator_crown`. `RecordedDm` is a **LABELED** default (`lib.rs:77-78` "MODELED — the brain … a
  deterministic stand-in for a live LLM"). **Nothing about the code is dishonest and nothing about the
  brain is unlabeled. What survives is precisely two lines of manifest prose.**
- **FIX — two prose edits, adopting the register already proven at `deos-hermes/Cargo.toml:92` ("the
  authentic leg the fixture carrier by default, the real MPC-TLS 2PC under `zk-live`") and already used at
  `attested-dm/src/lib.rs:8-9`:**
  1. `Cargo.toml:6` → 
     ```
     #   authentic     — the session leg: a SELF-SIGNED fixture carrier by default (it proves the
     #                   PRODUCE->VERIFY plumbing, NOTHING about where the narration came from);
     #                   real MPC-TLS transport provenance under `tlsn-live`; real MODEL provenance
     #                   only via `deos_hermes::attest::attest_turn_bedrock`. See `authentic_provenance`.
     ```
  2. `Cargo.toml:48-49` → "a `verify_zkoracle`-checkable proof it is **well-formed and injection-free**,
     carrying an authentic leg whose provenance is the fixture carrier by default
     (`AuthenticPolicy::AllowFixture`) and a real MPC-TLS presentation under `tlsn-live`
     (`AuthenticPolicy::RequireMpcTls`)".
  3. **DO NOT change `Cargo.toml:41`.**
- **No canary needed** — no soundness hole, no code defect, no test lies. `verify_zkoracle` admits the
  fixture only under `AuthenticPolicy::AllowFixture`, and `AuthenticPolicy::RequireMpcTls` refuses it
  outright (`lib.rs:26, 93-95`).

*(M02's doc leg, M09's doc leg, and M04 also belong to this variant; filed under their primary shape.)*

---

# §2 — RANKING

## §2.1 By severity

| Rank | ID | Severity | Kind | Blast radius | Exploitable at HEAD? |
|------|----|----------|------|--------------|----------------------|
| 1 | **M13** | **CRITICAL** | soundness-hole | deployed circuit — `bridge`/`wire` verify path | **YES** — `fact_commitment` is a free-floating PI; a predicate proof does not bind to token state |
| 2 | **M01** | high | soundness-hole | game/faction demo layer, but its whole headline claim | **YES** — stapled unlock at rep 0 on the only deployed program |
| 3 | **M14** | high | soundness-hole (gate dead) | the CI gate protecting all 25 by-name goldens | n/a — it is the mechanism that let M13 ship |
| 4 | **M11** | high | soundness-hole (tripwire dead) | executor↔AIR projection; 4 sites cite a fictional invariant | no live exploit; a real SetField divergence is shipping undetected |
| 5 | **M21** | high | soundness-hole (proof scope) | metatheory guarantee A's warrant | no — 27 vs 33; `Promise`/`React`/`ShieldedTransfer` unexamined |
| 6 | **M07** | **closed 2026-07-20** | repaired false-claim | 4 shipped frontends incl. the hbox devnet | no — the committed/rendered hand is now derived from the engine deal |
| 7 | **M05** | high | false-claim | the flagship `Adventure::play` loop | no value; a faucet where a fair draw is claimed |
| 8 | **M16** | high (harness) | false-claim + real AIR bug | the differential harness's advertised teeth | the diff-le AIR is genuinely forgeable in range |
| 9 | **M15** | medium | soundness-hole (sim vacuous) | CI differential; conceals a live `gen_kimchi` emitter bug | no — emit-only backend |
| 10 | **M03** | medium | false-claim | griefing/DoS only — `cross_leg` closes theft | cancellation of a live trade by any `&mut TradeWorld` holder |
| 11 | **M06** | medium | false-claim | guild aggregate/ranking | no — ungated `pub fn admit` already hands out the cap |
| 12 | **M09** | medium | false-claim + trapdoor | `apply_choice`, advertised as sole referee | **no shipped scene trips it** — latent for the next author |
| 13 | **M20** | medium | soundness-hole (as-documented) | node devnet, `--prove-turns` off by default | no — commitments inert; (balance,nonce) truthful |
| 14 | **M02** | medium | false-claim | multislot set-bonus (no owner check anywhere) | no value at stake |
| 15 | **M08** | medium | false-claim | automatafl attestation surface | no — teeth + AIR + resume replay unaffected |
| 16 | **M10** | medium | false-claim (proof is the mirror) | 3 chat-surface parity suites | no — parity true today, unenforced |
| 17 | **M19** | medium | false-claim | demo + tests only; **conceals a real absence** | no — but the marquee cross-chain demo is the exposure |
| 18 | **M17** | low-medium | false-claim | ~30 test names sell an unreachable gate | no — both sides off the live path |
| 19 | **M18** | low-medium | false-claim | 2 lines of registry-facing manifest prose | no |
| 20 | **M04** | low | false-claim (doc-only) | orientation; a sibling crate asserts the opposite | no |
| 21 | **M12** | low | false-claim (doc-only) | orientation; already propagated to a 2nd crate | no |

**Duplication tier (no separate findings, but the same disease):** the `SeatedTug` adapter triplicated
across `dreggnet-web/src/seated.rs` + telegram + wechat (`seated.rs:14` in both self-describes as "a
byte-for-byte peer"); the 10 hand-retyped offering registrations (M10 part 2); the double Lean mirror
`EffectTag` vs `DeployedEffect` (M21 part 3); the 24-of-25 emit gates that re-declare `GOLDEN_JSON`
rather than `include_str!`ing it (M14).

## §2.2 By leverage — the lanes

**Ranked by (findings closed) × (severity closed). A build swarm should take L1 first and L2 in
parallel; L1's step 1 is the only item where value is at stake today.**

### L1 — THE LEAN→ARTIFACT TRANSPORT GATE · closes **M13 (CRITICAL) + M14 (high)**, structurally prevents both
*One lane. The two findings are one disease: Lean pins a GOLDEN, an ungated hand transcription carries
it to disk, and the drift script never re-derives the subtree.*
1. Regenerate `circuit/descriptors/by-name/predicate-arith.json` from the Lean guard (M13 §1) — route
   through `DREGG_VK_REGEN_ACK` per `docs/VK-REGEN-CONTROLS.md`.
2. Lift `predicate_arith_witness.rs` to width 24 (M13 §2). Flip `:157` from ratifier to canary (M13 §3).
3. `include_str!` the deployed file in `predicates_arithmetic_emit_gate.rs:70` (M13 §4) — **and apply the
   same rule to the other 23 emit gates** (`turn_chain_emit_gate.rs:47` is the only one already correct).
4. Make `by-name/` genuinely emitted: `emit_descriptors.py` EMITTERS + `DESC.rglob` + delete
   `collect_by_name_hashes` (M14 §2).
5. Ship the ~20-line guard-vs-disk interim check TODAY (M14 §3), resolving named-def goldens.
6. Land the tamper canary (M13 CANARY).
**Why first:** M13 is the only finding where a prover can produce a false verified statement on a
deployed path. M14 is why nobody noticed. Fixing either alone leaves the other's failure mode live.

### L2 — POINT EVERY HARNESS AT THE REAL ARTIFACT · closes **M11 + M10 + M15 + M16 + M17**, and half of M14
*One mechanical rule, five applications: **a test may not re-declare an object it can import.***
- M11: delete `project_turn_to_vm`, call `dregg_turn::executor::convert_turn_effects_to_vm`. **Expect
  `differential_set_field` to go RED — that red is the deliverable.**
- M10: `dev-dependencies` on `dreggnet-web`, derive `want` from `demo_host()`, assert **set equality**.
- M15: make `eval_generic` the sole decision procedure; Skip what cannot be evaluated.
- M16: delete `prove_trivial`; Skip out-of-range; **then fix the forgeable AIR (independent, do not skip)**.
- M17: either delete the claim + rename 30 tests, or dev-dep `token` and point at
  `verify_token_datalog_full` (**never** at the `#[deprecated]` `verify_caveats`).
**Every one of these is a dev-dependency edit + a delete. None requires new architecture.**

### L3 — ONE AUTHOR PER PROGRAM · closes **M01 (high) + M19**, prevents the twin-engine variant
- M01: factor `push_slot_bound_faction_gates` and call it from BOTH `faction_compiled` and
  `Roster::compile` — **the drift is the root cause, not the symptom.**
- M19: `#[deprecated]` + `#![deny(deprecated)]` turns the alias's prose prohibition into a build failure;
  then build the weighted verified ballot and **delete both aliases so the collision cannot recur.**

### L4 — IDENTITY IS THE KEY THAT SIGNS · closes **M03 + M06**
*Both are a re-authored identity/roster sitting next to the real cap/key, bound by a label string or a
convention.* M03: `party_cell` becomes a function of `assets.pubkey_of(label)`. M06: delete
`GuildBoard::members`, mint an unforgeable `Membership` witness from a real cap-bounded turn. **Both have
a working in-tree exemplar one rung up** (`dreggnet-guild/src/treasury.rs:73-96` for M03;
`act_on_guild` for M06).

### L5 — FAIL CLOSED ON THE UNREPRESENTABLE · closes **M09 + M20**
*Both arms silently fall back to a weaker/synthetic shape where the strong one could not be built.*
M09: `apply_choice` refuses `fully_gated == false`. M20: seed the `None` arm from the real cell, and keep
`CellState::new` only where the cell is genuinely fresh. **The information needed is already captured in
both cases** (`self.story.fully_gated`; `full_turn_pre_cell` cloned at `blocklace_sync.rs:4404`).

### L6 — SHIP THE COMPOSING TYPE · closes **M02 + M05**
*Both have the real primitive built, tested, and one call away; the loop calls the faucet next to it.*
M05 is a two-line swap into `CraftForge::mint_loot_material` (already exists, already tested). M02 needs
`OwnedSet`, a 20-line mirror of `gear::Loadout`.

### L7 — THE HAND-TRANSCRIBED ROSTER · closes **M21**, and generalizes L1
*Same disease as L1 at the enum level rather than the byte level. The Rust-side exhaustive `match` with
no `_` arm is the enforcer; the Lean-emitted TSV is the transport. **Do both or strike the claim.***

### L8 — DOC-ONLY SWEEP · closes **M04 + M12 + M18**, plus the doc legs of M02/M09/M16/M17
*Cheap, mandatory, and must not be mistaken for closure.* Note **M12's preferred fix is a deletion**
(zero consumers), and **M18 must not touch `Cargo.toml:41`**.

---

# §3 — STRUCTURAL ANALYSIS

## §3.1 Why this codebase keeps producing this shape

Not carelessness. Every one of the 21 was produced by a **method working correctly** — and the mirror is
the method's exhaust. Five mechanisms, each visible in the evidence:

**(1) The iterative/approximative method builds the whole system at low resolution first — and the
LABEL is the only thing holding the low-resolution part in place.** A label is prose. Prose does not
survive a refactor, a second author, or a promotion. Every finding here is a case where the *code* was
honest at its own altitude and a doc **one level up** asserted the intended resolution:
`forge_run_loot`'s own doc says "the fair-draw-seeded material **faucet**" while the crate doc sells a
real fair draw (M05). `compiler.rs:76-79` says "left to the runtime/handler gate and **no executor
constraint is emitted**" while `lib.rs:14-17` says "the executor admits **IFF** the gate passes" (M09).
`predicate_arith_witness.rs` concedes "There is no in-circuit hash tooth on FACT_COMMITMENT" **in the
same docstring** that claims it is "dispatched from the Lean-#guard-pinned golden" (M13).
`kimchi_sim.rs:15-21` honestly labels the Poseidon delegation and `lib.rs:33` says "asserts **every**
gate's polynomial evaluates to zero" (M15). `attested-dm/src/lib.rs:21-26` was swept honest and
`Cargo.toml:6` was left behind (M18). **The truth is almost always already written down, one file away,
by the same author. The lie is a promotion.**

**(2) A second author is created by every generator, port, and re-implementation — and nothing forbids
divergence.** `Roster::compile` vs `faction_compiled`; `HostBallotBox` vs `collective_choice`;
`telegram_default_host` vs `catalog_default_host`; `EffectTag` vs `DeployedEffect` (**two Lean
transcriptions of one Rust enum, which disagreed 27 vs 33 and both compiled**); `project_turn_to_vm` vs
`convert_turn_effects_to_vm`; `predicate-arith.json` vs `predicateGeDesc`. **Where the tree factored the
shared thing, no drift occurred** — `register_surfaces` is "the ONE call web makes, reused verbatim"
(`dreggnet-web/src/lib.rs:2022`), and **exactly those 8 of 18 keys are the only ones not at risk** (M10).
That is the control experiment, in-tree, and it is decisive: **sharing prevents this; discipline does
not.**

**(3) The test is written by the author of the mirror, in the mirror's vocabulary, so it inherits the
mirror's blind spot as its coordinate system.** `case_constraints` (`lib.rs:460-470`) filters
`MethodIs` — so `generated_teeth_are_real_per_faction` **would pass byte-identically if every slot-bound
gate in the crate were deleted** (M01). `seat_card_ids` reads `session.hands`, the fabricated array
(M07). `predicate_arith_dispatches_with_expected_shape` asserts `trace_width == 5` — **the mirror is
defended by CI; restoring the truth turns a green test red** (M13). `air_claim` generates the AIR trace
**from** the reconstruction, so mirror is compared to a trace of mirror (M11). This is why "green"
carried no information here: **the harness and the artifact were the same object.**

**(4) Verification apparatus is exempt from the verification standard.** `check-descriptor-drift.sh`'s
header states the self-consistency fallacy in precise, correct terms — and its by-name leg commits it
(M14). `effect_vm_differential.rs` justifies its mirror with **two claims that are factually impossible**
("module-private" — it is `pub use`d at `mod.rs:737`; "independent of the executor crate" — it imports
`TurnExecutor` at `:39-42` and constructs it in every test). Nobody audits the auditor, so the auditor
drifts furthest.

**(5) The alias/name is doing the lying, and names are invisible at the use site.** `CollectiveChoice`
resolves to a verified engine in `dregg-pay` and to a `HashSet` in `dregg-interchain-gov`. Both descriptors
carry the wire name `dregg-predicate-arith-ge::threshold-v1`. **A reader cannot see the difference, and
evidently the author could not either** — `dregg-interchain-gov` did the exact thing
`dregg-governance/src/lib.rs:578-586` forbids **in writing**, because the prohibition was prose and the
name was code.

**The one-sentence diagnosis:** *the tree consistently makes the true statement at the altitude where the
code lives and the false one at the altitude where the reader lives, because the correspondence between
the two is carried by prose, and prose has no compiler.*

## §3.2 Making each variant UNREPRESENTABLE

The reference move — the caveat-DSL fix bound to AST identity, where the bug class **cannot be
expressed** — generalizes to one rule per variant. **The test of a proposed fix: after it, can a
competent, well-meaning author still produce this finding? If yes, it is a repair, not a closure.**

| Variant | The bug class | The move that makes it unrepresentable |
|---|---|---|
| **twin-engine** (M01, M19) | two constructors of one program, free to diverge | **There is only one constructor.** Both callers invoke `push_slot_bound_faction_gates`; the shape exists once, so "identical in shape" is a tautology rather than a claim. For M19: **delete the alias** — a demoted twin retained under a colliding name is a loaded gun; `#[deprecated]` + `deny` is the interim, deletion is the closure. |
| **re-authored-peer** (M07, M03, M20) | two objects constructed side-by-side from the same seed | **Make one a FUNCTION of the other, not a peer of it.** `hands: commit_dealt_hands(&engine, seed)` — hands cannot disagree with engine because hands is *derived from* engine (M07). `party_cell(label) = f(assets.pubkey_of(label))` — one identity, not two label-parallel KDFs (M03). `initial_vm_state = f(pre_cell)` — the fiction is unconstructible when the real cell is in scope (M20). **The type system enforces this for free once the peer's constructor stops existing.** |
| **fixture-on-live-path** (M05, M02, M08) | the faucet and the real primitive have the same signature, so the loop can call either | **Make the fixture un-callable from the live type.** Delete `mint_material`'s reachability from `forge_run_loot` — better, make `LootDraw` a **required argument** so there is no way to mint a material without a drop (M05). Give `SetBonusGate` no way to exist outside `OwnedSet` on the public surface (M02). For M08: **give `verify` no access to `session.board`** — if the function cannot see the host's memory, it must replay. |
| **host-vs-proven** (M06, M09) | a host structure and a proven gate both type-check as "the membership/eligibility answer" | **Make the answer an unforgeable witness minted only by the proven path.** `record_clear(&self, witness: Membership, ..)` where `Membership` has a private constructor reachable only from a committed `act_on_guild` turn (M06). `apply_choice` refuses `fully_gated == false` — **the primitive structurally cannot commit a turn whose gate it did not check** (M09). |
| **shared-constant** (M03) | two systems agree because they were handed the same string | **Derive one from the other's authenticated output.** The label must stop being the join key; the pubkey becomes it. **A shared constant is a join with no foreign key.** |
| **fresh-per-caller-world** (M07, M05's vault) | each caller builds its own world, so nothing crosses | **Thread the ledger, do not re-mint it.** M05's fix is specifically *not* `LootVault::claim` (private `AssetWorld`, no `into_assets()`) but `CraftForge::mint_loot_material` (**same ledger the live path already holds**). The rule: **a primitive that owns a private world and exposes no handoff cannot be composed — and will therefore be mirrored.** |
| **harness-tests-its-own-mirror** (M11, M13, M14, M10, M15, M16, M17) | a test re-declares an object it could import | **`include_str!`/`use` or it does not count.** A golden that is a `r#"..."#` literal is not a golden; a roster that is a `[&str; 18]` literal is not a parity proof. Mechanically: **no test may contain a `const` whose value duplicates a shipped artifact.** M14's `DESC.rglob` + emitter routing makes an un-emitted descriptor a **routing-gap FAILURE**, not a silent exemption. |
| **lean-models-reauthored-shape** (M21, M13) | Lean's compiler proves totality over the transcription, and prose calls it a proof about Rust | **Transport the object, do not re-type it.** Lean emits a TSV/JSON; Rust `include_str!`s it and diffs against an exhaustive `match` **with no `_` arm** — so a new Rust variant **fails to compile** until the roster names it, and a drifted golden fails the diff. **The Rust compiler is the only thing that can see the Rust enum; the Lean compiler is the only thing that can see the Lean roster. The gate must be the diff between their outputs, never either compiler alone.** And: **one mirror can be gated; two mirrors cannot** — collapse `EffectTag`/`DeployedEffect`. |
| **doc-claims-absent-seam** (M16, M04, M12, M17, M18) | a doc asserts a mechanism at an altitude where no code contradicts it | **Encode the claim as a check.** M13's `:171` weld sentence becomes `assert!(poseidon2_lookups >= 1)` in `dispatch_names_decode_and_check`. M04's "(E1 closed)" label is earned only by a test outside the crate exercising `trait_root_of`. **A doc claim with no executable dual is a name, not a proof** — and M12's fix is the strongest form: **delete the type nothing reads**, so the claim has no subject. |

**The single highest-leverage structural move, if only one ships:** *an artifact that is loaded at
runtime may not also be typed by hand anywhere in the tree.* That one rule closes M13, M14, M11, M10,
M15, M17, M21 — **7 of 21, including the critical one and both dead tripwires.**

## §3.3 Detection — what catches the NEXT one automatically

Ranked by (bug class caught) ÷ (cost). Each is a real, buildable check, not an aspiration.

### D1 — THE RE-DECLARED-ARTIFACT LINT · catches M13, M14, M11, M10, M15, M17 · ~1 day
An `ast-grep` rule + CI job:
- **Flag any `const NAME: &str = r#"{...}"#` or `= "{...}"` in a `tests/` or `#[cfg(test)]` scope whose
  parsed content matches a file under a registered artifact dir** (`circuit/descriptors/**`,
  `metatheory/emitted/**`). Require `include_str!`. **`turn_chain_emit_gate.rs:47` is the compliant
  exemplar; the other 24 emit gates are the violations.**
- **Flag any `const X: [&str; N]` in a test whose elements are a hand-typed roster of a registry the
  crate could dev-dep.** (`EXPECTED_KEYS`.)
- **Flag any fn in `protocol-tests/`, `*-differential/`, or `tests/` whose doc says "Mirrors `X`" /
  "Kept inline" / "independent of the … crate" where `X` resolves to a public path.** `project_turn_to_vm`'s
  own doc comment names its violation.

### D2 — THE CITATION CHECKER · catches M11, M13, M14, M21, M04 · ~1 day, highest truth-per-line
A script over all `//!`/`///`/`#`-comments extracting **claims that name a mechanism**, and asserting the
mechanism exists:
- `"asserted by the … in `path`"` ⇒ **`path` must exist AND contain an assertion referencing the cited
  symbol.** *(M11's citation appears at 4 sites and resolves at 0.)*
- `` "`X` is module-private" `` ⇒ **`X` must not be `pub use`d.** *(M11: `mod.rs:737`.)*
- `` "verbatim from the Lean #guards" / "extracted verbatim" `` ⇒ **the file must be byte-equal to the
  named guard.** *(M13.)*
- `` "reads it via `F`" / "consumer reads … via `F`" `` ⇒ **`F` must have >= 1 caller outside its own
  crate's tests.** *(M04: `trait_root_of` has 0.)*
- `` "the commitment binds X" `` ⇒ **`X` must appear in the commitment fn.** *(M12: zero hits in
  `commitment.rs`.)*
- `` "the SAME N offerings `C` registers" `` ⇒ **the citing crate must dep `C`.** *(M10.)*
**Every finding in this map cites its own falsifier in its own prose. The claims are already written in a
near-checkable register — this makes them checkable.**

### D3 — THE LIVE-PATH-VS-TESTED-PATH DIFF · catches M01, M05, M19, M02, M17 · ~2 days, the sharpest signal
For each `pub fn` that constructs/deploys a program, world, or engine, compute (a) its callers outside
the defining crate, (b) its callers inside `#[cfg(test)]`. **Report every symbol where (a) is non-empty
and (b) is empty, and where a sibling symbol has the inverse profile.** That exact query, run against
`dreggnet-faction`, prints M01 as one line:

```
Roster::compile      external: dreggnet-quest/src/giver.rs:517    tests: (none)
faction_compiled     external: (none)                             tests: lib.rs:801, lib.rs:864
```

**"The tested program is the one nothing outside the crate deploys; the deployed program is the one
nothing tests" is a mechanically detectable inversion.** M05 (`mint_loot_material` external: none, tests:
`forge.rs:407-446`) and M17 (`verify_caveats` external: none) fall out of the same query.

### D4 — THE STAPLEABLE-SLOT CANARY, PROMOTED TO A GATE · catches the M01 class · already minted
The standing falsifier exists. **Make it a test generator:** for every `CellProgram::Cases`, for every
slot written by any case, assert a `SlotChanged{slot}` case exists **or** the program carries an explicit
`#[allow(stapleable(slot, reason = "..."))]` naming the residual. `dreggnet-faction/src/lib.rs:423-430`
is the model of a legitimate exemption (the dynamic rival ceiling genuinely cannot be soundly
slot-bound); **`roster.rs`'s silence is what reads as coverage.** Make silence impossible.

### D5 — THE MUTATION CANARY, ENFORCED · catches M15, M16, M11, M06 · per-fix cost, no infra
Already minted as discipline; make it **a required field of every soundness-relevant test**: the test
must name the mutation that turns it red, and CI periodically applies it. Every vacuous check in this map
dies instantly under it — `gen_kimchi.rs:96 → vec![0,0,0,0,0]` leaves `cross_backend_differential` green
(M15); deleting every `SlotChanged` in `dreggnet-faction` leaves `generated_teeth_are_real_per_faction`
green (M01); deleting the range constraint leaves M16's suite green. **A falsifier that was never red
proves nothing.**

### D6 — THE ALIAS/NAME-COLLISION GATE · catches M19, M13 · ~half a day
Report any identifier exported under the same name by two crates where one is a `type` alias/`pub use`
rename to a differently-named type. `CollectiveChoice` (verified engine vs `HostBallotBox`) fires
immediately. Extend to artifact `"name"` fields: **two descriptors bearing
`dregg-predicate-arith-ge::threshold-v1` with different `trace_width` should be impossible to check in.**

### D7 — THE FAIL-CLOSED-FALLBACK AUDIT · catches M09, M20, M16 · ~1 day
Grep for the shape *"the strong path could not be built, so take the weak one"* — `return (vec![],
false)`, `_ => None`, `Some(rot) / None`, `if too_big { trivial() }` — and require **each such arm to
either refuse or carry a named residual with a test.** All three findings state the inversion in their
own comments (`compiler.rs:76-79`; `turn_proving.rs:722-729`; `plonky3_runner.rs:393`). **The tree
already knows where its fallbacks are; nothing forces them to be honest.**

**Adopt D1 + D2 + D3 first.** Together they mechanically catch **13 of 21** — including the critical one
— for roughly four days of work, and they are the three that catch findings *nobody was looking for*.

---

# §4 — HONEST COUNT: what was swept, what was not

## §4.1 The sweep

- **8 found by accident**, while doing other work: a mini faction cell; a governance twin engine; a
  self-signed notary; a re-implemented Mandate lattice; per-surface fresh worlds; host-computed-vs-AIR-
  proven; a shared constant instead of a cross-cell read; a differential harness validating its own
  hand-built descriptor. **Accidental discovery at that rate is itself the finding** — it implies a
  population, not a set of incidents.
- **13 subsystems** then hunted deliberately: `rpg-core`, `rpg-econ`, `rpg-social`, `games`,
  `story-engine`, `surfaces`, `kernel`, `circuit`, `dsl-codegen`, `metatheory`, `governance`,
  `node-federation`, `crypto-attest`.
- **21 findings survived adversarial verification.** Each had every refutation route tried; several were
  **narrowed or downgraded** by that pass, and some of the reporters' supporting evidence was **refuted**
  (M14's "5 goldens unpinned" — false, all 5 pinned via named defs; M10's "retypes all 18" — false, 8 are
  genuinely shared; M20's "every non-graduated effect" — false, NoOp-only at HEAD; M18's `Cargo.toml:41`
  — refuted outright; M04/M12/M17 downgraded to doc-only). **Those corrections are in §1 and must be
  carried, not re-derived** — a lane that repeats the refuted evidence will burn a day and reach the same
  place.

## §4.2 Denominator

The workspace is **~186 `members` crates** (+ excluded workspaces: `discord-bot`, `deos-zed-full`,
`dregg-tui`, `wasm`) across **219 top-level directories**. **13 subsystems were swept.** By any honest
accounting that is **well under half the tree**, and the swept fraction was chosen by where the
accidental 8 clustered — i.e. **biased toward where the disease was already known to live.**

## §4.3 NOT covered — named, with where I expect more and why

**High expectation (the disease's known habitat, unswept):**
1. **`starbridge-apps/*` — ~40 crates, ZERO swept.** This is the single largest gap and the highest
   prior. It is the exact shape that produced M01/M02/M05: many small app crates, each with a
   headline-claim module doc, each composing a real kernel primitive, each written fast. `escrow-market`
   and `privacy-voting` and `sealed-auction` and `bounty-board` and `execution-lease` all name teeth in
   their descriptions. **Note `NotYourLeg` was found live in `starbridge-apps/escrow-market/` during
   M03's grep — unexamined.** *Expect: fixture-on-live-path, doc-claims-absent-seam, host-vs-proven.*
2. **The rest of `metatheory/`.** M21 was found by counting ONE inductive against ONE Rust enum, and it
   had already drifted 27 vs 33 — **and a second Lean mirror of the same enum existed and disagreed.**
   Nothing was checked about the **other** hand-transcribed Lean shapes: `AssuranceCase.lean`'s other
   guarantees, `Circuit/Spec/*`, the Polis constitution files, the PQ metatheory's FIPS hypothesis.
   *Expect: more `lean-models-reauthored-shape`, and more `#assert_axioms`-clean-but-hypothesis-bearing
   statements — that class is orthogonal to this sweep and was NOT looked for at all.*
3. **The other 24 by-name emit gates + the 69 main descriptors.** M13 was found in **1 of 25** by-name
   goldens; the remaining 24 were byte-compared **only against their Lean guards** (all match today), but
   **the 69-file main set's gates were not audited for the `GOLDEN_JSON`-literal-vs-`include_str!`
   pattern** that made M13 invisible. **`presentation_descriptor_witness.rs:179` and
   `blinded_membership_witness.rs:347` define `GOLDEN_JSON` AS `include_str!` of the disk file — the
   "golden" IS the artifact, no Lean tie. That is a KNOWN, UNFILED instance of this variant.**
4. **`deos-*` (13 crates), `grain-*` (6), `crypto-*` (5), `chain/`, `eth-lightclient`,
   `cosmos-lightclient`, `solana-*`, `fhegg-*`, `sel4/`.** Entirely unswept. The Solana bridge already
   has 3 known exploitable value holes from a separate audit — **those are value holes, not necessarily
   mirrors, but the bridge fold is documented as UNSOUND and the light clients are the exact
   host-vs-proven shape.** *Expect: host-vs-proven, doc-claims-absent-seam.*
5. **`dregg-pq`, `pqvrf`, `dice`, `narrator`, `tee-verify`/`tee-produce`, `zkoracle-prove`,
   `deco-prove`.** Attestation/randomness crates — **M18 was the only `crypto-attest` finding and it was
   the mildest possible shape.** The subsystem was swept for one crate, not thirteen. *Expect:
   fixture-on-live-path (self-signed/modeled carriers), which is precisely M18's neighborhood.*

**Medium expectation:**
6. **`sdk/`, `cell/`, `turn/`, `circuit/` beyond the two kernel findings.** M11 and M12 were the only
   kernel findings and they came from two different directions; **the kernel was not swept
   systematically.** `sdk/src/cipherclerk.rs` carries M11's false citation twice and is 6000+ lines.
7. **`dreggnet-*` unswept members:** `market`, `compute`, `hermes`, `grain`, `council`, `doc`, `names`,
   `tournament`, `season`, `game-board`, `prove-service`, `offerings` (only touched via M08's trait
   contract). *The 9 dreggnet findings came from ~12 of ~28 crates — the hit rate in swept dreggnet
   crates was high enough that I expect several more here.*
8. **`demo/`, `web/`, `site/`, `extension/`, `launchpad-web/`, `sdk-ts/`, `sdk-py/`.**
   `demo/real-dungeon-service/src/main.rs:103,309-313` is **already known to carry M09's false
   "sole referee" claim** — filed under M09 but the rest of `demo/` is unexamined.

**Low expectation (but not zero):** `token/`, `macaroon/`, `secrets/`, `blocklace/`, `captp/`,
`persist/`, `storage/` — older, more settled, more single-authored.

## §4.4 What this sweep did NOT look for at all

- **The `#assert_axioms`-blind-to-HYPOTHESES class.** A `def FooHard` used as a hypothesis is an
  assumption; the axiom checker never sees it. Orthogonal to mirrors, same family of self-deception.
- **Vacuous/tautological theorem statements** (`P → P`) in Lean. M21 touched the registry's *scope*, not
  its theorems' *content*.
- **Floors that are EMPTY at deployed parameters** (the resolution-ruler class).
- **Non-Rust/Lean surfaces:** TS/Python SDKs, JS runtime, the site's machine-reader twin
  (`site/deep` is *by construction* a re-authored twin of `dregg.net` — **whether it drifts is exactly
  this question and was not asked**).

## §4.5 Expected true population

Extrapolating honestly: **13 subsystems, biased toward known-infected territory, produced 21 confirmed.**
The unswept ~60% is less biased but includes `starbridge-apps/*` (~40 crates of exactly the productive
shape) and the untouched Lean/kernel/bridge mass. **A defensible estimate is 35-60 total instances at
HEAD**, of which I would expect **2-5 more at soundness-hole severity** — most likely in
`starbridge-apps/*` (fixture-on-live-path), the light clients (host-vs-proven), and the unaudited main
descriptor set (the M13 shape).

**The count matters less than the shape of the count:** *the 8 accidental finds and the 13 deliberate
subsystems produced the same variants in the same proportions.* That is what a systemic defect looks
like, and it is why §3.2 (unrepresentability) and §3.3 (D1+D2+D3) are the deliverable — **fixing 21 and
shipping no gate returns this map to its current length within two quarters.**

---

*Written from the verified sweep, 2026-07-16, against HEAD `c451eb1f2`. Not committed. No source edited.*
