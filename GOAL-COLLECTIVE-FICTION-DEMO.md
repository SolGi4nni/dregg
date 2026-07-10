# GOAL: collective-fiction web DEMO-READY by morning

## ▶▶ THE DEMO RUNS — OPEN IT (verified by driving, screenshot at demo/run/screenshot.png)
```
node demo/serve.mjs      # then open http://127.0.0.1:8787
```
A self-contained page (NO extension): the REAL wasm StoryWorld loads "Founding the Commons", <dregg-story
collective> mounts in-page, and a crowd auto-plays each branch — you watch the assembly vote (5-1-1 → 5-2 → 5-2),
each winning branch a verified turn (receipts 1→2→3→4), landing on the ending where the founding record CAN'T be
rewritten, and "✓ receipt chain verified — nothing was rewritten." Pause + "vote yourself" too. The transcript of
a driven run: demo/run/transcript.txt.

A runnable artifact ember OPENS and SEES: a real verifiable story loads in a browser, a crowd votes each
branch (custody-signed turns, real CollectiveChoiceEngine quorum), the winner advances, the playthrough
replays. VERIFY BY DRIVING, not fixtures-pass. Bar: the artifact RUNS end-to-end + a captured run.

## THRUST: get a RUNNABLE demo first, then the netlayer + extension-less dream.

## NEXT 3 MOVES
1. Author a real multi-branch demo story (.scene) — 5-8 passages, several collective branches → ending.
2. Build the runnable demo — self-contained page-SDK (load wasm StoryWorld + <dregg-story collective> +
   the story in a tab, no extension) preferred; extension-loaded demo + OPEN-ME fallback.
3. Story netlayer fetch (content-addressed dregg://story/<addr> → verified StoryWorld) — the real load path.

## DONE-LOG
- done: authored demo/stories/the-commons.scene (the crowd IS the assembly; 3 branches → 2 endings on whether the record can be rewritten — the dregg thesis as a story). Compile+play verified via the demo driven-run.
- firing: DEMO PAGE lane (a491b1c26180a99cf) — self-contained page-SDK: real wasm StoryWorld over the-commons.scene, <dregg-story collective> in-page (no extension), auto-play the crowd + interactive, DRIVEN run + screenshot/transcript capture.
- firing: STORY NETLAYER lane (a9aecdbc92c80c7a1) — content-addressed dregg://story/<addr> → verified StoryWorld (mirror the doc/poll netlayer), hostile-story fail-closed.
- note: the deos_app wasm-clean refactor is COMMITTED (788b1b930); its stale build-monitor keeps echoing stage-greens (privacy-voting/collective-choice) — already verified + committed, ignore.
- done: STORY NETLAYER committed — dregg://story/<addr> content-addressed + verified before it plays (hostile story refused); also fixed a latent bug (StoryWorld ctor now threads the verified scene). test:netlayer 8/8.
- done: the-commons.scene VERIFIED BY DRIVING (wasm/tests/demo_scene_smoke.rs, 1/1) — compiles + plays a crowd branch. Demo foundation solid.
- waiting: demo-page lane (a491b1c26180a99cf) — the deliverable; I DRIVE it myself when it lands (the bar).

## STATUS (morning read)
- ✅ CORE DELIVERABLE DONE: the demo RUNS end-to-end, verified by DRIVING it myself (0c5776764). Real wasm
  StoryWorld, 3 crowd-voted branches, verify() true, captured screenshot + transcript. ember opens it as above.
- ✅ Story netlayer (content-addressed, hostile-refused) + scene-threading bug fix committed.
- ✅ the-commons.scene verified by driving (smoke test) + fixed spween syntax (quoted values).
- ⏸ ON DISK, BLOCKED (not mine): the wasm open_branch_poll IDEMPOTENCY fix (bindings_story.rs — a re-open at the
  same passage now preserves ballots instead of re-minting the engine; + a test). Correct + written, but I can't
  build-verify it: ANOTHER TERMINAL is mid-refactor of dregg-lean-ffi + dregg-sdk (uncommitted), which breaks the
  wasm build. Verify + commit the moment their refactor lands. The DEMO is unaffected (its adapter works around it).
- SEAM (named): the extension-less REAL-passkey voter in the demo page (the demo already runs extension-less with a
  demo voter; a real PasskeyCustody voter is the next enhancement, non-blocked — page-side TS).
- ✅ EXTENSION-LESS PASSKEY VOTER done + verified by DRIVING (committed): a WebAuthn passkey enrolls page-side,
  its biometric-gated ballot counts on the real CollectiveChoiceEngine under a stable id (900be4c3…), signed by a
  real hybrid ed25519+ML-DSA-65 key; second ballot refused (nullifier). Base auto-play unbroken. node demo/
  run-passkey.mjs. Note: enroll needs http://localhost:8787 (WebAuthn rejects a bare IP) — in OPEN-ME.
- GOAL SUBSTANTIALLY ACHIEVED: the demo RUNS + a stranger votes extension-less with a passkey, both verified by
  driving, both committed, discoverable (▶▶ banner). The dreggic collectivity web is real in a browser tab.
- ONLY PENDING: the wasm idempotency fix (on disk), blocked on another terminal's dregg-sdk refactor. Wakeup armed
  to re-check + verify+commit when unblocked. Does NOT affect the demo.


## ⚑⚑ THE TRUE AMBITION (ember, 07-10) — I built the STAGE and mistook it for the PLAY
`cv` + memory spelunk: the fiction engine is NOT pre-scripted CYOA + branch voting (that is the collective-
voting SUBSTRATE — a good start). The soul is **`attested-dm`: a provably-honest, UN-JAILBREAKABLE AI
dungeon-master.** A confined + attested LLM narrates an on-chain world; every narration is a receipted attested
turn on a WorldCell carrying a ZkOracleAttestation proving it is AUTHENTIC (a real model, not forged),
WELL-FORMED, and INJECTION-FREE. THE KILLER PROPERTY: a player's prompt-injection is reflected into the DM's
narration and caught by the injection-free leg → the turn CANNOT be attested → REFUSED, and the world advances
not at all (anti-ghost). The DM narrates freely but acts only within DmCaps (it cannot grant an unearned crown).
VERIFIED RUNNING (cargo test -p attested-dm, unblocked by the dregg-sdk churn): a_player_prompt_injection_is_
refused · injection_refusal_is_the_injection_free_leg_NOT_A_HEURISTIC (the verified dregg-dfa derivative matcher)
· an_injection_smuggled_into_a_forged_attestation_is_rejected_at_verify · a_swapped_narration_over_a_real_
attestation_is_rejected · a_tampered_session_is_rejected · a_fabricated_receipt_is_rejected · the_dm_cannot_
grant_an_unearned_item · a_benign_player_message_that_merely_mentions_rules_is_NOT_refused (non-vacuous).
Plus: `first-room` = the MUD room primitive (a room is a cell, an inhabitant is a cell, acting is a turn);
`branch-stitch-multiplayer` = players fork the world, diverge privately, stitch back through a settlement-sound
gate (clash refused, never last-writer-wins); `tussle`/`gallery` = sealed commit-reveal for simultaneous/hidden
choices (blind voting).
API: `narrate_turn(&self, world: &mut WorldCell, player: &PlayerMessage) -> Result<Receipt, DmError>`;
`DmError::{Injection, OverCap}`; `WorldCell::new(scene)`; `DmCaps::{narrator, pure_narrator}.authorize(effect)`.
attest_narration attests a GIVEN narration (no live model needed to demo the tooth); attest_narration_live
(MPC-TLS 2PC) is the CROWN, opt-in behind `tlsn-live`.

## NEXT THRUST: the un-jailbreakable AI dungeon-master, playable
Build the demo where **you play a living world narrated by an AI, and when you try to jailbreak it, it provably
refuses.** DM runs native (unblocked); browser is the play surface; the killer moment lands in a tab.
