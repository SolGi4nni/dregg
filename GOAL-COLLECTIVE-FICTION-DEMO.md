# GOAL: collective-fiction web DEMO-READY by morning
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
