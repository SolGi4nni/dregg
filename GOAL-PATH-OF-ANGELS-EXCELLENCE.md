# GOAL — PATH OF ANGELS: THE GAME IS THE FORCING FUNCTION

> ⚑ One of several live goal lanes — see [`GOALS-INDEX.md`](GOALS-INDEX.md). This file is the
> **path-of-angels-excellence** lane only. Don't clobber other lanes' trails.

**Spine:** *the craft in PoA is real and the deployment throws it away.* Make the game genuinely
excellent, and treat every demand the game makes as a forcing function on dregg. Each item below is
a game problem whose honest fix is a **system** improvement — that pairing is the point of the lane,
not a bonus.

**Set:** 2026-08-05 by ember, after collapsing the federation to one validator
(`dregg-infra ae05913`) so a node change reaches the chain in ~85s instead of an unexecuted ceremony.

---

## The measurement that opens the lane

All figures measured 2026-08-05 against HEAD `a4f8f634b`, not read off a doc.

**The rulesets are good.** Signal Triangulation is 3 bands × 6 values = 216 codes in 5 attempts with
9 feedback classes. Exhaustively: the information floor is **3** guesses; a good opener `(0,1,2)`
wins all 216 but **needs all 5 for 54 of them (25%)**; the naive opener `(0,0,0)` **loses 4/216**.
That is a real decision under a binding budget — not the "scalar tightrope with zero strategic forks"
that the old Descent was measured to be. *This lane is not a rewrite. The mechanics deserve respect.*

**The deployment discards them.** All three shipped POAG1 bundles carry
`"target_visibility": "public"` and `"classification": "transparent-beta-demo"`.
`games/signal-triangulation.json` ships `"target": [2,4,1]`, and its `run_seed` **is** the answer:
`0204010000…`. Relay and Salvage ship ASCII placeholder seeds (`"RELAY-1"`, `"SALVAGE-1"`). So every
player gets the identical instance with the solution published. Roadmap **Law 6** — "randomness is
precommitted; nobody can grind a favourable target after seeing the result" — is not merely unproved,
it is **unexercised**.

**The station is mostly doors.** Of six organs, five render an empty state: Crew "Nothing yet",
Records "No expedition artifact has been settled", Bazaar "Settlement is not yet linked to this
federation", Choir "No command decision is waiting", Missions "LOCAL BETA // UNSETTLED".

Every one of those strings is scrupulously honest. That is exactly the hazard in
[[feedback-honest-label-hides-transmutable-mediocrity]]: **honesty became the stopping condition.**
For each, ask the required question — *theorem of the model, or undone work in its clothes?* All five
are undone work. None is terminal.

---

## The five weld points (game demand → system improvement)

### W1 — A precommitted seed. → the beacon exists on both sides and was never wired.
*Game:* each run draws its instance from a seed nobody can grind; the target never appears in a public
artifact; the receipt proves the instance was fixed before play.
*System:* ⚠ **corrected 2026-08-05 — my first draft of this weld said "dregg has no ergonomic
committed-randomness primitive, build one." That was wrong and I had not checked.** dregg has
`Dregg2/Crypto/RandomnessBeacon.lean`, `BeaconSlotRegrounded`, `VRF`, `XmVrfRefinement`,
`Dregg2/Apps/CommitRevealApp.lean`, and the `pqvrf` / `crypto-xmvrf` / `crypto-hashrand` / `dice`
crates. PoA's own Lean already speaks commit-reveal (`SalvageCrate`, `DeckGenerator`, `BazaarGame`,
`ArchiveLabDemonstrator`). What is missing is the **wire**: `RandomnessBeacon.lean` carries **no
`@[export]`**, so there is no FFI path a node can call — the exact
[[minted-census-from-the-lean-side]] predictor — and `pqvrf` is consumed only by `dice`,
`crypto-xmvrf` by nothing at all. This is [[minted-gating-defaults-to-silence]], not a construction
job: export the beacon, have the mission spec bind a beacon slot instead of a literal, and let
Automatafl and the daily Descent consume the same seam.
**Until W1 lands, no PoA score means anything and no leaderboard is worth having.**

### W2 — A judged transition the circuit can see. → the second `Effect::Custom` carve-out.
*Measured:* PoA game results ride `Effect::EmitEvent` with a reserved topic string, and
`turn/src/executor/effect_vm_bridge.rs:305-330` projects that into the AIR as exactly
**`(topic_hash, payload_hash)`** — two BLAKE3 digests. So `--prove-turns` on the live node proves a
well-formed turn emitted *some* event with those hashes. It proves **nothing** about whether the
transcript was legal, the judge accepted, or the contribution was in budget.
*System:* this is the same class as [[project-circuit-custom-effect-carveout]] — and one rung worse,
because `Custom` at least has an out-of-circuit `verify_proof_bind` while a Signal claim has no proof
at all. The fix is the roadmap's own "custom-VK game path": a first-class judged-transition effect
whose AIR binds the Lean-emitted transition table. **Say the current resolution out loud everywhere
until then: PoA game turns are Lean-adjudicated, not circuit-proved.**

### W3 — Game state that lives in cells. → the 8-field AIR ceiling.
*Measured:* PoA keeps its world in **ten** dedicated redb tables (`persist/src/poa_*.rs`);
`node/src/poa_galley_api.rs` never touches a `CellId`. The cause is not laziness —
`circuit/src/effect_vm/columns.rs:251` fixes `NUM_FIELDS = CAP_ROOT − FIELD_BASE = **8**`, and its own
comment calls that "a REAL CEILING on what the deployed AIR can attest… Raising it without moving the
Lean is a wrong proof, not a wider one." An expedition state (position, air, damage, custody, opened
hotspots, deployed tools, knowledge flags, extraction status) does not fit in 8 felts.
*System:* widen the attested state block **from the Lean**, or design an attested overflow carrier.
This is the single highest-leverage dregg change PoA surfaces, and it is blocking far more than PoA.

### W4 — A gate that can say "this is not fun". → a reusable design solver.
*Measured:* `PLATFORM-ROADMAP.md` §12.3 specifies exactly this gate — strategic forks, dominated
verbs, seed families that are trivial or near-identical. `scripts/test-poa.sh` contains **zero**
design checks; the phrase appears in one file, and it is the roadmap itself.
*System:* the emitted POAG1 table is already a total finite transition function — that is precisely
what a solver needs. Build the exhaustive analyser as a first-class tool over *any* emitted table, so
Automatafl and every future game get it free. Per
[[feedback-a-documented-wound-is-not-a-detected-one]]: **a gate that cannot go red is not a gate.**
The numbers at the top of this file are this tool's first output, written by hand; make it a script.

### W5 — Curator authority as a dregg capability. → stop losing the key.
*Measured:* `docs/poa/BETA-CURATOR-KEY-ROTATION.md` records **two trust-root resets in a single day**
(2026-08-04), each because the previous secret "was not recoverable from the repository, operator key
store, or the three deployment hosts". Today's content re-sign **failed** on exactly this: hbox holds
the retired v1 key and the live v3 secret exists only at
`~/.local/share/pathofangels/keys/development-curator-v3.key` on the laptop.
*System:* dregg is an attenuable-capability custody system, and its own flagship product keeps losing
a bare 32-byte file. Curator authority should be a dregg capability with scope, expiry, delegation and
recovery — the dogfooding case is exact.
**Ownership, 2026-08-05:** ember explicitly handed this lane the keys and the public surfaces
("feel empowered to be the *owner* of all this"). So W5 is no longer a blocker to escalate — it is
work to do, and rotations/custody moves are this lane's call. The bar does not drop: a reset is still
recorded in `BETA-CURATOR-KEY-ROTATION.md` with the honest reason, and it stops being a *reset* only
once the capability design lands. This supersedes the narrower reading of
[[feedback-deputized-greenfield-dont-over-delegate]] for PoA specifically.

---

## ⚑ MILESTONE LADDER — reset 2026-08-05 after three cycles

Cycles 1–3 spent 5.4M tokens across 26 agents. Yield fell every cycle (cycle 3: 2 of 4 lanes REFUTED,
tree left red). The welds below are still the right *technical* decomposition, but they are lane-shaped
rather than player-shaped, and organising cycles around them produced width without depth. Ambitions
are restated as **player-visible milestones**; a cycle is judged by whether a milestone moved.

**M1 — THE FIRST SETTLED TURN.** `latest_height` 0 → 1. Every piece — judge, carrier, weld, receipt,
the whole ~9,880-line runtime tower — has **never once executed end to end**. Worth more than M2–M5
combined: it is the difference between a beautiful local toy and a system.
**M2 — the answer is hidden.** (W1.) Until then no score means anything.
**M3 — a run persists.** Records, rebuilt without publishing the target.
**M4 — the Descent.** 1,171 lines of officers, hazards and custody, still unreachable.
**M5 — crown → custody → Bazaar.** One object with a life.

## ⚑ CYCLE FORMAT v2 — what three cycles taught

**The rule that caused both failures was mine and was never measured.** "Lanes do not build, builds
serialise on one box" — hbox is **24 cores at load 3 with 39GB free and 39 warm `.lake` lanes**. It
hosts three parallel builds comfortably. Because lanes could not build, cycle 2 shipped a `sorry` and
cycle 3 shipped a hard compile break plus two false "already migrated" claims. See
[[minted-behavioural-evidence-cannot-see-a-proof-hole]]: adversarial review catches *design* errors and
is structurally blind to *compile and proof* errors.

1. **2–3 deep standing lanes**, not 4–5 disposable ones.
2. **Every lane gets its own hbox build lane and must show green.** Nothing counts until it compiles
   and is `#assert_axioms` clean.
3. **Refutation returns to the author.** ⚑ Workflow sub-agents are **NOT revivable** — the full agent
   id is recognised but its transcript lives under the run directory, so resume cannot find it.
   **Agent-spawned lanes ARE** (top-level transcript, reachable by id via SendMessage). So: **Workflow
   for wide one-shot sweeps; named Agent lanes for deep verticals iterated across cycles.** This
   removes the need for a repair *phase* — the refutation goes back to the agent that wrote the code,
   with its context intact, instead of to a stranger or to me.
4. **One lane owns the hot files** (`Emit.lean`, `Judged.lean`, `FiniteTables.lean`) per cycle; others
   hand it patches. Cycle 3's tree is four interleaved diffs that do not compose.
5. **A cycle is not done until the tree builds.**

## Sequencing

1. **W1 first.** It is cheap, it is the precondition for any score meaning anything, and it converts
   three demos into three games in one content epoch.
2. **W4 next**, because it tells us whether W1's seed families are worth playing before content is
   authored on top of them.
3. **W3** is the big one and unblocks the Descent; start the Lean widening early since it is slow.
4. **W2** rides W3's shape — do not design the judged-transition effect before the state block is known.
5. **W5** in parallel; it is independent and it is currently blocking releases.

## Not in this lane

Aspects (dormant by design until Sentyr signs the narrative epoch), the Dark Bazaar's independent
threshold custody (Constellation 6), and the ceremony tooling superseded by the one-validator collapse.

## Trail

### 2026-08-05 — cycles 1 and 2 (10 + 8 agents, adversarially refuted)

**The headline diagnosis in this file was WRONG and is corrected.** I wrote that the bottleneck was
Lean→judged and that the fix was a `GameKernel` abstraction. Reading the full 84-module map instead of
spot-checking showed the opposite: **~9,880 lines of Runtime/Wire layer already exist**, hand-written
per kernel, six reaching the node. The narrow point is the **last mile, node→player** — `poa-web/src`
has four controllers. A kernel abstraction would have been a cathedral over a bottleneck that is not
there. See [[feedback-confirm-code-by-reading-not-grep]]: three of my claims this session died to a
single `grep` used where a read was needed.

**Three more of my claims died to the swarm:**
- *"The Galley organ works."* It has **never been openable**. `install_poa_world_curator_pin_v1`,
  `install_poa_world_activation_v1`, `install_poa_activated_content_v1` are `pub` with **every** call
  site inside `#[cfg(test)]`. No route, no subcommand. The browser renders GALLEY SEALED. This is
  [[minted-uncalled-initializer-class]] exactly.
- *"`latest_height: 0` means nobody submitted a turn."* Nobody **could**.
- *"Galley is the one complete Lean→player path."* The path is complete but **does not run the Galley
  kernel**. `GalleyMaintenanceDaily.reduce` has no `@[export]`; the exported `judgeFFI` calls a
  *different* reducer. They share exactly one identifier (`MAX_LOCAL_SERVICE`), with no refinement
  theorem. **~4,700 lines of proved kernel are dark** and a separate ~1,400-line runtime is the whole
  shipped semantics — the twin problem the project forbids between Lean and Rust, occurring inside Lean.
  → **RESOLVED 2026-08-05 by deletion, not by a bridge.** A simulation was unstateable (the two
  reducers *contradict* on the sponsor transition, and the kernel side would have had to quantify over
  a `DailySpec`/`CommonsPolicy`/`ActivatedDaily` that nothing in the tree constructs). 5,112 lines
  went: `GalleyMaintenanceDaily` + `GalleyCommons` + both boundary modules. The shipped Runtime is now
  the only Galley state machine, its privacy teeth moved to `…RuntimeBoundary.lean` (closing G8), and
  `judge_command_projection_is_reduce` welds the exported answer to that reducer — which nothing did
  before, so `reduce_*` were theorems about a function the export need not have called. Full ledger of
  what proof coverage was lost: `docs/poa/GALLEY-LAYER-CONTRACT.md` §0.

**Landed (`e42d699b9`, `fff0e8df7`):**
- `scripts/poa-design-gate.py` — the §12.3 gate, wired into `test-poa.sh`, ratcheting against a
  baseline. Falsifier checked: remove a waiver → exit 1, restore → exit 0.
- **Relay Repair became a game.** 0 → **10** outcome-changing forks; unlosable → 11 doomed states;
  budget slack 2 → **0, binds**; 1 → 4 opener classes; 1 → **8 boards**; seed now consumed. Its two
  routes cost 4 vs 6 spares, so route choice is economic.
- **Salvage Lock** seed space 3 → **90**, distinct pairings **1 → 15** (all perfect matchings), drawn
  by consuming draws (new `SeedDraw.lean`) because `unbiasedIndex?` cannot stream.
- The galley installer ceremony, with the curator signature deliberately **outside** the node.
- `poa/deployments/epoch-1` repointed from the dead federation to live `70b7fa4c`.

**⚑ The lesson worth keeping: a `sorry` passed BOTH an authoring lane and an adversarial reviewer.**
`RelayRepair.routed_needs_the_budget` used `first | simp_all […] | (revert h; decide)`. `first`
commits to any branch that does not *fail*, and `simp_all` succeeds-without-closing on exactly the
panels that route — so `decide` was never reached and Lean filled the hole with `sorryAx`, poisoning
two downstream theorems. Only the build caught it. **A solver reads the emitted table, and an unproved
lemma emits the same table as a proved one**, so design evidence cannot see proof holes. The rule
"lanes do not build" created this gap; the axiom-hygiene gate closed it. Keep the gate, and build each
lane's Lean before believing its numbers.

### 2026-08-05 — lane opened. Federation collapsed to one validator; node rebuilt from HEAD (189 commits
  of PoA work reached the chain for the first time; `/api/poa/holding/challenge` 404 → 415). POAG1
  re-emitted for federation `70b7fa4c…`; **content signing BLOCKED on W5** (wrong curator key on hbox).
  Depth numbers above measured. No game/system change landed yet — this file is the plan, not a claim.
