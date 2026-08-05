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
recovery — the dogfooding case is exact. ⚠ Key custody is ember's decision
([[feedback-deputized-greenfield-dont-over-delegate]]); this lane may design it, not rotate it.

---

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

- 2026-08-05 — lane opened. Federation collapsed to one validator; node rebuilt from HEAD (189 commits
  of PoA work reached the chain for the first time; `/api/poa/holding/challenge` 404 → 415). POAG1
  re-emitted for federation `70b7fa4c…`; **content signing BLOCKED on W5** (wrong curator key on hbox).
  Depth numbers above measured. No game/system change landed yet — this file is the plan, not a claim.
