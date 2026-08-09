# The station page's disclaimer ledger — 2026-08-09

The Path of Angels station page (`poa-web/index.html`, tiles built by
`poa-web/src/platform-terminal.js`) is a wall of honest caveats under the header
*"Each instrument keeps its own evidence grade."* Honest labelling is a stopping
condition, not a win. This ledger sorts every badge on that page into exactly
one of two kinds and justifies each verdict **at source**, not from the badge's
own wording — the badge is the thing under suspicion.

- **TERMINAL** — a true property of the design that should never move. Removing
  it would require making the system *worse*.
- **TRANSMUTABLE** — undone work wearing a badge. Nothing about the design
  forbids the thing; nobody built it.

A third column turned out to be necessary and is the most valuable part of this
document:

- **WRONG** — the badge misdescribes reality. Either it claims a gap that has
  already closed, or it credits evidence that does not exist.

---

## ⚠ First: the wall I was given is not the wall that ships

The brief's table came from a screenshot that predates `019fb00a1`
("the machinery talked like a build log — same claims, the ship's register").
Every badge string was rewritten in that commit. Before sorting anything, here
is the diff between the wall as described and the wall in `HEAD`:

| tile | brief's badge | badge actually in `HEAD` |
|---|---|---|
| Field drills | `AUTHORITY CHECK` | **tri-state**: `SIGNED BY THE CURATOR` / `CHECKING THE MANIFEST` / `RULES REFUSED` |
| Crew expedition | `PINNED PROVENANCE` | `PINNED PROVENANCE` (new detail text) |
| Evidence intake | `PINNED PROVENANCE` | `PINNED PROVENANCE` (new detail text) |
| Flight Recorder | `LINKED REPLAY` | `LINKED REPLAY` (new detail text) |
| Expedition roster | `NO PROFILE RECEIPT` | `NO PROFILE RECEIPT` (new detail text) |
| Dark Bazaar | `NO SETTLEMENT` | `NO SETTLEMENT` (new detail text) |
| The Galley | `VERSIONED NODE` | `VERSIONED NODE` (new detail text) |

**`AUTHORITY CHECK` no longer exists.** It was the *pending* label — a loading
state, not a disclaimer — and it is now `CHECKING THE MANIFEST`. A wall entry
that reads "the content epoch is still being authenticated" is describing a
spinner. It is not sortable and it is not owed a closure; the sortable badge on
that tile is the **ready** one, which is a positive grade with a scoping clause.

The brief's table also omits one badge entirely: the evidence register's
`NO RUN RECEIPT` row (`platform-terminal.js`, `register`), which is the badge
this pass found the most wrong with.

---

## The sort

**8 badges. 4 TERMINAL · 2 TRANSMUTABLE · 3 WRONG (all now fixed).** The counts
overlap: a badge can be a true-but-transmutable claim AND misdescribe what is
there, and §5 is both.

| # | badge | verdict |
|---|---|---|
| 1 | Field drills — `SIGNED BY THE CURATOR` (the grade) | **TERMINAL** |
| 1b | Field drills — *"A run stays in this browser and settles nothing"* (the copy) | **WRONG** → fixed |
| 2 | Crew expedition — `PINNED PROVENANCE` | **TERMINAL** (grade) + **TRANSMUTABLE** rider |
| 3 | Evidence intake — `PINNED PROVENANCE` / curator-only promotion | **TERMINAL** |
| 4 | Flight Recorder — `LINKED REPLAY` "not a finality proof" | **TERMINAL** |
| 4b | Flight Recorder — *"the head the node reported"* | **WRONG** → fixed |
| 5 | Expedition roster — `NO PROFILE RECEIPT` | **TRANSMUTABLE** + **WRONG** (understated) → fixed |
| 6 | Dark Bazaar — `NO SETTLEMENT` | **TRANSMUTABLE** (large) |
| 7 | The Galley — `VERSIONED NODE` | **TERMINAL** |
| 8 | Register — `NO RUN RECEIPT` | **TERMINAL**, but it was **hiding a second grade** → fixed |

---

## 1 · Field drills — `SIGNED BY THE CURATOR`

**Grade text:** *"The curator's signature on manifest revision 1.10 checks out.
That vouches for the rules, not for any run you play."*

### Verdict: TERMINAL — and the check behind it is real

`poa-web/src/content-epoch.js:authenticateContentEpoch` is an actual Ed25519
verification: it hashes the manifest bytes, requires the digest to equal the one
the signature names, requires the signing key to equal an **external** pin
fetched from `/poa-curator-key.json` (deliberately outside the POAG1 bundle,
`poa-web/src/trust-config.js`), requires `content_epoch`/`counter` to equal the
deployment pins (rollback refusal), and only then calls
`crypto.subtle.verify({name:"Ed25519"}, …)` over a domain-separated preimage.
Deployed values agree: `poa/artifacts/poag1/manifest.sig.json` and
`poa-web/public/artifacts/poag1/manifest.sig.json` both carry epoch 1 / counter
10, matching `POA_EXPECTED_CONTENT_EPOCH = 1` and
`POA_EXPECTED_CURATOR_COUNTER = 10`.

**Why the scoping clause can never move:** a signature over *content* and a
receipt for a *player's run* are signatures by different parties over different
objects. The curator signs which rules were offered; only the player's key and
the node's judgement can say anything about a run. No amount of work makes one
into the other. Keep it forever.

> ⚑ Live hazard, not a badge: a sibling lane is signing **counter 11**. The
> instant `manifest.sig.json` carries 11 while `trust-config.js` pins 10, the
> whole rack refuses with `counter-rollback`. That is the pin working correctly;
> it just needs both to move together.

### 1b · The tile copy was WRONG — and it hid the best thing on the page

The Field drills tile said, unconditionally:

> `${n} drills are open, on rules the curator signed.` **`A run stays in this browser and settles nothing.`**

The second half is true. **The first half is false.** A *judged* run does not
stay in this browser. `poa-web/src/judged-session.js` opens a session on the
node at `POST /api/poa/signal/{authority}/session/open`, spends bursts at
`…/session/guess`, and reads the transcript back at `…/session/{player}` — and
the node, not the page, classifies every guess with the Lean feedback oracle
against a slot commitment the curator signed *before the run opened*. The module
is explicit that it will not score a guess locally: *"a second implementation of
the rule is a second rule"*.

Those three routes are **public** — `node/src/api.rs:2483`, inside
`public_routes`, pinned by `the_unauthenticated_route_surface_is_exactly_this`
(`node/src/api.rs:11130`). The page reaches them through the same-origin
`/node/*` tunnel. Per `judged-session.js`'s own measured record, five walls that
used to block judged play have fallen (`FALLEN_WALLS`, most recently
`claim-cell-underivable` on **2026-08-09**), and `canPlay` is now routinely
`true` for an invited player with a current Cipherclerk.

So the page carried a caveat that erased its own strongest instrument. A visitor
read "it all stays in your browser" and had no reason to look at the judged
panel sitting directly above the tile — a panel that describes a node-scored
deduction game.

**Fixed** (`poa-web/src/platform-terminal.js`). The copy now states what the two
modes *are*, unconditionally and without asserting reachability:

> *"…A practice run stays in this browser and settles nothing; a judged run
> leaves it, and the node scores it against a slot the curator committed to in
> advance."*

The true half — **settles nothing** — survives verbatim, because it is still
true (see §8). Whether judged play is reachable *right now* is measured, and
lives in the judged panel and the new register row rather than being asserted in
static copy.

---

## 2 · Crew expedition — `PINNED PROVENANCE`

**Grade text:** *"The bytes on disk match the digests this build was compiled
against. The full table is checked inside the lab, not out here."*

### Verdict: the grade is TERMINAL. Its rider is TRANSMUTABLE.

Both halves of the grade are true at source. The station tile fetches only the
small manifest (`platform-terminal.js:loadExpeditionProvenance`) and
`tests/platform-terminal.test.mjs` pins that the multi-megabyte fixtures are
*not* fetched. The lab then hashes the whole table:
`poa-web/labs/expedition-lab-runtime.js:632-635` computes `sha256Text` over the
entire fixture and refuses unless it equals `BUILTIN_FIXTURE_SHA256`.

Byte-pinning is terminal for a static web build: a browser cannot re-run Lean,
so "these are the bytes Lean emitted at this commit" is the strongest statement
this surface can make about a table. The laziness half ("not out here") is
technically transmutable and **should not be transmuted** — eagerly fetching a
multi-megabyte table on the overview to retire half a sentence is a worse page.

**The transmutable rider** is the tile copy's *"it settles nothing and promotes
nothing into the record."* That is undone work, and the repo says so itself:
`poa-web/README.md`'s DrEX pressure-harness table lists Expedition as needing
"Lean-authored joint state machine, participant signatures, exact contribution
and custody output." The Lean kernel exists (`CrewFieldMission*`), has exactly
one export (`dregg_poa_crew_field_step`), and has **no safe Rust wrapper caller,
no node route, and no client**. Priced in §"What I did not take", item C.

---

## 3 · Evidence intake — `PINNED PROVENANCE` / promotion is curator-only

**Grade text:** *"The archive's manifest is pinned byte for byte. That is all it
does: it settles nothing and promotes nothing."*
**Tile copy:** *"…and only the curator can promote what comes out of it."*

### Verdict: TERMINAL

Curator-only promotion is not a placeholder — it is an implemented authority
edge. `poa-curator/` signs *exact* promote/supersede decisions over all four
fields of the Lean `ArtifactRef` projection, and its README states that
promotion additionally requires a live `CanonAdmissionOracle` over the full
action, that there are **no allow-all adapters**, and that "a well-shaped signed
request is not a canon transition by itself."

This can never move, for the reason in §1: canon is what a named authority
vouched for. A surface that could promote its own output would be a surface
whose canon means nothing. The web curator console is correctly labelled
*"Read-only surface // curator tool not connected"* (`index.html`) — a browser
page must never hold the curator key, and that is also terminal.

---

## 4 · Flight Recorder — `LINKED REPLAY`

**Grade text (was):** *"Every link on screen agrees with the next one, and with
the head the node reported. That is not proof the network settled any of it."*

### Verdict on "this is not a finality proof": TERMINAL — and structurally enforced

This is the badge the brief guessed correctly, and it is more terminal than the
wording suggests. Digest continuity is a property of a chain of digests;
finality is a property of a quorum. No amount of link-checking crosses that gap.

What makes it *structurally* terminal is that the runtime refuses to let a node
say otherwise. `poa-web/labs/flight-recorder-runtime.js:74` and `:95`:

```js
refuse(value.consensus_finality === VIEW_FINALITY, "recorder-finality",
       "status overstates or changes its finality claim");
```

where `VIEW_FINALITY = "not_asserted_by_this_view"`. A node that claimed
finality would be **refused**, not displayed. The disclaimer is a load-bearing
check, not a note. Keep it forever, and do not "upgrade" it — a future real
finality source is a *different* grade, added beside this one, never a
relaxation of this refusal.

### 4b · But the grade was WRONG about where its evidence came from

The shipped configuration is a **demo fixture**:

```json
// poa-web/labs/flight-recorder.config.json
{ "format": "POA-FLIGHT-RECORDER-CONFIG-1", "mode": "demo",
  "api_base_url": null, "authority_id": null, "max_transitions": 64 }
```

`labs/flight-recorder-demo.fixture.json` is three transitions labelled *"Crown
Relay rehearsal"* whose digests are `aaaa…`, `1111…`, `3333…`. **No node ever
reported that head.** The grade nonetheless said "*and with the head the node
reported*" — identically in both modes, because the grade was a constant.

This is the identity-carrier class: a conclusion that credits an organ that
never spoke. Notably, the *today board* on the same page already gets this right
(`src/today-board.js:319`: "a `demo-fixture` rehearsal, so its 3 transitions are
a demonstration and not the ship"). One instrument told the truth and the badge
beside it did not.

**Fixed** (`poa-web/src/platform-terminal.js:recorderGrade`). A pinned rehearsal
and a live redacted view are different evidence, so they now get different
labels:

- live source → `LINKED REPLAY`, *"…and with the head the **authority's node**
  reported. That is not proof the network settled any of it."*
- demo source → **`LINKED REHEARSAL`**, *"Every link agrees with the next one
  inside a byte-pinned rehearsal fixture (Crown Relay rehearsal). **No node
  reported this head and no ship made these transitions**, so it is not proof
  the network settled any of it either."*

The finality clause survives in both. Pointing the recorder at the live
authority is a separate, larger job — priced as item A below, **not taken**.

---

## 5 · Expedition roster — `NO PROFILE RECEIPT`

**Grade text (was):** *"A crew choice lives in one local transcript and nowhere
else."*

### Verdict: TRANSMUTABLE — *and* it was understating, which is the third wrongness

**The "no officer profile / no crew receipt" claim is TRANSMUTABLE and correct.**
There is no design property here; nobody built an officer.

- No route: the node's complete PoA surface is 19 routes
  (`node/src/api.rs`, public set pinned at `:11130`). None is a profile, roster,
  officer, or inventory route.
- `metatheory/Dregg2/Games/PathOfAngels/OfficerLogbook.lean` (796 lines) defines
  a rebuildable career record and a `CrewReceipt` — with **no `@[export]`**, no
  Rust reference, and no client. `grep -rn OfficerLogbook` over every `.rs`,
  `.js` and `.ts` returns zero.
- The crew lane is large and *built in Lean only*: `CrewFieldMission.lean`,
  `CrewFieldMissionRuntime.lean`, `CrewRelayExpedition.lean`,
  `CrewExpeditionAuthority.lean`. There is no `poa_crew_field_ffi.rs`, unlike its
  four sibling FFI arms (`poa_galley_ffi.rs`, `poa_records_ffi.rs`,
  `poa_crate_open_ffi.rs`, `poa_station_daily_ffi.rs`). The single export
  `dregg_poa_crew_field_step` has **no Rust caller**.
- The repo names it as future work in its own words (`poa-web/README.md`):
  Officer needs "wallet-bound but privacy-conscious profile capability and
  versioned state transition."

### But the badge misled by omission, and that is the same error as the other two

The grade said a crew choice "lives in one local transcript **and nowhere
else**", and the Crew muster card renders three hardcoded facts — *Officer
profile: unbound · Asset custody: none · Persistent roster: not exposed*. A
player reads that as **"this terminal remembers nothing about me."** That is
false. The node keeps durable, player-key-keyed state in at least three places
on this very terminal:

- **The Galley** inserts your actor key into `publicPlayers` permanently and
  then **refuses a second shift from that key**:
  `GalleyMaintenanceDailyRuntime.lean:712-717` —
  `decide (payload.actor ∈ state.publicPlayers) then none`, and
  `publicPlayers := insertDigest payload.actor state.publicPlayers`. The browser
  reads it back at `poa-web/src/galley-runtime.js:401`.
- **The judged Signal store** is a redb table keyed
  `authority_id || slot_be64 || player_key`
  (`persist/src/poa_signal_session.rs:196-201`) and survives restarts by design —
  its own docblock says the spent-round count "is a fact the node must remember
  across restarts, and remember for the RIGHT player."
- **Canon** carries a per-player counter (`PlayerCounters.lean`,
  `NetworkJudgeWire.lean:202-208`), and `/api/poa/records/{authority}` publishes
  each finalized run's `origin_key` — player key plus counter.

So the wrongness is directional, and it is the **same direction as §1b and
§4b**: the page understated itself. Three badges, three understatements.

**Fixed** (`poa-web/src/platform-terminal.js`). The true claim stays word for
word and gains the fact it was eliding:

> *"A crew choice lives in one local transcript and nowhere else, and no officer
> profile or crew receipt exists on any surface. What the node does keep is
> narrower and real: your player key, wherever you have acted — a Galley shift it
> will not let you take twice, and a judged slot's spent bursts."*

The Crew muster card gains a fourth fact row, **What the node keeps** — *"your
player key where you have acted"* — so the three "nothing" rows can no longer be
read as a general absence.

Building the actual officer profile is priced as item B. **Not taken** — see the
warning attached to it, because this is the badge most likely to be closed
badly.

---

## 6 · Dark Bazaar — `NO SETTLEMENT`

**Grade text:** *"Nothing on this build owns salvage, and nothing on it settles a
trade."*

### Verdict: TRANSMUTABLE — and *currently true at every layer*, including in Lean

This one deserves credit: it is accurate on the server too, not just in the
browser, and it is accurate for a stronger reason than "nobody wired it up."

- **"Salvage" is not a resource today.** `poa/artifacts/poag1/games/salvage-lock.json`
  carries `"competitive_rewards": false, "economic_rewards": false`. The Salvage
  *Crate* persists a 40-byte replay-guard row (`player[32] || period_be[8]`,
  `node/src/poa_crate_api.rs:139-143`) — no item, no quantity, no balance.
- **Lean forbids tradeable loot structurally.**
  `metatheory/Dregg2/Games/PathOfAngels/SalvageCrate.lean:90-94` requires
  `entry.custody = .nonEconomic` for a loot entry to be *shape-valid at all*,
  with a pinned falsifier at `:857-866`
  (`check_forged_transferable_table_refuses`).
- **The Galley cannot mint.** `GalleyMaintenanceDailyRuntime.lean:735-739`
  (`reduce_preserves_advantage_anchors`) proves `lootRoot` is invariant under
  every accepted reduction, and `:1148-1151`
  (`receiptOf_has_no_advantage_delta`) proves `lootDelta = 0`. The deployed
  artifact agrees: `poa/artifacts/galley/epoch-1/policy.json` has
  `"dregg_mint": 0` and `"loot_root": "0000…0000"`.
- **The node has never heard of DrEX.** `grep -rni drex node/src/` — zero hits.
  DrEX's own settle path trades computrons between a pinned trader roster and
  names PoA as the node it does *not* settle against
  (`drex-web/serve.mjs:261`).

Yet it is transmutable, and the shape of the fix already exists in Lean:
`metatheory/Dregg2/Games/PathOfAngels/OrdinarySalvageExchange.lean` is exactly
the missing organ (`MintAuthorization`, `MarketUnit`, `CustodyAuthorization`,
`ExchangeReceipt`, `DurableDeployment`), with a boundary theorem that story
relics can never enter the market
(`OrdinarySalvageExchangeBoundary.lean:63-70`). It has **zero** Rust/TS/JS
references. `docs/reference/PREALPHA-FINAL-CUT-2026-08-07.md:129` already
classifies it: *"kernels + boundary statements | no export, no route, no
client."*

Priced as item D. **Not taken** — it is the largest item on this page.

---

## 7 · The Galley — `VERSIONED NODE`

**Grade text:** *"The Galley stays shut unless its node supplies every part — the
actions, the view, the events, the receipt, the replay. A missing piece closes
the hatch; it is never filled in here."*

### Verdict: TERMINAL

This is a fail-closed check, and the project's standing rule is that anything
weakening a check deserves a pause. `poa-web/src/galley-runtime.js` enforces
exact key sets on every served document (`CURRENT_KEYS`, `SESSION_KEYS`,
`STATUS_KEYS`, `PROJECTION_KEYS`, `EVENT_PAYLOAD_KEYS`) — an *unknown* field is
refused, not ignored, in both directions. The browser holds no Galley reducer;
the node owns projection, actions, unsigned turn bytes, events and receipts.

"Fails closed unless the frozen V1 API supplies everything" is the correct
permanent posture for a surface that renders someone else's authority. It should
never move.

> One genuinely transmutable thing hides nearby and is *not* this badge: the
> README says the Galley's "projection remains deliberately opaque until the
> authoritative presentation schema is frozen." Freezing that schema is undone
> work. It is a different sentence in a different place, and it does not weaken
> the `VERSIONED NODE` refusal.

---

## 8 · Evidence register — `NO RUN RECEIPT`

**Grade text (was):** row *"Browser run"* — *"A run written down in this browser
grants nothing: no score, no salvage, no rank, and no change to the ship."*

### Verdict: TERMINAL as a statement — but the row was doing a second job badly

The claim itself can never move, and for the same reason a Rust case-test is not
translation validation: **a page cannot be evidence about itself.** A transcript
a browser authored, about a hidden instance the same browser drew from
`HiddenInstance.practiceRunSeed`, is a self-report. It could not grant anything
even if someone wanted it to.

**But the register had only one run row, and there are two kinds of run.** A
judged run is a different object with strictly stronger evidence: the node
re-derives a curator-committed instance and scores it with the Lean oracle
(§1b). Folding both into "Browser run" meant the register — the page's own
answer to *"what does each green light actually mean"* — hid its most
interesting light behind its weakest caveat.

**Fixed** (`poa-web/src/platform-terminal.js`). The register now carries two
rows:

- **Practice run** — `NO RUN RECEIPT`, with the reason made explicit and
  permanent: *"…That can never change — a page cannot be evidence about
  itself."*
- **Judged run** — a new grade, and **every branch of it is measured**, never
  asserted:

| measured state | grade | tone |
|---|---|---|
| nothing asked yet (`judged === null`) | `STILL READING` | dim |
| node served a session matching the verified commitment | `NODE-JUDGED, UNSETTLED` | amber |
| `custody.canPlay` (signer detected **and** route answered) | `JUDGED RUN REACHABLE` | amber |
| otherwise | `NO JUDGED RUN` + the blocker's own code | dim |

Two disciplines from `judged-session.js` are carried over deliberately. First,
*"we have not looked"* renders differently from *"there is nothing"* — a
not-yet-measured row says `STILL READING`, never an absence. Second, every
non-trivial branch **names the standing wall by its code**
(`settle-node-curtained`), so a player reads why rather than a shrug.

The heading copy was updated to match (`index.html`): "Five different green
lights: the curator's signature, where a table came from, whether a replay links
up, what a practice run grants, and what the node did with a judged one. None of
them upgrades another, and the last two are not the same light."

> ⚑ And the "settles nothing" half of every one of these stays true. The
> remaining wall is measured and is **not** on this side of the wire:
> `CUSTODY_BLOCKERS[0] = settle-node-curtained`. Measured 2026-08-09: every path
> on `node.pathofangels.network` answers `HTTP 401` with
> `www-authenticate: Basic realm="restricted"` from Caddy — the private-beta
> curtain in `dregg-infra`'s `edge/anchor/Caddyfile`, at site-block top level
> with no path matcher. The page reaches the session routes through the
> same-origin `/node/*` tunnel an invited player already carries; the extension
> talks to the direct host and holds no invitation credential, deliberately.
> **So: play judged — yes. Settle — no.** Fixing that is a deployment change
> (route the claim through the same tunnel, or carve out the public signal
> routes), not a page change.

---

# What I closed, and what a player now sees

Five changes, all in `poa-web`. Every one makes the page say **more** about the
gap, never less. No caveat was deleted while its gap stood.

1. **`src/platform-terminal.js` — the daily copy.** A player who previously read
   "a run stays in this browser" now reads that a practice run does and a judged
   run does not, and that the node scores the judged one against a
   pre-committed slot. The judged panel above the tile stops looking like
   decoration.
2. **`src/platform-terminal.js` — `recorderGrade`.** The Flight Recorder tile no
   longer claims a node reported its head when a rehearsal fixture supplied it.
   In the shipped demo configuration the badge now reads `LINKED REHEARSAL` and
   says outright that no node reported this head and no ship made these
   transitions. `LINKED REPLAY` is reserved for a live source.
3. **`src/platform-terminal.js` + `src/app.js` + `index.html` — the judged
   register row.** The evidence register gained a sixth row that grades judged
   play off measured state, threaded from `state.judgedCustody` /
   `state.judgedSession` through `buildPlatformModel({… judged})` and refreshed
   from `renderJudged()` so panel and register can never disagree. A player can
   now tell, on the front page, whether a judged run is reachable and exactly
   which named wall stops it from settling.
4. **`src/platform-terminal.js` — the crew grade and a fourth crew fact.** The
   `NO PROFILE RECEIPT` claim is unchanged and still true; beside it the page now
   says what the node *does* keep — your player key where you have acted, a
   Galley shift it will not let you take twice, a judged slot's spent bursts. The
   Crew muster card's three "nothing" rows gain a **What the node keeps** row so
   they cannot be read as a general absence.
5. **`src/judged-session.js` — a docblock that asserted a fallen wall.** Not a
   badge, but the same class, in the file every judged claim on this page rests
   on. Its header said `claim-cell-underivable` "stands" and that
   `wasm.cell_id_for_pubkey` "has never existed in any build of the wasm", while
   `FALLEN_WALLS` in the same file records that wall as fallen on **2026-08-09**
   and the shipped `extension/dregg_wasm.js:2584` exports the function. It also
   sent readers to `CUSTODY_BLOCKERS`, which no longer contains it. Corrected to
   name the wall that actually stands (`settle-node-curtained`), with the
   retired claim kept visible rather than quietly overwritten — this is the
   file's own rule: *a wall a docblock asserts is one that rots.*

Tests: `tests/platform-terminal.test.mjs` gains three cases and two assertions
that fail if any of these regress — including `assert.doesNotMatch(daily.copy,
/A run stays in this browser/)` and `assert.doesNotMatch(recorder.grade.detail,
/the head the node reported/)`, which pin the exact retired wrongness rather
than the replacement.

> ⚑ Suite state when this landed: `npm test` in `poa-web` is 325/345 with **20
> pre-existing failures in a sibling lane's in-flight POAG1 re-emit**
> (`poa/artifacts/poag1/{catalog,manifest,manifest.sig,games/*}.json` are
> modified in the worktree, and `poa-web/src/trust-config.js` is mid counter-11
> bump). None of the 20 imports `platform-terminal.js`, `app.js`,
> `judged-session.js`, or reads `index.html` — verified by reading each failing
> file's import list, not assumed. The three test files covering this work are
> 62/62.

---

# What I did not take, priced honestly

## A · Point the Flight Recorder at the live authority — ~half a day, plus a measurement I cannot make from here

**Player gain: high.** They would inspect the ship's actual wake instead of a
three-row rehearsal.

**Why not now:** the flip itself is four lines of JSON
(`mode: "live"`, `api_base_url`, `authority_id`), and the routes it needs are
already public — `GET /api/poa/signal/{authority}/status` and
`…/transitions/{sequence}` at `node/src/api.rs:2238,2242`. But:

1. **I cannot measure the live endpoint from here.** If the deployed node is not
   reachable at the configured base, `loadConfiguredFlightRecorder` refuses and
   the front-page tile turns red for every visitor. That is honest and
   fail-closed, and it is still a regression I would be shipping blind. The
   discipline is to measure what reality decides, not to guess it.
2. **There is a design flaw to fix on the way.** `authority_id` is hand-pinned
   in an *unsigned* config file, while the page already learns the authority
   from the *authenticated* POAG1 catalog (`state.missions[0].federationId`).
   The pin exists as anti-spoofing, and deriving it from the signed manifest
   instead would be strictly stronger. The right fix is not "fill in the config"
   but "feed the recorder the verified federation id, and keep the config for
   `mode` and `max_transitions` only."

**Shape:** thread the verified `federationId` from `app.js` into
`loadPlatformEvidence`; change `parseFlightRecorderConfig` to accept
`authority_id: null` in live mode when the caller supplies a verified one, and
to refuse a config authority that *disagrees* with it; set `api_base_url` to
`/node` so it rides the same same-origin tunnel the judged session already uses;
verify against the live host before merging.

## B · A persistent officer profile — ~3 days, and the one most likely to be closed badly

**Player gain: high** — the difference between four role cards and a character.

**Cost, honestly:** it is not a UI job. It needs (i) a durable per-actor table —
`persist/src/lib.rs` has twelve PoA modules and none is a profile store; (ii) a
route — none of the 19 PoA routes touches one; (iii) a versioned state
transition authored in Lean, with `OfficerLogbook.lean` as the starting kernel,
which currently has no `@[export]` at all; (iv) a decision about what a profile
may hold and who may read it, which is key-material-adjacent and is the
operator's call, not mine.

> ⚠ **This is the badge to be most careful about.** The cheap version — have the
> page remember an officer in `localStorage` and drop the caveat — would be
> exactly the failure this whole exercise exists to prevent: a route that
> fabricates a receipt, which is strictly worse than a card saying there is no
> receipt. There is already a correct precedent to follow instead:
> `galley-status.js` refuses to invent an actor to make the node answer, and
> says so in its own comments. An officer profile must be node-held and
> actor-keyed, or it must not exist.

## C · Crew expedition settles something — ~1 week

**Player gain: medium-high** — an expedition that leaves a mark.

**Cost:** the Lean side is furthest along of the three big ones —
`CrewFieldMission*` exists and exports `dregg_poa_crew_field_step` — but that
export has no safe Rust wrapper caller, no node route, and no client. Landing it
means participant signatures over a joint state machine (several players, not
one), a contribution/custody output object, and a durable record. It also
overlaps B: an expedition contribution that credits nobody is not much of a
contribution. Sequence B before C.

> A sibling lane landed `360af8138` ("the crew handoff, driven end to end") on
> the same day as this ledger. Re-price C against that commit before starting;
> its subject suggests part of this path now runs.

## D · DrEX settlement into the web build — weeks, and it is five jobs, not one

**Player gain: high, eventually. Not an afternoon, and not a fortnight.**

Concretely missing, in dependency order:

1. **A mint at the source.** A `MarketUnit` can only be created from a
   `CrewFieldMissionRuntime.OrdinaryMintAuthorization` inside a sealed EventBatch
   receipt (`OrdinarySalvageExchange.lean:44-56`). That means C lands first.
2. **An `@[export]` for `OrdinarySalvageExchange`.** There is none.
3. **A durable custody table.** None of the twelve PoA persist modules holds
   custody.
4. **An HTTP route.** None of the 19.
5. **A bridge object.** DrEX settles computrons between pinned traders; there is
   no asset representation a PoA `MarketUnit` could inhabit on either side. The
   Dark Bazaar judge that would clear it
   (`circuit-prove/src/dark_bazaar_private_poa_settlement.rs:546`) has every
   call site behind `#[cfg(test)]`.

The Dark Bazaar tile's four locked gates — inventory, private order, clearing,
settlement — are an accurate map of exactly this, and rendering them as four
independent gates rather than one "coming soon" is the right presentation. Leave
the badge; it is describing real work.

---

# The most valuable finding

**Three badges were wrong, and all three were wrong in the same direction: they
understated the system.** Not one badge on this page overclaimed.

- The **Flight Recorder** grade credited "the head the node reported" while
  reading a fixture no node has ever served. (Overclaims its *source*,
  understates nothing — but it is the same failure to look at what produced the
  evidence.)
- The **Field drills** copy denied that anything leaves the browser while a
  node-scored judged path sat live on the same page, one panel above the tile.
- The **crew** grade said a crew choice lives "nowhere else" on a terminal whose
  node durably keeps your player key in at least three player-keyed stores.

And the register hid a fourth: a judged run's evidence grade, folded into the
practice run's caveat.

The pattern is worth naming, because it is the opposite of the failure everyone
watches for. A caveat that **understates** reads as scrupulous, passes every
review, and is never challenged — nobody audits a page for being too humble. It
costs the player the best thing on the surface, and it costs the project the
credit for work that is actually done. "Honestly labelled" was doing the work of
a stopping condition in all three cases, exactly as the doctrine warns; in two
of them the honest-sounding sentence was simply false.

A corollary for the next pass: **read the badge against what produced it, not
against the roadmap.** Every one of these survived because a reviewer checked
"is this gap real?" (yes, some gap was) instead of "is this sentence true?" (no).
