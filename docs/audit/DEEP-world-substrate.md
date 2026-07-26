# DEEP audit — the world / realm / entity substrate

Archaeology, read-only, current-resolution. Scope: the pieces a living world
composes from — `realm-model/`, `param-compose/`, `entity-compose/`, the node MUD
primitives (`node/src/mud_e2e.rs`, `node/src/shared_world.rs`), the three deployed
games, and the Custom-VK Door. Each component is labelled **REAL** (works, driven),
**PROTOTYPE** (a model / standalone), **NAMED** (a seam, described not built), or
**STUBBED** (present but hollow at current resolution), with citations, plus how
CONNECTED it is to the rest.

The through-line finding: **there are three separate substrates that each work, and
the cleanest-modeled one (the assigned realm/entity stack) is the least wired in.**

---

## 0. The map at a glance

| component | resolution | driven? | in root workspace? | wired to a running world? |
|---|---|---|---|---|
| `realm-model` (realm/instance/identity/catalog) | **REAL as a model / PROTOTYPE as production** | yes, 4 test files | **NO — standalone `[workspace]`** | **NO — 0 reverse deps** |
| `realm-model` hybrid-PQ identity + succession | **REAL** (real ed25519 + ML-DSA-65) | yes | no | no |
| `realm-model` durable persistence (receipt chain) | **NAMED** (explicitly not served) | n/a | no | no |
| `param-compose` (the Braid — general composition AIR) | **REAL** (proves, budgeted, non-vacuity) | yes | **YES** (member + default) | **NO — only entity-compose uses it** |
| `entity-compose` (entity ⊗ Door end-to-end) | **REAL through the Door / NAMED final weld** | yes, incl. `#[ignore]` real prove | **NO — standalone `[workspace]`** | **NO — 0 reverse deps, game-free** |
| the outcome→cell-field weld | **NAMED** (one missing executor atom) | shape demonstrated | — | — |
| `node/src/mud_e2e.rs` (hosted MUD) | **REAL** | yes, e2e over HTTP | yes (`node`) | **YES — this is a running world** |
| `node/src/shared_world.rs` (2-identity live world) | **REAL** | yes, e2e over HTTP | yes (`node`) | **YES** |
| `dungeon-on-dregg` (reimagined descent) | **REAL** | yes + served | yes (default member) | **YES — via spween-dregg + services** |
| `dregg-multiway-tug` (Lean-sourced) | **REAL** | yes + served | yes (default member) | **YES — via dreggnet-game-board** |
| `dregg-automatafl` (hand-written AIR) | **REAL & plays / DEBT as "refinement"** | yes + served | yes (default member) | **YES — but the AIR is the flagged debt** |
| the Custom-VK Door (`Effect::Custom`) | **REAL & deployed** | yes (entity-compose e2e) | yes (`turn`/`cell`) | **YES** |

---

## 1. `realm-model/` — the §9 decisions as ONE coherent model

Source spec: `docs/design/HOARDLIGHT-LIVING-WORLD.md` §9; honest-scope companion
`docs/design/MUD-SUBSTRATE.md`. The crate makes three interdependent "cheap now,
expensive-to-retrofit" decisions as one model over a real ledger.

### 1a. What is REAL (driven against cell-backed state)

Every object is a genuine `dregg_cell::Cell` on a genuine `dregg_cell::Ledger`
(`realm-model/src/world.rs:134-145`, `spawn_cell` at :180). The three decisions
MEET in `RealmWorld::admit` (`world.rs:485-561`): resolve surface→identity, locate
instance→realm, gate the cited `ruleset_root` against the realm catalog, enforce the
scope membrane, apply effects, chain a receipt. All refusals leave the ledger
unchanged (validate-all-before-apply, `world.rs:518-536`).

- **§9.4 realm/instance** — `Realm` (durable cell, `realm.rs:80-94`) vs `Instance`
  (scoped child, `instance.rs:46-57`); `open_instance` pins the parent value at
  birth (`world.rs:377-399`), `settle_instance` crosses the membrane to advance the
  durable hoard (`world.rs:590-636`). Driven end-to-end: instance A settles 40 → a
  NEW instance B pins **40** not 0 (`realm-model/tests/driven.rs:94-99`).
- **§9.5 canonical identity, surfaces DERIVE** — `mint_identity` exists first
  (`world.rs:230-265`); `bind_surface` writes a binding cell whose entire state is
  the canonical id (`world.rs:279-290`); there is deliberately **no**
  `identity_from_surface(...)`. Two surfaces resolve to the SAME id
  (`realm-model/tests/driven.rs:140-150`).
- **§9.2 ruleset catalog = committed law** — membership is non-vacuous: stored
  VALUE == the root, so admission checks `get(key(C)) == Some(C)` (`catalog.rs:30-41`,
  `world.rs:467-477`). The canary: unlist a listed root and the SAME turn is now
  refused (`realm-model/tests/driven.rs:254-265`).
- **Per-realm membrane** (ember's DECIDED "Both") — `PinAtBirth` vs `MovingParent`
  is COMMITTED on the realm cell (`realm.rs:17-31`, `world.rs:346-364`) and
  load-bearing: flip the membrane and the same instance's `visible_parent` flips
  (`realm-model/tests/membrane_per_realm.rs:117-139`). The additive settle is a conflict-free
  commutative accumulator; a non-commutative settle gets an OCC variant that DETECTS
  a moved head (`Refused::SettleConflict`) but the resolution policy is named as
  ember's call (`world.rs:653-679`, `membrane_per_realm.rs:182-239`).
- **Hybrid-PQ identity succession + guardian recovery** — this is genuinely REAL
  crypto: a `HybridKey` is real ed25519 (`ed25519-dalek`) AND real ML-DSA-65
  (`dregg_turn::pq::MlDsaTurnKey`) from one seed (`identity.rs:94-144`), matching the
  shipped hybrid signer. Rotation gated by signer-commitment == committed current key
  (`world.rs:788-827`), K-of-N guardian recovery counting distinct valid guardians
  (`world.rs:837-882`). Canaries driven in `realm-model/tests/hybrid_identity_succession.rs`.
  A self-audit test even proves the honest limit: the ed leg is cofactored (small-order
  forgeable *in isolation*) but PINNED-BY-COMMITMENT at both callers, so not reachable
  (`realm-model/tests/classify_b_reachability_probe.rs` — verdict PINNED-KEY).

### 1b. What is PROTOTYPE / NAMED (the crate's own honest scope)

`MUD-SUBSTRATE.md:313-390` states it plainly, and the code agrees:

- **The admission gate is a standalone function, not the executor.** In production the
  catalog check belongs in `turn/src/executor/proof_verify.rs` and `ruleset_root`
  must become a first-class field of `dregg_turn::Turn`/receipt (it is not today).
  `world.rs:1-18` says this in the module doc. **NAMED.**
- **Effect application bypasses the signed-turn executor** — it writes fields directly
  via `Ledger::update_with` (`world.rs:193-204`), not the signed / fee-estimated /
  capability-authorized HTTP path that mud_e2e actually drives. Same types, not the
  same path. **PROTOTYPE.**
- **Only `Effect::SetField` is interpreted**; all other variants refused
  (`world.rs:529`). **STUBBED for the general effect vocabulary.**
- **Durable persistence is NOT served.** `RealmWorld` chains receipts in-memory
  (`world.rs:143-144`, `hash_receipt` :932). The real chain is populated only
  client-side from the cipherclerk's in-memory `Vec<TurnReceipt>`; no node endpoint
  serves it. `MUD-SUBSTRATE.md:365-389` names this as *the* load-bearing dependency
  for realm persistence and calls it the first production add (a `node/` + `persist/`
  change). **NAMED — the realm's history survives only while one process holds it.**

### 1c. Connectedness: **DISCONNECTED**

`realm-model` has its own empty `[workspace]` table (`realm-model/Cargo.toml:38`),
so it is **not a member of the root breadstuffs workspace** — the main `cargo build`
never builds it. Its comment says so outright: "this crate is NOT a member of the
root breadstuffs workspace (the main loop adds it after)." Reverse-dependency search:
**nothing references `realm_model` except its own four test files.** It is the
textbook "built the real thing, never connected it."

---

## 2. `param-compose/` — the Braid (general parameter-composition AIR)

### REAL

The §9.3 component: a Custom-VK AIR proving
`outcome = Σ_linear coeff·P[role].params[i] + Σ_knots coeff·P[a].params[i]·P[b].params[j]`
over N typed projections — the nonlinear KNOTS being exactly what the declarative
`AffineLe`/`AffineEq` StateConstraint vocabulary cannot express, forcing a hand-AIR
(`src/lib.rs:19-30`). It is engine-general: a new creature / balance table / whole
new institution system costs **data** (a new `ruleset_root`), never a kernel or AIR
edit (`lib.rs:31-45`). The PI layout is CONSTANT in the number of subjects — one
`subjects_root` binds the whole ordered list at ~124 bits rather than a slot per
subject (`src/pi.rs:1-33`), which is the precise cul-de-sac §9.3 forbids.

Budget is measured, not asserted: the realistic `n4 p8 l8 k6` shape folds an
**803-column** leaf, 221 under the 1024 cap, and `param-compose/tests/prove_fold.rs` proves that
saturated shape as a single foldable leaf (`lib.rs:56-86`). Honest scope is
enumerated in `lib.rs:107-137` (outcome-not-welded, identity faithfulness upstream,
bounded 28-bit identity namespace goes vacuous past the margin and a defeating shape
is REFUSED, roles are keys, selective disclosure is a commitment opening).

### Connectedness: **near-isolated**

`param-compose` IS a root workspace member + default member (built by CI). But the
only code that uses it is `entity-compose` (reverse-dep search: `param_compose`
appears only in its own tests + `entity-compose`). **No game uses the Braid.** The
deployed games carry their own program artifacts (multiway-tug/automatafl below), so
the "most reused, most tempting-to-hardcode component" is, at current resolution,
reused by exactly one downstream — and that downstream is itself standalone.

---

## 3. `entity-compose/` — a real entity ⊗ the Door, end to end

### REAL (through the deployed Door) + NAMED (the final weld)

This crate wires four already-built pieces that "had never been wired together
before" (`src/lib.rs:1-24`): a param-carrying entity cell (params in the committed
wide plane at key ≥ 16, so they move the v9 commitment), the `param-compose` AIR,
the `Effect::Custom` Door, and the cell.

The end-to-end test genuinely drives `TurnExecutor::execute` (not a helper):
`entity-compose/tests/end_to_end.rs:204-269`. A real entity's params compose into a licensed outcome
(`10·2 + (-2)·5·4 = -20`), the turn carries the sub-proof through the Door, PASSES the
state weld against the entity's REAL commitment, and dies at the intentionally-
unparseable rotated-leg parse (the fast terminus — the weld runs before the
minutes-slow leg). The **canary bites**: a proof about a DIFFERENT entity is refused
by the weld (`TurnError::CustomProofStateBindingMismatch`, `end_to_end.rs:280-338`)
and the sovereign commitment does not advance. Non-vacuity: an outcome the ruleset
does not license has no satisfying witness (`end_to_end.rs:348-378`). And the SLOW
truth exists: `entity-compose/tests/leaf_prove.rs` (`#[ignore]`, minutes, `--features prove`) mints
a real foldable leaf whose in-circuit PI commitment BYTE-matches the host `WideHash`
binding the `Effect::Custom` row carries, over the entity's real `old8/new8`
(`leaf_prove.rs:64-108`) — and a forged outcome cannot mint a leaf (:113-156).

**The one NAMED residual — the outcome→cell-field weld.** The state weld checks only
the `[old8 ‖ new8]` prefix, not the app PIs, so a host could write outcome `X` into
the cell while the sub-proof commits outcome `Y` and the Door would not notice
(`src/lib.rs:38-50`). The host arranges the post cell to carry the outcome and a
harness check verifies the equality the kernel is missing
(`harness_verify_outcome_welded`, `lib.rs:249-268`). Closing it for real is a single
cell-state-layout-aware executor atom — precisely named, shape demonstrated, not
built.

### Connectedness: **DISCONNECTED + game-free by design**

`entity-compose` also has its own empty `[workspace]` (`entity-compose/Cargo.toml:19`)
— **not a root member.** Reverse-dep search: nothing uses it but its own tests. It is
deliberately game-free ("this crate knows no game"). So the composing substrate is
proven reachable from the Door, but stands alone: no realm, no identity, no game
rides it yet.

---

## 4. The node MUD primitives — the substrate that actually RUNS

These are the counter-example to the disconnection story: **REAL, driven, and part of
the shipping `node` crate.**

### 4a. `node/src/mud_e2e.rs` — the hosted living world (REAL)

Boots a headless `NodeState` (no gpui), hosts a real deos-js gamemaster program
(`mud_gm.js`) that spawns rooms/character/NPC as real cells, publishes cap-gated
affordances, and the player DISCOVERS them over the node's HTTP route and FIRES
signed turns through the genuine `/turns/submit` ingress (`mud_e2e.rs:160-359`). The
reactive tick (`mud_gm_tick.js`) observes xp≥100 and drives a level-up + NPC reaction
+ a forked **dungeon INSTANCE** with its OWN published surface (`mud_e2e.rs:361-402`).
The asymmetry is receipted and real: a player's cross-cell write on an NPC it holds
no cap over, and a reach into a dungeon fork it holds no cap over, are BOTH refused by
the executor's authority gate while the GM's same moves commit (`mud_e2e.rs:404-457`).
This is the running world; the realm-model `Instance` is explicitly "what THIS dungeon
fork becomes when named as protocol" (`instance.rs:1-9`) — i.e. the fork is real, the
protocol-object is the (disconnected) model.

### 4b. `node/src/shared_world.rs` — two identities co-inhabit (REAL)

Two DISTINCT key-ceremony identities (`AgentCipherclerk` each) connect over real HTTP,
fire cap-gated turns into a shared board, and each SUBSCRIBES to the node's receipt
event stream so identity B observes A's turns live (`shared_world.rs:1-30`,
`boot_shared_world` :173-243, `SharedClient` :284-508). Presence + attribution are
real (`receipt.agent`); the over-reach (B firing at A's private cell) is refused by
the authority gate (`touch_private` :462-472). This is the "one identity resolves
across surfaces" (realm-model §9.5) — but here each identity is a raw agent cell, NOT
a `CanonicalIdentity`; realm-model's `resolve_surface` is what this SHOULD resolve to
(`MUD-SUBSTRATE.md:152-156`) and does not.

---

## 5. The three games — what deploys + plays

All three are **root workspace default members** (built + tested by CI) and are served
by real services. Crucially, they ride a DIFFERENT substrate than §1-3: `spween-dregg`
(the deployed `WorldCell`/`EmbeddedExecutor`) and, for multiplayer, `starbridge-v2`.

### 5a. `dungeon-on-dregg` — the reimagined descent (REAL)

A move is a real cap-bounded `TurnReceipt` on `spween-dregg`'s `EmbeddedExecutor`; an
illegal move is a real `WorldError::Refused` that commits nothing; the gate is an
executor-enforced `CellProgram`/`StateConstraint` tooth (`Cargo.toml` header). It
CONSUMES a wide real stack by composition: `collective-choice` (quorum voting),
`dregg-dice` (verifiable randomness), `dreggnet-asset` (loot as owned transfer-gated
notes), `procgen-dregg` (provably-fair drops), `dregg-schema` (the validated
allocator), and — honoring the "AIR authored in Lean" law — the descent's register
state is a `dregg_schema::Schema` and its program is **loaded from a Lean-emitted
artifact**: `dungeon-on-dregg/program/dungeon_program.json` (16 KB) is the checked-in
cache of `metatheory/Dregg2/Games/DungeonProgram.lean` (46 KB), the Rust loader doing
only symbolic-name→allocator-index resolution. Multiplayer (`mud` module) rides
`starbridge_v2::world::World` (the real multi-actor ledger); single-player rides the
serial `EmbeddedExecutor`. **Deployed:** `demo/real-dungeon-service` hosts The
Warden's Keep over HTTP — `POST /session/move` is one real executor turn,
`GET /session/verify` replays and checks receipt-chain links, `POST /validate` lints
`.dungeon` source live (`demo/real-dungeon-service/src/main.rs:1-45`). Also reached
through `dreggnet-offerings`, `dreggnet-web/telegram/wechat`, and `discord-bot`.

### 5b. `dregg-multiway-tug` — Lean-sourced card game (REAL)

A 2-player tug-of-influence game (original re-theming of the Hanamikoji mechanic) on
the real executor: state as a `dregg-schema`-allocated layout, teeth as
`CellProgram::Cases` (conservation via `SumEquals`, one-action-per-round via
`WriteOnce`), a play is a verified turn (`Cargo.toml`). It carries the full stack: a
Poseidon2 hidden-hand membership tooth that lines up with the real `MerkleMembership`
STARK, the `game-turn-slice` foldable-leaf lowering, `dregg-circuit-prove` recursion,
and `dregg-lightclient::verify_history` accepting the folded whole-match proof. It has
a Lean-emitted symbolic program loader (`program_loader.rs`) and a
`dreggnet-offerings` `TugOffering` surface. **Deployed** via `dreggnet-game-board`
(matches) and `dreggnet-prove-service` (folds); reachable through the surface
frontends and `wasm/src/bindings_multiway_tug.rs`.

### 5c. `dregg-automatafl` — plays REAL, but the AIR is the flagged DEBT

n=2 (and 11×11) board-transition game, served through `dreggnet-game-board` /
`dreggnet-prove-service` and the offering surfaces. It genuinely plays and folds. BUT:
its `air.rs`/`moves.rs`/`builder.rs` are a **hand-authored Custom-VK AIR** (813 + 1168
+ 773 lines) — exactly the "hand-written Rust AIR debt" `~/.claude/CLAUDE.md` flags as
"DEBT, not a foundation." Its `Cargo.toml` and `tests/refinement.rs` describe it as
"Refines `Dregg2.Games.Automatafl.applyTurn`" with a differential oracle
(`automatafl-logic` git dep) — but per project doctrine a Rust AIR carries no proof
and "translation validation between a Rust AIR and a spec is a LIE" (no semantics of
Rust). So: **REAL as a playable, folding match; the "refinement/verified" framing is
the debt, not verification.** Contrast with 5a/5b, which source their programs from
Lean.

---

## 6. The Custom-VK Door + app-root weld — REAL & deployed

`Effect::Custom` reaches `TurnExecutor::execute` for real: the registry dispatch, the
count gate, the registry verifier accept/reject, and the state weld
(`[old8 ‖ new8]` == the cell's stored sovereign commitment / claimed new) all fire on
the deployed path — proven by entity-compose's e2e distinguishing every failure mode
(`end_to_end.rs:243-268`) and the wrong-entity weld refusal
(`CustomProofStateBindingMismatch`, :324-337). The PI ABI is
`dregg_circuit::effect_vm::custom_state_binding` (`param-compose/src/pi.rs:35-40`). The
wide plane (`set_field_ext` at key ≥ 16 → committed `fields_map`) genuinely carries
entity params INTO the v9 chip commitment the Door welds (`entity-compose/src/lib.rs:52-149`).
So the composing substrate is REAL from the Door inward; the single hole is the app-layer
outcome→cell-field atom (§3, NAMED).

---

## 7. What a living world could stand up TODAY (from these pieces)

**Today, unmodified, you can run:**
- A **hosted multiplayer MUD** — rooms, characters, NPCs, level-ups, forked private
  dungeon instances with membrane isolation — as deos-js programs on the node, driven
  by signed cap-gated turns over HTTP, with a receipted authority asymmetry (mud_e2e).
- A **live 2-identity shared world** with live receipt-stream sync, presence,
  attribution, and a real over-reach refusal (shared_world).
- **The reimagined descent** (The Warden's Keep) as a real HTTP service where every
  move is an executor turn, illegal moves are real refusals, runs are replay-verified,
  and `.dungeon` text compiles onto the same executor — with the descent program
  sourced from Lean (real-dungeon-service + dungeon-on-dregg).
- **Two more deployed games** (multiway-tug, automatafl) as verified turns that fold
  into whole-match proofs the light client accepts, reachable from web / Telegram /
  WeChat / Discord surfaces (dreggnet-game-board, dreggnet-offerings).
- **A real entity composing through the Door** — params in a committed cell plane,
  a nonlinear-knot outcome proven under a versioned ruleset, bound to the entity's
  real commitment (entity-compose, with the real leaf-prove behind `#[ignore]`).

**What you could NOT stand up today from these pieces:**
- A world that **persists across a node restart** with replayable history — the
  durable node-served receipt/turn chain does not exist (§1b, NAMED).
- **Committed law** enforced by the executor — the catalog gate and `ruleset_root`
  are modeled in `RealmWorld::admit`, not in the executor's proof-verify path; two
  hosts can still be configured with different accepted VK sets (§1b).
- **One canonical identity resolved across surfaces** in the running node — the MUD
  and shared-world attribute raw agent cells; the `CanonicalIdentity` / `resolve_surface`
  layer is unwired (§1c, §4b).
- **A game that rides the Braid** — no deployed game uses `param-compose`; the games
  carry bespoke programs, and entity-compose (which does ride it) carries no game.
- The **outcome→cell-field weld** for any composition-carrying turn (§3, NAMED).

---

## 8. The load-bearing disconnections (built-not-wired)

The recurring "built the real thing, never connected it" pattern, ranked by how much
would be unlocked by wiring each:

1. **`realm-model` is a standalone crate with zero reverse deps** — not even in the
   root workspace (`Cargo.toml:38` empty `[workspace]`). The cleanest model of
   realm/instance, canonical identity, committed catalog, per-realm membrane, and
   hybrid-PQ succession EXISTS and is driven, and the running node
   (mud_e2e/shared_world) implements the SAME concepts ad-hoc in JavaScript + raw
   agent cells. The wiring is fully named (`MUD-SUBSTRATE.md:163-198`): catalog gate
   into the executor, `ruleset_root` onto `Turn`, surface resolution in the offering
   ingress (`dreggnet-offerings/src/lib.rs:302` is the seam), realm/instance as
   node-hosted objects, and the durable receipt chain. None of it is done.

2. **The durable receipt/turn chain is not served** — this is the single dependency
   that makes realm persistence real, and it is the first production add named
   (`MUD-SUBSTRATE.md:365-389`), building on `persist/src/snapshot.rs`. Without it the
   whole realm/instance persistence story is process-lifetime only.

3. **`entity-compose` + `param-compose` (the Braid) are wired to each other and to the
   Door, but to no game and to no realm.** The general composition verifier — "the
   most reused, most tempting-to-hardcode component" — has exactly one consumer, which
   is itself standalone. A HOARDLIGHT creature/item/institution system is supposed to
   be "one ruleset root over this substrate"; today no such system exists on it.

4. **The outcome→cell-field weld** — one named executor atom stands between
   entity-compose being "reaches the Door and self-verifies" and "the kernel forces the
   post-state to carry the proven outcome" (§3).

5. **`dregg-automatafl`'s hand-authored AIR** — the game plays, but its AIR is the
   Rust-AIR debt the project doctrine forbids extending, and its "refinement" framing
   is not verification. multiway-tug and dungeon-on-dregg show the intended Lean-sourced
   pattern; automatafl is the un-migrated exception.

**Net:** the *running* living world (node MUD + spween-dregg games + dreggnet-* serving
+ multi-surface frontends) is real and broad. The *principled* substrate
(realm/instance/identity/catalog + the Braid + the entity Door composition) is real and
clean but sits beside it, unwired — three working substrates that have not been made
one. The gap between them is entirely NAMED work, not undiscovered risk.
