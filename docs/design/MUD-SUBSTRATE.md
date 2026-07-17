# The MUD Substrate: realm / instance / identity / catalog

## The expensive-to-retrofit model, made concrete

`docs/design/HOARDLIGHT-LIVING-WORLD.md` §9 names the decisions that are *cheap
to make now and expensive to remove after players, assets, content, and
historical receipts depend on them*. Three of them are interdependent — an
**identity** acts in an **instance** of a **realm** whose **catalog** gates the
law the turn cites — so they are built as ONE coherent model in the `realm-model/`
crate, not three lanes that would invent incompatible interfaces.

This document records that model, the three decisions it commits, how it fits the
existing MUD primitives (`node/src/mud_e2e.rs`, `node/src/shared_world.rs`), the
exact node + surface wiring it needs (named, because the model crate does not
edit those), the decisions that are genuinely ember's call, and honest scope
(what is a working model vs a prototype vs a named decision-for-ember).

It is **engine-general**: a realm is not "Hearthspire", an identity is not "a
dragon", a ruleset is an opaque 32-byte root. No game content appears anywhere in
the crate.

---

## What the crate is

`realm-model/` is a standalone crate (its own `[workspace]`, path-deps into the
root — the dregg-tui pattern; the main loop adds it to the root workspace later).
It composes with the ground truth rather than reinventing it:

- **real cell-backed state** — every object is a real `dregg_cell::Cell` on a
  real `dregg_cell::Ledger`, the same primitives mud_e2e / shared_world use;
- **the real effect vocabulary** — a realm turn carries
  `dregg_turn::action::Effect` (the exact `Effect::SetField { cell, index, value }`
  mud_e2e fires);
- **the node's id derivation** — `derive_cell_id(seed)` mirrors
  `spawned_cell_for(seed)` = `derive_raw(blake3(seed), default_token)`.

Files:

| file | object |
|---|---|
| `realm-model/src/realm.rs` | `Realm` — the persistent shared world (a durable cell) |
| `realm-model/src/instance.rs` | `Instance` — a scoped, disposable child of a realm |
| `realm-model/src/identity.rs` | `CanonicalIdentity`, `SurfaceRef`, `Surface` — the durable principal + per-surface refs |
| `realm-model/src/catalog.rs` | `RulesetCatalog` — a realm's committed active-ruleset-root set |
| `realm-model/src/world.rs` | `RealmWorld` — the admission gate where the three decisions meet, over one `Ledger`, plus the ordered receipt chain |
| `realm-model/tests/driven.rs` | the driven prototype (persistence, cross-instance identity, catalog-as-law, membrane) |

---

## Decision 1 (§9.4): persistent REALM vs child INSTANCE — separate first-class objects

**The decision.** A `Realm` is the persistent shared world (durable, many
participants, cross-session): one durable cell whose state outlives any session.
An `Instance` is a scoped/seeded child of a realm: its own cell, disposable, with
an explicit relationship to its parent.

**What persists vs what resets.** The realm cell's fields (`EPOCH`, `HOARD`) are
durable world state. The instance cell's fields (`STATUS`, `RESULT`, `PARENT_PIN`)
are scoped scratch that resets with the instance — a fresh instance is a fresh
cell.

**The membrane (birth).** `open_instance` PINS the realm's current durable value
into the instance's `PARENT_PIN` at birth. This chooses the §9.4 option "child
pins a parent root at birth" over "child observes a moving parent" — see
**decisions-for-ember**.

**The membrane (return).** `settle_instance` reads the instance's certified
`RESULT`, crosses the membrane to advance the realm's durable `HOARD`/`EPOCH`, and
finalizes the instance. Only the settle path may write the realm cell; an ordinary
in-instance turn that targets the realm cell is refused
(`Refused::OutsideInstanceScope`). This is the durable/disposable boundary,
enforced — the same isolation flavor as mud_e2e's dungeon-fork membrane, promoted
from a JavaScript host program into the model (the doc's exact ask).

**Driven** (`realm_persists_across_instances`): instance A pins parent=0, earns
40, settles → realm hoard=40, epoch=1, instance finalized (and refuses reuse). A
NEW instance B pins parent=**40** (sees the persisted value), settles +5 → realm
hoard=45. The realm outlived both instances.

---

## Decision 2 (§9.5): a canonical IDENTITY the surfaces DERIVE from

**The decision.** A `CanonicalIdentity` is a durable principal minted from a
principal key; it exists FIRST. A `SurfaceRef` — `(Surface, surface-local id)`
like `(Discord, "pip#1234")` or `(Web, "sess-…")` — is *bound onto* an existing
canonical identity. The binding is a real cell whose entire state IS the canonical
id it points at. Resolution reads that cell → the canonical id.

**The direction is the whole point.** There is deliberately no
`identity_from_surface(discord_id)` constructor. A surface can only be bound to a
canonical identity that was minted independently, so the surface is DERIVED (it
points at the identity) and the canonical identity is PRIMARY. This is the §9.5
refusal — "do not make the first Discord ID the world identity" — made structural.

**This is the object the offering host's viewer should resolve to.**
`dreggnet-offerings`' viewer is currently an opaque per-surface identity
(`dreggnet-offerings/src/lib.rs:302`). `RealmWorld::resolve_surface` is the
resolution it should perform: per-surface ref → durable canonical id.

**Driven** (`one_identity_across_surfaces_and_instances`): one identity, bound to
a Discord surface AND a Web surface, resolves to the SAME canonical id via either;
an unbound surface resolves to nothing (a surface id is not itself an identity);
the same identity acting in two different instances arriving on two different
surfaces produces receipts attributed to the SAME canonical id.

---

## Decision 3 (§9.2): the RULESET CATALOG = committed law

**The decision.** Today VK registration is host config: a verifier is registered
in ONE executor instance (`cell/src/custom_effect.rs`), and two hosts can be
configured with different accepted sets. The catalog moves the admitted-roots set
into COMMITTED CELL STATE owned by the realm: which `ruleset_root` a turn may cite
is read from the realm's catalog cell, and the `ruleset_root` is a first-class
field of the turn and the receipt — not inferred from the serving binary.

**Cell-backed and non-vacuous.** Each admitted root `R` is stored in the catalog
cell's committed extended-field map under a key derived from `R`, with the stored
VALUE being `R` itself. Admission of a cited root `C` checks
`get(key(C)) == Some(C)` — confirming both that `C` is listed AND that the listing
is genuinely `C` (not an 8-byte-key coincidence). Unlisting writes zero, which no
real root equals.

**Driven** (`catalog_is_committed_law`): a turn citing an unlisted root is refused
(`Refused::RulesetNotInCatalog`) and commits nothing; a turn citing the listed
root is admitted and its receipt commits the root. **Canary:** unlist the
previously-listed root and the SAME turn is now refused — proving the gate reads
live committed catalog state, not a compile-time set.

**Relationship to `param-compose`.** `param-compose` already binds `ruleset_root`
as a public input (`param-compose/src/pi.rs`) — the AIR proves the composition is
the one THAT root's law licenses. The catalog is the missing complement: it
governs WHICH `ruleset_root`s a realm ADMITS. Together: the catalog says a root is
law; the VK proves a turn obeyed that exact root.

---

## How it fits mud_e2e / shared_world

- **A realm is what mud_e2e's world becomes when it persists.** mud_e2e hosts a
  living world (rooms, a character, an NPC) as cells on the node ledger, but the
  ledger is a tempdir that dies with the test. `Realm` is that world's durable
  identity + durable state; the model's job is to make "persist it" a protocol
  object, not a rewrite.
- **An instance is what mud_e2e's dungeon fork becomes as protocol.** mud_e2e
  forks a private dungeon instance with its own surface and refuses a player who
  reaches into it (`node/src/mud_e2e.rs:434`). `Instance` + the scope membrane are
  that isolation named as protocol (`open_instance` / `settle_instance` /
  `OutsideInstanceScope`) rather than left in `mud_gm.js`.
- **An identity is what a shared_world participant resolves to.**
  `shared_world.rs` gives each key-ceremony participant an agent cell and
  attributes every receipt to it (`receipt.agent`). `CanonicalIdentity` is the
  durable object that agent cell (and its Discord/web/telegram surfaces) resolve
  to — so "who acted" is one principal across surfaces, not a per-surface string.
- **The effect vocabulary is identical.** Both fixtures fire
  `Effect::SetField { cell, index, value }`; `RealmTurn.effects` is exactly that,
  so a realm turn is admissible on the same executor path.

---

## The node + surface wiring this model needs (named — not edited here)

The model crate does not edit `node/` or the surfaces. The wiring it requires,
named precisely:

1. **Catalog gate in the executor, not a standalone function.**
   `RealmWorld::admit` models the semantics; production must move the catalog
   membership check into the executor's proof-verify path
   (`turn/src/executor/proof_verify.rs:216`, where a proof-carrying turn already
   fails closed on an unregistered VK). The realm's catalog cell becomes the
   authority the executor reads, replacing (or gating) the per-instance
   `CustomEffectRegistry` (`cell/src/custom_effect.rs:184`). Concretely: a turn's
   cited `ruleset_root` must be checked for membership in the addressed realm's
   catalog cell BEFORE the custom-effect verifier is dispatched.

2. **`ruleset_root` as a real field on `Turn`/receipt.** Today it is not a
   first-class field of `dregg_turn::Turn`; the executor infers law from the cell
   program + registered VKs. The turn envelope needs the cited `ruleset_root`
   (and the addressed realm/instance) so the executor can perform the catalog
   check and the receipt can commit the root. `dregg-turn::turn::Turn` +
   `TurnReceipt` are the structs to extend (additively).

3. **Surface resolution in the offering/node ingress.** The node's signed-turn
   ingress and `dreggnet-offerings` currently key on a per-surface identity. They
   need to resolve a `SurfaceRef` → canonical id via a binding cell before
   attributing/authorizing a turn. Named surfaces to wire: the Discord bot
   (`discord-bot/`), the web/telegram/wechat backends under `dreggnet-*`, and the
   node HTTP ingress (`node/src/api`). `dreggnet-offerings/src/lib.rs:302`'s
   identity wrapper is the seam.

4. **Realm/instance lifecycle as node-hosted objects.** `open_instance` /
   `settle_instance` must be node operations (hosted server programs, akin to
   mud_e2e's `deos_host::host_server_program`), so instances are durable cells the
   node serves, not test-local structs.

5. **A durable, node-served receipt chain** — see honest scope below.

---

## Decisions — two DECIDED by ember, two still open

Of the four policy items the model originally flagged, ember has DECIDED two. They
are now built and driven; the other two remain policy calls.

### DECIDED — Membrane is PER-REALM (§9.4), ember chose "Both"

The membrane is a **property of the realm**, committed on the realm cell
([`realm::field::MEMBRANE`]), not one fixed engine policy. Each realm declares a
[`Membrane`]:

- **`PinAtBirth`** (the original committed behavior) — the instance snapshots the
  realm root at open; concurrent realm changes are INVISIBLE until settle.
  Deterministic and replayable — a fair daily roguelite run (The Descent's daily
  seed), where two players on the same seed must see the same world regardless of
  what the shared realm did meanwhile.
- **`MovingParent`** (new) — the instance tracks the realm HEAD; concurrent realm
  changes are VISIBLE as they happen. A live shared world (a persistent town like
  Hearthspire), where an instance is a window onto the moving realm.

`RealmWorld::visible_parent(instance)` is the load-bearing read: under `PinAtBirth`
it returns the birth pin, under `MovingParent` the live realm head. The property
is genuine — **flip a realm's membrane and the same instance's visible parent
flips** (the canary).

**What `MovingParent` needs that `PinAtBirth` did not — the settle-back conflict.**
Under a moving parent the settle-back becomes a live interaction, not a snapshot
merge. Two shapes:

- The **additive settle** (`settle_instance`) is a *commutative accumulator* —
  read-live-head + add — so it is **conflict-free** even under `MovingParent`: two
  concurrent settles both land, no lost update. Driven.
- A **non-commutative settle** (a result that is a function of the head it read)
  can lose an update if the head moved underneath it. The model provides an
  **optimistic-concurrency settle** (`settle_instance_expecting(expected_head)`)
  that **DETECTS** the conflict (`Refused::SettleConflict`) and refuses rather than
  clobbering the concurrent advance. Driven (conflict detected + refused; rebased
  settle lands). The **conflict-RESOLUTION** policy once detected — rebase the
  result onto the new head, three-way merge, or last-writer-wins — is **still
  ember's call** (see the open decisions below; `MovingParent` is what forces it).

**Driven** (`realm-model/tests/membrane_per_realm.rs`): per-realm membrane read off the cell;
`PinAtBirth` hides a concurrent advance while `MovingParent` shows it; flip →
visibility flips (canary); additive settles conflict-free; OCC settle detects a
moved head and refuses.

### DECIDED — Hybrid-PQ identity from ONE seed, with succession + guardian recovery (§9.5), ember chose "recommended"

A `CanonicalIdentity`'s key is a **hybrid** key — ed25519 AND ML-DSA-65 — derived
from ONE 32-byte seed, exactly as the shipped hybrid signer does
(`turn/src/pq.rs`: `MlDsaTurnKey::from_ed25519_seed` = `ML-DSA.KeyGen(ξ = seed)`,
ctx `dregg-hybrid-turn-v1`; the ed25519 half from the same seed bytes). The
canonical id is a **durable cell whose state NAMES the current key**
([`identity::field::KEY_COMMIT`]) — the cell id is the stable durable principal;
the key is state that succeeds.

- **Rotation.** A succession turn SIGNED BY THE OLD KEY advances the committed
  current-key commitment (`rotate_identity`). The succession is **hybrid-signed**
  (ed25519 ∧ ML-DSA-65 over one canonical `succession_message`). The identity's id
  is unchanged, so **every surface binding still resolves to the same canonical id
  across the rotation** — the durable-principal property survives a key change. A
  resolver `follow_chain` walks the succession chain from genesis to the current
  key. **Canary:** a rotation signed by a non-current, non-guardian key is
  REFUSED (`Refused::WrongSuccessionKey`) — accepting it would be a stolen
  identity; the message binds the target, so signing one commit and submitting
  another also fails (`BadSuccessionSignature`).
- **Recovery.** A pre-registered **K-of-N guardian set** (`register_guardians`,
  guardian key commitments listed non-vacuously in the cell's committed field map,
  the catalog pattern) can co-sign a succession (`recover_identity`) so a lost key
  is not a lost identity. The gate counts DISTINCT registered guardians whose
  hybrid co-sign verifies and requires ≥ threshold. **Canary:** below threshold
  fails (`Refused::BelowGuardianThreshold`); a non-guardian cannot pad a quorum;
  one guardian signing twice counts once.

The anti-forgery tooth is a **key commitment**, not a raw signature: the cell
commits to the current key's `(ed_pk, ml_pk)` via `commit_hybrid`; a succession
supplies the signer's public keys, and the gate recomputes the commitment and
checks it against the committed value (or membership in the guardian set) before
verifying the hybrid signature — a stranger cannot substitute their own keys.

**Driven** (`realm-model/tests/hybrid_identity_succession.rs`): rotate → current key advances,
epoch advances, id unchanged, chain resolves to current, both surfaces still
resolve to the same id; wrong-key + tampered-target refused; the retired key
cannot succeed again; 2-of-3 guardian recovery lands, 1-of-3 (and a
non-guardian-padded set, and a doubled single guardian) refused; the hybrid
signature fails closed on either a broken PQ half or a broken classical half.

### Still ember's call

- **Settle-back conflict RESOLUTION + certification policy.** `MovingParent` now
  FORCES the conflict question (above): the model DETECTS a non-commutative
  settle-back conflict (`settle_instance_expecting` → `SettleConflict`), but the
  *resolution* — rebase onto the new head, three-way merge, or last-writer-wins —
  is a policy call, as are: who may settle, whether a settle requires a proof of
  the instance's terminal state, and which results are eligible to cross the
  membrane (the §9.4 "terminal export policy"). **ember's call.**
- **Catalog governance + activation.** The model exposes `list_ruleset` /
  `unlist_ruleset` as direct operations. §9.2 asks for activation height/time,
  catalog inclusion proofs, deprecation-without-deletion, emergency refusal, and
  governance authority (who may append a root). The model deliberately does not
  pick a governance scheme. **ember's call.**

Additionally, **who may amend the guardian set** in production is the same
`set_state` authority the shipped guardian-rotation weld pins
(`sdk/src/guardian_rotation.rs` — `install_guardian_council_authority`); in this
model the owner installs guardians directly. And **device delegation / re-binding
a surface to a new identity** (a distinct account-migration flow) is still not
modeled here.

---

## Honest scope

**Working model** (real, driven against cell-backed state):
- realm / instance / identity / catalog as first-class cell-backed objects;
- realm persistence across instances (settle-back is durable; a new instance sees
  the persisted value);
- one canonical identity across two surfaces and two instances (resolution is
  cell-backed; the binding is derived, not primary);
- the catalog gates the cited `ruleset_root` (unlisted refused, listed admitted,
  canary non-vacuous);
- the instance-scope membrane (an in-instance turn cannot forge the durable realm
  cell);
- **the per-realm membrane** — `PinAtBirth` (deterministic) vs `MovingParent`
  (live) committed on the realm cell, load-bearing (flip → visibility flips), the
  additive settle conflict-free and the OCC settle conflict-detecting;
- **hybrid-PQ identity succession + guardian recovery** — a real ed25519 + ML-DSA
  hybrid signature (the shipped `turn/src/pq.rs` derivation) gates every
  succession; rotation by the current key, K-of-N guardian recovery, the durable
  id surviving a key change, and all the canaries above are driven.

**Prototype / what the node + executor must enforce (named):**
- The **succession gate** (`rotate_identity` / `recover_identity`) is modeled as a
  `RealmWorld` method. In production it is the SAME wiring the catalog needs
  (items 1–2 above): the cited succession is a real `Turn` whose authorization is
  `Authorization::HybridSignature` (the shipped hybrid perimeter,
  `turn/src/executor/authorize.rs::verify_hybrid_signature`), the current-key
  commitment + guardian set live in the identity cell's committed state, and the
  executor checks *signer-commitment == committed-current-key* (or guardian
  membership + threshold) BEFORE admitting the `SetField` that advances
  `KEY_COMMIT`. The shipped guardian-rotation program
  (`sdk/src/guardian_rotation.rs`) is the production shape for the guarded
  key/council slot; this model's succession is the same guarded-advance discipline
  applied to the identity's current-key slot, with the recovery quorum on the
  cell's `set_state` authority. The succession chain, like the realm receipt
  chain, needs the durable node-served history (below) to be replayable across
  restart.
- The **OCC settle** detects a conflict but does not resolve it — the resolution
  policy is ember's open call (above).

**Prototype** (models the semantics; production moves it):
- the admission gate is a standalone function in `RealmWorld::admit`. In
  production it is the executor's proof-verify path; the catalog check belongs
  there, and `ruleset_root` belongs on the real `Turn` (wiring items 1–2 above).
- effect application writes fields directly (`Ledger::update_with`) rather than
  going through the full signed-turn executor. The model uses the real `Effect`
  and `Ledger` types, so this is the same shape, but it is not the signed,
  fee-estimated, capability-authorized executor path mud_e2e drives over HTTP.
- the model interprets only `Effect::SetField`; other effect variants are refused
  (`Refused::UnsupportedEffect`).

**Named decisions-for-ember**: the four policy items above.

### The receipt-chain dependency — what makes realm persistence *real*

`RealmWorld` chains receipts with `previous_receipt_hash` — an ordered,
hash-linked history of admitted turns. **This is the load-bearing dependency for
realm persistence, and it is not served today.**

- `dregg_turn::Turn` already has a `previous_receipt_hash` field, and
  `TurnReceipt::receipt_hash()` chains it (`turn/src/turn.rs`).
- But the chain is populated ONLY client-side, from the client cipherclerk's
  in-memory `Vec<TurnReceipt>` (`sdk/src/cipherclerk.rs:1040`,
  `receipt_chain()` at :2242). In mud_e2e the previous hash comes from
  `s.cclerk.receipt_chain().last()` (`node/src/mud_e2e.rs:112`).
- That chain is **in-memory on the client**, **not durable across restart**, and
  **not served by the node over the wire** (no node endpoint returns it).

So a realm that claims to persist across sessions needs the node to durably
**store and serve** the ordered full turn bodies + receipt chain (the §7.6
"historical replay availability" retention class). Without it, `open_instance`
pinning a parent value and `settle_instance` advancing a durable hoard are real
against a live ledger, but the realm's HISTORY is reconstructible only while a
single process holds it in memory. **Naming the dependency: durable realm
persistence == a node-served, restart-durable receipt/turn chain.** That is the
first production add for this substrate, and it is a `node/` + `persist/` change
(the snapshot machinery in `persist/src/snapshot.rs` is the recovery primitive to
build it on).
