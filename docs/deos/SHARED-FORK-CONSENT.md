# Shared confined fork with graduated consent — "invite someone to my computer"

The capability: I hand someone a **fork of my world** — a confined sub-world they
inhabit as their own principal — whose cap-graph has GRADUATED rights. Inside the
fork they can *do various things locally* with no consent from me; but anything
that **elaborates elsewhere** — touching the network, or my REAL (non-embedded)
cells — pauses and **requests my consent**, granted or denied live. Some of the
things they hold are study-only references; some are consent-gated network
boundaries; the rest are fully embedded.

> Ember: *"invite someone to my computer by sending them a fork that lets them do
> various things LOCALLY but always requests my consent for elaborating
> elsewhere; some of these things are studyrefs and networkboundaries, others are
> just embedded."*

This is the AUTHORITY / CONSENT typing of the membrane. It is built almost
entirely over machinery that already exists in this tree — confinement, the cap
lattice, the powerbox grant-ceremony, the conditional turn, `World::fork`,
branch-and-stitch. The new thing is the *three-tier graduation of a culled
subgraph* and the *consent-as-hole-fill* binding.

## Lane coordination (no overlap)

The **deos-chat lane (`a155821`)** owns the **transport**: how the fork bytes get
to the recipient, the chat membrane that carries messages back and forth, the
conversational surface. THIS doc owns the **authority/consent typing** of the
membrane: which caps are embedded vs studyref vs networkboundary, how a
consent-request is shaped, how it resolves, how local work stitches back. The
seam between them is the `SharedFork` value (this doc's `Vec<Capability>` +
`Vec<StudyRef>` + `Vec<NetworkBoundary>`) handed to chat-transport for delivery,
and the `ConsentRequest` / `ConsentGrant` pair carried back over chat as messages.
Chat moves the envelopes; we type what is inside them.

---

## The model — a fork is a confined sub-world with a graduated cap-graph

A **shared fork** is a `World::fork()` (a deep-cloned ledger + the SAME verified
executor; `starbridge-v2/src/world.rs:581`) handed to **another principal**,
confined so the recipient *cannot escape it* (firmament confinement;
`sel4/dregg-firmament/src/sandbox.rs`), and whose **culled, cap-bounded subgraph**
of MY authority is partitioned into three tiers:

| tier | what the recipient may do | consent | grounded in |
|------|---------------------------|---------|-------------|
| **EMBEDDED** | exercise the cap LOCALLY, mutate the forked cell, any number of times | none — fully granted into the fork | `Effect::GrantCapability` + `CapabilityRef` (`cell/src/capability.rs`), attenuated by the real `is_attenuation` (`granted ⊆ held`) |
| **STUDYREF** | INSPECT / open the cell's exposed slots — read only | exercise (mutate) needs an **upgrade request** | `ReadCap` (`cell/src/read_cap.rs`): read-lattice `FieldSet` + `ViewKey`, attenuates via `is_read_attenuation` |
| **NETWORKBOUNDARY** | request to exercise; the exercise "elaborates elsewhere" (the network, or my real non-embedded cells) | every exercise opens a **consent request** to me, granted/denied live | the powerbox grant-ceremony (`starbridge-v2/src/powerbox.rs`) + a `ConditionalTurn` whose `ProofCondition` is my grant (`turn/src/conditional.rs`) |

The tiers form a lattice of *autonomy*: EMBEDDED ⊐ STUDYREF ⊐ NETWORKBOUNDARY in
"how freely the recipient may act without me". Promotion is monotone only with my
consent (a studyref → embedded via an upgrade grant; a networkboundary fires
once per consent). Demotion is free (any tier can be revoked).

---

## (a) How a shared fork is CONSTRUCTED

I hold a world (my live `World`, my c-list). To invite someone:

1. **Fork.** `let fork = world.fork()` — a deep clone of the ledger + the genuine
   executor (`world.rs:581`). Committing on the fork mutates ONLY the fork; my
   live world is untouched. This is the same substrate `simulate` uses.

2. **Birth the guest principal.** A fresh confined cell in the fork's ledger with
   an EMPTY c-list — exactly `AppLauncher::launch` (`powerbox.rs:404`): no ambient
   authority, the ocap floor. The guest is the recipient's identity *inside* my
   fork. (Transport — how the recipient's real key binds to this guest principal —
   is the chat lane's concern; here the guest is just a `CellId` holding nothing.)

3. **Cull the in-view subgraph.** From MY c-list, choose the caps that travel with
   the fork. This is a *designation*, exactly like the powerbox picker
   (`grantable_targets`, `powerbox.rs:458`): I can only put into the fork caps I
   actually hold (`mint_needs_held_factory`), and each is attenuated before it
   lands — never amplified.

4. **Grant the embedded caps.** For each EMBEDDED target, a real
   `Effect::GrantCapability { from: me, to: guest, cap }` committed through the
   fork's `commit_turn`, attenuated to `confer_rights ⊆ held` by the genuine
   `is_attenuation` (`powerbox.rs:263`). The guest now holds exactly these caps in
   its c-list; it exercises them with no further consent.

5. **Attenuate the studyrefs to read-only.** For each STUDYREF target, a
   `ReadCap::new(target, slots, view_key)` narrowed by `is_read_attenuation`
   (`read_cap.rs:332`). The guest can `open_slot` / `open` the exposed slots
   (decrypt + commitment-check) but holds NO write cap to the target — exercising
   requires an upgrade request (step (b)).

6. **Mark the networkboundaries.** For each NETWORKBOUNDARY target, NO cap is
   granted into the guest's c-list. Instead the fork records a *boundary
   descriptor*: "an exercise of `target` is a consent-gated turn". An attempted
   exercise does not run — it opens a `ConsentRequest` (step (b)/(c)). These are
   exactly the caps whose exercise is "elaborating elsewhere": the network, or my
   real non-embedded cells.

7. **Confine the fork.** The recipient runs the fork as a sandboxed sub-world
   (`sandbox.rs`'s `Confinement`: deny-default, the granted endpoints are the only
   channels, no `network*`, no `process-exec*`). The guest *cannot escape the
   fork to reach my real world* except through the consent door. This is the
   firmament half: confinement is what makes "elaborating elsewhere" a request
   rather than a fait accompli.

The result is a `SharedFork { embedded, studyrefs, boundaries }` value (the type
sketch below), handed to the chat lane for delivery.

---

## (b) How the recipient ACTS

* **Embedded → local turns.** The guest builds a turn over its embedded caps and
  commits it on the fork. The fork's verified executor applies the IDENTICAL
  conservation / ocap / program guarantees my live world would (`world.rs:581`
  contract). No consent, any number of times. These are *the various things they
  do locally*.

* **Studyref → inspect, exercise = upgrade-request.** The guest opens the
  studyref's slots (`ReadCap::open`) to inspect a cell. If it wants to *exercise*
  (mutate) that cell, it cannot — it holds no write cap. It raises an **upgrade
  request**: a `CapabilityRequest` (`powerbox.rs:62`) for write rights over the
  studyref's target. That routes to me (step (c)) as a powerbox designation. A
  studyref is *a sturdyref you can look at but not pull on without asking.*

* **Networkboundary → exercise opens a consent request.** When the guest attempts
  to exercise a networkboundary cap, the fork does NOT run the turn. It packages
  the intended turn into a `ConditionalTurn` (`conditional.rs:88`) whose
  `condition` is "my grant has arrived", and emits a `ConsentRequest` to me. The
  turn is *pending* — fail-closed: it does nothing until I consent, and expires at
  `timeout_height` if I never do (`is_expired`, `conditional.rs:144`). This is the
  partial-turn-with-a-hole shape: the hole is my consent.

---

## (c) How my CONSENT resolves a request

A consent request reaches me (over the chat lane). I decide:

* **Grant.** I run a real powerbox grant: `Powerbox::grant(world, me, guest,
  target, confer_rights)` (`powerbox.rs:237`). The two real gates fire —
  `mint_needs_held_factory` (I must hold a cap reaching `target`) and
  `gen_conferral_is_attenuation` (`confer_rights ⊆ held`). It mints a fresh
  attenuated `Effect::GrantCapability` and commits it — the executor is the
  authority, I am only the designation UI. The resulting `TurnReceipt` is my
  **signed consent**.

  - For a **studyref upgrade**, the grant mints a write cap into the guest's
    fork c-list (the studyref is promoted to embedded for that target).
  - For a **networkboundary**, the grant becomes the **hole-fill**: it is the
    `ConditionProof` that satisfies the pending `ConditionalTurn`'s
    `ProofCondition`. The condition is a `TurnExecuted { turn_hash }` /
    `LocalProof` over my grant turn — my executor signature on the receipt is the
    consent witness (`resolve_condition`, `conditional.rs:191`; the
    `TurnExecuted` arm verifies the receipt's `executor_signature` against my
    trusted key — *anyone could otherwise fabricate a receipt*). Resolution is
    **one-shot**: the proof nullifier (`used_proof_hashes`) prevents a single
    consent from being replayed to fire the boundary twice — exactly the
    promise-hole-is-a-nullifier insight (partial-turn memory). On `Resolved`, the
    pending turn executes; the boundary fired *once*, with my consent.

* **Deny.** I do nothing, or let the `ConditionalTurn` time out. The pending turn
  **expires** (`ConditionalResult::Expired`) — no state change, fail-closed. The
  guest's boundary exercise simply did not happen; it never reached my real
  world. (Denial is first-class: a powerbox `Denied` outcome, an expired
  conditional, or a refused — over-amplifying — grant all collapse to "the guest
  got nothing".)

The crucial property: a networkboundary exercise is a `ConditionalTurn` whose
`ProofCondition` is the owner's grant. **Resolves on consent, fail-closed
otherwise.** The guest can never elaborate elsewhere without a signed grant of
mine binding the specific turn.

---

## (d) How their local work MERGES back — branch-and-stitch

The guest's embedded turns accumulate as the fork's own history — a divergent
branch of my world. To bring their work back, **branch-and-stitch**
(`docs/deos/BRANCH-AND-STITCH-PROTOCOL.md`, `starbridge-v2/src/branch_stitch.rs`):

* The fork is a `VirtualBranch` confined away from my MAIN frontier
  (`branch_stitch.rs:95`). Its embedded turns are **structurally imaginary** with
  respect to my real cells: the guest holds no debit-reach cap to a main cell
  (`VirtualBranch::confined`, `:121`), so no branch turn can drain my real
  authority. The guest's local work is real *inside the fork*, imaginary *to me*,
  until stitched.

* `Stitch` is the pushout-correct, explicitly-lossy settlement
  (`branch_stitch.rs:271`; `DocGraph::merge` = least-upper-bound, `:233`). The
  I-confluent part of the guest's work merges clean; a genuine conflict is an
  EXPLICIT linear DROP — never a silent conjure.

* The **settlement gate** is the consent boundary at merge time: a stitch may only
  confer authority I held **at the settlement tip** (Settlement Soundness,
  `branch_stitch.rs:38`). The consent-gated turns the guest did inside the fork —
  the networkboundary ones — are exactly the ones whose stitch-back re-checks my
  authority *now*, not at fork time. Authority is read at settlement: a cap I have
  since revoked cannot ride a stitch into my real world.

So: the guest's purely-local (embedded) work stitches as ordinary document merge;
the consent-touching work re-clears the boundary at the settlement tip.

---

## (e) What's REAL-NOW vs roadmap

**Real now (each is live code, cited):**

* **Confinement** — `sandbox.rs`'s `Confinement` (deny-default Seatbelt on macOS /
  Linux LSMs; the endpoint is the only channel) + the firmament cap-tower; the
  fork is a confined sub-world the recipient cannot escape.
* **`World::fork`** — `world.rs:581`, deep-clone ledger + real executor; commits
  on the fork mutate only the fork.
* **Cap attenuation lattice** — `is_attenuation` (`granted ⊆ held`,
  `capability.rs:603`), `is_narrower_or_equal` (`permissions.rs:52`), faceted +
  in-place attenuation, the tombstone revoke.
* **Studyref machinery** — `ReadCap` (`read_cap.rs`): read-lattice `FieldSet`,
  `ViewKey`, `is_read_attenuation`, `open_slot` (decrypt + commitment-bind). A
  studyref IS an attenuated `ReadCap` with no write cap.
* **Powerbox grant-ceremony** — `powerbox.rs`: `CapabilityRequest`,
  `Powerbox::present`/`grant`/`Denied`, `AppLauncher::launch` (the confined
  requester), the two real gates, the executor backstop. The networkboundary
  consent IS this ceremony.
* **Conditional turn / hole-fill** — `conditional.rs`: `ConditionalTurn`,
  `ProofCondition` (incl. `TurnExecuted` with executor-signature verification),
  `resolve_condition`, the proof nullifier (one-shot), timeout/fail-closed. A
  networkboundary exercise is a `ConditionalTurn` whose condition is my grant.
* **Branch-and-stitch** — `branch_stitch.rs`: `VirtualBranch::confined`,
  `admits_debit` (no-drain), `Stitch::settle` (pushout, explicit drop, settlement
  gate). The merge-back path.

**Roadmap (the WIRING this design names; not yet built as one capability):**

* The `SharedFork` value type that *partitions* a culled subgraph into the three
  tiers as a first-class object (the sketch below is the first slice — types +
  the consent-as-conditional-turn shape, compile-checked; the construction/act
  loop is still assembled by hand from the pieces).
* **FINDING — the consent signing domain (must close before the boundary is
  real).** `resolve_condition`'s `TurnExecuted` arm verifies the receipt's
  `executor_signature` against `receipt.receipt_hash()` (`conditional.rs:478`),
  but the embedded executor signs `canonical_executor_signed_message()`
  (`executor/mod.rs:1212`) — a DIFFERENT message. Worse, the `starbridge-v2`
  `World` never configures an executor signing key at all, so its receipts carry
  `executor_signature: None` and the `TurnExecuted` arm would reject them
  outright. So wiring `SharedFork::resolve_consent` to a real `World`-grant
  receipt requires (a) configuring the `World` executor with the owner's signing
  key (`with_executor_signing_key`), AND (b) reconciling the two signing domains —
  either teach the `TurnExecuted` arm to accept `canonical_executor_signed_message`,
  or shape the consent condition as a `LocalProof` over the grant's public inputs
  instead of `TurnExecuted`. The sketch's resolution test exercises the condition
  machinery directly with a domain-matched signed receipt (as `conditional.rs`'s
  own `test_turn_executed_resolved` does), so the one-shot consent shape is proven;
  the `World`-receipt wiring is the gated follow-up.

* A **boundary descriptor** on the fork that intercepts an exercise of a marked
  target and turns it into a `ConsentRequest` + a pending `ConditionalTurn`
  automatically (today the interception is manual — the guest must *choose* to
  raise the request rather than the fork *forcing* it; making the fork's executor
  fail-closed on an un-consented boundary exercise is the genuine new gate).
* The **studyref → upgrade-request** routing as a typed flow (today it is a
  `CapabilityRequest` raised by hand).
* The chat lane's binding of a real recipient key to the guest principal, and the
  delivery of `SharedFork` / `ConsentRequest` / `ConsentGrant` envelopes.

The honest line: **every primitive exists and is proven/tested; the capability is
a WELD, not a build** — the new value is the three-tier graduation typing and the
fail-closed boundary interception, which the sketch begins and the roadmap above
finishes.

---

## (f) First-slice type sketch

`starbridge-v2/src/shared_fork.rs` (compile-checked under `embedded-executor`).
Grounded in the real `dregg_cell` / `dregg_turn` types:

```rust
pub struct SharedFork {
    pub guest: CellId,                    // the confined recipient principal
    pub embedded: Vec<EmbeddedCap>,       // CapabilityRef granted into the fork
    pub studyrefs: Vec<StudyRef>,         // ReadCap (read-only); upgrade needs consent
    pub boundaries: Vec<NetworkBoundary>, // consent-gated; exercise = ConditionalTurn
}
```

The consent flow for a networkboundary is a `ConditionalTurn` whose
`ProofCondition` is the owner's grant (`NetworkBoundary::consent_request` builds
the pending turn; the owner's `Powerbox::grant` receipt resolves it via
`resolve_condition`). See the module for the full shape + tests.
