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
| **STUDYREF** | INSPECT / open the cell's exposed slots — read only | exercise (mutate) needs an **upgrade request** | `ReadCap` (`cell-crypto/src/read_cap.rs`, crate `dregg_cell_crypto`): read-lattice `FieldSet` + `ViewKey`, attenuates via `is_read_attenuation` |
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
   (`cell-crypto/src/read_cap.rs`). The guest can `open_slot` / `open` the exposed slots
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
* **Studyref machinery** — `ReadCap` (`cell-crypto/src/read_cap.rs`, crate `dregg_cell_crypto`): read-lattice `FieldSet`,
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

**Real now (the WIRING this design named, now built + tested):**

* The `SharedFork` value type that *partitions* a culled subgraph into the three
  tiers is a first-class object: `SharedFork::construct` mints the embedded caps
  through real powerbox turns, records the studyrefs + boundaries, and the
  **mint → rehydrate → drive → stitch round-trip** is tested end-to-end
  (`mint_rehydrate_drive_stitch_round_trip`): a live world is forked (the
  snapshot), the in-view subgraph partitioned (docs embedded / peer
  networkboundary), the rehydrated fork holds ONLY the granted subgraph
  (anti-amplification asserted), the guest DRIVES a real turn over its embedded
  cap, and the work STITCHES back via `branch_stitch` — clean where disjoint
  (the pushout/LUB), REFUSED where it would confer authority the owner does not
  hold at the settlement tip (the settlement gate, an over-authorized cap = a
  linear DROP). Each graduated tier is enforced + tested:
  `embedded_tier_is_exercisable_locally_with_no_consent` (drive, no consent),
  `studyref_tier_inspects_but_refuses_exercise_without_an_upgrade` (inspect ok,
  no write cap, exercise = upgrade request), and the networkboundary consent
  tests above.
* The surface-cap-layer membrane (`starbridge-web-surface`) carries the
  per-viewer projection with an **always-on anti-amplification tooth**:
  `Membrane::project` now REFUSES (fail-closed) any projection that fails to
  attenuate BOTH the held authority and the lineage on EVERY axis (window rights
  via the real `is_attenuation`; fetch/navigate/permission sets via `⊆`) — a
  hard gate, not a `debug_assert` (a release build can no longer ship an
  amplified cap). Proven across hops by
  `the_membrane_round_trip_holds_the_anti_amplification_tooth_on_every_hop`.

**Still roadmap (named, with the lane that finishes it):**
* **FINDING — the consent signing domain (CLOSED).** `resolve_condition`'s
  `TurnExecuted` arm verified the receipt's `executor_signature` against
  `receipt.receipt_hash()` (`conditional.rs:478`), but the embedded executor signs
  `canonical_executor_signed_message()` (the `v3` domain,
  `b"executor-receipt-sig-v3:" || receipt_hash`; `turn.rs:1003`) — a DIFFERENT
  message — and the `starbridge-v2` `World` configured no executor signing key, so
  its receipts carried `executor_signature: None`. A real `World`-grant receipt
  therefore could not resolve a `TurnExecuted` consent. **Closed** by: (a)
  `World::with_executor_signing_key` / `set_executor_signing_key` /
  `executor_public_key` (`world.rs`), with `World::fork` carrying the key, so a
  committed receipt is a real signed witness; (b) `SharedFork::resolve_consent`
  now verifies the witness in the executor's OWN signing domain via
  `verify_consent_witness` (`shared_fork.rs`) — applying the IDENTICAL three checks
  the generic arm applies (turn-hash binding to the SPECIFIC grant, signature
  authenticity under a trusted key, the one-shot proof nullifier) but over
  `canonical_executor_signed_message`. The grant turn whose hash the boundary binds
  to is built through the single `Powerbox::grant_turn` constructor (the same turn
  `grant` commits), so the consent binds a SPECIFIC grant. Proven end-to-end:
  `networkboundary_resolves_against_a_real_world_grant_and_fires_once` (a real
  signed grant resolves + fires once), `consent_rejects_a_fabricated_or_untrusted_witness`
  (untrusted key → fail-closed), `consent_rejects_a_witness_bound_to_a_different_grant`
  (binding → fail-closed). The earlier `resolve_condition`-direct keystone test is
  retained as the generic one-shot-shape proof.

* **FINDING — automatic fail-closed boundary interception (CLOSED).** The fork's
  commit path no longer relies on the guest *choosing* to raise a consent request:
  `SharedFork::commit_turn_gated` (`shared_fork.rs`) is the executor-forcing door.
  It classifies the driven turn over the SAME `touched_cells` the live commit path
  uses (`world.rs`); a turn touching NO boundary target passes through to
  `World::commit_turn` (an embedded exercise — or a studyref inspect — runs locally,
  no consent); a turn touching a marked `NetworkBoundary` target is REFUSED,
  fail-closed, UNLESS it is paired with a valid `ConsentWitness` — the owner's signed
  grant receipt, re-verified at the gate by `verify_consent_witness` (the identical
  three teeth: turn-hash binding to the bound grant, signature authenticity under a
  trusted executor key, and the one-shot proof nullifier). On a valid witness the
  consent's hole-fill is a REAL attenuated `Powerbox::grant` of the boundary cap into
  the FORK (owner → guest, at the boundary `ceiling`, so the powerbox's own two gates
  cap it), and only THEN does the consented turn run — the boundary "elaborates here"
  exactly once. With no consent the gate hands back the `ConsentRequest` the owner
  resolves (via the existing `resolve_consent`). **The compulsion is structural:**
  `commit_turn_gated` is the mandatory door, and exercise-without-consent is refused,
  not merely discouraged. Proven by: `gate_refuses_a_boundary_exercise_without_consent_fail_closed`
  (a, the executor never runs the un-consented exercise — fail-closed, not "the guest
  didn't ask"), `gate_admits_the_same_boundary_exercise_after_a_valid_consent` (b, the
  SAME turn commits once a valid signed consent resolves),
  `gate_never_gates_an_embedded_cap_exercise` (c, an embedded exercise is never gated),
  `gate_refuses_a_forged_or_wrong_consent_witness` (d, untrusted-key / wrong-grant /
  wrong-boundary witnesses are each refused), and
  `gate_replay_of_a_consent_fires_the_boundary_only_once` (the one-shot nullifier,
  end-to-end through the gate).
* The **studyref → upgrade-request** routing as a typed flow (today it is a
  `CapabilityRequest` raised by hand).
* The chat lane's binding of a real recipient key to the guest principal, and the
  delivery of `SharedFork` / `ConsentRequest` / `ConsentGrant` envelopes.

The honest line: **the capability is a WELD over proven primitives, and the weld
is now built + tested** — the three-tier graduation typing, the mint → rehydrate
→ drive → stitch round-trip, the consent-signing-domain resolution, and the
always-on anti-amplification tooth are live code with passing tests
(`cargo test -p starbridge-web-surface`; `cd starbridge-v2 && cargo test
--no-default-features --features embedded-executor --lib shared_fork`). The
*automatic* fail-closed boundary interception is now CLOSED too:
`SharedFork::commit_turn_gated` COMPELS consent — a boundary cap cannot reach the
executor without the owner's signed grant; the gate, not the guest's good manners,
is the door. What remains is the chat lane's transport binding (a real recipient
key to the guest principal, delivery of the `SharedFork` / `ConsentRequest` /
`ConsentGrant` envelopes) — named above.

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
