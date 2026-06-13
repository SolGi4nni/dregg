# The `notify` cascade — the full staged plan across the dregg system

*(WIP plan doc. Read-only census + the demo-app design + the execution order. No code or
proof is changed by this doc. The core VK-touching edit is HELD for the cutover-settle —
§Execution Order says exactly what lands now and what lands in the coordinated VK bump.)*

`notify` is a first-class **async-notification authority**: the right to *cause a wake / deliver
a signal* on a target, WITHOUT the rights to read its state, send it a synchronous message, or
receive its replies. It is the asynchronous dual of the synchronous endpoint `call`/`write` — a
fourth **Synchrony** dial (sync turn ↔ async signal), sibling to the single-machine *Agreement*
dial. The design and the census of where async-signal already lives ungated are in
`docs/NOTIFY-PRIMITIVE.md`; the seL4-grounding rationale and the ~9-site core ripple are in
`metatheory/docs/rebuild/AUTHORITY-DIVERGENCE-FINDING.md`. This doc is the *cascade*: every layer
`notify` must reach, each site classified, the demo app, and the order the pieces land in.

---

## The hard constraint that shapes the whole plan (read first)

The felt-encoders and the VK bump touch the **circuit**, which is mid-cutover-churn: the C3
fork-surgery grinds the circuit toward v1-deletion and the rotation train already bumps the VK.
**Two simultaneous VK bumps would break the verifier contract** (the cell-commitment ↔ circuit ↔
verifier triangle must agree on one VK at a time). Therefore the VK-touching core of `notify`
lands as **one coordinated VK bump at the cutover-settle**, not into the churning circuit. Every
site below is classified into one of three lanes:

| lane | meaning | when |
|---|---|---|
| **WIDE-SAFE-NOW** | touches no felt-encoder / no VK / no live `Auth` ctor — read-only-concurrent with the cutover churn | proceeds immediately, beside other lanes |
| **GATED-ON-STEP-1** | depends on the firmament-local `NotifyAuthority` reference landing first (it has — see §Step-1) but still touches no VK | after Step 1 is committed |
| **VK-BUMP-AT-SETTLE** | touches a felt-encoder, the cap-leaf digest, the verifier, or the live `Auth`/`FullActionA` enum ⇒ a VK/encoding bump | the single coordinated batch at cutover-settle, Rust + Lean moving together |

The discipline is `STAGED-ADDITIVE-THEN-CUTOVER`: the wide-safe theory and the demo are built
and validated *beside* the live path; the VK cutover is a separate, deliberate, atomic act.

---

## Step 1 is DONE — the validated reference exists

`metatheory/Dregg2/Firmament/NotifyAuthority.lean` (≈510 lines, axiom-clean, `#assert_all_clean`
over 18 keystones, `#guard` teeth both polarities) is **already built and green** (local). It is
the transfer triangle of this design: the cap-algebra on async-signal as a theorem, touching no
core `Auth`, no felt-encoder, no VK. What it establishes (the reference the rest of the cascade
amplifies onto):

- **`NotifyCap { target : ObjId, rights : AuthReq, badgeMask : Nat }`** (`NotifyAuthority.lean:168`)
  — the held right to WAKE `target`, scoped to badges within `badgeMask`. `rights` is the EXISTING
  `AuthReq` tier lattice (the Rust `AuthRequired` mirror, `CapTPConcrete.lean:47`); the `badgeMask`
  is the new payload-scope sub-lattice.
- **The badge mask IS `facetAttenuation`** (`NotifyAuthority.lean:102`) — the same `u32`-mask
  bit-subset `(child &&& parent) == child` the captp handoff validator already runs
  (`CapTPConcrete.lean:146`), completed to a genuine partial order (`maskNarrowerOrEqual` reflexive
  / antisymmetric / transitive, `0` ⊥). **No new lattice** — two existing orders instantiated on a
  notification cap.
- **`signalGated cap n badge`** (`NotifyAuthority.lean:205`) — the cap-gated WRAPPER over the
  existing `SeL4Kernel.Notification.signal` badge-OR accumulator. Commits (OR's the masked badge)
  iff the badge is within the held mask; refuses (`none`) otherwise — fail-closed, both `#guard`'d.
- **Non-amplification keystone** `signalAdmissible_attenuate_no_amplify` (`:273`): a badge
  admissible through an ATTENUATED (narrower-mask) cap is admissible through the original — attenuation
  only SHRINKS the admissible badge set. `attenuateNotify` (`:190`) narrows BOTH axes (rights via the
  reused `grantOk`, mask via `maskNarrowerOrEqual`); a widening on either is REFUSED.
- **seL4-faithful well-formedness** `notificationCap_confers_at_most_notify_read` (`:331`): a
  notification cap confers at most `{Reset, Receive, Notify}` — never `{Grant, Call, Reply}` — the
  `SeL4Abstract.lean:225` strip as a dregg fact. `Notify` is a DISTINCT ctor from `SyncSend`/`Call`/
  `Reply` (`notify_distinct_from_sync`, `:384`), so the async wake is genuinely separate from the sync
  write.

Everything classified **GATED-ON-STEP-1** below can now proceed; the demo app (§Demo) runs on this
module ALONE.

---

## Layer 1 — LEAN SEMANTICS

### 1a. The core `Auth.notify` constructor + its ripple — VK-BUMP-AT-SETTLE

The investigation's ~9-site list is **confirmed exactly** by this census. The core edit adds
`notify` to `inductive Auth` (`Authority/Positional.lean:38`, currently
`| read | write | grant | call | reply | reset | control`). The ripple, every site verified present:

| # | site | file:line | edit | lane |
|---|---|---|---|---|
| 1 | felt-encoder `authCode` | `Circuit/Witness/SpawnWitness.lean:77` | `\| .notify => 7` arm | VK-BUMP-AT-SETTLE |
| 2 | felt-encoder `authCode` | `Circuit/Witness/DelegateWitness.lean:100` | `\| .notify => 7` arm | VK-BUMP-AT-SETTLE |
| 3 | felt-encoder `authCode` | `Circuit/Witness/RefreshDelegationWitness.lean:73` | `\| .notify => 7` arm | VK-BUMP-AT-SETTLE |
| 4 | felt-encoder `authCode` | `Circuit/Witness/RevokeDelegationWitness.lean:97` | `\| .notify => 7` arm | VK-BUMP-AT-SETTLE |
| 5 | felt-encoder `authCode` | `Circuit/Witness/attenuateAWitness.lean:44` | `\| .notify => 7` arm | VK-BUMP-AT-SETTLE |
| 6 | FFI `authTag` / `authOfTag` | `Exec/FFI.lean:429`/`:434` | `\| .notify => 7` (+ decode `7 => some .notify`) + matching Rust marshaller | VK-BUMP-AT-SETTLE |
| 7 | `Fintype Auth` `elems` | `Exec/Caps.lean:54` | add `Auth.notify` to the set; `complete` re-`decide`s | WIDE-SAFE-NOW* |
| 8 | `toString`/display | `Widget/DreggForest.lean:60` | `\| .notify => "notify"` arm | WIDE-SAFE-NOW |

The five `authCode` defs are byte-identical (`| .read => 0 | .write => 1 | … | .control => 6`); each
gets one `| .notify => 7` arm and emits a column value `7` the circuit and the Rust marshaller must
agree on — **that agreement is the VK/encoding bump**. (`DelegateAttenWitness.lean` has NO `authCode`
of its own; it reuses one of the five — so the count is five, not six.) The FFI `authTag` (note: the
investigation called it `authCode`; in `Exec/FFI.lean` it is `authTag`/`authOfTag`, the 0..6 wire
codec) needs the new tag AND its Rust counterpart, so it is firmly in the VK batch.

`*` The `Fintype` and `toString` arms are technically VK-independent (they don't emit a felt), but
because `Auth.notify` cannot exist until the enum is edited, they MOVE WITH the core edit in
practice — there is no `Auth.notify` to enumerate before then. They are listed as "wide-safe in
isolation" only to mark that they carry zero proof restructuring.

**Proofs: the constructor-agnostic claim is CONFIRMED (zero restructuring).** `attenuate`
(`Caps.lean`, a `List.filter` on `keep`), `capAuthConferred` (`Positional.lean:66`, returns the
rights list verbatim), `confRights` (`Caps.lean`, `.toFinset` of that list), and every
`attenuate_subset` / `attenuate_non_amplifying` / `authNarrowerOrEqual` proof are `List.Subset` /
membership facts — invariant under adding a ctor. Every `Fintype.complete` and `cases a <;> …`
re-closes under `decide`/`simp` with the new arm. The only genuinely-new proof work is **extending
α** (next).

### 1b. The seL4 grounding: α-totalization — VK-BUMP-AT-SETTLE (Lean-only, but moves with 1a)

`SeL4Abstract.alpha` (`SeL4Abstract.lean:451`) maps the 7 used seL4 auths onto dregg's `Auth`, with
`Notify ↦ none` at `:459` (the one IPC ctor going to `none`; `Read`/`Write`/`DeleteDerived`/`AAuth`
go to `none` as *principled* projections per the divergence finding). The edit:

- `| .Notify => some .notify` replaces `| .Notify => none` (`:459`);
- add `.notify` to `usedAuth` (`:467`) — it becomes the 8th used auth;
- `alpha_total_iff_used` (`:473`, `cases a <;> simp`) and `alpha_injective_on_used` (`:479`,
  `fin_cases <;> simp_all`) re-close automatically;
- `dregg_executor_cap_authority_grounded_in_seL4` (`:547`) then covers the firmament's FULL IPC +
  notification authority — α total on all 7 seL4 IPC authorities (`Receive, SyncSend, Notify, Reset,
  Grant, Call, Reply`), the divergence finding's named payoff: the one genuine IPC conflation closed.

This touches no felt-encoder, so it is VK-independent in isolation — but it references `Auth.notify`,
which only exists after 1a, so it lands in the same batch. The Step-1 module's well-formedness
theorems (`notificationCap_confers_at_most_notify_read` et al.) ALREADY operate over the transcribed
12-ctor `SeL4Abstract.Auth` (which already has `.Notify`/`.Receive`), so they need NO change — they
were written to be exactly the dregg fact this α-totalization grounds.

### 1c. The firmament: `NotifyCap` as a Target/Rights in `CapGradation` — GATED-ON-STEP-1

Step 1 lives firmament-locally and reuses `grantOk` (`CapGradation`, = `authNarrowerOrEqual granted
held`, the Rust `is_attenuation`). Lifting `NotifyCap` into the `CapGradation` mint discipline (so a
notify cap is minted/attenuated through the SAME `mint`/`grantOk` gate as an endpoint cap, with the
badge-mask as an additional `granted ⊆ held` leg) is **additive and VK-free** — it is the natural
follow-on to Step 1 and needs no core `Auth` edit. Classify GATED-ON-STEP-1. (A fuller "the
Notification object is a first-class `CapGradation` Target" weld is the §Step-3 organ work.)

### 1d. The EFFECT system: cap-only, OR a `signalA` effect? — the fork that decides a SECOND VK bump

This is the load-bearing modelling call, and the census makes it sharp. The executable effect enum
is `FullActionA` (`Exec/TurnExecutorFull.lean:1998`) — ~20 constructors mirroring dregg1's `apply.rs`
ops (`balanceA`, `delegateAttenA`, `attenuateA`, `setFieldA`, `createCellA`, `exerciseA`, …). **There
is no `signalA`/`notifyA` effect today.** Two faithful paths:

- **(A) CAP-ONLY (the Step-1 path, RECOMMENDED for the first cut).** `notify` is an *authority*, and
  a `signal` is modelled as an ordinary `setFieldA` that writes the target's badge-accumulator field
  (balance-neutral, exactly like the inbox `deliver` is a `SetField`, `InboxFactory.lean:29`), GATED
  by the holder's `NotifyCap` via `signalGated`. **No new `FullActionA` ctor, no new EffectVm
  descriptor, no extra VK bump** beyond the 1a authority-code bump. The badge-mask rides the cap leaf
  (next paragraph). This is what Step 1 already proves and what the demo runs on.
- **(B) FIRST-CLASS `signalA` EFFECT (a later enrichment).** Add `| signalA (actor target : CellId)
  (badge : Int)` to `FullActionA`, with its own EffectVm wide-descriptor
  (`EffectVmEmitSignal…`, mirroring the `EffectVmEmit*` family at `Circuit/Emit/`) and the
  `descriptor_agrees_with_executor` soundness theorem. This is a SECOND, SEPARATE VK bump (a new
  effect column) — explicitly deferred past the authority-code bump. The discipline (`signal`/`wait`
  are each ordinary turns; the async-ness is the GAP between them, `NOTIFY-PRIMITIVE.md` §3.4) holds
  either way.

**The cap-leaf encoding (where the badge-mask lives) — VK-BUMP-AT-SETTLE, but cheap.** The cap-root
leaf (`circuit/src/cap_root.rs:94` `CapLeaf`) ALREADY carries `mask_lo`/`mask_hi` — an `EffectMask`
(u32) split low-16/high-16, folded into the 7-field Poseidon2 leaf digest (`:115`). The notify
badge-mask is the SAME shape. Two sub-options, both a one-field encoding change ⇒ a VK bump:
  - reuse the existing `mask_lo`/`mask_hi` field as the badge-mask when the cap's `auth_tag` indicates
    a notification cap (no new leaf field, but a semantic overload on the mask), or
  - add a parallel `badge_mask_lo`/`badge_mask_hi` pair to `CapLeaf` (an 8th/9th leaf field, the
    cleanest, but it changes the leaf arity ⇒ a larger VK bump).

Either way the leaf-digest change is a felt-level encoding bump, so it joins the cutover-settle batch.
The RECOMMENDATION: **path (A) + reuse the existing effect-mask field for the badge-mask** for the
first cut (smallest VK delta), with the parallel-field and first-class-`signalA` enrichments as named
later waves.

### 1e. The organs (the WELD) — GATED-ON-STEP-1 (Lean modelling) + VK-free

The point of `notify` is that it names the authority three ungated wake mechanisms + two ambient
delivery surfaces already need (`NOTIFY-PRIMITIVE.md` §1, file:lines verbatim):

| organ | the ungated wake (file:line) | current "may signal" authority | notify weld |
|---|---|---|---|
| mailbox / CapInbox | `Apps/InboxFactory.lean:183` deliver gate; Rust `node/src/relay_service.rs` HTTP-poll drain (owner Ed25519 sig) | sender-set membership / owner-equality | deliver becomes a held `NotifyCap` (gated by the sender's cap, not the frozen sender-set); consume stays owner |
| pubsub / channels | `Apps/PubsubFactory.lean:157` publish gate; Rust `node/src/channels_service.rs:300` `broadcast` send (UNGATED), `:1061` no-auth SSE | frozen publisher slot / ungated broadcast | publish becomes a held `NotifyCap`; the SSE wake becomes cap-gated (a subscriber receives the `(channel, seq)` wake iff it holds a `notify`-watch cap over the topic) |
| WorldEvent dynamics | `starbridge-v2/src/dynamics.rs:111` `emit` (ambient), `:122` `since` (poll) | none (ambient) | producing an event requires holding `notify` over the event's subject; `since` visibility gated on a watch cap |
| blocklace finality | `node/src/blocklace_sync.rs:107` `finality_notify: Arc<Notify>`, `notify_one()` `:329/:363/:1504`, `.notified()` `:1860` | in-process condvar (ungated) | in-process only — no cross-boundary cap needed; modelled as the canonical Notification the others refine |
| cross-agent `--wake` | buildr `~/pug/.../herdr/src/cli.rs:2189` (non-blocking spool post) | none (and currently mis-modeled as a SYNC joint turn, `Apps/AgentOrchestration.lean`) | re-expressed as a cap-gated async `signal` (the demo, §Demo) — composes with, does not replace, the synchronous `JointTurn` |

The **Lean modelling** of these welds (re-expressing `InboxFactory.deliver` / `PubsubFactory.publish`
gates to route through a `NotifyCap` instead of membership/slot) is additive, VK-free, and
GATED-ON-STEP-1. The **Rust** side (gate the channels `broadcast`, the dynamics `emit`, the relay
drain) is §Layer-3 organ work — a separate wave per organ (`W-organ-*`), and only the parts that
change the on-wire authority encoding touch the VK.

---

## Layer 2 — PROOFS

**The constructor-agnostic claim is CONFIRMED (see 1a).** The attenuation/non-amplification core
(`attenuate`, `capAuthConferred`, `confRights`, `attenuate_subset`, `attenuate_non_amplifying`,
`authNarrowerOrEqual_*`) is `List.Subset`/membership and is INVARIANT under adding `Auth.notify` —
**zero proof restructuring**. The proofs that genuinely need work, exhaustively:

| proof | file:line | why it needs touching | lane |
|---|---|---|---|
| `alpha_total_iff_used` | `SeL4Abstract.lean:473` | `.notify` joins `usedAuth`; re-`cases`/`simp` (mechanical) | VK-BUMP-AT-SETTLE (Lean) |
| `alpha_injective_on_used` | `SeL4Abstract.lean:479` | new used ctor; `fin_cases <;> simp_all` re-closes | VK-BUMP-AT-SETTLE (Lean) |
| `dregg_executor_cap_authority_grounded_in_seL4` | `SeL4Abstract.lean:547` | statement unchanged; benefits (α now total on IPC) — re-checks under the new α | VK-BUMP-AT-SETTLE (Lean) |
| the 5 `authCode`-bearing witness soundness lemmas | `Circuit/Witness/*Witness.lean` | the felt-encoder gained an arm; the `r.map authCode` image lemmas re-`decide` over the new code `7` | VK-BUMP-AT-SETTLE |
| Step-1 keystones | `NotifyAuthority.lean` | NONE — already written against the 12-ctor `SeL4Abstract.Auth`; they are the target the α-totalization grounds | already done |

No proof is BROKEN by `notify`; the work is (a) mechanical re-closure where the enum is `cases`'d, and
(b) the genuinely-new but small α-totalization. Everything else is invariant.

---

## Layer 3 — RUST IMPL

**Crucial framing: the Rust authority model is NOT the Lean `Auth` enum.** dregg's Rust side has TWO
authority namespaces, and `notify` interacts with neither the way the investigation's enum-arm count
might suggest:

- **`AuthRequired`** (`cell/src/permissions.rs:5`) — the per-action/per-cap *tier* lattice
  (`None`/`Signature`/`Proof`/`Either`/`Impossible`/`Custom{vk_hash}`), tier-encoded `None=0…Custom=5`
  (`cell/src/factory.rs:208`), folded into the cap-leaf `auth_tag` felt
  (`cell/src/commitment.rs:520` `auth_required_to_tag`) and the per-cell authority digest
  (`commitment.rs:742` `compute_authority_digest_felt`, the 8 `Permissions` fields). This is the
  `rights : AuthReq` field of `NotifyCap` (the Lean `CapTPConcrete.AuthReq` mirrors it exactly). **A
  notify cap's RIGHTS ride this lattice unchanged** — `notify` does NOT add an `AuthRequired` tier.
- **`Authorization`** (`turn/src/action.rs:221`) — the *provided* credential discriminator
  (`Signature`/`Proof`/`Breadstuff`/`Bearer`/`CapTpDelivered`/`Custom`/`AnyOf`/`Unchecked`). The "who
  is acting / how is it authorized" carrier. `notify` does NOT add an `Authorization` variant either
  — a `signal` is authorized the SAME way any effect is (signature/proof/bearer over the cap).

So what `notify` actually changes on the Rust side is **the badge-mask on the cap, the gate that
checks it, and (path B only) a new effect**. Per site:

| # | Rust site | file:line | what changes | lane |
|---|---|---|---|---|
| R1 | the cap-leaf `CapLeaf` (badge-mask field) | `circuit/src/cap_root.rs:94` (`mask_lo`/`mask_hi` `:102`, `digest` `:115`) | encode the badge-mask (reuse the effect-mask field, or add a parallel `badge_mask_*` pair) — a leaf-digest encoding change | VK-BUMP-AT-SETTLE |
| R2 | `auth_required_to_tag` / cap-leaf builder | `cell/src/commitment.rs:520`, `cap_root.rs:551` | if the badge-mask is a NEW leaf field, build it here from the cap; if it reuses the effect-mask, no change | VK-BUMP-AT-SETTLE (R1-coupled) |
| R3 | the in-circuit cap gate (the signal admissibility check) | `circuit/src/effect_vm_p3_full_air.rs` (the `auth_tag`/mask columns, `:255`, `:1963`) | a `signalGated` analogue: a signalled badge must be within the leaf's badge-mask (the in-circuit `badge &&& ¬mask == 0` gate) — only on path B, or as a Phase-B cap-gate | VK-BUMP-AT-SETTLE |
| R4 | the verifier | `verifier/src/` (the VK/public-input contract) | re-pin the VK after R1/R3 change the leaf digest / add a column — the single coordinated VK bump | VK-BUMP-AT-SETTLE |
| R5 | the FFI `authTag` Rust marshaller | the Rust counterpart of `Exec/FFI.lean:430` (the 0..6 → 0..7 wire codec) | add the `notify => 7` wire tag mirroring the Lean side | VK-BUMP-AT-SETTLE |
| R6 | `Authorization::to_auth_kind` / the auth-tag plumbing | `turn/src/action.rs:547`, `turn/src/lean_shadow.rs:1568` `auth_to_wire` | no change for path A (notify rides existing auth kinds); path B threads the new effect's auth through | (path B) VK-BUMP-AT-SETTLE |
| R7 | (path B only) a `Effect::Signal` / `signalA` effect | `cell/src/effect_vm/effect.rs:73` (`Effect`), `turn/src/action.rs:800` (`Effect`), the executor `apply_*` | a new effect variant + its EffectVm AIR — a SECOND VK bump, deferred | DEFERRED (separate VK bump) |

**The smallest Rust cut** (matching Lean path A + effect-mask reuse): R1 (badge-mask = the existing
effect-mask field, semantically) + R4 (VK re-pin) + R5 (the FFI tag), with R3 as a Phase-B in-circuit
gate. The organ welds (gate `channels_service.rs:300` `push_message`, `dynamics.rs:111` `emit`,
`relay_service.rs` drain on a held notify cap) are the §Layer-5 / §Step-3 application-level waves —
they change *who may call the wake*, enforced at the node/service layer, and only touch the VK if they
change the on-chain cap encoding.

---

## Layer 4 — SDK

**Census: there is NO `notify`/`signal`/`wake` client method today.** The SDK (`sdk/src/`) surfaces
async delivery as *ambient subscription*, never as a held wake-cap:

| surface | file:line | current model | notify API to add |
|---|---|---|---|
| channels | `sdk/src/channels.rs:204` `subscribe()` (returns a `broadcast::Receiver`), `:300` `push_message` (ungated wake) | post = cryptographic (AEAD under group key); subscribe = ungated | a `Channel::notify(badge)` that exercises a held `NotifyCap`; `subscribe` gated on a watch cap |
| mailbox | `sdk/src/mailbox.rs:364` `grant_sender()` (executor-gated sender-set write), `:389` `sender_authorized()` (membership gate) | deliver = sender-set membership; drain = owner Ed25519 sig | `Mailbox::signal(target, badge)` under a held `NotifyCap` instead of sender-set membership |
| events | `sdk/src/events.rs:79` `NodeEvents::subscribe()` → `ReceiptStream` (ambient, reconnect via `Last-Event-ID`) | ambient broadcast, server-side `ReceiptFilter` only | a `notify`-watch handle so an event subscription is a held cap, not ambient |

**The notify SDK API design (WIDE-SAFE-NOW — pure surface design, no VK):**

- **`NotifyCapHandle`** — the client-side handle for a held `NotifyCap` (target cell + rights tier +
  badge-mask), the SDK mirror of the Lean `NotifyCap`. Obtained by delegation (the coordinator
  attenuates its own notify cap and hands the worker a `NotifyCapHandle` with a narrower badge-mask).
- **`fn signal(&self, badge: u64) -> Result<CommittedTurn>`** on `NotifyCapHandle` — the wake. The
  badge must be within the handle's mask (client-side pre-check mirroring `signalGated`; the executor
  re-checks). Returns the committed turn that OR'd the badge into the target's accumulator.
- **`fn attenuate(&self, narrower_rights, narrower_mask) -> Option<NotifyCapHandle>`** — the
  client-side `attenuateNotify`: narrow BOTH axes, `None` if either would amplify. The sub-delegation
  primitive (hand a sub-coordinator "wake for kind K only").
- **`fn watch(&self, target) -> SignalStream`** — the receive side: subscribe to a target's
  badge-`wait` accumulator; yields the OR'd badge each time it advances. The dual of `signal` (no
  authority needed to receive your OWN signal — the §2.3 asymmetry).

The API design and types are pure surface (no felt, no VK) ⇒ **WIDE-SAFE-NOW**. The *wiring* of
`signal` to a real on-chain badge-mask gate is GATED-ON-STEP-1 (Lean reference) and ultimately on the
VK bump (the cap-leaf badge-mask). `sdk-ts` (`sdk-ts/src/`) has the parallel surface (`mailbox.ts`,
`events.ts`, `client.ts`) and gets the matching TS `NotifyCapHandle` + `signal`/`watch` — also
WIDE-SAFE-NOW as a design.

---

## Layer 5 — APPS

### Existing apps that gain a notify feature (the census verdict)

| app | file:line (the gate) | async mechanism today | notify feature |
|---|---|---|---|
| `InboxFactory` | `Apps/InboxFactory.lean:183` deliver / `:191` consume | sequenced slots; deliver = sender-set membership | deliver becomes a held `NotifyCap` (gated by the sender's cap, not the frozen sender-set); the relational no-overflow caveats stay |
| `PubsubFactory` | `Apps/PubsubFactory.lean:157` publish / `:166` read | shared head + per-reader cursors; publish = frozen `publisher` slot | publish becomes a held `NotifyCap`; readers stay cursor-based (no cap) |
| `QueueFactory` | enqueue gate `~:199` | bounded FIFO; enqueue = sender membership | enqueue becomes a held `NotifyCap`; dequeue stays owner; capacity bounds orthogonal |
| `Subscription`/`SubscriptionGated` | consume op `~:62` | abstract automaton / MonotonicSequence on the seq slot | inherits the queue's notify feature; the gated layer is execution, not a new design point |
| `BountyBoardGated` | claim/cancel `~:161` | escrow states; sync claim | COULD extend: a poster `signal`s claimants (async wake) that a bounty opened, under a scoped notify cap |
| `AgentOrchestration` | worker spawn `~:104`, dispatch via `execFullForestA` `~:379` | SYNCHRONOUS joint-turn forest (root + workers commit atomically) | the demo's foil — see below; it is sync today, the demo adds the async edge |

`ToolAccessDelegation` (rate/deadline/scope mandate cell), `ChannelGroup` (key-epoch state machine),
and `NameserviceGated` (metadata registry) do NOT gain from `notify` — they are synchronous control/
registry cells, no async wake. (Verified by reading each gate.)

**`AgentOrchestration` is the key foil.** It already models a coordinator/worker swarm, but
dispatch is a SYNCHRONOUS joint-turn (root + delegated workers in ONE `execFullForestA`, all-or-
nothing). It has NO async wake — exactly the `--wake` the metatheory lacks
(`NOTIFY-PRIMITIVE.md` §1.7). The demo is its async sibling, not a rewrite of it.

### THE DEMO APP — `Dregg2/Apps/SwarmSignal.lean` (the verified async swarm-signal coordinator)

**The strongest demonstration: a coordinator-agent NOTIFIES worker-agents under ATTENUATED,
badge-masked notify caps — the verified async `--wake` the metatheory previously lacked.** A worker
may be poked by its coordinator on badge X but cannot signal back, cannot read coordinator state, and
cannot widen its badge or poke a peer it lacks the cap for. This is the ADOS A2 async layer made
verified.

**It runs on Step 1's `NotifyAuthority` ALONE — WIDE-SAFE-NOW.** This is the early-demo version, by
design: it uses `NotifyCap` / `signalGated` / `attenuateNotify` directly (no core `Auth.notify`, no
felt-encoder, no VK). It demonstrates the cap algebra as a runnable, `#guard`-tested app without
waiting for the cutover-settle. (A later "deep" version, after the VK bump, expresses the same app
through the core `Auth.notify` + a first-class `signalA` effect on the gated executor — but the demo's
*teeth* are all present in the Step-1-only version.)

**The cells:**
- **`coordinator`** (cell 0) — holds the root `NotifyCap` over each worker, with a WIDE badge-mask
  (all task-kind bits, e.g. `0b111`).
- **`workerA`, `workerB`** (cells 1, 2) — each is a Notification object (a badge-OR accumulator,
  `SeL4Kernel.Notification`) the coordinator may signal. Each worker holds, at most, a `watch` on its
  OWN accumulator (the §2.3 asymmetry: receiving your own signal needs no authority).
- a **`subCoordinator`** (cell 3) — to whom the coordinator sub-delegates "wake workerA for task-kind
  K only" (an attenuated notify cap, mask `0b001`), demonstrating the delegation chain.

**The notify caps + badges (the badge = which event/task-kind):**
- `coord→workerA`: `NotifyCap { target := workerA, rights := .signature, badgeMask := 0b111 }` — may
  wake workerA for any of three task kinds (bits `0b001`=compile, `0b010`=test, `0b100`=deploy).
- `coord→workerB`: same shape, `target := workerB`.
- `subCoord→workerA`: `attenuateNotify (coord→workerA) .signature 0b001` — `some` (a narrowing), the
  sub-coordinator may wake workerA for `compile` (`0b001`) ONLY.

**The gate-teeth it demonstrates (each a `#guard`, both polarities, mirroring `NotifyAuthority.lean`
§5):**
1. **Coordinator wakes workerA on a held badge** → `signalGated (coord→workerA) workerA.accum 0b010`
   is `some` (commits, OR's `0b010` into workerA's accumulator). The worker `wait`s and sees `0b010`.
2. **A worker cannot widen its badge** → `(subCoord→workerA).attenuateNotify _ 0b111` is `none` (the
   sub-coordinator holds mask `0b001`; widening to `0b111` is REFUSED) —
   `attenuateNotify_refuses_mask_widening`.
3. **A worker cannot poke a peer it lacks the cap for** → the sub-coordinator has NO cap over workerB,
   so there is no `signalGated (subCoord→workerB) …` that commits (it must construct a cap it does not
   hold; the demo shows the only caps in scope, and none target workerB from subCoord).
4. **A worker cannot signal back / read coordinator state** → workerA holds only a `watch` on its own
   accumulator; it has no `NotifyCap` whose target is `coordinator`, so `signalGated _ coordinator.accum
   …` is unconstructible from workerA's caps. (The `notify`-confers-at-most-`{notify,read}` well-
   formedness, `notificationCap_confers_at_most_notify_read`, is the proof this is structural, not
   incidental.)
5. **An out-of-mask signal is refused** → `signalGated (subCoord→workerA) workerA.accum 0b010` is
   `none` (subCoord's mask is `0b001`; `0b010` is outside) — `signalGated_refuses_of_inadmissible`.
6. **Attenuation strictly shrinks** → the sub-coordinator admits `0b001` but the coordinator admits
   `{0b001, 0b010, 0b100}`; the keystone `signalAdmissible_attenuate_no_amplify` proves every badge the
   sub-coordinator can signal, the coordinator could too.

**The app structure** (matching the Gated-app template, `Apps/NameserviceGated.lean`): domain defs
(cell ids, the badge-kind bits) → the `NotifyCap` constellation (coordinator's caps + the attenuated
sub-delegation) → the gated wake as a `signalGated` over each worker's `Notification` → the `#guard`
teeth above (both polarities) → conservation (every wake is balance-neutral — it writes a badge
accumulator, not the ledger) → `#assert_all_clean` over the keystones. Because it reuses Step 1's
proven `signalGated`/`attenuateNotify` verbatim, the app's own proof burden is the *witnesses* (the
concrete `#guard`s on the named cells), not re-proving the algebra.

**The alternative (also WIDE-SAFE-NOW): an event-driven pub-sub demo.** Publishers `signal`
subscribers under attenuated notify caps — a `publisher` holds `NotifyCap { target := topic,
badgeMask := topic-kinds }`, a `subscriber` holds a `watch`, and `attenuateNotify` hands a
restricted-topic publisher "may publish kind K only". This maps directly onto `PubsubFactory.lean`
(replacing the frozen `publisher` slot with a held cap) and gates the Rust `channels_service.rs:300`
broadcast. It demonstrates the same teeth (can't widen the topic-mask, can't publish a kind not held)
in the pub-sub idiom. The swarm-signal coordinator is the RECOMMENDED primary demo (it directly
answers the ADOS `--wake` wedge and is the most legible "verified async coordination" story); the
pub-sub app is the natural second demo and the bridge to the channels organ weld.

---

## Execution order — what lands now, what lands in the cutover-settle VK bump

### Lands NOW (WIDE-SAFE / GATED-ON-STEP-1, concurrent with the cutover churn)

1. **Step 1** — `Dregg2/Firmament/NotifyAuthority.lean`. **DONE** (axiom-clean, green local). The
   validated reference.
2. **The demo app** — `Dregg2/Apps/SwarmSignal.lean` on `NotifyAuthority` alone (GATED-ON-STEP-1).
   The verified async swarm-signal coordinator + its `#guard` teeth. The early, legible demonstration.
   Optionally the pub-sub event-driven demo as a second app.
3. **The SDK notify API DESIGN** — `NotifyCapHandle` + `signal`/`attenuate`/`watch` surface in
   `sdk/src/` (and the `sdk-ts` mirror). Types and signatures only (WIDE-SAFE-NOW); the on-chain
   wiring waits for the VK bump.
4. **The firmament `CapGradation` lift** of `NotifyCap` (1c) and the **organ Lean modelling** (1e):
   re-express the `InboxFactory.deliver` / `PubsubFactory.publish` gates to route through a
   `NotifyCap`. Additive, VK-free, GATED-ON-STEP-1.
5. **The `toString` arm** (`DreggForest.lean:60`) and the `Fintype` `elems` (`Caps.lean:54`) are
   VK-independent in isolation — but since `Auth.notify` does not exist until the core edit, they
   travel WITH batch (6) in practice.

### Lands AT THE CUTOVER-SETTLE (the single coordinated VK bump — Rust + Lean together)

6. **The core `Auth.notify` constructor** (`Authority/Positional.lean:38`) + the 5 felt-encoder arms
   (`Circuit/Witness/{Spawn,Delegate,RefreshDelegation,RevokeDelegation,attenuateA}Witness.lean`,
   `| .notify => 7`) + the FFI `authTag`/`authOfTag` (`Exec/FFI.lean:430`) + its Rust marshaller +
   the `Fintype`/`toString` arms. **One atomic enum-plus-encoding bump.**
7. **The α-totalization** (`SeL4Abstract.lean:459` `Notify ↦ some .notify`, `:467` `usedAuth`,
   re-close `:473`/`:479`/`:547`). Lean-only, but references `Auth.notify` so it ships in (6)'s batch —
   delivers the grounding payoff (α total on all 7 seL4 IPC authorities).
8. **The Rust cap-leaf badge-mask** (`circuit/src/cap_root.rs:94` `CapLeaf` — reuse `mask_lo`/`mask_hi`
   for the badge-mask, the smallest delta) + the in-circuit signal-admissibility gate
   (`effect_vm_p3_full_air.rs`, Phase-B) + **the verifier VK re-pin** (`verifier/src/`). This is the
   payload that makes the bump a VK bump; it MUST be the only VK change in flight (the rotation/C3
   churn must have settled first).
9. **The differential** — kernel (Lean) ↔ NEW Rust over the badge-mask cap, before cutover (the
   `STAGED-ADDITIVE-THEN-CUTOVER` validation that the two agree byte-for-byte on the new leaf).

### Lands LATER (named follow-on waves, each its own VK bump or organ weld)

10. **The first-class `signalA` effect** (path B): `| signalA … ` on `FullActionA`
    (`TurnExecutorFull.lean:1998`) + `Effect::Signal` on the Rust `Effect` enums
    (`effect_vm/effect.rs:73`, `action.rs:800`) + a new `EffectVmEmitSignal` wide-descriptor +
    `descriptor_agrees_with_executor`. A SEPARATE, second VK bump — deferred past the authority-code
    bump.
11. **The Rust organ welds** (`W-organ-*`): gate `channels_service.rs:300` `push_message` / the SSE on
    a watch cap, `dynamics.rs:111` `emit` on a notify cap, the relay drain — each a wave, reachable
    from the shell, touching the VK only where it changes the on-chain cap encoding.
12. **The parallel `badge_mask_lo`/`badge_mask_hi` leaf field** (the cleaner alternative to reusing the
    effect-mask), if the effect-mask overload proves cramped — another leaf-arity VK bump.

---

## The honest staging rationale + the one risk carried forward

**Why stage at all.** The VK is a single shared contract across the cell-commitment, the circuit, and
the verifier. The circuit is mid-cutover-churn (C3 fork-surgery toward v1-deletion; the rotation train
already bumps the VK). Landing the `notify` felt-encoders + cap-leaf change INTO that churn would put
two simultaneous VK bumps in flight, and the verifier can only honor one VK at a time — the contract
would break. So the VK-touching core (the `Auth.notify` ctor, the felt-encoders, the α-totalization
that moves with them, the Rust cap-leaf badge-mask, the verifier re-pin) is held as ONE coordinated
batch at the cutover-settle, Rust and Lean moving together. Everything that does NOT touch the VK —
the Step-1 reference (done), the demo app, the SDK API design, the firmament lift, the organ Lean
modelling — proceeds NOW, beside the churn, because it is genuinely read-only-concurrent with it.

This is not a deferral of the hard core: the hard core (the cap algebra on async-signal) is ALREADY a
theorem (Step 1). What is staged is the *encoding cutover* — a deliberate, atomic, separately-gated
act, exactly the `STAGED-ADDITIVE-THEN-CUTOVER` discipline the rotation train itself follows.

**The one genuine new risk, carried forward (NOT closed): the badge-OR covert channel.** A badge-OR
accumulator is a classic covert channel — a signaller modulates bits of the badge, a waiter reads the
OR; bandwidth = the badge width, and the OR leaks *that a signal happened* even across an attenuation
that hid the content. Worse, the "may wake but not read state" attenuation (the new expressivity
`notify` adds) is EXACTLY the authority that creates a one-bit covert channel: the wake itself signals
"something happened." The design bounds this — the **badge-mask is the info-flow scope**, so an
attenuation `mask₁ ⊆ mask₂` is also a *bandwidth* attenuation (the keystone
`signalAdmissible_attenuate_no_amplify` is, read this way, a bandwidth-non-amplification result). But a
`notify` cap is NEVER information-free even stripped of `read`, and dregg has no noninterference
argument yet (it is explicitly out-of-scope, `SeL4Abstract.lean:40`). This is a *feature to price* in
any future noninterference work, not a bug to remove — flagged here, in the same breath as the brick,
not laundered away. The demo app's "a worker cannot signal back / cannot read coordinator state" teeth
demonstrate the *authority* containment; they do NOT claim *information* containment (a worker that
holds a watch on its own accumulator can still infer, from the wake's timing and badge, facts about
the coordinator's schedule). That gap is the named, carried-forward risk.

---

## Appendix — the load-bearing site index (this census, file:line'd)

- **Step 1 (done):** `metatheory/Dregg2/Firmament/NotifyAuthority.lean` — `NotifyCap` `:168`,
  `signalGated` `:205`, `attenuateNotify` `:190`, keystone `signalAdmissible_attenuate_no_amplify`
  `:273`, well-formedness `notificationCap_confers_at_most_notify_read` `:331`, teeth `:417`–`:483`.
- **Core `Auth`:** `metatheory/Dregg2/Authority/Positional.lean:38` (the 7-ctor enum), `capAuthConferred`
  `:66`.
- **The 5 felt-encoders:** `metatheory/Dregg2/Circuit/Witness/SpawnWitness.lean:77`,
  `DelegateWitness.lean:100`, `RefreshDelegationWitness.lean:73`, `RevokeDelegationWitness.lean:97`,
  `attenuateAWitness.lean:44` (each `def authCode : Auth → ℤ`, arms `.read=>0 … .control=>6`).
- **FFI codec:** `metatheory/Dregg2/Exec/FFI.lean:429` (`authTag`), `:434` (`authOfTag`).
- **`Fintype`/`toString`:** `metatheory/Dregg2/Exec/Caps.lean:54` (`elems`),
  `metatheory/Dregg2/Widget/DreggForest.lean:60`.
- **α-totalization:** `metatheory/Dregg2/Firmament/SeL4Abstract.lean:451` (`alpha`), `:459`
  (`Notify ↦ none`), `:467` (`usedAuth`), `:473`/`:479`/`:547` (the re-closing theorems), `:225`
  (the `NotificationCap` strip Step 1 already pins), `:182` (the `SyncSend` vs `Notify` split).
- **`AuthReq` (the notify cap's rights):** `metatheory/Dregg2/Exec/CapTPConcrete.lean:47`
  (`inductive AuthReq`), `:72` (`authNarrowerOrEqual`), `:146` (`facetAttenuation` = the badge order).
- **The effect enum (path-B fork):** `metatheory/Dregg2/Exec/TurnExecutorFull.lean:1998`
  (`FullActionA`, ~20 ctors, NO `signalA` today).
- **Rust authority model:** `cell/src/permissions.rs:5` (`AuthRequired`), `turn/src/action.rs:221`
  (`Authorization`); tier encoding `cell/src/factory.rs:208`; the cap-leaf `auth_tag` fold
  `cell/src/commitment.rs:520`; the per-cell authority digest `commitment.rs:742`.
- **Rust cap-leaf (the badge-mask home):** `circuit/src/cap_root.rs:94` (`CapLeaf`), `:102`
  (`mask_lo`/`mask_hi`), `:115` (`digest`), `:146` (`split_effect_mask`), `:551` (the builder).
- **Rust in-circuit auth gate:** `circuit/src/effect_vm_p3_full_air.rs:255` (the held-auth-tier tag),
  `:1963` (the in-circuit encode fold); `circuit/src/effect_vm/effect.rs:40` (the leaf auth_tag read).
- **SDK:** `sdk/src/channels.rs:204` (`subscribe`)/`:300` (`push_message`), `sdk/src/mailbox.rs:364`
  (`grant_sender`)/`:389` (`sender_authorized`), `sdk/src/events.rs:79` (`subscribe`); `sdk-ts/src/`
  (`mailbox.ts`, `events.ts`, `client.ts`).
- **The apps:** `metatheory/Dregg2/Apps/InboxFactory.lean:183`/`:191`, `PubsubFactory.lean:157`/`:166`,
  `QueueFactory.lean` (enqueue `~:199`), `BountyBoardGated.lean` (claim `~:161`),
  `AgentOrchestration.lean` (worker spawn `~:104`, dispatch `~:379`); the demo →
  `metatheory/Dregg2/Apps/SwarmSignal.lean` (NEW); the gated template →
  `metatheory/Dregg2/Apps/NameserviceGated.lean`.
- **The organs (Rust ungated wakes):** `node/src/channels_service.rs:300` (broadcast),
  `node/src/relay_service.rs` (HTTP-poll drain), `starbridge-v2/src/dynamics.rs:111` (ambient emit),
  `node/src/blocklace_sync.rs:107` (`finality_notify`).
