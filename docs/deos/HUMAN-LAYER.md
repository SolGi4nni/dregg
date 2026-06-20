# The Human Layer

deos is a sovereign OS someone *lives in*. dregg has the capability and crypto
substrate cold — cells as principals, attenuable proof-carrying tokens, a real
weighted-threshold-signature scheme, KERI-shaped compromise-resistant key
rotation, all of it executor-enforced and much of it Lean-proven. What has been
barely addressed is the **human who holds the keys**: how a person *is* a
principal, how they keep and recover their authority, and how they see and
wield it without a cryptography degree.

This is the load-bearing gap, and it follows from one fact: **you cannot lose
your own OS.** If deos is where someone keeps their life, then losing a key,
losing a laptop, or having a device stolen cannot mean losing access to that
life — and it cannot be fixed by a company with a "reset my account" button,
because there is no company. The recovery story has to be as sovereign as the
rest of the system: no trusted third party, no custodian, no backdoor. It has
to be the ocap/threshold way, all the way down.

This document designs that layer. The encouraging news, from the census below,
is that **almost every cryptographic piece already exists and is wired into the
executor.** The human layer is mostly a *weld and a UX*, not a new substrate.

---

## 0. What the substrate already provides (census)

Read these as the floor we build on, not as things to invent.

### Identity as an HD-keyed cipherclerk

`dregg_sdk::AgentCipherclerk` (`sdk/src/cipherclerk.rs`) is the wallet-grade
credential holder: an Ed25519 signing identity, a roster of held capability
tokens, attenuation/delegation, turn signing, and proof generation. It is built
from a **BIP39 24-word mnemonic** (`sdk/src/mnemonic.rs:45` `generate_mnemonic`,
256 bits of entropy + checksum) via `AgentCipherclerk::from_mnemonic`
(`sdk/src/cipherclerk.rs:1182`) or from a raw 64-byte seed
(`from_seed`, `:1193`). From the one seed it HD-derives namespaced
sub-identities — `derive_sub_agent_at_path` (`:1254`) explicitly supports
`"dregg/device/laptop"`, `"dregg/app/orderbook"`, `"dregg/signing/cold"`, all
recoverable from the single seed.

An identity *owns* a cell: `AgentCipherclerk::cell_id(domain)`
(`sdk/src/cipherclerk.rs:1340`) is the same derivation `Cell::with_balance`
uses, so the identity is the principal that holds that cell.

### Identity cells with KERI-shaped pre-rotation (the recovery primitive)

This is the keystone. `starbridge_polis::identity` (surfaced through
`sdk/src/identity.rs`) implements **KERI-style key pre-rotation** as a real
cell program, with kernel semantics **proven in
`metatheory/Dregg2/Apps/PreRotation.lean`**:

- An identity cell carries a `CURRENT_KEYS_COMMIT_SLOT` (commitment to the
  current device key set) and a `NEXT_KEYS_DIGEST_SLOT` — a commitment to the
  *next, unexposed* key set (`sdk/src/identity.rs:47-51`).
- Rotation is the `KeyRotationGate` state constraint
  (`cell/src/program.rs:1331`). To rotate, a turn must **exhibit the preimage**
  of the pre-committed next-keys digest, **install** the new key set, **commit a
  fresh next digest** (the forward chain), and **wait out a cooling window**
  (`cell/src/program.rs:3090-3145`).
- **The current keys are powerless.** The gate *never reads* the current key
  set (`cell/src/program.rs:1325-1328`). This is the proven theorem
  `rotate_current_keys_irrelevant` (it is `rfl` — `PreRotation.lean:170`) and
  its consequence `rotate_compromise_resistant` (`:180`): **a thief holding
  every current signing key still cannot rotate the identity.** Only the holder
  of the pre-committed next-key preimage can. This is exactly the property a
  recovery story needs.
- The receipt stream over the two key registers *is* the key-event log (the
  KERI KEL shape) — an auditable history of every rotation.
- The cooling window (`rotateStepCooled_refuses_inside`, `:287`) makes recovery
  *slow and visible to the council* — so a stealthy takeover surfaces before it
  completes.

The charter pins a **recovery council** at genesis (`sdk/src/identity.rs:35`,
`:108`): `charter.council.members_commitment()` is written into
`COUNCIL_COMMIT_SLOT` and is *pinned for life*. The council is a polis council
factory — content-addressed `(threshold, members)` (`starbridge-apps/polis/src/lib.rs:22`,
`council` module at `:330`, M-of-N with `1 <= M <= N`).

### Real weighted threshold signatures (no DKG, no trusted dealer)

`dregg-hints` (the `hints/` crate) is a **HINTS weighted-threshold-signature**
implementation over BLS12-381 with KZG/Plonk-style aggregation
(`hints/README.md`). Its headline properties are precisely what social recovery
wants:

- **Silent setup** — *no DKG protocol between signers.* Each guardian generates
  a keypair locally and publishes a public key + a "hint." Anyone can aggregate.
- **Dynamic, weighted thresholds** — the threshold can be chosen *per message*,
  after key generation, and guardians can carry different weights.
- `sign` / `sign_aggregate` / `verify_aggregate` (`hints/src/lib.rs:90,178,208`);
  `ThresholdNotMet` is a first-class error (`hints/src/types.rs:163`).

And it is **already an executor-verified authorization mode.** The turn executor
exposes `ThresholdSigVerifier` (`turn/src/executor/membership_verifier.rs:1067+`),
which on a `Authorization::Custom { vk_hash }` discharge deserializes the
aggregate QC, looks up a host-trusted `ThresholdSigCommittee`, runs
`hints::verify_aggregate` (SNARK + BLS pairing) against the canonical signing
message, and **fails closed** unless the aggregated weight meets the threshold
(`:1100-1112`). So "a turn authorized by an M-of-N guardian quorum" is not a
thing to build — it is a thing to *wire up*.

### Multi-mode authorization (primary OR backup OR quorum)

`Authorization::OneOf` (`turn/src/action.rs:310+`) is the categorical coproduct
of authorization modes: *any one of* a set of candidates suffices. Its
documented app driver is verbatim our case — *"recovery flows ('primary OR
backup OR social-recovery quorum')"* (`turn/src/action.rs:316`). The executor
verifies exactly one indexed candidate; `Unchecked` and nested `OneOf` are
rejected (no auth-bypass). For genuine M-of-N it routes to
`Authorization::Custom` with a threshold-sig predicate (the caveat at `:330`),
which is exactly the `ThresholdSigVerifier` path above.

### The trusted-designation UX (the powerbox / CapDesk)

`starbridge-v2/src/powerbox.rs` is the human-in-the-loop capability flow built
right: an ocap system has **no ambient authority**, so a confined app cannot
name a resource it was never granted. The powerbox is the trusted UI (the
cockpit's own principal, *not* the app) that presents a picker of *what the user
actually holds*, lets the user **designate** one + the rights to confer, and
mints a fresh attenuated cap into the app's c-list via **a real grant turn**.
The grant is strictly attenuating (`granted ⊆ held`, the genuine
`dregg_cell::is_attenuation`), held-bounded (you cannot grant what you do not
hold — proven `mint_needs_held_factory`), and the executor is the backstop. The
cockpit's POWERBOX tab renders exactly these rows. This is the *granting* half
of the trust UX; the human layer adds the *holding / revoking / recovering*
halves.

---

## 1. Identity: how a human IS a principal

A human in deos is **a sovereign identity cell, keyed by a cipherclerk, mirrored
across their devices.** Three things, with a clean relationship:

```
   the human  ──owns──▶  an IDENTITY CELL  (the sovereign principal: a KERI key-event log)
       │                        │
       │ holds the seed         │ COUNCIL_COMMIT pins the recovery guardians
       │ (24-word mnemonic)     │ CURRENT_KEYS commits the live device keys
       ▼                        │ NEXT_KEYS_DIGEST pre-commits the next (escrowed) set
   a CIPHERCLERK  ──derives──▶  per-DEVICE sub-identities  (dregg/device/laptop, …)
   (HD root, dregg/0)           per-PURPOSE sub-identities  (dregg/signing/cold, …)
```

- **The person ≙ the identity cell.** Not a key — a *cell*. The cell is the
  durable, content-addressed principal whose `CURRENT_KEYS_COMMIT_SLOT` says
  "these device keys speak for me right now." Keys rotate underneath a stable
  identity; the cell, and the cells it owns (the person's data, their app
  state, their authority), persist across every rotation. This is the crucial
  inversion from key-as-identity systems (Bitcoin, raw PKI): **losing a key is
  not losing the identity**, because the identity is the cell and the key is
  merely its current speaker.

- **Devices are sub-identities, not separate principals.** Each device holds an
  HD-derived sub-identity (`derive_sub_agent_at_path("dregg/device/<name>")`).
  All of a person's devices' public keys are *members of the current key set*
  committed in `CURRENT_KEYS_COMMIT_SLOT` (multiple device keys, like the
  two-device charter in `sdk/tests/identity_prerotation_e2e.rs:40`). So "my
  laptop and my phone both speak for me" is the key-set commitment; adding or
  retiring a device is a *rotation* (it changes the committed set), and a
  stolen device's key is a *member to rotate out*. This is the
  cross-device-firmament tie: ONE identity across DISTANCE, each device a local
  speaker for the same sovereign cell (the n=1 firmament collapse).

- **The seed is the root, escrowed away from daily keys.** The 24-word mnemonic
  derives the cipherclerk root (`dregg/0`) and every device/purpose
  sub-identity. The daily device keys are *exposed* (they sign turns); the
  **next-keys preimage** (the rotation credential) is *unexposed and escrowed
  with the recovery council, not alongside the current keys*
  (`sdk/src/identity.rs:32-35`). This separation is what makes the next section
  possible.

**Genesis** is one ceremony (`genesis_effects`, `sdk/src/identity.rs:97`):
install the birth key-set commitment, the first next-keys pre-commitment, and
the pinned recovery council; step the cell UNINIT → ACTIVE. This is KERI's `icp`
(inception) event.

---

## 2. Key management + recovery — the load-bearing part

> *You cannot lose your OS.* Every other section serves this one.

The threat model has four cases. The substrate handles all four *without a
trusted third party*, because recovery is a key rotation gated on a guardian
quorum — pure ocap/threshold, no custodian.

### 2a. Routine: add / retire a device (no loss)

Rotate the key set (`AgentRuntime::rotate_identity`, `sdk/src/identity.rs:159`):
exhibit the pre-committed next-key preimage, install the new device set (adding
the new phone, dropping the old one), commit a fresh next digest. Riding the
normal `.turn()` path; no council needed for a routine add when you still hold a
current device. The KEL records it.

### 2b. Device lost or stolen (you still have one device + the seed)

Same rotation, but it *removes* the lost device's key from the committed set.
Because the gate **never reads the current keys**
(`rotate_current_keys_irrelevant`), the thief holding the stolen device's key
**cannot rotate, cannot block your rotation, and is cut off the instant your
rotation lands.** The cooling window makes the change visible to your council
while it settles. This is compromise resistance as a *proven theorem*, not a
policy.

### 2c. All keys lost (you lost every device, OR forgot the seed) — SOCIAL RECOVERY

This is the case that kills most systems. Here it is **M-of-N guardian
recovery**, and it is a *capability-grant flow*, not an account reset:

1. **At genesis you chose guardians** — N people (or your own other identities,
   or a hardware token, or a notary cell) whose threshold-sig public keys +
   weights were committed into the recovery council
   (`COUNCIL_COMMIT_SLOT`, pinned for life). E.g. 3-of-5 friends, or
   2-of-3 (you-on-another-device + spouse + a paper backup).

2. **You (or your new device) request recovery** — a proposed rotation to a
   *fresh* key set you generate now. You do **not** need any old key for this;
   that is the whole point.

3. **Guardians authorize, asynchronously and silently** — each guardian signs
   the recovery message with their HINTS key (`hints::sign`). **No guardian has
   to talk to any other guardian** (silent setup, no DKG). Whoever assembles the
   request `sign_aggregate`s the partials into one succinct QC once the weighted
   threshold is met (`hints/src/lib.rs:178`).

4. **The recovery rotation commits** — the turn is authorized by
   `Authorization::Custom` carrying that aggregate QC; the executor's
   `ThresholdSigVerifier` runs `hints::verify_aggregate` against the council
   committee and admits the rotation **iff** the quorum threshold is met
   (`turn/src/executor/membership_verifier.rs:1100`). The cooling window applies
   (`rotateStepCooled`), so a recovery is *slow and visible* — if it is an
   attacker who suborned your guardians, you see it coming and can react.

5. **You are back.** The identity cell is unchanged; only its current key set
   was rotated to your new device. Every cell you owned, every cap you held,
   your whole life in the OS — still yours, because the *identity is the cell*.

   Recovery is exactly the `Authorization::OneOf` driver named in the code:
   *"primary OR backup OR social-recovery quorum"* (`turn/src/action.rs:316`).

**There is no trusted third party anywhere in this.** The guardians are *your*
designation; the threshold is *your* policy, pinned at genesis; the executor
verifies the math; no one — not a company, not a majority of guardians below
threshold, not a thief with your phone — can move the identity except a genuine
quorum. The honest crypto is HINTS over BLS12-381, and it is the *real verifier
the executor already runs*, not a sketch.

### 2d. The escrow discipline (what a guardian actually holds)

A guardian does **not** hold your seed. Two sound designs, both on existing
primitives:

- **Quorum-as-rotation (preferred):** guardians hold *threshold-sig keys*. The
  recovery credential is "a quorum of guardian signatures authorizes a rotation
  to a key set the recovering user freshly chose." No guardian ever sees key
  material that lets them act *as* you alone; below threshold they have nothing.
  This is 2c exactly. (Caveat in §5: guardians-collude-above-threshold is the
  residual trust — chosen, weighted, and visible, but real.)

- **Sharded next-preimage (optional belt-and-suspenders):** the unexposed
  next-keys preimage can be Shamir-split across guardians so that M-of-N
  *reconstruct* it. This re-uses the existing pre-rotation gate with no new
  verb. It is strictly weaker than quorum-as-rotation (reconstruction exposes
  the preimage to whoever assembles it), so we offer it only as a fallback for
  guardians who cannot run a signer. Quorum-as-rotation is the default.

---

## 3. The trust UX — the human's view of their authority

The principle: **"Would a 5-year-old click it with delight, AND can ember
not-lose-her-OS."** The powerbox already proves the *granting* surface is
buildable and honest; the human layer is the panel around it. One surface, four
faces, every one of them a *real* projection of executor state (the moldable
inspector framework, `docs/deos/INSPECTOR-FRAMEWORK.md`):

1. **WHO I AM** — the identity cell as a living card: my devices (the current
   key set, each a friendly icon — laptop, phone, paper), my recovery guardians
   (faces, with the threshold drawn as "any 3 of these 5"), the KEL as a
   plain-language timeline ("you added your phone · Tue"). Reflects
   `inspect_identity` (`sdk/src/identity.rs:50`) and the council commitment.

2. **WHAT I HOLD** — my capability tokens, surfaced from the *real* cipherclerk
   (`reflect_token`, `starbridge-v2/src/cipherclerk.rs:592`): each cap as "what
   it lets me touch, and how narrowed." Not a hex dump — a sentence.

3. **WHAT I'VE GRANTED, AND UNDO** — the delegations I've made
   (`reflect_delegation`, `cipherclerk.rs:645`) and the **revoke** gesture. Each
   granted cap shows the grantee and a single "take it back" action that builds
   the real revocation turn. (Revocation is the dual of the powerbox grant; the
   panel makes "who can touch my stuff, and stop them" a one-click question.)

4. **DESIGNATE (the grown-up powerbox)** — when an app asks for authority, the
   trusted picker of §0 shows *only what I hold*, in human terms, and I point at
   one thing. The 5-year-old version: "this app wants to use your photos — pick
   which album." The adept version: the same flow, but live-inspectable down to
   the attenuation lattice and the receipt the grant left.

The whole surface is **moldable and live** (the Pharo/Smalltalk half of the deos
vision): an adept can open any card and inspect the cell, the key set, the
council, the QC — the image is its own debugger. A child clicks faces and albums
and it Just Works. Same surface; the depth is opt-in.

The **recovery UX** specifically must be rehearsable and reassuring:
- *Setup* ("Who are your guardians?") is a warm, social moment — pick faces,
  set "how many of them," done. Print a paper backup if you want a non-human
  guardian.
- *Recovery* (on a new device) is "I lost everything" → "ask your guardians" →
  a visible progress bar of arriving guardian approvals → "welcome back." The
  cooling window is shown as a safety feature ("settling — if this wasn't you,
  tap here"), not a delay to apologize for.
- *Drills* — the OS can run a no-op recovery rehearsal so a person has done it
  *before* the day they need it. Most recovery systems fail because the user
  never practiced; deos should make practicing delightful.

---

## 4. The design + the first buildable milestone

**The design in one line:** a human is a *sovereign identity cell* keyed by a
*cipherclerk*, with daily *device sub-keys* that rotate freely under a stable
identity, and a *recovery council* of guardians whose *HINTS threshold-sig
quorum* can authorize a rotation to a fresh key set — so no key, device, or seed
is ever a single point of total loss, and no trusted third party is ever
involved.

**Everything cryptographic for this already exists and is executor-wired** (§0).
The work is the weld + the UX, in three milestones.

### Milestone 1 (first buildable): identity-as-cell + social recovery on the live substrate

Smallest end-to-end slice that makes the #1 guarantee real:

- **Identity bootstrap** in the cipherclerk panel: generate a mnemonic, create
  the identity cell (`create_identity` → `genesis_effects`), name the first
  device. (All existing SDK calls; `sdk/tests/identity_prerotation_e2e.rs` is
  the working reference.)
- **Choose guardians**: a UX over a polis council charter
  (`starbridge-apps/polis` council factory) whose members are guardian
  threshold-sig public keys, threshold M-of-N, committed into the identity's
  `COUNCIL_COMMIT_SLOT`. Register the committee with the executor's
  `StaticThresholdSigPolicy` (`turn/src/executor/membership_verifier.rs:1175`)
  keyed by the council commitment.
- **The recovery flow itself**: on a fresh device, propose a rotation to a new
  key set; collect guardian `hints::sign` partials; `sign_aggregate`; submit the
  rotation turn under `Authorization::Custom` verified by `ThresholdSigVerifier`;
  watch it settle through the cooling window. The acceptance test is the whole
  point: **a cipherclerk with NO old keys, given a guardian quorum, recovers
  control of the identity cell and all the cells it owns** — and is REJECTED
  with anything less than the threshold.
- **The trust panel, v1**: faces 1 (WHO I AM) + the recovery setup/run UX.

This milestone is mostly *wiring proven parts together* — the rotation gate, the
threshold verifier, and the council factory each already pass their own tests;
the milestone is the seam that joins them into "ember cannot lose her OS," with
one e2e test that proves it.

### Milestone 2: the full trust panel + device fleet
Faces 2/3/4 (hold / granted+revoke / grown-up powerbox); multi-device key sets
with friendly add/retire; the KEL timeline; recovery *drills*.

### Milestone 3: cross-device firmament + guardian liveness
Devices as live firmament speakers (sync the identity cell across a person's
machines per the firmament n=1 collapse); guardian-presence indicators;
optional sharded-preimage fallback for non-signer guardians; per-purpose cold
keys (`dregg/signing/cold`) with `Authorization::OneOf` (hot key OR cold-vault
proof).

---

## 5. Honest hard parts

The substrate is unusually complete, so the hard parts are the genuinely-hard
ones, not gaps we can wave away. Each is named *with* its closure lane.

- **Recovery is genuinely hard, and the council is real trust.**
  Quorum-as-rotation removes the *custodian*, not the *trust* — a quorum of
  guardians colluding *above threshold* can move your identity. That is a
  deliberate, chosen, weighted, *visible* (cooling-window + KEL) trust, far
  better than a company's silent backdoor, but it is not zero. Mitigations to
  design: higher thresholds, weighting (a paper backup you hold = a heavy
  guardian), the cooling window as a veto opportunity, and a "panic" rotation
  the user can trigger during cooling if a recovery they didn't initiate
  appears. *Closure lane: the recovery-UX threat-model doc + the panic-veto
  turn.*

- **Key UX is where almost every system dies.** The 24-word mnemonic is honest
  but hostile; "escrow the next-keys preimage with the council, not next to your
  current keys" is correct but unintuitive. The whole bet of §3 is that the
  *identity-is-a-cell* inversion lets us hide raw keys behind devices and
  guardians — the user manages *people and devices*, which they understand, not
  *secrets*, which they don't. This must be validated with real humans, not
  asserted. *Closure lane: usability testing of the recovery drill against the
  Pug handoff bar (works without ember in the loop).*

- **The device-trust model has a bootstrapping seam.** Adding a device means
  getting its new public key into a rotation — which needs an authenticated
  channel between two devices (QR pairing, etc.) or it is itself an attack
  surface. The pre-rotation gate secures the *commitment*; getting the right key
  *to* the commitment is the unbuilt seam. *Closure lane: the device-pairing
  ceremony (likely a short-lived powerbox-style designation between the old and
  new device).*

- **Guardian liveness and rotation.** Guardians lose their own keys, die, fall
  out with you. The council commitment is pinned per identity, so *changing your
  guardian set* is itself an authority operation that must be specced (almost
  certainly: a council amendment authorized by the *current* council quorum,
  riding the polis amendment machinery). Until specced, a recovery council is
  set-once — a real limitation. *Closure lane: the guardian-set-rotation verb.*

- **The committee registration is host-trusted today.** `StaticThresholdSigPolicy`
  maps a commitment → committee in host memory
  (`turn/src/executor/membership_verifier.rs:1170`); for a light client to
  verify a recovery *without* trusting the host, the council committee must be
  bound *into the commitment the circuit checks* (the same "gate must bind the
  write into the commitment" obligation the circuit-soundness campaign tracks).
  Recovery-by-quorum is sound for the local sovereign case now; making it
  light-client-unfoolable is the circuit-soundness tie-in. *Closure lane: the
  council-commitment binding obligation in `docs/CIRCUIT-FUNCTIONAL-CORRECTNESS.md`.*

- **Threshold-sig setup ceremony.** HINTS needs a KZG universal setup
  (`hints::GlobalData`) and each guardian must publish a hint. Silent setup
  means no DKG, but there is still a one-time "publish your guardian key + hint"
  step whose UX and trust (whose universal params?) must be designed so a
  non-expert can do it. *Closure lane: the guardian-onboarding ceremony in
  Milestone 1.*

---

## Summary

deos's human layer is not a missing substrate — it is a **weld and a UX over an
unusually complete one**. A human is a *sovereign identity cell* (the durable
principal), keyed by an HD *cipherclerk*, spoken for by rotating *device keys*,
recoverable by a *guardian quorum*. The single load-bearing guarantee — *you
cannot lose your own OS* — is delivered by KERI-shaped, **Lean-proven**,
compromise-resistant key rotation (`rotate_current_keys_irrelevant`) authorized,
when all keys are lost, by a **real HINTS weighted-threshold-signature quorum**
that the executor **already verifies** (`ThresholdSigVerifier` →
`hints::verify_aggregate`) — with **no trusted third party** anywhere in the
loop. The first milestone is the seam that joins the three already-tested parts
(rotation gate + threshold verifier + council factory) into one end-to-end
"recover-with-no-old-keys" flow, fronted by a trust panel that a five-year-old
can click and an adept can inspect to the felt.
