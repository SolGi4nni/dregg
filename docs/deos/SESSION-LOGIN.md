# The deos Session / Login Manager

The desktop spine runs L5 (the surface tree) through L8 (the cockpit / WM)
over capabilities. The WM/login investigation found one piece missing from
that spine: there is no **login manager**. Every primitive the manager needs
exists; the manager that composes them does not. This document designs that
small, trusted, L6-adjacent cell.

The model is one sentence:

> **login = receiving your root capability · a session = the cap-tree you hold
> · logout = revoking it.**

There is no separate "auth subsystem", no session table, no token store. A
session *is* a c-list. The window manager renders exactly what the root cap
authorizes; revoking the root darkens the whole tree synchronously. The login
manager is the ceremony that, on a proven principal, hands a fresh root cap
into a derived identity cell — and nothing more.

---

## 1. The primitives this composes (it reinvents none)

Everything below already exists and is exercised. The login manager is a
designation flow over them, exactly as the powerbox is a designation flow over
`Effect::GrantCapability`.

| Step | Primitive | Where |
| --- | --- | --- |
| identity = content-address of a key | `CellId::derive_raw(pubkey, token_id)` | `types/src/lib.rs:701` |
| attenuation = caveats + re-HMAC | the macaroon root-key → cap-tree | `token/src/macaroon_backend.rs` |
| hand a cap from held caps | `Powerbox` grant ceremony (`Effect::GrantCapability`) | `starbridge-v2/src/powerbox.rs:237` |
| the per-factory initial cap set | `CapTemplate { target: CapTarget, max_permissions, attenuatable }` | `cell/src/factory.rs:502` |
| logout = the cap goes dark | `Effect::RevokeCapability { cell, slot }`, n=1 synchronous | `turn/src/action.rs:970`, `sel4/dregg-firmament/src/surface.rs:407` |
| verifiable credentials / KERI pre-rotation | the identity app | `starbridge-apps/identity/src/lib.rs` |
| multi-user legitimacy floors | the polis | `metatheory/Metatheory/{Polis,DreggPolis}.lean` |

Two facts make this safe by construction, both already proven and both
re-enforced by the real executor:

- **You cannot grant what you do not hold** (`mint_needs_held_factory`,
  `metatheory/Dregg2/Spec/Authority.lean`). The login manager grants from a
  *system principal* that holds the user's home cells; an attempt to hand more
  than that is refused in-band and again by `World::commit_turn`.
- **A grant is strictly attenuating** (`gen_conferral_is_attenuation`). The
  root cap-template is `≤` what the system principal holds. The user's session
  can never exceed the authority the deos image was configured to give them.

---

## 2. The model

### 2.1 AUTHENTICATE — establish the principal

The login manager never trusts a claimed identity; it proves possession of a
key. Two admission modes, both grounded in the identity app:

1. **Challenge–response.** The manager issues a random nonce; the principal
   signs it with the secret half of `pubkey`; the manager verifies the
   signature against `pubkey`. This is the floor — possession of the key *is*
   the identity (the cell is its content-address).
2. **KERI pre-rotation.** The identity app already carries KERI-shaped
   pre-rotation (`next_keys_digest`). A returning principal proves continuity:
   the presented current key hashes to the previously-committed
   `next_keys_digest`, and a fresh `next_keys_digest` is committed for the next
   login. This survives key rotation without re-deriving identity — recovery,
   not just authentication.

Output: a proven `Principal { pubkey }`. Nothing is granted yet.

### 2.2 DERIVE the root cell

```
root_cell = CellId::derive_raw(&pubkey, &ROOT_TOKEN)
```

The identity cell is the content-address of the key under a fixed root token.
This is deterministic and stateless: the *same* key always derives the *same*
root cell. The manager checks the live ledger:

- **First login** → the root cell does not exist → mint it (a `createCell`
  genesis-shaped turn) and provision its home cells (below).
- **Returning login** → the root cell exists → retrieve it. The home cells and
  any persisted session state are already there.

Identity is therefore not a row in a database; it is a derivation. Lose the
manager's storage and a returning user re-derives to exactly the same cell.

### 2.3 HAND the root cap — the `CapTemplate`

The session's authority is described by a **`CapTemplate`** — the per-user
initial cap set. The `cell/src/factory.rs:502` `CapTemplate` already encodes
exactly the right thing (target · max_permissions · attenuatable); a login
`CapTemplate` is a *vector* of these, the c-list the session is born holding:

```
CapTemplate (a login template) ≔ Vec<CapEntry>
  CapEntry {
    target:        CapTarget,      // SelfCell | Specific(home/surface cell) | Any
    max_permissions: AuthRequired, // the ceiling for that edge
    attenuatable:  bool,           // may the session re-delegate it?
  }
```

A default user template names:

- a cap to the user's **home cell(s)** (`Specific(home)`, full rights,
  attenuatable) — their documents, settings, data;
- caps to the **surfaces / apps they may launch** (`Specific(launcher)` /
  per-app factory caps, attenuated) — the WM renders exactly these as the
  app menu;
- a self-cap (`SelfCell`) so the session can mint sub-caps for the apps it
  launches (this is what makes the powerbox work *inside* the session).

The manager grants each entry into `root_cell` via the **powerbox grant path**,
unchanged: a real `Effect::GrantCapability` from the **system principal** (the
deos image's own root identity, which holds the home cells and factory caps)
into `root_cell`, attenuated to the template entry. Because it is the real grant
turn, `mint_needs_held_factory` and `gen_conferral_is_attenuation` both bite:
the system principal can only ever hand a user authority it was itself
configured to hold, narrowed.

The template is **policy, not mechanism**: it is the one place a deos
deployment says "what does a fresh user get". Changing it changes what every
new session is born holding, with no change to the grant machinery.

### 2.4 The SESSION = the cap-tree

After the grants, `root_cell`'s live c-list **is** the session. There is no
session object to keep in sync with the ledger — the ledger is the session
state. The WM reads `root_cell`'s c-list and renders:

- the home cells as the user's data surfaces;
- the launchable surfaces/apps as the menu;
- the powerbox, *scoped to `root_cell`'s held caps*, so an app the user
  launches can only ever be handed authority the user holds.

Sub-delegation grows the tree: launching an app mints a fresh confined app-cell
(the `AppLauncher` path, `powerbox.rs:404`) and the user designates one of
their held caps into it. The session is a live, growing cap-tree rooted at
`root_cell`.

### 2.5 LOGOUT = revoke the session root

Logout is one move: revoke `root_cell`'s held caps (or, equivalently, revoke
the system principal's cap *to* `root_cell` where that is the spine edge). At
`n = 1` this is `Effect::RevokeCapability`, **synchronous and transitive**: the
instant the revoke turn returns, the caps are gone from real cell-state; any
surface present / app invoke that depended on the tree "finds nothing held and
is refused, so the window cannot paint even one more frame"
(`sel4/dregg-firmament/src/surface.rs:392`). The whole cap-tree goes dark
because every leaf was reachable only through the root edges now removed.

This is the n=1 single-machine collapse the dregg4 vision names: distributed
revocation is an eventual group-key epoch lift, but the deos desktop is one box,
so logout is immediate. There is no stale session to expire, no token to
blacklist — the authority simply ceases to exist.

### 2.6 The receipt

Every step is a real turn and leaves a `TurnReceipt`: the mint of the root
cell, each grant of a template entry, and the revoke. A session's whole
lifecycle is a verifiable transcript on the ledger — login and logout are
auditable the same way every other dregg turn is.

---

## 3. The polis frame — multi-user and agent inhabitants

The polis (`metatheory/Metatheory/Polis.lean`) is the multi-inhabitant law.
The session model slots into it directly.

### 3.1 Each session is a floor

A `Floor State` is the set of states acceptable to a subject. A user's session
exports a floor: the authority their cap-tree confers and the invariants it must
preserve. The **shared desktop is the meet** of those floors —
`SharedFloor floors = fun s => ∀ i, floors i s` (`Polis.lean:77`). A state of
the deos image is acceptable iff it is acceptable to *every* logged-in
inhabitant.

The governing theorem is `polis_safety` (`Polis.lean:102`): for a sound policy
and a safe start, the enveloped system keeps the shared floor **at every step,
for every controller** — and the controller is universally quantified and never
inspected (`polis_envelope_ctrl_blind`, `Polis.lean:125`: "verify the cage, not
the animal"). Applied to deos: the login manager grants a cap-bounded session
to a principal it does not and need not psychologically classify. The bound is
structural — it holds *whatever* the inhabitant does, human or agent.

### 3.2 Schism is the empty meet

`disjoint_floors_no_polis` (`Polis.lean:53`): a polis exists only where the
exported floors have a non-empty meet. Two users with no shared cell and no
shared surface do not form a desktop polis — and that is correct, not a bug:
they are simply two disjoint sessions on one image, the edge of the polis being
the empty intersection, never a wall. A *shared* desktop (a co-edited document,
a shared surface) is exactly a non-empty meet: the cells both sessions hold a
cap reaching. The meet is of **exported floors, never of interiors** — neither
session sees the other's private cap-tree.

### 3.3 An agent (Hermes) logging in = a cap-bounded inhabitant

This is where the model pays off. An agent is "an intricate loop"
(`docs/deos/HERMES-INTEGRATION.md`); dregg closes the enforcement gap at one
seam — the tool-call → verdict → receipt boundary. **Agent login is exactly the
same ceremony as user login**: the agent authenticates with its key, derives its
root cell, and is handed a `CapTemplate`. The only difference is *which*
template — an agent's session is born holding a deliberately narrower cap-tree
(its mandate). Every tool-call the agent makes is then a turn authorized by a cap
*in its session* — and a tool-call that exceeds the mandate is refused in-band,
because the agent simply does not hold the cap, and the executor backstops it.

`polis_safety`'s controller-blindness is the load-bearing fact: the shared-floor
guarantee is *identical* for a human and an agent inhabitant. The deos polis
does not need to know whether an inhabitant is a person or a model; it needs only
the cap-bounded session. An agent is a first-class inhabitant of the deos polis,
governed by the same envelope, with no special case in the enforcement function
("there is no place to put a shadow of the controller").

Logout of an agent is the same synchronous revoke — and it is *the* kill switch:
revoke the agent's session root and its whole capability to act on the desktop
goes dark in one turn.

---

## 4. How much polis in v1? — thin-that-grows (recommended)

**Recommendation: v1 is a thin "authenticate → derive → grant → revoke", built
so the polis legitimacy-floor governance comes online incrementally as
multi-user and agent inhabitants land.**

The justification is that the two halves have different readiness:

- **The session mechanism is buildable today and entirely from existing,
  proven primitives.** `derive_raw`, the powerbox grant path, `CapTemplate`,
  and synchronous `RevokeCapability` are all live. A single-user login manager
  is a *weld*, not a build — exactly the kind of work the project's method
  prefers.
- **The polis legitimacy floors are a Lean trunk under active development.**
  `polis_safety` / `disjoint_floors_no_polis` are proven, but wiring the *live*
  deos image's shared-floor envelope to the kernel (the `DreggPolis` weld:
  authority = l4v `Auth`, disclosure = EpistemicDial) is the bigger, ongoing
  campaign. Coupling v1 login to full legitimacy-floor governance would gate a
  shippable desktop piece on the deepest part of the formal trunk.

Crucially, thin-that-grows is **not** a different design that gets thrown away.
The v1 session *already is* a floor (its cap-tree); v1 just doesn't yet compute
the *meet* of floors or run the envelope. The growth is additive:

1. **v1 — single-user.** authenticate → derive root cell → grant the default
   `CapTemplate` → revoke on logout. One session, the whole desktop. The WM
   renders the root cap. (This is the missing spine piece, closed.)
2. **v2 — multi-user floors.** Multiple concurrent sessions, each a floor. The
   shared desktop is the computed meet (`SharedFloor`); a co-edited cell is a
   non-empty meet, disjoint users are `disjoint_floors_no_polis`. Wire the
   `polis_safety` envelope so the shared image keeps every inhabitant's floor.
3. **v3 — agent inhabitants.** Hermes (and other agents) log in with a narrower
   `CapTemplate`; the tool-call seam authorizes against the agent's session;
   `polis_safety`'s controller-blindness makes the agent a first-class
   inhabitant under the same envelope; logout is the kill switch.

Each step adds, never rewrites. Ship v1; let the polis come online with the
multiplicity it governs.

---

## 5. The trusted-cell stance

The login manager is **L6-adjacent and trusted**, in the same sense the
powerbox is: it holds the **system principal** — the only principal in the image
that holds the home cells and factory caps a fresh session is provisioned from.
But it has no ambient authority beyond that: it can only grant *from* the system
principal's held caps, attenuated, through real turns the executor re-checks. A
bug in the login manager cannot mint authority that does not trace back to the
system principal's configured holdings (the `mint_needs_held_factory` backstop).
It is trusted to *designate the session*, not to *be the authority* — exactly the
powerbox split (the designation UI vs. the executor as authority).

The system principal itself is the deos image's root identity, seeded at image
construction (the genesis cells the desktop is born with). Bootstrapping it is
the one out-of-band step — the image's own key — and it is the natural place a
deployment configures "what authority does this desktop have to hand out".

---

## 6. Type sketch

A compile-checked sketch lives at `starbridge-v2/src/session.rs` (the same
`embedded-executor`-gated, gpui-free, `cargo test`-able home as `powerbox.rs`).
It defines `Principal`, `CapEntry` / `CapTemplate`, `Session`, and
`LoginManager` over the real `World`, `CellId::derive_raw`, `Effect::Grant/
RevokeCapability`, and the `Powerbox` grant path — and its tests exercise the
full ceremony: authenticate (a held-key check stand-in) → derive → grant the
template → the session c-list reflects exactly the template → revoke darkens the
whole tree. See the module docs there for the line-by-line grounding.
