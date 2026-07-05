# Branch-and-stitch multiplayer as a real app — the distributed-Houyhnhnm flagship

> **STATUS — BUILT (slice 0 executed).** This plan has been carried out. The transport-free
> primitive is live at `starbridge-v2/src/branch_stitch_session.rs` (`BranchStitchSession`,
> `Branch`, `StitchVerdict` — the exact §2.2 API), registered at `starbridge-v2/src/lib.rs`
> (`pub mod branch_stitch_session;` under `embedded-executor`), and the demo crate exists at
> `starbridge-apps/branch-stitch-multiplayer/` (`Cargo.toml` + `src/main.rs`, the Beat A/B/C
> arc). Read §§2–4 below as the design rationale for what shipped, not as future work.
> **One tail is still open:** the §2.4 refactor of `ForkMembraneHost::stitch_pair` into a thin
> adapter over the session did NOT land — `stitch_pair` (`starbridge-v2/src/shared_fork.rs`)
> still calls `stitch_projections` / `settle_umem_stitch` directly rather than delegating to
> `BranchStitchSession::stitch`. That is the one genuinely-remaining slice.

The distributed-Houyhnhnm synthesis — *distributed · reversible · capability-secure ·
witnessed · branch-and-stitch* — already exists as a PROVEN theorem and a working
production path. What was missing was the last adoption step: a reusable primitive a plain
demo can call, and an inspiring app that exhibits the whole thing end to end without
dragging in the cockpit's chat/GPU transport stack.

This is the design + build plan for that (now executed — see the STATUS banner).
Present-tense, first-principles, grounded to `file:line` at HEAD.

The one-breath claim the app makes real: **two agents fork one shared verified world,
diverge on their own branches, and stitch back through a single gated door — compatible
edits merge with conservation and authority preserved, a genuine conflict is refused
fail-closed, and a capability revoked between branch and settlement cannot ride the
stitch. Distributed, reversible, capability-secure, witnessed multiplayer — the thing
nobody else has.**

---

## 1. What exists today

### 1.1 The proven theorem (the gate the whole thing rides)

* `metatheory/Metatheory/SettlementSoundness.lean:153` — `settlement_soundness`: under any
  settlement predicate that *binds live authority*, a SETTLED turn necessarily exercised
  an authority LIVE at the settlement tip (an attenuation of something held AND honored by
  the tip's finalized revocation set).
* `…/SettlementSoundness.lean:192` — `revoke_before_tip_unsettleable` (the contrapositive
  keystone): a credential revoked-and-propagated before the tip makes the turn
  *unsettleable*, branch-time view notwithstanding. This is literally "a cap I have since
  revoked cannot ride a stitch into my real world."
* `metatheory/Dregg2/Circuit/SettlementSoundness.lean:112` `settledRevView` /
  `:210` `settlement_soundness` — the circuit-side twin (authority read at the finalized
  tip's revocation set, not the branch's stale view). `:251`
  `settlement_soundness_single_machine` is the n=1 immediate-revocation collapse.

These are `#assert_axioms`-clean per the circuit-soundness apex. The theorem is DONE; this
plan is about making a stranger able to *run* its operable shadow.

### 1.2 The operable control model (abstract, reusable, but not over a real World)

`starbridge-v2/src/branch_stitch.rs` is the gpui-free CONTROL model of the two turns
(`EnterVirtualization` + `Stitch`), named in the same vocabulary as the Lean keystones:

* `VirtualBranch` (`:95`) + `confined` (`:126`) + `admits_debit` (`:144`) — the operable
  shadow of `branch_cannot_drain_main` (a confined branch's main-debit is structurally
  imaginary).
* `Stitch::settle` (`branch_stitch.rs:327`) — the settlement gate. Its predicate
  (`:336`): `held.target == c.target && (held.debit_reach || !c.debit_reach)` — refuse any
  conferred cap not held at the settlement tip. This is the operable shadow of
  `settlement_soundness`.

It is reusable (gpui-free, `embedded-executor`-gated lib module) BUT it operates over an
ABSTRACT `DocGraph` (`branch_stitch.rs:232`), not a real `World`. It proves the algebra; it
does not fork a live cap-bounded world or drive real verified turns. A demo built on it
would be a model, not a multiplayer session.

### 1.3 The REAL machinery (over a live World) — and why it is locked away

The genuine fork-diverge-stitch over a real verified world is assembled from four pieces,
ALL gated on `embedded-executor` only (gpui-free, no `dev-surfaces`):

| Piece | Location | Role |
|---|---|---|
| `World::fork` | `world.rs:695` | deep-clone a live world into an independent verified fork (carries signing key, factories, receipt-chain heads) so a forked turn produces a receipt verifiable under the SAME executor key |
| `World::commit_turn` | `world.rs` (pub) | drive a real verified turn on a fork — identical conservation/ocap/program guarantees; mutates only the fork |
| `MembraneFrustum::mint` / `rehydrate` / `from_snapshot_bytes` | `shared_fork.rs:732`,`:745` | the cap-bounded cull around a focus (anti-amplification by omission), serialize across a boundary, rehydrate into an independent real `World` |
| `UmemBranch::mint`/`from_frustum`, `stitch_projections`, `settlement_held_at_tip`, `settle_umem_stitch`, `SettledUmemStitch::settles` | `umem_membrane.rs:122`,`:171`,`:346`,`:482`,`:557`,`:518` | the field-granular state pushout PLUS the settlement-sound authority gate |

The settlement gate in `settle_umem_stitch` (`umem_membrane.rs:557`) uses the IDENTICAL
predicate as the proven control model (`umem_membrane.rs:568` ≡ `branch_stitch.rs:336`),
but lossy-per-cap (a linear DROP surfaced as a first-class object) rather than whole-stitch
refusal — exactly the membrane's "drop the over-conferred cap, let the disjoint merge
proceed."

**The production entry point** that ties these together is `ForkMembraneHost::stitch_pair`
(`shared_fork.rs:1072`). It:
1. finds the two driven forks (`a`, `b`) in its registry (each a `(World, MembraneFrustum)`),
2. builds the shared-ancestor baseline `UmemBranch::from_frustum`, re-projects each driven
   fork, folds with `stitch_projections` (the STATE pushout),
3. gathers the caps each branch would confer (the focus's live caps in each driven fork),
4. reads `settlement_held_at_tip(&self.source_fork, focus)` — authority at the TIP, after
   any revocation committed on main between branch and settlement,
5. `settle_umem_stitch` — the gate; admits held caps, LINEAR-DROPS revoked-before-tip ones,
6. surfaces `StitchOutcome { settled_root, merged, dropped }`.

This is the live branch-and-stitch multiplayer the memory references (`3c0467262` /
`8ce5808cd` / `0f53bc45e`). It is REAL and tested:
* `starbridge-v2/tests/stitch_pair_settlement_sound_production.rs` — the gate fires through
  the live `stitch_pair`: a `gift` cap held at branch is REVOKED on main, the SAME stitch
  drops it after but not before (non-vacuous both ways).
* `starbridge-v2/tests/two_instance_multiplayer_session.rs` — two distinct principals
  (`ada`/`boris`) co-inhabit one world, disjoint edits fold clean, a same-field clash
  surfaces as a `ValueCollision` `ConflictObject` and does NOT settle; proven two ways
  (coordinated `stitch_pair` AND a serialization-boundary-crossing `stitch_umem_forks`) and
  they AGREE.

**Why it is locked inside starbridge-v2 (not callable by a plain demo).** `stitch_pair`
lives inside `ForkMembraneHost`, which is `#[cfg(feature = "dev-surfaces")]`
(`shared_fork.rs:997`). `dev-surfaces` pulls `deos-matrix` + `deos-zed` + `deos-hermes` +
`deos-terminal` + `firmament` (`starbridge-v2/Cargo.toml:180`) — the whole chat/cockpit
transport stack. The host is tied to `deos_matrix::membrane` WIRE types (`ForkHandle`,
`MembraneHost`, `StitchOutcome`, `ConflictObject`, `MembraneEnvelope`,
`shared_fork.rs:1003`). A plain demo that just wants "fork a world, diverge, stitch" must
therefore drag in the entire Matrix transport — even though the *logic* it needs
(steps 1-6 above) uses ONLY `embedded-executor` primitives. The `dev-surfaces` gate is
incidental to the wire wrapping, not to the branch-and-stitch semantics.

That gap — real semantics trapped behind a transport gate — is exactly the extraction.

---

## 2. The extraction — `stitch_pair` → a reusable primitive

### 2.1 The insight

The GUTS of `stitch_pair` (the state pushout + the settlement-sound authority gate) call
only `embedded-executor`-available items: `World`, `MembraneFrustum`, `UmemBranch`,
`stitch_projections`, `settlement_held_at_tip`, `settle_umem_stitch`. Nothing in steps 1-6
needs `deos_matrix`. The only `deos-matrix` coupling is the *shape of the inputs/outputs*
(`ForkHandle` → registry lookup; `StitchOutcome`/`ConflictObject` → the return). Strip that
shell and the primitive falls out.

### 2.2 The new module — `starbridge-v2/src/branch_stitch_session.rs`

A NEW module gated `#[cfg(feature = "embedded-executor")]` ONLY (gpui-free,
deos-matrix-free, no GPU). It is purely additive — it does not edit `world.rs`,
`shared_fork.rs`, or `umem_membrane.rs`; it composes their existing public surface.

Proposed API (transport-free, `World`-native):

```rust
/// A shared verified world that participants fork, diverge in, and stitch back —
/// the operable distributed-Houyhnhnm primitive. Transport-free: no deos-matrix,
/// no wire types, no GPU. The settlement-sound gate is `settle_umem_stitch`.
pub struct BranchStitchSession {
    base: World,        // the live main / settlement tip
    focus: CellId,      // the cap-bounded cull centre (anti-amplification)
    max_depth: u8,      // the cull depth
}

/// One participant's divergent branch — a real independent World fork plus the
/// shared-ancestor baseline it stitches against.
pub struct Branch {
    world: World,
    baseline: UmemBranch,   // UmemBranch::from_frustum(mint-time cull)
}

pub struct StitchVerdict {
    pub settled_root: Option<[u8; 32]>,        // Some iff the state pushout is clean
    pub merged: Vec<UKey>,                     // the addresses that folded clean
    pub state_conflicts: Vec<UKey>,            // same-address ValueCollisions (fail-closed)
    pub dropped_authority: Vec<ConferredCap>,  // revoked-before-tip caps, linear-DROPPED
}

impl BranchStitchSession {
    pub fn open(base: World, focus: CellId, max_depth: u8) -> Self;

    /// Mint a cap-bounded fork for a participant (the cull is pinned to `focus`,
    /// anti-amplification by omission). Returns an independent verified Branch.
    pub fn fork(&self) -> Branch;                  // World::fork + MembraneFrustum::mint/rehydrate

    /// Advance the main tip — e.g. a RevokeCapability committed between branch
    /// and settlement (the non-monotone revocation the soundness turns on).
    pub fn base_mut(&mut self) -> &mut World;

    /// Stitch two diverged branches under the settlement-sound gate. Authority is
    /// read at the TIP (`settlement_held_at_tip(&self.base, focus)`), not at branch.
    pub fn stitch(&self, a: &Branch, b: &Branch) -> StitchVerdict;
}

impl Branch {
    /// Drive a real verified turn on this branch (World::commit_turn). Returns the
    /// receipt; refuses fail-closed if the executor rejects.
    pub fn drive(&mut self, turn: Turn) -> Result<TurnReceipt, BranchError>;
}
```

`stitch` is the body of `shared_fork.rs:1090-1154` re-homed verbatim against `World`/
`Branch` instead of `ForkHandle`/registry, returning `StitchVerdict` instead of the
deos-matrix `StitchOutcome`. The gate predicate, the conferred-cap gather, the
`settlement_held_at_tip` read, the `settles()` decision — all unchanged.

### 2.3 What moves where

* **Nothing leaves `umem_membrane.rs`.** `settle_umem_stitch`, `settlement_held_at_tip`,
  `stitch_projections`, `UmemBranch`, `ConferredCap`, `SettledUmemStitch` are already
  `pub`. The session calls them.
* **Nothing leaves `world.rs` / `shared_fork.rs`.** `World::fork`, `commit_turn`,
  `MembraneFrustum::mint`/`rehydrate` are already usable at `embedded-executor`.
* **New:** `branch_stitch_session.rs` — the glue that today only exists *inside*
  `ForkMembraneHost`. ~120 lines, all composition.
* **One line in `lib.rs`:** `#[cfg(feature = "embedded-executor")] pub mod
  branch_stitch_session;` (a shared-manifest edit — main loop owns it, quiet window).

### 2.4 `ForkMembraneHost::stitch_pair` becomes a thin adapter (slice 1 — STILL OPEN)

**Status: not yet done.** The session (slice 0) landed, but `stitch_pair`
(`shared_fork.rs:1072`) still carries its own body — it calls `stitch_projections` /
`settle_umem_stitch` directly and does NOT delegate to `BranchStitchSession::stitch`. This
adapter refactor remains the one open tail of the plan.

Once done, `stitch_pair` (`shared_fork.rs:1072`) re-expresses as:
look up the two `(World, MembraneFrustum)` registry entries → build a `BranchStitchSession`
view over `source_fork`/`focus` → call `session.stitch(...)` → map `StitchVerdict` into the
deos-matrix `StitchOutcome`/`ConflictObject` (the wire wrapping the chat lane needs). No
behavioral change; `stitch_pair_settlement_sound_production.rs` and
`two_instance_multiplayer_session.rs` stay green as the regression oracle.

This refactor is DEFERRED to slice 1 because `shared_fork.rs` is the file the cockpit
sibling lane is editing — slice 0 must not touch it.

### 2.5 Why it stays in starbridge-v2 (not `turn`/`cell`)

`World` lives in `starbridge-v2/src/world.rs` and wraps `dregg_turn::executor::TurnExecutor`
over a `dregg_cell::Ledger`. The primitive is World-shaped, so it cannot descend into
`turn`/`cell` without moving `World` itself (a far larger, separate refactor). The honest
minimal home is a new starbridge-v2 module at `embedded-executor`. A future `dregg-branch-
stitch` facade crate (re-exporting the session for non-starbridge consumers) is a later
nicety, not this plan.

---

## 3. The demo — distributed reversible capability-secure multiplayer

A NEW gpui-free binary crate `starbridge-apps/branch-stitch-multiplayer` (a workspace
member, the first app to depend on `starbridge-v2` with `embedded-executor` — no GPU, no
Matrix). It tells one story in three escalating beats and prints the arc (so it doubles as
a runnable narration and an integration test).

### 3.1 The shared world (ordinary cap-gated genesis — no GM superpower)

Mirror `two_instance_multiplayer_session.rs:55`'s `shared_world`: a `room` focus reaching
two distinct principals `ada` and `boris`, a shared `board`, each their own `doc_ada` /
`doc_boris`, a `gift` cap (the conferrable authority later revoked), and an `offstage` cell
GRANTED TO NOBODY (the confinement foil — it must never ride the cap-bounded cull).

### 3.2 Beat A — COMPATIBLE merge (distributed reversible multiplayer)

`session.fork()` for ada and for boris. Each drives DISJOINT verified turns:
ada → `doc_ada` + `board.field[0]`; boris → `doc_boris` + `board.field[1]`. `session.stitch`
→ `settled_root` is `Some`, `merged` names both addresses, `dropped_authority` empty. Main
is untouched until/unless the verdict is applied — divergence stayed imaginary.

*Shows:* reversible (forks independent, main pristine), distributed (a fork can cross a
serialization boundary via `MembraneFrustum::from_snapshot_bytes`, as the two_instance test
proves), witnessed (every `drive` is a real verified receipt under the executor key).

### 3.3 Beat B — CONFLICT refusal (fail-closed, both readings preserved)

ada and boris BOTH write `board.field[0]` to different values. `session.stitch` → the
same-address clash surfaces in `state_conflicts` (a `ValueCollision` at the EXACT umem
address), `settled_root` is `None` — the stitch does NOT settle until explicitly resolved.
Both attributed readings live; no silent last-writer-wins.

*Shows:* the single gated door is fail-closed; a genuine conflict is a first-class object,
not a lost write.

### 3.4 Beat C — the SETTLEMENT-SOUND gate bites (the proven theorem, live)

Both branches would confer the `gift` cap back. BEFORE settlement, `session.base_mut()`
commits a real verified `RevokeCapability` turn on MAIN (the tip). `session.stitch` reads
authority at the TIP: the revoked-before-tip `gift` confer is LINEAR-DROPPED into
`dropped_authority` (an `AuthorityRevoked` object), while the disjoint STATE pushout still
settles — orthogonal. Non-vacuous: a stitch BEFORE the revoke drops nothing (gift rides);
the SAME call AFTER drops gift. This is `revoke_before_tip_unsettleable` made operable.

*Shows:* capability-secure (a cap you've revoked cannot ride a stitch into your real world;
`offstage` never appeared at all — anti-amplification by omission), and the proven
`settlement_soundness` gate firing in a runnable app a stranger can read.

### 3.5 Step → machinery map

| Demo step | Real machinery |
|---|---|
| genesis shared world | `World::new` + `genesis_cell`/`genesis_install` + ordinary `capabilities.grant` |
| ada/boris fork | `BranchStitchSession::fork` → `World::fork` + `MembraneFrustum::mint`/`rehydrate` |
| divergent turns | `Branch::drive` → `World::commit_turn` (real verified, signed receipt) |
| disjoint merge | `stitch_projections` field-granular pushout (`umem_membrane.rs:346`) |
| conflict refusal | `UmemStitch` `ValueCollision` + `SettledUmemStitch::settles` fail-closed (`:518`) |
| revoke on main | `World::commit_turn(revoke_capability(...))` on the tip |
| gate bite | `settlement_held_at_tip` (`:482`) + `settle_umem_stitch` (`:557`) — the proven gate |
| offstage never rides | the frustum cull's confinement-by-omission (`shared_fork.rs` mint) |

---

## 4. The first build slice — **DONE**

**Slice 0 — the smallest end-to-end proof: two branches, one stitch, the gate bites — LANDED.**
Built WITHOUT touching `shared_fork.rs` (the cockpit sibling lane's file), as planned —
purely additive new files plus two main-loop-owned shared-manifest lines. The files below
now exist:

New files (disjoint, no clobber) — **both shipped**:
1. `starbridge-v2/src/branch_stitch_session.rs` — the §2.2 primitive. Composition only; it
   imports the existing public surface of `world`/`shared_fork`/`umem_membrane`. Does NOT
   edit those files.
2. `starbridge-apps/branch-stitch-multiplayer/Cargo.toml` + `src/main.rs` — the §3 demo
   crate. `dev-dependency`-free; `dependencies = { starbridge-v2 = { path = "../../starbridge-v2",
   default-features = false, features = ["embedded-executor"] } }`. A gpui-free binary that
   runs Beats A/B/C and prints the arc, with `assert!`s so it doubles as the acceptance test.

Shared-manifest edits (main loop owns, quiet window — the clobber hazard):
3. `starbridge-v2/src/lib.rs` — one line: register `pub mod branch_stitch_session;` under
   `#[cfg(feature = "embedded-executor")]`.
4. root `Cargo.toml` — add `"starbridge-apps/branch-stitch-multiplayer"` to `members` (and,
   since it is gpui-free, `default-members`).

Acceptance (the slice is done when):
* `cargo test -p starbridge-v2 --no-default-features --features embedded-executor` covers a
  unit test of `branch_stitch_session` (Beat A merges; Beat B refuses; Beat C drops
  revoked-before-tip authority, non-vacuous both ways) — the gate predicate parity with
  `branch_stitch::Stitch::settle` asserted directly.
* `cargo run -p starbridge-branch-stitch-multiplayer` prints the three-beat arc and exits 0.
* The existing `stitch_pair_settlement_sound_production.rs` /
  `two_instance_multiplayer_session.rs` remain green (untouched — they are the oracle for
  the slice-1 adapter that comes later).

Explicitly OUT of slice 0 (deferred):
* The `ForkMembraneHost::stitch_pair` → adapter refactor (§2.4) — touches `shared_fork.rs`,
  the sibling lane's file. Slice 1, after slice 0 is green.
* Any `dregg-branch-stitch` facade crate — later.
* Serialization-boundary ("two OS instances") delivery — slice 2 (the two_instance test
  already proves the boundary crossing works; the demo can add it as a second transport).

The through-line: **a turn is the exercise of an attenuable proof-carrying token over owned
state, leaving a verifiable receipt** — and branch-and-stitch is that, forked and rejoined
under a proven gate. Slice 0 is the smallest honest exhibit of it as an app a stranger can
run.
