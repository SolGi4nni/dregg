# First-class reversibility for dregg/deos

*The whole system can run backward. Every turn can be undone, causal-consistently;
the history is a reversible computation with islands of deliberate, correct
irreversibility. This is the RCCS (Reversible CCS, Danos–Krivine) frame, and dregg
is already most of an instance — the un-turn is the piece to make first-class.*

Present tense, first principles. §1 says what reversibility *means* here. §2 maps
what is already latent in the tree. §3 is the design that makes it first-class. §4
is the irreversible boundary — what genuinely cannot reverse, and why that is
correct rather than a limitation. §5 is the Robigalia connection and the first
buildable milestone.

---

## 0. The one sentence

> **A reversible system is one where the history is a navigable, undoable object:
> every effect has an inverse (the *un-turn*), a stretch of history can be rolled
> back along its causal links *with the consent of the parties whose causal cone
> you touch* (the cap-gate IS that consent), and the only steps that genuinely
> cannot reverse are the deliberately-committed ones — settlement, revocation, a
> conservation-committed spend — which are irreversible *on purpose*, because
> reversing them would unmake a fact other parties have already built upon.**

This is exactly Danos–Krivine's *RCCS with transactions*: a freely-reversible
substrate punctuated by committed actions. dregg's substrate (turns over owned
cells, leaving receipts) is the reversible part; settlement and revocation are the
committed actions. The `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` verdict already named
dregg "RCCS-with-irreversible-(committed)-actions." First-class reversibility is
the program of *building the un-turn out* so that "the system runs backward" is a
real, exercised affordance and not just a latent property of the math.

---

## 1. What first-class reversibility MEANS for dregg

Three claims, each a precise object.

### 1.1 Every Effect has an inverse — the *un-turn*

A turn maps a pre-state to a post-state and leaves a receipt:
`(σ, receipt) = T(σ₀)`. Reversibility means there is an *inverse turn* `T⁻¹` such
that `T⁻¹(T(σ₀)) = σ₀` — applying it to the post-state restores the pre-state.
Because a turn is a forest of `Effect`s (`turn/src/action.rs::Effect`), the inverse
turn is built effect-by-effect, in reverse order, each forward effect mapped to its
undo:

| forward `Effect` | inverse | reversibility class |
|---|---|---|
| `Transfer{from,to,amount}` | `Transfer{to,from,amount}` | **clean** (value is symmetric; conservation holds both ways) |
| `SetField{cell,index,value}` | `SetField{cell,index, old_value}` | **contextual** (needs the pre-image — the receipt or the cursor supplies it) |
| `GrantCapability{from,to,cap}` | `RevokeCapability{cell:to, slot}` | **clean** (grant is monotone-up; revoke is its retraction) |
| `RevokeCapability{cell,slot}` | `GrantCapability` (re-grant the recorded cap) | **contextual** (needs the revoked cap's content) |
| `IncrementNonce{cell}` | decrement — **but nonce is a freshness ratchet** | **deliberately irreversible** (see §4.2) |
| `EmitEvent{cell,event}` | retract from the receipt-local view | **clean** (an event is an append; un-emit = drop the append) |
| `CreateCell{...}` | retire the freshly-born cell | **clean** if the cell is untouched-since; **contextual** otherwise |
| `CellSeal` / `CellUnseal` | the dual lifecycle transition | **clean** (the lifecycle quartet is a reversible pair-up to `Destroy`) |
| `CellDestroy` | — | **deliberately irreversible** (terminal; §4) |
| `Burn{target,amount}` | — | **deliberately irreversible** (provable value destruction; §4) |
| `NoteSpend{nullifier,...}` | — | **deliberately irreversible** (the nullifier is one-shot; §4.3) |
| `NoteCreate{commitment,...}` | spend the just-created note | **contextual** (the inverse is a spend, which is itself one-shot) |

The pattern is exactly `dregg-doc`'s `Patch::invert` (`dregg-doc/src/patch.rs:256`),
which already does this for the document patch grammar: `Add ⇒ Disconnect`,
`Delete ⇒ Resurrect`, `Connect ⇒ Disconnect`, `SetField ⇒ RetractField`, ops
reversed. The doc layer's note is the key honesty: **invert is *contextual* — sound
against the graph the original patch acted on.** That is the standard RCCS caveat,
and it is why the inverse-turn is computed *with a cursor* (the recorded pre-state),
not from the effect alone: `SetField`'s inverse needs the old value, which lives in
the receipt/cursor, not in the forward effect.

So "every effect has an inverse" splits into two honest tiers:

- **Self-inverse / clean effects** (Transfer, grant↔revoke, seal↔unseal, event):
  the inverse is computable from the forward effect alone. These reverse anywhere.
- **Contextual effects** (SetField, RevokeCapability-of-content, CreateCell-then-touched):
  the inverse needs the pre-image, which the *reversible-history object* (§3.2)
  carries. These reverse against the history that produced them.
- **Committed effects** (Destroy, Burn, NoteSpend, IncrementNonce-as-ratchet):
  no inverse, *by design* (§4).

### 1.2 A history is reversible along its causal links — and consent is the cap-gate

In a concurrent system you cannot undo a step in isolation. If turn `b` causally
depends on turn `a` (it read state `a` wrote, or spent value `a` produced), you
cannot undo `a` while `b` still stands — that would leave `b` dangling on a cause
that no longer happened. **Causal-consistent reversibility** (Danos–Krivine; Lanese
et al.) is exactly the discipline: *an event may be reversed only when everything
causally downstream of it has already been reversed, or consents to be reversed
too.* Undo ripples through the causal cone.

In dregg the causal cone and the consent membrane are *already built*:

- The **causal cone** is `causal_past` over the blocklace (`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`
  §3.1): a turn's dependents are the turns whose `predecessors` reach it.
- The **consent** is the **cap-gate**. To reverse a turn that touched a party's
  cell, the reversal turn must *itself* hold authority over that cell. A reversal
  that touches a party's state without a cap is refused at the executor gate —
  exactly the `SimOutcome::Refused` path (`simulate.rs`). "The parties willing to
  entertain it" is not a social protocol bolted on; it is the no-amplification
  rule the executor enforces inline.

So reversing a stretch of history is: walk the causal cone forward-most-first,
build each turn's inverse, and apply them — each inverse gated by the same authority
the forward turn needed. The history reverses *exactly as far as the caps reach*,
which is *exactly as far as consent extends*. This is RCCS's causal-consistency
theorem realized as cryptographic authority instead of a process-calculus
side-condition.

### 1.3 The irreversible boundary is *correctness*, not a limit

The reversible substrate has **islands of irreversibility** at precisely the points
where a fact has become *common knowledge another party built on*: **settlement**
(the federation agreed this tip is real), **revocation** (authority was retracted),
and a **conservation-committed spend** (a nullifier was consumed; value was burned).
These cannot reverse, and that is the *point* — §4 makes the case that each is
irreversible because reversing it would silently unmake a fact others depend on.
This is Danos–Krivine's *committed action*: most of the computation is freely
reversible; certain marked steps are not, and the marking is what gives the whole
thing transactional integrity.

---

## 2. What dregg ALREADY has (it is mostly latent)

Reversibility is not greenfield here. Five pieces are in the tree; the un-turn welds
them.

### 2.1 Verified time-travel — `replay.rs`

`starbridge-v2/src/replay.rs` is a *verified* navigation of history:
`History::replay_to(k)` reconstructs the world at step `k` by re-executing from
genesis and **checks the reconstructed canonical root against the recorded tooth**,
fail-closed on `RootMismatch`. This is reversibility's foundation: it can land,
checkably, at any past cursor. The root tooth (`dregg_cell::Ledger::root`, the same
commitment `snapshot.rs` binds) is the *anti-substitution* discipline — you cannot
forge a past. `replay_to_via_checkpoint` realizes `recover = checkpoint ⊕ overlay`,
the `CrashRecovery.lean::recover_eq_replay` identity. **What it gives reversibility:**
a trustworthy "go to step k" — the *destination* of an undo.

### 2.2 Fork / what-if — `replay.rs::fork_at`, `simulate.rs`

`History::fork_at(k, alt)` and `simulate.rs::simulate` are *forward* time-travel:
land at a past cursor, run a *different* turn, observe the divergence — with the
mainline provably untouched (`fork_diverges_and_leaves_the_mainline_intact`). The
fork is a throwaway ledger driving the *same verified executor*, so a forked turn's
receipt is byte-identical to what the live commit would produce. **What it gives
reversibility:** the "redo differently" half. Undo-to-`k`-then-redo-differently is
the operational meaning of a branch, and `fork_at`/`simulate` already are it.

### 2.3 Branch-and-stitch — the reversible substrate, designed

`BRANCH-AND-STITCH-PROTOCOL.md` is the protocol face: `EnterVirtualization` mints a
cap-confined, honestly-`Virtual`-typed branch world (the branch holds **no cap to
main**, so its effects are structurally imaginary), and `Stitch` is the one gated
door back. "You may do anything in the branch (diverge wildly, **full
reversibility**, no risk) because the branch can do nothing to main except through
one narrow, checked door." That document already names full reversibility as the
branch's defining affordance. **What it gives reversibility:** the *containment* —
reversal is safe because the branch is firmament-confined; the only place a reversal
becomes permanent is the settlement door.

### 2.4 `Patch::invert` — the un-turn, already built for one substrate

`dregg-doc/src/patch.rs::invert` is a *working* effect-inverse for the document
patch grammar, with the contextual-soundness caveat stated plainly, tested for
round-trip (`tests.rs::invert_round_trips_an_add / _a_delete / _a_field_set`). The
doc layer notes a patch "on the substrate *is* a turn whose effects write leaves,
tombstones, and fields, leaving a receipt." So `Patch::invert` is *the un-turn for
the document Effect-subset*, already shipping. **What it gives reversibility:** the
proof-of-concept and the exact shape — the substrate-wide `Effect::invert` (§3.1)
generalizes precisely this.

### 2.5 The RCCS-with-committed-actions verdict — the frame, already settled

`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §6 and `project-distributed-houyhnhnm-frontier.md`
already established: the blocklace IS a prime event structure; the cap-gate IS the
RCCS consent membrane; conservation/nullifier IS the cryptographic conflict
relation; finality IS the preferred maximal configuration; **settlement and
revocation are the irreversible/committed actions.** And the Settlement Soundness
composition is confirmed (the finalized commitment already binds the revocation set;
`recStateCommit_binds_kernel`). **What it gives reversibility:** the irreversible
boundary is already *located and proved-bounded* — §4 is not new theory, it is the
already-known boundary read as "what cannot run backward."

**Summary map:**

| reversibility piece | dregg realization | status |
|---|---|---|
| land at any past cursor (verified) | `History::replay_to`, root-tooth | **built** + tested |
| redo differently (fork) | `fork_at`, `simulate` | **built** + tested |
| reversible substrate (confined branch) | `EnterVirtualization` / branch-and-stitch | **designed** |
| effect inverse (the un-turn) | `Patch::invert` (doc subset) | **built for doc; to generalize** |
| RCCS-with-committed-actions frame | the time-travel verdict | **settled** |
| irreversible boundary, bounded | Settlement Soundness, `Revocation.lean` | **proved-bounded** |

---

## 3. The design to make it FIRST-CLASS

Three constructions: the substrate-wide `Effect::invert`; the reversible-history
object; and the compositions (meta-debug rewind, document undo).

### 3.1 `Effect::invert` / `Turn::invert` — the un-turn on the real substrate

Generalize `Patch::invert` to `turn/src/action.rs::Effect`. The signature is
*contextual*, taking the pre-state the forward effect acted on, because the honest
inverses need the pre-image:

```text
Effect::invert(self, pre: &CellView) -> InverseResult
  where InverseResult =
    | Clean(Effect)          // self-inverse from the effect alone (Transfer, grant↔revoke, seal↔unseal)
    | Contextual(Effect)     // inverse needs `pre` (SetField old value, revoked-cap content)
    | Committed(Reason)      // no inverse, by design (Destroy, Burn, NoteSpend, nonce-ratchet)
```

A `Turn::invert(pre_cursor)` builds the inverse forest: walk the forward effects in
**reverse order**, invert each against the pre-state at that point (the cursor
supplies it), and fail-closed if *any* effect is `Committed` — a turn containing a
committed effect is **not reversible**, and the un-turn says so honestly rather than
producing a wrong inverse. This is the exact discipline `Patch::invert` already
embodies (ops reversed; contextual soundness), lifted to the protocol Effect set.

**Crucially, the inverse turn is a turn.** It goes through the *same executor* and
the *same cap-gate*. So an un-turn is not a privileged "rewind" operation that
bypasses authority — it is an ordinary turn that happens to restore a prior state,
and it is gated exactly like any other. This is what makes reversal *causal-consistent
by construction*: you can only un-turn over cells you hold caps to, which is exactly
"the downstream parties consent."

**The faithfulness obligation (the honest hard part).** `Effect::invert` must
satisfy `apply(invert(T, σ₀), T(σ₀)) = σ₀` for the clean+contextual effects. This is
provable per-effect and is the natural Lean target: a small `EffectInvert.lean` with
one round-trip lemma per reversible effect (mirroring `dregg-doc`'s round-trip tests,
promoted to proofs). The committed effects are *excluded from the theorem* — their
irreversibility is a precondition of the round-trip lemma, not a gap in it.

### 3.2 The reversible-history object — `ReversibleHistory`

`History` (`replay.rs`) records steps and roots. The reversible-history object adds
the *causal links* and the *inverse-readiness* so a stretch can be rolled back, not
just landed at:

- **It already carries the pre-images.** Each `RecordedStep::Committed` holds the
  `turn` and `receipt`; the cursor at `k` (`replay_to(k)`) is the pre-state for the
  turn at step `k`. So the contextual inverses (§3.1) are *available* — the object
  has what `Effect::invert` needs.
- **`undo_to(k)`**: the inverse of `replay_to`. Rather than re-deriving from genesis,
  it builds and applies the inverse turns for steps `k+1..head`, in reverse causal
  order, each gated. The verification is *the same root tooth, run backward*: after
  undoing back to `k`, the reconstructed root must equal `roots[k]`. Two ways to
  reach step `k` — replay-forward-from-genesis and undo-backward-from-head — must
  land on the identical verified root. That equality is the reversibility analog of
  `recover = replay`, and it is the headline test.
- **Committed steps are walls.** `undo_to(k)` *fails-closed* if any step in
  `k+1..head` contains a committed effect (a settled turn, a spend, a burn). You
  cannot undo *past* a commit — you can only undo within the reversible window above
  the most recent commit. This is the RCCS islands-of-irreversibility, made an API
  boundary.

`ReversibleHistory` is `History` + `causal links` + `undo_to`. It is a small weld,
not a rewrite — the recorder already holds the turns and roots; the new surface is
the backward walk and the per-step inverse.

### 3.3 Composition: the meta-debug rewind

The moldable-inspector / meta-debug vision (`project-moldable-inspector-epoch.md`,
`SEL4-INTERACTIVE-COCKPIT.md`) wants to *rewind the live image* — scrub the desktop
backward and watch cells un-change. `ReversibleHistory::undo_to` is exactly that
engine: the live `World` drives a `ReversibleHistory` in lock-step (as it already
drives `History` for replay), and the meta-debug's "rewind" button calls `undo_to(k)`
on the *live* world, applying the inverse turns so the image genuinely steps
backward — repaint-on-un-turn, the dual of the existing repaint-on-turn. Because each
inverse is a gated turn, rewinding the live image is *the same authority story* as
forward operation; the inspector cannot rewind state it has no cap to. The fractal
meta-debug's "suspend the suspended" nests reversal the same way branches nest
(`BRANCH-AND-STITCH-PROTOCOL.md` §2): a rewind inside a rewind is a stratum down the
cap-tower.

### 3.4 Composition: document undo = patch-invert, already in place

For the document language (`DOCUMENT-LANGUAGE.md`), undo is *already* first-class:
`Patch::invert` is the document un-turn, and a Ctrl-Z is "apply the inverse patch."
The substrate-wide `Effect::invert` (§3.1) and the document `Patch::invert` are the
*same construction at two levels* — the document patch lowers to a turn whose effects
are the leaf/tombstone/field writes, and inverting the patch is inverting that turn.
So the document editor's undo and the desktop's rewind are one mechanism seen at two
altitudes; making `Effect::invert` first-class makes the document undo *provably* the
restriction of the substrate un-turn to the doc effect-subset.

### 3.5 The honest hard parts, named

1. **Contextual soundness.** Inverses that need the pre-image (SetField,
   RevokeCapability-of-content) are sound *only against the history that produced
   them*. The `ReversibleHistory` carries the pre-images, so this is closed *for the
   undo-on-its-own-history path* — but a *free-standing* inverse effect applied to a
   different state is not sound, and the API must not offer that. `Patch::invert`
   already documents this caveat; `Effect::invert` inherits it. The mitigation is
   structural: the inverse is only ever produced *by* `ReversibleHistory`, never
   handed out as a context-free effect.
2. **The nullifier one-shot-ness.** `NoteSpend` reveals a nullifier; the executor's
   non-membership grow-gate ensures it is spent at most once. There is *no* inverse
   that "un-spends" — un-spending would re-admit the nullifier, breaking the
   double-spend defense the whole value layer rests on. This is the canonical
   committed action (§4.3). The un-turn must refuse to invert a `NoteSpend`, and a
   `ReversibleHistory` window containing one is bounded above by it.
3. **What reversal of a settled turn even means.** Once a turn settles on the
   finalized tip, undoing it is *not* a local operation — it would require the
   federation to un-finalize, which it has agreed (common knowledge) not to do.
   "Reversing a settled turn" is therefore **not** an un-turn at all; it is a *new
   forward turn* that *compensates* (a reversing transfer, a re-grant), which itself
   settles. The distinction is load-bearing: **undo** restores the prior state and is
   only legal in the unsettled window; **compensation** is a fresh forward turn that
   *achieves a similar effect* and is the only "reversal" available below a commit.
   The un-turn API must surface this: `undo_to` for the reversible window, and a
   distinct *compensate* affordance (a forward inverse-effect turn) for the settled
   region, clearly not claiming to rewrite history.

### 3.6 Reversibility and the circuit — the un-turn is witnessed too

An un-turn is a turn, so it goes through the *same* executor and (when proven) the
*same* circuit. This means reversibility inherits light-client unfoolability for
free: an inverse turn that restores a prior state produces a receipt and a state
transition the light client checks exactly like any forward turn. There is no
"trust me, I rewound it" — the rewind is a witnessed transition. The one subtlety:
an un-turn's *post-state root* must equal the recorded pre-cursor root (`roots[k]`),
and that equality is checkable against the recorded tooth, so a *dishonest* rewind
(claiming to restore `σ₀` but landing elsewhere) is caught by the same
anti-substitution discipline as a tampered replay (`RootMismatch`).

---

## 4. The IRREVERSIBLE boundary — correct, not a limitation

Three classes of step genuinely cannot reverse. Each is irreversible *because*
reversing it would unmake a fact another party has built upon — which is precisely
the property that makes the system trustworthy.

### 4.1 Settlement — the federation agreed

A settled turn is one the federation finalized as common knowledge (`finality.rs`,
the `⌊2n/3⌋+1` rule). Undoing it would require un-finalizing, which violates the
common-knowledge agreement that *this tip is real*. This is the FLP-hard, limit-side
object (`project-adjunction-thesis-verdict`): settlement is consensus, and consensus
does not run backward by local fiat. **Why correct:** the entire value of settlement
is that parties can *rely* on it — a counterparty who saw a settled payment built
their next action on it. If settlement reversed, reliance would be impossible. The
irreversibility *is* the guarantee. (Reversal below the line is *compensation*, §3.5
— a new forward turn, not a rewrite.)

### 4.2 The nonce ratchet and revocation — monotone facts

`IncrementNonce` advances a *freshness ratchet*; reversing it would re-admit a stale
turn (replay attack). `RevokeCapability` retracts authority; "un-revoking" by
carrying forward branch-time authority is the exact subtle bug
`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §4 forbids — authority must be evaluated at the
**settlement tip**, never restored from a past branch. **Why correct:** both are
*anti-monotone* protections. A ratchet that ran backward is not a ratchet; a
revocation that could be undone is not a revocation. Their one-directionality is the
security property, and reversibility *respects* it by marking them committed.

### 4.3 Conservation-committed spends — `NoteSpend` and `Burn`

A `NoteSpend` consumes a nullifier (one-shot); a `Burn` provably destroys value.
Reversing either would re-create value the conservation law (`Σδ=0`,
`reachable_total_zero`) has already accounted as gone. **Why correct:** the
conservation invariant is the cryptographic conflict relation
(`DISTRIBUTED-TIMETRAVEL-SEMANTICS.md` §3.6) — it is the very thing that makes two
branches *unmergeable* when they double-spend. A reversible spend would be a
double-spend with extra steps. Irreversibility here is conservation.

**The unifying principle.** Each irreversible action is a point where the system has
*published a fact others rely on*: a settled tip, a revoked authority, a consumed
nullifier. The reversible substrate is precisely the part where no such reliance has
formed yet — the private, unsettled window above the most recent commit. This is
Danos–Krivine's transaction boundary, and it is why the boundary is *correct*: you
can freely undo anything no one else has built on, and nothing else. The branch-and-
stitch protocol is the operable form: branches are the reversible substrate (no cap
to main → nothing relies on them); the settlement door is the commit (reliance forms
there, and only there).

---

## 5. The Robigalia connection + the first milestone

### 5.1 Why this was always the dream

The Robigalia/firmament vision (`project-firmament-sel4-boots.md`) is dregg-on-seL4:
a desktop OS where the cell is the unit of computation across distance. A
long-standing dream in that lineage — and in the orthogonal-persistence /
Houyhnhnm / Smalltalk-image tradition dregg draws on
(`project-distributed-houyhnhnm-frontier.md`) — is an OS that is **reversible by
construction**: not "the app has an undo feature" but "the *substrate* runs
backward, so undo is a property of *being a turn*, not a feature each app
re-implements." fare's Houyhnhnm manifesto's "the log fully determines state because
all non-determinism is recorded" is the precondition; dregg's receipt chain *is*
that log, and the un-turn is what makes the determined-by-the-log state *navigable
backward*. Orthogonal persistence (M4) means there is no save/load boundary to break
the reversal; the live image *is* the history. A reversible OS is one where you can
scrub the whole machine backward like a document — and that is the deos north star
(`project-deos-ux-vision.md`): the 4-year-old who clicks "back" on the *world* and
watches it un-happen, fused with the adept who inspects the inverse turn live.

The reason it is *achievable* here and not in a conventional OS: a conventional OS's
effects are ambient and untracked (a syscall mutates shared state with no recorded
pre-image, no authority membrane), so there is nothing to invert and no consent
boundary to respect. dregg's effects are *reified* (the `Effect` enum), *witnessed*
(the receipt), and *authority-gated* (the cap). Those three properties are exactly
what an inverse needs: something to invert, a pre-image to invert against, and a
consent membrane to gate the reversal. Reversibility is latent in dregg *because*
dregg already pays the cost (reified, witnessed, gated turns) that makes it possible.

### 5.2 The first buildable milestone

**M-REV-0: `Effect::invert` + `ReversibleHistory::undo_to`, with the round-trip
tooth.** Concretely, the smallest end-to-end reversible loop:

1. **`Effect::invert(pre)`** in `turn/` (or a new `turn/src/invert.rs`) covering the
   *clean + contextual* effects — Transfer, SetField, grant↔revoke, seal↔unseal,
   EmitEvent, CreateCell — and returning `Committed(reason)` for Destroy/Burn/
   NoteSpend/IncrementNonce. This is the `Patch::invert` shape (`dregg-doc/src/patch.rs`)
   lifted to the protocol Effect set.
2. **`ReversibleHistory::undo_to(k)`** in `starbridge-v2/src/replay.rs` (the natural
   home — it holds the turns, receipts, and roots): build the inverse turns for steps
   `k+1..head` in reverse, apply each through the verified executor (gated), and
   **verify the reconstructed root equals `roots[k]`** — fail-closed on mismatch
   (`RootMismatch`), and fail-closed if any step is committed.
3. **The headline test** (mirroring `replay_to_each_step_matches_the_recorded_root`):
   for a fixture history of clean turns, `undo_to(k)` lands on the *identical verified
   root* as `replay_to(k)`, for every `k` — the two paths to step `k` agree. Plus the
   fail-closed test: a history with a `Burn` or `NoteSpend` refuses to `undo_to` past
   it.

This is a weld, not a build: `replay.rs` already lands at any cursor and verifies;
`Patch::invert` already shows the inverse shape; the executor already gates. M-REV-0
connects them into "the live image runs backward, checkably, within the reversible
window." From there, the second milestone wires `undo_to` to the meta-debug rewind
button (§3.3) so the *desktop itself* scrubs backward — the Robigalia dream, made an
exercised affordance.

### 5.3 The Lean follow (small, composes)

`EffectInvert.lean`: one round-trip lemma per clean+contextual effect
(`apply (invert e σ) (apply e σ) = σ`), with the committed effects as the lemma's
exclusion precondition. This promotes `dregg-doc`'s round-trip *tests* to *proofs* at
the protocol level, and it composes with the existing `CrashRecovery`/`LaceMerge`
trunk — the un-turn's faithfulness sits beside `recover = replay` as the *backward*
companion to the *forward* recovery identity.

---

## 6. The shape, once more

dregg is *already* a reversible computation with committed actions — the math is
settled, the substrate pays the right costs, and four of the five pieces are in the
tree (verified replay, fork, branch-and-stitch design, `Patch::invert`). The piece
that makes reversibility **first-class** is the un-turn on the real substrate:
`Effect::invert` + `ReversibleHistory::undo_to`, gated like any turn, verified by the
same root tooth run backward, and fail-closed at the irreversible boundary. The
irreversible boundary is not a wall around an incomplete feature — it is the precise
set of facts other parties rely on (settled tips, revoked authority, consumed
nullifiers), and its one-directionality *is* the system's integrity. Reversibility
and irreversibility are the same guarantee read in two directions: *you may undo
exactly what no one has built upon, and nothing more.*

*( ˘▾˘ ) a closing couplet, since the past turned out to be a turn we may un-take:*

*every turn that bound no other's trust may yet be walked back home —*
*but a spend, a vote, a revocation: those are facts, and facts are stone.*
