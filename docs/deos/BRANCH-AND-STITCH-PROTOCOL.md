# The branch-and-stitch protocol — consensual virtualized pasts, contained by nesting, stitched back lossily

This is the protocol face of `DISTRIBUTED-TIMETRAVEL-SEMANTICS.md`: how parties *do* distributed
time-travel — fork a past, explore it freely, and stitch the useful part back into main — soundly.
Present-tense; first-principles. Most of it is reuse; the genuinely-new surface is two small turns.

## The shape in one breath

Parties co-consent to **virtualize a past** (a joint turn off a past `WitnessCursor` that mints a
shared, cap-confined, honestly-typed *branch world*); the branch is safe to diverge in *because the
nesting confines it* (it holds no cap to main — its side-effects are structurally imaginary); and a
divergent branch **stitches itself back** through one gated door (a possibly-lossy reconciliation the
branch authors, conserving + authority-checked + conflict-rejecting at settlement). The nesting *is*
the safety; the single door *is* the soundness.

## 1. The consensual-branch handshake (`EnterVirtualization`, a new joint turn)

A branch is opened by a **joint turn** (`FamilyBinding` / the existing joint-turn machinery): the
parties co-sign, each consenting via its own cap, to fork a *shared* child world off a past
`WitnessCursor`. The handshake mints the branch world plus a **branch-cap** for each party.

Load-bearing: the branch is **honestly typed**. Its liveness-type (`Rehydration`) is `Virtual/Branch`,
never `Main/Live`, *by construction* — the type cannot lie about which-kind-of-true you are in. "We
agree we are in a virtualized past" is therefore not a convention but a co-signed, witnessed fact.

Reused: joint-turns (`FamilyBinding`), the membrane (the shared branch is a per-party-projected
surface), the derived liveness-type. New: the `EnterVirtualization` joint turn that mints the
branch world + the typed branch-caps.

## 2. Nesting IS the safety (capability confinement + the one door)

The intuition "the nesting level adds safety" is exact, and the mechanism is **firmament
confinement**, not a promise:

- **Containment is capability confinement.** A branch turn can only touch cells the branch holds caps
  to — *branch* cells. To touch a *main* cell you need a main-cap, which the branch **does not hold**.
  So branch side-effects *cannot leak* to main. This is fare's "all destructive experiments happen in
  branches never merged into official reality — the errors remain imaginary," made a cap fact.
- **The only door to main is a gated settlement** (§3). A branch reaches main *only* through an
  explicit settlement turn, and that door is the **Settlement Soundness gate** (`DISTRIBUTED-
  TIMETRAVEL-SEMANTICS.md` §verdict): conserves (no value conjured), current-authority (the
  finalized-tip revocation set, not the branch's stale authority), no-conflict (a branch spend of
  value main already spent = a nullifier collision = rejected).
- **It nests recursively.** A branch inside a branch is another stratum *down* the cap-tower (meta is
  down) — same confinement, same gate at each level. The fractal meta-debug's "suspend the suspended"
  and the sandbox-within-the-sandbox are the *same* firmament mechanism. The nesting is the firmament.

So: **you may do anything in the branch (diverge wildly, full reversibility, no risk) because the
branch can do nothing to main except through one narrow, checked door.** Divergence stays imaginary
until a deliberate stitch.

## 3. The lossy stitch-back (`Stitch`, the new DX primitive)

A divergent branch **authors a reconciliation forest** that merges its useful essence into main —
allowed to be **lossy**, which is the point:

- The **I-confluent / rhizomatic** parts merge cleanly (monotone — the part that *cannot* conflict
  just merges).
- The **conflicting** parts (conservation, authority) the author must resolve, and **linear logic
  forces *explicit* drops** (fare Ch5: "when writing an upgrade operator you must explicitly drop any
  data you don't care about, so you cannot lose information by mistake or omission"). Lossy is not
  sloppy — it is deliberate, typed loss.
- The result is a turn main's gate admits. "Doesn't preserve everything" is a feature: you explored a
  wild branch, found one good thing, stitch *that* back, drop the rest — cherry-picking the insight
  out of a failed experiment. Explorations are never wasted.
- **The correctness criterion is the pushout.** Patch theory (`DOCUMENT-LANGUAGE.md` — the same
  event-structure/RCCS object in version-control clothes) gives the principle: a stitch is a morphism
  into the colimit; the lossy part is the universal-property quotient. Patch theory does not *build*
  the stitch — it tells us whether we built it right.
- **A cross-party stitch is a partial turn with holes the consenting parties fill** (the partial-turn
  / promises thread — the hole *is* the consent point).
- **Spaceage = semi-automated:** auto-merge the confluent part; surface only the genuine conflicts for
  the author to drop-or-transform (fare's "the system automates a lot; the programmer focuses on the
  intrinsic non-trivial transformations").

## What is new vs. reused

**Reused** (in-tree or already designed): joint-turns/`FamilyBinding` (the handshake), the membrane +
liveness-type (honest virtual surface), capability confinement (containment), Settlement Soundness
(the door), conservation/nullifiers (conflict rejection), linear-logic-drop (explicit loss),
partial-turns (cross-party holes), the cap-stratified meta-tower (recursive nesting).

**New** (the small protocol): (1) the `EnterVirtualization` joint turn (mint the branch world + typed
branch-caps); (2) the `Stitch` reconciliation primitive (the semi-automated, linear-drop-forced,
pushout-correct merge-into-main through the Settlement Soundness gate).

Two small turns; everything else is composition. The branch-and-stitch protocol is distributed
time-travel made *operable* — and houyhnhnm "virtualization as branching" made *cap-secure and
witnessed*.
