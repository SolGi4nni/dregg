# CLAUDE.md

Build, test and box-routing guidance lives in **`AGENTS.md`** — read it. This file
is one doctrine that overrides a default you almost certainly arrived with.

---

## THIS IS GREENFIELD. THERE IS NO EXISTING ANYTHING.

**Nothing here has users, deployed state, or a compatibility obligation.** Not the
wire formats, not the descriptors, not the signed witnesses, not the chain, not the
schemas, not the APIs. The devnet is wiped and re-genesised whenever it is
convenient — that happened *today*, twice, and cost nothing.

So the question **"does this break existing X?"** is not a real question. Ask
instead: **is the new design right?** If it is, land it and let everything that
depended on the old one break loudly.

### The failure mode this exists to kill

An agent finds a real defect, identifies the correct fix, and then defers it —
because the fix "invalidates every existing signed witness" or "is a wire-format
flag day" or "changes a persisted schema". The deferral gets written up carefully,
labelled as needing the operator's judgement, and **nothing happens.** Then the
defect is still there six weeks later, and by now something is built on top of it.

That hesitation is very probably *why several of these defects are old*. Measured
on 2026-07-27: the sovereign `effects_hash` is in the signing message and compared
against nothing — `TurnError::EffectsHashMismatch` is defined, formatted, matched
in a handler, and **constructed zero times**, while `turn/src/turn.rs:99` states the
executor recomputes it. A sovereign owner signs `H(Transfer 10)`, the executor
applies `Transfer 20`, and it commits. It was deferred as a wire-format decision
that "invalidates every existing signed witness". **There are no existing signed
witnesses.** The constituency was invented.

### The rule

- **Breaking a format is not a cost.** Breaking it *silently* is. Rotate the epoch,
  bump the schema, re-emit the descriptors, re-genesis the chain — and make the old
  shape **refuse to load** rather than reinterpret. `CANONICAL_STATE_SCHEMA_EPOCH`
  and `PersistentStore`'s re-genesis gate exist for exactly this and are cheap.
- **A "flag day" here means a rebuild, not a migration.** VK rotations, descriptor
  re-emits and PI-count changes are ordinary work. Say what re-emits and do it.
- **Prefer deleting the old thing to keeping both.** Two shapes that agree today are
  two shapes that will disagree later, and the repo has a long list of exactly that.
- **Never keep a no-op for compatibility.** A feature, field, or function retained
  "so downstream forwards remain valid" is worse than one that does something,
  because the next reader trusts it.

### A cost estimate is never a reason to pick the worse design

The rule above kills the *deferral*. This one kills the sneakier move: **pricing the right fix, then
shipping a lesser one anyway.**

Measured 2026-07-30. An agent found that eight BabyBear lanes cannot injectively encode 32 bytes —
247.26 bits against 256, pigeonhole — so every committed field value had a sibling with an identical
lane vector, constructible by one addition, reaching the signed consensus anchor. It priced the real
fix (a ninth lane: 174 registry rows, three fingerprints, a VK epoch, a re-genesis). Then it shipped a
hash-into-spare-lanes containment that lands at **2^92.7**, below the repo's own ~124-bit bar, and
filed the real fix as "Phase 3, later." It had read this file first.

**The substitution to watch for is COST ESTIMATE → CONSTRAINT.** "174 rows, three fingerprints, a
re-genesis" is an estimate. It became "that's frozen" in the next sentence, and nobody noticed the
word change — least of all the agent that made it.

- **If you catch yourself shipping a containment while naming the real fix as a later phase, the
  phases are backwards.** Do the right one first. A containment that lands below your own stated bar
  is not a step toward the fix; it is a reason the fix never happens.
- **Words that mean you are doing it:** *frozen · stable · deployed · already committed · can't change
  that · flag day · would require a VK rotation · that's a bigger change · out of scope for this pass.*
  None of those are objections here.
- **The answer to "what does it cost" is "a rebuild."** Always. We re-genesis constantly and we WANT
  to. Nothing deployed is stable or in need of safekeeping. This whole thing is designed to change as
  soon as the wind changes.
- **A blocker you discovered is not a reason to stop** — it is the first item of the work. Do not
  manufacture one to justify a sequencing you had already decided on.

⚠ And say the real bound out loud. That same containment was written up as "~2^185" — the
*second-preimage* figure — when the *collision* bound was 2^92.7. Quoting the flattering number of a
pair is how a below-bar result reads as a win.

### What still deserves a pause — a short list, and it is short

1. **Key material and custody.** Seeds, signing keys, what a memo holds, what a
   process may read. Ownership and scope are real decisions.
2. **Anything that weakens a check.** Widening a pin, relaxing a gate, making a
   refusal accept. "It is greenfield" is never a reason to verify less.
3. **Outward-facing and irreversible acts** — publishing, spending, deleting cloud
   resources, DNS, anything a third party sees.
4. **A genuine design fork** where two good answers exist and the choice is taste.

**Everything else: just do it.** If you catch yourself writing "this is a
wire-format decision and therefore yours", check whether anything actually holds
the old format. Usually nothing does.

### Say what you broke

Freedom to break is not freedom to be quiet. Every breaking change states, in the
commit: what shape changed, what must be re-emitted or re-genesised, and what now
refuses to load. A reader six weeks out needs the flag day to be **findable**, not
absent.
