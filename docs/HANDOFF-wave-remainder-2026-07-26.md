# Handoff — the three wave items NOT landed, 2026-07-26

*Written by the recovery session that picked up the campaign after the prior one
(`d527daf6`) hit the weekly limit mid-wave. Six items were out; three landed, three did
not, and these three did not because they are **larger than they were estimated**, not
because there was no time. Each entry says what it actually needs, so the next session
does not re-derive it.*

Landed: the production-caller census, the limb-PI wiring, the bot archive flip +
`MAX_TURNS`. See `git log` for those.

---

## 1. The DSL trio — `lose:` / `player_hp:` / `consumable`

**Estimated "~20 / cheap / ~30 lines, no new `StateConstraint` variant needed". The line
count is plausible; the design decision inside it is not sized by it.**

State at HEAD, verified: all three **parse** (`dungeon-on-dregg/src/dsl/parse.rs:504`,
`:523`, `:556`) and reach the IR (`dsl/ir.rs:534`, `:541`, `:549`). The compiler then
refuses each **by name**, fail-closed — `dsl/compile.rs:708`, `:726`, `:732`, listed in
the module header's "honest residuals" block. That is the residual done right; the work is
lowering it, and the refusal is the tooth that keeps it honest meanwhile.

**Why `lose:` is not symmetric with the win objective.** `objective:` lowers as a
`ChoiceSpec` — a `Claim` choice the player *takes*, gated on `has_<item> >= 1`, writing
`dungeon_won = 1` (`compile.rs:662`). A lose condition has no choice to hang on: it is a
terminal PREDICATE over a world flag (`flag >= at_least`), and nothing fires it. So
lowering it means picking one of:

* **(a) Co-write.** Every choice whose writes push `flag_<f>` to `>= at_least` also writes
  `dungeon_lost = 1`. The compiler does know every write statically, so this is
  mechanical — but it needs the threshold comparison at compile time, and `at_least`
  interacts with flags that rise more than one step.
* **(b) Gate everything.** `dungeon_lost = 0` becomes a gate term on every other case.
  This collides with the grammar's stated monotonicity ("a flag rises, an item is held,
  and nothing ever closes" — `compile.rs:35`) and multiplies teeth per case.

**This is a design decision inside a proof-carrying compiler, and it should be taken
deliberately.** (a) is the smaller change and preserves the monotone reading; (b) is the
one that makes "lost" actually stop play. They are not equivalent and the difference is
visible to a player.

`player_hp:` and `consumable` both have proven executor idioms already in the crate
(`dungeon-on-dregg/src/combat.rs`, and the charged-consumable pattern at
`lib.rs:2089`/`:2292` with its `HeapField { used_key, Lte(charges) }` shape) — those two
are closer to genuinely mechanical, and `consumable` is the better first one because its
deployed shape is already written and driven.

---

## 2. The C4 deployed side — `wayRider`, the monotonic tooth, `stateSlots`

**The wave's "real project", and the prior session's dedicated agent for it died on the
weekly limit with `Now the Rust deployed side.` as its last line.**

The three named symptoms, located at HEAD:

* **`wayRider` refuses every unlock.** `metatheory/Dregg2/Games/DungeonProgram.lean:419`.
  The rider fires on any verb that flips `way_w` and demands, alongside the `0→1`
  transition, `.heapField (.named (relicName (keyFor w))) (.equals CARRIED)`.

  What I could establish at HEAD, and what I could not: `unlockCase`
  (`DungeonProgram.lean:342`) is the verb that flips a way — it freezes `depth`, `wounds`,
  `pack`, `bank`, every `hoard`, `harm`, and carries `relicFreeze`, but does NOT freeze
  `way_w`. **So the naive explanation is wrong**: the relic cannot be moving out from under
  the demand during the unlock, because relics are frozen for the whole case. I did not
  determine the actual cause and am not guessing at one here.

  The two things to check first, in this order: (i) whether the rider's `.heapField`
  demand resolves against a heap projection that a RIDER case actually receives — a
  demand evaluated against a projection with no relic entries is unsatisfiable no matter
  what the player holds, and that shape would explain "refuses EVERY unlock" better than
  anything state-dependent; (ii) whether `keyFor w` / `relicName` produce the key the
  deployed heap is actually keyed by, and whether `CARRIED` is the value that encoding
  uses. Both are cheap to settle by evaluation and neither requires changing a tooth to
  find out.
* **The monotonic tooth is falsified by `take`.**
* **`stateSlots` must widen.**

**Substrate, said out loud:** this is **Lean-authored** program/teeth work
(`DungeonProgram.lean` is the deployed `CellProgram`), and the emitted artifact
(`dungeon_program.json`) is what the executor re-checks. Rust does not get to author a
tooth here. The Rust half is the caller and the regenerated artifact.

⚠ **Widening `stateSlots` moves the deployed layout**, so this is flag-day-adjacent in the
same way as item 3 — check it against the re-genesis already in flight (`HORIZONLOG.md`,
`a0687f268`) rather than landing a second, independent layout move.

---

## 3. Deploying the staged `setFieldValue8` — EMIT-changing

*"The protocol currently cannot express an honest 32-byte field write."* The Lean is
written (`Dregg2/Circuit/Emit/EffectVmEmitRotationV3.lean` + `…Refused.lean`; the plan entry is
`docs/reference/EFFECT-ALGEBRA-RECKONING-2026-07-26.md` §P2.1, Tier 2 "the emit-changing
repairs"). The deployed registry rows are the 8
`setFieldValue8VmDescriptor2-{slot}R24` members (`HORIZONLOG.md:995`).

**It is not blocked on the work; it is blocked on SEQUENCING.** It moves the deployed AIR,
so it invalidates existing proofs and moves the VK — and a re-genesis flag day is already
in flight and already ember-authorized, with the registry TSVs still uncommitted and
`check-drift-taxonomy` correctly refusing pending `--allow-regenesis`. Landing a second
independent emit change in that window means two flag days instead of one.

**Recommendation: fold it into the in-flight re-genesis rather than staging a separate
one**, and take that decision explicitly rather than by arrival order.

---

## The thing all three share

Every one of them is **flag-day-adjacent or design-decision-shaped**, which is exactly why
they were the three left when the cheap items were done. None is blocked on understanding.
Two of them (2 and 3) want the same window, and taking them together is strictly cheaper
than taking them apart.
