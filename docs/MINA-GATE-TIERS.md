# The Mina gate, tiered — what the everyday run costs, what it catches, what we gave up

**Landed 2026-07-30.** `scripts/check-mina-attestation.sh` had grown to ~19 legs,
222+ checks and 94 fault injections. Its headline row carried a 3000-second
budget and its `--self-test` row 14400 — **56% of the entire default
`local-gates.sh` budget for one directory**, and the self-test alone was ~6.5
hours.

---

## The evidence the tiering is built on

**The self-test found nothing this arc.** Every defect that arc actually found
was found by a **cheap exhaustive out-of-circuit differential**, in seconds:

| instrument | what it walks | what it found |
|---|---|---|
| the braid twin (`root-fri-braid` [2b]) | 11,303 segments | **four** defects — a full output buffer on entry, `sample_bits` taking the low bits, `alpha_pow` starting at one, an undefined path direction. Each "would have compiled and proved cleanly for as far as any affordable run reaches". |
| the uniform checker (`root-fri-uniform` [3b]) | 820 chain boundaries | **all 19** block-to-block joins broken. First observable at instance 46, sealed at 820 — "any affordable proof run would have been green and wrong." |
| the o1js hash probe | 13 measured rows | settled a 200× question **before any Rust was written**. |

An injection proves the gate **can** fire. It does not find defects. That
asymmetry is the whole design.

⚑ And on the day the tiering landed, the injection **pre-flight** — promoted out
of the 6.5-hour run into the everyday one — found **six unusable injections in
3.2 seconds**: four pointing at nothing after four different refactors, and two
matching *two sites each*, so `perl s///` (no `/g`) disarmed the first and left
the other with no falsifier while the suite reported green.

---

## The tiers

`--tier N`, or `MINA_TIER` for a leg run by hand. **The gate's default is tier 0.
A leg's own default is tier 2**, so `npm run root-fri-braid` is unchanged.

### Tier 0 — the default. **MEASURED 25 s.**

Nothing in it compiles a circuit.

| check | cost | what it says |
|---|---|---|
| `tsc --noEmit` at the pinned o1js | 7 s | the committed TypeScript compiles — the directory's *original* defect |
| the injection **pre-flight** | 3.2 s | all 96 falsifiers still match live code, **each at exactly one site** |
| `check-mina-npm-coverage.sh` | 1 s | every `package.json` script is in a tier or allowlisted with a reason |
| `recorded-constants.tsv` census | <1 s | all 29 pinned rows are as recorded, and every `RECORDED_*` in the tree is pinned |
| `root-fri-braid` @0 | 1–3 s | the 11,303-segment walk against p3's own α, βs and query indices |
| `root-fri-uniform` @0 | 6–13 s | the homogeneity, the plan, **all 820 chain boundaries** |
| `root-fri-preamble` @0 | 1–4 s | the batch-STARK preamble differential and its discriminating polarities |
| `fri-walk-plan`, `kat`, `merkle-constraints` | ~5 s | the cut list, the Poseidon vectors, the hashing-row extrapolation |

Measured on an idle box: **25 s**. Measured while a tier-1 run competed for the
same machine: **39 s**. Against the 3000-second budget the row used to carry.

### Tier 1 — pre-merge. One representative instance per family, compiled and proved.

`gate` (the zkApp), `poseidon2-rows` (the hash), `probe` (the Rust emitting
side), `fri-chain` (the FRI family — the leg that *found* the coset-descent bug),
`dregg-verify` (the assembly), `root-air` + `root-air-real` (the root's own AIR),
`partition` (the chain family), `cellcommit-native` (Route B), and the three walk
legs at their full selves.

✅ **The tier-1/tier-2 red closed 2026-07-30** (was: `root-fri-braid` [5] exiting
1 with `1 splice(s) were NOT ATTEMPTED at this cut`). Nothing was wrong with the
circuit; the leg had no vocabulary for the third outcome. It has one now — see
**the cut rule**, below. Measured after: braid **6 m 42 s** at tier 1 (24 checks,
7 of 8 falsifiers attributed), `root-air` 103 s, `root-air-real` 83 s,
`cellcommit-native` 21 s, `mina-merkle` 60 s, `incnonce-native` 16 s.

### Tier 2 — the old headline. Every family member, the full chains, the ceiling.

Plus `--self-test`, the injection suite. The braid runs at `FRIBRAID_LIMIT=12`
here, which is what reaches the first cut that can attribute a bent Merkle
sibling; see below.

---

## The cut rule — why a smaller run of the braid was a *different* test

`root-fri-braid` [5] proves a prefix of the walk and then puts eight falsifiers
to a real `prove()` at one **cut**. The cut used to be implied by the run size: a
backwards search for the last proved slice carrying a witnessed Merkle sibling.
That selects on the **witness** (`aux > 0`) and what refuses a *bent* sibling is
the **assertion that closes over it** — the `cur == commitment` of that sibling's
own round, which can be several cuts later. The uniform-walk lane measured the
coarse rule wrong at two positions for two different reasons (`block7`: no closer
at all; `block9`: a closer for the *previous* round). **Both accepts were correct
behaviour by the circuit. The harness was wrong about where it could test.**

**The corrected rule, now implemented:** a cut can attribute a bent sibling iff
it contains a closer for the **same** round (or fold layer) as its **first**
aux-consuming segment, **positioned after** it. Measured on the braid's own
839-slice plan, in milliseconds, at tier 0:

| | cuts |
|---|---|
| in the deployed plan | 839 |
| consuming a witnessed Merkle sibling | 489 |
| **also closing the round their first sibling feeds — can attribute a bend** | **330** |
| carrying a sibling and unable to attribute a bend in it | 159 |
| the `block9` shape (a closer, wrong round) | 0 |

So **39.3% of the plan's cuts, and 67.5% of the ones that carry a sibling, can
attribute the bend.** The first is cut 11; the first cut carrying a sibling at
all is cut 10. The zero is worth reading precisely: on *this* slicing the coarse
"contains a closer" rule happens to coincide with the corrected one. That is a
property of the deployed slicing, not evidence about the rule — and it is
recorded, so if the slicing changes and that shape appears, the leg goes red.

**And both obvious handlings are wrong.** Asserting the refusal is a false red;
dropping the attempt is an absent falsifier reading as a pass. So the result is
**three-valued — refused / accepted / NOT ATTRIBUTABLE, with the reason** — where
the reason is a *prediction the harness commits to before the child runs*.
Predicted-attributable and then accepted is still a hard red.

Four of the eight are cut properties rather than circuit properties, and each
says which: `auxBent` needs a same-round closer; `friDigestBent` at cut 0 is
unattributable because cut 0 enters `airTerminalSeal(dagDigest, …)`, which does
not close over `friCommit`; `carryBent` at cut 0 has nothing carried in; both
digest bends need an unread chunk.

**The count is floored** (`FRIBRAID_MIN_ATTRIBUTED`, recorded 7). This is the
failure a third value creates: a narrower run no longer goes red, it goes
**quieter**. A run that attributes less than the recorded one must say so in its
invocation, where a reader sees it.

**Measured, both budgets, 2026-07-30:**

| budget | cut chosen | attributed | wall clock | the eighth row |
|---|---|---|---:|---|
| `FRIBRAID_LIMIT=4` (default, tier 1) | cut 3 | **7 of 8** | 402 s | `one Merkle sibling bent` — **NOT ATTRIBUTABLE WITHIN BUDGET**, stated with the cut that would buy it |
| `FRIBRAID_LIMIT=12` (tier 2) | cut 11 | **8 of 8** | 1,131 s | `✓ REFUSED: one Merkle sibling bent` |

(Both green, both re-proved from nothing. The tier-2 figure was measured with a
tier-0 gate run competing for the same box for part of it, so it is an upper
bound; 12 slices at the uncontended 49 s/slice would be about 850 s.)

The candidate table the leg prints is itself the evidence for the rule: at
`LIMIT=12`, **cut 10 carries 96 sibling lanes and still attributes only 7 of 8**,
because nothing in it closes `r0`. The old rule would have cut there at
`LIMIT=11` and asserted a refusal that cannot happen.

**And the rule has its own falsifier — the 96th injection, `braid_cut`.** It puts
§3.27's original rule back (select on the witness: `if (p.aux > 0)` in place of
`if (p.closer !== null)`) and the tier-0 census must go red, because every
carrying cut would then "attribute" and the corrected rule would be
discriminating nothing. That is the precise state in which a NOT ATTRIBUTABLE
verdict launders a non-test as a stated reason. **Measured: 9.5 s end to end**,
including the pre-flight over all 96 — it runs the braid at `MINA_TIER=0`,
because the check it falsifies is a tier-0 check and watching it go red does not
need the leg's proving half.

---

## ⚠ What a tier-0 green no longer implies — stated exactly

**Nothing compiled.** So a tier-0 green does **not** say:

- that any Kimchi circuit **accepts** anything — no Pickles proof was produced or
  verified;
- that any circuit **refuses** anything — no tamper, splice, forged transcript or
  wrong AIR was put to a real `prove()`;
- that the zkApp consumes an attestation proof, or refuses one bound to another
  root;
- that any **row count** is still what the docs quote — the ratchets *compare a
  measurement*, and tier 0 takes no measurement. It checks only that the recorded
  figure has not moved.

What it **does** say is that every out-of-circuit twin still reproduces p3's own
numbers on the real geometry, that every recorded figure is pinned, and that
every falsifier in the suite still points at exactly one piece of live code.

**Tier 1 restores the first four at one family member each. Tier 2 restores the
rest.**

---

## Injections converted to controls

**A control cannot be forgotten or silently unpointed; an injection can, and has
been, ten times across four lanes.** So where a permanent control already asserts
the same thing free on every pass, the injection is **held**:

| held | count | the control that replaced it |
|---|---|---|
| constant-drift (`RECORDED_*` bent, whole leg re-run at ~2–4 min) | 11 | `bridge/mina-zkapp/recorded-constants.tsv`, checked every pass, **plus** the reverse — an unpinned `RECORDED_*` is a failure |
| the `air_fullchain` trio (~87 min, **~22% of the self-test**) | 3 | leg 19's own permanent `REFUSED:` / `UNPINNED:` / `UNBOUND:` greps, asserted on every green pass |

**Held, not deleted, and the distinction is the design:** PASS 1 still checks
their patterns every single run, so they cannot silently stop existing;
`SELFTEST_ALL=1` re-runs them; the PASS line says how many were held.

⚠ **What the census does not say** is that a leg still *compares* its figure to a
measurement. So the trade is three-legged and stated: the census says the figure
has not moved, the per-leg `ratchet: ` grep says the ratchet **ran**, and **one**
constant-drift injection (`rows`) stays live to say the mechanism **bites**.

Measured end to end, `SELFTEST_LEGS="rows" --self-test`: **33 s** — pre-flight
over all 96, then three faults injected and all three turning the gate red,
including the surviving constant-drift representative. The PASS line reports the
14 held.

---

## Coverage — the thing that keeps tiering honest

Tiering moves work from the everyday run to a nightly one, which is exactly the
shape of quietly testing less. `scripts/check-mina-npm-coverage.sh` is what makes
that safe: **every `package.json` script is in a tier or in
`bridge/mina-zkapp/npm-scripts-allow.tsv` with a reason of at least 20
characters**, and a row naming a script that no longer exists is a failure too.

Measured 2026-07-30 before it existed: **nine** npm scripts in no gate at all,
including ~7,600 LOC of that window's FRI work and the whole of Route B's o1js
side. Lean has `lean-orphans-allow.txt`; TypeScript had nothing. **Three more
scripts appeared while this was being written, and the check caught all three.**

`leg_at_tier` does the same job inside the gate: it **dies** on a leg name not in
`TIER_TABLE`, so a lane that adds a leg and forgets the table gets a hard red
rather than a leg that quietly runs in the tier that has to finish in a minute.

---

## Named follow-ups (deliberately not done — five lanes were live in these files)

1. **Gate the Pasta family.** `pasta-differential` (tier 0 — it is an
   out-of-circuit differential and exactly the shape tier 0 is for),
   `pasta-verify` (tier 1), `pasta-root-rows` and `pasta-chain` (tier 2).
2. **Gate `cost-gate`** at tier 0 — it is a model check with no compile in it,
   and it owns the constants `recorded-constants.tsv` pins.
3. **Gate `root-claim-carry`** once its lane names a PASS line.
4. **Delete, rather than hold, the 14 converted injections** once their lanes
   have landed and the controls have a few weeks of standing.
5. **Pin the three `air_ceiling` budgets.** They were *not* converted, because
   they are not `RECORDED_*` and the census does not cover them — calling them
   "already covered" would have been a lie.
6. **The tier-0 artifact dependency.** Braid/uniform each have one out-of-circuit
   check that reads `.fullchain/proof-6.json`, a gitignored artifact only a
   tier-2 run mints. At tier 0 it runs when the file is present and **prints that
   it did not** when it is absent. Minting it cheaply from the committed root
   proof would close the last stated gap in tier 0.
7. ~~**Make `root-fri-braid` [5]'s splice table three-valued.**~~ **DONE
   2026-07-30** — see *The cut rule* above. The measurement that motivated it
   stands and is the reason the section exists: the *same* splice, `a digest of a
   FRI lane chunk this slice never reads, bent`, was **✓ REFUSED** at the cut a
   4-slice run picks and **✗ ACCEPTED** at the cut a 1-slice run forces. Same
   circuit, same bend, opposite verdicts — because the cut moved, not because
   anything about the object changed.

   ⚑ The general lesson, and it is why this stays written down: **a "smaller run
   of the same test" is only smaller if the test does not choose its own subject
   from what the run happened to do.** This one does — so the leg now *states*
   its cut, lists what every cut it reached could have attributed, and floors the
   attributed count. Narrowing is available, and it is legible.
