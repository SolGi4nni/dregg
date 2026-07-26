# PARKED — the vacuity campaign

**Parked 2026-07-26 at `754570c90`.** Written so the next session resumes from this file alone.

A hypothesis that this tree *proves false* at deployed BabyBear parameters makes every theorem
assuming it VACUOUS — true, and saying nothing whatever about the deployed system. The campaign's
first half is done: accrual is **stopped** by a build-time gate. The second half — draining the
~2.4k declarations that already carry such a hypothesis — is barely begun, and this file says
exactly where it stands, what is measured, and what the next hand should pick up.

Read §2 first if you read only one section. It is the largest single object in the way and **both
of the campaign's instruments are blind to it.**

---

## §0 — provenance of every number below

Three different measurements are floating around in prior handoff prose and they do not agree,
because they were taken at three different commits and two of them predate a gate change. This
section pins which is which; everything later cites back to here.

| tag | commit | what it is | trust |
|---|---|---|---|
| **CENSUS** | `e0160d116` | `#floor_census` TSV, on disk at `docs/artifacts/floor-census-v2-2026-07-26/` | MEASURED, re-verified below |
| **GATE@e016** | `e0160d116` | the `floor-ratchet` line from that root build | MEASURED, recorded in `META.txt` |
| **GATE@5336** | `5336b8a00` | the line quoted in the incoming handoff | MEASURED but **STALE**, see below |
| **HEAD** | `754570c90` | this file | partly measured; **root build NOT verified** |

### ⚑ The gate line in the incoming handoff is stale

The handoff quotes `2059 grandfathered carriers … binder 1665 + prop-body 40 + propdef-user 121 +
bundle 24 + bundle-user 209 … 628 Function.Injective-spelled sites ungated`. That line has **no
`inj-spelled` term**, so it predates `cd3a7efa5` (*"the INLINE spelling is gated"*, 2026-07-26
03:14) — the commit that closed the spelling hole and moved 282 sites from "ungated residual" into
the baseline. Do not quote it as current. The gate's live format string
(`Dregg2/Verify/FloorRatchet.lean:693`) now emits `… + bundle-user N + inj-spelled N; baseline N,
slack N; inline injectivity: N REFUTED signatures gated, N sites left at N UNREFUTED signatures …`.

Anything quoting "628 ungated" or a bare `2059`/`2058` carrier count is describing the tree before
that commit.

### What I verified at HEAD, read-only, this session

| fact | value | instrument |
|---|---|---|
| gate wiring present + armed | **PASS** | `metatheory/scripts/floor_ratchet_check.sh --presence` |
| baseline, named half (working tree) | **2100** | `grep -c '^  "' …/FloorRatchetBaseline.lean` |
| baseline, named half (HEAD) | **2105** | same, via `git show` |
| baseline, inline half | **282** | `…/FloorRatchetBaselineInline.lean` |
| **baseline total** | **2382** (worktree) / **2387** (HEAD) | the two halves; `#floor_ratchet` consumes `grandfathered ++ inlineSpelled` (`FloorRatchet.lean:830`) |
| teeth roster | **14** modules | `TeethWiring.lean` `def roster` (the handoff said 12 — it has grown) |
| census ruler md5 | `67bb5125396a226884fbd432b045fd70` | `md5 -q Dregg2/Verify/FloorCensus.lean` — **unchanged** since the census run, so the TSV still describes the current instrument |
| census TSV md5 | `18f10d2008be50c0250e2754944a3d87` | matches `META.txt` exactly |

**NOT verified at HEAD: the root build.** The last MEASURED green is `e0160d116` (10362 jobs,
EXIT=0, recorded in `META.txt`) and `5336b8a00` (10360 jobs, per the handoff). HEAD is **39 commits
past `e0160d116`**, of which **11 touch `metatheory/`**, and **17 past `5336b8a00`** (3 touching
`metatheory/`). Nobody has built the root since. Treat green as **expected, not established** —
§4 explains why that distinction has cost this campaign real time.

### ⚑ The working tree is not HEAD

`metatheory/Dregg2.lean` and `metatheory/Dregg2/Verify/FloorRatchetBaseline.lean` are **modified and
uncommitted** by a co-tenant terminal, mid-port: five `Dregg2.Circuit.MapOpWideKey*` names are being
drained from the baseline (2105 → 2100). That is a real port in progress and the ratchet moving
*down* is the intended direction. **Do not revert, stash, or `git add -A` around it.** Any repo-wide
number you take in this working tree includes someone else's half-finished work — see §4.

---

## §1 — the state, measured

### The gate (accrual: STOPPED)

`#floor_ratchet` is a Lean command at the end of `metatheory/Dregg2.lean`, implemented in
`metatheory/Dregg2/Verify/FloorRatchet.lean`. It reads the elaborated environment and the checked-in
baseline **through imports**, so lake re-runs it exactly when any declaration changes: `lake build
Dregg2` *is* the gate. A new declaration that takes a provably-false hypothesis is a **build error**.

It derives its floor set from in-tree refutations rather than reading a list, and it now gates six
classes — `binder`, `prop-body`, `propdef-user`, `bundle`, `bundle-user`, `inj-spelled`. The last
three were holes closed on 2026-07-25/26, and each was a bypass anyone could have taken that day:

- **`bundle-user`** — a declaration taking a floor-carrying *structure* as a hypothesis is exactly
  as vacuous as one taking the floor directly, and until it landed it added **zero** carriers.
  `CommitSurface` alone was reached by **409** declarations through this hole.
- **`inj-spelled`** — `Poseidon2SpongeCR f` is *definitionally* `Function.Injective f`, so the
  identical hypothesis cost a build error under one spelling and nothing under the other. 282 sites.

`metatheory/scripts/floor_ratchet_check.sh` is the CI wiring. It is not a second implementation; it
adds the one thing the Lean command structurally cannot do — notice that it is **gone** (a deleted
command raises no error, and `Dregg2.lean` has been silently truncated twice). It runs
presence → **canaries** → full build. The canaries are the load-bearing part: four
`scripts/floor_ratchet_canary*.lean` files each declare a deliberate violation of one evasion class
and must make the gate **error, naming every violating theorem**. A zero exit there is a hard
failure, because it means the gate has stopped being able to fail. One canary carries a `control_`
theorem asserting the opposite — a genuine refutation that must stay EXEMPT, so an over-tightened
gate (where writing a refutation becomes a build error) is caught too.

### The census (surface: MEASURED, first and only v2 run)

`docs/artifacts/floor-census-v2-2026-07-26/floor-census-v2.tsv` — 668,524 bytes, 4571 records.
**It has run.** Every v2 figure quoted before it existed was an estimate; the census needs
`import Dregg2` and a fully elaborated environment, and the root did not elaborate for most of the
campaign.

I recomputed the headline numbers from the TSV rather than trusting `META.txt`'s prose. **All
reproduce exactly.**

```
1925 carriers = endpoint 127 + threader 1266 + dead 100 + no-value 14
                + tooth 95 + prop-body 16 + propdef-user 37 + embedded 270
surface-port 1898   (carriers minus the 27 embedded refutation WITNESSES,
                     which are anti-floor content, not port surface)
35 candidate floors, 27 REFUTED, 8 unrefuted
```

Per-floor, with SOLE-floor counts recomputed from field 11 of the CARRIER records:

| floor | carriers | sole-floor |
|---|---:|---:|
| `StateCommit.compressNInjective` | 753 | 233 |
| `Poseidon2Binding.Poseidon2SpongeCR` | 732 | **707 (97%)** |
| `StateCommit.cellLeafInjective` | 470 | **13 (3%)** |
| `StateCommit.compressInjective` | 366 | 12 |
| `StateCommit.logHashInjective` | 291 | 137 |
| `HermineHintMLWE.HashCR` | 57 | 57 |
| `HashFloorHonesty.CollisionResistant` | 57 | 47 |
| `Lattice.MSISHard` | 45 | 43 |
| `DeployedCapTree.Compress8CR` | 31 | 31 |

Multi-floor: **547** carriers over **27** combinations (412 threaders), and the distribution is far
more concentrated than the roadmap's textual pre-scan guessed (it sized this at "~16 combos" over
353 sites). Four combos hold 473 of 547 — **86%**:

```
306 (203 threaders)  cellLeaf + compress + compressN
 94  (94 threaders)  cellLeaf + compressN + logHash
 42  (42 threaders)  compressN + logHash
 31  (28 threaders)  cellLeaf + compressN
```

A batch port table has **four rows**, not sixteen and not twenty-seven.

### The two instruments do not agree, and should not

The census reports **1925** carriers; the gate's baseline is **2382**. Neither is the other's
correction. The census classifies against the **proof term** (endpoint / threader / dead) over
floors bound in hypothesis position. The gate asks only *"is this declaration in the baseline"*, and
counts classes the census reports separately (`bundle-user`) or not at all (`inj-spelled`). Quoting
one as if it refuted the other is a category error that has already confused two handoffs.

### What a clean census would mean

"The stated assumptions are not provably false in-tree." **Never "verified."** The 1925 carriers are
theorems that are true and say nothing about the deployed system; the 27 refuted floors are the
reason. And all of it sits above the undischarged FRI/STARK floor regardless.

---

## §2 — ⚑ THE BIG PARKED ITEM: `CommitSurface` has no inhabitant at all

**This is the item to read before planning anything.**

### The object

`Dregg2/Circuit/CircuitSoundness.lean:117` — `structure CommitSurface`, five primitives plus five
CR facts:

```lean
structure CommitSurface where
  CH        : CellId → Value → ℤ      -- per-cell leaf hash
  RH        : RecordKernelState → ℤ   -- rest hash over the non-`cell` components
  cmb       : ℤ → ℤ → ℤ
  compress  : ℤ → ℤ → ℤ
  compressN : List ℤ → ℤ
  cmbInj    : compressInjective cmb
  compInj   : compressInjective compress
  compNInj  : compressNInjective compressN
  leafInj   : cellLeafInjective CH
  restFrame : RestHashIffFrame RH     -- ⚑ THE FIFTH FIELD
```

> **Disambiguation, because this has bitten before.** There is a *second, unrelated*
> `structure CommitSurface` at `Dregg2/Circuit/EffectCommit.lean:101`. That one is **pure data**
> (`CH RH cmb compressN LH`) with **no CR fields and no `restFrame`**. It is not affected by any of
> this. Everything below is about the `CircuitSoundness` one.

### The refutation

`Dregg2/Circuit/RestFrameCardinalityFloor.lean` proves, with no `sorry`, no `axiom`, no
`native_decide`:

```lean
theorem restHashIffFrame_false_by_cardinality (RH : RecordKernelState → ℤ) :
    ¬ RestHashIffFrame RH
```

`RestHashIffFrame RH` demands that `RH` separate any two kernels differing in the non-`cell`
components. Two of those components are **function spaces** — `bal : CellId → AssetId → ℤ` and
`caps : Label → List Cap`, with `CellId = AssetId = Label = ℕ`. So the `Set ℕ`-indexed family
`balFam s` (cell `c` holds one unit of every asset iff `c ∈ s`) composed with `RH` and
`Encodable.encode` would be an injection `Set ℕ → ℕ`, which `Function.cantor_injective` refutes.

### Why this is a different *kind* of false from every other floor

Every gated floor (`Poseidon2SpongeCR`, `compressNInjective`, …) is false **at deployed BabyBear
width** — true of a hypothetical unbounded hash, false of the one we ship. That is why the honest
repair for those is a per-instance non-collision side condition at the pair the proof actually uses.

`RestHashIffFrame` has no such repair. It is false for **every** `RH : RecordKernelState → ℤ`, at
**any** width, on **any** machine. There is no instance to be per-instance at. The file makes the
point unmissable with a second theorem whose width hypothesis is discharged **unused**:

```lean
theorem restHashIffFrame_false_at_babyBear (RH : RecordKernelState → ℤ)
    (_hb : ∀ k, 0 ≤ RH k ∧ RH k < (2013265921 : ℤ)) : ¬ RestHashIffFrame RH :=
  restHashIffFrame_false_by_cardinality RH
```

**Widening the digest to 8 felts — the answer for the CR floors — does nothing here.** The
obstruction is the domain, not the codomain.

### The consequence

`CommitSurface` is **strictly stronger than every gated floor**, so it has **no inhabitant at all**.
Draining its four CR fields would not re-inhabit it. This is the "shed one floor of a multi-floor
declaration and the metric moves by zero" failure (§3), one level deeper and total.

### ⚑ Both instruments are blind to it

Neither of the campaign's tools will ever show you this. Checked against both shape tests before the
refutation was written, and confirmed by the fact that **landing the refutation did not turn the
tree red**:

- **`scripts/binding_surface_complete.py`** tier A is a binder-position test over a hand-checked
  list of refuted floors. `RestHashIffFrame` is not on that list, and its `CommitSurface` occurrence
  is a structure **field**, which the ruler documents as a known false-negative.
- **`#floor_ratchet`** *derives* its floor set instead of listing it — the better design — but the
  derivation requires the floor to be injectivity-**shaped** (`FloorCensus.injShape` /
  `injShapeAnd`: the telescoped body must be an fvar equation, or a conjunction of them).
  `RestHashIffFrame`'s body is a **∀-iff over a 17-fold conjunction** of component equalities. It
  does not match, and it is not a named sentinel.

The honest statement is that the gate defends the floors it can recognise, and **this one has to be
recognised by a human**. Widening the derivation blindly to catch it is not obviously right; that is
an open design question, not a to-do.

### Size, measured at HEAD

| | count | how |
|---|---:|---|
| `RestHashIffFrame` binder positions | **227** | `grep -rnoE '[({][^()]*: *RestHashIffFrame'` |
| modules containing one | **80** | same, `-l` |
| modules taking a `CommitSurface` binder | **83** | `grep -rlE '[({][^()]*: *(…)?CommitSurface'` |
| total `RestHashIffFrame` mentions | 434 | includes doc comments |

(The file's own doc-comment says "234 binder positions across 85 modules **at the time of writing**".
227/80 is the same measurement re-taken at HEAD; the drift is ongoing co-tenant ports, not a
discrepancy.)

**This is a multi-session project, not a swarmcycle.** 80–85 modules, and the whole state-commitment
binding chain rests on it — `recStateCommit_binds_kernel`, `commit_binds`, and the `_orBreak`
REGROUNDED twins that were built precisely to be valid at a real hash.

### ⚑ THE PRESCRIBED REPAIR

**Port `CommitSurface` shedding `restFrame` IN THE SAME PASS as the four CR fields.** Not before,
not after — the same pass, or the metric moves by zero.

The structural fix is the one this class always wants: **digest the FINITE SUPPORT actually
touched** — the `accounts : Finset CellId` rows — never the whole function. That turns an
uncountable domain finite and makes the field **satisfiable**. The resulting side condition is a
per-instance non-collision at the two encoded row-lists, exactly like every other cut-over endpoint
in the campaign.

This is not a bespoke idea. `Dregg2/Verify/InjSpelledFloors.lean` already proves the same
cardinality refutation for a whole *family* of whole-function digests —
`balDigest_not_injective`, `capsDigest_not_injective`, `cellValueDigest_not_injective`,
`recordKernelStateDigest_not_injective`, and ~10 more, all via
`not_injective_of_uncountable_domain` — and those theorems are what **arm** the inline half of
`#floor_ratchet`. `RestHashIffFrame` is the same disease wearing a shape the derivation cannot see.
The finite-support repair is the family answer.

---

## §3 — the work order, measured rather than assumed

### ⚑ The endpoint→cone unlock model is FALSE

It was assumed that porting an *endpoint* frees the *threaders* above it. **Measured at 0.5**: 20
endpoints ported freed only 10 threaders, and **the threader class rose**
(`docs/ROADMAP-assurance-perimeter.md:64`). Do not plan on cascade.

The mechanism is now understood and the census explains it exactly: **a declaration stays a carrier
while ANY floor remains.** So:

> **Multi-floor sites must shed EVERY floor in one pass, or the metric does not move.**

That single rule is the whole work order. `cellLeafInjective` is the worked example of ignoring it:
470 carriers, of which **457 carry another floor too**. The cellleaf wave freed 13 sites. That *is*
the 0.5 unlock ratio, explained.

### Priority, in order

**① Bundles pay best.** One structure, and everything that takes it as a hypothesis, in one edit.
`CommitSurface` is 409 reached declarations — but see §2: it is the multi-session one, and it needs
`restFrame` in the same pass. The other 6 bundle structures / 18 floor-typed projections are much
smaller and are the place to learn the move.

**② Sole-floor, pointed at the right floor.** The roadmap's rule ② says "sole-floor declarations
(verify sole-floor status FIRST)", and the measurement says *which* floor to point it at — and it is
**not** the one with the most carriers:

> **`Poseidon2SpongeCR`: 732 carriers, 707 of them sole-floor (97%).** A port there retires the
> whole site. The same effort against `cellLeafInjective` retires 13.

**③ The four-row batch table.** 473 of the 547 multi-floor sites in four combos (§1). The remaining
23 combos hold 74 sites, 14 of them singletons — hand work, last.

### Blocked, with the blocker named

- **`Dregg2/Circuit/ClosureLog.lean:86`, `structure StateDecodeLog`.** Its `hLogInj` field *is* the
  named log-CR floor carrier (`logHashInjective LH`), and it is not incidental — it is what
  `EffectCommit.CommitSurface.LH`'s binding (`AssuranceCase.integrity_guarantee` /
  `effectCircuit_rejects_log_forge`) realizes. It also takes `S : CommitSurface` (the
  `CircuitSoundness` one, §2). **Blocker: it cannot be ported before `CommitSurface` is**, because
  the port would shed `logHashInjective` and leave the bundle. Sequence it after §2.

### One more blocked item, found while writing this file

**`docs/CLAIMS-LEDGER-vacuity.md` row 42 is labelled CITABLE and is vacuous.** Verified at HEAD:

```lean
-- Dregg2/Storage/DeployedFloorRegrounded.lean:466
theorem storage_migration_strictly_stronger
    (hCR : Poseidon2SpongeCR poseidon2Hash) …   -- ⚑ the CONCRETE deployed hash
```

and `:473` in the same file proves `storage_old_hypothesis_unavailable : ¬ Poseidon2SpongeCR
poseidon2Hash`. By the ledger's own §3 rule that is DO-NOT-CITE. The genuinely citable object is the
*separate* declaration `storage_old_hypothesis_unavailable`, which the ledger never lists — so the
vacuous one wears the CITABLE label and the real one is absent. **Row 43 `mmr_migration_strictly_
stronger` (`:479`) is the same shape.** Both ledger rows also cite stale line numbers (`:397`,
`:410`; actual `:466`, `:479`).

This is one doc edit, and it is the highest-consequence small item in the campaign: a CITABLE label
is what someone quotes externally.

---

## §4 — operational laws, each paid for in lost time

**A red root build DELETES a build-embedded gate rather than failing it.** `lean` writes no olean
for a module that errors, so a downstream import silently resolves to the **last green olean** and
reports a surface that predates your change. This is how the gate went dark for **111 commits**. A
green you did not watch elaborate is not evidence. Corollary: `--presence` is cheap and answers a
different question (is the gate *wired*) than the build (does it *pass*) — run both, and know which
one you ran.

**Never measure a repo-wide metric in the working tree.** This tree is co-tenant; right now it
carries five uncommitted baseline drains and two modified gate files that belong to another
terminal. Every real measurement in this campaign was taken on a clean `git archive` export, and the
one time that was skipped the tree yielded a green **no other checkout reproduced**.

**Ask where a number came from before planning on it.** "121 endpoints" propagated through two
planning docs before someone noticed it was automatafl's n²=121. The roadmap's "~16 combos" was a
textual pre-scan; measured, 27. The handoff's `2059` predates a gate class. When a number has no
instrument named beside it, it is an estimate wearing a measurement's clothes.

**A committed CONSUMER whose PROVIDER was never committed has broken this tree at least three
times.** Before committing, check that every module you import is also committed — not merely
present on your disk.

**Do not poll a build in a wait-loop.** That starved a lane to death on 2026-07-25.

---

## §5 — the exact next commands

### Build here, not on persvati

**hbox** is free and warm; persvati was taken. On hbox use `swarm-build <cmd>` — **never bare
`taskset`**. It enforces `MemoryMax` (memory is what kills the box; affinity is not), plus `nice`.
hbox is co-tenant with codex's datacake HOL build — spare its procs and keep waves small.

### Re-verify the gate on a clean export

```bash
# 1. clean export of the commit under test (NOT the working tree)
C=$(git rev-parse HEAD)
D=/tmp/dregg-verify-$C && mkdir -p $D
git archive $C | tar -x -C $D

# 2. APFS-clone the olean cache — near-instant, and lake traces are CONTENT-hash keyed,
#    so unchanged modules replay. ~30 min, not a cold build.
cp -c -R /Users/ember/dev/breadstuffs/metatheory/.lake $D/metatheory/.lake

# 3. the gate IS the build. Tee it; never re-run a build to search its output.
cd $D/metatheory && lake build Dregg2 2>&1 | tee /tmp/gate-$C.log | tail -n 40

# 4. the line
grep -n 'floor-ratchet' /tmp/gate-$C.log
```

Expect a line of the shape `floor-ratchet OK — N grandfathered carriers over 27 refuted floors …
binder … + inj-spelled …; baseline 2387, slack N; inline injectivity: …`. **If it has no
`inj-spelled` term, you are reading a stale log.**

For the full wiring + canary + build (what CI runs):

```bash
cd $D/metatheory && bash scripts/floor_ratchet_check.sh          # presence + 4 canaries + build
bash scripts/floor_ratchet_check.sh --presence                   # fast, pre-commit
bash scripts/floor_ratchet_check.sh --canary                     # presence + canaries, no build
```

The canaries must **die** (non-zero, banner present, every deliberate violation named). A zero exit
there means the gate has gone blind, and every green build since means nothing.

### Re-run the census

```bash
cd $D/metatheory
# ⚑ the output path is a string LITERAL in the driver — edit line 27 first
$EDITOR scripts/run_floor_census.lean          # #floor_census "/tmp/floor-census-v2.tsv"
lake env lean scripts/run_floor_census.lean    # ~2 min warm; ~5m40s from cold elaboration
```

Before trusting a diff against the committed TSV, **verify the ruler is the same object in both
trees** — the instrument must not have moved under the measurement:

```bash
md5 -q Dregg2/Verify/FloorCensus.lean   # must be 67bb5125396a226884fbd432b045fd70
```

Diff against `docs/artifacts/floor-census-v2-2026-07-26/floor-census-v2.tsv`. Expect churn only in
`SUMMARY constants` / `our-constants`, added `MODULE` lines, and CARRIER line-number shifts. **A
changed FLOOR / CARRIER-class / BUNDLE / PROJ / COMBO record is a real change and worth reading.**

### The single highest-value next move

**Port `Poseidon2SpongeCR`'s 707 sole-floor carriers.**

It is the only place in the measured distribution where the unit of work and the unit of progress
coincide: 97% of that floor's 732 carriers carry **no other floor**, so shedding it *ends the
carrier* rather than moving it between classes. It needs no new theory — the repair is the campaign's
standard per-instance non-collision side condition at the pair each proof actually uses, and the
cut-over metaprogram (`Dregg2/Tools/ConePort`, with its pinned post-state teeth) already exists and
has been run on smaller waves. It is a swarmcycle, it is batchable, and it is the largest single
movement of the ratchet available.

Do it **before** §2. `CommitSurface` is the bigger object but it is a multi-session port that needs
the `restFrame` finite-support redesign settled first, and `Poseidon2SpongeCR` does not block on it.

Two small things worth doing in the same session, both cheap:
- fix `docs/CLAIMS-LEDGER-vacuity.md` rows 42/43 (§3) — one doc edit, external-quotation risk;
- decide, and write down, whether `#floor_ratchet`'s derivation should grow to recognise
  ∀-iff-shaped floors like `RestHashIffFrame`, or whether that class stays human-recognised (§2).
  Right now it is undecided, which means it is silently the latter.

---

## Appendix — file map

| path | what |
|---|---|
| `metatheory/Dregg2/Verify/FloorRatchet.lean` | the gate; `elab "#floor_ratchet"` at `:830`, log format at `:693` |
| `metatheory/Dregg2/Verify/FloorRatchetBaseline.lean` | named-half baseline, `def grandfathered` at `:2277` |
| `metatheory/Dregg2/Verify/FloorRatchetBaselineInline.lean` | inline-half baseline, `def inlineSpelled` (282) |
| `metatheory/Dregg2/Verify/FloorRatchetSpecimens.lean` | the gate's self-test fixtures (5 known verdicts, asserted every root build) |
| `metatheory/Dregg2/Verify/FloorCensus.lean` | the census ruler (`#floor_census`) |
| `metatheory/Dregg2/Verify/InjSpelling.lean` | derives the gated inline-injectivity signature set |
| `metatheory/Dregg2/Verify/InjSpelledFloors.lean` | the whole-function-digest cardinality refutations that arm it |
| `metatheory/Dregg2/Verify/TeethWiring.lean` | `#teeth_wired` — the 14 teeth that must be in the build |
| `metatheory/Dregg2/Circuit/RestFrameCardinalityFloor.lean` | ⚑ §2, the refutation both instruments miss |
| `metatheory/Dregg2/Circuit/CircuitSoundness.lean:117` | ⚑ §2, `structure CommitSurface` (the one with `restFrame`) |
| `metatheory/Dregg2/Circuit/EffectCommit.lean:101` | the *other* `CommitSurface` — pure data, unaffected |
| `metatheory/Dregg2/Circuit/ClosureLog.lean:86` | `StateDecodeLog`, blocked on §2 |
| `metatheory/Dregg2/Storage/DeployedFloorRegrounded.lean:466,473,479` | the ledger rows 42/43 defect |
| `metatheory/scripts/floor_ratchet_check.sh` | CI wiring: presence → canaries → build |
| `metatheory/scripts/floor_ratchet_canary*.lean` | 4 canaries, one per evasion class |
| `metatheory/scripts/run_floor_census.lean` | census driver (output path is a literal, line 27) |
| `metatheory/scripts/binding_surface_complete.py` | the older binder-position ruler (tier A) |
| `docs/artifacts/floor-census-v2-2026-07-26/` | the TSV + `META.txt` provenance |
| `docs/ROADMAP-assurance-perimeter.md` | the plan; `:64` has the measured 0.5 unlock |
| `docs/CLAIMS-LEDGER-vacuity.md` | claim-by-claim citability; rows 42/43 need the §3 fix |
| `docs/WOUND-apex-premise-vacuity-2026-07-24.md` | the wound this campaign answers |
