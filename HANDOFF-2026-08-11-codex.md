# HANDOFF — 2026-08-11, Claude session → Codex

Read this before touching anything. It was generated from command output and landed
commits, not from conversation memory; where a claim is pending a measurement it says
so. ~53 commits landed in the ~30 hours before this handoff; `git log --since` is the
full record.

---

## 1. Where the two directions stand

### dregg → Mina — **40/40, key on devnet**

- `the_forty_agree_at_every_slot` (`KimchiWrapMainPins12`, `#assert_compiled`):
  the emitted forty wrap public-input words agree with Mina's own
  `to_public_input` at **every slot**, measured against a referee re-baked from the
  same run's output (`scripts/rebake-wrap-referee.py` is now the ONLY route — the
  manual paste that once let the referee go stale at exactly slot 12 is retired).
- The wrap VK is **registered and APPLIED on devnet**: tx
  `5JvPhT5DkyrhjEEn85ccCqfe38LZy14NTtRbzczLdK2eELjAAm2V`, block 543252, account
  digest `9872307806…` (519 rows, public 40). Mina's own binprot reader re-parses
  the on-chain bytes to that digest.
- ⚠ **whatThisIsNot** (recorded in the artifact itself): a registered key is
  account state, **not a verdict on a proof**. There is no
  `Pickles.Side_loaded.Proof` for this circuit — the artifact is a kimchi proof of
  the Lean `w4_bind` sub-circuit. The 40/40 is about the public input that key
  would be handed. **Do not round this up.** Producing the Pickles-shaped proof
  object is the direction's genuine remainder.
- Item #11 (the accumulator leg: §19 still takes `solveG`'s solve) is **exactly
  where it was** — 40/40 did not buy it and did not need it.

### Mina → dregg — built, largely **not yet run in production**

- **Tie 1 is welded AND routed** (`a8f809b4c`, `b51189214`): a leaf adapter
  verifies both STARKs in one circuit; `prove_welded_body_hash_chain_fold` is a
  production prover; a node **refuses an unwelded root**
  (`DREGG_MINA_BODY_ROOT_VK` → `DREGG_MINA_BODY_WELDED_ROOT_VK`, old name refuses).
  Cost measured as a band: welded tower **2.64–2.94×** the plain one.
  ⚠ Nothing in this repo produces a `MinaHeadProofWire`, and no deployment sets
  either anchor — "a node will accept it" ≠ "a node has run it".
- **Tie 2 is expressible** (`c775a31ec`): `dregg-mina-bodyhash-relimb::v1` —
  one 254-bit boolean block, two spellings, the identity a regrouping theorem, not
  a gate. 1.00× committed, zero lookups. ⚠ Not routed; REFUSAL 16 is what runs.
- **BLAKE3 is in pure Lean** (`870ed1d93`): 159/159 descriptors at both hops,
  derive-key mode included, chunk boundaries proved load-bearing by falsifier.
- **The canonical encoder is in Lean** (`317ce6ad3`): a Lean descriptor term can
  be fingerprinted end-to-end without Rust. `DREGGIR2` binary record, byte-exact
  differential over all 159 served descriptors, falsifiers that share every other
  line with the true encoder.
  ⚠ Do not confuse the two digests: `emitVmJson2` renders the **JSON build
  artifact** (SHA-256, registry pin); `canonicalBytes` renders the **binary
  fingerprint record**. Three separate write-ups conflated them.
- **The interpreter bridge holds at ℤ** (`AirProgramRows` + the canonicality
  certificate): a trace satisfying the emitted transcript constraints IS a
  `runProgAt` execution, at ℤ not mod-P. +63 columns, not the +255 once quoted.
- The deployed custom turn **folds** (`20d903660`): the VK spine reached all 16
  `*_segmented` carrier nodes; both load-bearing canaries green.

---

## 2. Known-red ledger

**`scripts/local-gates.sh --all`, 2026-08-11: 77 green / 44 red / 125 rows.**
⚑ **44 reds is NOT 44 findings.** Classified below by spot-reading each row's
tail. Confidence noted: (verified) = I read the mechanism; (bucketed) = inferred
from the row's one-line tail. Re-run and re-classify before trusting any single
row — the log is at `/tmp/gates-handoff.log` this session but is not durable.

**C1 — GATE CRASHED, not a finding (2, verified).** A gate that threw renders as
a red identical to a real defect — the session's whole theme:
- `descriptor-anchor-inertness` — `TypeError: string indices must be integers`.
  Its own `-red` self-test PASSES, so the gate logic is sound; it throws on
  current descriptor data (likely a seam JSON shape the parser doesn't expect —
  the 25 body-preimage seams + tie-2 relimb landed this session). **Fix the
  parser; this is not a tree defect.**
- `prover-freedom-ratchet-red` — bare `Node.js v26.4.0` line = the Node self-test
  **crashed**. The env, not a finding.

**C2 — BOTH ARMS RED = gate can't self-test → broken OR a deep finding (3, verified).**
Look at these first; a `-red` that won't go red is the "documented wound is not a
detected one" class:
- `chip-absorb-arity` + `-red` (`1 leg(s) failed`) — **most suspicious; could be
  real.** Neither the primary nor the self-test passes.
- `nextest-names` + `-red` (`Fix the config… do NOT delete`) — a test was
  renamed/removed and the nextest config points at a stale name. **Plausibly from
  this session's teeth-rename commit `334746475`** — check that first.
- `schema-epoch-log` + `-red` (self-test injection failed) — schema epoch drift.

**C3 — THE REGEN CLEARS THESE (red by design, flag-day pending; ~6, bucketed).**
Firing the deferred nine-descriptor regen (§5 item 1; you have standing authority)
converts this cluster in one act: `descriptor-drift`, `emitter-routing`,
`emit-gate-weld`, `vk-pin-closure` (also needs pin adjudication after),
`forcing-gadget-tie`, `no-degraded-felt`. ⚠ **`the_link_airs_chainlink_pin…`
goes RED when the regen lands — that red is the design; merge the constants per
its docblock, never edit the literal.**

**C4 — RATCHET BASELINE STALE from a 53-commit day (~19, bucketed).** These want a
deliberate `--bless` / `--update-baseline` by someone who reads what moved — NOT a
blind re-baseline: `guard-discipline` (17 rows, ⚠ **blocked by a SIBLING's guard
increase in `TauPrefixMonotone`/`BlocklaceFinality` — do not bless that regression
blind**), `guard-modules`, `doc-refs`, `lean-citations` (≥12 predate this session),
`ratchet-darkness`, `lean-orphans`, `elab-cost` (new `MinaBodyHashRelimb` module —
legitimately new, seed it), `feature-tiers`, `prover-freedom-ratchet`,
`prose-claims`, `silent-skip`, `bare-ignore`, `no-disarmed-guard`,
`doctest-fences`, `production-callers`, `no-unchecked-auth`, `independence-controls`,
`never-run-targets`, `mirror-gates`.

**C5 — CROSS-SESSION / BUILD-ARTIFACT FRESHNESS, not Mina (~8, bucketed).** Other
lanes' territory: `wasm-freshness`, `extension-wasm-freshness`,
`extension-package-freshness`, `lean-seed-freshness`, `lean-seed-closure`,
`lean-seed-member-freshness`, `nightly-verdict` (a `gh run` CI check),
`player-copy-punctuation` (a UI-copy gate).

**C6 — CEREMONY, ember's (2).** `provenance` + `-red`: the stamp records
`source_dirty=true`. Clears when ember stamps (§4 item 1).

Reds that are **expected and load-bearing** — do not "fix" them wrong:

| red | why it is red | what un-reds it |
|---|---|---|
| `vk-pin-closure` (row 115) | **8–9 served `vk_pin`s name a program no descriptor in the tree has.** Real defect, independently reproduced Lean-side. | Adjudicating the pins **after** the regen (below) settles which side moved. Do not adjudicate against a mid-reshape tree: "any verdict would name a tree, not a fact." |
| `every_seam_end_matches_its_served_descriptor` | `2ad7e48c8` moved the canonical encoding → **every** fingerprint moved, incl. descriptors whose bytes didn't change. | The deferred regen. |
| `check-descriptor-drift.sh` | The canonicality certificate widened 9 programAir descriptors 469→532; JSON not yet re-emitted. Red **by construction**. | The regen. |
| `the_link_airs_chainlink_pin_is_stale_against_the_served_bytes` | Currently GREEN — it asserts **disagreement**. It goes **RED when the regen lands**, and that red is the DESIGN: its docblock says the fix is **the constant-merge, never editing the literal**. | Delete the duplicate constant + the theorem together, per its own docblock. |
| `check-ignored-test-routing.py` | Over its `unrouted` ceiling by 4 (other lanes' tests). | Ember's ceiling decision (see §4). |

---

## 3. Traps that cost real time this session (measured, every one)

**Verdict hygiene — the wrapper answers for the work:**
- Read exit codes **directly**, never through a pipeline. `tee | tail` returns
  `tail`'s; a trailing `echo "EXIT=$?"` returns the echo's. Five instances in one
  day, incl. three "green" runs that had failed in 0.3 s.
- `exit 0` with no `test result:` line means **nothing ran** — check the COUNT;
  `-- --ignored` for ignored tests.
- **PRESENT is not CURRENT**: a stale olean made a proved theorem read as
  unverified for a day; a stale emit binary wrote wrong fixtures. Rebuild before
  measuring; check the olean is newer than its source.
- A missing `Ring.olean` is probably a **wiped mathlib**, not a proof failure:
  `python3 scripts/check-mathlib-intact.py` (row 1 of local-gates) answers in
  one line. `metatheory/.lake/packages/mathlib` is a symlink to `~/src/mathlib4`.
- `pgrep -x lean`, never `-c` (matches ZFS kernel threads → a lane panic-killed a
  healthy build); `pgrep -f` can match its own command line.
- `setsid` **does not exist on macOS** — a launcher returned exit 0 for a command
  that never ran. macOS: plain `nohup … &`. Linux boxes: `setsid nohup` (a
  `nohup`'d `swarm-build` dies silently when ssh exits — its scope is
  session-bound).

**Git discipline — the shared tree bites:**
- `--only` is **path-granular, not hunk-granular**. It has absorbed a sibling's
  unfinished feature into HEAD (left it red) and swept 12 of 14 hunks that
  belonged to someone else. For shared files: temp index
  (`GIT_INDEX_FILE` + `read-tree HEAD` + `apply --cached`), verify with
  `git ls-tree` against the commit.
- Check staged deletions **before AND after** every commit — isolated-index
  commits re-create the stale-index hazard (one pass left 30 phantoms).
- A pre-commit **rustfmt hook leaves a stale index entry** on files it reformats:
  worktree == HEAD but the index holds the unformatted blob, so a bare
  `git commit` lands a formatting regression. Hit twice.
- **Never `git checkout` a shared hot file** (it destroyed a lane's work).
  **Never `git stash`** (house law; swarm-unsafe).
- Hot shared files: `HORIZONLOG.md`, `Dregg2.lean`, `lakefile.toml`,
  `local-gates.sh`.

**Boxes:**
- `ssh hbox` works; **`hbox.local` fails on AUTH even when the box is healthy**
  ("unreachable" reports from that name are wrong). hbox swaps under memory
  pressure and drops mDNS. 24 cores/123 GB; build via `swarm-build <cmd>`;
  lane dir `/tank/dregg-build`; **never touch `sdb`**.
- ⚠ **hbox is co-tenant with Codex's own datacake HOL build** — you may be
  sharing the box with your other self. Spare `~/dev/datacake` poly/Holmake.
- persvati: 24 cores/83 GB. `scripts/dregg-clean-build --host persvati` works
  **now** (it never had: non-interactive ssh missed `~/.profile`, elan off PATH,
  rc 127 rendered as `CB_RESULT=RED` — an env fault as the expected verdict).
- **ONE heavy job per box.** Concurrency inflated module times 5–11× and the
  laptop once hit 50 lean procs / 105.6 GB / load 210. Serial is faster.
- Do not share `.lake` between boxes/laptops — races produce phantom GREENs as
  well as phantom reds.
- Lean: hoist circuit-deriving terms out of lambdas (a pin went >2h → 298 s; the
  evaluator re-derived a 10,753-row circuit 82 times).

**Epistemics — the class behind most of the above:**
- The repo's failure mode is **a transcribed derived value going stale** (~10
  incidents in one session) and **a relayed claim skipping re-measurement**
  (every refuted premise this session was one). Trust theorems and gates over
  prose; docblocks here have been stale, and one cited a gate file that had
  never existed. When a claim names a file/line, read it before building on it.
- "Two agreeing transcriptions are not two witnesses; they are one witness
  copied." Prefer gates that compare **two computations over the same input**
  (the blake3/encoder differentials) over stored-vs-computed.

---

## 4. Decisions reserved for ember — do not take these yourself

1. **PROVENANCE.json** — the stamp ceremony is ember's. A clean stamp would need
   to cover: the regen's descriptor set, the pickles wrapmain copies, the
   finalize-scalars v2 traces, the Wrap census figures, the body-preimage seam
   artifacts, and the welded-root anchor.
2. **The `unrouted` ceiling** (156 needed vs 152 allowed) — registering the four
   `#[ignore]`d adapter tests requires raising it; the blocker is ~80 MB of
   untracked `pasta-fp-bodyhash` witnesses no scheduled lane can run.
3. **VK rotation / re-genesis authority — GRANTED, standing.** ember, 2026-08-11,
   asked whether the grant extends to Codex: *"yeah rekeying is ALWAYS always
   approved :)"*. So: fire regens, rotate VKs, re-genesis freely — this is
   greenfield, a flag day is a rebuild, and there is nobody to rekey. The
   obligations that come WITH the grant: say what re-emits, confirm the old
   shape **refuses** rather than reinterprets, and re-measure (never read
   forward) anything a referee graded. ⚠ The grant does NOT include stamping
   `PROVENANCE.json` — that ceremony stays ember's (item 1). Devnet only;
   no mainnet.
4. **fermentation / minidregg** — deliberately undecided. The pricing memo's
   durable numbers: 26% of the cone's 86,956 emitted constraints have a
   constructor in minidregg today; minidregg has no trace/row/selector
   vocabulary (grep-measured, 0 hits across its five Air files). The named
   de-risking spike: port `dregg-mina-preamble-legs::v1` (38 constraints,
   width 30) onto a row-extended minidregg fold and diff the bytes. ⚠ Time
   estimates in that memo ran ~10× long against this team's measured pace —
   the whole breadstuffs project is two months old; the Mina cone was ~2 weeks.
5. **Deleting the Rust encoder** — the differential currently *needs* both
   sides. Deleting one turns two witnesses into one; that's a deliberate
   decision about what replaces the gate, not cleanup.

---

## 5. Ranked next work (each item verified open, none owned)

0. **Fire the deferred nine-descriptor regen — do this FIRST.** It was held all
   session while lanes were live; the tree is now quiesced (index 0, no
   my-lanes running, peers confirmed disjoint), so it is safe. You have standing
   rekeying authority (§4 item 3). Sequence: (a) `scripts/emit-descriptors.sh`
   or the project's regen entry point; (b) the chainlink tripwire
   `the_link_airs_chainlink_pin_is_stale_against_the_served_bytes` goes RED —
   **merge the two duplicate constants and delete the theorem, per its own
   docblock; do NOT edit the literal**; (c) re-bake the wrap referee via
   `scripts/rebake-wrap-referee.py` and **re-measure the forty — never read the
   40/40 forward across a re-emit**; (d) re-run the C3 gate cluster and confirm
   it drained. ⚠ Do this on a quiet box, ONE heavy job, not sharing `.lake`.
   The Claude session chose NOT to fire it at wrap-up on purpose: a clean
   quiesced tree is a better handoff than a mid-flag-day one, and this is a
   multi-step flag day better done with fresh context than exhausted context.
1. **Post-regen pin adjudication** — after the regen lands and the chainlink
   tripwire fires, merge the duplicate constants and adjudicate the 8–9 dangling
   pins. This un-reds row 115 for real.
2. **A `Pickles.Side_loaded.Proof`** — the genuine dregg→Mina remainder (§1).
3. **Run the rewired rotated-forgery tooth** — `mixed_root_forgery_executes_A_
   claims_B` wiring is verified, verdict UNRUN (`#[ignore]`, needs a real
   segment fold).
4. **A `MinaHeadProofWire` producer + deployment anchors** — tie 1 is routed but
   nothing runs it end-to-end.
5. **15 `must_refuse_or_unsat_panic` sites** still discard their reason
   (`blinded_membership`, `caveat_admission`, `custom_leaf_adapter` ×6,
   `note_spend`/`presentation`/`solvency_leaf_adapter` ×2 each,
   `custom_leaf_multi_output_node8`) — measure each message first; two lookalike
   sites this session produced a *different* failure mode than their siblings.
6. **Segment B's ξ field decision** (two block-539508 ξ's: wrap polyscale Fq
   `330305…` vs step deferred Fp `282268…`) and the `b`-half inconsistency
   (`W_B ≠ shiftTockOf(B0)`) — both on the block-verification road, both need
   the numbers in hand before wiring.
7. **Item #11, the accumulator leg** (`G` derived instead of solved) — on the
   block-verification road; NOT needed for 40/40, needed for `equal_g` at
   block 539508's opening.
8. **Carry-chain completeness** (soundness is general; completeness for every
   `zv < N` is three KATs, not a theorem), `RangeTablesHonest`, `RomFaithful`,
   row-0 `Tracks`, `TableSem` tag 7 (no Lean constructor; reader refuses by
   name), and `bodyAccPort` (welds against a fold root, which has no descriptor
   for `SeamEnd` to key on).
9. **The 12 pre-existing `lean-citations` findings** and the `doc-refs` baseline.

## 6. Scratch left in the worktree, deliberately

`before-full.png`, `rack-after-unblock.yml` (Path-of-Angels session's), and
`metatheory/wip/Measure19d.lean` (a lane's wip scratch). None is source; none is
load-bearing.
