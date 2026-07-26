# Handoff — the silence sweep lane, 2026-07-25/26

Written for whoever picks this up without the session context. **314 commits in twenty hours.**
The lane's finding, in one sentence:

> **Almost nothing here was broken. Things were never connected, or quietly disconnected, and
> every mechanism that could have said so is written in a language whose default is silence.**

Detail: `HORIZONLOG.md` (2026-07-25 entry), `docs/CLAIM-CORRECTIONS-2026-07-25.md`, and the
memories `minted-gating-defaults-to-silence`, `minted-census-from-the-lean-side`,
`minted-hardening-commit-disarms-a-guard`.

---

## PARKED — deliberately not attempted, with what each actually needs

Ranked by what blocks a release claim, not by size. **None of these is a mystery. They are work.**

### 1. ⚑ No verifying `WholeChainProof` can be produced in this tree

`ugc-dregg/tests/fixtures/whole_history_proof.bin` no longer decodes (`EnvelopeDecode`), **and
its producer fails at HEAD** with `RecursionFailed(InvalidOpeningArgument(CapMismatch))` after a
12m46s release build. So the fixture cannot be re-baked, and **the crown's live proving path
cannot produce one either.**

Damage is confined: `fixture_fold()` returns `Option`, so only the 3 tests needing a valid proof
are red, each carrying the re-bake command and the measured error in its failure text.

**Needs:** someone who knows the recursion layer to read `CapMismatch` against a prover/verifier
cap disagreement. This is the single largest open item — it is a *capability* claim, not a test.

### 2. ⚑ `Cell.token_id` is an asset AND a namespace salt

It denominates a balance *and* salts `CellId::derive_raw(owner_pubkey, token_id)`. Every
`channel_token_id` / `dkg_ceremony_token_id` / trustline hash / `BOND_CELL_DOMAIN` helper wanted a
**name** and got a **private currency**.

Sharper: **fees are moves to the fee well and a Transfer is single-asset, so a cell in a private
asset cannot be funded and cannot pay a fee at all.** 30 `dregg-node` tests are red on
`cross-asset Transfer rejected` — *collateral, not the bug.* **Do not fix the tests.** Written up
at `node/src/executor_setup.rs::default_token_id`.

**Needs a design decision, two honest options:** (a) split `Cell.token_id` into `asset` +
`name_salt` — correct, a Cell wire change plus a store migration; (b) sponsored fees, so the
operator's cell pays for a turn whose agent is the app cell. The owner side cannot absorb the tag
(the adopt turn authorizes against the cell's real `public_key`).

### 3. 24+ uncensused Rust twins, six already diverged

The twin-deletion campaign's "11 of 11" was **11 of 35+** — it enumerated 13 Rust FFI wrappers
against 51 decision `@[export]`s, i.e. only the quarter Rust already called. See
`minted-census-from-the-lean-side` for the full ranked list and, more usefully, **why** the census
missed them.

Three were fixed (`ff30a6032`), one deleted (`ac6e36be8a`). The rest are enumerated with their
Lean counterparts named. **A `def` with no `@[export]` is the best predictor there IS a twin.**

### 4. 63 test targets nobody has watched run

Enumerated with per-row reasons in `.github/dark-targets.txt`; classified expensive /
environment / forgotten. Four were armed. **The executions never happened** — the lane was starved
on a contended box, and said so rather than claiming them.

### 5. Smaller, each self-contained

- **The burn AIR emits 33 constraints against Lean `burnDesc`'s 38.** *Not exploitable* —
  `verify_effect_binding_proofs_with_ledger` reconstructs all four amounts from
  executor-authoritative state. The real residual: conservation is enforced by **executor
  arithmetic, not in-circuit**, so it is not inherited by a standalone burn-proof verifier.
  Emitting from Lean would move the deployed AIR and invalidate existing burn proofs.
- **Onboarding's Ed25519-only window.** A cell id commits to the Ed25519 key alone, so a
  never-acted cell's ML-DSA anchor is established by its *first turn*. Closing it needs the
  **funding** turn to carry the recipient's ML-DSA key (`Effect::CreateHybridCell` already exists).
  Refusing the first turn protects nothing and only freezes the coins.
- **`dregg-pq`'s `ml_dsa_*_from_seed` are one-keygen-per-call by construction** — and cannot be
  fixed by memoising there, because a cache inside a free function over a bare seed **is** the
  process-global secret pool that was deliberately rejected. Callers hold their own keys (done in
  `dea5ffb5f`, `13c8ed397`). What `dregg-pq` *can* add is the in-flight `PqSite` attribution, so
  the pattern is countable instead of invisible.
- **tug is one round and the last-mover edge got WORSE** with real decisions (57% → 64.8%): the
  round's final act is now a free pick of the better half. The honest port is a **multi-round match
  with an alternating opener** — a match-state change, not a rule change.
- **automatafl's surface resolves a clash by DROPPING MOVES** (the audited-wrong rule) and
  `unfoldable_round` then marks the match unfoldable. 10/10 driven matches contain a clash, so **no
  real match folds to a proof.** The fold machinery is fine; the surface's clash rule is the bug.
  ⚠ The "automatafl is a dead draw" claim was **RETRACTED** — see the claim-corrections doc.

---

## The instruments this lane built — use them, they are cheap

- `scripts/swap-guard` — kills paging *build* processes, orphans first. macOS has no cgroups.
- `docs/BUILD-BUDGET.md` — routing, the box table, the VERDICT contract. **Re-measured 07-26.**
- `.github/dark-targets.txt` + a **two-sided** ratchet: a new dark row fails, *and a stale row
  fails*. `scripts/check-dark-modules.py` for unreferenced `.rs`.
- `dregg-lean-ffi/tests/cfg_gate_declaration_audit.rs` — asserts `USED ⊆ EMITTED`, which the
  `unexpected_cfgs` lint **structurally cannot** (a false outer `#[cfg]` strips its contents before
  the lint runs, and 19 of 28 gate names live inside one such module).
- `dreggnet-web/tests/common/mod.rs::guard` — a tower layer that panics on a *missing-authority*
  act POST, narrow enough that presented-but-rejected still 409s.
- `commands::ack::Acked` — a type with a private field, so **work-before-ack does not typecheck**.

## The trust ladder — every layer lied at least once on 07-25

1. a notification's exit code — `0` over a failed build, `0` over `test result: FAILED`, `1` over a `timeout` kill
2. a wrapper's `VERDICT` — a killed run flushed a buffered **PASS**; a superseded run flushed a
   stale **FAIL** carrying the reader's own command string 22 minutes late
3. **`test result: N passed` from libtest, N non-zero, filter confirmed to have matched** ← trust only this

And still not sufficient: a shared log filename served one lane **a green from another agent's
crate**, and `grep` on a NUL-corrupted log matches nothing silently — *empty reads as clean*.
Discriminators: `running N tests` present · N non-zero · log mtime · `file` says text · `PPID` is
yours.

## Two lane-behaviours worth keeping

**A refusal message tells you what happened, not what is possible.** Three times in one day:
`pbuild` correctly refusing to cross-ship a Mach-O archive became *"persvati cannot run executor
tests"* — for **eight hours**, against a **2m14s** native rebuild. Ask what it would take.

**The discipline was in the artifact and not yet in the operator.** A lane shipped three guards
against absent-answers-wearing-right-answers'-clothes, then read an empty grep as clean and a busy
box as its own build being alive. Apply the checklist to the tools you *read with*, not only to the
tests you *write*.
