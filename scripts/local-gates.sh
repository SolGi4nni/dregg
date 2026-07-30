#!/usr/bin/env bash
# local-gates.sh — run the gates CI invokes, HERE, and print one table.
#
# ── WHY THIS EXISTS ────────────────────────────────────────────────────────────
# The bar is not "GitHub is green". It is: **these gates would succeed if run on a
# real box.** Those are different questions, and on this repo they are VERY
# different — measured 2026-07-26, of the last 60 `ci.yml` runs, 37 were CANCELLED
# and 21 failed and 0 succeeded. Not because the tree was that broken: the median
# gap between commits on `main` is 92 SECONDS and the median run needs ~87 MINUTES
# to reach a conclusion, so ~56 of every 57 pushes cancel their predecessor and
# never get measured at all. A GitHub verdict is a lottery ticket; a local run is
# an answer.
#
# Local is also, in at least two measured ways, the STRICTER test:
#   * `check-doc-refs` — macOS's case-insensitive APFS makes a doc's
#     `Circuit/Foo.lean` match the real `circuit/` dir, so ~60 dead references
#     RESOLVE on a Linux runner and die here.
#   * the `dregg-pq` fail-closed abort was CPU-count dependent: hosted runners are
#     4-vCPU (under the threshold), every dev box with 8+ cores aborted.
# So "it passed in CI" was never evidence that it passes for a person.
#
# ── USAGE ──────────────────────────────────────────────────────────────────────
#   ./scripts/local-gates.sh              # the cheap set (minutes)
#   ./scripts/local-gates.sh --all        # + the expensive ones (see below)
#   ./scripts/local-gates.sh doc-refs …   # only the named gates
#
# Exit 0 iff every gate it RAN passed. Skipped gates are printed, never silently
# dropped — a runner that quietly narrows its own coverage is the thing this repo
# keeps getting bitten by.
set -uo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT" || exit 2

RUN_ALL=0; WANT=()
for a in "$@"; do case "$a" in --all) RUN_ALL=1 ;; -h|--help) sed -n '2,30p' "$0"; exit 0 ;; *) WANT+=("$a") ;; esac; done

# name | timeout_s | command
GATES=(
  "doc-refs|300|bash scripts/check-doc-refs.sh"
  "dark-modules|300|python3 scripts/check-dark-modules.py"
  "never-run-targets|300|python3 scripts/check-never-run-targets.py"
  "emit-gate-weld|120|python3 scripts/check-emit-gate-weld.py"
  "independence-controls|300|bash scripts/check-independence-controls.sh"
  "ratchet-darkness|120|bash scripts/check-ratchet-darkness.sh"
  "lean-orphans|120|bash scripts/check-lean-orphans.sh"
  "forcing-gadget-tie|120|python3 scripts/check-forcing-gadget-tie.py"
  "forcing-gadget-tie-red|60|python3 scripts/check-forcing-gadget-tie.py --self-test"
  "no-degraded-felt|120|bash scripts/check-no-degraded-felt.sh"
  "anchored-lc-committee|60|bash scripts/check-anchored-lc-committee.sh"
  "anchored-lc-committee-red|60|bash scripts/check-anchored-lc-committee.sh --self-test"
  "byte-to-felt|120|bash scripts/check-byte-to-felt.sh"
  "p3-rev|60|bash scripts/check-p3-rev.sh"
  "drift-taxonomy|120|bash scripts/check-drift-taxonomy.sh"
  "no-unchecked-auth|300|bash scripts/no-unchecked-auth.sh"
  "mirror-gates|900|bash scripts/check-mirror-gates.sh"
  "mirror-gates-canary|900|bash scripts/mirror-gates/canary.sh"
  # SPLIT 2026-07-27. The execution phase is one `cargo test --test <stem>` per gate across
  # 24 binaries; it grew past 600s and TIMED OUT, which is not a verdict — and a timeout ran
  # NEITHER phase, so this row reported nothing for a whole session while looking like
  # coverage. That is precisely the disease this gate was written to catch. S1..S4 need no
  # cargo, take ~0s, and catch the delete/rename/manifest-edit class; they run here. The
  # execution half keeps its real budget under --all, where it can finish.
  "gates-executed-static|120|python3 scripts/check-gates-executed.py --static-only"
  # feature-tiers is the STATIC half only (seconds, no cargo): every (crate, feature) pair in the
  # tree has a tier, and no tier row is stale. The T3 COMPILE sweep it plans is nightly and lives
  # in .github/workflows/feature-surface.yml — `scripts/feature-t3-sweep.sh` runs it by hand.
  "feature-tiers|180|python3 scripts/check-feature-tiers.py"
  "feature-t3-ratchet|60|bash scripts/feature-t3-sweep.sh --self-test"
  "ci-invariants-structural|900|bash scripts/ci-invariants.sh structural"
  "descriptor-drift|900|bash scripts/check-descriptor-drift.sh"
  "wasm-freshness|120|bash scripts/check-wasm-freshness.sh"
  "effect-payload-shape|900|bash scripts/check-effect-payload-shape.sh"
  # An em-dash in a string a PLAYER reads. Paired with its own can-it-go-red run, the way
  # `feature-t3-ratchet` is: the gate is a NEGATIVE assertion, which is the shape that passes
  # just as happily when the reader is broken. ~1s, no cargo.
  "player-copy-punctuation|180|python3 scripts/check-player-copy-punctuation.py"
  "player-copy-punct-red|60|python3 scripts/check-player-copy-punctuation.py --self-test"
  # A word from the project's PRIVATE VOCABULARY (`executor`, `receipt`, `merkle`, `no-cheat`, `fog`
  # …) in copy a player reads. Same shape and the same pairing as the two rows above, and for the
  # same reason: `dreggnet-web/src/guide.rs` had this gate and it WORKED, on ONE function — so
  # `/guide` scored 0 violations while the same list was broken on 6 of 13 live surfaces. The list
  # is now `scripts/player-vocabulary.tsv`, read by this sweep AND by `guide.rs` via `include_str!`,
  # because a second reader must not mean a second list. The `-red` row is not optional: the
  # headline is a NEGATIVE assertion, so it passes just as happily when the reader is broken, and
  # the self-test also drives the sweep's own MIN_SURFACES / MIN_UNITS floor red to show it bites.
  # ~1s, no cargo, and no wrapper needed — token 2 of the command is the script itself.
  "player-vocabulary|180|python3 scripts/check-player-vocabulary.py"
  "player-vocabulary-red|60|python3 scripts/check-player-vocabulary.py --self-test"
  # A ROUTING IDENTITY where a player expects a PERSON — `71b278f3dc43444…` in a column headed
  # Holder. The third widening of the same shape, and the clearest one yet that scope is the whole
  # game: `refusal::audit_player_text` has a raw-hex-run rule and has had one for a while — but say
  # WHERE it bans, because this file's whole thesis is that a gate not in this list is not a gate.
  # It is not in this list and it is not on any production path: measured 2026-07-27 it has TWENTY-
  # FOUR call sites and every one of them is test code (`baseline/production-callers.tsv` classes it
  # THEATRE), in `dreggnet-offerings/src/refusal.rs`'s own module tests, `dreggnet-web/tests/
  # refusal_copy_gate.rs`, and three `dreggnet-web` src test modules — each pointed by hand at an
  # ENUMERATED list of surfaces. That is the right runtime for a linter over STATIC copy (a check at
  # render time would be inspecting a message already on its way to a player), so this is not a
  # function to wire; it is a claim to state precisely. Its rule scored zero on this wound because it
  # is pointed at REFUSALS and a roster is not a refusal. It would not have
  # caught it pointed there either — the sites truncate to 15–18 chars and that rule starts at 32,
  # the shortest run in this product that IS a key. Seven sites across four crates on 2026-07-27,
  # each crate having minted its OWN `fn short_identity`, so the wound propagated by copy-paste
  # rather than by call — which is why rule R2 bans re-minting one (`short_root` / `short_digest`
  # stay legal: a root IS a machine value). The `-red` row is not optional: the headline is a
  # NEGATIVE assertion, so it passes just as happily on a broken reader, and the self-test also
  # narrows the scope to drive the MIN_FILES / MIN_POSITIONS floor red. ~1s, no cargo, and token 2
  # of the command is the script itself, so it needs no wrapper.
  "identity-as-a-name|180|python3 scripts/check-identity-as-a-name.py"
  "identity-as-a-name-red|60|python3 scripts/check-identity-as-a-name.py --self-test"
  # The JavaScript inside a Rust `r##"…"##` is a `&str` to rustc and to every reader
  # downstream of it. `dreggnet-web/src/telegram_miniapp.rs` shipped a SyntaxError in
  # `TG_SHELL_SCRIPT` for FOUR DAYS: a dead Mini App serving 200, `cargo test` green,
  # this table green, because nothing here had ever parsed a line of it. `node --check`
  # over every embedded bundle, ~4s, no cargo. Paired with its own can-it-go-red run —
  # like `player-copy-punct-red` and `feature-t3-ratchet`, it is a NEGATIVE assertion,
  # and it also asserts a MINIMUM unit count so a dead extractor cannot read as clean.
  # ⚠ It needs `node`, and it FAILS rather than skips without one. That is the point.
  "embedded-js|180|python3 scripts/check-embedded-js.py"
  "embedded-js-red|120|python3 scripts/check-embedded-js.py --self-test"
  "test-stubs-firewall|300|bash scripts/check-test-stubs-firewall.sh"
  "no-disarmed-guard|180|bash scripts/check-no-disarmed-guard.sh"
  "lean-seed-freshness|120|bash scripts/check-lean-seed-freshness.sh"
  "nightly-verdict|120|bash scripts/check-nightly-verdict.sh"
  # A function that DECIDES something — `verify_*`, `check_*`, `*_admits` — with no
  # production caller. `dregg_circuit::effect_vm::verify_balance_limb_pis` was the
  # Group 6 range precondition, was re-exported twice, said "verifiers MUST call this",
  # and was invoked by no production path and no test: nothing in the tree could report
  # that, because it compiles (it is `pub`, so not dead code) and has no failing test
  # (it has no test). A ratchet over the 235 known rows, not a threshold over the ~4 800
  # uncalled `pub fn`s — a library's surface is SUPPOSED to have callers it cannot see,
  # and a gate over that number is a wall nobody reads. Paired with its own red run: its
  # first scanner LOST both freshly-added call sites to a `/*` inside a line comment and
  # reported the symbol UNCALLED minutes after it was wired, which is exactly the
  # direction a negative assertion fails in. ~40s, no cargo.
  "production-callers|300|python3 scripts/check-production-callers.py"
  "production-callers-red|60|python3 scripts/check-production-callers.py --self-test"
  # An `#[ignore]` with no reason: a test switched off by someone no longer here to be
  # asked. The tree is at ZERO of them (270 attributes, 270 reasons) and this keeps it
  # there — at 270 across 224 crates, one un-annotated addition merges unnoticed.
  # ⚠ It is NOT `grep -F '#[ignore]'`, which reports 177 violations on a tree that has
  # none: this repo writes ABOUT its ignores constantly, in doc comments, in
  # `producer_descriptor_coverage_gate.rs`'s 24-row table, and inside the reason
  # strings themselves (`devnet_adversarial.rs` explains that "an #[ignore] reports
  # `ignored` (honest), not `ok` (a lie)"). So it scans source with comments and string
  # literals BLANKED, reusing check-production-callers.py::strip_noise rather than
  # growing a second Rust reader. ~27s, no cargo. Paired with its own red run — the
  # headline is a NEGATIVE assertion, and the -red row drives all four disease shapes
  # plus the nine prose shapes that fooled the naive scan. It also asserts a MINIMUM
  # population so a broken reader cannot read as clean.
  "bare-ignore|180|python3 scripts/check-bare-ignore.py"
  "bare-ignore-red|60|python3 scripts/check-bare-ignore.py --self-test"
  # The SAME disease one altitude up: a documentation example switched off. A ```ignore
  # doctest fence is an example the compiler was told not to read, and on 2026-07-27 the
  # tree had 71 of them with ZERO reasons — structurally none COULD have one, because a
  # fence info-string rejects unknown attributes. ~38 of the 71 turned out not to be
  # structural at all: real in-scope API that had DRIFTED (a missing `use`, a renamed
  # function) and was silenced rather than repaired. So the reason goes as the first
  # line INSIDE the block, where the reader gets it too, and ```ignore is reserved for
  # structural impossibility — a dependency cycle, a deliberately broken exhibit, source
  # quoted from a non-dependency. It also catches the INERT-ATTRIBUTE shape
  # (```ascii,no_run): rustdoc reads any unknown token as "not Rust", so the attribute
  # beside it silently does nothing — `gating defaults to silence`, in a code fence.
  # ⚠ NOT a grep, and NOT strip_noise either — strip_noise BLANKS comments and a fence
  # lives inside one, so it is the same lexer run inside-out. The -red row drives seven
  # disease shapes and twelve shapes a naive grep gets wrong on this tree (a ```ignore
  # nested inside an open ```text block; the marker named in prose; a fence inside a raw
  # string literal). Exemptions live in `scripts/doctest-ignore-baseline.tsv` and
  # RATCHET: a stale row is a FAILURE, so a repaired fence retires its own exemption.
  # Rides the default `bare-ignore` invocation too, so it cannot be the leg left unwired.
  "doctest-fences|180|python3 scripts/check-bare-ignore.py --fences"
  "doctest-fences-red|60|python3 scripts/check-bare-ignore.py --fences --self-test"
  # Every binary()/package()/test() name in `.config/nextest.toml` still resolves. That file
  # selects tests BY NAME, and a name that outlives its referent does not mislead a reader —
  # it changes what the suite RUNS. It has cost this repo twice. 2026-07-15, LOUD: a deleted
  # test binary made nextest hard-error while validating EVERY profile, so
  # `scripts/test-gauntlet.sh` exited nonzero in all four modes HAVING RUN ZERO TESTS, for an
  # unknown number of commits. 2026-07-27, SILENT: measured against nextest 0.9.136/137/140,
  # `binary()` and `package()` hard-error on an unresolvable name (exit 96) but `test(~…)`
  # returns exit 0 and prints NOTHING — and 21 of the 41 `test(~…)` names in that file named
  # tests deleted weeks earlier in `d260028f1`. Polarity decides the damage: in a `not (…)`
  # exclusion a dead name is only a lie, but in `heavy`/`gpu`'s POSITIVE selectors it silently
  # stops the profile running the test it exists to run, and drops GPU teeth into the
  # GPU-less `armed` lane. ~35s, NO cargo build — resolution is `cargo metadata --no-deps`
  # for binary/package (which beats nextest's own check, that can only fire after a full
  # workspace compile) and an `rg` over `fn` declarations for test(). Paired with its own red
  # run like the rows above, same reason: a NEGATIVE assertion passes just as happily when
  # its own extractor is broken. That row is not decoration — it caught this gate injecting
  # its fault into a COMMENT line and then pronouncing itself blind, and it drives the
  # MIN_NAMES / MIN_PACKAGES / MIN_FNS floors red so a dead reader cannot read as clean.
  "nextest-names|300|python3 scripts/check-nextest-names.py"
  "nextest-names-red|120|python3 scripts/check-nextest-names.py --self-test"
  # A test that `return`s on a missing fixture and reports `ok`. STRICTLY WORSE than the
  # row above: an `#[ignore]` prints `ignored`, which is a true statement, and this prints
  # the same word cargo prints for a test that ran every assertion. `libtest` has exactly
  # two runtime outcomes and no runtime skip, so `return` is never the honest third option.
  # Measured 2026-07-27 before the repair: 168 tests, 112 of them the Lean-archive class in
  # `exec-lean`/`node`/`dregg-lean-ffi`/`sdk` — i.e. concentrated in the suites that guard
  # the machine-checked cores, where a green is a claim nobody checked. The mechanism
  # (`dregg_lean_ffi::demand_lean`) already existed and was correct; it was DISARMED
  # everywhere a human looks — `ci.yml` armed it only on a successful seed fetch, and of
  # the last 60 ci.yml runs 0 succeeded, and THIS FILE never set it at all. It is now armed
  # by default (`DREGG_TEST_ALLOW_MISSING_LEAN=1` to opt out, visibly).
  # ⚠ NOT a grep: this tree writes ABOUT its own skips in doc comments and panic strings,
  # so it reads BLANKED source via check-production-callers.py::strip_noise, walks the brace
  # stack to drop `return`s belonging to closures/nested fns/async blocks, and resolves the
  # per-crate bool helpers (`skip_no_lean`, `ensure_oracle`, `skip_if_core_unlinked`) that
  # hide the probe one call away — keying on direct probes alone found 15 of exec-lean's 41.
  # SILENT is ZERO-TOLERANCE (the tree is at zero); INVERSE and REENTRANT are baselined
  # residuals with different fixes. ~50s, no cargo. Paired with its own red run — the
  # headline is a NEGATIVE assertion and its first cut reported ZERO findings tree-wide
  # because one offset was off by one. The -red row drives 7 disease shapes and 9 shapes
  # that must stay quiet (prose, closures, nested fns, an already-`#[ignore]`d test, a
  # two-armed if/else), and the MIN_TESTS/MIN_GUARDED floors so a dead reader cannot read
  # as clean.
  "silent-skip|300|python3 scripts/check-silent-skip.py"
  "silent-skip-red|120|python3 scripts/check-silent-skip.py --self-test"
  # A Cargo package that NO workspace claims, and a commit that does not resolve from a
  # clean checkout of ITSELF. Two shapes of the same silence. The first cost the most:
  # the ten `orb/crates/*` packages — ~40,000 lines of a TLS/HTTP dataplane — were in
  # neither the root `members` nor its `exclude` from `4bcb934a3` (an untitled sweep-up
  # with an empty body) until 2026-07-27. `cargo metadata` from inside any of them exited
  # 101; `cargo build --workspace` compiled NONE of them; so no `#[allow(dead_code)]` in
  # the subtree was checked by anything, which is how `dataplane/src/proxy_grpc.rs` — zero
  # callers repo-wide — kept a module doc saying it was "wired into the running dataplane".
  # The state emits no line: cargo complains only when you stand inside the directory.
  # This gate found SEVEN MORE the same day (`sel4/verifier-pd`, whose own manifest SAID it
  # was standalone and had never been made so; four `[patch]` sources; a nested vendored
  # crate under deos-homeserver's own workspace), so it is a class, not an instance.
  # The second shape is what a shared tree manufactures: AGENTS.md correctly tells each
  # lane to commit only its own named paths, and the result is a commit whose manifests
  # reference a sibling's still-uncommitted work — green for the author, a broken bisect
  # point for everyone. ⚠ IT IS A MANIFEST CHECK, NOT A BUILD: it catches a missing member
  # dir, a path dep on an uncommitted sibling, an unparseable manifest and a declared
  # `[[bin]]` whose source is not in the commit; it does NOT catch a missing `mod foo;`
  # file, a type error, or a missing build-script artifact. `cargo metadata --no-deps` is
  # ~0.3s, a `cargo check` per commit is hours; the manifest half is the half that broke.
  # ~12s / ~12s / ~70s, no compile. The -red row is not optional — the headline is a NEGATIVE
  # assertion — and it injects every fault into a FRESH `git archive` EXTRACT in a temp
  # dir, so unlike most red-proofs it cannot leave the shared tree disarmed. It also
  # blinds its own reader to drive the MIN_PACKAGES floor red.
  "workspace-closure|180|python3 scripts/check-workspace-closure.py"
  "commit-self-contained|180|python3 scripts/check-workspace-closure.py --rev HEAD"
  "workspace-closure-red|600|python3 scripts/check-workspace-closure.py --self-test"
  # The OpenTheory→Lean importer, RUN. `docs/opentheory-importer-poc/OTPoC.lean` replays a
  # real OpenTheory v6 article into Lean `Expr`s and hands each export to the KERNEL — and
  # until 2026-07-27 it was wired into NOTHING: `grep -rn 'opentheory|OTPoC' .github/ scripts/
  # metatheory/lakefile*` returned zero hits, so it ran only when a human typed a command out
  # of a plan doc. Worse, its three real-article imports each sat behind `if ← p.pathExists
  # … else logInfo`, so with the articles absent the file elaborated EXIT=0 having imported
  # exactly one theorem (`True`). Both halves are closed: the Lean file HARD-ERRORS on a
  # missing article, and this row is the thing that runs it. The gate asserts FLOORS (≥3
  # kernel-checked exports, ≥14 axiom-gate discharges, ≥4 reject-tests refused for their
  # STATED reason), because "exit 0" was exactly the signal that lied. ~8s, no cargo; needs a
  # Lean toolchain and FAILS rather than skips without one, like `embedded-js` and `node`.
  # The -red row is not optional: two of the three checks it protects are NEGATIVE assertions
  # (a gate that refuses, a test that expects refusal), which pass just as happily when the
  # probe is broken. It removes each guard from a scratch copy — the axiom gate's exactness
  # check, the `thm` Γ-content check, the articles themselves, the reject-tests' reason
  # assertion — and requires the matching test to go red for its stated reason. A fault
  # injection that matches NOTHING is a failure, so renaming these lines breaks the self-test
  # loudly instead of disarming it. ~42s.
  "opentheory-importer|600|bash scripts/check-opentheory-importer.sh"
  "opentheory-importer-red|900|bash scripts/check-opentheory-importer.sh --self-test"
  # The Mina<->dregg attestation zkApp, RUN. Same shape as the row above and found the
  # same way: `bridge/mina-zkapp/` was in ZERO targets — no workflow, no gate script, no
  # npm workspace (docs/AUDIT-IMPORTER-AND-DOCS.md §3.6, F-B10) — and what was committed
  # did not run: `tsc` failed on `src/DreggPoseidonAttestation.ts` and the PoC that was
  # reported working had run in a SCRATCH DIR at an o1js the tree did not pin. So the one
  # cryptographic result in that directory (Mina's Poseidon and dregg's agree bit-for-bit,
  # and a Kimchi circuit can verify a Merkle path into a root the Rust side produced)
  # could not go red. This row runs it from the committed TypeScript, compiled by `tsc`
  # and executed out of `dist/`: 9 gold digests + the depth-2 root + the field modulus
  # against the Rust probe's pinned table, a real Pickles compile/prove/verify of the
  # in-circuit path, two tamper rejections, and the `DreggAttestedGate` zkApp deploying on
  # a local chain and CONSUMING the proof recursively (that last one is what makes "a Mina
  # zkApp verified…" name something that ran — before this, only a bare ZkProgram had).
  # It also checks the two things the devnet deployment listed AGAINST ITSELF: the ANCHOR
  # (its comment once said "relay-authorized" over a body that checked nothing, and then a
  # lane "fixed" that with a trusted relay key — so this gate now checks the PROOF
  # OBLIGATION `setDreggRoot` carries, that the obligation REFUSES a root with no
  # BabyBear vouch in it, and the placeholder key's polarities as a PLACEHOLDER), and that
  # a WELL-FORMED proof of another statement is refused by VERIFICATION rather than by the
  # parser — with the identical proof bytes accepted on their own account update as the
  # control, which is what makes the refusal attributable.
  # ⚑ Two more legs since 2026-07-28, both MEASUREMENTS that are ratcheted at 2%: RUNG 1
  # is a Poseidon2-BabyBear MERKLE OPENING (2,677 rows/level, 58,971 for the deployed
  # depth-22 — more than one Pickles step's usable rows) and RUNG 2 is ONE FRI QUERY at
  # the deployed geometry (684,726 rows, 13-15 steps). Both are KAT'd elementwise against
  # the DEPLOYED p3 objects via the probe's `p2merkle`/`p2fold` subcommands, and Rung 2
  # needs a 16 GB node heap. That is the size of the thing the placeholder key stands in
  # for, and having it measured is why the docs can say so.
  # ⚠ It needs `node` >= 20, o1js pinned at 2.15.0, and now `cargo`, and it FAILS rather
  # than skips without any of them — like `embedded-js`. The 1.9.1 the tree used to pin is
  # not a choice: its prover bindings abort inside Poseidon absorb during `compile()` on
  # node >= 26. Cargo is required because the third leg is the DREGG SIDE:
  # `circuit-prove/sketches/mina-pasta-hash-probe` is the crate that EMITS the attested
  # root, it is its own workspace so no other row reaches it, and this gate used to be
  # Node-only — so the emitting half of the bridge ran in no gate at all. That leg runs
  # `cargo test --locked` and then the `merkle` subcommand end to end on unprecomputable
  # leaves, cross-checked elementwise against o1js. No Lean. The -red row is not optional
  # — most of these legs are NEGATIVE assertions, which pass just as happily on a broken
  # driver. It injects FIFTY-SIX faults into SCRATCH COPIES of both the TypeScript and
  # the Rust crate (never the shared tree) — and a fault that matches NOTHING is itself a
  # failure. One of them bends only the `merkle` subcommand's printed root: every
  # `cargo test` still passes and only the cross-check catches it, which is the gap the
  # third leg exists to close. Another puts back the coset-descent bug the 16-layer chain
  # leg found — right on ~half of all query indices and on 100% of the all-zero one every
  # row measurement uses, which is why no single-round check saw it.
  # ⚑ Two more legs since 2026-07-28 EVENING, and the eighth is a SOUNDNESS rung, not a
  # measurement. RUNG 6 is the DEEP QUOTIENT: every rung before it starts its fold chain
  # from a WITNESSED reduced opening, so the walk authenticates a number the prover chose
  # and says nothing about the committed trace. It is now COMPUTED from the MMCS-opened
  # rows, the absorbed claimed evaluations and the transcript's alpha, KAT'd against
  # `p2deep` (p3's own `open_input`), and the leg PROVES a witness the pre-rung-6
  # statement admits and requires the new one to REFUSE it — the gap exhibited rather than
  # asserted. RUNG 7 starts the AIR constraint evaluation at zeta (selectors, alpha-fold,
  # quotient-chunk recomposition, closing equality, all KAT'd against p3's own domain
  # algebra) and prices it as `A + N*h` with `A` and `h` MEASURED and `N` — the constraint
  # count across the root's 7 AIRs — named as uncounted rather than invented.
  # ⚑ `SELFTEST_LEGS="deep air"` scopes PASS 2 of the -red row to named legs. The
  # PRE-FLIGHT is never scoped: what you re-run is a budget question, what you notice has
  # rotted is not. A scoped run says so in its PASS line.
  # ⚑ TIERED 2026-07-30, and the cheap tier is the DEFAULT. This row was 3000s and its
  # `-red` partner was 14400s — 56% of this whole table's budget for ONE directory — and
  # in the window that grew it to nineteen legs the self-test found NOTHING. Everything
  # that arc found was found by a cheap exhaustive out-of-circuit differential: the braid
  # twin walks 11,303 segments and found four defects that "would each have compiled and
  # proved cleanly for as far as any affordable run reaches"; the uniform checker walks
  # 820 boundaries and found ALL NINETEEN block-to-block joins broken, first observable at
  # instance 46. An injection proves the gate CAN fire; it does not find defects.
  # So the row here is TIER 0: MEASURED 25s. It runs those twins, the recorded-figure
  # census, the npm coverage check, and PASS 1 of the self-test — which on the day it
  # landed found SIX unusable injections in 3.2 seconds, four pointing at nothing and two
  # matching two sites each. NOTHING IN IT COMPILES A CIRCUIT, and it says so.
  # ⚠ WHAT MOVED OUT OF THE EVERYDAY RUN: every Pickles compile/prove/verify — the zkApp
  # consumption, the tamper refusals proved by a real prover, the row ratchets, the
  # splices, the chains, the ceiling. `--tier 1` (below, under --all) proves one instance
  # per family; `--tier 2` is the old headline. docs/MINA-GATE-TIERS.md has the table and
  # the honest trade.
  "mina-attestation|300|bash scripts/check-mina-attestation.sh"
  # The npm-script coverage mechanism, on its own row and with its own can-it-go-red run.
  # It is the thing that stops tiering becoming a way to quietly stop testing: measured
  # 2026-07-30, NINE npm scripts in `bridge/mina-zkapp/` were in no gate at all and
  # nothing went red when a tenth appeared. Lean has `lean-orphans-allow.txt`; TypeScript
  # had nothing. THREE more scripts appeared while the mechanism was being written, and it
  # caught all three. ~1s, needs node. The `-red` row is not optional — it is a NEGATIVE
  # assertion, which passes just as happily when the reader is broken.
  "mina-npm-coverage|120|bash scripts/check-mina-npm-coverage.sh"
  "mina-npm-coverage-red|120|bash scripts/check-mina-npm-coverage.sh --self-test"
  # A CLAIM THE CODE DOES NOT CARRY. Every row above this one checks an ARTIFACT — a
  # target, a manifest, a fence, a caller, a row. None of them reads PROSE, and prose was
  # the carrier of six separate wounds on 2026-07-30 alone, every one found by a person
  # and none by a check. The worst was `DreggFederation.advanceState`, documented "the
  # state transition was cryptographically verified" on a file with ZERO occurrences of
  # `.verify(`, `Proof<`, `ZkProgram`, `SelfProof` and `DynamicProof` — a monotonic
  # counter with a signature-free setter — beside a class doc saying `nullifierRoot`
  # "prevents double-withdrawal" over a field set to `Field(0)` at init and never read
  # again. ⚑ That doc was hiding a LIVE HOLE, not overstating a weak one.
  # ⚠ IT CATCHES TWO OF THE SIX AND SAYS SO IN ITS OWN HEADER. The other four need a
  # reader, and the `-historical` row below is what keeps that number a MEASUREMENT: it
  # replays all six from git as they were BEFORE repair and FAILS if the score and the
  # design disagree — so narrowing a rule to go green somewhere else reds here.
  # ⚠ AND IT IS TUNED AGAINST CRYING WOLF, which is the failure mode that kills an
  # instrument like this. Scoped to a declaration's body R1 reported 34 honest sites;
  # file-scoped it reports zero. "blocks"/"stops" are not protective verbs here because
  # "block" is a noun on nearly every line of this tree that contains it. A NEGATED claim
  # is a disclaimer and a QUOTED one is a report, and both were caught firing by the
  # self-test. The contradicting-comments rule (specimen 3) was prototyped, MEASURED at
  # 1,589,852 pairs, and REJECTED — `--contradiction-probe` keeps it runnable so the
  # verdict stays checkable.
  # ~25s, no cargo, no node, no Lean toolchain. The `-red` row is not optional: the
  # headline is a NEGATIVE assertion and it drives four disease shapes, four honest
  # shapes that must stay quiet, R3 against synthetic import graphs, the allowlist's own
  # discipline, and six blindness FLOORS — including `Lean import edges`, which exists
  # because a 64 KB header slice silently zeroed R3's whole harvest during development
  # and the run still printed OK.
  "prose-claims|300|python3 scripts/check-prose-claims.py"
  "prose-claims-red|180|python3 scripts/check-prose-claims.py --self-test"
  "prose-claims-historical|180|python3 scripts/check-prose-claims.py --historical"
)
# Expensive — only under --all, each with the reason it is not in the cheap set.
GATES_ALL=(
  "gates-executed|2400|python3 scripts/check-gates-executed.py"
  "lean-marshal|1200|bash scripts/check-lean-marshal.sh"
  "ci-invariants-falsifiers|14400|bash scripts/ci-invariants.sh falsifiers"
  # TIER 1 — one representative instance per family, COMPILED AND PROVED. This is the
  # pre-merge run and the one to reach for after touching a circuit: it restores what a
  # tier-0 green cannot imply, at one family member each rather than all of them.
  "mina-attestation-t1|3600|bash scripts/check-mina-attestation.sh --tier 1"
  # TIER 2 — the old headline. Every family member, the full chains, the ceiling.
  "mina-attestation-t2|7200|bash scripts/check-mina-attestation.sh --tier 2"
  # The injection suite. It holds 14 faults a permanent control now covers (their
  # patterns are still checked, every pass, by tier 0's pre-flight); `SELFTEST_ALL=1`
  # re-runs those too. ⚑ This is the row that was 4 HOURS of budget in the cheap set.
  "mina-attestation-red|14400|bash scripts/check-mina-attestation.sh --self-test"
)

want() { [ ${#WANT[@]} -eq 0 ] && return 0; printf '%s\n' "${WANT[@]}" | grep -qx "$1"; }

printf '%-28s %-6s %-8s %s\n' GATE RESULT TIME NOTE
printf '%.0s─' {1..96}; echo

pass=0; fail=0; skip=0; timedout=0; failed=()
run_one() {
  IFS='|' read -r name to cmd <<< "$1"
  want "$name" || return 0
  # A gate whose script is missing is a FINDING, not a skip: something references it.
  set -- $cmd; local script="$2"
  if [ ! -f "$script" ]; then
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" MISSING "-" "$script does not exist"
    fail=$((fail+1)); failed+=("$name"); return 0
  fi
  local s e rc out
  s=$(date +%s); out="$(timeout "$to" bash -c "$cmd" 2>&1)"; rc=$?; e=$(date +%s)
  local note; note="$(printf '%s' "$out" | tail -1 | cut -c1-46)"
  if [ "$rc" -eq 0 ]; then
    printf '%-28s \033[32m%-6s\033[0m %-8s %s\n' "$name" PASS "$((e-s))s" "$note"; pass=$((pass+1))
  elif [ "$rc" -eq 124 ]; then
    # ⚑ A TIMEOUT IS A FAILURE, AND ITS OWN MESSAGE SAYS WHY: "not a verdict".
    #
    # This used to increment `skip`, so a gate that could NEVER finish contributed nothing and
    # the table still ended clean. Measured: `gates-executed` timed out for an entire session
    # (528s in the morning, past its 600s budget by evening) while sitting in the cheap set
    # looking like coverage — and the summary read "1 failing" with it invisible.
    #
    # That is this repo's signature disease pointed at its own instrument: a gate that cannot go
    # red is not a gate, and a gate that cannot FINISH cannot go red. Counted as a failure now,
    # and named separately in the summary so a reader can tell "produced no verdict" from "found
    # a defect" — those want different fixes (a budget or a phase split, vs an actual repair).
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" TIMEOUT "$((e-s))s" "exceeded ${to}s — NOT A VERDICT, counted as a failure"
    fail=$((fail+1)); failed+=("$name (timeout)"); timedout=$((timedout+1))
  else
    printf '%-28s \033[31m%-6s\033[0m %-8s %s\n' "$name" "FAIL" "$((e-s))s" "$note"
    fail=$((fail+1)); failed+=("$name")
  fi
}

for g in "${GATES[@]}"; do run_one "$g"; done
if [ "$RUN_ALL" -eq 1 ]; then
  for g in "${GATES_ALL[@]}"; do run_one "$g"; done
else
  for g in "${GATES_ALL[@]}"; do
    IFS='|' read -r name _ _ <<< "$g"; want "$name" || continue
    printf '%-28s \033[90m%-6s\033[0m %-8s %s\n' "$name" SKIP "-" "needs --all"; skip=$((skip+1))
  done
fi

echo
echo "passed $pass · failed $fail · skipped $skip"
[ "$timedout" -gt 0 ] && echo "  ⚠ $timedout failure(s) produced NO VERDICT (timeout) — that wants a budget or a phase split, not a repair"
[ ${#failed[@]} -gt 0 ] && printf 'failing: %s\n' "${failed[*]}"

# ── WHAT THIS DELIBERATELY DOES NOT RUN, and why ───────────────────────────────
cat <<'EOF'

NOT run here, deliberately — each is a real gate, none of them is covered by the above:
  * scripts/axiom-hygiene-guard.sh   whole Dregg2 Lean corpus. A hosted runner was KILLED at
                                     ~56 min (exit 143); it plausibly only ever failed for being
                                     on the wrong machine. Run it locally where .lake is warm.
  * scripts/bare-clone-repro-gate.sh clones + builds from scratch; minutes-to-an-hour of its own.
  * cargo test --workspace           the broadest signal there is. Run it separately, and note
                                     `--no-fail-fast` or the first failure abandons the remaining
                                     test targets and you measure less than you think.
                                     ON LINUX IT IS TWO INVOCATIONS, and the second is not
                                     optional — it is what keeps the first from costing 9 tests:
                                       CARGO_PROFILE_DEV_DEBUG=0 CARGO_PROFILE_TEST_DEBUG=0 \
                                       cargo test --workspace --exclude deos-zed \
                                         --exclude grain-verify-wasm --exclude starbridge-web \
                                         --no-fail-fast -- --test-threads=4
                                       cargo test -p grain-verify-wasm -p starbridge-web --lib
                                     THE debuginfo-OFF PAIR IS NOT COSMETIC. Measured on
                                     persvati 2026-07-26 with the repo default
                                     (`[profile.dev] debug = "line-tables-only"`): this run
                                     grew one lane's target/ to 311 GB and died at
                                     `rustc-LLVM ERROR: IO failure on output stream: No space
                                     left on device` with ~250 GB free when it started. ci.yml
                                     sets both vars for exactly this reason; a local run that
                                     omits them measures an ENOSPC, not the tree.
                                     Those two crates declare `crate-type = ["cdylib","rlib"]`
                                     and reach the Lean archive, and a `-shared` ELF link of
                                     libleanrt's local-exec-TLS mimalloc is rejected outright
                                     (R_X86_64_TPOFF32). `--lib` builds the lib with `--test`,
                                     i.e. an executable, so their tests still run. See the block
                                     above `members` in Cargo.toml.
  * ci-invariants falsifiers         38 rows x ~7 min, each a separate `cargo test -p <crate>`
                                     link. It holds the ONE cargo target lock for ~4 h and blinds
                                     every other lane on the box. Offload it:
                                       scripts/pbuild <warm-lane> bash scripts/ci-invariants.sh falsifiers
EOF
[ "$fail" -eq 0 ]
