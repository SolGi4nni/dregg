# THE MIRROR MAP — SWEEP TWO

**13 further adversarially-verified findings (M22–M34) of the same failure mode, hunted in the exact
territory sweep one named as unswept: `starbridge-apps` (31 crates), `site/deep`, the TS/JS/Py surfaces,
the circuit goldens, and the Lean vacuity class.**

Swept 2026-07-15/16 against HEAD `c451eb1f2`. Companion to `RE-AUTHORED-MIRROR-MAP.md` (M01–M21); every
finding survived the same refutation pass (labeled-double / legitimate-abstraction / labeled-placeholder /
live-path-uses-the-real-thing / claim-misread each tried, each failed). Severities are the CORRECTED ones.

**Sweep two's headline is not the 13.** It is three measured facts:
1. **Sweep one's estimate HELD on count and dead-centre on soundness — and was WRONG about location.**
   The worst hole came from the bucket sweep one said it "did NOT look for at all" (§4.4), and it is
   shipped on npm (M30).
2. **The structural law holds 13/13 — and TIGHTENED.** The truth is no longer "one file away." It is
   increasingly *in the same file, by the same author, in the same function* (M30, M32, M24).
3. **The gates sweep one proposed are BUILT and RUNNING — and catch 0 of 13.** Measured, not guessed
   (§5). They filed sweep one's own named-unfiled items and are blind to this territory by construction.

## ID table

| ID | Where | Variant | Severity |
|----|-------|---------|----------|
| M26 | `starbridge-apps/tool-access-delegation/src/lib.rs:122` | harness-tests-own-mirror + lean-models-reauthored-shape | **HIGH** (soundness) |
| M30 | `sdk-ts/src/internal/wire.ts:274` | harness-tests-own-mirror (**STALE-ORACLE**) | **HIGH** (soundness, published) |
| M33 | `intent/src/drex_routing.rs:248` | fixture-on-live-path | **HIGH** (soundness) |
| M32 | `metatheory/Dregg2/Firmament/SeL4Abstract.lean:552` | **hypothesis-bundle-uninhabited** (NEW) | **HIGH** (proof-scope) |
| M29 | `~/dev/dregg-site/templates/blog.html:11` | doc-claims-absent-seam / re-authored-peer | **high** |
| M22 | `starbridge-apps/billing/src/usage.rs:182` | re-authored-peer + harness-validates-own-reconstruction | medium |
| M23 | `starbridge-apps/compartment-workflow-mandate/tests/cwm_lean_differential.rs:30` | harness-tests-own-mirror | medium |
| M24 | `starbridge-apps/agent-orchestration/python/tests/test_differential.py:94` | harness-tests-own-mirror | medium |
| M25 | `metatheory/Dregg2/Apps/NameserviceGated.lean:87` | lean-models-reauthored-shape | medium |
| M27 | `circuit-prove/tests/adjacency_membership_golden_audit.json` | harness-tests-own-mirror | medium |
| M28 | `scripts/build-pages-dist.sh:93` | doc-claims-absent-seam | medium |
| M31 | `sdk-ts/src/endpoints.ts:2` | re-authored-peer / shared-constant | medium |
| M34 | `intent/src/verified_settle.rs:19` | doc-claims-absent-seam | medium |

**Running total: 34 confirmed (M01–M34).**

---

# §1 — FINDINGS BY VARIANT

Each entry: **CLAIM** (verbatim, cited) · **TRUTH** · **LIVE?** · **FIX** (executable) · **CANARY** (must
be RED before the fix — a falsifier that was never red proves nothing).

---

## VARIANT E — harness-tests-its-own-mirror *(the dominant variant again: 4 of 13)*

### M26 — TAD pins a test-only mirror to Lean while deploying a program that enforces strictly less · **HIGH / soundness-hole**

- **CLAIM** — `tests/lean_differential.rs:9-11`: "the anti-drift tooth that keeps the running Rust
  admission mirror == the proven Lean policy, so the formal `tool_invocation_commit_iff_admit` guarantees
  **actually describe what the deployed app enforces**." · `src/lib.rs:7-9`: the worker "can **NEVER**
  invoke the tool beyond the granted rate, scope, or deadline." · `src/lib.rs:152-154` calls `admit_table`
  "the admitted transition table **the executor's `Cases` allow-list enforces**."
- **TRUTH** — `deleg_admit`/`deleg_corpus`/`admit_table` have **ZERO non-test callers**. Verified:
  `grep -rn "AllowedTransitions\|StrictMonotonic" starbridge-apps/tool-access-delegation/src/` → **0**.
  The deployed `tad_cell_program` (`src/lib.rs:192`) and `tad_state_constraints` (`:260`) are
  WriteOnce×3 + Monotonic + FieldLteField. **Three conjuncts of `delegAdmit` are absent from every
  deployed program:**
  1. **SCOPE does not exist.** `MandateService::exercise` (`src/service.rs:245-261`) **takes no tool
     argument**. `TOOL_ID_SLOT` is written (`service.rs:227`, `lib.rs:659`), never read-and-compared. A
     mandate scoped to tool 77 meters a call to tool 99 identically.
  2. **`new == old + 1`** — `Monotonic` is `new >= old` (`cell/src/program/eval.rs:402-409`).
     `StrictMonotonic` (`eval.rs:425`) is unused. The executor commits `0 -> 3` in one turn while
     `delegAdmit g now tool 0 3 = false`.
  3. **DEADLINE** — absent from `tad_state_constraints` (the factory/service/reactor path) entirely.
- **The Lean does not reach the cell.** `ToolAccessDelegation.lean:188` requires
  `hprog : s.kernel.slotCaveats cell = (mandateSpec g now tool cell).caveats`, and `mandateSpec_caveats`
  (`:157-159`) proves those are `[.admitTable callsMadeSlot ...]` **by `rfl`**. No deployed TAD cell
  installs an admit-table ⇒ `hprog` is **false of every real cell** ⇒ the commit-iff-admit theorem says
  nothing about the running app.
- **LIVE? YES, INVERTED.** Deployed: `tad_factory_descriptor` (`:317`), AX3 service (`service.rs:67,142`),
  AX5 reactor (`reactor.rs:109`), AX2 deos surface (`lib.rs:653`). **The tested program is the one nothing
  deploys; the deployed program is the one nothing pins to Lean.**
- **The tell** — `tests/lean_differential.rs:61-67` `scope_tooth_bites` proves the scope tooth **entirely
  against the mirror** (`assert!(!deleg_admit(&DEMO, 50, 99, 0, 1))`). No executor-driven wrong-tool test
  exists **because it is not expressible**. Contrast the deadline tooth, genuinely driven through the real
  executor at `tests/deos_seam.rs:347-362`.
- **FIX** — ⚠ **CORRECTION to the obvious fix:** installing
  `AllowedTransitions{CALLS_MADE_SLOT, admit_table(g, now, tool)}` alone **does NOT restore SCOPE** —
  baking `tool` into the table at install time yields table `T77`, but the executor still never learns
  which tool an `exercise` is for, so it applies `T77` to every invocation. Lean escapes this because
  `mandateSpec` closes `(g, now, tool)` into a **per-presentation** spec; a statically-installed program
  has no presentation. Three parts:
  1. **SCOPE (the real hole):** add `PRESENTED_TOOL_SLOT`; change `exercise` (`src/service.rs:245-261`) to
     take `tool: &str` and emit `self.set(PRESENTED_TOOL_SLOT, tool_id_field(tool))` beside the
     CALLS_MADE advance; gate with equality against `TOOL_ID_SLOT`. `FieldLteField` exists
     (`cell/src/program/types.rs:980`); either add `FieldEqField` or encode as two symmetric
     `FieldLteField`s. Same on AX2 (`lib.rs:653`) and AX5 (`reactor.rs:109`).
  2. **SINGLE-STEP + RATE:** replace `Monotonic{CALLS_MADE_SLOT}` with
     `AllowedTransitions{ slot_index: CALLS_MADE_SLOT, allowed: admit_table(g, now, tool) }` in `:192` and
     `:260`. The evaluator is fail-closed by absence and AIR-proven (`circuit/tests/state_constraint_air_teeth.rs`).
     **This makes `admit_table` a SHARED function with a real caller rather than a test-only mirror** —
     the sibling `starbridge-apps/polis/src/service.rs:88-94` already deploys exactly this machine.
  3. **DEADLINE:** add `FieldGteHeight{ index: DEADLINE_SLOT, offset: 0 }` to `tad_state_constraints()`.
  Then close the Lean seam: generalize `hprog` (`:188`) from caveat-list EQUALITY to "the installed
  caveats CONTAIN the admit-table" with a monotonicity-of-conjunction lemma, **or** make the deployed list
  literally equal `[.admitTable callsMadeSlot ...]`. Without one, the theorem still says nothing.
- **CANARY (RED first)** — add an **executor-driven** wrong-tool rejection to `tests/deos_seam.rs`,
  mirroring the deadline tooth at `:347-362`: a mandate scoped to tool 77, an `exercise` for tool 99, must
  be `Err`. **It cannot even be written today** (no tool argument) — that inexpressibility IS the finding.
  Then: revert (2) and confirm a `0 -> 3` jump commits (RED). Delete or demote `scope_tooth_bites`
  (`tests/lean_differential.rs:61-67`) — it makes no claim about deployment.

### M30 — the TS wire encoder drops `provenance`; its "drift killer" compares against a gitignored, two-week-old snapshot of itself · **HIGH / soundness-hole · PUBLISHED**

- **CLAIM** — three, at reader altitude. (1) `sdk-ts/src/internal/wire.ts:5-8`: "drift in any of them MUST
  FAIL the differential test in `test/wire.test.mjs`, which checks **byte equality against the repo's own
  `dregg-wasm` build**." (2) `test/wire.test.mjs:1-15`: "**THE DRIFT KILLER**… asserts BYTE EQUALITY…
  **ANY DRIFT IN THE POSTCARD LAYOUT… FAILS HERE**." (3) `sdk-ts/PUBLISHED-VERIFY.md:17` ships the
  conclusion to consumers: "| Byte-faithful to the Rust facade | **yes** |" for `@dregg/sdk@0.3.0` on npm.
- **TRUTH** — HEAD `cell/src/capability.rs:134` declares `#[serde(default)] pub provenance: [u8; 32]` —
  **`serde(default)` ONLY, no `skip_serializing_if`** — so postcard **emits its 32 bytes**. Verified:
  `wire.ts:274-287` writes seven fields and stops. This is **not** an unmodeled path: the encoder's own
  comment **quotes that exact rule verbatim for `allowed_effects`** and emits a literal `w.u8(0)` to honor
  it — then misses the newer field carrying the identical annotation. *The truth is in the same function.*
- **Why the tripwire is dead (mechanical, verified):** `wasm/pkg/.gitignore` is a single `*`;
  `git ls-files wasm/pkg` → **0**. The oracle is **untracked**. `package.json`'s
  `"test": "npm run build && node --test 'test/*.test.mjs'"` **builds the TS, never the wasm**.
  `wasm/pkg/dregg_wasm_bg.wasm` is dated **Jul 2 23:38**; `provenance` landed **Jul 15** in `ddd2408c5`.
  **DISPOSITIVE** — the oracle's own serde field-name table, read out of the binary:
  `grep -a -o -E "targetslotpermissions.{0,90}" wasm/pkg/dregg_wasm_bg.wasm` →
  `targetslotpermissionsbreadstuffexpires_atallowed_effectsstored_epochPublic…` — **seven fields, no
  `provenance`.** TS and the oracle are the SAME pre-provenance reconstruction. On a fresh clone the
  oracle does not exist and the drift killer **cannot run at all**.
- **LIVE? YES — shipped npm.** `runtime.ts:304 grantCapability` → `turns.ts:137` → `identity.ts:110
  encodeSignedTurn` → `client.ts:284 POST /api/turns/submit-signed`. The node side is the real type
  (`turn/src/action.rs:1078 cap: CapabilityRef`). postcard is non-self-describing and positional, so the
  node reads the **32 bytes following the cap** (the next effect's tag, or
  `may_delegate`/`commitment_mode`/`balance_change` for a trailing grant) as `provenance` and desyncs —
  the turn fails to decode **or decodes to a DIFFERENT action than the one signed**. Every SDK-issued
  capability grant is affected.
- **CORRECTION to the reporter (harsher):** the mirror is **not "defended by CI" — it is not defended at
  all.** `.github/workflows/publish-sdk-ts.yml` is the only workflow referencing sdk-ts. It **does** build
  the wasm fresh (its header, lines 14-19, says this is only so `.d.ts` generation resolves
  `typeof import("dregg-wasm")` types) — then runs `npm ci`, `npm run build`, `npm pack --dry-run`,
  `npm publish`. **It never runs `npm test`.** CI builds a fresh oracle and then declines to compare
  against it, then publishes.
- **CONTROL (in-tree, decisive)** — `AuthRequired` (`cell/src/permissions.rs`:
  None/Signature/Proof/Either/Impossible/Custom) matches `wire.ts:251-272` varints 0..5 **exactly**.
  *The enum that did not change did not drift. The struct that gained a field did.* Drift is a function of
  **change under a dead gate**, not of author care.
- **FIX — oracle FIRST** (with the stale snapshot in place the encoder fix is unverifiable and the same
  snapshot will bless the next drift):
  1. `sdk-ts/package.json`: `"pretest": "wasm-pack build ../wasm --target nodejs --out-dir pkg"`. Keep the
     target consistent with what `helpers.mjs:17` loads (`initSync` + `readFileSync` of
     `dregg_wasm_bg.wasm`); note `publish-sdk-ts.yml` builds `--target web`.
  2. `wire.ts:287`, append: `w.bytes(exactBytes(cap.provenance ?? new Uint8Array(32), 32, "cap.provenance"));`
     and add `provenance?: Bytes32;` to the interface. `[0u8;32]` is the legacy/unprovenanced sentinel per
     `capability.rs:134`'s own doc, so that default is correct for a direct grant.
  3. Add `npm test` to `publish-sdk-ts.yml` (working-directory: sdk-ts) so the differential **gates the
     publish**; better, a push/PR workflow — today **no workflow runs sdk-ts's tests**.
  4. Retract `PUBLISHED-VERIFY.md:17` and flag `0.3.0`'s `grantCapability` path. **npm consumers are
     affected regardless of what main looks like after the fix.**
- **CANARY (RED first — this is the whole point)** — with (1) in place, apply (2) **second** and watch
  `test/wire.test.mjs` go **RED before** and GREEN after, against a **freshly built** oracle.
  `wire.test.mjs:105-110` (`richEffects`) already exercises `grantCapability`, so the test body needs no
  change. **A green-before means the oracle is still stale.**

### M23 — the CWM Lean differential feeds COMPARTMENT labels where Lean feeds ROLE labels, so no row traverses a single graph edge · **medium**

- **CLAIM** — `tests/cwm_lean_differential.rs:1-16`: "the **mirror-drift tooth**… A hand port can SILENTLY
  DRIFT… **That is the out-of-band seam this test kills**… **Drift on EITHER side fails**." · `:28-29`
  "the Lean **`charterMandate3` actor**" · `:37` "the Lean **`clerkMandate3` actor**."
- **TRUTH** — Lean: `charterMandate3.actorLabels = [Label.named "officer"]`, `clerkMandate3 := { … with
  actorLabels := [Label.named "clerk"] }` (`Core.lean:180-189`) — **ROLE labels**; every Lean row traverses
  an edge of `charterGraph3`. Rust (verified verbatim): `officer_labels()` =
  `WorkflowPhase::CHARTER.iter().map(|p| p.compartment_label())` = `[review, redact, sign]`;
  `clerk_labels()` = `vec![clearance_label("review")]` — **COMPARTMENT labels**.
- **THE DEADNESS IS EXACT** — `dominates` (`src/lib.rs:217-235`) is reflexive: `if a == b { return true; }`
  **before any edge walk**. Officer's rows resolve review⊐review, redact⊐redact, sign⊐sign; clerk row 0
  resolves reflexively, rows 1-2 fail because no edge has `src == review`. **No Rust row traverses an
  edge.** Set `charter_clearance_graph()` to `vec![]` → **all 8 rows byte-identical, test GREEN**. Add the
  over-permissive `(clerk_label(), Sign.compartment_label())` → **all 8 rows unchanged, GREEN**. Both edits
  flip `cwmDiffCorpus` and trip the Lean `#guard` at `Core.lean:316`. **The Rust vector is a CONSTANT
  FUNCTION of the graph** — while `lib.rs:190-191` calls that graph load-bearing ("This IS the graph the
  cell commits in its `CLEARANCE_GRAPH_ROOT_SLOT`") and `lib.rs:209-216` calls `dominates` "the hand-port
  of the proved-sound Lean `ClearanceGraph.dominatesD`" — *exactly the hand-port the tooth claims to guard.*
  `dominates` could be replaced wholesale by `a == b` and this tooth stays green.
- **THE FOSSIL THAT EXPLAINS IT** (not in the reporter's evidence) — `lib.rs:994-996` still carries
  "Scaffold clearance check uses compartment label membership… here we include the phase label directly for
  the skeleton." That is from when `step_clearance_ok` **was** a flat `contains`. `lib.rs:250-255` now says
  it is "NO LONGER a flat `contains` — it walks the reflexive-transitive dominance closure." **The
  differential's inputs were never migrated when the impl was upgraded.** The corpus is pre-upgrade; the
  claim is post-upgrade.
- **LIVE?** The harness is the live path for the *claim*. The **shipped** gate (the executor's root-bound
  `ClearanceDominates`) IS genuinely exercised with the real role labels at `tests/deos_seam.rs:402-465`,
  both polarities — which is why this is a **dead tripwire**, not an open hole.
- **AGGRAVATING** — `metatheory/Dregg2/Apps/VERIFICATION-TOOLKIT-GUIDE.md:171` names this exact file **THE
  TEMPLATE** for every new verified app's differential ("Template: `compartment-workflow-mandate/tests/
  cwm_lean_differential.rs`"). The census banks it as proven core to keep
  (`docs/deos/APPS-DEOS-INTEGRATION-CENSUS.md:46`). **The pattern propagates.**
- **FIX — FOUR TOKENS, and the pinned literal does not change.** Both helpers are **already `pub`**
  (verified: `lib.rs:173` `pub fn officer_label`, `:177` `pub fn clerk_label`) and already used correctly
  by `tests/deos_seam.rs:410,455`. Mirror the sibling that does it right — `src/colonist_job.rs:458-465`
  `pub fn crafter_labels() -> Vec<FieldElement> { vec![crafter_label()] }`:
  ```rust
  fn officer_labels() -> Vec<FieldElement> { vec![officer_label()] }
  fn clerk_labels()   -> Vec<FieldElement> { vec![clerk_label()] }
  ```
  Imports become `{FieldElement, clerk_label, cwm_advance_admits, officer_label}`. **Why the pin survives:**
  officer now walks the three real edges → (true,1),(true,2),(true,3); cursor 3 ≥ terminal → (false,0).
  clerk walks clerk→review → (true,1); redact/sign have no clerk path → (false,0),(false,0). **Identical to
  `CWM_LEAN_DECISIONS[:48-53]` and to the Lean `#guard` — but now EARNED through the graph instead of
  through reflexivity.**
- **CANARY (RED first, mandatory)** — blank `charter_clearance_graph()` to `vec![]`: rows must flip, test
  must **FAIL**. Add `(clerk_label(), WorkflowPhase::Sign.compartment_label())`: clerk row 2 must flip to
  (true,3), test must **FAIL**. **Both are GREEN today; both must be RED after.** Then revert.
  Also kill the fossil at `lib.rs:994-996`, and audit the named sibling
  `storage-gateway-mandate/tests/sgm_lean_differential.rs` (`VERIFICATION-TOOLKIT-GUIDE.md:172`) with the
  same falsifier.
- **STANDING FALSIFIER (generalizes)** — *for any Lean↔Rust differential, **zero out the structure the
  mirror claims to traverse** (graph, table, edge set). If the pinned vector does not move, the corpus is
  not exercising it — the two sides are computing different functions that happen to agree on the grid.*

### M24 — the Python "differential" pins no cross-language vector, and its digest silently falls back to sha256 · **medium**

- **CLAIM** — (1) `test_differential.py:1-6`: "These tests **pin the Python mirror against the SAME vectors
  the Rust `#[test]`s assert**… **Drift on either side fails**." (2) `__init__.py:118-120`: "**the
  differential test pins the blake3 vector when blake3 is present**." (3) `python/pyproject.toml:15-16`:
  "when present the content-address **matches the Rust side byte-for-byte**… **the differential test pins
  whichever is active**."
- **TRUTH** — the whole digest "differential" is `a == b; a != c; a != d; len(a) == 32`. Self-consistency
  only — true for **any** deterministic 32-byte hash. The Rust `#[test]` at `mcp.rs:188-197` asserts **the
  same four facts**. The two tests are structurally parallel and **share no value**.
  `grep -rniE "digest|content_address|blake3|hex|[0-9a-f]{16,}" python/tests/` → **no pinned literal, no
  Rust-produced vector anywhere in the Python tree.** The claimed blake3 pin **does not exist**; neither
  does one for the fallback.
- **THE FALSIFIER, EXECUTED** — blake3 is **NOT INSTALLED** (`import blake3` → ModuleNotFoundError;
  `pyproject.toml:13 dependencies = []` makes it an optional extra). **The sha256 fallback
  (`__init__.py:127-128`) is the LIVE path right now**, producing
  `98899c2c391334c11e0a7db46ceffd96aadbd655af0672c1332cbd59bd7b50ad` for `("search", {"q":"dregg"})` —
  sharing **nothing** with the Rust blake3 digest — and `python3 tests/test_differential.py` still prints
  **14/14 passed**. *The claimed tooth is asleep on the machine it ships to, and nothing notices.*
- **SECONDARY** — `__init__.py:263` truncates: `content_address(mcp_name, args)[:8].hex()` = **64 bits**,
  against `mcp.rs:73-76` which makes the full width load-bearing ("full 256-bit collision resistance (no
  argument-chooser can find a colliding call)"), while `LoggedCall` (`:187-190`) calls itself "the
  content-address (the receipt's audit payload). **Mirrors the Rust `LoggedStep`**" — whose `sub_task`
  (`mcp.rs:162`) binds the full 64-char digest. 64 bits is birthday-findable in ~2³². `audit()`
  (`:275-303`) **never re-derives a digest at all**.
- **IN THE FILE'S FAVOUR (and the law's)** — `§2 test_mcp_default_costs_match_rust` **DOES** pin real
  cross-language literals (50/100/150/200/300 matching `mcp.rs:99-107`). *The file is not uniformly
  toothless; the rot is exactly §3.* **The truth is in the same file, one section up.**
- **LIVE?** For the package: `content_address` is the digest the shipped hermes weld surfaces
  (`hermes_guardrail.py:111` → `DreggGuardrailDecision.digest_hex` → `to_metadata()["dregg_digest"]`). Off
  the Rust executor path — the digest is an **audit payload, not a gate** (`authorize_call`'s scope/budget
  teeth at `:246-261` never touch it). No gate opens, no receipt is forged. Bounded, and I will not inflate
  it.
- **FIX** — a differential with no shared constant is not a differential:
  1. **SHARED VECTORS FILE** — `starbridge-apps/agent-orchestration/tests/vectors/mcp_digest.json`, checked
     in, read by **both** sides (one artifact, two readers, no re-authoring). Include a multi-key +
     non-ASCII vector (pins `canonical_args`' `sort_keys`/compact-separators/`ensure_ascii=False` against
     serde_json's BTreeMap ordering) and an empty-args vector (pins the `args or {}` path).
     **Generate the values FROM THE RUST SIDE ONLY** (`McpToolCall::new(name, args).digest_hex()`) — never
     by running the Python and pasting its output, which re-authors the mirror a second time. Rust asserts
     via `include_str!`; Python reads the same path. *Feasible today: serde_json's Map is a BTreeMap here
     (no `preserve_order` in the lock), so it serializes keys sorted, matching `sort_keys=True`.*
  2. **MAKE THE FALLBACK LOUD** — promote blake3 to a hard dep (`dependencies = ["blake3>=0.4"]`) and
     delete the fallback; or export `CONTENT_ADDRESS_BACKEND` and have the vector test **FAIL** (not skip)
     when it is not blake3. Resolve the backend **once at import**, not per-call in a bare `except
     Exception` that also swallows a broken blake3 install as a silent hash swap.
  3. `__init__.py:263` → full `.hex()`. Truncate **at the display**, never in the stored audit payload.
  4. `audit()` re-derives: store `args` on `LoggedCall`, then
     `if content_address(entry.name, entry.args).hex() != entry.digest_hex: raise MandateError(...)`.
  5. Strike the three false claims until (1)-(4) land.
  6. **Ops — why it stayed asleep:** no `.github/workflows/` step invokes `test_differential.py`
     (`ci.yml:66` mentions the crate only in a comment). Add one that installs the `dev` extra and runs it.
- **CANARY (RED first)** — with the vectors file in place, uninstall blake3 → the vector test must go
  **RED** (today: 14/14 green with the wrong hash). Mutate one byte of a checked-in vector → RED on **both**
  sides.

### M27 — the adjacency isolation audit proves its teeth against a private 26-constraint copy of a deployed 34-constraint AIR · **medium**

- **CLAIM** — `circuit-prove/tests/adjacency_membership_audit_extra.rs:38-40`, verbatim: "The
  **byte-identical** Lean-emitted golden, embedded to prove against the **SAME descriptor the gate pins**
  (**kept in sync by the `#guard`** in AdjacencyMembershipEmit.lean and the gate's assert_eq)."
  **False on every conjunct.**
- **TRUTH (measured, canonicalized set-diff)** — audit golden: `trace_width=32`, **constraints=26**, 4791
  bytes. Deployed `circuit/descriptors/by-name/adjacency-membership.json`: **same wire name**
  `dregg-membership-adjacency::poseidon2-v1`, `trace_width=32`, **constraints=34**, 6959 bytes. Diff: **8
  only-in-deployed, 0 only-in-audit → STRICT SUBSET.** All 8 missing are `boundary row:"last"`
  re-lowerings (dir booleanity col2/col10, l/r selection cols 3/4/11/12, parent-index cols 7/15).
  1. not byte-identical (26 vs 34); 2. not the gate's descriptor — `adjacency_membership_emit_gate.rs:44`
  defines its **own** 34-constraint `r#"..."#` and asserts `len()==34` at `:495`; it contains **zero** path
  references to the audit file; 3. nothing keeps it in sync —
  `grep -rn adjacency_membership_golden_audit .` returns **exactly one hit: its own `include_str!` at
  `:41`.** No Lean `#guard` names it.
- **WHY THE GATE IS BLIND (verified in source)** — `scripts/mirror-gates/mirror_gates.py:480` bails:
  `continue  # nothing else loads it: the const IS the loader, not a "golden"`. **A2 only fires when a
  SECOND loader reads the same path.** A private golden with exactly one reader sits in the designed-in
  blind spot. Confirmed empirically: `grep -c "adjacency_membership_golden_audit" <gate output>` → **0**.
  The gate fires on the **emit gate next door** (`A1:adjacency_membership_emit_gate.rs:46`) and misses this.
- **THE IN-TREE CONTROL SETTLES IT** — the sibling test-local goldens that **are** pinned match their
  deployed twins exactly: `accumulator_nonrev_golden.json` 48 == by-name 48; `quantified_absence_golden.json`
  20 == by-name 20. (`committed_threshold_golden.json` has no by-name twin — neutral, not a
  counterexample.) **Exactly the one nothing pins is the one that drifted.**
- **LIVE? NO** — test-only, and the mirror is strictly **weaker**, so no production soundness hole. The harm
  is that the audit's stated purpose is to be the **only** tripwire on the deployed Last-row
  `L_IDX_OUT`/`U_IDX_OUT` PiBinding — and that tripwire currently proves its teeth on an AIR nobody deploys.
  The header (`:13-15`) claims the isolation is "**PROVEN** by a descriptor-mutation control"; that control
  runs on the 26-constraint mirror.
- **FIX — do NOT hand-patch the 8 constraints in** (that recreates the same unpinned mirror one commit later):
  1. **DELETE** `circuit-prove/tests/adjacency_membership_golden_audit.json` (only reader repo-wide is
     `:41`).
  2. **ONE AUTHOR:** hoist the emit gate's Lean-pinned 34-constraint literal (`adjacency_membership_emit_gate.rs:44`)
     into `circuit-prove/tests/common/adjacency_golden.rs` and have **both** tests read it via
     `#[path = "common/adjacency_golden.rs"] mod adjacency_golden;`. The Lean `#guard emitVmJson2
     adjacencyDesc == …` (`AdjacencyMembershipEmit.lean:250`) then authors the audit too — **exactly the
     property the comment falsely asserted.** *Prefer this over `include_str!` of the by-name artifact: a
     single-reader `include_str!` reproduces the `:480` blind spot and has no Lean author.*
  3. Add a local tripwire after parse: `assert_eq!(desc.constraints.len(), 34, "the audit must run on the
     DEPLOYED adjacency AIR");`
  4. Rewrite `:38-40` and the `:13-15` "PROVEN" header.
- **CANARY (RED first) + RE-EARN THE PROOF — do not assume it survives.** Re-run against the 34-constraint
  descriptor and confirm all three legs: (a) the honest (5,6) trace still ACCEPTS under the 8 restored
  constraints (**observe, do not argue**); (b) the forged `idx_lower=4` PI is still REJECTED; (c) **the
  isolation control** — `retain` still removes exactly 1 constraint (verified: `PiBinding{Last,7,3}` occurs
  once in the deployed set too), and with the pin gone the forged trace is still ACCEPTED. **Leg (c) is at
  genuine risk:** if a restored last-row constraint independently rejects the forged trace, the pin is no
  longer isolated on the deployed AIR and the tamper must be re-derived — **that would be a real finding
  about the deployed descriptor, and is precisely what the mirror has been hiding.**

---

## VARIANT H — hypothesis-bundle-uninhabited *(NEW — sweep one §4.4: "NOT looked for at all")*

### M32 — `SeL4DeriveNonAmpBridge` is PROVABLY UNINHABITED, so the seL4 grounding theorem is vacuous — and five surfaces cite it, including the paper · **HIGH / proof-scope**

- **CLAIM** — five promotions. (1) `SeL4Abstract.lean:5-8`: "it replaces a black-box authority assumption…
  with a *named, pinned, transcribed* one. **A named assumption is a severe-problem-reduced.**"
  (2) `:58-61`: "`dregg_executor_cap_authority_grounded_in_seL4` **DISCHARGES** the seL4-side leg of
  dregg's cap-non-amplification"; `:63` "**axiom-clean** (`#assert_all_clean`)." (3) `AssuranceCase.lean:770-776`,
  **inline on the apex's cap-authority conjunct**: "**GROUNDED IN TRANSCRIBED SEL4**… So this leg **rests
  on transcribed seL4 text, not a black box**." (4) `Dregg2.lean:222`: "**THE PAYOFF**… derives dregg's
  cap-non-amp leg… from the seL4 lemma." (5) the **public** `docs/deploy-gate.html:246`: "(This leg is
  grounded in a line-for-line transcription of seL4's own capability spec.)" — **no hypothesis caveat.**
- **TRUTH — machine-checked.** `commutes` (`:561-563`) has a **`keep`-FREE left side** and a
  **`keep`-INDEXED right side**:
  ```lean
  commutes : ∀ (keep : List Auth) (c : DCap),
    deriveCap (embedSlot c) (embed c) (embedNoChildren c) = some (embed (Exec.attenuate keep c))
  ```
  forcing `embed (attenuate keep c)` **constant in `keep`**; `reflectAuth` (`:566-567`) pushes that down to
  `capAuthConferred`. Refuted by any two-rights endpoint cap: `Exec/Caps.lean:88` is a **genuine filter**
  (`.endpoint t rights => .endpoint t (rights.filter (· ∈ keep))`) and `Authority/Positional.lean:101-104`
  reads rights straight off. **⇒ `[read] = [read, write]`.**
  Falsifier ran clean (`lake env lean`, exit 0; `#print axioms` ⇒ `[propext, Quot.sound]` — **no sorry, no
  new axiom**): `theorem seL4DeriveNonAmpBridge_uninhabited : ¬ Nonempty SeL4DeriveNonAmpBridge`.
  Scratch: `/private/tmp/claude-501/-Users-ember-dev-breadstuffs/d5e67b2b-cba3-4592-a363-46da3f161ca8/scratchpad/VacuityProbe.lean`.
- **THE §4/§5 ASYMMETRY IS THE AUTHOR'S OWN CONVENTION, AND IT INDICTS §5** — §4 carries a `fires`
  non-vacuity witness at `:416-421` **plus** five `rfl` satisfiability examples at `:404-414`, including an
  explicit "so the §4 hypothesis is satisfiable" and an explicit "not ∅ ⊆ ∅" check. **§5 carries NONE.**
  *The same author, in the same file, demonstrably knows a hypothesis-carrying theorem needs an inhabitation
  witness — and §5 skipped it.* **The truth is in the same file, one section up.**
- **LIVE?** The theorem has **zero code consumers** — `SeL4DeriveNonAmpBridge` is never constructed
  anywhere. `running_entry_sound`'s cap conjunct is discharged at `AssuranceCase.lean:782` by the **native**
  `execFullForestG_no_amplify` (`Exec/FullForestAuth.lean:1014`, witness at
  `Verify/KeystoneAuditRunnable.lean:183`) — a genuinely real proof. **So there is NO executor hole, and
  that is precisely why the doc-claim is pure fiction rather than a load-bearing bug.** The **CLAIM** is
  fully live: the apex leg comment, the root manifest, the public deploy-gate page, and —
  **found in verification, not in the report** — **the academic paper**: `paper/sections/11-sel4.typ:34-38`
  ("This stacking is **mechanized**… the bridge theorem **grounds** the dregg layer in it") and
  `paper/sections/14-related.typ:72-73` ("**grounds the inner graph in the outer one mechanically**"),
  both with **no caveat**. *A reviewer is told a vacuously-true theorem is a mechanized grounding.*
- **REFUTED PREMISES (carry these; do not re-derive):**
  - ✗ "`anyOf` exists only in research docs, not the executable kernel" — **FALSE.**
    `Dregg2/Exec/Program.lean` is executable and proved: `anyOf` at `:284`, `senderInField` at `:110`
    (its docstring: "Mirrors `SimpleStateConstraint::SenderInSlot`"), `TurnCtx.sender` at `:1063`,
    `evalSimpleCtx` at `:1125`. `RelayOperator.lean:80` already ships
    `.anyOf [.monotonic "bond", .strictMono "disputeCount"]` with a proved `bond_decrease_needs_dispute`
    (`:180`). **F1-F7 ARE expressible today — this makes the fix cheap and removes the excuse.** The correct
    narrow claim: not expressible in the **`SlotCaveat`** language (`RecordKernel.lean:87-130`) that
    `caveatsAdmit`/`execFullForestG` consult.
  - ✗ "the Lean models the PRE-FIX program" — **unprovable.** `git log -S` returns the single squashed
    commit `ddd2408c5`. The honest charge is **subset-asserted-as-exact**, not regression.
- **FIX — IMMEDIATE (strike; the theorem contributes zero to the leg it is credited on):**
  1. `AssuranceCase.lean:770-776` — delete the "GROUNDED IN TRANSCRIBED SEL4… not a black box" comment;
     say the leg is proved natively by `execFullForestG_no_amplify`, which is what `:782` invokes.
  2. `Dregg2.lean:222` — strike "THE PAYOFF". Keep the §1-§4 description (accurate).
  3. `docs/deploy-gate.html:246` — strike the seL4-provenance parenthetical.
  4. `paper/sections/11-sel4.typ:34-38` + `14-related.typ:72-73` — remove the
     `#lean("Firmament.dregg_executor_cap_authority_grounded_in_seL4")` citations and the
     "mechanized"/"grounds… mechanically" claims. **`seL4_derive_cap_non_amplifying` (§4) remains citable —
     it is real and non-vacuous.**
  5. `:5-8`, `:58-61` — "a severe-problem-reduced" is false while the bundle is empty. Say
     **stated-but-UNINHABITED**.
- **STRUCTURAL** — re-shape `commutes` so the seL4 side is **keep-indexed**. Root cause: l4v `derive_cap`
  (`CSpace_A.thy:105-114`) takes **no rights mask**, so a keep-free LHS can never equal a keep-indexed RHS.
  `embed` must carry the attenuation into the seL4 `EndpointCap`'s `cap_rights` and compose with the
  transcribed `cap_rights_to_auth` (`Access.thy:107-113`). §5 **must** then carry a `fires` witness
  mirroring §4's convention at `:416-421`. ⚠ **Arrow caveat:** `recExec` is a **different executor arrow**
  from the credential-gated `execFullForestG` that `NameserviceGated` rides — say which arrow each theorem
  rides; do not let the fixed doc claim "the gated turn is verified." The alternative (extend `SlotCaveat`
  with `anyOf`/`senderInSlot`) touches the shared kernel inductive and every downstream consumer ⇒ full
  `lake build`, **ember-gated, do not fire from a lane**.
- **CANARY (GREEN first — inverted, and that is the gate)** — land
  `seL4DeriveNonAmpBridge_uninhabited` in the file **now**. It is **GREEN today** — *that is the proof the
  bundle is empty*. After the re-shape it **MUST go RED** and be replaced by the inhabitation example.
  **Green-falsifier-then-red is the gate on the fix.**
- **NOT A DELETION** — §1-§4 are **real**: faithful l4v transcription pinned to commit `e2f32e54` with
  per-def line headers, witnessed non-vacuity, honest 8-of-12 α-projection analysis
  (`alpha_total_iff_used`, `alpha_injective_on_used`), `alphaList_mono`. **Only §5's bridge is empty.**

---

## VARIANT C — fixture-on-live-path

### M33 — the DrEX book is built from self-asserted `offer_amount`, never from the verified Solana lock; `mirror_conserves` is `x <= x` · **HIGH / soundness-hole**

- **CLAIM** — `drex_routing.rs:216-217`: "This is the **LOCK→MIRROR boundary: a lock that does not verify
  never mints and so never enters the book**." · `:236-247`: route "Runs: 1. **mirror conservation**… **no
  fixture is emitted for a flow that did not actually settle+conserve**." · `:22-44` the ASCII diagram
  routes `MirrorLeg{recipient, amount, asset}` ──► ring matcher. · the `provenance` string baked into every
  emitted fixture (`:348-351`): "solana_mirror.verify_lock (lock→mirror) → solver.rs → verified_settle.rs".
- **TRUTH — verified verbatim.** The conservation loop populates `locked` **and** `minted` in the **same
  loop from the same `leg.amount`**:
  ```rust
  for leg in mirror_legs {
      *locked.entry(leg.asset).or_default() += leg.amount as u128;
      *minted.entry(leg.asset).or_default() += leg.amount as u128;
  }
  let mirror_conserves = locked.keys().chain(minted.keys())
      .all(|a| minted.get(a).copied().unwrap_or(0) <= locked.get(a).copied().unwrap_or(0));
  ```
  **`minted[a] <= locked[a]` is `x <= x` — a constant `true`, shipped in the fixture as a checked property.**
  Over `&[]` it is vacuously true. The book is built from `parties` (`:268-283`
  `offer_amount: p.offer_amount`), **never** from `mirror_legs`.
- **THE DEAD FIELD PROVES IT** — `MirrorLeg.party_byte` (`:120`) is written once at `:230` and **read
  nowhere in `intent/src/`**. Repo-wide `grep -rn party_byte --include=*.rs` → **four hits**: the decl, that
  write, and two test-side constructions. **The only field that could bind a verified lock to a book entry
  is never consulted by any production code.** Nothing cross-references `party_byte` against
  `Party.id_byte`; nothing requires a party to *have* a leg; nothing bounds `p.offer_amount` by
  `leg.amount`. A party that locks 1 and writes `offer_amount: 1_000_000` routes.
- **THE VERIFIED EXECUTOR CANNOT BACKSTOP IT (the strongest refutation, and it fails structurally)** —
  `settle_fulfillment_verified` (`verified_settle.rs:358-366`) seeds its pre-ledger via
  `funded_ledger(&legs)` (`:255-264`), which credits each sender **exactly the amount it is about to
  send**. **The verified kernel's under-funding gate therefore CANNOT bite.** The `recKExecAsset` fold is
  genuine, but it is fed a ledger **conjured from the legs themselves**. No lock-derived backing enters the
  chain at any point.
- **NOT A LABELED RESIDUAL — and this cuts the other way.** `:45-57` has an explicit "**Honest scope (the
  residuals, labeled — NOT hidden)**" block naming exactly three: proof-gen/clearing-root,
  one-vault-stands-for-per-chain-vaults, trusted-oracle. **Unbacked offers is not among them.** The author
  enumerated what is unbuilt and affirmatively asserted **this one closed**.
- **THE FALSIFIER THAT NEVER ROUTES** — `intent/tests/drex_routing_e2e.rs:203-206` is titled "TOOTH
  (lock→mirror boundary): a FORGED lock attestation is rejected by the mirror, so it **never mints and never
  enters the book**. The routing flow's first gate bites." **Its body never calls `route`** — it only
  asserts `verify_mirror_lock` errors. *The claim it names is exactly the one it does not test.* **There is
  no first gate on the routing flow.**
- **LIVE?** `route` is the sole producer of `RoutingFixture`; the committed
  `chain/test/fixtures/drex_routing.json` carries `"mirror_conserves": true` and is replayed by
  `chain/test/DrexRoutingE2E.t.sol` against `DreggVault.escrowRelease`. **CORRECTION to the reporter:**
  `intent/src/bin/drex_clear.rs` and `intent/examples/drex_clear_book.rs` do **NOT** import `drex_routing`
  (verified by reading their use-blocks) — they rebuild the pipeline from `solver.rs` + `verified_settle.rs`.
  That narrows blast radius but does not refute: `generate_fixture` (`:285-314`) is a caller and its output
  is committed and consumed on-chain.
- **FIX** — bind `mirror_legs` to `parties` **before** the book is built, and make conservation compare
  **two independently-sourced quantities**. New `RoutingError` variants: `MissingLock`,
  `LockAssetMismatch`, `UnbackedOffer`, `OrphanLock`. Replace `:253-264` with a `backing: BTreeMap<u8,
  &MirrorLeg>` keyed by `party_byte`; error on orphan legs; then build `locked` from the **verified legs**
  and `minted` from **what the book offers**, erroring per-party on `p.offer_amount > leg.amount` and
  `leg.asset != p.offer_asset`. **Keep BOTH the per-party check and the aggregate** — the aggregate alone
  lets two parties in the same asset cross-subsidize. `route(&parties, &[], id)` must then return
  `Err(MissingLock)`.
- **CANARY (RED first)** — add falsifiers that **actually call `route`**: `no_lock_no_book_entry`;
  `offer_exceeding_the_verified_lock_is_refused` (Alice locks 100, claims 1_000_000 →
  `Err(UnbackedOffer{backed:100, offered:1_000_000})`); `a_forged_lock_never_enters_the_book` (drive
  `route`, not just `verify_mirror_lock`); `a_lock_for_the_wrong_asset_does_not_back_the_offer`.
  **Mutation canary:** revert the `:253-264` fix and confirm `offer_exceeding_the_verified_lock_is_refused`
  goes **RED** — if it stays green the bind is still not load-bearing. Retitle or extend the mis-titled
  `:203`. Regenerate the fixture: **the clearing root should be UNCHANGED** for the honest 3-party ring
  (offers already equal locks: 100/50/200) — itself a check that the fix only removes reachable-bad states.

---

## VARIANT B — re-authored-peer

### M22 — the "verifiable bill" re-declares the receipt payload and verifies it against itself · **medium**

- **CLAIM** — four sites. `invoice.rs:8-16`: "**`Invoice::verify_against_receipts` re-witnesses the bill**…
  A single padded line or inflated total fails the check — '**every line traces to a settled turn
  receipt**.'" · `:221-229`: "**Re-witness the bill against its receipts** (the verifiable-invoice tooth)…
  A padded line, an inflated total, **or a tampered receipt amount** all fail." · `usage.rs:12-15`: "is
  **the verifiable-bill tooth**." · **the published** `Cargo.toml:5`: "an invoice is an aggregation VIEW
  over settled turn receipts."
- **TRUTH** — `SettleReceipt` (`usage.rs:182`) keeps `dregg_turn::TurnReceipt`'s 32-byte hash and
  **re-declares the payload** (`amount`, `asset`, `period`) as free host-side fields — dropping the executor
  Ed25519 signature, `turn_hash`, `effects_hash`, and pre/post state. `verify_against_receipts` (`:231`)
  **takes NO external input** and **never reads `r.receipt_hash`** — it re-sums `r.amount`, which the issuer
  typed. `Invoice::assemble` copies `e.receipt` into each line while summing `e.amount_units`;
  `verify_against_receipts` re-sums those same clones. **The document under test carries the evidence it is
  checked against.** Repo-wide, `receipt_hash` is READ in exactly two places (`body_hash` at `:297`, hashing
  it as **opaque bytes**, and the test) and COMPARED against a receipt/ledger/chain in **zero**. The hash is
  inert decoration. `SettleReceipt::new([0xAB;32], "CREDIT", 999_999, 0)` + a matching padded line verifies
  `Ok(())`; a **real** receipt hash carrying `amount: 999_999` for a turn that moved 20 also verifies `Ok(())`.
- **LIVE?** `verify_against_receipts` is the **only** verification API the crate exposes
  (`grep 'pub fn .*verify' src/` → exactly one) and its headline tooth. No deployed value.
- **HONEST QUALIFICATION (carry it)** — the fn's own sentence "a tampered receipt amount… fails" is
  **narrowly TRUE** (tamper one receipt without touching the line → sum mismatch). *That sentence survives.*
  The module-level and Cargo-level "every line traces to a settled turn receipt" do not. And the test does
  drive real executor turns (`tests/billing_period_invoice.rs:183-193` pulls real `receipt.receipt_hash()`
  from `exec.submit_action`; `:229-241` cross-checks `settled_hashes`) — **but that binding lives in the
  TEST's own bookkeeping, not the crate. The test holds ground truth the library cannot reach.**
- **FIX — the truth is one crate away, same directory, same template** (`agent-orchestration/src/lib.rs:544-558`,
  see §4):
  1. `SettleReceipt { receipt: TurnReceipt, turn: Turn, period: i64 }` + `settled_amount(&self, asset)`
     **derived** from the Transfer call in `self.turn`'s forest. **Delete
     `SettleReceipt::new(receipt_hash, asset, amount, period)`** — the constructor that lets an issuer type
     any four values. Replace with `from_settled(receipt, turn, period)` returning `Err` unless
     `turn.hash() == receipt.turn_hash`.
  2. Give the verifier an anchor it cannot author:
     `verify_against_receipts(&self, executor_vk: &VerifyingKey)` → (a) verify the executor signature
     (reject if `executor_signature.is_none()`); (b) `r.turn.hash() == r.receipt.turn_hash`; (c) amount
     **derived**, never read off a host field.
  3. Add the exactly-once check the docs already promise: `dregg_turn::verify_receipt_extends`
     (`turn/src/verify.rs:215`) pairwise over the period's receipts, and reject duplicate
     `receipt.receipt_hash()` across **all** lines (a receipt replayed onto two lines = double-billing the
     same settled turn).
  4. Until (1)-(3) land, **rename the fn `check_internal_arithmetic`** and strike "re-witnesses the bill" /
     "every line traces to a settled turn receipt" from `invoice.rs:8-16`, `:221-229`, `usage.rs:12-15`, and
     **the published `Cargo.toml:5`**.
- **CANARY (RED first — both pass today and must fail)** — `fabricated_settle_receipt_is_rejected` (a line
  padded with an unsigned/forged receipt → `Err`); `inflated_amount_on_a_real_receipt_is_rejected` (a real
  settled receipt for a turn that moved 20, presented on a line claiming 999_999 → `Err(LineDoesNotTrace)`).
  *Under the fix the amount is derived, so the claim cannot be typed at all.*
- **Raise to HIGH** the moment billing is on a path where a bill is presented to a paying counterparty.

### M31 — three authorings of "the ONE source of truth" for the product domain, and they disagree · **medium**

- **CLAIM** — `sdk-ts/src/endpoints.ts:2`: "Dregg endpoints — **the ONE SOURCE OF TRUTH** for the
  production domains (TS side)." · `:43`: "**The CURRENT PRODUCTION domains**" over
  `devnet: "devnet.dregg.fg-goose.online"`. · `:4` "Mirrors the Rust `dregg_sdk::endpoints` module" —
  **true, and that is the defect: it faithfully mirrors a peer that is also stale.**
- **TRUTH** — three authorings, bound by nothing but a label:
  ```
  sdk/src/endpoints.rs:53        pub const DEVNET: &str = "devnet.dregg.fg-goose.online";
  sdk-ts/src/endpoints.ts:46     devnet: "devnet.dregg.fg-goose.online",
  extension/src/endpoints.ts:22  export const DEFAULT_DEVNET_DOMAIN = "node.dregg.net";
  ```
  The truth is **one file away, same language, same author** — `extension/src/endpoints.ts:11-14`: "The
  prior default (`devnet.dregg.fg-goose.online`) was the **RETIRED devnet-era domain**; the product surface
  is `dregg.net`." The retirement sweep is real and documented
  (`GOAL-MULTICHAIN-SETTLEMENT.md:565` "(4) fg-goose retired→node.dregg.net") and reached
  `extension/manifest.json:19-20`, `manifest-firefox.json:19-20`, `settings-script.js:4-5`,
  `settings.html:72-76` — **and left both "source of truth" modules behind.**
- **The mirror is defended by CI** (M13's shape): `sdk/src/endpoints.rs:176`
  `assert_eq!(e.devnet, "devnet.dregg.fg-goose.online");` — **correcting the domain turns a green test RED.**
- **BREADTH (the reporter under-counted)** — four first-party consumers trust it:
  `dregg-tui/src/main.rs:871`, `discord-bot/src/config.rs:70` (both `from_env().devnet_url()`), and
  `sdk-ts/extension/src/background.ts:30` (`const DEFAULT_NODE_URL = devnetUrl()`). **The strongest evidence
  and the reporter missed it: TWO browser extensions in this repo boot with DIFFERENT default node hosts** —
  `extension/src/background.ts:156` → `node.dregg.net`; `sdk-ts/extension/src/background.ts:30` →
  `devnet.dregg.fg-goose.online`. Same author, same repo, same purpose.
- **IMPACT (the reporter over-counted — and its fix is UNSAFE)** — DNS via 1.1.1.1:
  `node.dregg.net` → **A=[] CNAME=[] — NO RECORD AT ALL**; `devnet.dregg.fg-goose.online` →
  `A=[34.224.208.52]`, `curl` → 000 (no answer). **Neither default reaches a working node**, so the staleness
  is true but **inert**. The extension's value is **aspirational, not live** — a third guess that is
  better-*labeled*, not a source of truth to copy. **"Retarget both to `node.dregg.net`" would repoint the
  SDK, TUI, and Discord bot at a host with no DNS record**: stale-but-resolving → unresolvable.
- **FIX**
  - **STEP 0 (BLOCKING, ember-gated)** — **DECIDE the host and CREATE the DNS.** Until a host answers, fix
    the **lie** (Step 3) and the **structure** (Step 2) without touching the literal.
  - **STEP 1** — one hand-authored copy: `sdk/src/endpoints.rs::defaults`. Interrogate the un-swept siblings
    too (`hosting=dregg.works`, `portal=portal.dregg.studio`).
  - **STEP 2 — GENERATE, do not mirror** (Rust and TS cannot share a constant): emit one `endpoints.json`
    from `sdk/src/endpoints.rs`; generate `sdk-ts/src/endpoints.ts`, `extension/manifest.json` +
    `manifest-firefox.json` host_permissions, and `settings-script.js` from it; check them in; CI
    regenerates and runs **`git diff --exit-code`**. `extension/src/endpoints.ts:16-18` **already honestly
    documents why these cannot import** (a browser extension needs literal hosts in the manifest) — *that is
    exactly why the gate must be generation + diff-check, not an import.* Fold both extensions' backgrounds
    onto the resolved value.
  - **STEP 3** — `endpoints.rs:175-190`: **assert the INVARIANT, not the string** (`from_env()==production()`,
    and `devnet_url()==format!("https://{}", defaults::DEVNET)`) so the test **cannot go stale by
    construction**. *A test that must be hand-edited whenever the truth changes is the mechanism, not the
    guard.* Delete "the ONE source of truth" from `endpoints.ts:2` (once generated it is a tautology; until
    then it is false) → "GENERATED from `sdk/src/endpoints.rs` — do not edit by hand." Sweep
    `sdk-ts/src/client.ts:372`, `deploy/games/.env.example:55`, `deploy/games/caddy/Caddyfile.games:16`.
- **CANARY (RED first)** — a CI check greping the tree for `fg-goose` outside `SUPERSEDED/` and historical
  logs, failing on any hit in `src/`. **It must be RED today** (it will fire on `endpoints.rs:53`,
  `endpoints.ts:46`, `client.ts:372`). *The sweep reached 5 extension files and missed 2 SDK modules because
  nothing was watching; that is the hole to close, not this one string.*

---

## VARIANT F — lean-models-reauthored-shape

### M25 — `registryCaveats` models 3 of the deployed 10 constraints and calls itself "exactly" the program; the Lean `#guard`s the impostor hole as ADMITTED · **medium**

- **CLAIM** — (1) `NameserviceGated.lean:84-86`: "the registry cell's factory-installed SLOT CAVEATS —
  **exactly the dregg1 nameservice program**." (2) `nameservice/tests/verified_correspondence.rs:1`:
  "**# Verified-correspondence tests — the SHIPPED nameservice IS the verified one.**" (3) `:9-12`: "the
  shipped turn is the verified one, **not merely a spec-twin that drifted**."
- **TRUTH** — `registryCaveats` = **3** caveats. The deployed `name_cell_program()` (`src/lib.rs:237-256`)
  = **10**: the 3 legacy **plus** `owner_authorization_constraints()` **F1-F7** (`:308-357`), pinned via
  `name_child_program_vk() = canonical_program_vk(&name_cell_program())` (`:370-372`) into
  `name_factory_descriptor().child_program_vk` (`:412`). **The word "exactly" is the lie.**
- **THE FACT THAT SETTLES IT — two files, same author, opposite assertions about the same slot:**
  `NameserviceGated.lean:75` says OWNER_HASH has "**no caveat: ownership moves**";
  `nameservice/src/lib.rs:258-264` says of that same slot: "The problem these close: the slot caveats **used
  to be silent about *who* may write [`OWNER_HASH_SLOT`]**, so an impostor's `SetField(OWNER_HASH_SLOT, ..)`
  **passed `CellProgram::evaluate`**." **The Lean is a verified model of the impostor hole.**
  `NameserviceGated.lean:345` `#guard ((execFullForestG reg0 (transferNode goodCred 8)).isSome)` machine-
  asserts a credentialed transfer **COMMITS with no owner caveat** — the deployed program **refuses that
  exact turn** for a non-owner via F1/F2.
- **NOT A VULNERABILITY** — `fresh_program()` (`verified_correspondence.rs:41-43`) reads
  `name_factory_descriptor().state_constraints`, which extends with `owner_authorization_constraints()` at
  `:446`, so the five Rust tests **do** evaluate the full 10-constraint set and are non-vacuous. **The Rust
  teeth are live and real.** Because `CellProgram::Predicate` is a **conjunction** ("evaluates every
  constraint on every transition", `:250-254`), the deployed program admits a strict **SUBSET** of the
  model's admitted set ⇒ Lean theorems 2/3/4 (all `= none`) **transfer for free**. *What is mirrored is the
  CLAIM OF VERIFICATION, not the code.* **The correspondence file never states that monotonicity argument —
  the only thing actually holding its correspondence up.**
- **REFUTED PREMISES (carry these):** ✗ "F1-F7 are not expressible even in principle" — **FALSE**, see M32
  (`Program.lean` has `anyOf`/`senderInField`/`TurnCtx.sender`). Narrow claim: not in **`SlotCaveat`**.
  ✗ "the Lean models the PRE-FIX program" — unprovable (single squashed commit). The charge is
  **subset-asserted-as-exact**. ✗ `:9-12`'s sentence enumerates "the WriteOnce/Monotonic caveat set" — and
  **that set does match**; the overclaim lives in the unqualified `:1` headline and the Lean's "exactly".
- **FIX — TIER 1 (docs; do now):** `Lean:84-86` → "**THREE of the TEN** `StateConstraint`s… F1-F7 are NOT
  modelled here: `SlotCaveat` has no `anyOf`/`senderInSlot`. **SOUNDNESS DIRECTION:** `Predicate` is a
  conjunction, so the deployed program admits a SUBSET ⇒ every `= none` theorem transfers; **the positive
  `#guard`s do NOT**." `Lean:75` → strike "no caveat: ownership moves"; say the deployed program gates it
  with F1/F2. `Lean:345` → annotate "true in THIS MODEL; the deployed program REFUSES this for a non-owner."
  `verified_correspondence.rs:1` → "Correspondence tests — **five of the shipped program's ten
  constraints**"; `:9-12` → state the subset/conjunction argument the file actually depends on, and say
  **F1-F7 has NO Lean coverage.**
  **TIER 2 (the real closure, cheaper than it looks):** write `Dregg2/Apps/NameserviceOwned.lean` over
  `Program.lean`'s `RecordProgram` (template: `RelayOperator.lean` — `relayProgram:72`, `relayStep:109`,
  `bond_decrease_needs_dispute:180` is already the F1 shape, proved) carrying the 10-constraint
  transcription, and prove `ns_impostor_cannot_seize` + F3/F4/F5 + F7. ⚠ **same arrow caveat as M32.**
- **CANARY (RED first)** — **non-vacuity gate on Tier 2:** a `#guard` exhibiting the **owner-signed transfer
  COMMITTING** alongside the impostor's rejection — *otherwise this reproduces the same bug in a new
  language.* Then the Rust side must add: an impostor `SetField(OWNER_HASH_SLOT)` rejected by F1, an atomic
  stage-and-seize rejected by F5, a register-with-zero-OWNER_PK rejected by F7 — **each with its owner-signed
  positive twin.**

---

## VARIANT G — doc-claims-absent-seam

### M29 — the blog deck tells its reader the dense twin is the page they are already on · **high**

- **CLAIM** — `~/dev/dregg-site/templates/blog.html:11`: "The dense engineering ledger lives at
  `<a href="https://emberian.github.io/dregg/deep/">the technical twin</a>`. **This is the readable one.**"
- **TRUTH** — the href is **hardcoded absolute**, so zola's base_url rebase does not rewrite it. The page
  served at `emberian.github.io/dregg/deep/blog/` tells its reader the dense ledger is at
  `…/dregg/deep/` — **where the reader already is.** A single deployed page names **two different URLs as
  "the technical twin"**: `site/deep/blog/index.html:51` (→ itself) and `:72` (the base.html footer →
  `/dregg/`). **The rewrite mechanism demonstrably works and was bypassed:** `templates/base.html:56` uses
  `{{ config.base_url | safe }}/receipt/` and correctly rendered to `…/dregg/deep/receipt/`. **blog.html:11
  sits two lines from a working idiom it declined to use.**
- **THE ESCALATION — the reporter was too charitable.** It conceded "On `www.dregg.net/blog/` the sentence
  is at least directionally honest (it points off-site)." **That concession is FALSE.**
  `diff -rq dregg-site/public site/deep` → 35 differing files, and **every hunk of every one is base_url
  rewriting. Zero prose differs.** There is exactly ONE zola site (`config.toml:1 base_url =
  "https://www.dregg.net"`) built twice at two base_urls. **THE DENSE/ACCESSIBLE SPLIT DOES NOT EXIST.** So
  the sentence has **no true instantiation on either deployment**: on the twin it points at itself; on
  dregg.net it points at a URL-rewritten clone of dregg.net and calls that clone "the dense engineering
  ledger."
- **The truth is two files away, same templates dir** — `templates/base.html:53`
  `<a href="https://emberian.github.io/dregg/">Technical twin</a>` and `templates/why.html:80` "the dense
  index written for you is at `<a href="https://emberian.github.io/dregg/">the technical hub</a>`" — both
  pointing at the **hub**. **`blog.html:11` is the one place that promotes `/deep/` to that role.**
- **LIVE?** YES on both deployed sites. `scripts/build-pages-dist.sh:97` ships it, and asserts its existence
  at `:105`.
- **⚠ DO NOT APPLY THE REPORTER'S FIX AS STATED** — retargeting `blog.html:11` to
  `https://emberian.github.io/dregg/` cures the self-reference but **keeps the "dense ledger" falsehood**:
  density probes on `site/root/index.html` give theorem:1, lemma:0, axiom:0 vs `site/deep/index.html`
  theorem:2 — **comparable landing pages.** That fixes the symptom the reporter named and leaves the lie it
  actually proved.
- **FIX** — delete the false distinction. Replace the deck with a claim that survives **both** builds and
  cannot self-reference under **any** base_url:
  ```html
  <p class="page-deck">Notes from the workshop. The engineering record lives in
    <a href="https://github.com/emberian/dregg">the source</a>.</p>
  ```
  **Do NOT hand-edit** the rendered `site/deep/blog/index.html:51` or `public/blog/index.html:51` — they are
  generated; the next zola run restores the sentence.
- **THE REAL DECISION (ember-gated, not a code edit)** — either **(a)** build a genuinely dense twin
  (deep-only content in the zola source behind a shortcode/flag, so the two builds differ **in PROSE**), or
  **(b)** retire the dense/accessible framing everywhere. **Until (a) ships, every sentence promising a
  dense counterpart is [[feedback-describe-at-current-not-intended-resolution]].**
- **CANARY (add to the build)** —
  ```
  diff <(sed 's|https://www\.dregg\.net|BASE|g' dregg-site/public/blog/index.html) \
       <(sed 's|https://emberian\.github\.io/dregg/deep|BASE|g' site/deep/blog/index.html)
  ```
  **Today this is EMPTY — which is the proof the twin is a mirror.** If (a): this diff **must become
  non-empty in prose**. If (b): assert instead
  `! grep -rn 'dense engineering ledger\|the readable one' site/deep/ dregg-site/public/`.

### M28 — `site/deep` is sold as "the pretraining-grade dense twin"; it is the same bytes with a substituted base_url · **medium**

- **CLAIM** — `scripts/build-pages-dist.sh:93-96`: "deep — **the full dense product site (the
  pretraining-grade twin of dregg.net)**: every page with its **theorem names, test counts, and seam ledgers
  intact**… **dregg.net carries the accessible layer and links here per-page**." · `site/README.md:9-18`
  promotes the same absent split ("deliberately two sites… the technical half: written for LLMs, experts,
  and developers. Dense, heavily cross-linked").
- **TRUTH — two falsifiable halves, both false.**
  (a) **Density:** `grep -c theorem site/deep/receipt/index.html ~/dev/dregg-site/public/receipt/index.html`
  → **27 and 27.** The "full dense product site" retains **nothing** the "accessible layer" shed.
  (b) **"per-page":** `grep -rln "dregg/deep" ~/dev/dregg-site/templates/ content/` → **exactly ONE file**
  (`templates/blog.html`). The every-page footer (`base.html:53`) links `https://emberian.github.io/dregg/`
  — the **hub** — not `/deep/`. **One page is not per-page.**
  `site/README.md`'s own Layout table lists root/, assets/, explorer/, … and **no `deep/` row at all** —
  *the deploy ships a verbatim clone of the human-facing site under the technical site's banner,
  undocumented in the file that documents the technical site.* `grep -n "deep" site/root/index.html` → **no
  output**: the deployed hub does not link its own twin.
- **CORRECTIONS TO THE REPORTER (all strengthening)** — normalize+diff produced residuals on **11** files,
  not 1; `site/deep` holds **60** tracked files / **37** HTML+XML, not 80/40. Every residual is the **same**
  base_url substitution, HTML-entity-escaped (`https:&#x2F;&#x2F;`) in the `og:url` meta, which the `sed`
  could not reach. **Correcting the arithmetic makes the mirror MORE verbatim, not less.**
- **LIVE?** YES — `build-pages-dist.sh:97` copies all tracked files into the Pages dist;
  `.github/workflows/pages.yml:243` runs it. Deployed, and **per the comment aimed at pretraining crawlers**.
- **FIX — do not delete the mirror** (a crawlable self-hosted copy under the repo domain is defensible):
  1. `build-pages-dist.sh:93-96` → "deep — a **verbatim mirror** of the dregg.net product site (zola output
     from `~/dev/dregg-site`, re-rendered with base-url `.../deep`). **Identical content, NOT a denser
     variant**: it exists so the product pages are crawlable under this domain and survive independently of
     the dregg.net deploy. The dense technical layer is the hub at `site/root/index.html`." Drop all four
     false phrases.
  2. `site/README.md` — keep the **real** split (dregg.net = narrative; `root/index.html` = the hub, which
     genuinely IS different: 25KB of verified repo links vs a 13KB narrative index) and add the missing
     Layout row for `deep/` marking it generated ("do not hand-edit").
  3. Optional: `site/root/index.html` links neither dregg.net nor `/deep/` — if the hub is the technical twin
     the footer advertises, it should link the product site back.
- **CANARY** — shared with M29 (the normalize+diff). **It is empty today; that emptiness IS the finding.**

### M34 — `verified_settle`'s header says the Lean FFI decides every leg "on every native build"; there is no feature, and the Rust mirror decides for every consumer but `node` · **medium**

- **CLAIM** — `:19-24`: "**On every native build (Lean unconditional), each leg is settled by the REAL Lean
  FFI**… **NOT a Rust mirror. When the feature is off**, the in-process `rec_exec_asset` runs the SAME
  verified transition." · `:306-310`: "**with the feature on**, the fold's **accept/reject** and post-ledger
  **ARE the linked verified executor's**, leg by leg — not a Rust mirror." Duplicated at
  `trustless.rs:1628-1635`.
- **TRUTH** — **there is no feature.** `intent/Cargo.toml` declares `[features] default = []` — dregg-intent
  has **none**. (`no-lean-link` exists only on *other* crates; `intent/Cargo.toml:36` itself says "The
  deleted `no-lean-link` feature is now a dependency choice, not a flag.") The gate is a **runtime
  `OnceLock`** (`verified_gate.rs:20-30`) and the cross-check **silently no-ops** when unset
  (`:701-703`: `if crate::verified_gate::gate().is_none() { return Ok(()); }`). **The header contradicts
  itself in one breath** — "Lean unconditional" **and** "when the feature is off" — the fossil of the deleted
  gate.
- **STRONGER THAN REPORTED** — `starbridge-apps/sealed-auction/Cargo.toml` and `tussle/Cargo.toml` have **no
  `dregg-exec-lean` dependency at all**. In those processes the gate is not merely unregistered — it is
  **structurally unregisterable**. Only `node/src/lib.rs:572` and
  `exec-lean/tests/fulfillment_ffi_verified.rs:34` ever register.
- **THE ALTITUDE SHAPE, EXACTLY** — the **downstream consumers are HONEST**: `tussle:43-47` ("with no gate
  registered (this crate's own process, tests included) the fold is the in-process Rust mirror — no FFI
  cross-check runs"), `sealed-auction:27-31` same. **The false claim lives ONLY in the module that owns the
  mechanism.**
- **THE REJECT ASYMMETRY** — `settle_ring_verified:318-333` returns `LegRejected` from the `None` arm
  **before** `ffi::cross_check_leg` is called. So the reject verdict is **never** cross-checked even WITH a
  gate registered. Fail-closed ⇒ not a value hole — but `:306-310` claims "accept/**reject**… ARE the linked
  verified executor's."
- **Not a value hole:** `rec_exec_asset` implements a conservative gate (amount ≥ 0, ≤ src_bal, from ≠ to,
  both cells live) and the fold asserts per-asset conservation fail-closed. **The harm is TCB
  misrepresentation:** the module owning the mechanism tells an auditor the PROVED Lean executor decides
  every shipped settlement, when unproven Rust decides for every consumer except `node`.
- **FIX** — rewrite `:19-26`, `:306-310`, `trustless.rs:1629-1633` to the runtime truth, mirroring the
  honest wording tussle/sealed-auction already use. Delete "On every native build (Lean unconditional)",
  "NOT a Rust mirror", "When the feature is off". State the asymmetry explicitly.
  **TOOTH A** (closes the asymmetry): add `ffi::cross_check_leg_rejected` on the `None` arm — no-op when
  unset, else `FfiDivergence` if the export reports `ok == true`.
  **TOOTH B** (pins the mirror): the mirror's fidelity rests on **prose** —
  `RingFFI.ffi_export_realises_settleRing_leg` is **Lean-to-Lean** and does **not** constrain
  `rec_exec_asset`; the header itself dismisses `tests/ring_settlement_differential.rs` as "verified by
  prose". Add a differential in `exec-lean/tests/` (the only crate that can reach the FFI) driving
  `rec_exec_asset` vs `ffi::settle_leg` over a corpus covering **both arms**.
- **CANARY (RED first)** — mutate `rec_exec_asset`'s bound (e.g. `amount <= src_bal` → `<=
  src_bal + 1`) and confirm Tooth B's differential goes **RED**. Today **no test anywhere** would catch it
  for the 6 non-`node` consumers.

---

# §2 — RANKING

## §2.1 By severity

| Rank | ID | Severity | Why it ranks here |
|---|---|---|---|
| 1 | **M30** | **HIGH — soundness, PUBLISHED** | Breaks **every SDK-issued capability grant** on `@dregg/sdk@0.3.0`; postcard desync can decode to **a different action than the one signed**. The only finding shipped to third parties. Its guard has **never run in CI**. |
| 2 | **M26** | **HIGH — soundness** | The **SCOPE tooth does not exist**: `exercise` takes no tool argument, so a mandate scoped to tool 77 meters tool 99. `hprog` is false of every real cell ⇒ the Lean says nothing about the app. |
| 3 | **M33** | **HIGH — soundness** | Book built from self-asserted `offer_amount`; `mirror_conserves` is `x <= x`; the verified kernel **cannot** backstop it (`funded_ledger` conjures the funds). Fixture consumed on-chain by `DreggVault.escrowRelease`. |
| 4 | **M32** | **HIGH — proof-scope** | Vacuous theorem cited as a mechanized grounding on **5 surfaces incl. the paper and the public deploy-gate**. No executor hole (native proof is real) ⇒ integrity defect, not a bug. |
| 5 | **M29** | **high** | Two deployed public surfaces; root cause falsifies M28 too. Website copy — no proof/capability/value path. |
| 6–13 | M22, M23, M24, M25, M27, M28, M31, M34 | medium | Dead tripwires, false claims, TCB misrepresentation. **No exploitable hole in any.** |

**Honest note on the mediums:** every one was *offered* a higher severity by its reporter's framing and
**declined it on evidence** (M27 is strictly weaker ⇒ no production hole; M24's digest is an audit payload,
not a gate; M25's Rust teeth are live and the conjunction makes the Lean rejections transfer; M34 is
fail-closed). **M31 was raised on breadth and lowered on impact** (no DNS record on any of the three
authorings). *Resisting inflation is the point — a map that cries soundness everywhere cannot be ranked.*

## §2.2 By leverage — the lanes

### L9 — **CARRY THE OBJECT, NOT ITS NAME** · closes **M22**, and is the rule the counter-example proves (§4)
`SettleReceipt{hash, amount, asset, period}` → `SettleReceipt{receipt: TurnReceipt, turn: Turn}`.
**The bind (`turn.hash() == receipt.turn_hash`) becomes EXPRESSIBLE the moment the real object is in
scope — and once expressible it gets written.** Template already in the same directory:
`agent-orchestration/src/lib.rs:544-558` + `audit_run:1063`. *Highest truth-per-line in sweep two.*

### L10 — **POINT THE CORPUS AT THE ROLE** · closes **M23** · **four tokens**
`officer_labels() -> vec![officer_label()]`. Both helpers already `pub` (`lib.rs:173,177`); the pinned
literal **does not change**. Then audit `sgm_lean_differential.rs` and fix
`VERIFICATION-TOOLKIT-GUIDE.md:171`, **which ships this file as the template for every future app**.
*Cheapest fix in either sweep; stops propagation.*

### L11 — **THE ORACLE IS A BUILD INPUT, NOT A FOUND ARTIFACT** · closes **M30 + M24**, prevents the STALE-ORACLE shape
`"pretest": "wasm-pack build ../wasm"` + a checked-in shared vectors file + `npm test` in CI.
**A differential that compares against a gitignored build artifact is a differential against a frozen
mirror.** *Best severity-per-effort in sweep two: ~10 lines closes the only published soundness hole.*

### L12 — **DERIVE THE BOOK FROM THE BACKING** · closes **M33**
Bind `mirror_legs`→`parties` by `party_byte` **before** the book is built; make `locked`/`minted` two
**independently-sourced** quantities. *Kills a dead field, a tautology, and a mis-titled falsifier at once.*

### L13 — **INHABITATION WITNESS REQUIRED** · closes **M32**, and opens the whole Lean-vacuity class
§4 has `fires` at `:416-421`; §5 has none. **Make §4's convention a rule.** Generalizes far past this file —
see §5/G4.

### L14 — **DOC STRIKE + THE SUBSET ARGUMENT** · closes **M25, M28, M34**, and the doc legs of M22/M23/M27/M32
Mostly deletions. **The one piece of real content:** M25's fix must *add* the soundness argument
(`Predicate` is a conjunction ⇒ deployed admits a subset ⇒ `= none` theorems transfer, positive `#guard`s do
not) — **the only thing holding the correspondence up, which the file never states.**

### L15 — **GENERATE THE DOMAIN** · closes **M31** · ⚠ **STEP 0 is ember-gated** (no DNS record exists)

---

# §3 — CALIBRATION: did sweep one's estimate hold?

**This section matters more than the list.**

## §3.1 The count — **HELD, trending LOW**

| | Sweep one | Sweep two | Total |
|---|---|---|---|
| Confirmed findings | 21 | **13** | **34** |
| Subsystems swept | 13 | 7 (starbridge×3, circuit-goldens, site/deep, js-ts-py, lean-vacuity, unswept-crates) | 20 |
| Crates in scope | ~13 of ~186 | +31 starbridge (partial) + 4 non-Rust surfaces | still **well under half** |

Sweep one's estimate: **35-60 total instances at HEAD.** We stand at **34 after two sweeps**, with the
light clients, `deos-*`, `grain-*`, `chain/`, `crypto-*`, and most of `metatheory/` **entirely unswept**.
**The estimate HELD and is trending to the LOW end of its own band** — i.e. it will be *exceeded*, not
missed. Corroboration that is not extrapolation: **the mirror-gate suite reports 42 machine findings and 71
advisory leads** (§5). Those are unverified leads, not confirmed instances — but if even a third confirm,
the population clears 45 and the band's **upper** half is the honest bet.

## §3.2 The soundness count — **HELD, dead centre**

Sweep one predicted **2-5 more at soundness-hole severity.** Sweep two found:

- **M26** (TAD — scope tooth does not exist) — soundness
- **M30** (sdk-ts wire — every capability grant, **published**) — soundness
- **M33** (drex_routing — unbacked offers reach an on-chain fixture) — soundness
- *(**M32** SeL4 — HIGH, but proof-scope: the vacuity is real, the executor is not holed)*

**3 genuine + 1 adjacent = squarely inside 2-5.** The predictive model was sound.

## §3.3 The location — **WRONG, and this is the finding**

Sweep one ranked its expectations (§4.3). Scored:

| Predicted | Result |
|---|---|
| **1. `starbridge-apps/*` — "the single largest gap and the highest prior"** | ✅ **HIT** — 5 findings (M22, M23, M24, M25, M26) incl. the **HIGH** M26. Prediction vindicated. |
| **3. the unaudited descriptor set (the M13 shape)** | ⚠ **PARTIAL** — M27 confirmed the shape, but came in **medium** (strict subset ⇒ strictly weaker ⇒ no production hole), **not** the predicted soundness severity. |
| **2. the rest of `metatheory/`** | ✅ **HIT** — M25 + M32. |
| **4. the light clients (host-vs-proven)** | ⬜ **NOT SWEPT** — still open (§6). |
| **§4.4 "did NOT look for at all": TS/Python SDKs, JS runtime, `site/deep`** | 🔴 **THE MISS** — yielded **M30 (HIGH, published), M24, M31, M28, M29**: **5 of 13, including the worst finding in either sweep.** |
| **§4.4 "did NOT look for at all": Lean vacuity / hypothesis-bearing statements** | 🔴 **THE MISS** — yielded **M32 (HIGH)**, a **new variant**. |

**The calibration lesson, stated plainly:** sweep one's *ranked* list was accurate about where the disease
**lives**. It was wrong about where the disease is **worst**. **The highest-severity finding in this entire
audit (M30) came from the bucket labeled "did not look for at all"** — not from the top of the ranked
high-expectation list. The `site/deep` line in §4.4 even *named the exact question* ("whether it drifts is
exactly this question **and was not asked**") — and the answer was: it does not drift, because **it is not a
twin at all** (M28/M29).

**Why the miss was structural, not an oversight:** sweep one's instruments were Rust-shaped. A sweep hunts
where its tools can see. **`starbridge-apps` was predicted highest because it is Rust and legible;
`sdk-ts` was unranked because nothing in the toolkit could read it** — and that is *precisely* why its guard
had rotted for two weeks with a published npm package downstream. **The unswept-because-unreadable territory
is not lower-risk; it is lower-observed.** *Absence of evidence was read as evidence of absence, and the
gates (§5) encode the same bias.*

---

# §4 — THE STRUCTURAL LAW, AND THE COUNTER-EXAMPLE

## §4.1 Does the law hold? **13/13 — and it TIGHTENED.**

Sweep one: *"the truth is almost always already written down, one file away, by the same author. The lie is
a promotion."* In sweep two the distance **shrank**:

| ID | Where the truth already is | Distance |
|---|---|---|
| **M30** | The **same function** quotes the `serde(default)`-not-`skip_serializing_if` rule **verbatim** for `allowed_effects` — and misses the newer field carrying the identical annotation | **same fn** |
| **M32** | **§4 of the same file** carries a `fires` witness at `:416-421` + five satisfiability examples; **§5 carries none** | **same file** |
| **M24** | **§2 of the same file** (`test_mcp_default_costs_match_rust`) pins real cross-language literals; §3 pins nothing | **same file** |
| **M33** | The falsifier at `:203` is **titled correctly** ("never enters the book") and never calls `route` | **same file** |
| **M23** | `colonist_job.rs:458-465` `crafter_labels() -> vec![crafter_label()]` does it right | same crate |
| **M22** | `agent-orchestration/src/lib.rs:544-558` | same dir, same template |
| **M25** | `nameservice/src/lib.rs:258-264` asserts the **opposite** of `NameserviceGated.lean:75` about the same slot | one file |
| **M26** | `polis/src/service.rs:88-94` already deploys the `AllowedTransitions` machine | sibling app |
| **M27** | 3 sibling goldens are **identical** to their deployed twins | same dir |
| **M28/M29** | `base.html:53` + `why.html:80` point at the hub **correctly** | same templates dir |
| **M31** | `extension/src/endpoints.ts:11-14` **names the retired domain as retired** | same language |
| **M34** | `tussle:43-47` + `sealed-auction:27-31` are **honest**; only the owning module lies | downstream |

**Sharpened diagnosis:** *prose has no compiler* (sweep one) is a special case of the deeper rule —
**an identifier is prose.** M30's mirror is not a distant copy; it is **one missing line in a function whose
own comment states the rule it violates.** No amount of author care closes that. **Only a gate does.**

## §4.2 The counter-example — **CLEAN territory, and WHY**

*This is worth more than another finding, so I verified it rather than trusting its doc-comment — which is
the sin under audit.*

**`starbridge-apps/agent-orchestration` — same directory, same template, same author, same week as
`billing` (M22) — and it is CLEAN.**

```rust
pub struct LoggedStep {
    pub step: WorkStep,
    pub spent_after: u64,
    pub receipt: TurnReceipt,   // the REAL receipt — sig, turn_hash, effects_hash, pre/post
    pub turn: Turn,             // "turn.hash() == receipt.turn_hash binds this"
}
```
**And the doc-claim has an executable dual** (verified, not assumed):
- `lib.rs:103` — `use dregg_turn::{TurnReceipt, VerifyError, verify_receipt_extends};` — the **real** verifier
- `lib.rs:117` — `verify_receipt_extends(pair[0], pair[1])?;` — **actually called**, pairwise
- **`lib.rs:1063` — `if e.turn.hash() != e.receipt.turn_hash { return Err(AuditError::TurnReceiptMismatch { ordinal }) }`** — **the bind its comment claims, performed**

**WHY it is clean — the replicable rule:** it **carries the object** (`receipt: TurnReceipt`, `turn: Turn`)
instead of **re-typing the object's name** (`SettleReceipt{receipt_hash: [u8;32], amount, asset}`).
Once the real objects are in scope, the bind is **expressible** — and *what is expressible gets written and
checked*. Billing carried a **32-byte hash**: the bind was **inexpressible**, so it degraded into a doc
sentence, and the sentence went into the **published `Cargo.toml`**.

> **A hash field is a foreign key with no database.** It *looks* like a binding and *checks* like a comment.

**The other clean sites confirm the same mechanism, and rank by strength:**

| Clean site | Why | Replicable? |
|---|---|---|
| `agent-orchestration` `LoggedStep`/`audit_run:1063` | **Carries the object; the bind is expressible ⇒ written ⇒ checked** | ✅ **the rule** |
| `colonist_job.rs:458-465` `crafter_labels` | Feeds the **role** label ⇒ the corpus **traverses the real graph** ⇒ the mutation bites | ✅ |
| M24 §2 cost map | Pins **real cross-language literals** — a shared value, not a parallel assertion | ✅ |
| M27's 3 sibling goldens (accumulator, quantified-absence) | **Pinned by a Lean `#guard` that names them** ⇒ a second author the artifact cannot outvote | ✅ |
| sweep one's `register_surfaces` | **Shared, not copied** | ✅ |
| M30's `AuthRequired` enum | **"The enum that did not change did not drift"** | ❌ **clean by stasis, not design** |

**`AuthRequired` is the control that proves the rule is not about care.** It is clean **only because nothing
changed.** `CapabilityRef` — same file, same author, same reviewer — gained a field and drifted **within two
weeks**. *Drift is a function of change under a dead gate. Every clean-by-stasis site is a finding waiting
for its next field.*

**What to replicate, in one line:** **share the value, or carry the object, or pin it from outside — never
re-type it and never name it.** Every clean site in this tree does exactly one of those three. Every finding
in both maps does none of them.

---

# §5 — DO SWEEP ONE'S GATES CATCH THESE? **MEASURED: 0 of 13.**

**Sweep one's D1/D2/D3 are BUILT and RUNNING** — `scripts/mirror-gates/mirror_gates.py` implements A1, A2,
D1, D2, D3. That is real progress and it is working: **it filed sweep one's own named-unfiled items** —
`circuit/src/presentation_descriptor_witness.rs:179` and `blinded_membership_witness.rs:347` both fire as
**A2-golden-is-the-artifact** (sweep one §4.3 cited them at the wrong path, `circuit-prove/tests/`; they live
in `circuit/src/`).

**Measured run** (`python3 scripts/mirror-gates/mirror_gates.py`): **42 findings, 71 advisory leads**
— 20 `A1-second-author`, 12 `D3-tested-twin-is-not-the-deployed-one`, 4 `A2-golden-is-the-artifact`,
6 `D2-*`.

**Coverage of sweep two's 13 findings — grep of the gate output for each finding's site:**

| Site | Gate hits | Verdict |
|---|---|---|
| `billing`, `compartment-workflow-mandate`, `tool-access-delegation`, `site/deep`, `sdk-ts`, `endpoints`, `SeL4Abstract`, `drex_routing`, `verified_settle` | **0** | invisible |
| `adjacency_membership` | 2 — but **A1 on `adjacency_membership_emit_gate.rs:46`**, the emit gate **next door**. `grep -c adjacency_membership_golden_audit` → **0** | **M27 invisible** |
| `nameservice`, `agent-orchestration` | 5, 4 — but **D3 on *different* findings** (`name_invariants_program` / `board_service_program` service-twins), not M25/M22 | different finding |

**0 of 13.** And the gates are **not weak — they are Rust-and-artifact-shaped**, encoding the same bias that
produced sweep one's location miss (§3.3):

1. **`A2` exempts single-loader goldens by design** — `mirror_gates.py:480`:
   `continue  # nothing else loads it: the const IS the loader, not a "golden"`. **A2 only fires when a
   SECOND loader reads the same path.** M27 sits exactly in that hole. **I measured the hole's width:** the
   tests-local private-golden shape has **exactly 4 instances** —
   `accumulator_nonrev_golden.json`, `adjacency_membership_golden_audit.json`,
   `committed_threshold_golden.json`, `quantified_absence_golden.json` — **all four invisible, and 1 of 4
   has already drifted.**
2. **No non-Rust reader** ⇒ M24 (.py), M30/M31 (.ts), M28 (.sh), M29 (.html) cannot be seen. *The gate cannot
   read the file where the only published soundness hole lives.*
3. **No Lean semantics** ⇒ M32's uninhabited bundle is invisible (`#assert_all_clean` is **blind to
   hypotheses** — the file's own sibling states this rule at `fri_params_soundness_budget.rs:50`).
4. **D3 only inspects constructors returning program/world/engine** (`mirror_gates.py:88`) ⇒ M22's
   `verify_against_receipts`, M26's `exercise`, M33's `route`, M34's `settle_ring_verified` are all
   **deciders, not constructors** — out of scope by construction.

## §5.1 The gates this territory needs

Ranked by (class caught) ÷ (cost). Each is buildable against the existing harness.

### **G1 — KILL THE SINGLE-LOADER EXEMPTION** · catches M27 + the 4-file blind spot · **~2 hours**
`mirror_gates.py:480` currently exempts any golden whose only reader is its own `include_str!`. **Invert it:**
a `*_golden*` artifact under `tests/` must have **an author the artifact does not have** — a Lean `#guard`
naming it, or a second in-tree pin. **FAIL when a golden's only reader is its own `include_str!`.**
*That is the exact shape A2's own docstring (`:354-358`) says it is trying to catch.* **Cheapest gate in
either sweep, and it closes a hole with a confirmed live instance.**

### **G2 — THE ORACLE FRESHNESS GATE** · catches M30 · **~half a day** · **the sharpest new signal**
**No differential may compare against a gitignored or untracked artifact.** Mechanically:
for every test importing an oracle, resolve it to a path; **fail if `git ls-files <path>` is empty and no
`pretest`/build step regenerates it.** `wasm/pkg/.gitignore` = `*`, `git ls-files wasm/pkg` = **0**, oracle
**13 days stale**, guard **never run in CI**, package **published**. **This one check, existing on 2026-07-02,
prevents M30 entirely.**

### **G3 — THE CROSS-LANGUAGE VECTOR GATE** · catches M24 + M30 + M31 · **~1 day**
Any file claiming *"pins/differential/byte-identical/mirrors the Rust"* must name a **checked-in vector
file read by both sides.** **A differential whose two sides share no literal is not a differential — it is
two parallel assertions of the same reconstruction.** Falsifier: *delete the shared vector file; if both
sides still pass, there was no pin.* Extend D2's citation checker to `.ts/.py/.mjs/.sh/.html/.typ`.

### **G4 — THE INHABITATION GATE** · catches M32, opens the Lean-vacuity class · **~1 day**
Any `structure` used as a hypothesis bundle in a payoff theorem **must have a `fires`/example witness in the
same file.** **§4 of `SeL4Abstract.lean` is the in-tree exemplar** (`:416-421` + `:404-414`); §5's silence is
what read as coverage. Pair with the standing rule: **`#assert_axioms` is blind to hypotheses.**
*Sweep one §4.4 named this class and did not look; it yielded a HIGH on first contact.*

### **G5 — D3 FOR DECIDERS, NOT JUST CONSTRUCTORS** · catches M22, M26, M33, M34 · **~2 days**
Extend D3 (`mirror_gates.py:88`) past constructors to **any `pub fn` whose name matches
`verify|check|audit|admit|route|settle|authorize`**, and report where the **fn's own doc names an external
anchor** (a receipt, a lock, a key, an executor) **that appears nowhere in its body.** M22
(`verify_against_receipts` takes no input and never reads `receipt_hash`), M33 (`route` reads `mirror_legs`
only in a tautology), M26 (`exercise` has no tool param) each print as one line.

**Adopt G1 + G2 first** — together **~1 day**, and they close the only published soundness hole plus a
4-file blind spot with a confirmed live drift. **G3 + G5** are the structural pair.

### §5.2 The gate finding sweep one did not anticipate
**The gates found 42 things and both maps together confirmed 34.** Those 42 are *machine leads, not verified
instances* — but they bound the population from a direction that is not extrapolation. Notably **12
`D3-tested-twin-is-not-the-deployed-one` hits, 8 of them in `starbridge-apps`** (`governed-namespace`
`governance_program` vs `governance_service_program`; `polis` `council_cell_program` vs
`council_service_program`; `subscription`; `swarm-orchestration`; `nameservice`; `agent-orchestration`;
`domains`) — **an unfiled `service_program`-vs-`cell_program` twin-engine cluster that neither sweep
adversarially verified.** *That is a systematic pattern across 8 sibling crates, and it is M01's exact
variant.* **Triage it before hunting new territory** (§6).

---

# §6 — THE HONEST REMAINING COUNT

## §6.1 What is STILL unswept after two sweeps

**Entirely unswept (zero findings, zero looked):**
1. **The light clients** — `eth-lightclient`, `cosmos-lightclient`, `solana-*`, `chain/`. **Sweep one
   predicted host-vs-proven here and it was never swept — the prediction is still outstanding.** The Solana
   bridge already carries **3 known exploitable value holes** from a separate audit and **the bridge fold is
   documented UNSOUND**. **Highest remaining prior.**
2. **`deos-*` (13 crates), `grain-*` (6), `crypto-*` (5), `fhegg-*`, `sel4/`.**
3. **`dregg-pq`, `pqvrf`, `dice`, `narrator`, `tee-verify`/`tee-produce`, `zkoracle-prove`, `deco-prove`** —
   attestation/randomness. *Expect fixture-on-live-path (self-signed/modeled carriers) — M18's neighborhood,
   swept for 1 crate of 13.*
4. **Most of `metatheory/`** — M25 + M32 came from **two files**. Untouched: `AssuranceCase.lean`'s **other**
   guarantees, `Circuit/Spec/*`, the 66 Polis files, **the PQ metatheory's FIPS hypothesis** (a named
   hypothesis in a #assert-clean file — **exactly M32's shape, and pre-identified in MEMORY as "gap = 1 FIPS
   hyp"**).
5. **The floors-empty-at-deployed-parameters class** (the resolution-ruler). Named by sweep one §4.4, **still
   not looked at by either sweep.** Orthogonal to mirrors; same family of self-deception.

**Partially swept (findings exist, coverage thin):**
6. **`starbridge-apps` — 5 of 31 crates.** M26 (HIGH) came from crate #5. **`escrow-market`,
   `privacy-voting`, `sealed-auction`, `bounty-board`, `execution-lease` all name teeth in their
   descriptions and remain unexamined** — sweep one's `NotYourLeg` lead is **still unfiled after two sweeps.**
7. **The 26 by-name emit gates + 69 main descriptors.** M27 was 1 of 4 tests-local goldens; **A1 reports 20
   second-author violations** across the emit gates that neither sweep verified.
8. **`sdk-ts` beyond `wire.ts`/`endpoints.ts`; `sdk-py` — ZERO swept.** M30 came from the **first** TS file
   examined. **`sdk-py` has had no sweep at all**, and M24 shows the Python surface carries the same
   claim-register.
9. **The kernel** (`cell/`, `turn/`, `sdk/`) — sweep one's M11/M12 came from two directions; still not
   systematic. `sdk/src/cipherclerk.rs` carries M11's false citation **twice** and is 6000+ lines.

## §6.2 Where I would look third — ranked

1. **TRIAGE THE 42 GATE FINDINGS FIRST — before hunting anything new.** They are already found, already
   localized, and cost only verification. **Start with the 12 D3 `service_program`-vs-`cell_program` twins
   (8 in `starbridge-apps`)** — that is **M01's exact variant across 8 sibling crates**, and M01 was a
   soundness hole. *Cheapest confirmed-finding-per-hour available.*
2. **`sdk-py` + the rest of `sdk-ts`.** The TS/Py surface went **0 → 1 HIGH (published) on first contact**,
   and **G2 does not exist yet**, so any other oracle is equally stale. **`sdk-py` has never been looked at.**
   *Highest expected severity, because this territory ships to third parties.*
3. **The light clients + `chain/`.** Sweep one's own unmet prediction, on a bridge already documented
   UNSOUND with 3 known value holes. *Highest expected value-at-risk.*
4. **The PQ metatheory's FIPS hypothesis + `AssuranceCase.lean`'s other legs.** M32's variant on first
   contact, and **MEMORY already names the FIPS hypothesis as the residual** — run G4's falsifier
   (`¬ Nonempty <bundle>`) against every hypothesis bundle cited by a payoff theorem. *Cheap: the falsifier
   is 8 lines and either compiles or does not.*
5. **The remaining 26 `starbridge-apps`.** 5 of 31 gave 5 findings incl. a HIGH — **a ~1:1 crate-to-finding
   rate**, the highest density in either sweep.

## §6.3 The honest number

**34 confirmed. 42 machine leads outstanding. ~60% of the tree unswept, including all of the
highest-value-at-risk territory.** Sweep one's **35-60** band **holds and will be exceeded** — not because
the estimate was wrong, but because **the two sweeps have now demonstrated the rate does not decay with
effort: 21 findings from 13 subsystems, then 13 more from 7, with the hit rate in `starbridge-apps` running
near 1:1 per crate.** *A sweep that finds a HIGH in the first file of a new surface has not finished that
surface.*

**The deliverable is still not the list.** Sweep one said *"fixing 21 and shipping no gate returns this map
to its current length within two quarters."* **Sweep two is the evidence:** the gates were built, they
**work**, they filed sweep one's own leftovers — **and they caught 0 of 13, because they can only read Rust.**
**M30 is what that costs**: an unreadable surface, a guard rotting on a gitignored artifact for 13 days, and
a false byte-faithfulness claim shipped to npm. **G1 + G2 are one day of work. Ship them before the third
sweep, or the third sweep will find the fourth sweep's findings and leave them for it.**
