# Decoration census — tests that cannot go red

**Swept 2026-07-31.** Scope: every `#[test]` in `starbridge-v2/src` (995) and
`turn/src` (703) — 1,697 tests extracted and analysed by shape, top candidates
mutation-tested against the live tree.

A **decoration** is a test whose name makes a claim its body cannot refute:
amputate the thing it says it guards and it stays green. The program that
produced this census shipped one itself (`views/mod.rs`, now fixed), which is why
the sweep exists.

The bar used here: **a candidate that was not mutation-tested is a SUSPICION, not
a finding.** Findings below carry the verbatim mutation and the verbatim result.

⚠ **Nothing in this census is a licence to mass-delete.** A weak test is often the
only coverage of its path. Every entry says what to *add*, and only one test was
touched (§1, which this census's commit rewrites).

---

## Summary

| # | Test | Shape | Mutation-proved? | Status |
|---|------|-------|------------------|--------|
| 1 | `panels_workspace.rs` `ui_event_guard_turns_a_panicking_action_into_a_logged_no_op` | std property dressed as a project property + name stronger than body | **YES** | **REWRITTEN in this commit** |
| 2 | `read_cap_lens.rs:355` `binding_invariant_demonstrates_byte_identity_live` | asserts a substring that its own subject emits **unconditionally** | **YES** | open |
| 3 | `organs.rs:546` `remote_path_organs_are_honest_not_faked` | name claims "not faked"; body accepts fabrications | **YES** | open |
| 4 | `read_cap_lens.rs:367` `no_committed_slots_degrades_honestly` | whole body inside an `if` with no `else` — vacuous the day the fixture changes | measured (red today) | open, latent |
| 5 | `conflict.rs:432` `commitment_is_deterministic` | determinism-only; sole coverage of `ConflictSet::commitment()`; a constant stub passes | suspicion (grep-confirmed no sibling) | open |
| 6 | `viewnode_pane.rs:867` `the_web_renderer_renders_the_same_panel` | name claims cross-renderer agreement; body never compares the two | suspicion | open |
| 7 | `systemui_caps.rs:486` `all_text_renders_the_full_chrome` and the prose-substring family | asserts literals the same module writes | suspicion (class) | open |
| 8 | `authorize.rs` `cap1_unchecked_*_refused` family | `is_err()` without naming the variant — a refusal for the **wrong reason** passes | suspicion (class) | open |
| — | `views/mod.rs:274` | stray duplicate `#[test]` + orphaned doc comment left by the palette fix | n/a | cosmetic |

Shapes hunted and **not** found in bulk, which is worth saying:

* **Source-file self-reference:** exactly one test in either tree reads source as
  text (`views/mod.rs:191`, the palette gate) and it is correct — it scans *other*
  files against a canonical one.
* **Literal tautologies:** zero `assert!(true)` / `assert_eq!(x, x)` in 1,697 tests.
* **Conditional vacuity:** the detector fired twice; both were false positives
  (`two_validators_never_share_a_derived_pq_key` in
  `finalized_receipt_core_v1.rs:1239` and its `exact_fnsp_v4` twin are strong
  tests with a real cross-identity falsifier). The only real instance is §4.
* **Determinism-without-distinctness:** 32 determinism/round-trip-only tests were
  listed and their modules checked for a distinctness sibling. All but §5 have
  one (`binding_proof.rs` has three `assert_ne!`s; `receipt_hash` is separated at
  `verify.rs:1118`).

---

## 1. `ui_event_guard_turns_a_panicking_action_into_a_logged_no_op` — FIXED

`starbridge-v2/src/cockpit/panels_workspace.rs:3368` (pre-fix line). Titled
**"THE SAFETY NET, PROVEN"**, doc claiming *"a real gpui Obj-C event callback (a
nounwind boundary) would never see the panic and never abort."*

The body called `Cockpit::guard_ui_event` **directly** with a `panic!()` closure
and asserted it returned `false`. That is `std::panic::catch_unwind` catching a
same-frame panic — a standard-library property. The `boot_cockpit()` above it was
never touched by the panic.

### Mutation

The guard was amputated from the seam whose crash the doc names — the pane's
"↗ pop out" mouse-down handler, `panels_workspace.rs:554`:

```rust
-  Cockpit::guard_ui_event("pane-popout", || {
+  (|| {
       …
-  });
+  })();
```

### Result — still green

```
running 2 tests
test cockpit::panels_workspace::popout_crash_repro::ui_event_guard_turns_a_panicking_action_into_a_logged_no_op ... ok
test cockpit::panels_workspace::popout_crash_repro::pop_out_active_tab_then_double_draw_does_not_panic ... ok
test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 990 filtered out; finished in 5.80s
```

**The safety net was entirely off the crash path and the test that says PROVEN did
not notice.**

### The fix (this commit)

Replaced by two tests, both mutation-proved to die:

* `a_panic_mid_action_is_contained_and_the_cockpit_still_draws_and_acts` — the
  panic is raised **mid-mutation inside a live `Cockpit` lease**; the test then
  drives a real repaint (`run_until_parked` → `window.refresh()` →
  `run_until_parked`), re-reads the root entity, and executes a real `tear_off_tab`
  afterwards. It also pins something the guard's own doc gets **wrong**:
  containment is not a rollback — the half-written mutation survives, so "logged
  no-op" means *the remainder does not run*, not *the cockpit is unchanged*.
* `the_pop_out_click_handler_is_wrapped_in_the_guard` (new module
  `ui_event_guard_seam`) — the missing half. It reads the render body of the
  `.id("pane-popout")` control and requires the `Cockpit::guard_ui_event("pane-popout"` 
  wrapper. This is the gate the amputation above turns red.

Mutation proof of the replacements, both mutations applied at once:

```
running 3 tests
test …::pop_out_active_tab_then_double_draw_does_not_panic ... ok
---- …::a_panic_mid_action_is_contained_and_the_cockpit_still_draws_and_acts stdout ----
panicked at starbridge-v2/src/cockpit/panels_workspace.rs:3400:17:
deliberate UI panic inside a click handler
failures:
    cockpit::panels_workspace::popout_crash_repro::a_panic_mid_action_is_contained_and_the_cockpit_still_draws_and_acts
    cockpit::panels_workspace::ui_event_guard_seam::the_pop_out_click_handler_is_wrapped_in_the_guard
test result: FAILED. 1 passed; 2 failed
```

### Residuals left standing, named in the code

* **The gpui boundary is still unmeasured.** There is no Obj-C in a headless test;
  ember's `process::abort` is not reproducible here at all. The guard's value at
  that boundary is an argument, not a measurement. Closing it needs a gpui fork
  patch, which is out of this crate — the same conclusion a Wave-1 lane reached.
* **`tear_off_tab_deferred` hands the window open to `cx.defer`**, whose body runs
  on a *later* app pass — **outside this guard and outside any other**. A panic in
  the deferred tear-off is contained by nothing. This is the pop-out path.
* **`panic = "abort"` disarms the whole net silently.** Under that strategy
  `catch_unwind` contains nothing. The workspace does not set it today and nothing
  pins that it never will. A gate scanning `[profile.*]` for `panic` would close
  this; it was not added here because it touches a file this lane does not own.

---

## 2. `binding_invariant_demonstrates_byte_identity_live` — DECORATION, PROVED

`starbridge-v2/src/read_cap_lens.rs:355`.

```rust
let prose = binding_invariant_prose(&view, &view.committed_slots());
assert!(prose.contains("BYTE-IDENTICAL"), "the live demonstration confirms binding is preserved");
assert!(prose.contains("HONEST SEAMS"), "the seams are named");
```

The name says the invariant is demonstrated **live**. `binding_invariant_prose`
does contain a live demonstration — it clones the cell state, seals a slot under
a demo `ViewKey`, and compares the side-table commitment to the stored one
(`read_cap_lens.rs:219-241`). But the string `BYTE-IDENTICAL` **also appears in the
unconditional preamble at `read_cap_lens.rs:211`**, which is pushed before any
demonstration runs. So the assertion is satisfied by a `push_str` that executes
whatever the seal does — including when `byte_identical` is `false`, and including
when the cell has no committed slots at all.

### Mutation

The whole live-demonstration block (`if let Some(&slot) = committed.first() { … }
else { … }`, lines 217-248) was made unreachable.

### Result — still green

`read_cap_lens::tests::binding_invariant_demonstrates_byte_identity_live` passed
with the demonstration gone. (Its sibling §4 went red — see below.)

### To make it refutable

Do not assert on the prose. Expose the comparison the prose narrates — have
`binding_invariant_prose` compute a `bool`/small struct the panel formats, and
assert **that**. Failing that, assert on the branch-specific text (`"LIVE on this
cell — sealed slot"` plus the short-hex), never on a token the preamble also
carries.

---

## 3. `remote_path_organs_are_honest_not_faked` — DECORATION, PROVED

`starbridge-v2/src/organs.rs:546`.

```rust
for o in &remote {
    assert!(!o.kind.is_empty());
    assert!(!o.seam.is_empty());
    assert!(o.route.contains("node") || o.route.contains("captp"));
}
```

The name asserts a property about *honesty* — that these organ descriptions are
not fabricated. The body accepts any non-empty string.

### Mutation

```rust
return vec![
    RemoteOrgan { kind: "x", seam: "y", route: "node" },
    RemoteOrgan { kind: "x", seam: "y", route: "node" },
    RemoteOrgan { kind: "x", seam: "y", route: "node" },
];
```

### Result — still green

`organs::tests::remote_path_organs_are_honest_not_faked` passed against three
fabricated placeholders — the literal thing its name forbids.

**Do not delete it.** Its neighbour
`organs::tests::organ_survey_finds_embed_core_organs_in_the_live_world` **did** go
red under the same mutation (`assertion failed: survey.remote.iter().any(|o| o.kind
== "channel")`), so the path is covered. The problem is the *name*: rename it to
what it checks (`remote_path_organs_are_non_empty_and_route_somewhere`) or give it
the content check its title promises.

---

## 4. `no_committed_slots_degrades_honestly` — LATENT vacuity, measured

`starbridge-v2/src/read_cap_lens.rs:367`. Every assertion sits inside

```rust
if view.committed_slots().is_empty() {
    let prose = binding_invariant_prose(&view, &[]);
    assert!(prose.contains("no committed slots"));
}
```

with no `else`. It is **not** vacuous today: under the §2 mutation it went red
(`assertion failed: prose.contains("no committed slots")`), so the guard is taken
against the current `plain_world()` fixture. It becomes a silent no-op the moment
that fixture gains a committed slot — and nothing anywhere would report that.

**Fix:** assert the precondition instead of branching on it —
`assert!(view.committed_slots().is_empty(), "fixture drifted: …")` then the body
unconditionally.

This is the only true instance of the shape in 1,697 tests, and it is the shape to
keep grepping for: *an assertion whose reachability depends on a fixture*.

---

## 5. `commitment_is_deterministic` — stub-satisfiable sole coverage

`turn/src/conflict.rs:432`. Two `ConflictSet`s built from the same cell id are
asserted to have equal `commitment()`. `ConflictSet::commitment()` (`conflict.rs:107`)
has **no distinctness test anywhere in `turn/src`** — `grep -rn "assert_ne!" turn/src/conflict.rs`
returns nothing. A `commitment()` replaced by `[0u8; 32]` passes every test of it
that exists.

**Not mutation-proved** (the grep is the evidence, and it is exact). Add
`distinct_sets_have_distinct_commitments`.

Its neighbour at `conflict.rs:401`,
`false_positive_rate_matches_the_any_bit_overlap_design`, is the opposite of
decoration and worth reading as the model: it *measures* the false-conflict rate
over 2,016 pairs and pins it to a two-sided band, so both a saturated filter and a
dead one go red. That test cannot be satisfied by a stub in either direction.

---

## 6. `the_web_renderer_renders_the_same_panel` — SUSPICION

`starbridge-v2/src/deos_desktop/viewnode_pane.rs:867`. The name claims the web
renderer produces *the same panel* as its sibling. The body:

```rust
let html = status_panel_html();
assert!(html.contains("World Status"));
assert!(html.contains("receipts: 12"), "the seeded status rows paint their witnessed values");
```

Nothing in it references the other renderer, so "the same" is unmeasured; and a
`status_panel_html()` returning a hardcoded string would pass. Either compare the
two renderers' extracted rows, or rename to
`the_web_renderer_paints_the_seeded_status_rows`.

---

## 7. The prose-substring class — SUSPICION, ~30 members

Tests that assert a rendered string `.contains("SOME PHRASE")` where the phrase is
a literal in the same module's production code. Members include
`systemui_caps.rs:486` `all_text_renders_the_full_chrome`, `doc_lens.rs:443`,
`cell_inspector.rs:989`, `links_here.rs:557`, `settlement_inspector.rs:930/997`,
`cap_inspector.rs:803`, `edit.rs:991`.

This class is **not automatically decoration** — a text renderer has to be tested
somehow, and most of these render *derived* values (counts, hashes, names) so the
substring rides on real content. The discriminator is §2's: **is the asserted token
on a code path conditional on the property claimed, or in an unconditional
preamble?** §2 is the member of this class that failed that test. Each remaining
member wants one look with that question, ideally when its file is next touched
for another reason.

Cheap general upgrade: assert on the *derived* fragment (a hash prefix, a count,
a cell id) rather than the fixed banner.

---

## 8. `is_err()` without naming the variant — SUSPICION, class

`turn/src/executor/authorize.rs:3219` `assert_unchecked_refused` and the five
`cap1_unchecked_*_refused` tests that call it; also
`turn/src/executor/proof_verify.rs:4507` `every_state_prefix_lane_is_load_bearing`.

```rust
assert!(res.is_err(), "CAP-1: {name} … MUST be refused, got {res:?}");
```

A refusal for *any* reason passes — including a reason unrelated to the CAP-1
authority hole these tests were written for (a malformed fixture, a missing cell,
an unrelated precondition). These are real tests of a real refusal and should stay;
they are one `matches!` away from being exact. The neighbouring tests in the same
file already do it right (`proof_verify.rs:4522` and `:4542` both match the
specific `TurnError::CustomProofStateBindingMismatch` leg), so the pattern is
already in the file.

Counted: **11 tests** in the two trees whose *only* assertions are `is_ok()`/`is_some()`
(`world_chat.rs:486`, `verify.rs:674/689/696`, `tests.rs:10568/11188/11451`,
`finalize.rs:1344`, `authorize.rs:3289/3322`, `owner_envelope.rs:280`). Most are
positive-path companions to a real negative test on the adjacent line, which is
fine; they are listed here so the class is enumerable rather than re-derived.

---

## Method, so this is repeatable

Extraction and shape-matching scripts (throwaway, ~120 lines of Python) walked
every `#[test]` in both trees with its doc comment and body, then filtered by:

1. source-file self-reference (`read_to_string` / `include_str!` in a test body)
2. literal tautologies and `assert_eq!` where both sides share a function or const
3. every assertion nested under an `if` with no `else` and none at top level
4. every assertion of the form `is_ok()`/`is_some()`/`!is_empty()`/`.contains()`
5. determinism/round-trip-only tests, cross-checked for a distinctness sibling
6. names containing a strong claim (`refuse`, `cannot`, `never`, `forge`, `sound`,
   `proven`, `every`, `all`) against body size and assertion count
7. `.contains("LIT")` where `LIT` is also a literal in the module's production code

Then: **for every top candidate, amputate the subject and re-run.** Five mutations
were applied and reverted against the live tree; four are quoted verbatim above.

The single highest-yield filter was (6) — a strong verb in the name against a body
of one or two assertions. Every confirmed finding here was caught by it first.
