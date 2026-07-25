# DEOS Applet/Agent Capability-Authorization Audit — 2026-07-24

Deep read-only audit of the DEOS applet/agent authority boundary (survey's #1 next-target). It came back
non-empty: one HIGH (CRITICAL on open-cockpit) agent-escalation, plus a real Lean↔Rust enforcement gap.

## 🔴 F1 (HIGH / CRITICAL on open-cockpit) — model `run_js` reaches the GM `deos.server.*` surface
The `deos.server.*` GM natives — `spawnCell`/`fork` (mint OPEN 100k-computron cells), `setField` (write any
OPEN cell), `grant` (hand out caps) — are `JS_DefineFunction`'d into the SAME JS global that model-authored
`run_js` evaluates in. They take NO `held` argument and run NO `is_attenuation` check
(`deos-js/src/attach.rs:357,373,400-402` — "GM's own-world privilege, NO held bound"), and the PRELUDE
exposes them as `deos.server.*` (`js.rs:633,769-794,1787-2057`). Reached via
`deos-hermes/src/run_js.rs:288 → js.rs:821 run_attached → :706 eval`, model-wired at
`deos-hermes/src/mcp_server.rs:342 call_run_js_bridged`. EXPLOIT: the model emits inside its run_js script
`deos.server.spawnCell(s,"open")` / `deos.server.setField(openCell,i,v)` / `deos.server.grant(x,cell,"none")`
— minting unlimited funded cells, writing/granting any OPEN cell on the cockpit ledger, as ONE metered
run_js turn, entirely outside its rate/scope mandate. `world_bridge_e2e.rs:49-56` configures a fully-OPEN
cockpit = total compromise. COVERAGE GAP that hides it: `red_team_authority_amplification.rs` attacks the
SDK ToolGateway (different surface); `red_team_sandbox_escape.rs` attacks OS confinement; NEITHER tests that
run_js cannot reach `deos.server.*`. FIX (Rust host-wiring, NO circuit): give JsRuntime a trusted-vs-confined
install mode — do NOT install `__deos_server_*` in the eval global used by run_js/run_attached (the model's
hands); the GM surface only in the operator's authoring runtime. Add a red-team test asserting
`deos.server.grant/spawnCell/setField` are unreachable (throw/undefined) from a run_js script.
- SAFE by contrast (do not touch): the `run_js` EMBEDDED path (`run_on`, JsTarget::Embedded) returns errors
  for the GM natives (js.rs:80-112, inert); `deos-js-runtime` (boa) exposes ONLY cap-gated t/tCell/batch/
  transfer, no server surface — the clean confined engine.

## 🟡 F2 (MED) — ToolGateway executor backstop under-enforces the Lean spec (deadline absent)
Lean `mandateSpec`/`tool_invocation_commit_iff_admit` (`ToolAccessDelegation.lean:149-159,186`) proves the
executor commits IFF full `delegAdmit` = scope∧deadline∧rate. The deployed Rust `mandate_program`
(`sdk/tool_gateway.rs:238-251`) carries ONLY `FieldLte{rate}` + `Monotonic` — scope is re-homed to the biscuit
method-cover (defensible), but DEADLINE has NO executor realization (only in-band `deleg_admit` vs a
caller-supplied `now`). The doc claim "even if a caller bypassed deleg_admit the executor rejects" is TRUE for
rate, FALSE for deadline. Not model-exploitable today (hermes supplies `now` host-side), but the "executor is
the independent backstop" guarantee the crown proves is only 2/3 present. FIX: bake a height-bounded deadline
constraint into `mandate_program` (improve, don't degrade) — or honestly downgrade the doc claim.

## 🟢 F3 (LOW) [TWIN — add to CI guard] — the ToolGateway differential is hand-pinned, not FFI
`tool_gateway.rs:1310 tool_gateway_admit_mirrors_lean_delegadmit` (+ the starbridge-apps/tool-access-delegation
mirror) HAND-PINS the Lean §8 `#guard` literals as Rust asserts — no FFI/generated corpus (unlike macaroon's
caveat_chain_diff). A future Lean `delegAdmit` edit stays green until a human re-pins. VERDICT on the twin
(smell #2): PREDICATE NOT DRIFTED — `deleg_admit` (tool_gateway.rs:220) is conjunct-for-conjunct faithful to
Lean `delegAdmit` (:126). Add BOTH mirrors to the CI twin-guard registry.

## 🟢 F5 (LOW) — native_server_grant accepts "none"/"open" → universal cap
`deos-js/src/js.rs:1427 parse_auth_label` / `:1954 native_server_grant` rejects UNKNOWN labels but a deliberate
`"none"` → AuthRequired::None (universal). Amplifies F1. FIX: reject "none"/"open" (require an explicit
non-universal authority), independent of F1.

## Cleared / classify (do not re-flag)
F4 predicate not drifted (INFO); F6 `held=None` mount makes is_attenuation vacuous BUT effects are self-scoped
to the applet's own cell (not an escalation; real over-reach is F1); F7 deos-zed raw std::fs = trusted-by-design
local editor (WATCH if it ever hosts untrusted content); F8 hermes bridge.rs admit_with_work is SOUND
(name→MandateKey→tool_id, scope structural, confused-deputy enforced at the executor).

## Dispatch: F1 (fix-first, Rust host-wiring + red-team test) → F5 (reject universal label) → F3 (CI twin-guard,
both mirrors) → F2 (deadline into mandate_program). DEOS was the right #1 target; TEE-verify crypto + federation
quorum internals are the ranked next audits.
