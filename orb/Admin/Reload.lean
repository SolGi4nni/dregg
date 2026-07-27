/-
Admin.Reload — the proven safety decision behind `POST /admin/reload`.

An operator pushes a new textual deployment config to the running host. The
untrusted admin shell (`crates/dataplane/src/admin.rs` → `reconfig::reload_now`
→ `config::reload`) crosses the PROVEN parser (`Dsl.Config.parseOn`, the same
`drorb_deployment_of_config` gate SIGHUP takes) and then either

  * APPLIES the parsed deployment (a new running generation), or
  * REJECTS the push and keeps the running config untouched (fail-safe).

The safety-critical clause is the reject half: a malformed or otherwise
unparseable config must NEVER become the running config — a bad admin push can
not brick the serve. The parser is the gate: the decision here consults only
`parseOn`'s verdict, so its `none` (an invalid config) is fail-safe by
construction.

This file states that decision as a pure function `reload` over an abstract
`RunState` (the running deployment + its generation) and discharges the two
obligations:

  * `reload_rejects_invalid` — `parseOn` says `none` ⇒ the running state is
    byte-for-byte unchanged (config AND generation);
  * `reload_applies_valid` — `parseOn` says `some c` ⇒ the running config
    becomes exactly `c` and the generation is bumped once.

Non-vacuity is witnessed three ways: both branches are shown REACHABLE (a
concrete invalid string parses to `none`; a well-formed config renders to a
string that parses to `some` via the proven `parseOn_render`), and a reckless
mutant that bumps the generation on a rejected push is proved to VIOLATE the
fail-safe contract — so the gate is load-bearing, not decorative.
-/

import Dsl.Config.Parse

namespace Admin
namespace Reload

open Dsl (DeploymentConfig)
open Dsl.Config (parseChars parseOn ParsedConfig WF render denoteOn parseOn_render)
open Dsl.Cfg (LbPolicy)

/-! ## The running-config state and the reload decision -/

/-- The state the admin reload mutates: the deployment the running host serves
under, and a generation counter bumped on every successful apply (surfaced by
`/admin/config` as `generation`). The transition/config type is the real
`Dsl.DeploymentConfig` the deployed serve is generated from. -/
structure RunState where
  /-- The deployment every subsequent request is served under. -/
  cfg : DeploymentConfig
  /-- The config generation (0 = boot default; bumped once per applied reload). -/
  gen : Nat

/-- **The reload decision.** Parse `raw` through the PROVEN parser gate
(`parseOn`, over the running config as the base); apply the parsed deployment
with the generation bumped only if it parses, else keep the running state
untouched (fail-safe). The `none` arm is the safety-critical one: an
unparseable config is never installed. -/
def reload (st : RunState) (raw : String) : RunState :=
  match parseOn st.cfg raw with
  | some c => { cfg := c, gen := st.gen + 1 }
  | none => st

/-! ## The two obligations -/

/-- **Fail-safe (the safety-critical theorem).** When the proven parser rejects
the pushed config (`parseOn … = none`), the reload is a no-op: the running state
— both the deployment AND its generation — is exactly unchanged. A bad admin
push cannot brick the serve. -/
theorem reload_rejects_invalid (st : RunState) (raw : String)
    (h : parseOn st.cfg raw = none) : reload st raw = st := by
  unfold reload; rw [h]

/-- Corollary spelled out at the config projection: a rejected push leaves the
running deployment identical. -/
theorem reload_rejects_keeps_cfg (st : RunState) (raw : String)
    (h : parseOn st.cfg raw = none) : (reload st raw).cfg = st.cfg := by
  rw [reload_rejects_invalid st raw h]

/-- **Apply.** When the proven parser accepts the pushed config
(`parseOn … = some c`), the running deployment becomes exactly `c` and the
generation is bumped once. -/
theorem reload_applies_valid (st : RunState) (raw : String) (c : DeploymentConfig)
    (h : parseOn st.cfg raw = some c) :
    (reload st raw).cfg = c ∧ (reload st raw).gen = st.gen + 1 := by
  unfold reload; rw [h]; exact ⟨rfl, rfl⟩

/-! ## Non-vacuity — both branches are reachable -/

/-- A concrete unparseable config: a single non-keyword line is not a four-line
deployment, so the proven parser returns `none`. -/
theorem parseChars_bad : parseChars ['x'] = none := by rfl

/-- The reject branch is REACHABLE: there is a string the proven parser rejects,
so `reload_rejects_invalid`'s hypothesis is satisfiable (not vacuously false).
Independent of the running config, since `parseOn` maps the parser's verdict. -/
theorem reject_reachable (st : RunState) : ∃ raw, parseOn st.cfg raw = none := by
  refine ⟨"x", ?_⟩
  show (parseChars "x".data).map (denoteOn st.cfg) = none
  rw [show "x".data = ['x'] from rfl, parseChars_bad]; rfl

/-- A concrete well-formed parsed config (a plain HTTP listener over a
round-robin pool, no routes/vhosts). -/
def okConfig : ParsedConfig :=
  { addr := ['1','0'], port := 8080, poolName := ['p'], lb := LbPolicy.roundRobin,
    l4 := none, zeroRtt := false, routes := [], vitems := [] }

/-- `okConfig` is well-formed: its tokens carry no separator and it declares no
routes or vhosts. -/
theorem okConfig_wf : WF okConfig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · intro r hr; exact absurd hr (List.not_mem_nil)
  · intro it hit; exact absurd hit (List.not_mem_nil)
  · trivial

/-- The apply branch is REACHABLE: a well-formed config renders to a string the
proven parser accepts (`parseOn_render`), so `reload_applies_valid`'s hypothesis
is satisfiable. This anchors the apply half to the real parse-soundness theorem. -/
theorem apply_reachable (st : RunState) :
    ∃ raw c, parseOn st.cfg raw = some c := by
  exact ⟨render okConfig, denoteOn st.cfg okConfig, parseOn_render st.cfg okConfig okConfig_wf⟩

/-- A worked end-to-end instance: pushing the rendered `okConfig` installs its
denotation as the running config and bumps the generation exactly once. -/
theorem reload_okConfig (st : RunState) :
    (reload st (render okConfig)).cfg = denoteOn st.cfg okConfig
    ∧ (reload st (render okConfig)).gen = st.gen + 1 :=
  reload_applies_valid st (render okConfig) (denoteOn st.cfg okConfig)
    (parseOn_render st.cfg okConfig okConfig_wf)

/-! ## Non-vacuity — the fail-safe contract, and a mutant that violates it -/

/-- **The fail-safe contract** over an arbitrary reload discipline: a rejected
push (parser says `none`) does not advance the running generation. A reload that
satisfies it never counts an invalid config as an applied one. -/
def RejectKeepsGen (r : RunState → String → RunState) : Prop :=
  ∀ st raw, parseOn st.cfg raw = none → (r st raw).gen = st.gen

/-- The real reload satisfies the fail-safe contract. -/
theorem reload_rejectKeepsGen : RejectKeepsGen reload := by
  intro st raw h; rw [reload_rejects_invalid st raw h]

/-- A reckless mutant: it still parses through the gate, but on a REJECTED push
it bumps the generation anyway (as if a bad config were a real reload). Every
accepted push behaves like the real reload. -/
def recklessReload (st : RunState) (raw : String) : RunState :=
  match parseOn st.cfg raw with
  | some c => { cfg := c, gen := st.gen + 1 }
  | none => { st with gen := st.gen + 1 }

/-- **Non-vacuity via a mutant.** For any base config, the reckless reload
VIOLATES the fail-safe contract: on the unparseable `"x"` it advances the
generation, so the gate's `none` verdict genuinely gates the applied-generation
count — the fail-safe theorem is not vacuously true. -/
theorem recklessReload_violates (base : DeploymentConfig) :
    ¬ RejectKeepsGen recklessReload := by
  intro h
  have hbad : parseOn base "x" = none := by
    show (parseChars "x".data).map (denoteOn base) = none
    rw [show "x".data = ['x'] from rfl, parseChars_bad]; rfl
  have key := h { cfg := base, gen := 0 } "x" hbad
  simp only [recklessReload] at key
  rw [hbad] at key
  simp at key

end Reload
end Admin
