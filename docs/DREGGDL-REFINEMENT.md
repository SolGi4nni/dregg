# DreggDL refinement — a deploy-time behavioral check, decided by FlowRefine

A DreggDL deployment ([`dregg-deploy/`](../dregg-deploy), `docs/CAPDL-POLYGLOT-DX.md`)
lowers a declarative capability layout into an ordered, receipt-chained **turn
sequence** (`apply.rs::build_turn_sequence`): births, then funds, then grants
(the delegation forest nested), in dependency order. That sequence is a **flow**
— a state-threaded sequence of observable affordance-fires — in exactly the
sense of `metatheory/Dregg2/Deos/FlowAlgebra.lean`. And
`metatheory/Dregg2/Deos/FlowRefine.lean` makes flow **refinement** `A ≤ᶠ B` a
decidable simulation game (`decideRefines`, sound + complete). So a DreggDL plan
gains a deploy-time **refinement** check on top of its existing static
no-amplification **safety** check.

This document records what that check is, the two questions it answers, and the
honest boundaries: the static-safety vs behavioral-refinement distinction, and
how the gate runs the **verified** procedure (the Lean `@[export]`, with a σ-free
in-process fallback for non-linking targets).

## 1. The deployment IS a flow

A lowered DreggDL plan is a `dregg_turn::CallForest`-per-turn, the turns ordered
births → funds → grants. Read each effect the deployment performs as one
**visible letter** of a flow (the affordance fired, with its capability shape),
and the phase/dependency order as sequential composition `⋆`. The whole
deployment is then one flow `Proc` — a `⋆`-chain of effect-`Emit`s.

The mapping lives in [`dregg-deploy/src/refine.rs`](../dregg-deploy/src/refine.rs):

| DreggDL artifact | flow object |
|---|---|
| one `Effect` (a `Transfer` / `GrantCapability` / `CreateCellFromFactory` / …) | one letter `Emit ℓ`, where `ℓ` encodes the effect's **kind + capability/value shape** (`effect_letter`) |
| the per-turn DFS order + the births→funds→grants turn order | sequential composition `⋆` (`flow_of_plan` / `flow_of_forest`) |
| a nested re-delegation (a child grant tree) | its effects, in DFS order, in the same `⋆`-chain |

The letter is a deterministic digest of the effect's serialized shape, tagged by
kind. The consequence that makes refinement meaningful: **two effects with the
same observable shape get the same letter, a widened one gets a different
letter.** Re-granting the *identical* facet is a matchable move (an attenuation
or equal refines); granting a *wider* facet, a *new* recipient, or a *re-target*
changes the bytes and so the letter — a move the narrower side cannot match.

Because a lowered deploy never branches (it is a fixed effect sequence), its flow
is **linear**: a single path of letters. The refinement game and its witness walk
both exploit this (§4).

## 2. The order is online simulation (why this is not trace-containment)

`FlowAlgebra` proved dregg's flow algebra is **right-skewed**: the order `≤ᶠ` is
online step-by-step **simulation** (the simulator commits each move with no
lookahead), strictly finer than offline trace language — on the very
counterexample that separates the two sides in simulation, the trace languages
are *equal* (`flow_choice_languages_equal`). `FlowRefine` then made `A ≤ᶠ B`
decidable: a finite, **σ-free** simulation game (`decideRefines`, the dregg
analogue of Pradic's Theorem 1.4), sound + complete against `≤ᶠ`
(`decideRefines_iff`, LAW #1). "σ-free" is the linchpin (`FlowRefine` §3): the
threaded state never decides a move, only the syntax does — so the decision is a
finite, state-free recursion.

Refinement `A ≤ᶠ B` reads: *every move-sequence `A` can perform, `B` can match,
step for step* — i.e. `A` does no more than `B` permits. For deployments that is
exactly the safety-relevant question of "is this layout within that envelope?".

## 3. The two checks FlowRefine enables

### (a) safe-upgrade — `new ≤ᶠ old`

> *Does the new deploy spec refine the running one?*

`refines_upgrade(new_plan, old_plan)` decides `new ≤ᶠ old`. If it holds, the new
deployment only **narrows** behavior: every effect-sequence the new plan can
perform, the running plan already could — **no new reachable effect or
capability is introduced**. This is the gate for "is this redeploy safe to roll
forward?": a safe upgrade cannot do anything the running deployment did not
already authorize.

An upgrade that **widens** — adds an effect, a wider cap, a new grant edge, a new
recipient — is rejected, and the finding names the diverging effect-letter (the
exact game position where `new ⋠ old`).

### (b) intent-conformance — `lowered ≤ᶠ intent`

> *Does the lowered sequence refine the declared abstract intent?*

The operator declares an **intent**: the menu of effect-shapes they meant to
authorize (a `FlowSpec` — from explicit `IntentEffect`s, or from a reference
plan's envelope). `refines_intent(plan, intent)` decides `lowered ≤ᶠ intent`. A
lowering that does **more** than the intent declared — a stray grant, a wider cap
— fails, with the out-of-envelope effect named. The lowering is held to its
stated envelope.

The intent is the **repeat-menu** `μ = ⊔_{ℓ ∈ allowed} (ℓ ⋆ μ)`: at every step it
offers a choice among the allowed letters and returns to the same menu, so any
finite sequence over the alphabet is simulable. For a *linear* lowered flow this
collapses to a membership check (see §5).

## 4. The honest boundary: static safety vs behavioral refinement

The refinement gate **adds to**, and does **not replace**, the existing static
check. They are different properties; neither subsumes the other.

| | `dregg-userspace-verify::check_no_amplification` (the existing gate) | `refines_upgrade` / `refines_intent` (this module) |
|---|---|---|
| **kind** | static graph property of **one** forest | behavioral relation between **two** flows |
| **asks** | along each delegation edge, is the child cap `⊆` the parent cap? (no re-delegation amplifies) | does plan `A` do only what plan/intent `B` permits, move-for-move, in `≤ᶠ`? |
| **catches** | an *amplifying re-delegation within* the spec | a *widening relative to* a prior deployment or an intent |
| **misses** | how the spec relates to a previous deploy / an intent | an in-forest amplification (not its job) |

A spec can **pass** no-amplification (its own grant graph attenuates) yet **fail**
safe-upgrade (it widens relative to what is running). The test
`the_two_checks_are_independent_widening_passes_safety_but_fails_refinement`
pins exactly this: a deployment that adds a fresh, flat (non-amplifying) grant
**passes** the static safety check but **fails** the behavioral refinement check
against the running plan — because the new grant is a reachable effect the
running deployment never had.

The `apply` gate (`plan_apply`) runs the static check unconditionally and refuses
a failing spec before emitting any turn. The refinement gate is **optional and
additive**: it runs when a target — a running plan or an intent — is supplied. It
does not gate `plan_apply`; it is a separate `assurance.refines`-style verdict an
operator (or a redeploy pipeline) consults. Like the static audit, it is an audit
artifact, **not** a trust boundary: it certifies a relation between *artifacts*,
and says nothing the executor does not separately enforce about live state.

## 5. Implementation: the verified procedure, and the linear-flow decision

`refine.rs::decide_refines` routes its `A ≤ᶠ B` decision through the **verified
Lean procedure** when the linked archive exports it
(`dregg_lean_ffi::decide_refines_gate_available()`): the two flows are serialized
to the export's preorder-token wire and the verdict is read off
`@[export] dregg_decide_refines` — the PROVEN `FlowRefine.decideRefines`. So on a
native build the deploy gate runs the decision procedure whose soundness +
completeness against `≤ᶠ` is `decideRefines_iff` (LAW #1), not a re-implementation.

The σ-free fragment the deploy side ever builds:

- `Proc` — the σ-free process (`Done` / `Emit ℓ` / `Ch` / `Seqp`), the
  `Proc`-only projection `FlowRefine.PStep` / `moves` operate on.
- `encode_proc` — the byte-exact inverse of `FlowRefine.encodeProcToks` /
  `decodeProc` (a preorder token stream: `d` done · `e<ℓ>` emit · `c` ch ·
  `s` seqp). A `Proc` built here decodes to the SAME `Proc` in Lean (the codec
  round-trip `#guard`s pin it).

**The in-process fallback.** `decide_refines_mirror` (`moves` / `decide_fuel` /
`decide_refines_mirror`, exact mirrors of `FlowRefine.moves` / `decideFuel` /
`decideRefines` at the canonical fuel `proc_size A + 1`) decides the same game in
Rust, for targets that cannot link the Lean archive (`wasm32`, the zkvm guest) or
a stale archive predating the export. It AGREES with the verified procedure by
construction: the game is **σ-free** (`FlowRefine` §3 — the state never decides a
move), so the Lean kernel-reduction and this Rust recursion compute the same
`Bool`. The differential test `ffi_decide_refines_agrees_with_lean_both_polarities`
asserts FFI-verdict == mirror-verdict on `FlowAlgebra`'s headline counterexample
(`early = (P⋆R)⊔(Q⋆R)`, `late = (P⊔Q)⋆R`) — the half holds, the right-skew fails,
**both polarities** — the exact verdicts the Lean `#guard`s pin.

**The linear-flow shortcut for intent-conformance.** The repeat-menu `μ`,
materialized to depth `n`, is exponential in the alphabet size — running the game
on it would pay that cost. But for a *linear* lowered flow `A`, refinement
against the menu collapses:

> `A ≤ᶠ μ`  ⟺  every letter in `A`'s trace is in `allowed`.

(`→` each `A`-move is a letter `ℓ` that `μ` matches iff `ℓ ∈ allowed`, landing
back at `μ`; `←` "the remaining `A`-suffix vs `μ`" is a simulation when every
`A`-letter is allowed. The repeat-menu has no `⋆`-skew to exploit — its right
factor is `μ` at every node.) So `refines_intent` decides conformance by a
membership check over `A`'s trace (`allows_trace`, O(|A|·|alphabet|)) instead of
the exponential menu. The equivalence is pinned non-vacuously, **both
polarities**, by `intent_trace_decision_agrees_with_the_decide_refines_game`:
the fast trace-check and the actual `decide_refines` game run on the
*materialized* `μ` agree, on an allowing intent (refines) and a missing-letter
intent (does not).

## 6. The Lean-FFI boundary — the gate runs the proven procedure

The gate calls the verified procedure across the same Lean-FFI seam the rest of
the dregg2/Rust bridge uses (`FinalityGate.dregg_blocklace_finalize`,
`dregg_record_kernel_step`, …):

- **Lean:** `FlowRefine.decideRefinesGate` is the `String → String` body, exposed
  as `@[export dregg_decide_refines]`. It decodes the `"A=<procW>;B=<procW>"`
  wire, runs `decideRefines`, and returns `"1"` (A ≤ᶠ B) / `"0"` (A ⋠ B) /
  `"ERR"` (fail-closed). The export **carries the proof**:
  `gate_one_iff_sim` (`"1"` ⟺ `A ≤ᶠ B`) and `gate_zero_iff_not_sim`
  (`"0"` ⟺ `¬ A ≤ᶠ B`) — so gating the deploy on a `"1"` is gating it on the
  verified refinement relation, by construction (not "agreement-checked").
- **Bridge:** `dregg-lean-ffi` adds the `dregg_decide_refines_str` C shim and
  `shadow_decide_refines` / `decide_refines_gate_available`; `build.rs` splices
  `Dregg2.Deos.FlowRefine` into the archive and probes the symbol.
- **Caller:** `refine.rs::decide_refines` routes through `shadow_decide_refines`
  when the gate is available, falling back to the σ-free mirror otherwise.

The one fact Rust trusts but does not re-prove is `decideRefines_iff` (soundness +
completeness against `≤ᶠ`) — which lives in Lean and now decides the live gate.

## Where it lives

- [`dregg-deploy/src/refine.rs`](../dregg-deploy/src/refine.rs) — the module:
  the `Proc` + `encode_proc` wire + FFI-routed `decide_refines` (with the σ-free
  `decide_refines_mirror` fallback), the deploy→flow mapping (`flow_of_plan` /
  `flow_of_forest`), the intent `FlowSpec` (the repeat-menu + the linear-flow
  `allows_trace` decision), and the two gates `refines_upgrade` /
  `refines_intent` with located `RefineFinding`s.
- [`dregg-deploy/src/refine/tests.rs`](../dregg-deploy/src/refine/tests.rs) — the
  FFI differential (the verified export agrees with the Lean `#guard`s AND the
  mirror, both polarities), the mirror-agreement tests, the deliverable (safe
  narrowing accepted, unsafe widening rejected with the divergence named), the
  safety-vs-refinement independence pin, and the intent-conformance +
  trace-equivalence tests.
- The bridge: [`dregg-lean-ffi`](../dregg-lean-ffi) — `shadow_decide_refines` /
  `decide_refines_gate_available` (`src/lib.rs`), the `dregg_decide_refines_str`
  C shim (`src/lean_init.c`), and the `Dregg2.Deos.FlowRefine` splice + probe
  (`build.rs`).
- Upstream: [`metatheory/Dregg2/Deos/FlowRefine.lean`](../metatheory/Dregg2/Deos/FlowRefine.lean)
  (`decideRefines`, sound + complete; `@[export dregg_decide_refines]` +
  `gate_one_iff_sim` / `gate_zero_iff_not_sim`) and
  [`metatheory/docs/FLOW-COMPOSITION-ALGEBRA.md`](../metatheory/docs/FLOW-COMPOSITION-ALGEBRA.md)
  (the right-skew that makes refinement decidable).
