# Lean toy audit — exhaustive census (2026-06-13)

An exhaustive, read-only audit of the entire Lean codebase (`metatheory/Dregg2/`,
**630 files / 251,638 lines**) for *toys* — holes in the "axiom-clean, sorry-free,
non-vacuity-tested" assurance claim. Method: one auditor per module group (27
groups), each confirming findings by reading actual code (not grepping), plus an
**adversarial verify pass** on every RED/load-bearing finding (a skeptic tries to
*refute* that each is a real hole).

## Verdict: the discipline largely HOLDS

The raw greps were ~99% false positives — the 615 "sorry" hits, 221 "native_decide"
hits, 238 ":= True" hits were overwhelmingly **doc-comments and self-attestation
banners** ("no sorry, no `:= True`, no native_decide, #assert_axioms-pinned…"),
field names (`Caveat.admits`), and prose. Confirmed real toy surface:

| category | raw grep | **confirmed real** |
|---|---:|---:|
| sorry / admit (proof position) | 615 | **0** |
| laundering axioms | 8 decls | **0** (all 8 are the legit crypto floor) |
| fake `#eval`-as-test | 228 | **0** (real smoke uses `#guard`) |
| load-bearing vacuity | 238 | **1** |
| `native_decide` | 221 | **4** |
| undischarged carried hypotheses | — | 13 (most legit; ~3 real debt) |
| hidden semantics (opaque/extern) | 246 | 3 (2 = legit crypto floor) |

20 of 27 groups GREEN. **RED: Coord only.** YELLOW: Apps, Circuit, Exec,
Lightclient, Spec, Time.

## The burn-down (ranked, most load-bearing first)

### 1. ⛔ THE real toy — a confirmed tautology (RED, must fix)
`Dregg2/Coord/SharedBudgetDynamics.lean:128` — `overspend_bounded_by_f_ceiling`:
```lean
theorem overspend_bounded_by_f_ceiling (balance f advSpend : Nat)
    (hadv : advSpend ≤ f * ceiling balance f) : advSpend ≤ f * ceiling balance f := hadv
```
It **takes its own conclusion as a hypothesis and returns it.** A
load-bearing-*named* Byzantine-overspend safety bound that proves nothing. The
verify pass confirmed it. FIX = prove the real bound from the Stingray ceiling
dynamics (or delete it and re-route consumers to a theorem that actually bounds
overspend). This is the one genuine vacuity in 251K lines.

### 2. ⚠ native_decide (discipline cleanup, 4 — Exec group)
`Dregg2/Exec/CapTPHandoffSound.lean:432,468,590,595` — all anonymous `example`
non-vacuity witnesses (validateHandoff2 = true/false). Good *intent* (both-polarity
teeth), wrong *tactic* — `native_decide` trusts the compiler outside the kernel.
Swap → `by decide`. Low severity (examples, not keystones), but it's the banned
pattern and should be the only 4 in the tree.

### 3. ⚠ one opaque relation to confirm
`Dregg2/Coord/StingrayCertReconcile.lean:367` — `producedBy : Silo → Cert → Prop`
is `opaque`. Confirm it isn't hiding semantics a soundness proof leans on (vs. a
legitimate abstraction boundary). (The other 2 "hidden" hits — `Crypto/PortalFloor`'s
8 `@[extern]` crypto ops + the Merkle `VerifierKernel` reference instance — the
verify pass OVERTURNED: they are the **legit named crypto floor**, not toys.)

### 4. honest carried-hypothesis debt (not laundering — labeled OPEN)
The 13 carried hyps are mostly legitimate (abstraction boundaries / structural
tree-invariants discharged on witnesses). The verify pass flagged these as *real
but honestly-labeled* apex debt to eventually discharge:
- `Apps/SealedBidAuction.lean:540` `escrow_refinement_sound (h : UserspaceDominatesKernel …)`
  — the userspace-escrow ≥ kernel-escrow obligation; only proved inhabitant is
  reflexivity; the real userspace-escrow cell-program witness needs a state clock
  the executor lacks (loudly fenced OPEN, segregated from the proved pile).
- `Coord/CausalOrder.lean` `hb_irrefl/hb_asymm/…` carry `d.noDup` undischarged
  (the sibling invariant exists — mild).
- `Coord/StingrayCertReconcile.lean:355` `byzantine_undetected_overspend_le_f_ceiling`
  (pairs with finding #1).
- Circuit `TurnEmit`/`TurnCircuitCompose` refinement hyps, Lightclient non-omission,
  Spec `WholeTurnTriangle`, Spike `state_commitment_binds_state`, Crypto `UCBridge`
  CryptHOL binding, Time `Deadline` — abstraction-boundary or named-floor hyps,
  reviewed as legit.

## What this means
dregg's Lean is disciplined: zero real sorries, zero laundering axioms, zero fake
tests across a quarter-million lines. The fixable surface is **one tautology + four
native_decide + one opaque to confirm**, plus a short list of honestly-labeled apex
debts (the escrow refinement the standout). The assurance claim is real; this is a
small, concrete burn-down, not a rot census.
