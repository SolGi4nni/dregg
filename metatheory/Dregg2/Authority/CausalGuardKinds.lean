/-
# Dregg2.Authority.CausalGuardKinds — NAMED constructors for the two causal guard atoms.

`Authority/CausalGuard.lean` defines the two installable causal guard atoms — `causallyAfter(E)` and
`monotoneOverForks(val)` — as `Predicate.Verifier` plugins that an app installs at the registry's
OPEN extension point `WitnessedKind.custom vk`. Promoting them to first-class *named kinds*
(`causalAfter` / `monotoneFork`) would be the cleanest surface, but that edits the SHARED
`Predicate.WitnessedKind` enum (a TCB-wide change touching every registry).

This module gives the same ergonomic win WITHOUT touching `Predicate.lean`: a thin convenience layer
that pins STABLE `vk` constants for the two atoms (`causalAfterVk` / `monotoneForkVk`) and exposes
`install…`/`registryFor…` builders so an app author installs a causal guard BY NAME —

  `installCausalAfter base B E`   /   `installMonotoneFork base B val`

— rather than hand-rolling the raw `fun k => if k = .custom vk then some (causallyAfterVerifier …)`
plumbing at a magic number. The wrappers are PROVED to denote the CausalGuard semantics: a witness
the named-kind registry accepts is exactly a causal-inclusion fact (`CausalAfter`) / a non-regressing
monotone edge — soundness flows through `registry_sound`/`adversarial_find_cannot_forge` unchanged.

The two `vk` constants are CONTENT-ADDRESSED stand-ins (distinct `Nat`s; in dregg1 they would be the
BLAKE3 hashes of the two predicate descriptors). `causalAfter_vk_ne_monotoneFork_vk` pins them
distinct, so the two named extensions never collide on one registry (`custom_distinct_vk`).

§8 boundary: NONE NEW — every result is dispatch + the order facts CausalGuard already proved. Pure,
`#eval`-able. Defines only new names under `namespace Dregg2.Authority.CausalGuardKinds`; touches
neither `Predicate.lean` nor `CausalGuard.lean`.
-/
import Dregg2.Authority.CausalGuard

namespace Dregg2.Authority.CausalGuardKinds

open Dregg2.Authority.Blocklace
open Dregg2.Time.Causal
open Dregg2.Authority.Predicate
open Dregg2.Authority.CausalGuard

/-! ## 1. The two STABLE `vk` constants — content-addressed names for the causal atoms.

In dregg1 a `custom` kind is keyed on the BLAKE3 hash of its predicate descriptor (`predicate.rs`);
here we fix two distinct `Nat`s standing for "the `causally_after` predicate descriptor" and "the
`monotone_over_forks` predicate descriptor". They are the NAMES an app author refers to. -/

/-- The stable `vk` for the `causallyAfter(E)` guard atom — the named slot it installs into. -/
def causalAfterVk : Nat := 0xCA05A  -- "causal-after"

/-- The stable `vk` for the `monotoneOverForks(val)` guard atom — its named slot. -/
def monotoneForkVk : Nat := 0x709E  -- "mono-fork"

/-- **`causalAfter_vk_ne_monotoneFork_vk` (PROVED) — the two named atoms never collide.** Their `vk`
constants are distinct, so installing both on one registry keeps them in separate dispatch slots
(`Predicate.custom_distinct_vk`): a `causally_after` proof can never be misrouted to the
`monotone_over_forks` verifier, nor vice-versa. -/
theorem causalAfter_vk_ne_monotoneFork_vk : causalAfterVk ≠ monotoneForkVk := by decide

/-! ## 2. `causallyAfter` — the named install + its registry, with the denotation lemma.

`installCausalAfter base B E` returns a registry equal to `base` everywhere EXCEPT the
`custom causalAfterVk` slot, where it dispatches `causallyAfterVerifier B E`. The app author writes
the call; the guarantee is the lemma below. -/

/-- **`installCausalAfter base B E`** — install the `causally_after(E)` guard atom under its stable
named kind. Returns a `Registry` that dispatches `causallyAfterVerifier B E` at `custom causalAfterVk`
and falls back to `base` elsewhere. The app author's one-liner; the kind is `causalAfterKind`. -/
def installCausalAfter (base : Registry GateStmt ChainWit) (B : Lace) (E : Block) :
    Registry GateStmt ChainWit :=
  fun k => if k = .custom causalAfterVk then some (causallyAfterVerifier B E) else base k

/-- The named kind the `causally_after` atom dispatches at (sugar for `.custom causalAfterVk`). -/
abbrev causalAfterKind : WitnessedKind := .custom causalAfterVk

/-- **`causalAfter_dispatch` (PROVED)** — the named registry runs EXACTLY the CausalGuard verifier at
its kind: `registryVerify (installCausalAfter base B E) causalAfterKind gate chain
= causallyAfterVerifier B E gate chain`. The named wrapper is a faithful re-exposure, not a new
checker. -/
theorem causalAfter_dispatch (base : Registry GateStmt ChainWit) (B : Lace) (E gate : Block)
    (chain : ChainWit) :
    registryVerify (installCausalAfter base B E) causalAfterKind gate chain
      = causallyAfterVerifier B E gate chain := by
  unfold registryVerify installCausalAfter causalAfterKind
  rw [if_pos rfl]

/-- **`causalAfter_named_denotes` (PROVED) — the wrapper DENOTES the CausalGuard semantics.** When the
NAMED-kind registry accepts a gate (with any witness chain), the gate causally follows `E` in the
happened-before order: `CausalAfter B E gate`. The named slot carries the identical modality the raw
atom does — promoting it to a name changes the ergonomics, never the meaning. -/
theorem causalAfter_named_denotes (base : Registry GateStmt ChainWit) (B : Lace) (E gate : Block)
    (chain : ChainWit)
    (h : registryVerify (installCausalAfter base B E) causalAfterKind gate chain = true) :
    CausalAfter B E gate :=
  causallyAfter_denotes_precedes B E gate chain ((causalAfter_dispatch base B E gate chain) ▸ h)

/-- **`causalAfter_named_discharges` (PROVED) — soundness-by-verification through the named kind.** An
accepted causal chain at the named kind discharges the predicate via `registry_sound`: the named
extension is a genuine registry plugin, inheriting the keystone unchanged. -/
theorem causalAfter_named_discharges (base : Registry GateStmt ChainWit) (B : Lace) (E gate : Block)
    (chain : ChainWit)
    (h : registryVerify (installCausalAfter base B E) causalAfterKind gate chain = true) :
    @Dregg2.Laws.Discharged GateStmt ChainWit
      (verifiableOfRegistry (installCausalAfter base B E) causalAfterKind) gate chain :=
  registry_sound (installCausalAfter base B E) causalAfterKind gate chain h

/-- **`causalAfter_named_cannot_forge` (PROVED) — the named gate is the sole authority.** No prover can
make the named atom accept a gate the in-TCB causal check rejects: if `causallyAfterVerifier B E gate
chain = false`, the named-kind dispatch rejects for every prover. A gate that does not causally follow
`E` is inadmissible at the named kind, exactly as at the raw atom. -/
theorem causalAfter_named_cannot_forge (base : Registry GateStmt ChainWit) (B : Lace) (E gate : Block)
    (chain : ChainWit) (hreject : causallyAfterVerifier B E gate chain = false) :
    ∀ (find : GateStmt → Option ChainWit), find gate = some chain →
      registryVerify (installCausalAfter base B E) causalAfterKind gate chain = false := by
  intro find hfound
  rw [causalAfter_dispatch base B E gate chain]
  -- the dispatch IS the verifier (defeq via the rewrite), and the verifier rejects.
  exact (causalAfter_dispatch base B E gate chain ▸
    causallyAfter_adversarial_cannot_forge base causalAfterVk B E gate chain hreject find hfound :
    _)

/-! ## 3. `monotoneOverForks` — the named install + its registry, with the denotation lemma.

The successor atom: install `monotoneStepVerifier B val` at the stable `monotoneForkVk` name. The
statement is the predecessor block `a`, the witness the successor `b`; accept iff `b` acks `a` and
`val` did not regress. -/

/-- **`installMonotoneFork base B val`** — install the `monotone_over_forks(val)` guard atom under its
stable named kind `custom monotoneForkVk`. The app author's one-liner; falls back to `base` elsewhere. -/
def installMonotoneFork (base : Registry Block Block) (B : Lace) (val : Block → Nat) :
    Registry Block Block :=
  fun k => if k = .custom monotoneForkVk then some (monotoneStepVerifier B val) else base k

/-- The named kind the `monotone_over_forks` atom dispatches at. -/
abbrev monotoneForkKind : WitnessedKind := .custom monotoneForkVk

/-- **`monotoneFork_dispatch` (PROVED)** — the named registry runs EXACTLY the per-edge monotone
verifier at its kind. The named wrapper is a faithful re-exposure of `monotoneStepVerifier`. -/
theorem monotoneFork_dispatch (base : Registry Block Block) (B : Lace) (val : Block → Nat)
    (a b : Block) :
    registryVerify (installMonotoneFork base B val) monotoneForkKind a b
      = monotoneStepVerifier B val a b := by
  unfold registryVerify installMonotoneFork monotoneForkKind
  rw [if_pos rfl]

/-- **`monotoneFork_named_denotes` (PROVED) — the wrapper DENOTES the CausalGuard semantics.** An
accepted step at the NAMED kind is a real, non-regressing ack edge: `precedes B a b ∧ val a ≤ val b`.
The named slot carries the identical local-monotonicity modality `monotoneStepVerifier` does. -/
theorem monotoneFork_named_denotes (base : Registry Block Block) (B : Lace) (val : Block → Nat)
    (a b : Block)
    (h : registryVerify (installMonotoneFork base B val) monotoneForkKind a b = true) :
    precedes B a b ∧ val a ≤ val b :=
  monotoneStep_sound B val a b ((monotoneFork_dispatch base B val a b) ▸ h)

/-- **`monotoneFork_named_implies_global` (PROVED) — every named-kind edge ⇒ global monotonicity.** If
EVERY direct ack edge is accepted by the named `monotone_over_forks(val)` kind, then `val` is monotone
along the WHOLE happened-before order (`MonotoneOverForks B val`). The named extension installs the
global causal grow-only property: each accepted edge denotes a local non-regression
(`monotoneFork_named_denotes`), and `monotoneStep_implies_monotone` chains them across `precedes`. -/
theorem monotoneFork_named_implies_global (base : Registry Block Block) (B : Lace) (val : Block → Nat)
    (haccept : ∀ a b, pointed B a b →
      registryVerify (installMonotoneFork base B val) monotoneForkKind a b = true) :
    MonotoneOverForks B val :=
  monotoneStep_implies_monotone B val
    (fun a b hab => (monotoneFork_named_denotes base B val a b (haccept a b hab)).2)

/-! ## 4. NON-VACUITY — the named installs decide exactly as the raw atoms (the demo lace witnesses).

We install both named kinds over the empty base registry (`emptyReg`, fails closed everywhere) on the
demo lace and check: the honest commit-reveal is ACCEPTED at the named `causalAfter` kind; the
concurrent fork reveal is REJECTED; the named slots are content-addressed (the `causalAfter` install
is silent at the `monotoneFork` kind). -/

/-- The empty base registry — every kind unregistered (fails closed); we install the named atoms over it. -/
def emptyReg {Stmt Wit : Type} : Registry Stmt Wit := fun _ => none

-- The honest reveal is ACCEPTED at the NAMED causal-after kind (single base ack edge `g0 ← g1`).
#guard registryVerify (installCausalAfter emptyReg demoLace CommitReveal.commit) causalAfterKind
        CommitReveal.honestReveal CommitReveal.honestChain                       -- true (accepted)
-- The concurrent fork reveal is REJECTED at the named kind (no ack edge `f1 ← f2`).
#guard (registryVerify (installCausalAfter emptyReg demoLace CommitReveal.forkCommit) causalAfterKind
        CommitReveal.forkReveal [] == false)                                     -- true (rejected)
-- A non-regressing step is ACCEPTED at the NAMED monotone-fork kind (seq 0 ≤ 1 on `g0 ← g1`).
#guard registryVerify (installMonotoneFork emptyReg demoLace (fun b => b.seq)) monotoneForkKind g0 g1
                                                                                  -- true (accepted)
-- Content-addressing: the causal-after install is SILENT at the monotone-fork kind (distinct vk).
#guard (registryVerify (installCausalAfter emptyReg demoLace CommitReveal.commit) monotoneForkKind
        CommitReveal.honestReveal CommitReveal.honestChain == false)              -- true (not consulted)

/-- **`named_commit_reveal_accepted` (PROVED) — the headline at the named kind.** The honest reveal is
admitted at the NAMED `causalAfter` kind, and its denotation is the lightcone fact
`CausalAfter demoLace commit honestReveal`. The named ergonomic surface carries the full guarantee. -/
theorem named_commit_reveal_accepted :
    registryVerify (installCausalAfter emptyReg demoLace CommitReveal.commit) causalAfterKind
        CommitReveal.honestReveal CommitReveal.honestChain = true ∧
      CausalAfter demoLace CommitReveal.commit CommitReveal.honestReveal := by
  refine ⟨by decide, ?_⟩
  exact causalAfter_named_denotes emptyReg demoLace CommitReveal.commit CommitReveal.honestReveal
    CommitReveal.honestChain (by decide)

/-- **`named_commit_reveal_rejected` (PROVED) — the named-kind teeth.** The concurrent fork reveal is
rejected at the NAMED kind for EVERY witness chain — a reveal that never observed its commit is
inadmissible whether plumbed raw or by name. -/
theorem named_commit_reveal_rejected (chain : ChainWit) :
    registryVerify (installCausalAfter emptyReg demoLace CommitReveal.forkCommit) causalAfterKind
        CommitReveal.forkReveal chain = false := by
  rw [causalAfter_dispatch]
  by_contra hne
  have hacc : causallyAfterVerifier demoLace CommitReveal.forkCommit CommitReveal.forkReveal chain
      = true := by
    cases hb : causallyAfterVerifier demoLace CommitReveal.forkCommit CommitReveal.forkReveal chain
    · exact absurd hb hne
    · rfl
  exact demo_causalAfter_fails.1
    (causallyAfter_denotes_precedes demoLace CommitReveal.forkCommit CommitReveal.forkReveal chain
      hacc)

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms causalAfter_vk_ne_monotoneFork_vk
#assert_axioms causalAfter_dispatch
#assert_axioms causalAfter_named_denotes
#assert_axioms causalAfter_named_discharges
#assert_axioms causalAfter_named_cannot_forge
#assert_axioms monotoneFork_dispatch
#assert_axioms monotoneFork_named_denotes
#assert_axioms monotoneFork_named_implies_global
#assert_axioms named_commit_reveal_accepted
#assert_axioms named_commit_reveal_rejected

end Dregg2.Authority.CausalGuardKinds
