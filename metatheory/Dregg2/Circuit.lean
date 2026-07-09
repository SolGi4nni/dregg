/-
# Dregg2.Circuit — the circuit-from-Lean bridge: the ZK/AIR constraint system as a
# first-class Lean object, proved equivalent to the verified step spec.

`Exec/StepComplete.lean` proves every committed step attests the four `fullStepInv`
conjuncts (Conservation ∧ Authority ∧ ChainLink ∧ ObsAdvance). This module writes those
conjuncts as an arithmetic constraint system (AIR/R1CS shape, ℤ as field stand-in) and
proves soundness ∧ completeness:

    bridge : satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s'

`kernelCircuit` is pure data that extracts to the Rust prover; `bridge` certifies that
checking it is equivalent to checking `fullStepInv`. Given `bridge`, a verifier implemented
as `decide (satisfied kernelCircuit …)` has its §8 soundness law derived, not assumed.

Field layout: `totalPre`/`totalPost` (Conservation), `authBit` (Authority),
`lenPre`/`lenPost` (ObsAdvance + ChainLink length), `chainOk` (ChainLink list-equality).

Boundary: Conservation and ObsAdvance are pure arithmetic (both directions proved).
Authority is a {0,1} bit-equation (both directions proved). ChainLink full list-equality
cannot be reconstructed from scalars alone; it is carried as a decidable `chainOk` indicator
(defined to be the spec predicate). The obligation that the Rust prover's CR-hash digest
binds to this indicator — the §8 binding law, once flagged `-- PRIMITIVE:` — is now
DISCHARGED, reduced to `HashCR` (the standard hash collision-resistance floor) in
`section DigestBinding`: modelling the digest as a collision-resistant hash of the
length-framed chain trace, `chain_digest_binds` proves it determines the trace uniquely and
`chain_digest_binds_chainOk` proves it therefore determines the `chainOk` value — a hash
collision is the ONLY way two chains with different `chainOk` share a digest. Residual: `HashCR`.
-/
import Mathlib.Tactic
import Dregg2.Exec.StepComplete
import Dregg2.CryptoKernel
import Dregg2.Crypto.HermineHintMLWE

namespace Dregg2.Circuit

open Dregg2.Exec
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)

/-- `Turn` is a structure of decidable-eq scalar fields, so its equality (and hence
list-of-`Turn` equality, the ChainLink witness) is decidable. -/
instance : DecidableEq Turn := fun a b => by
  rcases a with ⟨a1, a2, a3, a4⟩; rcases b with ⟨b1, b2, b3, b4⟩
  simp only [Turn.mk.injEq]
  exact inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ## The constraint-system IR (arithmetic over ℤ — the field stand-in). -/

/-- A circuit variable (a column / wire index). -/
abbrev Var := Nat

/-- An assignment of field values to variables (the witness vector). -/
abbrev Assignment := Var → ℤ

/-- **Arithmetic expressions** — variables, constants, `+`, `*` over the field. This is the
circuit-shaped IR (R1CS/AIR gates are exactly sums of products of wires). -/
inductive Expr where
  | var   : Var → Expr
  | const : ℤ → Expr
  | add   : Expr → Expr → Expr
  | mul   : Expr → Expr → Expr
  deriving Repr

/-- Evaluate an expression under an assignment. -/
def Expr.eval : Expr → Assignment → ℤ
  | .var v,     a => a v
  | .const c,   _ => c
  | .add e₁ e₂, a => e₁.eval a + e₂.eval a
  | .mul e₁ e₂, a => e₁.eval a * e₂.eval a

/-- A single constraint: the gate equation `lhs = rhs`. -/
structure Constraint where
  lhs : Expr
  rhs : Expr

/-- A constraint **holds** under an assignment iff both sides evaluate equal. -/
def Constraint.holds (c : Constraint) (a : Assignment) : Prop :=
  c.lhs.eval a = c.rhs.eval a

/-- A constraint system is a list of constraints (the full AIR/R1CS). `abbrev` so the
`List` membership instance is visible to the `∀ c ∈ cs` quantifier in `satisfied`. -/
abbrev ConstraintSystem := List Constraint

/-- The system is **satisfied** iff every constraint holds (the prover's claim). -/
def satisfied (cs : ConstraintSystem) (a : Assignment) : Prop :=
  ∀ c ∈ cs, c.holds a

/-! ## Variable layout (the named wires of the PI surface). -/

/-- `totalPre`  — total supply before the turn. -/
def vTotalPre  : Var := 0
/-- `totalPost` — total supply after the turn. -/
def vTotalPost : Var := 1
/-- `authBit`   — the authority decision as a {0,1} bit. -/
def vAuthBit   : Var := 2
/-- `lenPre`    — receipt-chain length before. -/
def vLenPre    : Var := 3
/-- `lenPost`   — receipt-chain length after. -/
def vLenPost   : Var := 4
/-- `chainOk`   — {0,1} indicator that `post-log = turn :: pre-log` (ChainLink witness). -/
def vChainOk   : Var := 5

/-! ## `encode` — lay the pre/turn/post out as the witness vector. -/

/-- A {0,1} field encoding of a `Bool`. -/
def boolBit (b : Bool) : ℤ := if b then 1 else 0

/-- A {0,1} field encoding of a decidable `Prop`. -/
def propBit (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- **`encode`** — the pre-state, turn, and post-state laid out as a field assignment (the
witness the prover commits to). Unmentioned variables default to `0`. -/
def encode (s : ChainedState) (t : Turn) (s' : ChainedState) : Assignment := fun v =>
  if      v = vTotalPre  then total s.kernel
  else if v = vTotalPost then total s'.kernel
  else if v = vAuthBit   then boolBit (authorizedB s.kernel.caps t)
  else if v = vLenPre    then (s.log.length : ℤ)
  else if v = vLenPost   then (s'.log.length : ℤ)
  else if v = vChainOk   then propBit (s'.log = t :: s.log)
  else 0

/-! ## `kernelCircuit` — the four `fullStepInv` conjuncts as arithmetic gates. -/

/-- **Conservation gate:** `totalPost − totalPre = 0`, i.e. `totalPost = totalPre`. -/
def cConservation : Constraint :=
  { lhs := .var vTotalPost, rhs := .var vTotalPre }

/-- **Authority gate:** `authBit = 1` (the turn was authorized). -/
def cAuthority : Constraint :=
  { lhs := .var vAuthBit, rhs := .const 1 }

/-- **ChainLink gate:** `chainOk = 1` (the post-log is `turn :: pre-log`). The indicator is
bound by the chain digest in a real circuit — that binding is now the theorem
`chain_digest_binds_chainOk` (reduced to `HashCR`); here `chainOk` is the decidable witness. -/
def cChainLink : Constraint :=
  { lhs := .var vChainOk, rhs := .const 1 }

/-- **ObsAdvance gate:** `lenPost − lenPre − 1 = 0`, i.e. `lenPost = lenPre + 1`. -/
def cObsAdvance : Constraint :=
  { lhs := .var vLenPost, rhs := .add (.var vLenPre) (.const 1) }

/-- **The kernel circuit** — the constraint DATA encoding all four conjuncts. THIS is what
extracts to the Rust prover. -/
def kernelCircuit : ConstraintSystem :=
  [cConservation, cAuthority, cChainLink, cObsAdvance]

/-! ## Per-gate equivalences (each conjunct ↔ its gate under `encode`). -/

-- The variable lookups, proved by `simp`-unfolding the `if`-cascade with the index facts.

private theorem enc_vTotalPre (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vTotalPre = total s.kernel := by
  simp [encode, vTotalPre]

private theorem enc_vTotalPost (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vTotalPost = total s'.kernel := by
  simp [encode, vTotalPost, vTotalPre]

private theorem enc_vAuthBit (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vAuthBit = boolBit (authorizedB s.kernel.caps t) := by
  simp [encode, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vLenPre (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vLenPre = (s.log.length : ℤ) := by
  simp [encode, vLenPre, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vLenPost (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vLenPost = (s'.log.length : ℤ) := by
  simp [encode, vLenPost, vLenPre, vAuthBit, vTotalPost, vTotalPre]

private theorem enc_vChainOk (s : ChainedState) (t : Turn) (s' : ChainedState) :
    encode s t s' vChainOk = propBit (s'.log = t :: s.log) := by
  simp [encode, vChainOk, vLenPost, vLenPre, vAuthBit, vTotalPost, vTotalPre]

/-- **Conservation: gate ↔ conjunct** (full arithmetic, both directions). -/
theorem conservation_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cConservation.holds (encode s t s') ↔ consP s t s' := by
  unfold Constraint.holds cConservation consP
  simp only [Expr.eval, enc_vTotalPre, enc_vTotalPost]

/-- **Authority: gate ↔ conjunct** (the {0,1} bit, both directions). -/
theorem authority_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cAuthority.holds (encode s t s') ↔ authP s t s' := by
  unfold Constraint.holds cAuthority authP
  simp only [Expr.eval, enc_vAuthBit, boolBit]
  constructor
  · intro h
    by_cases hb : authorizedB s.kernel.caps t = true
    · exact hb
    · simp only [Bool.not_eq_true] at hb; rw [hb] at h; simp at h
  · intro h; rw [h]; simp

/-- **ChainLink: gate ↔ conjunct** (via the decidable indicator). The indicator is *defined*
to be the spec predicate, so both directions close; the §8 binding of the digest to this
indicator is now the theorem `chain_digest_binds_chainOk` (reduced to `HashCR`). -/
theorem chainlink_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cChainLink.holds (encode s t s') ↔ chainP s t s' := by
  -- (§8 binding of the digest to this indicator: now `chain_digest_binds_chainOk`, reduced to `HashCR`.)
  unfold Constraint.holds cChainLink chainP
  simp only [Expr.eval, enc_vChainOk, propBit]
  by_cases hc : s'.log = t :: s.log
  · simp [hc]
  · simp [hc]

/-- **ObsAdvance: gate ↔ conjunct** (full arithmetic, both directions). -/
theorem obsadvance_iff (s : ChainedState) (t : Turn) (s' : ChainedState) :
    cObsAdvance.holds (encode s t s') ↔ obsP s t s' := by
  unfold Constraint.holds cObsAdvance obsP
  simp only [Expr.eval, enc_vLenPre, enc_vLenPost]
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; push_cast; ring

/-! ## THE BRIDGE — the circuit is SOUND ∧ COMPLETE vs the verified spec. -/

/-- **`bridge` — the deliverable.** Satisfying `kernelCircuit` on the encoded
pre/turn/post is EXACTLY the verified `fullStepInv` (Conservation ∧ Authority ∧ ChainLink ∧
ObsAdvance). Forward (`→`) is circuit **soundness** (a satisfying witness proves the spec);
backward (`←`) is **completeness** (a real step has a satisfying witness). Both directions
of all four conjuncts are proved. -/
theorem bridge (s : ChainedState) (t : Turn) (s' : ChainedState) :
    satisfied kernelCircuit (encode s t s') ↔ fullStepInv s t s' := by
  unfold satisfied kernelCircuit fullStepInv
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (conservation_iff s t s').mp (h cConservation (by simp))
    · exact (authority_iff s t s').mp     (h cAuthority   (by simp))
    · exact (chainlink_iff s t s').mp     (h cChainLink   (by simp))
    · exact (obsadvance_iff s t s').mp    (h cObsAdvance  (by simp))
  · rintro ⟨hc, ha, hch, ho⟩ c hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact (conservation_iff s t s').mpr hc
    · exact (authority_iff s t s').mpr ha
    · exact (chainlink_iff s t s').mpr hch
    · exact (obsadvance_iff s t s').mpr ho

/-- **Soundness corollary** — a satisfying circuit witness PROVES the verified step
invariant (the `→` half of `bridge`, named for the extraction story). -/
theorem circuit_sound (s : ChainedState) (t : Turn) (s' : ChainedState)
    (h : satisfied kernelCircuit (encode s t s')) : fullStepInv s t s' :=
  (bridge s t s').mp h

/-- **Completeness corollary** — every real committed step yields a satisfying witness (the
`←` half). Composed with `cexec_attests`, the EXECUTOR produces circuit-satisfying witnesses
for free. -/
theorem circuit_complete (s : ChainedState) (t : Turn) (s' : ChainedState)
    (h : fullStepInv s t s') : satisfied kernelCircuit (encode s t s') :=
  (bridge s t s').mpr h

/-- **The executor produces satisfying witnesses (end-to-end).** Any committed
chained step (`cexec`) yields an assignment satisfying `kernelCircuit` — chaining
`cexec_attests` (step-completeness) with `bridge` (circuit completeness). This is the
prover side: running the kernel *is* generating a valid witness. -/
theorem cexec_satisfies_circuit {s s' : ChainedState} {t : Turn}
    (h : cexec s t = some s') : satisfied kernelCircuit (encode s t s') :=
  circuit_complete s t s' (cexec_attests h)

/-! ## The §8 verify-law derivation story (the extraction seam). -/

/-- **`verify_law_derivable`** — the verify soundness law is derived, not assumed.
For a verifier implemented as `decide (satisfied kernelCircuit (encode s t s'))`, the law
`verifyStep = true → fullStepInv` is `(bridge …).mp ∘ of_decide_eq_true`. The formerly
`-- PRIMITIVE:` obligation — that the Rust prover's CR-hash digest binds to the `chainOk`/
field wires — is now DISCHARGED in `section DigestBinding`: `chain_digest_binds_chainOk`
reduces that §8 cryptographic seam to `HashCR` (a hash collision is the only way one digest
serves two chains with different `chainOk`). No assumed §8 law remains — only the hash floor. -/
theorem verify_law_derivable (s : ChainedState) (t : Turn) (s' : ChainedState)
    [Decidable (satisfied kernelCircuit (encode s t s'))]
    (h : decide (satisfied kernelCircuit (encode s t s')) = true) :
    fullStepInv s t s' :=
  (bridge s t s').mp (of_decide_eq_true h)

/-- **The completeness companion of the derived verify law** — a real step makes
`verifyStep` accept. Together with `verify_law_derivable` this is a full soundness∧
completeness characterization of the circuit-checking verifier, with NO assumed §8 law. -/
theorem verify_complete (s : ChainedState) (t : Turn) (s' : ChainedState)
    [Decidable (satisfied kernelCircuit (encode s t s'))]
    (h : fullStepInv s t s') :
    decide (satisfied kernelCircuit (encode s t s')) = true :=
  decide_eq_true ((bridge s t s').mpr h)

/-! ## `section DigestBinding` — the §8 binding law, REDUCED to `HashCR` (the last PRIMITIVE seam).

`chainlink_iff`/`bridge` reduce circuit-checking to `chainP s t s'` (`s'.log = t :: s.log`) via the
decidable `chainOk` indicator. The one seam that stayed cryptographic — flagged `-- PRIMITIVE:` — was
"the Rust prover's CR-hash digest BINDS to that indicator" (`ChainedState.log`'s digest is
`CryptoKernel.hash log`, per `StepComplete`). We close it exactly as `Crypto.IdentityCommitment` closes
the id-commitment: model the digest as a collision-resistant hash `H` (the SAME `HashCR` carrier the
Hermine/identity arguments ride) applied to an INJECTIVELY length-framed chain trace. Then the digest
determines the trace uniquely (`chain_digest_binds`), hence determines any indicator of the trace and in
particular `chainOk` (`chain_digest_binds_chainOk`); two chains with a shared digest but different
`chainOk` are precisely a hash collision (`digest_collision_is_hash_collision`), breaking `HashCR`. So
the §8 binding is a THEOREM, and the only irreducible object is `HashCR` — the hash floor, no fresh
`…Hard` carrier. -/

section DigestBinding

/-- The digest of a chain **trace** `tr` (the log / receipt chain, framed): the collision-resistant hash
`H` (the imported `CommitReveal` carrier at index `Unit`) applied to the length-framed preimage
`frame tr`. Models `CryptoKernel.hash (frame log)` — the Rust prover's CR-hash over the chain. -/
def chainDigest {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig) (frame : Trace → Pre)
    (tr : Trace) : Dig :=
  cr.H () (frame tr)

/-- The verify gate: the presented trace `tr` recomputes to the claimed digest. Mirrors the Rust `==`
check of `CryptoKernel.hash log` against the committed digest. -/
def verifyDigest {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig) (frame : Trace → Pre)
    (dig : Dig) (tr : Trace) : Prop :=
  chainDigest cr frame tr = dig

/-- **DIGEST BINDING — the digest determines its trace UNIQUELY (the floor).** Under `HashCR` and an
injective framing, if two traces both verify against the same digest they are equal. Both verify ⇒
`H(frame tr) = dig = H(frame tr')` ⇒ (by `HashCR`, then injectivity of the length-framing)
`tr = tr'`. So a prover cannot serve one digest for two different chains without a hash collision. -/
theorem chain_digest_binds {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : Trace → Pre) (hinj : Function.Injective frame) (hcr : HashCR cr)
    (dig : Dig) (tr tr' : Trace)
    (h : verifyDigest cr frame dig tr) (h' : verifyDigest cr frame dig tr') : tr = tr' := by
  unfold verifyDigest chainDigest at h h'
  exact hinj (hcr () (frame tr) (frame tr') (h.trans h'.symm))

/-- **The digest binds ANY indicator of the trace** — in particular the `chainOk` value. If two traces
verify against the same digest, every function of the trace (any indicator `ind`) agrees on them. This is
the general form of "the digest binds `chainOk`": `chainOk` is one such indicator. -/
theorem chain_digest_binds_indicator {Trace Pre Dig β : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : Trace → Pre) (ind : Trace → β) (hinj : Function.Injective frame) (hcr : HashCR cr)
    (dig : Dig) (tr tr' : Trace)
    (h : verifyDigest cr frame dig tr) (h' : verifyDigest cr frame dig tr') : ind tr = ind tr' :=
  congrArg ind (chain_digest_binds cr frame hinj hcr dig tr tr' h h')

/-- **The reduction — distinct traces sharing a digest BREAK `HashCR`.** The contrapositive of
`chain_digest_binds`: two DISTINCT chains verifying one digest cannot coexist with collision-resistance.
This is what grounds the §8 binding in the one standard carrier `HashCR`. -/
theorem distinct_traces_break_hashcr {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : Trace → Pre) (hinj : Function.Injective frame) (dig : Dig) (tr tr' : Trace)
    (hne : tr ≠ tr') (h : verifyDigest cr frame dig tr) (h' : verifyDigest cr frame dig tr') :
    ¬ HashCR cr :=
  fun hcr => hne (chain_digest_binds cr frame hinj hcr dig tr tr' h h')

/-- **A digest-collision IS an `H`-collision (the length-framing is faithful).** Distinct traces hashing
to the same digest give two DISTINCT pre-images (by injectivity of the framing) mapping to one hash
output — a genuine collision on `H`. So a `chainOk`-equivocating digest reduces to a raw hash collision:
nothing beyond `HashCR` is at stake. -/
theorem digest_collision_is_hash_collision {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : Trace → Pre) (hinj : Function.Injective frame) (tr tr' : Trace) (hne : tr ≠ tr')
    (h : chainDigest cr frame tr = chainDigest cr frame tr') :
    ∃ p p' : Pre, p ≠ p' ∧ cr.H () p = cr.H () p' :=
  ⟨frame tr, frame tr', fun hp => hne (hinj hp), h⟩

/-- **A false chain is REJECTED by the honest digest (the teeth of binding).** If the honest trace `tr`
verifies the digest, any DIFFERENT trace `tr'` does NOT — passing would force `tr' = tr` by
`chain_digest_binds`, contradiction. So a digest opens for exactly its chain, no other. -/
theorem false_chain_not_bound {Trace Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : Trace → Pre) (hinj : Function.Injective frame) (hcr : HashCR cr)
    (dig : Dig) (tr tr' : Trace) (hne : tr ≠ tr') (h : verifyDigest cr frame dig tr) :
    ¬ verifyDigest cr frame dig tr' :=
  fun h' => hne (chain_digest_binds cr frame hinj hcr dig tr tr' h h')

/-! ### Tying the binding to the ACTUAL `chainOk` wire. -/

/-- The `chainOk` indicator of a chain trace `(preLog, turn, postLog)`: whether `postLog = turn :: preLog`
— the exact `chainP`/`vChainOk` predicate `s'.log = t :: s.log`. -/
def traceChainOk : List Turn × Turn × List Turn → Bool
  | (pre, tn, post) => decide (post = tn :: pre)

/-- **THE §8 BINDING LAW — the digest binds `chainOk` (reduced to `HashCR`).** For any injective framing
of the chain trace, if two traces verify the same digest they carry the SAME `chainOk` value. This is the
formerly-`PRIMITIVE` obligation, now a theorem: the Rust prover's CR-hash digest cannot serve one digest
for a valid chain (`chainOk = true`) and an invalid one (`chainOk = false`) — that would be a hash
collision. Reduced to `HashCR`, no assumed carrier. -/
theorem chain_digest_binds_chainOk {Pre Dig : Type*} (cr : CommitReveal Unit Pre Dig)
    (frame : List Turn × Turn × List Turn → Pre) (hinj : Function.Injective frame) (hcr : HashCR cr)
    (dig : Dig) (tr tr' : List Turn × Turn × List Turn)
    (h : verifyDigest cr frame dig tr) (h' : verifyDigest cr frame dig tr') :
    traceChainOk tr = traceChainOk tr' :=
  chain_digest_binds_indicator cr frame traceChainOk hinj hcr dig tr tr' h h'

/-- **`traceChainOk` IS the `vChainOk` wire.** The trace indicator on `(s.log, t, s'.log)`, as a {0,1}
field element, equals the `encode … vChainOk` wire value `propBit (s'.log = t :: s.log)`. So
`chain_digest_binds_chainOk` binds precisely the ChainLink wire that `chainlink_iff`/`bridge` consume. -/
theorem traceChainOk_eq_wire (s : ChainedState) (t : Turn) (s' : ChainedState) :
    boolBit (traceChainOk (s.log, t, s'.log)) = encode s t s' vChainOk := by
  rw [enc_vChainOk]
  simp only [traceChainOk, boolBit, propBit]
  by_cases hc : s'.log = t :: s.log <;> simp [hc]

end DigestBinding

#assert_axioms chain_digest_binds
#assert_axioms chain_digest_binds_indicator
#assert_axioms distinct_traces_break_hashcr
#assert_axioms digest_collision_is_hash_collision
#assert_axioms false_chain_not_bound
#assert_axioms chain_digest_binds_chainOk
#assert_axioms traceChainOk_eq_wire

/-! ## Teeth — the digest binding FIRES, and its `HashCR` hypothesis is LOAD-BEARING.

(a) A `HashCR`-respecting instance: the honest chain digest verifies, and a false chain (whose `chainOk`
    is `false`) is REJECTED by that digest — `false_chain_not_bound` fires.
(b) A `HashCR`-VIOLATING toy: a constant hash makes a VALID chain (`chainOk = true`) and an INVALID one
    (`chainOk = false`) share one digest, so the digest FAILS to bind `chainOk` — the `HashCR` hypothesis
    is genuinely load-bearing (non-vacuous), and the shared digest is exhibited as a real `H`-collision.
(c) The length-framing is faithful: naive concatenation of the three trace fields COLLIDES (ambiguous
    boundary), whereas the length-prefixed framing is injective — a digest-collision is a real hash one. -/

section Teeth

/-- The commitment hash `H((), p) = p`, injective on the framed domain (`HashCR`). Stands in for the
collision-resistant `CryptoKernel.hash` over the length-framed chain trace. -/
def exCRd : CommitReveal Unit (List ℕ) (List ℕ) := ⟨fun _ p => p⟩

theorem exCRd_hashcr : HashCR exCRd := fun _ _ _ h => h

/-- Length-prefixed framing of a toy trace `(pre, turn, post)` (over `ℕ`): `len(pre) ‖ pre ‖ turn ‖
len(post) ‖ post`. Self-describing, hence injective — the faithful reason a digest-collision is a hash
collision, not a framing artifact. -/
def exTraceFrame : List ℕ × ℕ × List ℕ → List ℕ
  | (pre, tn, post) => pre.length :: (pre ++ (tn :: post.length :: post))

/-- The framing is genuinely injective: distinct traces map to distinct pre-images (so distinct chains
give distinct digests under a real hash). Proved exactly as `IdentityCommitment.lenFrame_inj`. -/
theorem exTraceFrame_inj : Function.Injective exTraceFrame := by
  rintro ⟨pre, tn, post⟩ ⟨pre', tn', post'⟩ h
  simp only [exTraceFrame, List.cons.injEq] at h
  obtain ⟨hlen, hcat⟩ := h
  obtain ⟨hpre, hrest⟩ := List.append_inj hcat hlen
  simp only [List.cons.injEq] at hrest
  obtain ⟨htn, _, hpost⟩ := hrest
  subst hpre; subst htn; subst hpost; rfl

/-- A VALID chain trace: `post = turn :: pre` (`[1,2,3] = 1 :: [2,3]`), so `chainOk = true`. -/
def exGood : List ℕ × ℕ × List ℕ := ([2, 3], 1, [1, 2, 3])
/-- An INVALID chain trace: same `pre`/`turn` but `post = [9] ≠ 1 :: [2,3]`, so `chainOk = false`. -/
def exBad : List ℕ × ℕ × List ℕ := ([2, 3], 1, [9])

/-- The toy `chainOk` indicator over the `ℕ` trace (the teeth analogue of `traceChainOk`):
whether `post = turn :: pre`. -/
def toyChainOk : List ℕ × ℕ × List ℕ → Bool
  | (pre, tn, post) => decide (post = tn :: pre)

/-- The honest digest of the valid chain. -/
def exIdd : List ℕ := chainDigest exCRd exTraceFrame exGood

/-- The honest (valid) chain trace verifies its own digest. -/
theorem honest_digest_verifies : verifyDigest exCRd exTraceFrame exIdd exGood := rfl

/-- **THE TEETH FIRE.** The invalid chain `exBad` (whose `chainOk` is `false`) is REJECTED by the honest
digest: `false_chain_not_bound` gives `¬ verifyDigest`. The prover cannot pass off a broken chain under
the honest digest without a hash collision. -/
theorem false_chain_rejected : ¬ verifyDigest exCRd exTraceFrame exIdd exBad :=
  false_chain_not_bound exCRd exTraceFrame exTraceFrame_inj exCRd_hashcr exIdd exGood exBad
    (by decide) honest_digest_verifies

-- The valid chain's `chainOk` is `true`; the invalid chain's is `false`; their framings differ.
#guard toyChainOk exGood = true
#guard toyChainOk exBad = false
#guard exTraceFrame exGood ≠ exTraceFrame exBad

/-- A COLLIDING hash `H((), p) = []` for every preimage — every trace hashes to the SAME digest. This
VIOLATES `HashCR`. -/
def badCRd : CommitReveal Unit (List ℕ) (List ℕ) := ⟨fun _ _ => []⟩

/-- `badCRd` genuinely fails `HashCR`: the distinct preimages `[1] ≠ [2]` collide to `[]`. -/
theorem badCRd_not_hashcr : ¬ HashCR badCRd :=
  fun hcr => absurd (hcr () [1] [2] rfl) (by decide)

/-- **BINDING FAILS WITHOUT `HashCR` (load-bearing).** Under the colliding `badCRd`, the VALID chain
`exGood` (`chainOk = true`) and the INVALID chain `exBad` (`chainOk = false`) BOTH verify against the empty
digest `[]` — distinct traces, DIFFERENT `chainOk`, one digest. So `chain_digest_binds_chainOk`'s
conclusion is FALSE here: its `HashCR` hypothesis is genuinely load-bearing — without collision-resistance
the digest no longer binds `chainOk`. -/
theorem digest_binding_needs_hashcr :
    verifyDigest badCRd exTraceFrame [] exGood ∧ verifyDigest badCRd exTraceFrame [] exBad
      ∧ exGood ≠ exBad ∧ toyChainOk exGood ≠ toyChainOk exBad :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- …and that shared digest is exhibited as a genuine `H`-collision (`digest_collision_is_hash_collision`
fires): distinct framed pre-images, one hash output. -/
theorem badCRd_digest_collision : ∃ p p' : List ℕ, p ≠ p' ∧ badCRd.H () p = badCRd.H () p' :=
  digest_collision_is_hash_collision badCRd exTraceFrame exTraceFrame_inj exGood exBad (by decide) rfl

-- The collision is real: distinct FRAMED pre-images, ONE digest — the hash collided, not the framing.
#guard badCRd.H () (exTraceFrame exGood) = badCRd.H () (exTraceFrame exBad)
#guard exTraceFrame exGood ≠ exTraceFrame exBad

/-- Naive `pre ++ (turn :: post)` — no length prefix, so the field boundary is AMBIGUOUS. -/
def naiveTraceFrame : List ℕ × ℕ × List ℕ → List ℕ
  | (pre, tn, post) => pre ++ (tn :: post)

-- WITHOUT length-framing the encoding COLLIDES: two DISTINCT traces give ONE pre-image `[1,2,3]`.
#guard naiveTraceFrame ([1], 2, [3]) = naiveTraceFrame ([], 1, [2, 3])
-- WITH length-framing the SAME distinct traces give DISTINCT pre-images — injectivity restored.
#guard exTraceFrame ([1], 2, [3]) ≠ exTraceFrame ([], 1, [2, 3])

end Teeth

#assert_axioms exCRd_hashcr
#assert_axioms exTraceFrame_inj
#assert_axioms honest_digest_verifies
#assert_axioms false_chain_rejected
#assert_axioms badCRd_not_hashcr
#assert_axioms digest_binding_needs_hashcr
#assert_axioms badCRd_digest_collision

/-- Sanity: the circuit has exactly the four conjunct-gates. -/
example : kernelCircuit.length = 4 := rfl

end Dregg2.Circuit
