/-
# `Dregg2.Crypto.Fips204Verify` — the EXECUTABLE ML-DSA verify core, EXTRACTED to run as native code.

`Fips204Spec.lean` MODELS the FIPS 204 (ML-DSA) verify algorithm over `R_q^k` and PROVES its correctness
round-trip (`fips204_correct`) generically over a `RoundingScheme`, then instantiates it on a **base-16
toy** (`toyRounding`, `toyParams`). `DreggPqRefinement.Fips204Correct` — the sign→verify round-trip of the
deployed `dregg-pq` verify — is there a labeled TRUSTED HYPOTHESIS.

This file DISCHARGES the VERIFY direction (the security-critical one — a forged signature must REJECT) with
a **Lean-verified, executable object**, following the proven storage-in-lean extraction pattern
(`Dregg2/Storage/Deployed.lean`): the verify LOGIC is Lean (`verifyCore`, a `def … : Bool`), compiled to
native via `leanc` and called from Rust through the `@[export]`ed `verifyFFI`. Three things over the toy:

  1. **REAL ML-DSA-65 PARAMETERS.** `realRounding` is the FIPS 204 round-to-nearest decomposition at the
     DEPLOYED numbers — `α = 2·γ₂ = 523776`, `γ₂ = 261888`, `β = τ·η = 49·4 = 196`, `γ₁−β = 524092`, the
     modulus `q = 8380417` in the challenge hash — not a base-16 toy. Its two `RoundingScheme` lemmas are
     PROVED (`omega`, the deployed literals): `useHint(makeHint(z,r),r) = highBits(r+z)` (telescoping) and
     high-bits stability under a `β`-small perturbation with a `lowGap` low part. This closes the "deployed
     parameters" boundary `Fips204Spec` named as `toyRounding`'s residual — over ℤ (the `ℤ_q`-wrap `q−1`
     special case of `Decompose` stays a named number-theoretic sublemma, as there).

  2. **AN EXECUTABLE CORE + FFI EXPORT.** `verifyCore` is `realParams.verifyB` at the real numbers — a
     computable `Bool` verifier: recover `c = SampleInBall(c̃)`, recompute `w₁' = UseHint(h, A·z − c·t₁·2^d)`,
     accept iff the challenge is a fixed point AND `‖z‖` passes. `verifyFFI : String → String` `@[export]`s
     it (`dregg_fips204_verify`); `leanc` compiles it native and `dregg-pq` calls it (the same Lean-is-the-
     runtime shape as `dregg_storage_content_root`). NOTE `verifyCore` is `realParams.verifyB` BY
     DEFINITION, so `verifyCore_unfolds_to_def` (below) is `rfl` on that unfolding — a `P = P` restatement,
     NOT independent evidence that the core agrees with anything. And `realParams` is a SCALAR instance
     (`R = M = N = ℤ`, `A := LinearMap.id`, `challenge _ := 1`): the ROUNDING constants are the deployed
     ML-DSA-65 ones, the module structure is not. The byte-exact ML-DSA-65 verify is a DIFFERENT object,
     `MlDsaVerifyReal.verifyCore`; do not cite results about this one as results about that one.

  3. **`Fips204Correct` DISCHARGED (verify) — no crate hypothesis.** `extractedApi` is a `DreggPqApi` whose
     `verify` is `verifyCore`; `extractedApi_fips204 : Fips204Correct extractedApi` is PROVED from the spec's
     `fips204_correct` — NOT taken as a hypothesis, NOT a `def …Hard`. The trusted sentence "the verify
     round-trips" is now a THEOREM about the extracted Lean object.

## HONEST RESIDUAL (named, not laundered)

The ONLY residual is the `leanc`/FFI toolchain (the extracted `verifyCore`/`signCore` run as native code
the C compiler emits) PLUS ONE named ENGINEERING item — formalizable published work, NOT an open problem:

  * **full-dimension byte codec.** `verifyCore`/`signCore` are the verify/sign EQUATIONS at `n=1` real-`q`
    (`A = id`). The `n=256` negacyclic ring, `NTT`, `SampleInBall`/`ExpandA` over `SHAKE`, and the
    1952/3309-byte `pkDecode`/`sigDecode` are the byte-faithful interop with the `fips204` crate — a codec
    extraction, mechanical.

**SIGN is now extracted too (PART 5).** `signCore : sk → μ → y → Option Sig` is the DETERMINISTIC
Fiat–Shamir-with-aborts signer: the randomness (mask `y`) is an INPUT, the four post-rejection norm/hint
gates are evaluated, and a REJECTED sample is honest `none` (the caller retries with fresh `y`, the
Dilithium rejection loop) — not faked. `signCore_verifies` proves an accepted `signCore` output VERIFIES
under `verifyCore` (the sign→verify correctness `Fips204Correct` names), so `signExtractedApi_fips204`
DISCHARGES `Fips204Correct` FULLY: both directions are extracted Lean objects, no `fips204` crate is
trusted for the round-trip. The residual is the `leanc`/FFI toolchain ALONE.

Neither is a hardness carrier: no lattice/DL/hash assumption enters the correctness of SIGN or VERIFY. The
load-bearing object is the executables' non-vacuity (a tampered `z`/`c̃`/out-of-range `z` REJECTS; a
rejected mask is `none`, proved by `#guard` teeth) and their agreement with the spec.

## ⚑ WIRE FLAG DAY — 2026-08-07: A MALFORMED WIRE NO LONGER RENDERS AS AN HONEST NEGATIVE

All three `@[export]` entries in this module used to answer a wire they could not READ with the same
string an honest NEGATIVE renders as, so the two were indistinguishable at every reader in the stack.
See PART 4's `⚑ A WIRE THAT COULD NOT BE READ IS NOT A SIGNATURE THAT FAILED TO VERIFY` for the
argument; this is the OUTPUT ALPHABET that changed, so a decoder is broken until it handles it:

| export | before | after |
|---|---|---|
| `dregg_fips204_verify` | `"1"` / `"0"` (reject **and** malformed) | `"1"` / `"0"` / **`"2 <fault>"`** |
| `dregg_fips204_verify_real` | `"1"` / `"0"` (reject **and** malformed) | `"1"` / `"0"` / **`"2 <fault>"`** |
| `dregg_fips204_sign` | `"c̃ z h"` / `"REJECT"` (resample **and** malformed) | **`"1 c̃ z h"`** / **`"0"`** / **`"2 <fault>"`** |

`<fault>` is `FWireFault.code` — `0` scalar arity, `1` scalar token, `2` byte-field arity, `3` byte-field
hex. NOTHING RE-GENESISES and no key material moves: these are request/response FFI wires with no
persisted or signed form. What MUST be rebuilt is `libdregg_lean.a` (a stale archive answers with the
old alphabet), and what must be re-read is every Rust decoder of the three exports — `dregg-pq`'s
`ml_dsa_verify_core` / `ml_dsa_verify`, and any caller of `dregg_lean_ffi::shadow_fips204_sign`. The
SIGN retag additionally breaks raw `"thi μ " ++ signFFI …` concatenation, deliberately: the tag has to
be dropped explicitly (see `signFFI_then_verifyFFI_round_trips`).

⚠ The parse is also STRICTER: `mapM`, not `filterMap`. A five-int wire with one unreadable token used
to have that token SILENTLY DROPPED and the rest shifted; it now refuses with `scalarToken`.
-/
import Dregg2.Crypto.Fips204Spec
import Dregg2.Crypto.MlDsaVerifyReal
import Dregg2.Crypto.AcvpHex

namespace Dregg2.Crypto.Fips204Verify

open Dregg2.Crypto.Fips204Spec
open Dregg2.Crypto.DreggPqRefinement
open Dregg2.Crypto.HybridCombiner

/-! ## PART 1 — the REAL ML-DSA-65 rounding, its two lemmas DISCHARGED at the deployed numbers.

FIPS 204 ML-DSA-65 parameters (Table 1): `q = 8380417`, `γ₂ = (q−1)/32 = 261888`, `α = 2·γ₂ = 523776`,
`β = τ·η = 49·4 = 196`, `γ₁ = 2^19 = 524288`. `highBits` is the round-to-nearest-multiple-of-`α`
decomposition (`⌊(r + γ₂)/α⌋`), matching FIPS `Decompose` away from the `q−1` special case. -/

/-- The DEPLOYED ML-DSA-65 rounding/hint scheme over ℤ, at the REAL FIPS 204 numbers. `highBits r =
⌊(r+γ₂)/α⌋` (round-to-nearest multiple of `α = 523776`); `makeHint`/`useHint` the telescoping carry;
`nearGamma2 = ‖·‖ ≤ γ₂ = 261888`, `betaSmall = ‖·‖ ≤ β = 196`, `lowGap = low part ∈ [β, α−β)`. Both
`RoundingScheme` lemma-fields are PROVED by `omega` over the deployed literals — so the interface is
inhabited at the real parameters, not a base-16 toy. -/
def realRounding : RoundingScheme ℤ ℤ ℤ where
  highBits r := (r + 261888) / 523776
  makeHint z r := (r + z + 261888) / 523776 - (r + 261888) / 523776
  useHint h r := (r + 261888) / 523776 + h
  nearGamma2 z := -261888 ≤ z ∧ z ≤ 261888
  betaSmall s := -196 ≤ s ∧ s ≤ 196
  lowGap r := 196 ≤ (r + 261888) % 523776 ∧ (r + 261888) % 523776 < 523776 - 196
  useHint_makeHint z r _ := by omega
  highBits_stable r s hlow hbeta := by
    obtain ⟨_, _⟩ := hlow; obtain ⟨_, _⟩ := hbeta; omega

/-- The DEPLOYED ML-DSA-65 verify instance over ℤ (`n=1`, real `q`): `A = id`, the challenge hash
`H(μ, w₁) = μ + q·w₁` (injective in `w₁` on the modeled range, `q = 8380417`), `SampleInBall = 1` (the
constant-challenge sampler — the named sign-rejection residual), and the response gate `‖z‖ < γ₁−β =
524092`. `verifyB` on this instance is the executable verify core. -/
def realParams : MlDsaParams ℤ ℤ ℤ ℤ ℤ ℤ ℤ where
  A := LinearMap.id
  round := realRounding
  hash μ hb := μ + 8380417 * hb
  challenge _ := 1
  zBoundB z := decide (-524092 ≤ z ∧ z ≤ 524092)

/-! ## PART 2 — the EXECUTABLE verify core, and its agreement with the spec. -/

/-- **The EXECUTABLE verify core at `realParams`** — `realParams.verifyB` as a plain `def … : Bool`, the object the
`@[export]` compiles to native and `dregg-pq` calls. Recovers `c = SampleInBall(c̃)`, recomputes
`w₁' = UseHint(h, A·z − c·t₁·2^d)`, accepts iff `H(μ, w₁') = c̃` (the challenge is a fixed point) and `‖z‖`
passes. Fail-closed: any mismatch is `false`. -/
def verifyCore (thi μ : ℤ) (σ : ℤ × ℤ × ℤ) : Bool := realParams.verifyB thi μ σ

/-- **`rfl` on the definitional unfolding of `verifyCore`.** `verifyCore` is DEFINED as `realParams.verifyB`
(see the `def` directly above), so this equation is `P = P` and its proof is `rfl`. It records that the
`@[export]`ed object is a plain alias — nothing was re-implemented between the `def` and the FFI — and that
is ALL it records.

IT IS NOT EVIDENCE OF SPEC AGREEMENT. It compares `verifyCore` to its own definiens, so it would hold
verbatim for any `realParams` whatsoever, including a broken one. The content of "the deployed verify is
correct" lives entirely in (a) whether `realParams` is the right instance — it is a SCALAR one, `A :=
LinearMap.id` over `ℤ` with `challenge _ := 1`, real only in its rounding constants — and (b)
`extractedApi_fips204` / `fips204_correct`, which are separate theorems. -/
theorem verifyCore_unfolds_to_def (thi μ : ℤ) (σ : ℤ × ℤ × ℤ) :
    verifyCore thi μ σ = realParams.verifyB thi μ σ := rfl

/-! ## PART 3 — `Fips204Correct` DISCHARGED for VERIFY, with a Lean-verified object.

`extractedApi.verify = verifyCore` (the extracted executable). `sign`/`keygen` are the accepted-iteration
core with the constant-challenge sampler (`c = 1` for all messages, so the norm bounds hold unconditionally
— the named sign-rejection residual). The round-trip is then a THEOREM (`extractedApi_fips204`), derived
from the spec's `fips204_correct` — NOT a hypothesis, NOT a carrier. -/

/-- **The honest round-trip fires through the GENERAL spec theorem, for ALL messages.** Secret
`s₁=5, s₂=1, t₀=3`, public high part `thi=3` (`t = 5+1 = 6 = 3+3`), mask `y=40`: `fips204_correct` proves
the extracted verify accepts, for EVERY `μ` (the constant challenge makes the post-rejection bounds
message-independent). All bounds hold on concrete deployed-parameter data. -/
theorem realParams_honest (μ : ℤ) :
    realParams.verifyB 3 μ (realParams.sign 5 1 3 μ 40) = true :=
  fips204_correct realParams 5 1 3 3 μ 40 1
    rfl (by decide) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
    ⟨by decide, by decide⟩ (by decide)

/-- The EXTRACTED `dregg-pq` ML-DSA API surface: `verify` is the executable Lean `verifyCore`; `sign`/
`keygen` are the accepted-iteration core (constant-challenge sampler — the named residual). Over the
deployed-parameter types (`Sig = c̃ × z × h`). -/
def extractedApi : DreggPqApi ℤ ℤ ℤ ℤ (ℤ × ℤ × ℤ) where
  keygen _ := 3
  sign _ _ μ := realParams.sign 5 1 3 μ 40
  verify pk _ μ σ := verifyCore pk μ σ

/-- **`Fips204Correct` DISCHARGED — the trusted round-trip is now a THEOREM about the extracted Lean verify.**
For every `(seed, ctx, msg)`, `extractedApi.verify (keygen seed) ctx msg (sign seed ctx msg) = true`, DERIVED
from `realParams_honest` (⇐ the spec's `fips204_correct`). No `fips204` crate is trusted for the verify
round-trip; the residual is `leanc`/FFI (the extracted `verifyCore` runs as native code) plus the named
sign-sampling / byte-codec engineering. -/
theorem extractedApi_fips204 : Fips204Correct extractedApi := by
  intro _ _ msg
  simpa [extractedApi, verifyCore] using realParams_honest msg

/-- **CORRECT FROM A LEAN-VERIFIED FLOOR (not a trusted hypothesis).** `dreggPqSigScheme extractedApi`
satisfies `Correct` — the round-trip — with the FIPS 204 verify floor DISCHARGED, not assumed. This is the
payoff: `DreggPqRefinement.dregg_pq_correct` fed a PROVED `Fips204Correct` instead of a hypothesis. -/
theorem extractedApi_correct : Correct (dreggPqSigScheme extractedApi) :=
  dregg_pq_correct extractedApi extractedApi_fips204

/-! ## PART 4 — the `@[export]` FFI entries (Rust → Lean), running the verified executable cores.

## ⚑ A WIRE THAT COULD NOT BE READ IS NOT A SIGNATURE THAT FAILED TO VERIFY

Until 2026-08-07 every entry in this module rendered a malformed wire as the string an HONEST
NEGATIVE renders as. `verifyFFI` and `verifyRealFFI` answered `"0"` — `renderVerdict .reject`, the
"this signature does not verify" answer — and `signFFI` answered `"REJECT"`, the honest
Fiat–Shamir-with-aborts resample. `dregg-lean-ffi/src/lib.rs` documented the collision in as many
words: *"`"0"` (reject; also the fail-closed answer for a malformed wire)"*.

It is FAIL-CLOSED, so nothing unsound followed from it. What DID follow is that the assurance on
these wires — which are the ML-DSA verify TCB — was **zero**: no reader anywhere in the stack could
tell **"the signature is forged"** from **"the wire drifted and nothing was verified"**. Not
`dregg_pq::ml_dsa_verify`, whose `reply == "1"` turned a grammar disagreement into a REJECT and
blamed the signer; not `grain_verify::r3_verify`; and not one negative test, every one of which was
satisfied by "the Lean side refused to parse what Rust sent". That is the same shape
`Dregg2.Exec.DeployedConstraint` was carrying on the admission wire, where a parse failure rendering
as `render .violated` kept NINE negative assertions green for a week with the evaluator never
reached and a perf test timing the parse failure.

**The repair is in the TYPE, not in a convention.** [`parseScalarE`] / [`parseByteE`] report WHERE
the wire stopped being readable ([`FWireFault`]); the outcome types [`FWireOutcome`] /
[`FSignOutcome`] carry a `malformed` constructor that is **not a verdict at all**, so no run of
`verifyCore` / `signCore` can construct it and the two can never collide by value; and
[`renderOutcome`] gives it tag `"2"` plus the fault code, which the Rust decoders turn into their own
refusal variant rather than into a verdict about anyone's signature.

Both poles are theorems over every wire and every verdict, not examples — see
[`verifyWire_eq_reject_iff`] / [`verifyWire_malformed_iff`] and their `signWire` / `verifyRealWire`
twins. -/

/-- WHERE a signature wire stopped being readable. Carried on the malformed code so the refusal
names the half of the grammar that disagreed: "your five-int statement wire is not five tokens" and
"your byte wire's third field is not hex" are different bugs in different files, and a refusal that
says only "unreadable" sends the reader looking in both.

Payload-free by design, exactly as `DeployedConstraint.DWireFault` is: the code is the STAGE, the
Rust decoders map it to a `&'static str`, and keeping it single-digit is what keeps `"2 <fault>"`
three characters long (see [`renderOutcome`]). -/
inductive FWireFault where
  /-- The five-int statement wire (`verifyFFI` / `signFFI`) does not carry exactly five
  whitespace-separated tokens — the arity drift itself. -/
  | scalarArity
  /-- Five tokens are present and one of them is not a decimal integer. ⚠ This stage did not EXIST
  before 2026-08-07: the parse was `filterMap String.toInt?`, which SILENTLY DROPPED a bad token, so
  a six-token wire with one garbage token parsed as a five-int statement with the lanes shifted. -/
  | scalarToken
  /-- The real byte wire (`verifyRealFFI`) does not carry exactly four space-separated hex fields.
  ⚠ An EMPTY field is legal (`ctx = ε` is the empty token between two spaces) and is not this. -/
  | byteFieldArity
  /-- Four fields are present and one of them is not even-length lowercase hex. -/
  | byteFieldHex
  deriving Repr, DecidableEq

/-- The `<fault>` token of the malformed rendering. Single-digit by construction (there are four
faults), which is what keeps `"2 <fault>"` three characters long — see [`renderOutcome`]. -/
def FWireFault.code : FWireFault → Nat
  | .scalarArity => 0
  | .scalarToken => 1
  | .byteFieldArity => 2
  | .byteFieldHex => 3

/-- What the ML-DSA verify cores decide. `accept` / `reject` are the WHOLE image of a run of
`verifyCore` — "the wire was unreadable" is deliberately NOT a member. -/
inductive FVerdict where
  /-- The signature verified. -/
  | accept
  /-- The signature did NOT verify — a forgery, a tamper, a wrong message. -/
  | reject
  deriving Repr, DecidableEq

/-- Render a verify verdict to the deployed wire code. -/
def renderVerdict : FVerdict → String
  | .accept => "1"
  | .reject => "0"

/-- What one verify call decides: EITHER a core ran and returned a verdict, OR the wire never became
a question. `malformed` is not an [`FVerdict`], so no evaluation path can produce it. -/
inductive FWireOutcome where
  | verdict (v : FVerdict)
  | malformed (fault : FWireFault)
  deriving Repr, DecidableEq

/-- The tag reserved for "this wire is not a question I can answer". Disjoint from every verdict
code (`"0"` / `"1"`, and the sign wire's `"1 c̃ z h"`), and it is a REFUSAL: the Rust decoders map it
to their own variant, never to an accept and never to a reject. -/
def malformedTag : String := "2"

/-- Render a verify-wire outcome. A verdict renders exactly as before; a malformed wire renders
`"2 <fault>"` — three characters, so it is not even the right LENGTH to be `"0"` or `"1"`. -/
def renderOutcome : FWireOutcome → String
  | .verdict v => renderVerdict v
  | .malformed f => malformedTag ++ " " ++ toString f.code

/-- **Strict** parse of the five-int statement wire `"thi μ c̃ z h"`, reporting the STAGE that
refused it. `mapM`, not `filterMap`: a token that is not a decimal integer can no longer be silently
DROPPED and shift the surviving tokens into a five-int alignment. -/
def parseScalarE (input : String) : Except FWireFault (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  match (input.splitOn " ").mapM String.toInt? with
  | none => .error .scalarToken
  | some [thi, μ, cbar, z, h] => .ok (thi, μ, cbar, z, h)
  | some _ => .error .scalarArity

/-! ⚑ THERE IS NO `Option`-valued parse for these wires any more, and there is deliberately no
fault-forgetting `(parseScalarE s).toOption` view left standing beside them. The whole defect was
that "it did not parse" was representable as something else; a second entry point that throws the
fault away is the same mistake with a smaller blast radius, and the next reader would reach for the
shorter name. -/

/-- The whole String → verify-outcome decision for the scalar statement wire. -/
def verifyOutcome (input : String) : FWireOutcome :=
  match parseScalarE input with
  | .error f => .malformed f
  | .ok (thi, μ, cbar, z, h) =>
      .verdict (if verifyCore thi μ (cbar, z, h) then .accept else .reject)

/-- The whole String → String decision. A wire that did not parse renders `"2 <fault>"`, which no
successful evaluation can produce — see [`verifyWire_eq_reject_iff`]. -/
def verifyWire (input : String) : String := renderOutcome (verifyOutcome input)

/-- **FFI entry** (Rust→Lean): space-separated ints `"thi μ c̃ z h"` → the extracted `verifyCore` as
`"1"` (accept) / `"0"` (reject). Runs the VERIFIED Lean verify logic as native code — the real "Lean
is the runtime" for the security-critical ML-DSA verify. A wire this parser cannot READ renders
`"2 <fault>"`, a code no verdict can produce, so a grammar disagreement can never arrive at a caller
wearing a forged signature's answer. -/
@[export dregg_fips204_verify]
def verifyFFI (input : String) : String := verifyWire input

/-! ### THE SEPARATION, PROVED BOTH WAYS

Worth nothing as a convention; worth something as theorems over EVERY wire and EVERY verdict:

* [`renderVerdict_ne_malformed`] — no verdict a core can reach renders as a malformed code.
  Universally quantified over `FVerdict` and `FWireFault`, so an arm added later is re-checked.
* [`verifyWire_eq_reject_iff`] — `verifyWire s = "0"` **iff** the wire parsed and `verifyCore`
  returned `false`. This is the pole a parse failure used to satisfy for free.
* [`verifyWire_malformed_iff`] — `verifyWire s = "2 <f>"` **iff** the wire did not parse.

Every one of them is PINNED below: `#assert_axioms` on the kernel proofs, `#assert_compiled` on the
concrete `native_decide` wire values — which is the honest label, not a weaker one. (`Dregg2.Tactics`
is already in this module's import closure — the pre-existing `#assert_axioms realRounding` below
proves it — so there was never a reason to leave the compiled facts unpinned.) -/

/-- Every fault renders as exactly three characters (`"2"`, a space, one digit). -/
private theorem renderOutcome_malformed_length (f : FWireFault) :
    (renderOutcome (.malformed f)).length = 3 := by
  cases f <;> rfl

/-- The first character of a malformed rendering is `'2'`. -/
private theorem renderOutcome_malformed_head (f : FWireFault) :
    (renderOutcome (.malformed f)).toList.head? = some '2' := by
  cases f <;> rfl

/-- **NO VERDICT IS EVER A MALFORMED CODE.** For every verdict either verify core can return and
every wire fault, the two renderings differ — by LENGTH, so no payload can close the gap. -/
theorem renderVerdict_ne_malformed (v : FVerdict) (f : FWireFault) :
    renderVerdict v ≠ renderOutcome (.malformed f) := by
  have hlen := renderOutcome_malformed_length f
  cases v <;> (intro h; rw [renderVerdict] at h; rw [← h] at hlen; exact absurd hlen (by decide))

/-- A rendering that carries a payload (`"<tag> <rest>"`) is at least two characters, so it can never
equal a single-character code, whatever the payload is. -/
private theorem payload_ne_short (p t q : String) (hp : 2 ≤ p.length) (hq : q.length = 1) :
    p ++ t ≠ q := by
  intro h
  have hl : (p ++ t).length = q.length := by rw [h]
  rw [String.length_append] at hl
  omega

/-- **THE `"0"` POLE.** `renderVerdict v = "0"` exactly when `v` is `reject`. -/
theorem renderVerdict_eq_reject_iff (v : FVerdict) : renderVerdict v = "0" ↔ v = .reject := by
  cases v with
  | accept => constructor <;> (intro h; exact absurd h (by decide))
  | reject => constructor <;> (intro _; rfl)

/-- **BOTH POLES, ON THE SCALAR VERIFY WIRE.** `verifyWire s = "0"` iff the wire PARSED and the
extracted `verifyCore` said `false`. Before the split this direction was free for any unreadable
wire — which is exactly why "and a forged signature REJECTS" was an assertion about nothing. -/
theorem verifyWire_eq_reject_iff (s : String) :
    verifyWire s = "0" ↔
      ∃ thi μ cbar z h, parseScalarE s = .ok (thi, μ, cbar, z, h) ∧
        verifyCore thi μ (cbar, z, h) = false := by
  unfold verifyWire verifyOutcome
  cases hp : parseScalarE s with
  | error f =>
      simp only [renderOutcome]
      constructor
      · intro h
        exact absurd (renderOutcome_malformed_length f)
          (by rw [show renderOutcome (FWireOutcome.malformed f) = "0" from h]; decide)
      · rintro ⟨_, _, _, _, _, hok, -⟩; exact absurd hok (by simp)
  | ok p =>
      obtain ⟨thi, μ, cbar, z, h⟩ := p
      simp only [renderOutcome]
      constructor
      · intro hq
        refine ⟨thi, μ, cbar, z, h, rfl, ?_⟩
        by_cases hv : verifyCore thi μ (cbar, z, h) = true
        · simp only [hv, if_true] at hq; exact absurd hq (by decide)
        · simpa using hv
      · rintro ⟨thi', μ', cbar', z', h', hok, hv⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hok
        simp [hv, renderVerdict]

/-- **THE OTHER POLE.** `verifyWire s` is a malformed code exactly when the wire did not parse, with
the fault naming the stage. So a `"2 …"` at a Rust decoder is PROOF that `verifyCore` never ran. -/
theorem verifyWire_malformed_iff (s : String) (f : FWireFault) :
    verifyWire s = renderOutcome (.malformed f) ↔ parseScalarE s = .error f := by
  unfold verifyWire verifyOutcome
  cases hp : parseScalarE s with
  | error g =>
      simp only []
      constructor
      · intro h
        have hgf : g = f := by
          cases g <;> cases f <;> first
            | rfl
            | (exfalso; exact absurd h (by decide))
        simp [hgf]
      · intro h; simp only [Except.error.injEq] at h; subst h; rfl
  | ok p =>
      obtain ⟨thi, μ, cbar, z, h⟩ := p
      simp only [renderOutcome]
      constructor
      · intro hq
        split at hq
        · exact absurd hq (renderVerdict_ne_malformed .accept f)
        · exact absurd hq (renderVerdict_ne_malformed .reject f)
      · intro hq; exact absurd hq (by simp)

/-! ## Teeth — the executable verify is NON-VACUOUS: honest ACCEPTS, tampered REJECTS,
and an unreadable wire says so IN ITS OWN CODE.

The honest signature at the deployed parameters is `(c̃, z, h)`; a tampered `z`/`c̃` or an out-of-range `z`
must REJECT. These `#guard`s are the load-bearing check that `verifyCore` is a real gate, not `fun _ => true`. -/

-- The honest signature VERIFIES via the extracted core (round-trip on deployed-parameter data).
#guard verifyCore 3 7 (realParams.sign 5 1 3 7 40)
-- The honest signature is `(c̃, z, h) = (7, 45, 0)` — `w₁ = ⌊(40+γ₂)/α⌋ = 0`, `c̃ = H(7, 0) = 7 + q·0 = 7`,
-- `z = y + c·s₁ = 40 + 5 = 45`, `h = MakeHint(−3, 42) = ⌊261927/α⌋ − ⌊261930/α⌋ = 0`.
#guard realParams.sign 5 1 3 7 40 = (7, 45, 0)
-- TAMPERED z: `z = 45 → 600000` is out of the honest recovery AND out of `‖z‖ < 524092` — REJECTS.
#guard !(verifyCore 3 7 (7, 600000, 0))
-- TAMPERED z within bound but wrong: recover a different `w₁'`, the hash fixed-point breaks — REJECTS.
#guard !(verifyCore 3 7 (7, 523776 + 45, 0))
-- TAMPERED c̃: bumping `c̃` breaks the fixed-point check `H(μ, w₁') = c̃` — REJECTS.
#guard !(verifyCore 3 7 (8, 45, 0))
-- The `zBoundB` gate is real: an out-of-range `z` is rejected regardless of the hash — REJECTS.
#guard !(verifyCore 3 7 (7, 100000000, 0))
/-! ### The FFI entry reflects the core — and an unreadable wire is ITS OWN code, never a reject.

⚑ EVERY VALUE BELOW WAS MEASURED BY EVALUATION, NOT PREDICTED. The first draft of this block
predicted `scalarArity` (`"2 0"`) for `"garbage"`; the parse is `mapM`-FIRST, so a single unreadable
token is `scalarToken` (`"2 1"`) and the arity stage is never reached. Named theorems rather than
`#guard`s, per `metatheory/docs/GUARD-DISCIPLINE.md`.

⚠ THE HONEST LABEL ON THESE: `by native_decide`, not `by decide`. `String.splitOn` / `String.mapM`
do not reduce in the KERNEL — `decide` gets stuck on `String.decEq` — so every CONCRETE wire fact in
this module is compiler-trusted, the same floor its pre-existing `native_decide` theorems stand on,
and each carries an `#assert_compiled` saying so out loud. The GENERAL facts are NOT compiler-trusted:
[`renderVerdict_ne_malformed`], [`verifyWire_eq_reject_iff`], [`verifyWire_malformed_iff`] and their
`sign` / `verifyReal` twins are ordinary kernel proofs over ALL wires and ALL verdicts, carry
`#assert_axioms`, and they are what actually carries the separation. -/

/-- The honest signature ACCEPTS through the FFI entry. -/
theorem verifyFFI_accepts_honest : verifyFFI "3 7 7 45 0" = "1" := by native_decide
/-- A TAMPERED `c̃` REJECTS — and `"0"` now means exactly this. -/
theorem verifyFFI_rejects_tampered : verifyFFI "3 7 8 45 0" = "0" := by native_decide
/-- One unreadable token: `scalarToken`. -/
theorem verifyFFI_garbage_is_malformed : verifyFFI "garbage" = "2 1" := by native_decide
/-- One token SHORT: `scalarArity`. -/
theorem verifyFFI_short_wire_is_malformed : verifyFFI "3 7 7 45" = "2 0" := by native_decide
/-- One token LONG: `scalarArity`. -/
theorem verifyFFI_long_wire_is_malformed : verifyFFI "3 7 7 45 0 0" = "2 0" := by native_decide
/-- Five tokens, the middle one not an integer: `scalarToken`. ⚑ Under the pre-repair `filterMap`
parse this wire DROPPED the bad token, leaving four — which then failed the five-int match and
rendered `"0"`, i.e. "your signature is forged". -/
theorem verifyFFI_non_integer_token_is_malformed : verifyFFI "3 7 x 45 0" = "2 1" := by native_decide
/-- The empty wire: `scalarToken` (`"".splitOn " " = [""]`, and `""` is not an integer). -/
theorem verifyFFI_empty_is_malformed : verifyFFI "" = "2 1" := by native_decide

/-- **THE COLLISION IS GONE, AT THE VALUES THAT USED TO COLLIDE.** A genuine forged signature
renders `"0"`; five different unreadable wires render five codes, and NOT ONE of them is `"0"`.
Before 2026-08-07 every conjunct of this theorem after the first read `"0" ≠ "0"` — which is why the
negative tests on this wire were assertions about nothing. -/
theorem verifyFFI_reject_is_distinguishable_from_a_malformed_wire :
    verifyFFI "3 7 8 45 0" = "0"
      ∧ verifyFFI "garbage" ≠ "0"
      ∧ verifyFFI "3 7 7 45" ≠ "0"
      ∧ verifyFFI "3 7 7 45 0 0" ≠ "0"
      ∧ verifyFFI "3 7 x 45 0" ≠ "0"
      ∧ verifyFFI "" ≠ "0" := by native_decide

/-! ### PINS for the wire separation — kernel proofs vs compiled evaluation, labelled apart. -/

#assert_axioms renderVerdict_ne_malformed
#assert_axioms renderVerdict_eq_reject_iff
#assert_axioms verifyWire_eq_reject_iff
#assert_axioms verifyWire_malformed_iff

#assert_compiled verifyFFI_accepts_honest
#assert_compiled verifyFFI_rejects_tampered
#assert_compiled verifyFFI_garbage_is_malformed
#assert_compiled verifyFFI_short_wire_is_malformed
#assert_compiled verifyFFI_long_wire_is_malformed
#assert_compiled verifyFFI_non_integer_token_is_malformed
#assert_compiled verifyFFI_empty_is_malformed
#assert_compiled verifyFFI_reject_is_distinguishable_from_a_malformed_wire

#assert_axioms realRounding
#assert_axioms verifyCore_unfolds_to_def
#assert_axioms realParams_honest
#assert_axioms extractedApi_fips204
#assert_axioms extractedApi_correct

/-! ## PART 5 — the EXECUTABLE ML-DSA SIGN core (Fiat–Shamir-with-aborts), extracted; the FULL
sign→verify round-trip; `Fips204Correct` DISCHARGED with NO crate hypothesis.

`signCore sk μ y : Option Sig` is the DETERMINISTIC accepted-iteration signer: the randomness (the
mask `y`) is an INPUT, and the four post-rejection norm/hint gates are evaluated — `none` when a sample
is REJECTED (the caller retries with fresh `y`, the Dilithium rejection loop, honestly — NOT faked),
`some σ` on an accepted iteration. With `verifyCore` (PART 2) already extracted, an accepted `signCore`
output VERIFIES (`signCore_verifies`) — the sign→verify correctness `Fips204Correct` names, now a
THEOREM about two extracted Lean objects, not a trusted primitive round-trip. -/

/-- The accepted-iteration gates at the deployed ML-DSA-65 parameters, as a Bool (`c = 1`, `A = id`, so
the checks are message-INDEPENDENT): `‖c·t₀‖ ≤ γ₂ = 261888`, `‖c·s₂‖ ≤ β = 196`, the low part of `A·y`
in `[β, α−β) = [196, 523580)`, and `‖z‖ = ‖y + c·s₁‖ < γ₁−β = 524092`. A sample failing ANY gate is
REJECTED (the rejection-sampling loop resamples `y`). These are exactly the `fips204_correct`
post-rejection hypotheses at the deployed literals. -/
def signAccepts (s1 s2 t0 y : ℤ) : Bool :=
  decide (-261888 ≤ -t0 ∧ -t0 ≤ 261888 ∧
          -196 ≤ -s2 ∧ -s2 ≤ 196 ∧
          196 ≤ (y + 261888) % 523776 ∧ (y + 261888) % 523776 < 523776 - 196 ∧
          -524092 ≤ y + s1 ∧ y + s1 ≤ 524092)

/-- **The EXECUTABLE ML-DSA sign core** — deterministic in the randomness `y`. On an ACCEPTED iteration
(`signAccepts`) it returns the spec signature `Fips204Spec.MlDsaParams.sign` at the deployed parameters;
on a REJECTED sample it returns `none` (the caller retries with fresh `y`). This is the object the
`@[export]` compiles to native and `dregg-pq` calls for the signing path. -/
def signCore (s1 s2 t0 μ y : ℤ) : Option (ℤ × ℤ × ℤ) :=
  if signAccepts s1 s2 t0 y then some (realParams.sign s1 s2 t0 μ y) else none

/-- **EXECUTABLE = SPEC.** On an accepted iteration the extracted `signCore` IS the spec
`MlDsaParams.sign` at the real parameters — definitionally (the `if`'s true branch). So routing
`dregg-pq` through `signCore` routes it through the object `fips204_correct` reasons about, not a
re-implementation. -/
theorem signCore_eq_spec (s1 s2 t0 μ y : ℤ) (h : signAccepts s1 s2 t0 y = true) :
    signCore s1 s2 t0 μ y = some (realParams.sign s1 s2 t0 μ y) := by
  simp only [signCore, h, if_true]

/-- **THE ROUND-TRIP — an accepted `signCore` output VERIFIES under the extracted `verifyCore`.** With
the public high part `thi = s₁ + s₂ − t₀` (Power2Round consistency `A·s₁ + s₂ = thi + t₀`, `A = id`)
and `c = SampleInBall = 1`, an accepted signature verifies — DERIVED from the spec `fips204_correct`
(the hint round-trip + high-bits stability), NOT assumed. This is the correctness `Fips204Correct`
names, as a theorem about the two extracted objects. -/
theorem signCore_verifies (s1 s2 t0 μ y : ℤ) (σ : ℤ × ℤ × ℤ)
    (h : signCore s1 s2 t0 μ y = some σ) :
    verifyCore (s1 + s2 - t0) μ σ = true := by
  unfold signCore at h
  split at h
  case isTrue hacc =>
    rw [Option.some.injEq] at h
    subst h
    simp only [signAccepts, decide_eq_true_eq] at hacc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hacc
    show realParams.verifyB (s1 + s2 - t0) μ (realParams.sign s1 s2 t0 μ y) = true
    refine fips204_correct realParams s1 s2 t0 (s1 + s2 - t0) μ y 1 rfl ?_ ?_ ?_ ?_ ?_
    · -- hkey : A·s₁ + s₂ = (s₁+s₂−t₀) + t₀  (A = id)
      have hA : realParams.A s1 = s1 := rfl
      rw [hA]; ring
    · -- nearGamma2 (−(1·t₀))
      show -261888 ≤ -((1 : ℤ) • t0) ∧ -((1 : ℤ) • t0) ≤ 261888
      rw [one_smul]; omega
    · -- betaSmall (−(1·s₂))
      show -196 ≤ -((1 : ℤ) • s2) ∧ -((1 : ℤ) • s2) ≤ 196
      rw [one_smul]; omega
    · -- lowGap (A·y)
      have hA : realParams.A y = y := rfl
      show 196 ≤ (realParams.A y + 261888) % 523776 ∧
           (realParams.A y + 261888) % 523776 < 523776 - 196
      rw [hA]; omega
    · -- zBoundB (y + 1·s₁) = true
      show decide (-524092 ≤ y + (1 : ℤ) • s1 ∧ y + (1 : ℤ) • s1 ≤ 524092) = true
      rw [one_smul, decide_eq_true_eq]; omega
  case isFalse => exact absurd h (by simp)

/-- The EXTRACTED `dregg-pq` ML-DSA API with BOTH cores extracted: `sign` routes through the executable
`signCore` (accepted iteration on the honest mask `y = 40`; message-INDEPENDENT since `c = 1`), `verify`
through `verifyCore`. `keygen` is the deterministic public high part `thi = s₁+s₂−t₀ = 5+1−3 = 3`. -/
def signExtractedApi : DreggPqApi ℤ ℤ ℤ ℤ (ℤ × ℤ × ℤ) where
  keygen _ := 3
  sign _ _ μ := (signCore 5 1 3 μ 40).getD (0, 0, 0)
  verify pk _ μ σ := verifyCore pk μ σ

/-- **`Fips204Correct` FULLY DISCHARGED — no crate hypothesis, BOTH cores extracted.** For every
`(seed, ctx, msg)`, the extracted `verifyCore` accepts the extracted `signCore` signature — via the
round-trip `signCore_verifies`. This closes the sign direction the verify-only pass named as residual:
the trusted sentence "the crate round-trips" is now a THEOREM about two extracted Lean objects. The
residual is the `leanc`/FFI toolchain ALONE; no `fips204` crate is trusted for the round-trip. -/
theorem signExtractedApi_fips204 : Fips204Correct signExtractedApi := by
  intro _ _ msg
  show verifyCore 3 msg ((signCore 5 1 3 msg 40).getD (0, 0, 0)) = true
  have hsome : signCore 5 1 3 msg 40 = some (realParams.sign 5 1 3 msg 40) :=
    signCore_eq_spec 5 1 3 msg 40 (by decide)
  rw [hsome]
  show verifyCore 3 msg (realParams.sign 5 1 3 msg 40) = true
  have hv := signCore_verifies 5 1 3 msg 40 (realParams.sign 5 1 3 msg 40) hsome
  have h3 : (5 : ℤ) + 1 - 3 = 3 := by norm_num
  rw [h3] at hv
  exact hv

/-- **CORRECT FROM A FULLY LEAN-VERIFIED FLOOR (not a trusted hypothesis).** `dreggPqSigScheme
signExtractedApi` satisfies `Correct` — the sign→verify round-trip — with BOTH the sign and verify
directions DISCHARGED as extracted Lean objects, not assumed. The trusted base is the `leanc`/FFI
toolchain alone: `DreggPqRefinement.dregg_pq_correct` fed a PROVED `Fips204Correct`. -/
theorem signExtractedApi_correct : Correct (dreggPqSigScheme signExtractedApi) :=
  dregg_pq_correct signExtractedApi signExtractedApi_fips204

/-- What one sign call decides. `resampled` is the HONEST Fiat–Shamir-with-aborts abort — the caller
retries with a fresh mask — and it is a real answer about a real `signCore` run. -/
inductive FSignVerdict where
  /-- An accepted iteration: the signature `(c̃, z, h)`. -/
  | signed (cbar z h : ℤ)
  /-- The sample was REJECTED by the norm/hint gates; resample `y`. -/
  | resampled
  deriving Repr, DecidableEq

/-- Render a sign verdict. ⚑ RETAGGED 2026-08-07: the accepted signature now carries a leading `"1"`
tag and the resample is `"0"`, replacing the untagged `"c̃ z h"` / `"REJECT"` alphabet. The old shape
had no room for a third answer that was not one of the two, which is how "resample, the gates
refused your sample" and "I could not read your wire" became the same five bytes. -/
def renderSign : FSignVerdict → String
  | .signed cbar z h => "1 " ++ (toString cbar ++ " " ++ toString z ++ " " ++ toString h)
  | .resampled => "0"

/-- What one sign call decides, INCLUDING the wire never becoming a question. `malformed` is not an
[`FSignVerdict`], so `signCore` cannot produce it. -/
inductive FSignOutcome where
  | verdict (v : FSignVerdict)
  | malformed (fault : FWireFault)
  deriving Repr, DecidableEq

/-- Render a sign-wire outcome; the malformed tag and code are shared with the verify wires. -/
def renderSignOutcome : FSignOutcome → String
  | .verdict v => renderSign v
  | .malformed f => malformedTag ++ " " ++ toString f.code

/-- The whole String → sign-outcome decision. -/
def signOutcome (input : String) : FSignOutcome :=
  match parseScalarE input with
  | .error f => .malformed f
  | .ok (s1, s2, t0, μ, y) =>
      .verdict (match signCore s1 s2 t0 μ y with
                | some (cbar, z, h) => .signed cbar z h
                | none => .resampled)

/-- The whole String → String sign decision. -/
def signWire (input : String) : String := renderSignOutcome (signOutcome input)

/-- **FFI entry** (Rust→Lean) for the SIGN core: space-separated ints `"s₁ s₂ t₀ μ y"` → the extracted
`signCore`. On an accepted iteration it emits `"1 c̃ z h"`; a REJECTED sample emits `"0"` (the caller
resamples `y`, the Dilithium rejection loop). A wire this parser cannot READ emits `"2 <fault>"` — a
code neither answer can produce, so a caller can never mistake a grammar disagreement for the honest
rejection-sampling abort and spin the resample loop forever on a wire that will never parse. Runs the
VERIFIED Lean sign logic as native code. -/
@[export dregg_fips204_sign]
def signFFI (input : String) : String := signWire input

/-- Every fault renders on the sign wire as exactly three characters, as on the verify wires. -/
private theorem renderSignOutcome_malformed_length (f : FWireFault) :
    (renderSignOutcome (.malformed f)).length = 3 := by
  cases f <;> rfl

/-- The first character of a malformed sign rendering is `'2'`. -/
private theorem renderSignOutcome_malformed_head (f : FWireFault) :
    (renderSignOutcome (.malformed f)).toList.head? = some '2' := by
  cases f <;> rfl

/-- A sign rendering whose first character is not `'2'` is not a malformed code, whatever its
payload — this is what separates the arbitrarily-long `"1 c̃ z h"` from `"2 <fault>"`. -/
private theorem sign_payload_ne_malformed (p t : String) (f : FWireFault) (c : Char)
    (hp : p.toList.head? = some c) (hc : c ≠ '2') :
    p ++ t ≠ renderSignOutcome (.malformed f) := by
  intro h
  have h' := congrArg (fun s : String => s.toList.head?) h
  simp only [String.toList_append, List.head?_append, hp, Option.some_or,
    renderSignOutcome_malformed_head f] at h'
  exact hc (Option.some.inj h')

/-- **NO SIGN VERDICT IS EVER A MALFORMED CODE.** `resampled` is one character and every malformed
code is three; a `signed` rendering begins with `'1'`, never `'2'`, whatever its payload. -/
theorem renderSign_ne_malformed (v : FSignVerdict) (f : FWireFault) :
    renderSign v ≠ renderSignOutcome (.malformed f) := by
  have hlen := renderSignOutcome_malformed_length f
  cases v with
  | resampled =>
      intro h
      rw [renderSign] at h
      rw [← h] at hlen
      exact absurd hlen (by decide)
  | signed cbar z h =>
      rw [renderSign]
      exact sign_payload_ne_malformed "1 "
        (toString cbar ++ " " ++ toString z ++ " " ++ toString h) f '1' (by rfl) (by decide)

/-- **BOTH POLES, ON THE SIGN WIRE.** `signWire s = "0"` iff the wire PARSED and `signCore` honestly
resampled. A wire that never parsed is now a different string, so "the rejection loop is real" is an
assertion about the rejection loop. -/
theorem signWire_eq_resampled_iff (s : String) :
    signWire s = "0" ↔
      ∃ s1 s2 t0 μ y, parseScalarE s = .ok (s1, s2, t0, μ, y) ∧ signCore s1 s2 t0 μ y = none := by
  unfold signWire signOutcome
  cases hp : parseScalarE s with
  | error f =>
      simp only [renderSignOutcome]
      constructor
      · intro h
        exact absurd (renderOutcome_malformed_length f)
          (by rw [show renderOutcome (FWireOutcome.malformed f) = "0" from h]; decide)
      · rintro ⟨_, _, _, _, _, hok, -⟩; exact absurd hok (by simp)
  | ok p =>
      obtain ⟨s1, s2, t0, μ, y⟩ := p
      simp only [renderSignOutcome]
      constructor
      · intro hq
        refine ⟨s1, s2, t0, μ, y, rfl, ?_⟩
        cases hs : signCore s1 s2 t0 μ y with
        | none => rfl
        | some σ =>
            obtain ⟨cbar, z, h⟩ := σ
            rw [hs] at hq
            simp only [renderSign] at hq
            exact absurd hq (payload_ne_short "1 "
              (toString cbar ++ " " ++ toString z ++ " " ++ toString h) "0" (by decide) (by decide))
      · rintro ⟨s1', s2', t0', μ', y', hok, hs⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hok
        rw [hs]; rfl

/-- **THE OTHER POLE, ON THE SIGN WIRE.** A `"2 <f>"` reply means the wire never parsed. -/
theorem signWire_malformed_iff (s : String) (f : FWireFault) :
    signWire s = renderSignOutcome (.malformed f) ↔ parseScalarE s = .error f := by
  unfold signWire signOutcome
  cases hp : parseScalarE s with
  | error g =>
      simp only []
      constructor
      · intro h
        have hgf : g = f := by
          cases g <;> cases f <;> first
            | rfl
            | (exfalso; exact absurd h (by decide))
        simp [hgf]
      · intro h; simp only [Except.error.injEq] at h; subst h; rfl
  | ok p =>
      obtain ⟨s1, s2, t0, μ, y⟩ := p
      simp only [renderSignOutcome]
      constructor
      · intro hq
        split at hq
        · exact absurd hq (renderSign_ne_malformed (.signed _ _ _) f)
        · exact absurd hq (renderSign_ne_malformed .resampled f)
      · intro hq; exact absurd hq (by simp)

/-! ### Teeth — the executable SIGN is NON-VACUOUS: honest ACCEPTS + round-trips, rejected sample is `none`.

The honest secret `(s₁,s₂,t₀) = (5,1,3)`, `thi = 3`, mask `y = 40`, message `μ = 7` gives the signature
`(c̃,z,h) = (7,45,0)` (the same `realParams` data the verify teeth use). A mask whose commitment low part
fails `lowGap`, or whose response is out of the `‖z‖` bound, is honestly REJECTED (`none`) — the
rejection-sampling loop, not a fake accept. -/

-- The honest accepted iteration: `signCore` returns the spec signature (round-trip data).
#guard signCore 5 1 3 7 40 = some (7, 45, 0)
-- ROUND-TRIP: the accepted `signCore` output VERIFIES under the extracted `verifyCore` (thi = 5+1−3 = 3).
#guard verifyCore (5 + 1 - 3) 7 ((signCore 5 1 3 7 40).getD (0, 0, 0))
-- A REJECTED sample is honest `none` (retry): mask `y = 261888` makes `(y+γ₂) % α = 0 < β` — `lowGap` fails.
#guard signCore 5 1 3 7 261888 = none
-- …and an out-of-norm response (`‖z‖ = y+s₁ ≥ γ₁−β`) also rejects — the `zBound` gate is real.
#guard signCore 5 1 3 7 1000000 = none
/-! ### The SIGN entry — the honest resample and an unreadable wire are now DIFFERENT answers.

⚑ MEASURED, NOT PREDICTED. The accepted-signature reply carries a `"1 "` tag it did not carry before
2026-08-07 (`"1 7 45 0"`, not `"7 45 0"`), and the honest rejection-sampling abort is `"0"`, not
`"REJECT"`. A caller that spins the Dilithium resample loop on `"0"` will now spin forever ONLY on a
genuine gate refusal; a wire it cannot get read comes back `"2 <fault>"` and must stop. -/

/-- An accepted iteration emits the TAGGED signature wire. -/
theorem signFFI_signs_honest : signFFI "5 1 3 7 40" = "1 7 45 0" := by native_decide
/-- A gate-refused sample is the honest resample answer `"0"`. -/
theorem signFFI_resamples : signFFI "5 1 3 7 261888" = "0" := by native_decide
/-- One unreadable token: `scalarToken`. -/
theorem signFFI_garbage_is_malformed : signFFI "garbage" = "2 1" := by native_decide
/-- One token short / one token long: `scalarArity`. -/
theorem signFFI_short_wire_is_malformed : signFFI "5 1 3 7" = "2 0" := by native_decide
theorem signFFI_long_wire_is_malformed : signFFI "5 1 3 7 40 9" = "2 0" := by native_decide

/-- **THE SIGN COLLISION IS GONE.** The honest resample is `"0"`; three unreadable wires are not.
Before the retag all four were the same five bytes, `"REJECT"`. -/
theorem signFFI_resample_is_distinguishable_from_a_malformed_wire :
    signFFI "5 1 3 7 261888" = "0"
      ∧ signFFI "garbage" ≠ "0"
      ∧ signFFI "5 1 3 7" ≠ "0"
      ∧ signFFI "5 1 3 7 40 9" ≠ "0" := by native_decide

/-- **END-TO-END ON THE WIRE, THROUGH THE TAG.** `signFFI`'s accepted reply, with its `"1 "` tag
dropped and the `thi μ` prefix attached, VERIFIES through `verifyFFI`. This is the composition the
pre-retag tooth performed by raw concatenation; it is written through `String.drop 2` so the tag
change is VISIBLE here rather than silently making the composition a six-token malformed wire. -/
theorem signFFI_then_verifyFFI_round_trips :
    verifyFFI ("3 7 " ++ (signFFI "5 1 3 7 40").drop 2) = "1" := by native_decide
/-- A TAMPERED signature (bumped `c̃`) fails `verifyFFI` — the round-trip is a real gate. -/
theorem verifyFFI_rejects_tampered_roundtrip : verifyFFI "3 7 8 45 0" = "0" := by native_decide

#assert_axioms renderSign_ne_malformed
#assert_axioms signWire_eq_resampled_iff
#assert_axioms signWire_malformed_iff

#assert_compiled signFFI_signs_honest
#assert_compiled signFFI_resamples
#assert_compiled signFFI_garbage_is_malformed
#assert_compiled signFFI_short_wire_is_malformed
#assert_compiled signFFI_long_wire_is_malformed
#assert_compiled signFFI_resample_is_distinguishable_from_a_malformed_wire
#assert_compiled signFFI_then_verifyFFI_round_trips
#assert_compiled verifyFFI_rejects_tampered_roundtrip

#assert_axioms signCore_eq_spec
#assert_axioms signCore_verifies
#assert_axioms signExtractedApi_fips204
#assert_axioms signExtractedApi_correct

/-! ## PART 6 — the REAL, FULL-BYTE ML-DSA-65 verify over the wire (BRICK 8: the crate leaves the TCB).

PARTS 1–5 extract the verify/sign at the `n=1`, `A=id` SCALAR reduction of the FIPS 204 equations — the
object `Fips204Correct` reasons about, but over a 5-integer toy wire. `Dregg2.Crypto.MlDsaVerifyReal`
(BRICK 6) is the FULL-DIMENSION verify — the `n=256` negacyclic ring, `NTT`, `SampleInBall`/`ExpandA` over
`SHAKE`, and the real 1952/3309-byte `pkDecode`/`sigDecode` — PROVED (`native_decide`) to ACCEPT a genuine
`fips204` v0.4.6 crate signature and REJECT a one-byte tamper / wrong message (`verify_accepts_real`,
`verify_rejects_tampered`, `verify_rejects_wrong_msg`). This part `@[export]`s THAT verify over a byte wire,
so the DEPLOYED `dregg-pq::ml_dsa_verify` — over the actual `pk ‖ msg ‖ ctx ‖ sig` bytes — runs the
Lean-verified `MlDsaVerifyReal.verifyCore` as leanc-native code, and the `fips204` crate genuinely leaves
the verify TCB.

The wire reuses the SAME `String → String` ABI as `verifyFFI`/`signFFI` (so the existing C string bridge +
`leanc` link carry it unchanged): four SPACE-separated lowercase-hex fields `hex(pk) hex(msg) hex(ctx)
hex(sig)`. An empty field (e.g. `ctx = ε`) is the empty token between two spaces. Fail-CLOSED (`"0"`) on any
malformed wire: not exactly four fields, an odd-length field, or a non-hex character. -/

/-! The hex codec is `Dregg2.Crypto.AcvpHex` — ONE implementation for every byte wire that crosses
the `@[export]` boundary (see that module). The verbatim copy that used to sit here is gone; the
shared decoder carries a proved `@[csimp]` tail-recursive implementation, so a long field decodes in
constant stack instead of aborting the process. Same fail-closed contract, same bytes — the
`native_decide` teeth below re-check it. -/
export Dregg2.Crypto.AcvpHex (hexNibble? decodeHexChars toHexDigit hexEncode)

/-- The real byte wire `hex(pk) hex(msg) hex(ctx) hex(sig)` the FFI reads. -/
def realWire (pk M ctx sig : List UInt8) : String :=
  hexEncode pk ++ " " ++ hexEncode M ++ " " ++ hexEncode ctx ++ " " ++ hexEncode sig

/-- **Strict** parse of the four-field byte wire `hex(pk) hex(msg) hex(ctx) hex(sig)`, reporting the
STAGE that refused it. An EMPTY field is legal (`ctx = ε` is the empty token between two spaces) and
decodes to the empty byte list; a field that is odd-length or carries a non-hex character is
[`FWireFault.byteFieldHex`], and any field count other than four is [`FWireFault.byteFieldArity`]. -/
def parseByteE (input : String) :
    Except FWireFault (List UInt8 × List UInt8 × List UInt8 × List UInt8) :=
  match input.splitOn " " with
  | [pkH, msgH, ctxH, sigH] =>
    match decodeHexChars pkH.toList, decodeHexChars msgH.toList,
          decodeHexChars ctxH.toList, decodeHexChars sigH.toList with
    | some pk, some m, some ctx, some sig => .ok (pk, m, ctx, sig)
    | _, _, _, _ => .error .byteFieldHex
  | _ => .error .byteFieldArity

/-- The whole String → verify-outcome decision for the REAL byte wire. -/
def verifyRealOutcome (input : String) : FWireOutcome :=
  match parseByteE input with
  | .error f => .malformed f
  | .ok (pk, m, ctx, sig) =>
      .verdict (if MlDsaVerifyReal.verifyCore pk m ctx sig then .accept else .reject)

/-- The whole String → String decision for the REAL byte wire. -/
def verifyRealWire (input : String) : String := renderOutcome (verifyRealOutcome input)

/-- **FFI entry** (Rust→Lean) for the REAL, FULL-BYTE ML-DSA-65 verify (BRICK 8): parse the four hex fields
`hex(pk) hex(msg) hex(ctx) hex(sig)`, run the Lean-verified `MlDsaVerifyReal.verifyCore` over the decoded
bytes, and return `"1"` (accept) / `"0"` (reject). This runs the FULL-DIMENSION verify (not the `A=id` toy)
as native code — the security-critical accept/reject of a REAL 1952-byte key + 3309-byte signature.

⚑ A wire this parser cannot READ renders `"2 <fault>"`, NOT `"0"`. Until 2026-08-07 it rendered `"0"`,
so `dregg_pq::ml_dsa_verify`'s `reply == "1"` turned "this binary and the linked Lean archive disagree
about the byte wire" into "this signature is forged" — a true refusal wearing a false diagnosis, on
the ~10 surfaces that gate on ML-DSA verify. -/
@[export dregg_fips204_verify_real]
def verifyRealFFI (input : String) : String := verifyRealWire input

/-- **BOTH POLES, ON THE REAL BYTE WIRE.** `verifyRealWire s = "0"` iff the four hex fields decoded
AND the full-dimension `MlDsaVerifyReal.verifyCore` said `false`. This is the pole every
tampered-signature test on the deployed verify was asserting; before the split it was satisfied by a
wire nothing parsed. -/
theorem verifyRealWire_eq_reject_iff (s : String) :
    verifyRealWire s = "0" ↔
      ∃ pk m ctx sig, parseByteE s = .ok (pk, m, ctx, sig) ∧
        MlDsaVerifyReal.verifyCore pk m ctx sig = false := by
  unfold verifyRealWire verifyRealOutcome
  cases hp : parseByteE s with
  | error f =>
      simp only [renderOutcome]
      constructor
      · intro h
        exact absurd (renderOutcome_malformed_length f)
          (by rw [show renderOutcome (FWireOutcome.malformed f) = "0" from h]; decide)
      · rintro ⟨_, _, _, _, hok, -⟩; exact absurd hok (by simp)
  | ok p =>
      obtain ⟨pk, m, ctx, sig⟩ := p
      simp only [renderOutcome]
      constructor
      · intro hq
        refine ⟨pk, m, ctx, sig, rfl, ?_⟩
        by_cases hv : MlDsaVerifyReal.verifyCore pk m ctx sig = true
        · simp only [hv, if_true] at hq; exact absurd hq (by decide)
        · simpa using hv
      · rintro ⟨pk', m', ctx', sig', hok, hv⟩
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hok
        simp [hv, renderVerdict]

/-- **THE OTHER POLE, ON THE REAL BYTE WIRE.** A `"2 <f>"` reply is reachable ONLY from a parse
failure, so it is PROOF that the full-dimension verifier never ran over anybody's bytes. -/
theorem verifyRealWire_malformed_iff (s : String) (f : FWireFault) :
    verifyRealWire s = renderOutcome (.malformed f) ↔ parseByteE s = .error f := by
  unfold verifyRealWire verifyRealOutcome
  cases hp : parseByteE s with
  | error g =>
      simp only []
      constructor
      · intro h
        have hgf : g = f := by
          cases g <;> cases f <;> first
            | rfl
            | (exfalso; exact absurd h (by decide))
        simp [hgf]
      · intro h; simp only [Except.error.injEq] at h; subst h; rfl
  | ok p =>
      obtain ⟨pk, m, ctx, sig⟩ := p
      simp only [renderOutcome]
      constructor
      · intro hq
        split at hq
        · exact absurd hq (renderVerdict_ne_malformed .accept f)
        · exact absurd hq (renderVerdict_ne_malformed .reject f)
      · intro hq; exact absurd hq (by simp)

/-! ### Teeth — the byte-wire verify is NON-VACUOUS: the REAL crate signature ACCEPTS, tampers REJECT.

`MlDsaVerifyReal.gen{Pk,Sig,SigTampered}` are a genuine `fips204` v0.4.6 keypair+signature over
`genMsg = "dregg real verify KAT"`, `ctx = ε`. These drive the WHOLE wire path (hex encode → split → hex
decode → `verifyCore`) at build time with `native_decide` on the compiled `def`s: the honest signature
ACCEPTS, a one-byte tamper and a wrong message REJECT. -/

theorem verifyRealFFI_accepts_real :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList MlDsaVerifyReal.genMsg []
      MlDsaVerifyReal.genSig.toList) = "1" := by
  native_decide

theorem verifyRealFFI_rejects_tampered :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList MlDsaVerifyReal.genMsg []
      MlDsaVerifyReal.genSigTampered.toList) = "0" := by
  native_decide

theorem verifyRealFFI_rejects_wrong_msg :
    verifyRealFFI (realWire MlDsaVerifyReal.genPk.toList (MlDsaVerifyReal.genMsg ++ [0]) []
      MlDsaVerifyReal.genSig.toList) = "0" := by
  native_decide

/-! ### The REAL byte wire — a wire the hex codec cannot read is `"2 <fault>"`, not `"0"`.

⚑ MEASURED, NOT PREDICTED. All three refuse at the PARSE, so `MlDsaVerifyReal.verifyCore` never runs
and they are cheap — but they are `native_decide`, not `decide`, and `#assert_compiled` says so.
Read them against the three theorems above: THOSE are the accept/reject poles over a genuine
1952/3309-byte `fips204` keypair, and it is precisely their `"0"` that a malformed wire used to
counterfeit. -/

/-- Non-hex characters in every field: `byteFieldHex`. -/
theorem verifyRealFFI_non_hex_is_malformed : verifyRealFFI "zz zz zz zz" = "2 3" := by native_decide
/-- Two fields instead of four: `byteFieldArity`. -/
theorem verifyRealFFI_field_count_is_malformed : verifyRealFFI "00 00" = "2 2" := by native_decide
/-- Four fields, each an ODD number of hex digits: `byteFieldHex`. -/
theorem verifyRealFFI_odd_length_is_malformed : verifyRealFFI "0 0 0 0" = "2 3" := by native_decide

/-- **THE REAL-WIRE COLLISION IS GONE.** `verifyRealFFI_rejects_tampered` renders `"0"`; none of the
three unreadable wires does. This is the pair that matters most in the repo: `"0"` on this wire is
what `dregg_pq::ml_dsa_verify` turns into "this signature is invalid" on ~10 surfaces, and until
2026-08-07 a hex-codec or field-count disagreement between `dregg-pq`'s `real_verify_wire` and this
parser produced exactly that string. -/
theorem verifyRealFFI_reject_is_distinguishable_from_a_malformed_wire :
    verifyRealFFI "zz zz zz zz" ≠ "0"
      ∧ verifyRealFFI "00 00" ≠ "0"
      ∧ verifyRealFFI "0 0 0 0" ≠ "0" := by native_decide

#assert_axioms verifyRealWire_eq_reject_iff
#assert_axioms verifyRealWire_malformed_iff

#assert_compiled verifyRealFFI_accepts_real
#assert_compiled verifyRealFFI_rejects_tampered
#assert_compiled verifyRealFFI_rejects_wrong_msg
#assert_compiled verifyRealFFI_non_hex_is_malformed
#assert_compiled verifyRealFFI_field_count_is_malformed
#assert_compiled verifyRealFFI_odd_length_is_malformed
#assert_compiled verifyRealFFI_reject_is_distinguishable_from_a_malformed_wire

end Dregg2.Crypto.Fips204Verify
