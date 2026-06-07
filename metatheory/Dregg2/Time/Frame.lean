/-
# Dregg2.Time.Frame — `frame_within`: the FRAME-CONVENTION deadline (attested, honest §8 trust).

The relativistic time-typing's *other* face (`docs/rebuild/INTENT-AS-CO-RECEIPT.md` §4,
`docs/rebuild/INTENT-REFS-time.md` ref #4 Spanner/TrueTime, ref #5 Lamport–Melliar-Smith): a
wall-clock deadline is NOT a lightcone fact — it is a **chosen reference frame**. A "time authority"
`F` (a fault-tolerant clock-sync quorum, Lamport–Melliar-Smith 1985) attests a frame-time `t`, valid
only **within a skew bound `±δ`** (TrueTime's `ε`: time is an interval `[earliest, latest]`, never a
point — "carry δ explicitly, never assume it 0").

This is built as a `Temporal` **`WitnessedPredicate`** over the EXISTING machinery:
  * the predicate registry `Authority.Predicate` (the `temporal` `WitnessedKind` already exists);
  * the credential issuer `Authority.Credential` (issuer + `attestation : Proof` + revocation);
  * `registry_sound` / `crypto_kind_routes_to_oracle` give soundness-by-verification FOR FREE.

  `FrameWithin reg F T δ att  :=  the registry's `temporal` verifier ACCEPTS F's attestation `att`
                                  of frame-time ≥ T within skew δ`

The CRITICAL discipline, exactly as §4 demands:
  * `δ` is a FIRST-CLASS field, threaded through the statement; the model NEVER collapses the
    interval to `δ = 0`. (`ThirdPartyDischarge.lean`'s `MAX_DISCHARGE_AGE = 300` was a `frame_within`
    MISSING its declared `δ` + frame; THIS is its honest retyping — the authority is named and the
    skew is explicit.)
  * the SOUNDNESS of the attestation — "the authority is honest within `f` faults; `|t − true_time|
    ≤ δ` physically; signatures are unforgeable" — is an EXPLICIT §8 CARRIER hypothesis
    (`FrameHonesty`), NEVER baked in as a def returning `True` and NEVER a Lean theorem. We prove the
    *protocol's acceptance discipline* + the *bridge from accept to a bounded-time fact GIVEN the
    carrier*; we do not, and cannot, prove the clocks are honest.

§8 portal (refs #5, #6): the time-authority is honest (≤ `f` of the clock quorum Byzantine), the skew
`δ` physically bounds the real drift, and signatures are unforgeable. Carried as `FrameHonesty`,
taken as a hypothesis at every point a *physical-time* conclusion is drawn. Acceptance itself (a bit
the in-TCB verifier emits) needs no honesty; only the leap from "accepted" to "real time is bounded"
does — and that leap is gated on the carrier.

Pure, computable, `#eval`-able.
-/
import Dregg2.Authority.Predicate
import Dregg2.Authority.Credential
import Mathlib.Tactic.Linarith   -- `linarith` (was transitive via CryptoKernel's `Mathlib.Tactic`,
                                  -- now imported explicitly after the FFI-closure import trim)

namespace Dregg2.Time.Frame

open Dregg2.Authority.Predicate
open Dregg2.Authority.Credential
open Dregg2.Crypto (CryptoKernel)

/-! ## 1. Time and the time authority. -/

/-- **`Time`** — wall-clock seconds since an epoch (`Int`, matching `ThirdPartyDischarge.Time`). NOT a
causal coordinate: a reading in some authority's chosen frame, meaningful only within its skew `±δ`. -/
abbrev Time := Int

/-- **`TimeAuthority`** — a chosen reference frame, identified by its issuer code (a DID / public-key
code, the `VC.issuer` field). Physically a fault-tolerant clock-sync QUORUM (Lamport–Melliar-Smith
CNV/COM), not a single oracle: its attestations carry a *proven worst-case skew* `δ` — GIVEN ≤ `f` of
the quorum are honest (the §8 carrier). Here a `Nat` code; the quorum substance lives in §8. -/
structure TimeAuthority where
  /-- The authority's issuer identifier (matches `Credential.VC.issuer`). -/
  issuer : Nat
  deriving DecidableEq, Repr

/-! ## 2. The frame-time STATEMENT — `δ` threaded EXPLICITLY (never collapsed to 0).

A `frame_within` claim is the statement the authority's attestation must discharge. It content-
addresses `(authority, T, δ)`: WHO attested, the lower-bound frame-time `T` ("the frame-clock has
reached at least `T`"), and the EXPLICIT skew `δ`. The `δ` field is the whole point — drop it and you
are back to the global-now fiction `expiry: u64`. -/

/-- **`FrameStatement`** — the statement a `frame_within` attestation discharges: authority `F`
attests its frame-clock has reached `T`, within skew `δ`. TrueTime's `TT.after(T)` with the interval
half-width `δ = ε` carried as a first-class field — the model knows it does not know the exact
instant. -/
structure FrameStatement where
  /-- The attesting reference frame. -/
  authority : TimeAuthority
  /-- The lower-bound frame-time claimed ("the clock has reached at least `T`"). -/
  T : Time
  /-- The EXPLICIT skew bound `±δ` (TrueTime's `ε`). NEVER assumed 0. -/
  δ : Time
  deriving Repr

/-- A `FrameStatement` is non-degenerate when its skew is a real, positive interval (`δ > 0`): the
authority genuinely *does not* claim point-precision. We keep `δ` general (an `Int` field) but expose
this predicate so non-vacuity can insist the carried skew is real. -/
def FrameStatement.skewReal (fs : FrameStatement) : Prop := 0 < fs.δ

/-! ## 3. `FrameWithin` — the attested predicate (built on the registry's `temporal` kind).

A `frame_within` deadline is DISCHARGED iff the predicate registry's `temporal` verifier accepts the
authority's reading `att` for the statement `fs`. This reuses `registryVerify` at kind `.temporal`:
the in-TCB dispatch routes to the authority's clock-sync verifier, whose accept bit is the
soundness-by-verification seam (`registry_sound`). The prover (the authority's `find`/reading
producer) stays untrusted — only the gate decides. -/

section Abstract
variable {Stmt Wit : Type}

/-- **`FrameWithin reg fs att` — `frame_within(F, T, ±δ)`.** The registry's `temporal` verifier
ACCEPTS the authority's attested reading `att` for the frame-statement `fs = (F, T, δ)`. A FRAME
CONVENTION: discharged by a verified attestation from `F`, carrying `δ` explicitly, NEVER true for
free. (`Stmt`/`Wit` are abstract — for the §8 crypto route they are `Digest`/`Proof` and the verifier
is `CryptoKernel.verify`; for the toy demo they are concrete codes.)

`stmtOf` projects the `FrameStatement` into the registry's statement type — the content-addressed
encoding the authority signs over (WHO, `T`, `δ`). -/
def FrameWithin (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt)
    (fs : FrameStatement) (att : Wit) : Prop :=
  registryVerify reg .temporal (stmtOf fs) att = true

/-- `FrameWithin` is exactly the registry's `temporal` accept bit (defining equation). -/
@[simp] theorem frameWithin_iff_accept (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt)
    (fs : FrameStatement) (att : Wit) :
    FrameWithin reg stmtOf fs att ↔ registryVerify reg .temporal (stmtOf fs) att = true :=
  Iff.rfl

/-! ## 4. SOUNDNESS-BY-VERIFICATION — an accepted attestation DISCHARGES the framed predicate.

This is the provable half, inherited verbatim from `Predicate.registry_sound`: if the `temporal`
verifier accepts, the framed predicate is discharged through `Laws.Discharged` at the registry-at-
`temporal` seam instance. The TCB is the registry's `Verify`; NOTHING about the (untrusted) reading
producer enters. NO honesty hypothesis is needed for *acceptance* — only for the physical-time leap
(§6 below). -/

/-- **`frameWithin_sound` (PROVED) — soundness-by-verification.** An accepted `temporal` attestation
discharges the framed predicate at the registry seam. Reuses `registry_sound`; the prover never
enters. (The leap from "discharged" to "real time ≥ T − δ" is §6, gated on the §8 carrier.) -/
theorem frameWithin_sound (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt)
    (fs : FrameStatement) (att : Wit)
    (h : FrameWithin reg stmtOf fs att) :
    @Dregg2.Laws.Discharged Stmt Wit (verifiableOfRegistry reg .temporal) (stmtOf fs) att :=
  registry_sound reg .temporal (stmtOf fs) att h

/-- **`frame_adversarial_cannot_forge` (PROVED) — the gate is the sole authority.** If the installed
`temporal` verifier REJECTS a reading, NO producer (however adversarial) can make `FrameWithin` hold
with it: acceptance has no prover-controlled path. Reuses `adversarial_find_cannot_forge`. So a frame
deadline cannot be forged by a lying clock-reading — it must pass the in-TCB verifier. -/
theorem frame_adversarial_cannot_forge (reg : Registry Stmt Wit) (v : Verifier Stmt Wit)
    (hreg : reg .temporal = some v) (fs : FrameStatement) (stmtOf : FrameStatement → Stmt)
    (att : Wit) (hreject : v (stmtOf fs) att = false) :
    ∀ (find : Stmt → Option Wit), find (stmtOf fs) = some att →
      ¬ FrameWithin reg stmtOf fs att := by
  intro find hfound
  have := adversarial_find_cannot_forge reg .temporal v hreg (stmtOf fs) att hreject find hfound
  unfold FrameWithin
  rw [this]
  simp

/-! ## 5. NON-VACUITY of the predicate ITSELF — undecided without the attestation, true WITH it.

The teeth §4 demands: a `frame_within` is NOT true-for-free. WITHOUT a registered verifier the kind
fails closed (`registryVerify … = false` — "no frame authority, no frame fact"); WITHOUT an accepting
attestation it is false; only WITH the authority's accepting reading does it hold. (Contrast the
causal face, which holds with no authority at all — that gap IS the load-bearing distinction.) -/

/-- **`frameWithin_false_without_authority` (PROVED) — no authority, no frame fact.** If the registry
has NO `temporal` verifier installed (`reg .temporal = none`), then `FrameWithin` is FALSE for every
attestation — the frame predicate is genuinely undecided/unmet without a named time authority. This
is the structural contrast to `Causal.CausalAfter`, which needs no authority. -/
theorem frameWithin_false_without_authority (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt)
    (hnone : reg .temporal = none) (fs : FrameStatement) (att : Wit) :
    ¬ FrameWithin reg stmtOf fs att := by
  unfold FrameWithin registryVerify
  rw [hnone]
  simp

/-! ## 6. The honest §8 CARRIER — and the leap from "accepted" to a bounded physical-time FACT.

Acceptance is a bit the in-TCB verifier emits; it says nothing physical by itself. To conclude
anything about REAL time we need the §8 trust assumption — the authority is honest within `f` faults,
the skew `δ` physically bounds the drift, signatures are unforgeable. We carry this as an EXPLICIT
`Prop` hypothesis `FrameHonesty`, NEVER a def returning `True`, NEVER proved. The bridge theorem then
says: GIVEN the carrier, an accepted attestation entails the true frame-time lies within `[T − δ, …]`.
The carrier is load-bearing — drop it and no physical conclusion follows. -/

/-- **`FrameHonesty F fs trueTime` — the §8 CARRIER (`Prop`, asserted, never proved).** The honest-
clock trust assumption for authority `F` attesting statement `fs`, relative to the (unobservable)
real time `trueTime`:

  (a) ≤ `f` of `F`'s clock-sync quorum are Byzantine (Lamport–Melliar-Smith / Dolev–Halpern–Strong);
  (b) the skew `δ` PHYSICALLY bounds the reading: the true time is at least `T − δ` (the authority's
      reading is honest within its declared interval — TrueTime's `[earliest, latest]`);
  (c) signatures are unforgeable (the standing crypto seam).

We encode the *operative* content (b) — `T − δ ≤ trueTime` — as the carrier's payload, since that is
what a physical-time conclusion consumes; (a) and (c) are the *reasons* an honest impl satisfies it,
named in the doc, discharged by the protocol + circuits, NOT here. This is a genuine constraint on
`trueTime`, NOT `True`: an authority lying by more than `δ` (true time `< T − δ`) FALSIFIES it. -/
def FrameHonesty (fs : FrameStatement) (trueTime : Time) : Prop :=
  fs.T - fs.δ ≤ trueTime

/-- **`frameHonesty_nontrivial` (PROVED) — the carrier is REAL, not `True`.** For a statement with a
real reading there is a `trueTime` SATISFYING the carrier (an honest clock: `trueTime = T`) and a
`trueTime` FALSIFYING it (a clock lying beyond `δ`: `trueTime = T − δ − 1`). So `FrameHonesty`
genuinely constrains the world — it is a falsifiable §8 assumption, exactly like the BFT honest-
majority, never the trivial carrier. -/
theorem frameHonesty_nontrivial (fs : FrameStatement) (hδ : fs.skewReal) :
    FrameHonesty fs fs.T ∧ ¬ FrameHonesty fs (fs.T - fs.δ - 1) := by
  unfold FrameHonesty FrameStatement.skewReal at *
  constructor
  · linarith
  · intro h; linarith

/-- **`frame_accept_bounds_realtime` (PROVED) — the BRIDGE: accepted + honest ⟹ real time bounded.**
The keystone of the frame face. GIVEN the §8 carrier `FrameHonesty fs trueTime` (the authority's
declared skew physically holds), an ACCEPTED frame attestation entails the real time is at least
`T − δ`: the frame reading is a genuine lower bound on physical time within the skew. WITHOUT the
carrier this conclusion does NOT follow (acceptance is just a verifier bit). The accepted-ness
`hacc : FrameWithin …` documents that we only invoke the carrier on a *verified* attestation — the
in-TCB gate gates which attestations we trust the §8 assumption about. -/
theorem frame_accept_bounds_realtime (reg : Registry Stmt Wit) (stmtOf : FrameStatement → Stmt)
    (fs : FrameStatement) (att : Wit) (trueTime : Time)
    (_hacc : FrameWithin reg stmtOf fs att)
    (hhonest : FrameHonesty fs trueTime) :
    fs.T - fs.δ ≤ trueTime :=
  hhonest

end Abstract

/-! ## 7. Routing through the §8 crypto oracle — the authority's attestation IS a `verify`.

For a real time authority the `temporal` verifier is the `CryptoKernel.verify` oracle (the
attestation is a signed/proven clock reading). `crypto_kind_routes_to_oracle` gives soundness-by-
verification through the oracle for free; the binding/extractability of the signature stays §8. -/

/-- **`frameWithin_via_oracle` (PROVED) — the frame predicate routed through the §8 oracle.** When
the `temporal` kind is registered with `CryptoKernel.verify` and the oracle accepts the authority's
signed reading, the framed predicate is discharged. No Lean reasoning into the crypto occurs — the
signature's unforgeability is the §8 carrier, not a theorem. Reuses `crypto_kind_routes_to_oracle`. -/
theorem frameWithin_via_oracle {Digest Proof : Type} [AddCommGroup Digest] [CryptoKernel Digest Proof]
    (base : Registry Digest Proof) (stmt : Digest) (proof : Proof)
    (horacle : CryptoKernel.verify stmt proof = true) :
    let reg : Registry Digest Proof :=
      fun j => if j = .temporal then some cryptoVerifier else base j
    @Dregg2.Laws.Discharged Digest Proof (verifiableOfRegistry reg .temporal) stmt proof := by
  exact crypto_kind_routes_to_oracle base .temporal stmt proof horacle

/-! ## 8. The retyping of `MAX_DISCHARGE_AGE` — the sharpest "before/after §4" example.

`ThirdPartyDischarge.lean` gates freshness on `0 ≤ now − created_at ≤ 300` — a BARE wall-clock check,
a `frame_within` MISSING its declared `δ` and frame. Here it is retyped honestly: the `300`-second
window IS a `FrameStatement` with the skew `δ = 300` carried EXPLICITLY and the verifying party named
as a `TimeAuthority`. The freshness bit becomes "the time authority attests `now` lies within `δ` of
`created_at`" — the skew is no longer a magic constant but the authority's declared interval. -/

/-- The `MAX_DISCHARGE_AGE` skew, now a FIRST-CLASS field (was the bare constant `300`). -/
def maxDischargeSkew : Time := 300

/-- **`dischargeFreshnessAsFrame F createdAt`** — the honest retyping of the discharge freshness
check: a `FrameStatement` for authority `F` attesting frame-time `createdAt` within the EXPLICIT skew
`δ = maxDischargeSkew` (300s). The `300` is no longer a magic constant buried in a `≤`; it is the
authority's *declared interval half-width*, exposed as `fs.δ`. -/
def dischargeFreshnessAsFrame (F : TimeAuthority) (createdAt : Time) : FrameStatement :=
  { authority := F, T := createdAt, δ := maxDischargeSkew }

/-- **`discharge_skew_is_explicit` (PROVED)** — the retyped freshness check carries its skew openly:
`(dischargeFreshnessAsFrame F t).δ = 300`, a real positive interval (`skewReal`). The `before` had no
`δ` field at all; the `after` exposes it — which is the entire content of §4's discipline on the
sharpest example in the codebase. -/
theorem discharge_skew_is_explicit (F : TimeAuthority) (createdAt : Time) :
    (dischargeFreshnessAsFrame F createdAt).δ = 300 ∧
      (dischargeFreshnessAsFrame F createdAt).skewReal := by
  refine ⟨rfl, ?_⟩
  show (0 : Time) < (dischargeFreshnessAsFrame F createdAt).δ
  show (0 : Time) < (300 : Time)
  norm_num

/-! ## 9. `#eval` demo — a concrete `temporal` registry: accept discharges, no-authority fails.

A toy `temporal` verifier accepting an authority's reading iff the reading echoes the content-
addressed statement (the Reference-kernel discipline). Exercises: WITH the verifier an attestation is
accepted (frame fact holds); WITHOUT it (fails-closed kind) the frame predicate is false. -/

namespace Demo

/-- Statement type = a content-addressed `Nat` code of `(issuer, T, δ)`. -/
abbrev Stmt := Nat
/-- Witness type = the authority's claimed reading `Nat` (echoes the statement when honest). -/
abbrev Wit := Nat

/-- Encode a `FrameStatement` to its content-addressed code (`issuer, T, δ` paired). The `δ` is part
of the address — a different declared skew is a DIFFERENT statement (the authority signs over `δ`). -/
def encodeStmt (fs : FrameStatement) : Stmt :=
  Nat.pair fs.authority.issuer (Nat.pair fs.T.toNat fs.δ.toNat)

/-- A toy `temporal` verifier: accepts iff the reading echoes the statement code (the honest
authority's signed reading IS the statement; a forged reading is anything else). -/
def temporalVerifier : Verifier Stmt Wit := fun stmt wit => decide (wit = stmt)

/-- A registry WITH the `temporal` authority installed. -/
def regWithAuthority : Registry Stmt Wit := fun
  | .temporal => some temporalVerifier
  | _         => none

/-- A registry WITHOUT any `temporal` authority (fails closed — "no frame, no frame fact"). -/
def regNoAuthority : Registry Stmt Wit := fun _ => none

/-- The reference time authority (issuer 99). -/
def F : TimeAuthority := { issuer := 99 }

/-- A frame claim: authority `F` attests frame-time `T = 1000` within skew `δ = 5`. -/
def fs : FrameStatement := { authority := F, T := 1000, δ := 5 }

/-- The honest attestation: the reading that echoes the statement code (what `F` signs). -/
def honestAtt : Wit := encodeStmt fs

-- WITH the authority + honest attestation ⇒ the frame predicate is ACCEPTED (holds).
#guard (registryVerify regWithAuthority .temporal (encodeStmt fs) honestAtt)      -- true
-- A FORGED reading (off by one) ⇒ REJECTED even with the authority present.
#guard (registryVerify regWithAuthority .temporal (encodeStmt fs) (honestAtt + 1) == false) -- false
-- WITHOUT any time authority ⇒ FALSE for the honest attestation too ("no frame, no fact").
#guard (registryVerify regNoAuthority .temporal (encodeStmt fs) honestAtt == false)        -- false
-- The skew δ is carried explicitly in the statement (not assumed 0).
#guard (decide (fs.δ = 5 ∧ 0 < fs.δ))                                              -- true

/-- The honest run discharges (soundness-by-verification): the accepted attestation is `Discharged`. -/
theorem demo_frameWithin_holds : FrameWithin regWithAuthority encodeStmt fs honestAtt := by
  unfold FrameWithin registryVerify regWithAuthority temporalVerifier honestAtt
  simp

/-- WITHOUT the authority the SAME honest attestation does NOT discharge (the teeth: not free). -/
theorem demo_frameWithin_fails_no_authority :
    ¬ FrameWithin regNoAuthority encodeStmt fs honestAtt :=
  frameWithin_false_without_authority regNoAuthority encodeStmt rfl fs honestAtt

end Demo

/-! ### Keystones — `#assert_axioms`-clean. -/

#assert_axioms frameWithin_sound
#assert_axioms frame_adversarial_cannot_forge
#assert_axioms frameWithin_false_without_authority
#assert_axioms frameHonesty_nontrivial
#assert_axioms frame_accept_bounds_realtime
#assert_axioms frameWithin_via_oracle
#assert_axioms discharge_skew_is_explicit
#assert_axioms Demo.demo_frameWithin_holds
#assert_axioms Demo.demo_frameWithin_fails_no_authority

end Dregg2.Time.Frame
