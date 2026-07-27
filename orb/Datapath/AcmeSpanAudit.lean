import Datapath.ServeConformantDense
import Datapath.ServeConformantFused
import Datapath.ServeZc

/-!
# Datapath.AcmeSpanAudit — every span that claims to be a deployed serve must serve HTTP-01

`Reactor.ServeConformant.conformantServe` carries the ACME HTTP-01 challenge route
(`acmeChallengeBytes`, RFC 8555 §8.3): a `GET /.well-known/acme-challenge/<token>`
is answered with the key authorization the validating CA recomputes, and never
reaches the inner serve. Certificate ISSUANCE AND RENEWAL depend on that arm
firing on whatever serve the process is actually running.

The `DRORB_SPAN` A/B switch (`crates/dataplane/src/serve.rs`) lets an operator
divert EVERY HTTP serve job to one of 24 alternative serve entry points. That is
a real hazard: a span whose control flow was written before the challenge route
landed silently drops it, and the only symptom is expired certificates weeks
later. That failure has already happened once — `conformantServeFast`
(`DRORB_SPAN=22`) was written before the arm existed, and because its module was
outside every Lake target the divergence went unbuilt and unnoticed until the
lakefile globs brought it under CI.

This module makes "does this serve answer the challenge?" a NAMED PROPERTY with
machine-checked proofs, so the next such drift is a build failure rather than a
renewal outage:

* `ServesAcme` — the obligation: on every input the challenge route claims, the
  serve returns exactly the challenge bytes.
* `conformantServe_servesAcme` — the wrapper discharges it for ANY inner, so the
  whole `conformantServe`-family (`DRORB_SPAN=19/20`, the deployed non-metered
  default `drorb_serve_conformant_head_idx`, and every metered conformant twin)
  inherits it.
* `conformantServeFast_servesAcme` / `serveConformantFastIdx_servesAcme` — the
  FUSED twin (`DRORB_SPAN=22`) discharges it too, THROUGH the byte-identity
  `conformantServeFast_eq`. This is the theorem whose failure was the `=22` bug:
  drop the arm from `conformantServeFast` again and this breaks the build.
* `conformantServe_acme_ca_accepted` — the end-to-end statement: the bytes the
  span serves on a challenge fetch are the serialization of a response whose body
  is the ONE value the CA accepts (`Pki.Acme.keyAuthorization_correct` over the
  REAL `Crypto.sha256`), and never the bare token.

## What this module does NOT claim

`ServesAcme` is proven only for the spans that carry the conformance wrapper.
The BARE-INNER spans (`DRORB_SPAN=3/4/7/18/21/24`) are proven byte-identical to
`Dataplane.drorbServe`, which has NO challenge arm — the arm lives in the
wrapper by design. They are inner-serve A/B probes, NOT deployable serves, and
selecting one loses HTTP-01 (and the `Date` finisher, and the whole RFC gate).
`conformantServe_inner_off_acme` states the design fact that makes that so: the
inner serve is consulted only OFF the challenge route. The measurement exemplars
(`=1/2/5/6/8..17`) do not route at all. See `docs/gateway/ACME-SPAN-AUDIT.md`.
-/

namespace Datapath.AcmeSpanAudit

open Proto (Bytes Request)
open Reactor (Response serialize)
open Reactor.ServeConformant (conformantServe acmeChallengeBytes addDate reqBytes
  isHeadReq respBytesRawBA scrubCorrBA stripBodyBA)
open Reactor.Stage.RequestHeadLimit (headGate)
open Datapath.ServeConformantFast (conformantServeFast)
open Reactor.Stage.AcmeChallenge (challengeResponse challengeResp tokenOf
  deployAcctKey getBytes acmePrefix challenge_fires challenge_body_ca_accepted)
open Pki.Acme (asciiBytes Http01Authz)

/-! ## 1. The obligation -/

/-- **A serve SERVES ACME HTTP-01** when, on every input the deployed challenge
route claims (`acmeChallengeBytes input = some out`, past the Z1 head gate), it
emits exactly those bytes. This is the property certificate renewal depends on:
the validating CA fetches `/.well-known/acme-challenge/<token>` and accepts the
authorization iff the body is the key authorization those bytes carry. -/
def ServesAcme (serve : ByteArray → ByteArray) : Prop :=
  ∀ (input : ByteArray) (out : Bytes),
    headGate input = none →
    acmeChallengeBytes input = some out →
    serve input = ByteArray.mk out.toArray

/-! ## 2. The conformance wrapper discharges it — for ANY inner -/

/-- **The wrapper serves the challenge, for every inner serve.** Past the Z1 head
gate the challenge route is consulted OUTERMOST, so whatever inner the span is
carrying (deployed `List`, dense, index-native head) the served bytes on a
challenge fetch are the route's bytes. Every `conformantServe`-family span
inherits this: `DRORB_SPAN=19` (`conformantServe drorbServe`), `=20`
(`conformantServe serveDenseIdx`), and the deployed non-metered default
`drorb_serve_conformant_head_idx` (`conformantServe serveHeadIdx`). -/
theorem conformantServe_servesAcme (inner : ByteArray → ByteArray) :
    ServesAcme (conformantServe inner) := by
  intro input out hg ha
  unfold conformantServe
  rw [hg, ha]

/-- **`DRORB_SPAN=20`** — the conformant-dense span serves the challenge. -/
theorem serveConformantDenseIdx_servesAcme :
    ServesAcme Datapath.ServeConformantDense.serveConformantDenseIdx :=
  conformantServe_servesAcme _

/-- **The deployed non-metered default** (`drorb_serve_conformant_head_idx`, the
`Seam::Http` arm in `crates/dataplane/src/serve.rs`) serves the challenge. Stated
here on its definiens `conformantServe serveHeadIdx` — `Dataplane.lean` defines
the export as exactly that, so the export inherits it definitionally. -/
theorem deployedDefault_servesAcme :
    ServesAcme (conformantServe Datapath.ServeHeadIdx.serveHeadIdx) :=
  conformantServe_servesAcme _

/-! ## 3. The FUSED twin discharges it too — through the byte-identity

This is the rung the `DRORB_SPAN=22` outage was missing. `conformantServeFast`
re-implements the wrapper's control flow with the post-processing fused into each
branch; nothing about that shape forces the challenge arm to be present. What
forces it is `conformantServeFast_eq` — the byte-identity to `conformantServe`
for EVERY input. Remove the arm from the fused twin and the identity is false, so
this theorem (and the build) fails. -/

/-- **The fused wrapper serves the challenge, for every inner serve** — through
`conformantServeFast_eq`. -/
theorem conformantServeFast_servesAcme (inner : ByteArray → ByteArray) :
    ServesAcme (conformantServeFast inner) := by
  intro input out hg ha
  rw [Datapath.ServeConformantFused.conformantServeFast_eq]
  exact conformantServe_servesAcme inner input out hg ha

/-- **`DRORB_SPAN=22`** — the fused conformant-dense span serves the challenge.
The span whose missing arm was the live ACME divergence. -/
theorem serveConformantFastIdx_servesAcme :
    ServesAcme Datapath.ServeConformantFast.serveConformantFastIdx :=
  conformantServeFast_servesAcme _

/-- **The fused head-idx serve** (`drorb_serve_conformant_fast_head_idx`, the
drop-in for the deployed non-metered default) serves the challenge. -/
theorem serveConformantFastHeadIdx_servesAcme :
    ServesAcme Datapath.ServeConformantFused.serveConformantFastHeadIdx :=
  conformantServeFast_servesAcme _

/-! ## 4. `DRORB_SPAN=23` — the tagged zero-copy split

`serveConformantZcIdx` returns a 1-byte-TAGGED payload, so it is not a
`ServesAcme` instance on the nose: the host strips the tag. The obligation lands
on the UNTAGGED bytes, and `Datapath.ServeZc.zcBulkHead_none_of_not_bulk` shows
the split arm cannot fire on a request whose line does not open `GET /bulk` — a
challenge fetch opens `GET /.well-known/`, so it always takes the `0x00` arm and
inherits `=22`'s answer. -/

/-- **`DRORB_SPAN=23`** — off the `/bulk` split arm the span emits the `0x00` tag
followed by exactly the challenge bytes, which is what the host serves after
stripping the tag (`serve_zc_into`). -/
theorem serveConformantZcIdx_servesAcme_off_bulk (input : ByteArray) (out : Bytes)
    (hb : List.isPrefixOf Datapath.ServeZc.bulkProbe input.toList = false)
    (hg : headGate input = none)
    (ha : acmeChallengeBytes input = some out) :
    Datapath.ServeZc.serveConformantZcIdx input
      = ByteArray.mk #[0] ++ ByteArray.mk out.toArray := by
  rw [Datapath.ServeZc.serveConformantZcIdx_eq_fast_of_not_bulk input hb,
    serveConformantFastIdx_servesAcme input out hg ha]

/-! ## 5. Non-vacuity — the hypotheses are the ordinary challenge fetch

`ServesAcme`'s hypotheses are not decoration: they hold of exactly the requests a
CA sends. `acmeChallengeBytes_fires` discharges the route hypothesis from the
PARSE (method `GET`, target under the well-known prefix) — no evaluation of the
account-key hash is needed to know the route fires. -/

/-- **The route fires on a parsed challenge fetch.** A request that parses with
method `GET` and a target under `/.well-known/acme-challenge/` drives
`acmeChallengeBytes` to the serialized challenge response — so `ServesAcme`'s
second hypothesis is discharged by the parse alone. -/
theorem acmeChallengeBytes_fires (input : ByteArray) (req : Request)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hm : req.method = getBytes)
    (hpre : acmePrefix.isPrefixOf req.target = true) :
    acmeChallengeBytes input
      = some (serialize (addDate (challengeResp (tokenOf req.target) deployAcctKey))) := by
  unfold acmeChallengeBytes
  rw [hp]
  show Option.map (fun r => serialize (addDate r)) (challengeResponse deployAcctKey req) = _
  rw [challenge_fires deployAcctKey req hm hpre]
  rfl

/-- **END TO END: what a conformant span puts on the wire for a CA.** For ANY
inner serve and ANY request that parses as a `GET` under the challenge prefix and
clears the Z1 head gate, the served bytes are the serialization of a `200` whose
body is a value `v` that

* the CA holding `deployAcctKey` ACCEPTS (`Http01Authz.validate = true`, and by
  `Pki.Acme.http01_validate_iff` that is the unique accepting value), and
* is NOT the bare token — the classic HTTP-01 responder bug is excluded.

Non-vacuous in both directions: the hypotheses are the ordinary CA fetch, and the
conclusion pins the bytes to the one CA-accepted string rather than to some
existential nobody can inhabit. -/
theorem conformantServe_acme_ca_accepted (inner : ByteArray → ByteArray)
    (input : ByteArray) (req : Request)
    (hg : headGate input = none)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hm : req.method = getBytes)
    (hpre : acmePrefix.isPrefixOf req.target = true) :
    ∃ v : List Char,
      conformantServe inner input
        = ByteArray.mk (serialize (addDate
            (challengeResp (tokenOf req.target) deployAcctKey))).toArray
      ∧ (challengeResp (tokenOf req.target) deployAcctKey).body = asciiBytes v
      ∧ Http01Authz.validate ⟨tokenOf req.target, deployAcctKey⟩ v = true
      ∧ v ≠ tokenOf req.target := by
  obtain ⟨v, hbody, hval, _, hne⟩ :=
    challenge_body_ca_accepted deployAcctKey (tokenOf req.target)
  exact ⟨v, conformantServe_servesAcme inner input _ hg
    (acmeChallengeBytes_fires input req hp hm hpre), hbody, hval, hne⟩

/-- The same end-to-end guarantee for the FUSED twin (`DRORB_SPAN=22`). -/
theorem conformantServeFast_acme_ca_accepted (inner : ByteArray → ByteArray)
    (input : ByteArray) (req : Request)
    (hg : headGate input = none)
    (hp : Proto.RequestSerialize.parse (reqBytes input) = some req)
    (hm : req.method = getBytes)
    (hpre : acmePrefix.isPrefixOf req.target = true) :
    ∃ v : List Char,
      conformantServeFast inner input
        = ByteArray.mk (serialize (addDate
            (challengeResp (tokenOf req.target) deployAcctKey))).toArray
      ∧ (challengeResp (tokenOf req.target) deployAcctKey).body = asciiBytes v
      ∧ Http01Authz.validate ⟨tokenOf req.target, deployAcctKey⟩ v = true
      ∧ v ≠ tokenOf req.target := by
  rw [Datapath.ServeConformantFused.conformantServeFast_eq]
  exact conformantServe_acme_ca_accepted inner input req hg hp hm hpre

/-! ## 6. Why the BARE-INNER spans do not serve it

The arm is in the wrapper, deliberately: the inner serve is consulted only OFF
the challenge route. So a span proven byte-identical to `Dataplane.drorbServe`
(`=3/4/7/18/21/24`) is faithful to what it claims and STILL does not answer the
challenge — those spans are inner-serve A/B probes, not deployable serves. -/

/-- **The inner serve is consulted only off the challenge route.** Past the Z1
head gate, when the challenge route declines, the wrapper is exactly the raw
pipeline over `inner` plus the `x-corr` scrub and `HEAD` strip — the inner's
bytes, unchanged by the ACME arm. Contrapositive of `conformantServe_servesAcme`:
whatever a bare inner serves on a challenge fetch, it is NOT the challenge
answer, because the wrapper never routes that input to it. -/
theorem conformantServe_inner_off_acme (inner : ByteArray → ByteArray)
    (input : ByteArray)
    (hg : headGate input = none) (ha : acmeChallengeBytes input = none) :
    conformantServe inner input =
      (if isHeadReq input then stripBodyBA (scrubCorrBA (respBytesRawBA inner input))
       else scrubCorrBA (respBytesRawBA inner input)) := by
  unfold conformantServe
  rw [hg, ha]

/-! ## 7. Why an equality theorem is the right tripwire

The `DRORB_SPAN=22` outage was not caught by any amount of green: the fused twin
typechecked perfectly while silently missing an arm. What catches it is a span
ASSERTING byte-identity to `conformantServe`. This theorem says exactly why that
works, for any twin whatsoever. -/

/-- **Missing the challenge answer REFUTES the twin equality.** If a candidate
wrapper `fast` fails to serve the challenge bytes on even one input the route
claims, then `fast inner` is provably NOT `conformantServe inner`. So a span that
states the twin equality cannot be missing the ACME arm — the equality is the
tripwire, and a twin that declines to state one (as `Datapath.ServeZc` did) has
no build-time protection at all. Contrapositive of `conformantServe_servesAcme`;
`fast` is universally quantified, so this covers every present and future
twin. -/
theorem twin_equality_forces_acme_arm
    (fast : (ByteArray → ByteArray) → ByteArray → ByteArray)
    (inner : ByteArray → ByteArray) (input : ByteArray) (out : Bytes)
    (hg : headGate input = none)
    (ha : acmeChallengeBytes input = some out)
    (hmiss : fast inner input ≠ ByteArray.mk out.toArray) :
    fast inner ≠ conformantServe inner := by
  intro heq
  exact hmiss (heq ▸ conformantServe_servesAcme inner input out hg ha)

/-! ## Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound} -/

#print axioms conformantServe_servesAcme
#print axioms serveConformantDenseIdx_servesAcme
#print axioms deployedDefault_servesAcme
#print axioms conformantServeFast_servesAcme
#print axioms serveConformantFastIdx_servesAcme
#print axioms serveConformantFastHeadIdx_servesAcme
#print axioms serveConformantZcIdx_servesAcme_off_bulk
#print axioms acmeChallengeBytes_fires
#print axioms conformantServe_acme_ca_accepted
#print axioms conformantServeFast_acme_ca_accepted
#print axioms conformantServe_inner_off_acme
#print axioms twin_equality_forces_acme_arm

end Datapath.AcmeSpanAudit
