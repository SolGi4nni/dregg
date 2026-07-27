import Datapath.AcmeSpanAudit
import Dataplane

/-!
# Datapath.AcmeDeployedAudit — the DEPLOYED serve crossings must serve HTTP-01 too

`Datapath.AcmeSpanAudit` discharges `ServesAcme` for the `DRORB_SPAN` A/B family.
That family is not the whole hazard. `crates/dataplane/src/serve.rs` picks the
serve entry point from a `Seam` **and** a metering flag, and two further
environment variables (`DRORB_BRAID`, `DRORB_GATEWAY`) divert every request to a
DIFFERENT proven serve — these are DEPLOYMENT modes, not measurement levers, so a
missing challenge arm on any of them is a live certificate-renewal outage rather
than a bad benchmark.

The crossings, read off `serve_job` (`crates/dataplane/src/serve.rs`, the
`match meter { … } match seam { … }` at the response-staging point):

| host crossing | selected by | export |
|---|---|---|
| `serve_metered_dense_conformant_into` | metered `Seam::Http` — **the io_uring production default** | `drorb_serve_pipeline_conformant` |
| `serve_metered_cfg_conformant_into` | metered `Seam::ServeCfg` (the config-driven default) | `drorb_serve_metered_cfg_conformant` |
| `serve_metered_braided_conformant_into` | `DRORB_BRAID=1` | `drorb_serve_metered_braided_conformant` |
| `serve_gateway_into` | `DRORB_GATEWAY=dreggnet` | `drorb_serve_gateway` |
| `serve_into_via(… drorb_serve_conformant_head_idx)` | non-metered `Seam::Http` | `drorb_serve_conformant_head_idx` |

Every one of them is `Reactor.ServeConformant.conformantServe` applied to its own
inner fold, so `Datapath.AcmeSpanAudit.conformantServe_servesAcme` discharges the
obligation for all five — but that is a fact about the CURRENT definitions, and
the `DRORB_SPAN=22` outage is the proof that "it happens to be shaped right
today" is not a guarantee. Naming each crossing here turns a future re-shaping of
any one of them (fusing the wrapper, inlining the gates, threading a new
admission argument through a hand-written control-flow copy) into a BUILD ERROR
at exactly the deployed symbol, instead of an expired certificate 90 days later.

Driven, not only proven — each row was exercised against a running dataplane on
hbox with `curl /.well-known/acme-challenge/<token>`; see
`docs/gateway/ACME-SPAN-AUDIT.md`.
-/

namespace Datapath.AcmeDeployedAudit

open Proto (Bytes)
open Reactor (serialize)
open Reactor.ServeConformant (conformantServe acmeChallengeBytes addDate reqBytes)
open Reactor.Stage.RequestHeadLimit (headGate)
open Reactor.Stage.AcmeChallenge (challengeResp tokenOf deployAcctKey getBytes acmePrefix)
open Pki.Acme (asciiBytes Http01Authz)
open Datapath.AcmeSpanAudit (ServesAcme conformantServe_servesAcme
  conformantServe_acme_ca_accepted)

/-! ## 1. The metered production default (`drorb_serve_pipeline_conformant`)

The single crossing the io_uring reactor takes for a plain metered HTTP job, and
the one the `--io auto` production reactor runs. Universally quantified over the
metering arguments the host threads in (peer address, rate sequence, the two DoS
admission readings), because the challenge answer must not depend on any of
them. -/

/-- **THE DEPLOYED METERED DEFAULT SERVES HTTP-01**, for every peer, rate
sequence and DoS admission reading. `drorb_serve_pipeline_conformant` is the ONE
symbol `serve_metered_dense_conformant_into` crosses. -/
theorem drorbServePipelineConformant_servesAcme
    (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64) :
    ServesAcme (drorbServePipelineConformant peer seq active span cap rateCount rateLimit burstCap burstRate) :=
  conformantServe_servesAcme _

/-! ## 2. The non-metered default (`drorb_serve_conformant_head_idx`) -/

/-- **The non-metered `Seam::Http` default serves HTTP-01.** Stated on the
`@[export]`ed symbol itself, not on its definiens — the audit's
`deployedDefault_servesAcme` covers the shape, this covers the SYMBOL the host
names in `serve_into_via`. -/
theorem drorbServeConformantHeadIdx_servesAcme :
    ServesAcme drorbServeConformantHeadIdx :=
  conformantServe_servesAcme _

/-- **`DRORB_SPAN=19`'s export** (`drorb_serve_conformant`) serves HTTP-01. -/
theorem drorbServeConformant_servesAcme :
    ServesAcme drorbServeConformant :=
  conformantServe_servesAcme _

/-! ## 3. `DRORB_BRAID=1` — the braided deployment -/

/-- **The braided deployment serves HTTP-01.** `DRORB_BRAID=1` diverts every
request to the forward-auth / request-id braid; the conformance wrapper (and so
the challenge route) is still outermost, for every peer and sequence. -/
theorem drorbServeMeteredBraidedConformant_servesAcme (peer : ByteArray) (seq : UInt64) :
    ServesAcme (drorbServeMeteredBraidedConformant peer seq) :=
  conformantServe_servesAcme _

/-! ## 4. `DRORB_GATEWAY` — the umbrella deployment, for EVERY selector

The gateway lane replaces the whole route table with a denoted multi-vhost
umbrella (`Dsl.Config.Gateway.denoteOn`). That is precisely the shape in which an
operator would expect to have to *declare* an ACME route — and would not. The
selector is universally quantified, so a NEW compiled-in umbrella config cannot
lose the challenge answer either: the arm is above the dispatch, not inside
it. -/

/-- **The Gateway umbrella serves HTTP-01, under every selector.** Including
selector `1` (`DRORB_GATEWAY=dreggnet`, the replicated dregg.net umbrella) and
any umbrella added later — no vhost or route declaration is required, and none
can suppress it. -/
theorem drorbServeGateway_servesAcme (peer : ByteArray) (seq gwSel : UInt64) :
    ServesAcme (drorbServeGateway peer seq gwSel) :=
  conformantServe_servesAcme _

/-! ## 5. The config-driven metered default (`drorb_serve_metered_cfg_conformant`)

The only crossing whose input is FRAMED (`be32 cfgLen :: config :: request`): the
wrapper is applied to the UNFRAMED request, so the obligation lands on that. The
hypothesis is the framing the host always writes
(`ServeGateway::call_metered_cfg`), and the conclusion is the challenge answer for
the request inside the frame — under ANY config, including a route table that
declares nothing. -/

/-- **The config-driven default serves HTTP-01, under any config.** For a
correctly framed input, a challenge fetch in the request half is answered with
the challenge bytes — the config's route table is never consulted, so no
deployment config can suppress renewal. -/
theorem drorbServeMeteredCfgConformant_servesAcme
    (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64) (input : ByteArray)
    (b0 b1 b2 b3 : UInt8) (rest : List UInt8)
    (hframe : input.toList = b0 :: b1 :: b2 :: b3 :: rest)
    (out : Bytes)
    (hg : headGate (ByteArray.mk (rest.drop (be32 b0 b1 b2 b3)).toArray) = none)
    (ha : acmeChallengeBytes (ByteArray.mk (rest.drop (be32 b0 b1 b2 b3)).toArray)
            = some out) :
    drorbServeMeteredCfgConformant peer seq active span cap rateCount rateLimit burstCap burstRate input = ByteArray.mk out.toArray := by
  unfold drorbServeMeteredCfgConformant
  rw [hframe]
  exact conformantServe_servesAcme _ _ _ hg ha

/-! ## 6. Non-vacuity — a REAL CA validation fetch, at the production symbol

`ServesAcme`'s hypotheses are the ordinary CA fetch, and this section pins that
on a concrete one rather than leaving it to prose. The Z1 head-gate hypothesis is
discharged by the KERNEL (`caFetch_headGate`, `rfl`); the parse hypotheses are
evaluated by the `#guard` below. The remaining step from parse to
`acmeChallengeBytes = some _` is `AcmeSpanAudit.acmeChallengeBytes_fires`.

Honest limit, same one the span audit hit: the parse is well-founded-recursive,
so `caHyps` is NOT definitionally `true` and the parse facts cannot be closed by
`rfl`/`decide` — they are evaluator-checked, not kernel-checked. Downstream of
the parse the account-key hash (`Crypto.sha256`) is an `@[extern]` with no
interpreter symbol, so the served body cannot be `#guard`ed at all. What IS
kernel-checked is everything the theorems above quantify over. -/

/-- The exact bytes a validating CA sends: the request driven against the running
dataplane on hbox for every row of `docs/gateway/ACME-SPAN-AUDIT.md`. -/
def caFetch : ByteArray :=
  "GET /.well-known/acme-challenge/tok0LmNkMsdN HTTP/1.1\r\nHost: dregg.net\r\n\r\n".toUTF8

/-- **The Z1 head gate lets a real CA fetch through** — kernel-checked. So the
first hypothesis of every `ServesAcme` instance above is discharged outright for
the request a CA actually sends. -/
theorem caFetch_headGate : headGate caFetch = none := by rfl

/-- The parse hypotheses of `acmeChallengeBytes_fires` on that request: it parses,
its method is `GET`, and its target is under `/.well-known/acme-challenge/`.
Evaluator-checked below (see the honest limit above). -/
def caHyps : Bool :=
  match Proto.RequestSerialize.parse (reqBytes caFetch) with
  | some r => (r.method == getBytes) && acmePrefix.isPrefixOf r.target
  | none => false

#guard (headGate caFetch).isNone
#guard caHyps

/-- **END TO END AT THE PRODUCTION SYMBOL, ON A REAL CA FETCH.** Given only the
parse facts `caHyps` evaluates to `true`, the bytes the deployed metered default
(`drorb_serve_pipeline_conformant` — the crossing the io_uring reactor takes) puts
on the wire for a CA validation fetch are the serialization of a response whose
body is a value the CA holding `deployAcctKey` ACCEPTS, and is not the bare token.
The Z1 hypothesis is gone (`caFetch_headGate`); every metering argument is
universally quantified. -/
theorem drorbServePipelineConformant_ca_accepted_on_real_fetch
    (peer : ByteArray) (seq active span cap rateCount rateLimit burstCap burstRate : UInt64) (r : Proto.Request)
    (hp : Proto.RequestSerialize.parse (reqBytes caFetch) = some r)
    (hm : r.method = getBytes)
    (hpre : acmePrefix.isPrefixOf r.target = true) :
    ∃ v : List Char,
      drorbServePipelineConformant peer seq active span cap rateCount rateLimit burstCap burstRate caFetch
        = ByteArray.mk (serialize (addDate
            (challengeResp (tokenOf r.target) deployAcctKey))).toArray
      ∧ (challengeResp (tokenOf r.target) deployAcctKey).body = asciiBytes v
      ∧ Http01Authz.validate ⟨tokenOf r.target, deployAcctKey⟩ v = true
      ∧ v ≠ tokenOf r.target :=
  conformantServe_acme_ca_accepted _ caFetch r caFetch_headGate hp hm hpre

/-! ## 7. What is NOT covered, stated plainly

* The `DRORB_SPAN` bare-inner levers (`=3/4/7/18/21/24`) and the echo exemplars
  (`=1/2/5/6/8..17`) do NOT serve the challenge, by design — see
  `Datapath.AcmeSpanAudit.conformantServe_inner_off_acme`. They are measurement
  levers; selecting one loses certificate renewal.
* `DRORB_SPAN=25` (`drorb_serve_grpcweb`) is a bare protocol edge and answers
  `415` to everything else, the challenge path included.
* The gateway lane is wired ONLY in the blocking reactor
  (`crates/dataplane/src/blocking.rs`); under the production io_uring reactor
  `DRORB_GATEWAY` is inert and the metered default (§1) runs. That is a host
  reachability fact, not a Lean one, and it is recorded in the findings doc.
-/

/-! ## Axiom audit — expect ⊆ {propext, Classical.choice, Quot.sound} -/

#print axioms drorbServePipelineConformant_servesAcme
#print axioms drorbServeConformantHeadIdx_servesAcme
#print axioms drorbServeConformant_servesAcme
#print axioms drorbServeMeteredBraidedConformant_servesAcme
#print axioms drorbServeGateway_servesAcme
#print axioms drorbServeMeteredCfgConformant_servesAcme
#print axioms caFetch_headGate
#print axioms drorbServePipelineConformant_ca_accepted_on_real_fetch

end Datapath.AcmeDeployedAudit
