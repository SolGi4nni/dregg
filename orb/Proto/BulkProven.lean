/-
# Proto.BulkProven — the `/bulk` 1 MiB large-body download on the DEPLOYED serve

PROVE-WHAT-RUNS for the ledger row `h1.bulk` (a large fixed-length 2xx body — the
homelab throughput endpoint, the `garbage.php` / Cloudflare `/__down` pattern).

The deployed default handler (`Reactor.App.demoApp`, dispatched by the running
`drorb_serve` through `App.handle`) routes `GET /bulk` under a non-vhost authority to
`Reactor.App.bulkRoute` — `VHandler.respond 200 bulkBody`, whose `bulkBody` is a
GENUINELY large `1 048 576`-byte (`1 MiB`) generated body. So the theorems below
describe the exact large 2xx the running dataplane emits for `GET /bulk`.

The CURL that anchors this file (lane `ran` field):

    $ curl -s -o /dev/null -w 'status=%{http_code} len=%{size_download}\n' \
           http://127.0.0.1:8080/bulk
    status=200 len=1048576

    $ curl -s -o /dev/null -w 'len=%{size_download}\n' http://127.0.0.1:8080/bulk   # no Accept-Encoding
    len=1048576                                                                       # NOT gzipped

Theorems:
  * `bulk_1mib` — the deployed app answers `GET /bulk` (any method, any headers, under a
    non-vhost `localhost` authority) with a `200` whose body is exactly `bulkBody`, and
    that body is exactly `1 048 576` bytes. Reuses the routing proof
    `Reactor.App.bulk_serves_large_body` and `Reactor.App.bulkBody_length`.
  * `bulk_plain_not_gzipped` — a request WITHOUT `Accept-Encoding: gzip` does not trip
    the deployed gzip stage: `acceptsGzip` is false, so `gzipStage.onResponse` is the
    identity — the 1 MiB body ships uncompressed, matching the `len=1048576` curl.
-/

import Reactor.App
import Reactor.Stage.Gzip

namespace Proto.BulkProven

open Reactor.App

/-- The deployed `/bulk` payload size: 1 MiB. -/
theorem bulk_size : bulkSize = 1048576 := rfl

/-- **`bulk_1mib`.** The DEPLOYED app answers `GET /bulk` — any method, any headers,
under a `localhost` (non-vhost) authority — with a `200` whose body is exactly
`bulkBody`, and that body is exactly `1 048 576` bytes (1 MiB). The whole deployed
decision: `bestMatch` falls through the author routes to the host/glob default,
`RouteAdvanced.dispatch` selects `bulkRoute`, `vhandlerResponse` builds the `200` + the
large body; `bulkBody_length` fixes its size. Curl-confirmed: `len=1048576`. -/
theorem bulk_1mib (req : Request)
    (htarget : targetSegments req.target = ["bulk"])
    (hhost : hostLabelsOf req = ["localhost"]) :
    (handle demoApp req).status = 200
  ∧ (handle demoApp req).body = bulkBody
  ∧ (handle demoApp req).body.length = 1048576 := by
  have hserve := bulk_serves_large_body req htarget hhost
  refine ⟨?_, ?_, ?_⟩
  · rw [hserve]
  · rw [hserve]
  · rw [hserve]; exact bulkBody_length

/-! ## The plain (no `Accept-Encoding`) request is delivered UNCOMPRESSED

The deployed pipeline carries the proven `gzipStage`. It only rewrites the body when
the request advertises `Accept-Encoding: … gzip …` (`acceptsGzip`). A plain `GET /bulk`
carries no such header, so the stage is a pure passthrough and the 1 MiB body reaches
the wire verbatim — exactly the `len=1048576` the no-`Accept-Encoding` curl measured. -/

/-- A request with no `Accept-Encoding` header does not accept gzip. -/
theorem no_accept_encoding_no_gzip (req : Request) (h : req.headers = []) :
    Reactor.Stage.Gzip.acceptsGzip req = false := by
  simp [Reactor.Stage.Gzip.acceptsGzip, h]

/-- **`bulk_plain_not_gzipped`.** When the request does not accept gzip, the deployed
`gzipStage`'s response phase is the IDENTITY on the threaded builder — no body rewrite,
no `Content-Encoding` header. So a plain `GET /bulk` ships the 1 MiB `bulkBody`
uncompressed, the `len=1048576` the curl observed (and never the larger stored-block
gzip that `Accept-Encoding: gzip` would trigger). -/
theorem bulk_plain_not_gzipped (c : Reactor.Pipeline.Ctx) (b : Reactor.Pipeline.ResponseBuilder)
    (hne : Reactor.Stage.Gzip.acceptsGzip c.req = false) :
    Reactor.Stage.Gzip.gzipStage.onResponse c b = b := by
  show (match Reactor.Stage.Gzip.acceptsGzip c.req with
        | true => (b.mapResp Reactor.Stage.Gzip.gzipBody).addHeader
                    (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
        | false => b) = b
  rw [hne]

end Proto.BulkProven

#print axioms Proto.BulkProven.bulk_1mib
#print axioms Proto.BulkProven.no_accept_encoding_no_gzip
#print axioms Proto.BulkProven.bulk_plain_not_gzipped
