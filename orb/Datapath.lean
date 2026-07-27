import Datapath.Span
import Datapath.Scan
import Datapath.Refine
import Datapath.Serve
import Datapath.FlatHeaders
import Datapath.FlatStage
import Datapath.FlatWire
import Datapath.FlatBody
import Datapath.IndexParse
import Datapath.FlatStage_cors
import Datapath.FlatStage_redirect
import Datapath.FlatStage_gzip
import Datapath.FlatStage_ipfilter
import Datapath.FlatStage_traversal
import Datapath.FlatStage_errpage
import Datapath.FlatStage_cond
import Datapath.FlatStage_policy
import Datapath.FlatStage_htmlrw
import Datapath.FlatStage_hrw
import Datapath.FlatStage_hdr
import Datapath.RefinesData
import Datapath.RefinesDataDemo

import Datapath.ServeFlatFull
import Datapath.ByteSeq
import Datapath.ByteSeqProto
import Datapath.HdrSeq
import Datapath.HdrSeqProto
import Datapath.StagePoly_redirect
import Datapath.StagePoly_gzip
import Datapath.StagePoly_policy
import Datapath.StagePoly_rate
import Datapath.StagePoly_basicauth
import Datapath.StagePoly_traversal
import Datapath.StagePoly_jwt
import Datapath.StagePoly_ipfilter
import Datapath.StagePoly_cache
import Datapath.StagePoly_hdr
import Datapath.ServeDense
import Datapath.ServeDenseFull
import Datapath.HtmlRewriteDense
import Datapath.HtmlRewriteDense2
import Datapath.GzipDense
import Datapath.ServeDenseFull2
import Datapath.BodyGate
import Datapath.ServeGated
import Datapath.ServeUltra
import Datapath.ServeDenseFullReal
import Datapath.DenseHead
import Datapath.ServeDenseReal
import Datapath.OffarmApp
import Datapath.OffarmArms
import Datapath.ServeOffarmIdx
import Datapath.ServeOffarmMeteredIdx
/-!
# Datapath — the data-refinement framework for a zero-copy serve

A NEW, additive framework layer that lets a buffer-native (zero-copy) serve be
**proven** to refine the deployed `List UInt8` model, without touching the
deployed serve, `Proto.Basic`'s `Bytes` type, or the compiler probes.

* `Datapath.Span` — the concrete representation: `SpanBytes`, a borrowed
  `(buf, off, len)` window, with `denote` (the abstract bytes) and the
  index-native `read`, bridged by `read_eq_denote`.
* `Datapath.Refine` — the refinement relation `Refines`, the serve-shape
  obligations, and **the first proven refinement**: `spanParseRequest_refines`
  (a zero-copy request parse yields the same `Proto.Request` as the deployed
  cons-list parser), plus the proven no-aliasing separation lemma.
-/
