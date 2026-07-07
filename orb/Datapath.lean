import Datapath.Span
import Datapath.Scan
import Datapath.Refine
import Datapath.Serve

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
