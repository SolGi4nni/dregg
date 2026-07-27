/-
# O11y.OtelDrive — drive the compiled OTLP/JSON span exporter

Prints the exported OTLP/JSON for a concrete sampled span (`O11y.exampleSpan`) and for a
two-span batch — the SEEN exporter output a collector would ingest.
-/
import O11y.OtelExport

open O11y
open O11y.OtelExport

def main : IO Unit := do
  IO.println "[otel-drive] single span OTLP/JSON:"
  IO.println (spanJson "GET /api/users" exampleSpan)
  IO.println s!"[otel-drive] traceId hex chars = {(hexOf exampleSpan.traceId).toList.length} (expect 32)"
  IO.println s!"[otel-drive] spanId  hex chars = {(hexOf exampleSpan.spanId).toList.length} (expect 16)"
  IO.println "[otel-drive] two-span batch OTLP/JSON array:"
  IO.println (exportSpans "GET /api/users" [exampleSpan, exampleSpan])
