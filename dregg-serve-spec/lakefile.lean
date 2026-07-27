/-
  lakefile.lean — the shared serve-specification library.

  A small, standalone package that BOTH the verified-translator tree and the
  verified-dataplane tree can `require` (neither imports the other). It carries
  the serve wire semantics only — one byte type, the response record + wire
  serializer, the pipeline data, and per-stage semantic content. Lean 4 core
  only (no external package), pinned to 4.30 via the sibling `lean-toolchain`.
-/
import Lake
open Lake DSL

package «dregg-serve-spec» where
  leanOptions := #[]

@[default_target]
lean_lib ServeSpec where
  srcDir := "."
  roots  := #[`ServeSpec]
