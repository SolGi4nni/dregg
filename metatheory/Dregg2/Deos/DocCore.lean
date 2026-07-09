/-
# `Dregg2.Deos.DocCore` — the EXECUTABLE dregg-document commitment core, **Init-only**.

Foundation piece **F4a** of `docs/DREGG-DOCUMENT-FOUNDATION.md` §2/§4: the in-tab `<dregg-doc>`
executor's commitment, written so its ENTIRE import + initialization closure is `Init` + this module
— no `ℤ`, no Mathlib. Per §4 the load-bearing discipline is that module *initialization* is not
erased (importing a module runs its `initialize_*` at boot and keeps the object), so minimality is an
IMPORT-GRAPH property: keep the `@[export]` fns over `UInt64` in an Init-only module; keep the binding
PROOFS in a SEPARATE Mathlib module (`DocProofs`) that is NEVER on the wasm import path.

This is the SAME shape as `Dregg2.Storage.Deployed.contentRootDeployed` (a Poseidon2 sponge fold
calling the fast Rust primitive via `@[extern "dregg_poseidon2_2to1"]`), but fixed-width over `UInt64`
and Mathlib-free. `DocProofs` proves this executable core computes exactly F2's ℤ-modeled `docCommit`
under the canonical encoding, so it inherits F2's injective + conflict-binds soundness.

**The FFI shape (per §4):** batched over the canonical byte encoding — the exported entry takes the
space-separated decimal felts of `commit.rs::canonical_bytes` (the SAME preimage `DocCommit.encode`
builds), not a `lean_object*` object-graph crawl. The pure core is `docCommitExec : List UInt64 →
UInt64` (the sponge); `docCommitFFI : String → String` is the thin parse/print wrapper, exactly like
`Deployed.contentRootFFI`.

NO imports (Init is implicit). Verify: `grep -o 'initialize_[A-Za-z0-9_]*' DocCore.c | sort -u` shows
only `Init` + `DocCore`.
-/

namespace Dregg2.Deos.DocCore

/-- **The fast Rust Poseidon2 2-to-1 compress**, over a native-scalar `@[extern]` (`u64 → u64 → u64`,
trivial ABI, no `lean_object` marshaling) — the SAME symbol `Storage.Deployed.p2compress` realizes:
`dregg_poseidon2_2to1`, wrapping `circuit::binding` Poseidon2 over BabyBear (field elements < 2^31 fit
a `u64`). Opaque here; its soundness is the §8 collision-resistance carrier, discharged in `DocProofs`
as a hypothesis, never a Lean law. -/
@[extern "dregg_poseidon2_2to1"]
opaque p2compress : UInt64 → UInt64 → UInt64

/-- **The sponge fold** over a canonical felt preimage: seed with the preimage length (matching
`Storage.Deployed.poseidon2Hash`'s `xs.length` seed), then absorb each felt through the fast Rust
compress. Init-only (`List.foldl`, `List.length`, `UInt64.ofNat`). -/
def spongeFold (pre : List UInt64) : UInt64 :=
  pre.foldl (fun acc x => p2compress acc x) (UInt64.ofNat pre.length)

/-- **`docCommitExec`** — the executable document commitment: the sponge over the canonical
byte-encoded document preimage (the felts of `DocCommit.encode` / `commit.rs::canonical_bytes`). The
verified LOGIC (the fold) is Lean; the hot PRIMITIVE is the fast Rust Poseidon2. `DocProofs` proves
this equals F2's ℤ `docCommit` under the encoding, so it is the ONE proven core in the tab. -/
def docCommitExec (pre : List UInt64) : UInt64 := spongeFold pre

/-- **`atomIdExec`** — the executable content-address of a single atom's canonical bytes (its
content-derived id): the same sponge over the atom's `DocCommit.encAtom` preimage felts. Same hash,
narrower preimage. -/
def atomIdExec (pre : List UInt64) : UInt64 := spongeFold pre

/-- Parse the batched canonical bytes: space-separated decimal felts → `List UInt64`. Init-only
`String` ops (`splitOn`, `toNat?`, `filterMap`, `Option.map`) — the same idiom as
`Deployed.contentRootFFI`. -/
private def parseFelts (input : String) : List UInt64 :=
  (input.splitOn " ").filterMap (fun s => s.toNat?.map UInt64.ofNat)

/-- **FFI entry (Rust→Lean): `@[export dregg_doc_commit]`** — the batched canonical byte preimage
(decimal felts) → the document commitment as a decimal string. The in-tab `<dregg-doc>` executor's
commit call: verified Lean logic, fast Rust Poseidon2 at the leaf. -/
@[export dregg_doc_commit]
def docCommitFFI (input : String) : String :=
  toString (docCommitExec (parseFelts input)).toNat

/-- **FFI entry: `@[export dregg_doc_atom_id]`** — an atom's canonical byte preimage → its
content-address as a decimal string. -/
@[export dregg_doc_atom_id]
def atomIdFFI (input : String) : String :=
  toString (atomIdExec (parseFelts input)).toNat

/-- Smoke `main`: exercises both exports so the wasm artifact runs a real computation. -/
def main : IO Unit := do
  IO.println ("dregg_doc_commit  = " ++ docCommitFFI "1 2 3 4 5 6")
  IO.println ("dregg_doc_atom_id = " ++ atomIdFFI "10 20 30")

end Dregg2.Deos.DocCore
