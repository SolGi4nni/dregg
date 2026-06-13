/-
# EmitMarshalGolden — the TRANSLATION-VALIDATION golden emitter for the Rust T8/T9 marshaller
(`dregg-lean-ffi/src/marshal.rs`), Klein CRITICAL-2 (the Rust half).

The Lean half of CRITICAL-2 is `Dregg2/Exec/FFI/Refine.lean`: it proves the `@[export]
dregg_exec_full_forest_auth` String→String body refines the gated model with the wire codec
(`parseWWire`/`encodeWWire`/`encodeWStatusOut`) INSIDE the proof, and `Dregg2/Exec/CodecRoundtrip`
proves `parseWWire ∘ encodeWWire = id`. So on the LEAN side the wire codec is out of the TCB and
`encodeWWire`/`encodeWStatusOut` are the PROVED reference encoders.

The remaining TCB limb is the hand-written Rust marshaller (`marshal_turn_hosted` = the T8 encoder;
`unmarshal_result` = the T9 decoder), upheld today by a round-trip differential that only checks the
Rust against ITSELF (+ one hard-coded golden + live-parser acceptance). The obligation is
translation-validation: that the Rust marshaller equals the LEAN codec.

This executable EMITS the golden corpus that anchors the Rust to the proved Lean encoder:

  * `IN <name>\t<encodeWWire case>`     — one line per shape-covering INPUT wire (the T8 target);
  * `OUT <name>\t<encodeWStatusOut …>`  — one line per OUTPUT wire (the T9 target, all 3 statuses).

`marshal.rs`'s `marshal_turn_hosted` must reproduce every `IN` line BYTE-FOR-BYTE, and
`unmarshal_result` must DECODE every `OUT` line to the expected structured result. The Rust side
(`marshal_conformance.rs`) builds the SAME named cases by construction and joins on `<name>`, so any
drift — a case present on one side only, or a single byte difference — fails the conformance gate.

The corpus is shape-covering (see `inputCorpus`/`outputCorpus` below): every one of the 12 `AuthW`
variants (incl. nested `oneOf`), every one of the 30 `FullActionA` arms, a DEEP multi-child forest
with a grandchild and delegation edges, all 11 `WState` fields populated with multi-element lists,
`Value` recursion (nested records, `dig`/`sym`/`int`, an escaped field name), signed-negative fields,
a full-width digest, and all three `TurnStatus` output codes.

SCRATCH executable: `lake env lean --run EmitMarshalGolden.lean > <goldenfile>`. NOTHING imports this
file; it is a pure-IO emitter over the verified `Dregg2.Exec.FFI` defs.
-/
import Dregg2.Exec.FFI

open Dregg2.Exec
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnAdmission (TurnStatus)

namespace EmitMarshalGolden

/-! ## §G0 — shared building blocks (reused by the named cases). -/

/-- The diagnostic host context (matches `WireHostCtx::diag()` on the Rust side). -/
def hcDiag : WHostCtx := diagHostCtx

/-- A NON-default host context (every field distinct + a populated freeze-set) so the host codec is
exercised on real data, not its defaults. Mirrors the Rust `host_populated` case. -/
def hcPopulated : WHostCtx :=
  { now := 12, blockHeight := 0, frozen := [3, 5, 9], storedHead := 4, budget := 777 }

/-- A maximally-populated wide state: all 11 fields non-empty + multi-element, `Value` recursion (a
nested record with a `dig`/`sym` and an escaped field name), and every side-table carrying ≥1 entry
(escrows with `some`/`none` option fields, a queue with a buffer, a swiss row with a rights array and
a `some` cert, multi-entry lifecycle/deathCert). Mirrors the Rust `state_full`. -/
def stateFull : WState :=
  { cells :=
      [ (0, .record [("balance", .int (-100)), ("nonce", .int 7),
                     ("meta", .record [("vk", .dig 255), ("tag", .sym 9)]),
                     ("weird\"key\\x", .int 1)])
      , (1, .record [("balance", .int 5)])
      , (2, .dig 0xABCDEF) ]
    caps := [ (0, [.endpoint 1 [.read, .write], .node 0]), (9, [.node 0, .null]) ]
    bal := [ (0, 0, 100), (0, 1, -3), (1, 0, 5) ]
    escrows :=
      [ { id := 1, creator := 0, recipient := 1, amount := 7, resolved := false,
          asset := 0, bridge := false, queueDep := none, queueMsg := none }
      , { id := 2, creator := 1, recipient := 0, amount := -4, resolved := true,
          asset := 2, bridge := true, queueDep := some 3, queueMsg := some 4 } ]
    nullifiers := [111, 222]
    commitments := [333]
    queues := [ { id := 1, owner := 0, capacity := 4, buffer := [333, 444] } ]
    swiss := [ { swiss := 5, exporter := 0, target := 1, rights := [.read, .write],
                 refcount := 1, cert := some 99 }
             , { swiss := 6, exporter := 1, target := 2, rights := [], refcount := 0, cert := none } ]
    revoked := [7, 8]
    lifecycle := [(0, 1), (2, 3)]
    deathCert := [(2, 42)] }

/-- The wide demo state (mirrors `marshal_roundtrip.rs::wide_demo_state` / FFI `wideDemoState`), the
shape the existing single golden uses — included so the new suite SUBSUMES the old hard-coded one. -/
def stateDemo : WState :=
  { cells := [ (0, .record [("balance", .int 100), ("nonce", .int 7)]), (1, .record [("balance", .int 5)]) ]
    caps := [(9, [.node 0])]
    bal := [(0, 0, 100), (1, 0, 5)]
    escrows := [ { id := 1, creator := 0, recipient := 1, amount := 7, resolved := false } ]
    nullifiers := [111]
    commitments := [222]
    queues := [ { id := 1, owner := 0, capacity := 4, buffer := [333, 444] } ]
    swiss := [ { swiss := 5, exporter := 0, target := 1, rights := [.read, .write], refcount := 1, cert := some 99 } ]
    revoked := []
    lifecycle := []
    deathCert := [] }

/-- A trivial single-cell state (the minimal non-empty state — exercises the singleton list arms). -/
def stateMinimal : WState :=
  { cells := [(0, .record [("balance", .int 0)])], caps := [], bal := [], escrows := [],
    nullifiers := [], commitments := [], queues := [], swiss := [], revoked := [],
    lifecycle := [], deathCert := [] }

/-- Wrap a root `WForest` into a `WTurn` with a fixed envelope (block_height 0 = the deployed shape;
the §16 round-trip + Refine.lean both pin `blockHeight = 0`). The `prev` digest is non-trivial so the
hex-32 codec is exercised on a non-zero value. -/
def turnOf (root : WForest) : WTurn :=
  { agent := 0, nonce := 7, fee := 5, validUntil := 1000, blockHeight := 0, prevHash := 0xDEADBEEF, root := root }

/-- A leaf root carrying the given credential + a monotone caveat, over a balance transfer. -/
def rootSig (a : AuthW) : WForest :=
  ⟨a, [{ tier := 0, cell := 0, asset := 0, min := 0 }],
     .balanceA { actor := 0, src := 0, dst := 1, amt := 30 } 0, []⟩

/-- A DEEP forest: root (signature + 2 caveats of distinct tiers) with TWO delegation children, the
first carrying a `keep`/`cap` edge AND a grandchild (so the §15 children recursion is exercised at
depth 2, with edges and caveats on every node). Mirrors the Rust `forest_deep`. -/
def forestDeep : WForest :=
  ⟨ .signature 7 7
  , [{ tier := 0, cell := 0, asset := 0, min := 0 }, { tier := 2, cell := 1, asset := 0, min := 1 }]
  , .emitEventA 0 0 0 0
  , [ ⟨1, [.read], .endpoint 1 [.read, .write],
        ⟨ .token 14 15, [{ tier := 1, cell := 1, asset := 0, min := 0 }], .emitEventA 1 1 0 0
        , [ ⟨2, [.read, .write], .node 0, ⟨.unchecked, [], .revoke 0 0, []⟩⟩ ] ⟩⟩
    , ⟨3, [], .null, ⟨.breadstuff 42, [], .makeSovereignA 3 3, []⟩⟩ ] ⟩

/-! ## §G1 — the INPUT corpus (the T8 encode targets). Each `(name, WWire)`; the line emitted is
`IN <name>\t<encodeWWire wire>`. -/

/-- Every `AuthW` variant as a root credential, named `auth_<i>` (covers all 12 `allAuths` incl.
the two nested `oneOf` cases). -/
def authCases : List (String × WWire) :=
  (allAuths.zipIdx).map (fun (a, i) =>
    (s!"auth_{i}", { host := hcDiag, state := stateMinimal, turn := turnOf (rootSig a) }))

/-- Every `FullActionA` arm as a root action under `.unchecked`, named `action_<i>` (covers all 30
`allActions` arms incl. the nested `exerciseA` inner array and the `heapWriteA` signed digests). -/
def actionCases : List (String × WWire) :=
  (allActions.zipIdx).map (fun (act, i) =>
    (s!"action_{i}",
      { host := hcDiag, state := stateMinimal,
        turn := turnOf ⟨.unchecked, [], act, []⟩ }))

/-- A turn whose `blockHeight > 0` — so the OPTIONAL `,"block_height":N` envelope arm FIRES (the
`if bh > 0` branch on both sides; the only encoder branch the `blockHeight = 0` cases skip). NOTE
this is OUTSIDE the proved round-trip boundary (`parseWWire_encode` requires `blockHeight = 0`), so it
anchors the ENCODER's optional arm only — see the residual note in the harness. -/
def turnBh (root : WForest) : WTurn :=
  { agent := 1, nonce := 2, fee := -3, validUntil := 9, blockHeight := 42, prevHash := 0xDEADBEEF, root := root }

/-- A root carrying a tier-3 ("coordinated") caveat — the only `WCaveat.tier` value the structural
cases above omit (they use 0/1/2). The encoder treats `tier` as a plain `Nat`, so this pins the
high-tier path too. -/
def rootTier3 : WForest :=
  ⟨.unchecked, [{ tier := 3, cell := 2, asset := 1, min := -5 }], .pipelinedSendA 9, []⟩

/-- The hand-built structural cases (deep forest, full state, escaped values, host context, the
demo-subsuming case, the optional block_height arm, the tier-3 caveat). -/
def structuralCases : List (String × WWire) :=
  [ ("forest_deep",     { host := hcDiag,      state := stateMinimal, turn := turnOf forestDeep })
  , ("state_full",      { host := hcDiag,      state := stateFull,    turn := turnOf (rootSig (.signature 7 7)) })
  , ("state_demo",      { host := hcDiag,      state := stateDemo,    turn := turnOf (rootSig (.signature 7 7)) })
  , ("host_populated",  { host := hcPopulated, state := stateFull,    turn := turnOf forestDeep })
  , ("full_combo",      { host := hcPopulated, state := stateFull,    turn := turnOf forestDeep })
  , ("turn_blockheight", { host := hcDiag,     state := stateMinimal, turn := turnBh (rootSig (.signature 7 7)) })
  , ("caveat_tier3",    { host := hcDiag,      state := stateMinimal, turn := turnOf rootTier3 }) ]

/-- The whole INPUT corpus. -/
def inputCorpus : List (String × WWire) := authCases ++ actionCases ++ structuralCases

/-! ## §G2 — the OUTPUT corpus (the T9 decode targets). `encodeWStatusOut state loglen status` over
all three `TurnStatus` codes + an echoed state, so the Rust `unmarshal_result` is anchored to the
proved OUTPUT encoder (`status:0/1/2`, the `ok`-bit narrowing, the empty sentinel). -/

def outputCorpus : List (String × String) :=
  [ ("out_committed",   encodeWStatusOut stateFull 3 TurnStatus.bodyCommitted)
  , ("out_prologue",    encodeWStatusOut stateDemo 0 TurnStatus.prologueCommittedBodyFailed)
  , ("out_rejected",    encodeWStatusOut stateDemo 0 TurnStatus.rejected)
  , ("out_sentinel",    encodeWStatusOut emptyWState 0 TurnStatus.rejected)
  , ("out_minimal_ok",  encodeWStatusOut stateMinimal 1 TurnStatus.bodyCommitted) ]

/-! ## §G3 — emit. -/

def main : IO Unit := do
  for (name, w) in inputCorpus do
    IO.println s!"IN\t{name}\t{encodeWWire w}"
  for (name, s) in outputCorpus do
    IO.println s!"OUT\t{name}\t{s}"

end EmitMarshalGolden

open EmitMarshalGolden in
def main : IO Unit := EmitMarshalGolden.main
