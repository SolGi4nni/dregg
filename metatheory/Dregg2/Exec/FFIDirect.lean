/-
# Dregg2.Exec.FFIDirect — the NO-COPY (`lean_object*`) C-ABI boundary.

The `Dregg2.Exec.FFI` boundary marshals the whole `(host, state, turn)` to a JSON STRING which the
Lean side then PARSES (`parseWWire`) back into the very inductives it could have been handed directly —
and re-ENCODES the post-state to a STRING the Rust side re-parses. That double JSON round-trip is the
~100µs/turn tax the bench measures (`perf/benches/lean_ffi_turn.rs`); the cost tracks JSON BYTES.

This module removes the JSON entirely. The Rust host CONSTRUCTS the boundary objects (`WHostCtx`,
`WState`, `WTurn`) as real Lean inductives by calling the BUILDER `@[export]`s below (bottom-up: leaves
first, then containers), runs the SAME proved `execFullForestAuthStep` body via `execDirect`, and READS
the post-state back out with the READER `@[export]`s — no string crosses the boundary in either
direction. Every builder is an ordinary total Lean function, so the LEAN COMPILER emits the correct
`lean_object*` constructor layout; the Rust side never touches a raw ctor offset (no UB surface).

NOTHING below changes the verified executor: `execDirect` calls the IDENTICAL admission/lift/run/read
chain `execFullForestAuthStep` uses (`stateOfWState`/`liftForestG`/`admCtxOfHost`/`turnHdrOf`/
`eraseAuth`/`runGatedForestTurnStatus`/`wstateOfState`). The only new code is the data-construction
(builders) and data-projection (readers) around that unchanged core.
-/
import Dregg2.Exec.FFI

namespace Dregg2.Exec.FFIDirect

open Dregg2.Exec
open Dregg2.Authority
open Dregg2.Exec.FFI
open Dregg2.Exec.FFI.Wide
open Dregg2.Exec.TurnExecutorFull (FullActionA)
open Dregg2.Exec.StarbridgeGated (DForest)
open Dregg2.Exec.TurnAdmission (runGatedForestTurnStatus TurnStatus)
open Dregg2.Exec.AdmissionWire (turnHdrOf)

/-! ## Generic list builders (build a `List α` bottom-up from C).

The C side starts with `mk*Nil` and folds with `mk*Cons elem tail`. One pair per element type that
crosses; `lean_object*` args are consumed (standard Lean ownership), so the C side hands ownership of
each freshly-built element/tail to the cons. -/

/-- u64 → `Nat`. The C side hands a `UInt64`; we widen to `Nat` (the wire/kernel scalar). -/
@[export dregg_d_nat_of_u64]
def natOfU64 (n : UInt64) : Nat := n.toNat

/-- (u64,bool) → signed `Int`. The C side cannot pass a negative directly through `UInt64`, so it
hands the magnitude + a sign flag; `neg = true` ⇒ `-mag`. -/
@[export dregg_d_int_of_u64]
def intOfU64 (mag : UInt64) (neg : Bool) : Int :=
  if neg then -(Int.ofNat mag.toNat) else Int.ofNat mag.toNat

/-! ### `List Nat` (nullifiers / commitments / revoked / frozen). -/

@[export dregg_d_natlist_nil]  def natListNil : List Nat := []
@[export dregg_d_natlist_cons] def natListCons (x : Nat) (xs : List Nat) : List Nat := x :: xs

/-! ### `List Auth` (cap rights / keep / swiss rights). `Auth` is `Dregg2.Authority.Auth` (8 ctors). -/

@[export dregg_d_auth_of_tag]
def authOfTag : UInt8 → Auth
  | 0 => .read | 1 => .write | 2 => .grant | 3 => .call
  | 4 => .reply | 5 => .reset | 6 => .control | _ => .notify

@[export dregg_d_authlist_nil]  def authListNil : List Auth := []
@[export dregg_d_authlist_cons] def authListCons (x : Auth) (xs : List Auth) : List Auth := x :: xs

/-! ### `Cap` (3 ctors) and `List Cap`. -/

@[export dregg_d_cap_null]     def capNull : Cap := .null
@[export dregg_d_cap_node]     def capNode (t : UInt64) : Cap := .node t.toNat
@[export dregg_d_cap_endpoint] def capEndpoint (t : UInt64) (r : List Auth) : Cap := .endpoint t.toNat r

@[export dregg_d_caplist_nil]  def capListNil : List Cap := []
@[export dregg_d_caplist_cons] def capListCons (x : Cap) (xs : List Cap) : List Cap := x :: xs

/-! ### `Value` (4 ctors) and the named-field list `List (FieldName × Value)`. -/

@[export dregg_d_value_int] def valueInt (i : Int) : Value := .int i
@[export dregg_d_value_dig] def valueDig (n : UInt64) : Value := .dig n.toNat
@[export dregg_d_value_sym] def valueSym (n : UInt64) : Value := .sym n.toNat
@[export dregg_d_value_record] def valueRecord (fs : List (FieldName × Value)) : Value := .record fs

@[export dregg_d_fieldlist_nil] def fieldListNil : List (FieldName × Value) := []
@[export dregg_d_fieldlist_cons]
def fieldListCons (name : String) (v : Value) (xs : List (FieldName × Value)) :
    List (FieldName × Value) := (name, v) :: xs

/-! ## `WState` builders.

`WState` carries 12 fields; the C side assembles each side-table list, then calls `mkWState`. We
expose typed list builders for the structured tables (cells/caps/bal) plus the per-cell `[k,v]`
tables (lifecycle/deathCert/delegate). Side-tables the kernel DROPS (escrows/queues/swiss) default
empty — they are wire-compat ballast `stateOfWState` ignores. -/

/-- `cells : List (CellId × Value)` — one `(id, value)` per cell. -/
@[export dregg_d_cells_nil] def cellsNil : List (CellId × Value) := []
@[export dregg_d_cells_cons]
def cellsCons (id : UInt64) (v : Value) (xs : List (CellId × Value)) :
    List (CellId × Value) := (id.toNat, v) :: xs

/-- `caps : List (CellId × List Cap)` — one `(holder, clist)` per cap-bearing cell. -/
@[export dregg_d_caps_nil] def capsNil : List (CellId × List Cap) := []
@[export dregg_d_caps_cons]
def capsCons (h : UInt64) (cl : List Cap) (xs : List (CellId × List Cap)) :
    List (CellId × List Cap) := (h.toNat, cl) :: xs

/-- `bal : List (CellId × AssetId × Int)` — one `(cell, asset, amt)` per ledger slot. -/
@[export dregg_d_bal_nil] def balNil : List (CellId × AssetId × Int) := []
@[export dregg_d_bal_cons]
def balCons (cell asset : UInt64) (amt : Int) (xs : List (CellId × AssetId × Int)) :
    List (CellId × AssetId × Int) := (cell.toNat, asset.toNat, amt) :: xs

/-- A per-cell `[cell, val]` table (`lifecycle` / `deathCert` / `delegate`). -/
@[export dregg_d_cellnats_nil] def cellNatsNil : List (CellId × Nat) := []
@[export dregg_d_cellnats_cons]
def cellNatsCons (cell val : UInt64) (xs : List (CellId × Nat)) :
    List (CellId × Nat) := (cell.toNat, val.toNat) :: xs

/-- Build the full `WState` from the assembled tables. `escrows`/`queues`/`swiss` default empty (the
kernel `stateOfWState` drops them); `nullifiers`/`commitments`/`revoked` are the note/revocation SETs. -/
@[export dregg_d_mk_wstate]
def mkWState (cells : List (CellId × Value)) (caps : List (CellId × List Cap))
    (bal : List (CellId × AssetId × Int)) (nullifiers commitments revoked : List Nat)
    (lifecycle deathCert delegate : List (CellId × Nat)) : WState :=
  { cells := cells, caps := caps, bal := bal,
    escrows := [], nullifiers := nullifiers, commitments := commitments,
    queues := [], swiss := [], revoked := revoked,
    lifecycle := lifecycle, deathCert := deathCert, delegate := delegate }

/-! ## `AuthW` builders (`Authorization Nat Nat`, 10 ctors; `oneOf` recurses). -/

@[export dregg_d_auth_signature] def authSignature (pk sig : UInt64) : AuthW := .signature pk.toNat sig.toNat
@[export dregg_d_auth_proof]
def authProof (vk pf : UInt64) (ba br : UInt64) : AuthW := .proof vk.toNat pf.toNat ba.toNat br.toNat
@[export dregg_d_auth_breadstuff] def authBreadstuff (tok : UInt64) : AuthW := .breadstuff tok.toNat
@[export dregg_d_auth_bearer]
def authBearer (dm ds : UInt64) (stark : Bool) : AuthW := .bearer dm.toNat ds.toNat stark
@[export dregg_d_auth_unchecked] def authUnchecked : AuthW := .unchecked
@[export dregg_d_auth_captp]
def authCapTp (im sm isig ss : UInt64) : AuthW := .capTpDelivered im.toNat sm.toNat isig.toNat ss.toNat
@[export dregg_d_auth_custom] def authCustom (st pf : UInt64) : AuthW := .custom st.toNat pf.toNat
@[export dregg_d_auth_oneof]
def authOneOf (cands : List AuthW) (i : UInt64) : AuthW := .oneOf cands i.toNat
@[export dregg_d_auth_stealth]
def authStealth (otp eph sig : UInt64) : AuthW := .stealth otp.toNat eph.toNat sig.toNat
@[export dregg_d_auth_token] def authToken (key sig : UInt64) : AuthW := .token key.toNat sig.toNat

@[export dregg_d_authwlist_nil]  def authWListNil : List AuthW := []
@[export dregg_d_authwlist_cons] def authWListCons (x : AuthW) (xs : List AuthW) : List AuthW := x :: xs

/-! ## `WCaveat` builders and the caveat list. -/

@[export dregg_d_mk_caveat]
def mkCaveat (tier cell asset : UInt64) (min : Int) : WCaveat :=
  { tier := tier.toNat, cell := cell.toNat, asset := asset.toNat, min := min }

@[export dregg_d_caveatlist_nil]  def caveatListNil : List WCaveat := []
@[export dregg_d_caveatlist_cons]
def caveatListCons (x : WCaveat) (xs : List WCaveat) : List WCaveat := x :: xs

/-! ## `FullActionA` builders (the 30 action arms; `exerciseA` recurses through inner actions). -/

@[export dregg_d_act_balance]
def actBalance (actor src dst : UInt64) (amt : Int) (asset : UInt64) : FullActionA :=
  .balanceA { actor := actor.toNat, src := src.toNat, dst := dst.toNat, amt := amt } asset.toNat
@[export dregg_d_act_delegate]
def actDelegate (delegator recipient t : UInt64) : FullActionA :=
  .delegate delegator.toNat recipient.toNat t.toNat
@[export dregg_d_act_revoke] def actRevoke (holder t : UInt64) : FullActionA := .revoke holder.toNat t.toNat
@[export dregg_d_act_mint]
def actMint (actor cell asset : UInt64) (amt : Int) : FullActionA := .mintA actor.toNat cell.toNat asset.toNat amt
@[export dregg_d_act_burn]
def actBurn (actor cell asset : UInt64) (amt : Int) : FullActionA := .burnA actor.toNat cell.toNat asset.toNat amt
@[export dregg_d_act_setfield]
def actSetField (actor cell : UInt64) (field : String) (v : Int) : FullActionA :=
  .setFieldA actor.toNat cell.toNat field v
@[export dregg_d_act_emit]
def actEmit (actor cell : UInt64) (topic data : Int) : FullActionA := .emitEventA actor.toNat cell.toNat topic data
@[export dregg_d_act_incnonce]
def actIncNonce (actor cell : UInt64) (newNonce : Int) : FullActionA := .incrementNonceA actor.toNat cell.toNat newNonce
@[export dregg_d_act_setperms]
def actSetPerms (actor cell : UInt64) (perms : Int) : FullActionA := .setPermissionsA actor.toNat cell.toNat perms
@[export dregg_d_act_setvk]
def actSetVk (actor cell : UInt64) (vk : Int) : FullActionA := .setVKA actor.toNat cell.toNat vk
@[export dregg_d_act_introduce]
def actIntroduce (introducer recipient target : UInt64) : FullActionA :=
  .introduceA introducer.toNat recipient.toNat target.toNat
@[export dregg_d_act_delatten]
def actDelegateAtten (delegator recipient target : UInt64) (keep : List Auth) : FullActionA :=
  .delegateAttenA delegator.toNat recipient.toNat target.toNat keep
@[export dregg_d_act_atten]
def actAttenuate (actor idx : UInt64) (keep : List Auth) : FullActionA := .attenuateA actor.toNat idx.toNat keep
@[export dregg_d_act_revdel]
def actRevokeDelegation (holder target : UInt64) : FullActionA := .revokeDelegationA holder.toNat target.toNat
@[export dregg_d_act_exercise]
def actExercise (actor target : UInt64) (inner : List FullActionA) : FullActionA :=
  .exerciseA actor.toNat target.toNat inner
@[export dregg_d_act_createcell]
def actCreateCell (actor newCell : UInt64) : FullActionA := .createCellA actor.toNat newCell.toNat
@[export dregg_d_act_createcellfactory]
def actCreateCellFromFactory (actor newCell : UInt64) (vk : Int) : FullActionA :=
  .createCellFromFactoryA actor.toNat newCell.toNat vk
@[export dregg_d_act_spawn]
def actSpawn (actor child target : UInt64) : FullActionA := .spawnA actor.toNat child.toNat target.toNat
@[export dregg_d_act_bmint]
def actBridgeMint (actor cell asset : UInt64) (value : Int) : FullActionA :=
  .bridgeMintA actor.toNat cell.toNat asset.toNat value
@[export dregg_d_act_nspend]
def actNoteSpend (nf actor : UInt64) (spendProof : Bool) : FullActionA := .noteSpendA nf.toNat actor.toNat spendProof
@[export dregg_d_act_ncreate]
def actNoteCreate (cm actor : UInt64) : FullActionA := .noteCreateA cm.toNat actor.toNat
@[export dregg_d_act_sov]
def actMakeSovereign (actor cell : UInt64) : FullActionA := .makeSovereignA actor.toNat cell.toNat
@[export dregg_d_act_refusal]
def actRefusal (actor cell : UInt64) : FullActionA := .refusalA actor.toNat cell.toNat
@[export dregg_d_act_rarchive]
def actReceiptArchive (actor cell : UInt64) : FullActionA := .receiptArchiveA actor.toNat cell.toNat
@[export dregg_d_act_cseal]
def actCellSeal (actor cell : UInt64) : FullActionA := .cellSealA actor.toNat cell.toNat
@[export dregg_d_act_cunseal]
def actCellUnseal (actor cell : UInt64) : FullActionA := .cellUnsealA actor.toNat cell.toNat
@[export dregg_d_act_cdestroy]
def actCellDestroy (actor cell certHash : UInt64) : FullActionA :=
  .cellDestroyA actor.toNat cell.toNat certHash.toNat
@[export dregg_d_act_rdel]
def actRefreshDelegation (actor child : UInt64) : FullActionA := .refreshDelegationA actor.toNat child.toNat
@[export dregg_d_act_psend]
def actPipelinedSend (actor : UInt64) : FullActionA := .pipelinedSendA actor.toNat
@[export dregg_d_act_hwrite]
def actHeapWrite (actor target : UInt64) (addr v newRoot : Int) : FullActionA :=
  .heapWriteA actor.toNat target.toNat addr v newRoot

@[export dregg_d_actlist_nil]  def actListNil : List FullActionA := []
@[export dregg_d_actlist_cons]
def actListCons (x : FullActionA) (xs : List FullActionA) : List FullActionA := x :: xs

/-! ## `WForest` / `WChild` builders (the recursive action tree). -/

@[export dregg_d_mk_wforest]
def mkWForest (auth : AuthW) (caveats : List WCaveat) (action : FullActionA)
    (children : List WChild) : WForest :=
  { auth := auth, caveats := caveats, action := action, children := children }

@[export dregg_d_mk_wchild]
def mkWChild (holder : UInt64) (keep : List Auth) (parentCap : Cap) (sub : WForest) : WChild :=
  { holder := holder.toNat, keep := keep, parentCap := parentCap, sub := sub }

@[export dregg_d_childlist_nil]  def childListNil : List WChild := []
@[export dregg_d_childlist_cons] def childListCons (x : WChild) (xs : List WChild) : List WChild := x :: xs

/-! ## `WTurn` and `WHostCtx` builders. -/

@[export dregg_d_mk_wturn]
def mkWTurn (agent nonce : UInt64) (fee : Int) (validUntil blockHeight prevHash : UInt64)
    (root : WForest) : WTurn :=
  { agent := agent.toNat, nonce := nonce.toNat, fee := fee, validUntil := validUntil.toNat,
    blockHeight := blockHeight.toNat, prevHash := prevHash.toNat, root := root }

@[export dregg_d_mk_whostctx]
def mkWHostCtx (now blockHeight : UInt64) (frozen : List Nat) (storedHead budget : UInt64) :
    WHostCtx :=
  { now := now.toNat, blockHeight := blockHeight.toNat, frozen := frozen,
    storedHead := storedHead.toNat, budget := budget.toNat }

/-! ## The DIRECT executor.

`execDirect host state turn` runs the IDENTICAL chain `execFullForestAuthStep` runs (no re-proof):
`stateOfWState`/`liftForestG`/`admCtxOfHost`/`turnHdrOf`/`eraseAuth`/`runGatedForestTurnStatus`/
`wstateOfState`. The post-state is read back at the input's cell/cap/bal orderings (positionally
deterministic, matching the JSON path), and packaged into `WStatusResult` for the C reader. -/

/-- The boundary RESULT: the post-state, the receipt-log length, and the three-way status code
(0=rejected, 1=prologue-only, 2=body-committed). Mirrors `encodeWStatusOut`'s three outputs without
the string. -/
structure WStatusResult where
  state  : WState
  loglen : Nat
  status : Nat

/-- Run the gated complete-turn executor on ALREADY-CONSTRUCTED Lean values. This is
`execFullForestAuthStep` with the JSON parse/encode shells removed — the admission/lift/run/read core
is byte-identical, so the produced post-state and status are exactly the JSON path's. -/
@[export dregg_exec_full_forest_auth_direct]
def execDirect (host : WHostCtx) (state : WState) (turn : WTurn) : WStatusResult :=
  let k0 := stateOfWState state
  let s0 : RecChainedState := { kernel := k0, log := [] }
  let cellIds := state.cells.map Prod.fst
  let capLabels := state.caps.map Prod.fst
  let balKeys := balKeysOf state
  let ctx := admCtxOfHost host
  let hdr := turnHdrOf turn.agent (eraseAuth turn.root) turn.nonce turn.fee turn.validUntil turn.prevHash
  let gforest : DForest := liftForestG turn.root
  let (st, res) := runGatedForestTurnStatus ctx hdr s0 gforest
  match res with
  | some s' =>
      { state := wstateOfState cellIds capLabels balKeys s'.kernel, loglen := s'.log.length,
        status := turnStatusCode st }
  | none =>
      { state := wstateOfState cellIds capLabels balKeys s0.kernel, loglen := 0,
        status := turnStatusCode st }

/-! ## MEASUREMENT instrumentation (additive, env-gated; zero exec-path change).

Two purely-additive `@[export]`s used by `perf/benches/lean_ffi_turn.rs` to attribute the fixed
per-call cost of the verified executor. NEITHER is on the production path (`run_direct` still calls
the unchanged `execDirect`); they are only invoked by the bench under `DREGG_LEAN_PROFILE=1`.

* `dregg_ffi_identity` — the BARE FFI-into-Lean floor: takes the same `WState` arg the executor takes
  and returns immediately (no exec). Timing a loop over it isolates the pure cost of crossing the
  C↔Lean boundary + the runtime/region/refcount setup, separate from any executor work.

* `dregg_exec_full_forest_auth_direct_profiled` — `execDirect` with `IO.monoNanosNow` fences between
  its four sub-phases (stateOfWState / liftForestG / runGatedForestTurnStatus / wstateOfState). The
  per-phase nanos are printed to stderr ONLY when `DREGG_LEAN_PROFILE=1`; the returned result is the
  identical `WStatusResult` the production `execDirect` returns (so the bench can also assert it). -/

/-- The bare identity floor: take the boundary `WState` and hand it straight back. The C side passes
the SAME built `WState` object the executor would consume; returning it (after the runtime's
inc/dec dance the boundary always pays) measures the pure cross-into-Lean + region cost with NO
executor work. -/
@[export dregg_ffi_identity]
def ffiIdentity (state : WState) : WState := state

/-- Force a `WState` to a cheap `Nat` fingerprint so a timed phase that produced it cannot be
elided / fused past the timestamp. Touches the list spines + scalar heads the projector built
(cells/bal/caps lengths + the head ids), which is O(structure) but tiny. -/
@[inline] private def wstateFingerprint (w : WState) : Nat :=
  w.cells.length + w.bal.length + w.caps.length + w.nullifiers.length
    + w.commitments.length + w.revoked.length
    + (w.cells.head?.map (·.1)).getD 0

/-- `execDirect` instrumented with monotonic-clock fences between the four sub-phases. Returns the
SAME `WStatusResult` as `execDirect`. Prints `DREGG_LEAN_PROFILE` ns lines only when the env var is
`1`. The phase results are forced (via `wstateFingerprint` / `.length` / a status read) between
`IO.monoNanosNow` reads so the strict per-phase work lands inside its measured window. -/
def execDirectProfiledIO (host : WHostCtx) (state : WState) (turn : WTurn) : IO WStatusResult := do
  let on := (← IO.getEnv "DREGG_LEAN_PROFILE") == some "1"
  -- pre-phase scalars the projector needs (kept out of the timed phases; cheap list maps)
  let cellIds := state.cells.map Prod.fst
  let capLabels := state.caps.map Prod.fst
  let balKeys := balKeysOf state
  let ctx := admCtxOfHost host
  let hdr := turnHdrOf turn.agent (eraseAuth turn.root) turn.nonce turn.fee turn.validUntil turn.prevHash
  -- (a) stateOfWState — rebuild the function-backed RecordKernelState from the wire.
  let t0 ← IO.monoNanosNow
  let k0 := stateOfWState state
  let s0 : RecChainedState := { kernel := k0, log := [] }
  -- force the kernel record to WHNF (allocates the closure-backed state record).
  let _ := s0.log.length
  let t1 ← IO.monoNanosNow
  -- (b) liftForestG — lift the wire forest to the gated DForest.
  let gforest : DForest := liftForestG turn.root
  let _ ← (pure (sizeOf gforest) : IO Nat)  -- force the lifted tree fully (structural)
  let t2 ← IO.monoNanosNow
  -- (c) runGatedForestTurnStatus — admission predicate + prologue + the gated forest body.
  -- ADDITIVE finer split (env-gated print only): attribute the gate's ~7µs to its REAL components.
  -- NOTE the protocol fact this measures: the executor's admission/turn path computes NO Poseidon2 —
  -- `admissible` is pure nonce/balance/freeze/chain-head COMPARISONS (the receipt-chain check is a
  -- `Nat` equality `prevReceipt = storedHead`, where the hash `H : Receipt → Nat` is an ABSTRACT
  -- §8-oracle parameter never evaluated here), and `commitPrologue`/`execFullForestG` touch records,
  -- not a sponge. So this split has an `admissible` leg, a `commitPrologue` leg, and a `body` leg —
  -- there is no Poseidon2 leg to attribute.
  let c0 ← IO.monoNanosNow
  let adm := Dregg2.Exec.Admission.admissible ctx hdr s0
  let _ := decide (adm = true)  -- force the predicate
  let c1 ← IO.monoNanosNow
  let sP := Dregg2.Exec.Admission.commitPrologue s0 hdr.agent hdr.fee
  let _ := sP.log.length  -- force the prologue state to WHNF
  let c2 ← IO.monoNanosNow
  let bodyRes := Dregg2.Exec.FullForestAuth.execFullForestG sP gforest
  let _ := bodyRes.isSome  -- force the body
  let c3 ← IO.monoNanosNow
  let (st, res) := runGatedForestTurnStatus ctx hdr s0 gforest
  let _ := turnStatusCode st  -- force the status
  let t3 ← IO.monoNanosNow
  -- (d) wstateOfState — project the post-kernel back out into the wire WState.
  let result : WStatusResult :=
    match res with
    | some s' =>
        { state := wstateOfState cellIds capLabels balKeys s'.kernel, loglen := s'.log.length,
          status := turnStatusCode st }
    | none =>
        { state := wstateOfState cellIds capLabels balKeys s0.kernel, loglen := 0,
          status := turnStatusCode st }
  let _ := wstateFingerprint result.state  -- force the projected WState spine
  let t4 ← IO.monoNanosNow
  if on then
    IO.eprintln s!"DREGG_LEAN_PROFILE stateOfWState={t1 - t0}ns liftForestG={t2 - t1}ns \
runGatedForestTurnStatus={t3 - t2}ns wstateOfState={t4 - t3}ns total={t4 - t0}ns"
    -- finer gate split: admissible (pure comparisons, NO Poseidon2) / commitPrologue / forest body.
    IO.eprintln s!"DREGG_GATE_SPLIT admissible={c1 - c0}ns commitPrologue={c2 - c1}ns \
body_execFullForestG={c3 - c2}ns poseidon2=0ns"
  pure result

/-- Pure-typed `@[export]` wrapper: runs the instrumented `execDirectProfiledIO` via `unsafeIO` so
the Rust caller sees the SAME `WStatusResult → lean_object*` ABI as `execDirect` (no `IO` world
token to thread). The `unsafeIO` only performs the env-read + timestamp reads + an optional
`eprintln`; on any IO error it falls back to the pure `execDirect`. -/
@[export dregg_exec_full_forest_auth_direct_profiled]
unsafe def execDirectProfiled (host : WHostCtx) (state : WState) (turn : WTurn) : WStatusResult :=
  match unsafeIO (execDirectProfiledIO host state turn) with
  | .ok r => r
  | .error _ => execDirect host state turn

/-! ## RESULT readers (project `WStatusResult` + the post-`WState` back to C scalars).

The C side reads the WHOLE post-state out while still inside the FFI call, then decrefs the result. The
post-state `bal`/`cells`/`caps` are read at the SAME orderings the input listed (the JSON path's
contract), so the C side iterates each list by length + index. -/

@[export dregg_d_res_status] def resStatus (r : WStatusResult) : UInt64 := UInt64.ofNat r.status
@[export dregg_d_res_loglen] def resLoglen (r : WStatusResult) : UInt64 := UInt64.ofNat r.loglen
@[export dregg_d_res_state]  def resState  (r : WStatusResult) : WState := r.state

/-- `Int → (mag : UInt64, neg : Bool)` reader: the C side reads the magnitude and sign separately
(the wire/kernel `bal`/value ints can be negative). -/
@[export dregg_d_int_mag] def intMag (i : Int) : UInt64 := UInt64.ofNat i.natAbs
@[export dregg_d_int_neg] def intNeg (i : Int) : Bool := i < 0

/-! ### `WState` field/list readers (length + indexed access). -/

@[export dregg_d_st_cells]       def stCells (w : WState) : List (CellId × Value) := w.cells
@[export dregg_d_st_caps]        def stCaps (w : WState) : List (CellId × List Cap) := w.caps
@[export dregg_d_st_bal]         def stBal (w : WState) : List (CellId × AssetId × Int) := w.bal
@[export dregg_d_st_nullifiers]  def stNullifiers (w : WState) : List Nat := w.nullifiers
@[export dregg_d_st_commitments] def stCommitments (w : WState) : List Nat := w.commitments
@[export dregg_d_st_revoked]     def stRevoked (w : WState) : List Nat := w.revoked
@[export dregg_d_st_lifecycle]   def stLifecycle (w : WState) : List (CellId × Nat) := w.lifecycle
@[export dregg_d_st_deathcert]   def stDeathCert (w : WState) : List (CellId × Nat) := w.deathCert
@[export dregg_d_st_delegate]    def stDelegate (w : WState) : List (CellId × Nat) := w.delegate

/-! ### `List Nat` reader. -/

@[export dregg_d_natlist_len]  def natListLen (xs : List Nat) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_natlist_get]  def natListGet (xs : List Nat) (i : UInt64) : UInt64 :=
  UInt64.ofNat ((xs[i.toNat]?).getD 0)

/-! ### `cells` reader: each entry is `(CellId, Value)`. -/

@[export dregg_d_cells_len] def cellsLen (xs : List (CellId × Value)) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_cells_id]  def cellsId (xs : List (CellId × Value)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map Prod.fst).getD 0)
@[export dregg_d_cells_val] def cellsVal (xs : List (CellId × Value)) (i : UInt64) : Value :=
  ((xs[i.toNat]?).map Prod.snd).getD (.int 0)

/-! ### `Value` reader: tag + payload projections. Tag 0=int 1=dig 2=sym 3=record. -/

@[export dregg_d_value_tag] def valueTag : Value → UInt64
  | .int _ => 0 | .dig _ => 1 | .sym _ => 2 | .record _ => 3
@[export dregg_d_value_int_get] def valueIntGet : Value → Int
  | .int i => i | _ => 0
@[export dregg_d_value_nat_get] def valueNatGet : Value → UInt64
  | .dig n => UInt64.ofNat n | .sym n => UInt64.ofNat n | _ => 0
@[export dregg_d_value_record_get] def valueRecordGet : Value → List (FieldName × Value)
  | .record fs => fs | _ => []

@[export dregg_d_fieldlist_len]  def fieldListLen (xs : List (FieldName × Value)) : UInt64 :=
  UInt64.ofNat xs.length
@[export dregg_d_fieldlist_name] def fieldListName (xs : List (FieldName × Value)) (i : UInt64) : String :=
  ((xs[i.toNat]?).map Prod.fst).getD ""
@[export dregg_d_fieldlist_val]  def fieldListVal (xs : List (FieldName × Value)) (i : UInt64) : Value :=
  ((xs[i.toNat]?).map Prod.snd).getD (.int 0)

/-! ### `bal` reader: each entry is `(cell, asset, amt)`. -/

@[export dregg_d_bal_len]   def balLen (xs : List (CellId × AssetId × Int)) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_bal_cell]  def balCell (xs : List (CellId × AssetId × Int)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map (fun p => p.1)).getD 0)
@[export dregg_d_bal_asset] def balAsset (xs : List (CellId × AssetId × Int)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map (fun p => p.2.1)).getD 0)
@[export dregg_d_bal_amt]   def balAmt (xs : List (CellId × AssetId × Int)) (i : UInt64) : Int :=
  ((xs[i.toNat]?).map (fun p => p.2.2)).getD 0

/-! ### `caps` reader: each entry is `(holder, List Cap)`. -/

@[export dregg_d_caps_len]    def capsLen (xs : List (CellId × List Cap)) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_caps_holder] def capsHolder (xs : List (CellId × List Cap)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map Prod.fst).getD 0)
@[export dregg_d_caps_clist]  def capsClist (xs : List (CellId × List Cap)) (i : UInt64) : List Cap :=
  ((xs[i.toNat]?).map Prod.snd).getD []

@[export dregg_d_caplist_len] def capListLen (xs : List Cap) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_caplist_get] def capListGet (xs : List Cap) (i : UInt64) : Cap := (xs[i.toNat]?).getD Cap.null

@[export dregg_d_cap_tag] def capTag : Cap → UInt64
  | .null => 0 | .endpoint _ _ => 1 | .node _ => 2
@[export dregg_d_cap_target] def capTarget : Cap → UInt64
  | .endpoint t _ => UInt64.ofNat t | .node t => UInt64.ofNat t | .null => 0
@[export dregg_d_cap_rights] def capRights : Cap → List Auth
  | .endpoint _ r => r | _ => []

@[export dregg_d_authlist_len] def authListLen (xs : List Auth) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_authlist_get] def authListGet (xs : List Auth) (i : UInt64) : UInt8 :=
  match (xs[i.toNat]?).getD Auth.read with
  | .read => 0 | .write => 1 | .grant => 2 | .call => 3
  | .reply => 4 | .reset => 5 | .control => 6 | .notify => 7

/-! ### per-cell `[cell,val]` table reader (lifecycle / deathCert / delegate). -/

@[export dregg_d_cellnats_len]  def cellNatsLen (xs : List (CellId × Nat)) : UInt64 := UInt64.ofNat xs.length
@[export dregg_d_cellnats_cell] def cellNatsCell (xs : List (CellId × Nat)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map Prod.fst).getD 0)
@[export dregg_d_cellnats_val]  def cellNatsVal (xs : List (CellId × Nat)) (i : UInt64) : UInt64 :=
  UInt64.ofNat (((xs[i.toNat]?).map Prod.snd).getD 0)

/-! ## Differential self-check (Lean-side): the DIRECT path agrees with the JSON export.

`execDirect` on the parsed `(host,state,turn)` of a wire produces the SAME `(state, loglen, status)`
the JSON `execFullForestAuthStep` re-encodes — proof the two share one core. We compare on the
re-encoded post-state string (no `BEq` on `WState`) + loglen + status code. -/

private def directMatchesJson (input : String) : Bool :=
  match parseWWire input with
  | none => false
  | some w =>
      let r := execDirect w.host w.state w.turn
      let jsonOut := execFullForestAuthStep input
      let directOut := encodeWStatusOut r.state r.loglen
        (match r.status with
         | 2 => TurnStatus.bodyCommitted
         | 1 => TurnStatus.prologueCommittedBodyFailed
         | _ => TurnStatus.rejected)
      directOut == jsonOut

-- the genuine-credential gated demo: direct == JSON (both commit, identical post-state):
#guard (directMatchesJson gatedDemoInput)
-- the forged-credential demo: direct == JSON (both roll back, identical echoed state + status):
#guard (directMatchesJson forgedGatedInput)
-- the satisfied/violated caveat demos: the caveat leg agrees through the direct path too:
#guard (directMatchesJson satisfiedCaveatInput)
#guard (directMatchesJson violatedCaveatInput)

end Dregg2.Exec.FFIDirect
