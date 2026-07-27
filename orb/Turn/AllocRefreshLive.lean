/-
# AllocRefreshLive — driving the PROVEN TURN allocation Refresh over bytes (RFC 8656 §7/§8)

`TurnLive` wired ALLOCATE (default-deny), `TurnPermLive` wired the two grant paths
(CREATE-PERMISSION §9 / CHANNEL-BIND §11), and `ChannelDataLive` wired the
ChannelData relay (§12). This lane wires the allocation **Refresh** transition
(RFC 8656 §7, message layout §8): the client periodically re-asserts an
allocation, and the server's LIFETIME response decides its fate —

  * a **positive** lifetime *extends* the allocation, moving its absolute expiry
    forward to `now + lifetime` while leaving every permission and channel
    binding untouched (§7.1: a refresh changes only the timer);
  * a **zero** lifetime *deletes* the allocation (§7: "a Refresh request with a
    REQUESTED-LIFETIME of 0 … is used to delete an allocation").

and proves the two properties a Refresh must have:

  1. `refresh_extends` — refreshing a live allocation with a positive lifetime
     re-binds it with `expiry = now + lifetime`, the refreshed allocation is
     `active` at `now` (it has been pushed into the future), and its relayed
     address / permissions / channel bindings are carried over verbatim (a
     refresh is not a re-allocation — it does not reset the grant state).

  2. `refresh_zero_deletes` — refreshing with lifetime 0 removes the allocation:
     a subsequent lookup finds nothing and it is not `active`. This is the §7
     teardown clause; it is what `deallocate` (Refresh, LIFETIME=0) relies on.

Both compose the proven `Turn.lean` state machine (`refresh`, `allocate`,
`createPermission`, `channelBind`, `active`, `TurnState.lookup/insert/remove`,
`lookup_insert`) — no forked transition. The selftest additionally drives the
lifetime **off the wire**: it builds the proven `refreshRequestMsg`, parses it
with the proven STUN `parse`, recovers the LIFETIME attribute, and feeds that
recovered value into the model `refresh` — so the number that decides
extend-vs-delete is the one carried by the RFC 8656 §8 byte layout, not a
side-channel.

## Honesty / realization boundary (the ChannelDataLive / TurnPermLive discipline)

This is **drorb-native**: a client and a relay speaking the modelled RFC 8656
Refresh wire format over the byte level in ONE process (no sockets), NOT a real
UDP interop against a third-party TURN server, and NOT the deployed HTTP
dataplane — TURN is a UDP relay method with no curl-able HTTP surface, so there
is no deployed endpoint to GET (a real boundary, stated: the drorb serve does
not emit TURN refresh over HTTP; the correspondence is byte-level). It is a live
cross-check (rung 2, a selftest), NOT the deployed serve. Everything
structural/codec/transition is the proven Lean; the selftest calls the proven
Lean functions on real bytes and cross-checks each decision against the model.
It exercises NO MESSAGE-INTEGRITY and NO crypto, so it runs under the pure Lean
interpreter (`lake env lean --run`) with zero linked crypto — no `@[extern]`
opaque is referenced by this file.

Deployed-engine correspondence: the extend-vs-delete decision modelled here — a
positive LIFETIME re-arms the expiry timer and preserves the grant state, a
LIFETIME of 0 tears the allocation down — matches the native TURN engine's
`refresh` / `deallocate` (deallocate = REFRESH carrying `LifeTime::new(0)`), so
the row's claim holds of the real relay logic, not merely of the model.

Usage:
  alloc-refresh-live selftest
-/
import Turn

namespace Turn.AllocRefreshLive

open Stun (Bytes Endpoint Attr Message)
open Stun
open Turn

/-! ## A `remove` lookup lemma

`Turn.lean` proves `lookup_insert` but not the dual for `remove`; the deletion
half of Refresh needs it. Looking up a 5-tuple in `s.remove ft` is always
`none`: `remove` filters out every entry whose key `= ft`, so `find?` for a
key `= ft` matches nothing. -/
theorem lookup_remove (s : TurnState) (ft : FiveTuple) :
    (s.remove ft).lookup ft = none := by
  simp only [TurnState.remove, TurnState.lookup, Option.map_eq_none_iff]
  rw [List.find?_eq_none]
  intro x hx
  have hfilt : decide (x.1 ≠ ft) = true := (List.mem_filter.mp hx).2
  simp only [ne_eq, decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at hfilt
  simp only [decide_eq_true_eq]
  exact hfilt

#print axioms Turn.AllocRefreshLive.lookup_remove

/-! ## Theorem 1 — a positive-lifetime Refresh extends the allocation (§7.1)

Given a live allocation `a` for `ft` and a positive `lifetime`, `refresh`:

* re-binds `ft` to `{ a with expiry := now + lifetime }` (only the timer moves);
* leaves that allocation `active` at `now` (its new expiry is strictly in the
  future because `lifetime > 0`);
* preserves the relayed address, the permission set, and the channel bindings —
  a refresh is not a re-allocation, so the default-deny grant state survives.

Not a `P → P`: the hypotheses are a real live allocation (`lookup ft = some a`)
and a satisfiable positivity bound (`0 < lifetime`); the conclusions are a
concrete re-binding, an `active` fact that is FALSE for `lifetime = 0`, and a
verbatim carry-over of the grant fields. It composes `lookup_insert` and the
`refresh` / `active` definitions. -/
theorem refresh_extends
    (s : TurnState) (ft : FiveTuple) (a : Allocation) (now lifetime : Nat)
    (hlook : s.lookup ft = some a) (hpos : 0 < lifetime) :
    -- the allocation survives, its expiry pushed forward to now + lifetime
    (refresh s ft now lifetime).lookup ft = some { a with expiry := now + lifetime }
    -- and it is live at now (the refresh moved it into the future)
    ∧ active (refresh s ft now lifetime) ft now = some { a with expiry := now + lifetime }
    -- and the relayed address / permissions / channels are carried over verbatim
    ∧ (∃ a', (refresh s ft now lifetime).lookup ft = some a' ∧
        a'.relayed = a.relayed ∧ a'.perms = a.perms ∧ a'.channels = a.channels) := by
  have hne : ¬ (lifetime = 0) := by omega
  have hstep : refresh s ft now lifetime = s.insert ft { a with expiry := now + lifetime } := by
    unfold refresh; rw [hlook]; simp [hne]
  have h1 : (refresh s ft now lifetime).lookup ft = some { a with expiry := now + lifetime } := by
    rw [hstep]; exact lookup_insert s ft _
  refine ⟨h1, ?_, ?_⟩
  · unfold active
    rw [h1]
    have hlt : now < now + lifetime := by omega
    simp only [decide_eq_true_eq]
    rw [if_pos hlt]
  · exact ⟨_, h1, rfl, rfl, rfl⟩

#print axioms Turn.AllocRefreshLive.refresh_extends

/-! ## Theorem 2 — a zero-lifetime Refresh deletes the allocation (§7)

Refreshing a live allocation with `lifetime = 0` removes it: the subsequent
lookup is `none` and it is not `active`. This is the RFC 8656 §7 teardown clause
(a Refresh with LIFETIME 0 deletes the allocation), the semantics the client's
`deallocate` relies on.

Not a `P → P`: the hypothesis is a real live allocation; the conclusion is that
after a zero-lifetime refresh the allocation is GONE — the opposite of
`refresh_extends`. It composes `lookup_remove` and the `refresh` / `active`
definitions. -/
theorem refresh_zero_deletes
    (s : TurnState) (ft : FiveTuple) (a : Allocation) (now : Nat)
    (hlook : s.lookup ft = some a) :
    (refresh s ft now 0).lookup ft = none
    ∧ active (refresh s ft now 0) ft now = none := by
  have hstep : refresh s ft now 0 = s.remove ft := by
    unfold refresh; rw [hlook]; simp
  have h1 : (refresh s ft now 0).lookup ft = none := by
    rw [hstep]; exact lookup_remove s ft
  refine ⟨h1, ?_⟩
  · unfold active; rw [h1]

#print axioms Turn.AllocRefreshLive.refresh_zero_deletes

/-! ## Byte helpers (mirror ChannelDataLive/TurnPermLive) -/

def ipStr (b : Bytes) : String := ".".intercalate (b.map (fun x => toString x.toNat))

/-- Recover the LIFETIME (§8) from a parsed STUN/TURN message: find the
LIFETIME attribute and decode its 32-bit big-endian value with the proven
`decodeLifetime`. -/
def lifetimeOfMsg (m : Message) : Option Nat :=
  (m.attrs.find? (fun a => decide (a.type = attrLifetime))).bind (fun a => decodeLifetime a.value)

/-! ## The selftest — client + relay over the byte level, one process -/

def selftest : IO UInt32 := do
  IO.println "== alloc-refresh-live selftest : RFC 8656 §7/§8 allocation Refresh, byte-level =="

  -- The client 5-tuple, the relayed address, and two peers (drorb-native topology).
  let epClient : Endpoint := { family := 1, port := 51000, addr := [10, 0, 0, 1] }
  let epServer : Endpoint := { family := 1, port := 3478, addr := [10, 0, 0, 254] }
  let epRelay  : Endpoint := { family := 1, port := 49152, addr := [203, 0, 113, 7] }
  let epPeerA  : Endpoint := { family := 1, port := 6000, addr := [198, 51, 100, 20] }
  let ft : FiveTuple := { client := epClient, server := epServer, proto := protoUDP }
  let txid : Bytes := [0x21, 0x12, 0xA4, 0x42, 1, 2, 3, 4, 5, 6, 7, 8]

  -- ── setup: allocate at now=0 for 600s, grant a permission + a channel bind ──
  let now0 : Nat := 1000
  let s0 := allocate TurnState.empty ft epRelay now0 600
  let s1 := createPermission s0 ft epPeerA.addr
  let s2 := channelBind s1 ft 0x4001 epPeerA
  let some aSet := s2.lookup ft
    | do IO.eprintln "server: allocation missing after setup"; return 1
  IO.println s!"\n-- setup: allocated relay={ipStr epRelay.addr}:{epRelay.port} at now={now0}, expiry={aSet.expiry} --"
  IO.println s!"   perms={aSet.perms.length} (peer A) channels={aSet.channels.length} (0x4001->A)"

  -- ── 1. WIRE: build a REFRESH request carrying LIFETIME=1200, parse it back ──
  let extendSecs : Nat := 1200
  let wire := refreshRequestMsg txid extendSecs
  let parsed := Stun.parse wire
  IO.println s!"\n-- wire (RFC 8656 §8: REFRESH request with LIFETIME attribute) --"
  match parsed with
  | none => do IO.eprintln "REFRESH request failed to parse (UNEXPECTED)"; return 1
  | some m =>
    IO.println s!"REFRESH request ({wire.length}B) parsed: typ=0x{Nat.toDigits 16 m.typ |>.asString}, attrs={m.attrs.length}"
    let lifeFromWire := lifetimeOfMsg m
    IO.println s!"   LIFETIME recovered off the wire = {lifeFromWire} (== {extendSecs} : {lifeFromWire == some extendSecs})"

    -- ── 2. EXTEND: refresh with the wire-recovered lifetime ──
    let now1 : Nat := 1500
    let lifeVal := lifeFromWire.getD 0
    let sExt := refresh s2 ft now1 lifeVal
    let extLookup := sExt.lookup ft
    let extActive := active sExt ft now1
    IO.println s!"\n-- extend (positive LIFETIME re-arms the timer, §7.1) --"
    match extLookup with
    | some a' =>
      IO.println s!"after refresh(now={now1}, lifetime={lifeVal}): expiry {aSet.expiry} -> {a'.expiry} (== {now1 + lifeVal} : {a'.expiry == now1 + lifeVal})"
      IO.println s!"   grant state preserved: relayed same={a'.relayed == aSet.relayed} perms={a'.perms.length} channels={a'.channels.length}"
    | none => IO.println "after refresh -> GONE (UNEXPECTED for positive lifetime)"
    let expiryMoved := (extLookup.map (·.expiry)) == some (now1 + lifeVal)
    let stillActive := extActive.isSome
    let grantKept :=
      match extLookup with
      | some a' => a'.relayed == aSet.relayed && a'.perms == aSet.perms && a'.channels == aSet.channels
      | none => false

    -- ── 3. DELETE: refresh with LIFETIME=0 tears the allocation down (§7) ──
    let wire0 := refreshRequestMsg txid 0
    let life0 := (Stun.parse wire0).bind lifetimeOfMsg
    let now2 : Nat := 2000
    let sDel := refresh sExt ft now2 (life0.getD 0)
    let delLookup := sDel.lookup ft
    let delActive := active sDel ft now2
    IO.println s!"\n-- delete (LIFETIME=0 deletes the allocation, §7) --"
    IO.println s!"   LIFETIME off the wire = {life0} (== some 0 : {life0 == some 0})"
    match delLookup with
    | some _ => IO.println "after refresh(lifetime=0) -> STILL PRESENT (UNEXPECTED)"
    | none   => IO.println "after refresh(lifetime=0) -> allocation deleted (lookup = none, not active)"
    let deleted := delLookup == none
    let notActive := delActive == none

    -- ── 4. faithfulness cross-check (realizes the two theorems) ──
    IO.println "\n-- cross-check (realizes refresh_extends + refresh_zero_deletes) --"
    IO.println s!"LIFETIME recovered from the §8 wire == requested       : {lifeFromWire == some extendSecs}"
    IO.println s!"positive refresh sets expiry := now + lifetime         : {expiryMoved}"
    IO.println s!"refreshed allocation is active at now                  : {stillActive}"
    IO.println s!"grant state (relayed/perms/channels) carried over      : {grantKept}"
    IO.println s!"LIFETIME=0 recovered from the wire                     : {life0 == some 0}"
    IO.println s!"zero-lifetime refresh deletes (lookup = none)          : {deleted}"
    IO.println s!"deleted allocation is not active                       : {notActive}"

    if lifeFromWire == some extendSecs && expiryMoved && stillActive && grantKept
        && life0 == some 0 && deleted && notActive then do
      IO.println "\nPASS — a positive-LIFETIME Refresh re-arms the expiry and keeps the grant state;"
      IO.println "       a LIFETIME=0 Refresh deletes the allocation. Both driven off the §8 wire."
      IO.println "TURN ALLOCATION REFRESH COMPLETE (drorb-native, byte-level, no crypto)."
      return 0
    else do
      IO.eprintln "\nFAIL — a stage of the Refresh transition did not cross-check."
      return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | [] | ["selftest"] => selftest
  | _ => do IO.eprintln "usage: alloc-refresh-live selftest"; return 1

end Turn.AllocRefreshLive

def main (args : List String) : IO UInt32 := Turn.AllocRefreshLive.main args
