/-
# Dregg2.Firmament.SeL4Kernel — the FORMAL LEAN SEMANTICS of the semihost seL4 microkernel.

`sel4/dregg-firmament/src/emulated_kernel.rs` is the EXECUTABLE: the `n = 1` `EmulatedKernel`,
the host-native backend for the rust-sel4 API surface (`docs/DREGG-DESKTOP-OS.md §3`, the
semihosted-seL4 KEYSTONE). ONE protection-domain source tree runs on this host emulator under
`cargo test` today and on real seL4 unchanged. The kernel PROMOTES `LocalBacking` (the real CNode
slot-table + mint/revoke derivation tree) by ADDING the three seL4 IPC primitives the desktop §3
spec calls for: a synchronous **Endpoint** (rendezvous), a **Notification** (badge-OR accumulator),
and **Untyped + Retype** (the kernel-enforced factory slot-caveat).

This module is the **formal semantics that executable refines** — the l4v data-refinement obligation
`Lean ⊑ Rust` (law #1: the desktop substrate's kernel semantics is proven from Lean, not just
asserted in Rust). Each theorem below is the refinement obligation FOR a named Rust function /
green Rust test, noted at the theorem. The Rust is the implementation; the Lean is the spec; the
correspondence is the obligation.

## We REUSE the existing dregg cap metatheory and the SIBLING firmament model (the WELD method)

The seL4 cap space rides the EXISTING attenuation lattice. We import:

  * `Dregg2.Exec.CapTPConcrete.AuthReq` — the concrete `AuthRequired` carrier
    (`none`/`signature`/`proof`/`either`/`impossible`/`custom`), the SAME `Rights =
    dregg_cell::AuthRequired` the emulator's CNode slots carry (`local.rs:36`);
  * `Dregg2.Exec.CapTPConcrete.authNarrowerOrEqual` — THE decision `granted ⊆ held` (the Rust
    `is_attenuation` / `AuthRequired::is_narrower_or_equal`, clause-for-clause), already proven a
    genuine partial order (reflexive / antisymmetric / transitive; `impossible` ⊥, `none` ⊤);
  * the SIBLING `Dregg2.Firmament.CapGradation` — `grantOk held granted := authNarrowerOrEqual
    granted held`, the ONE non-amplification decision, REUSED verbatim for the kernel's `mint`
    gate (a `seL4_CNode_Mint` gates on EXACTLY the same predicate the firmament router does).

The `EmulatedKernel::mint` (`emulated_kernel.rs:266`, forwarding to `LocalBacking::mint`,
`local.rs:106`) gates on `is_attenuation(p.rights, narrower)` — so our `mint` gates on
`grantOk parent.rights narrower = authNarrowerOrEqual narrower parent.rights`, the SAME predicate.
The whole point is that "an seL4 CNode mint enforces the identical `granted ⊆ held` law the
distributed delegate does" is a THEOREM, not a slogan.

The protocol-level revocation precedent is `Dregg2.Distributed.Revocation` (the topology-parametrized
`eventual_bounded_revocation` / `single_machine_collapse`); that model lives over the CREDENTIAL
revocation registry (a G-Set + propagation delay). The seL4 kernel's revoke is a DIFFERENT, simpler
structure — the synchronous **derivation-tree** revoke (`minted_from`) under the n=1 collapse, with
NO propagation delay at all (`delay ≡ 0` already; one `Mutex`-guarded removal). We model it directly
here as the transitive-subtree removal, and prove it is the n=1 immediate-dark property in the form
the kernel actually realizes it.

## What is proven (each mirrors a green Rust test as a Lean theorem)

  1. **MINT-ATTENUATES-REFUSES-AMPLIFICATION** — `mint` installs a child cap with rights `≤` the
     parent's (`authNarrowerOrEqual`); a mint that would amplify is REFUSED (`none`). (Refinement of
     `EmulatedKernel::mint` / `LocalBacking::mint`, `local.rs:106`; exercised by
     `mint_attenuates_and_refuses_amplification` / `promoted_cnode_mint_revoke_still_green`.)
  2. **REVOKE-SYNCHRONOUS-TRANSITIVE** — `revoke` removes the cap AND its entire derived subtree
     atomically: no in-flight survivor, the n=1 immediate-dark property — every descendant is dead
     the instant `revoke` returns. (Refinement of `EmulatedKernel::revoke` / `LocalBacking::revoke`,
     `local.rs:127`; exercised by `revoke_is_synchronous_and_transitive` /
     `bounds_local_is_genuinely_real_synchronous_revoke`.)
  3. **RETYPE-MINTS-EXACTLY-DECLARED** — `retype` yields exactly the declared `ObjectType`, only
     within budget; a wrong-type retype REFUSES (`WrongType`), an over-budget retype REFUSES
     (`Exhausted`) — the `DirectoryFactory → Untyped_Retype` slot-caveat as a theorem. (Refinement of
     `EmulatedKernel::retype`, `emulated_kernel.rs:328`; exercised by
     `retype_mints_only_the_declared_type` / `retype_exhausts_the_untyped_budget`.)
  4. **ENDPOINT rendezvous** — a `Recv` observes EXACTLY the `Call`'s message, and the reply the
     `Call` receives is EXACTLY the one the server parked for THIS call (matched by generation), with
     no buffering (the endpoint is a meeting point). (Refinement of `EmulatedKernel::recv`/`reply`/
     `call`/`call_served_by`, `emulated_kernel.rs:452`+; exercised by
     `endpoint_call_recv_reply_rendezvous_cross_thread`.)
  5. **NOTIFICATION badge-OR** — a `Wait` (after a sequence of `Signal`s) observes the bitwise-OR of
     all signalled badges since the last wait, then the object resets to zero (read-and-clear).
     (Refinement of `EmulatedKernel::signal`/`wait`/`poll_notification`, `emulated_kernel.rs:388`+;
     exercised by `notification_badge_or_accumulates_and_clears` /
     `notification_wait_blocks_until_signalled_cross_thread`.)

NON-VACUITY both polarities (`#guard` teeth that BITE): a valid mint COMMITS attenuated; an amplifying
mint REFUSES; a correct retype yields the type; a wrong-type / over-budget retype REFUSES; a real
rendezvous round-trips a non-trivial message; a badge-OR of distinct bits accumulates then clears. A
concrete `CellId := Nat` (here a slot/object id is already `Nat`, matching the Rust `u32`/`u64`) is
used ONLY for the executable witnesses; it is never load-bearing in a proof.

Discipline: axiom-clean (`#assert_all_clean` at the close), no `sorry`, no `native_decide` — `decide`
/ `#guard` / structural `cases <;> simp` only. `lake build` green (LOCAL).
-/
import Dregg2.Exec.CapTPConcrete
import Dregg2.Firmament.CapGradation
import Dregg2.Tactics

namespace Dregg2.Firmament.SeL4Kernel

open Dregg2.Exec.CapTPConcrete (AuthReq authNarrowerOrEqual)
open Dregg2.Firmament (grantOk)

/-! ## §0 — Identities.

A `SlotId` names a CNode slot (the Rust `u32` slot index, `local.rs`); an `ObjId` names a retyped
kernel object / shared region (the Rust `u64` `ObjectId`, `emulated_kernel.rs:106`). Both are `Nat`
here — and that is FAITHFUL, not a shortcut: the real `EmulatedKernel` hands out monotonic numeric
ids (`alloc_id`, `next_slot`), they ARE machine integers, not abstract cell-hashes. (Contrast
`CapGradation`'s `CellId`, which is a value-hash and stays abstract; a CNode slot is genuinely a
small integer index.) -/

/-- A CNode slot index — the Rust `u32` slot (`LocalBacking`'s `BTreeMap<u32, Slot>` key). -/
abbrev SlotId := Nat

/-- A retyped-object / region id — the Rust `u64` `ObjectId` (`emulated_kernel.rs:106`). -/
abbrev ObjId := Nat

/-! ## §1 — The CNode: the slot-table + the mint/revoke derivation tree.

Mirrors `LocalBacking` (`local.rs:50`): a `BTreeMap<u32, Slot>` where each `Slot` carries
`rights : Rights`, an `object` label, and `minted_from : Option<u32>` (the derivation edge —
`None` = an original cap, `Some parent` = a child minted from `parent`). `mint` installs an
attenuated child; `revoke` removes a slot and its TRANSITIVE mint-descendants. We model the table
as an association list keyed by `SlotId` (decidable, computable, `#guard`-able) and the operations
as pure state transitions — the functional spec the `Mutex`-guarded Rust refines. -/

/-- One CNode slot — a kernel object the PD holds a cap to. Mirrors the Rust `Slot` (`local.rs:35`):
the held `rights` (the SAME `AuthReq = dregg_cell::AuthRequired` lattice), an `object` label (the
endpoint name / frame paddr the syscall would touch), and `mintedFrom` (the derivation parent —
`none` = an original `install`ed cap, `some p` = minted from slot `p`). -/
structure Slot where
  /-- The held rights — the seL4 cap rights, the REAL dregg `AuthReq`. -/
  rights : AuthReq
  /-- The underlying kernel object's label (an endpoint name, a frame paddr…). -/
  object : String
  /-- The derivation parent: `none` for an original cap, `some p` for a cap minted from slot `p`.
  A `revoke` of `p` removes every slot transitively `mintedFrom` `p`. -/
  mintedFrom : Option SlotId
  deriving Repr, DecidableEq

/-- The CNode cap space — the slot-table + the next free slot id. Mirrors `LocalBacking`
(`local.rs:52`): `slots : BTreeMap<u32, Slot>` (here an assoc list) + `next_slot : u32`. The
derivation tree lives in the slots' `mintedFrom` edges; the table IS the tree. -/
structure CNode where
  /-- The slot table: `SlotId ↦ Slot`. (An assoc list — at most one entry per id, an invariant the
  monotone `nextSlot` allocator maintains; `install`/`mint` only ever insert a FRESH id.) -/
  slots : List (SlotId × Slot)
  /-- The next free slot id (monotone, kernel-minted) — `next_slot`. -/
  nextSlot : SlotId
  deriving Repr

namespace CNode

/-- A fresh, empty CNode — `LocalBacking::new` (`local.rs:60`). -/
def empty : CNode := { slots := [], nextSlot := 0 }

/-- Look up the slot at `s`, if live. Mirrors `slots.get(&slot)`. -/
def get (cn : CNode) (s : SlotId) : Option Slot :=
  (cn.slots.find? (fun p => p.1 == s)).map Prod.snd

/-- Is a cap LIVE at slot `s`? (Post-revoke: `false` immediately — the n=1 immediacy.) Mirrors
`LocalBacking::is_live` (`local.rs:151`). -/
def isLive (cn : CNode) (s : SlotId) : Bool := (cn.get s).isSome

/-- The rights held at `s`, if any. Mirrors `LocalBacking::rights_at` (`local.rs:156`). -/
def rightsAt (cn : CNode) (s : SlotId) : Option AuthReq := (cn.get s).map Slot.rights

/-- **`install obj r`** — install an ORIGINAL cap (`mintedFrom = none`) over object `obj` with
rights `r` at the next free slot, returning the new slot id and the updated CNode. Mirrors
`LocalBacking::install` (`local.rs:67`): the firmament minting a cap into a PD's CNode at CapDL
boot. -/
def install (cn : CNode) (obj : String) (r : AuthReq) : SlotId × CNode :=
  let s := cn.nextSlot
  (s, { slots := (s, { rights := r, object := obj, mintedFrom := none }) :: cn.slots,
        nextSlot := s + 1 })

/-- **`mint parent narrower`** — `seL4_CNode_Mint` with reduced rights: derive a CHILD cap at a new
slot over the SAME object with `narrower` rights, gated on the REAL `granted ⊆ held` law. Returns
`none` if `parent` is dead OR the mint would AMPLIFY (`¬ grantOk parent.rights narrower`), else
`some (childSlot, cn')` with the child installed `mintedFrom = some parent`. Mirrors
`EmulatedKernel::mint` → `LocalBacking::mint` (`local.rs:106`):
`if !is_attenuation(&p.rights, &narrower) { None } else { … minted_from: Some(parent) … }`. -/
def mint (cn : CNode) (parent : SlotId) (narrower : AuthReq) : Option (SlotId × CNode) :=
  match cn.get parent with
  | none => none
  | some p =>
    if grantOk p.rights narrower then
      let s := cn.nextSlot
      some (s, { slots := (s, { rights := narrower, object := p.object,
                                mintedFrom := some parent }) :: cn.slots,
                 nextSlot := s + 1 })
    else
      none

/-! ### The transitive-revoke set (`minted_from` closure).

`LocalBacking::revoke` (`local.rs:127`) collects the slot + EVERY slot transitively minted from it
(a worklist over the `minted_from` edges) and removes them all. We compute that doomed set as a
fuel-bounded transitive closure. The fuel is the slot-count (the derivation tree has at most that
many nodes, so the closure saturates within `|slots|` rounds) — total, decidable, no well-founded
recursion needed, and the kernel's `while i < doomed.len()` loop terminates for the same reason. -/

/-- The DIRECT children of a set `roots` of slots: every live slot whose `mintedFrom` is in `roots`.
One round of the worklist. -/
def directChildren (cn : CNode) (roots : List SlotId) : List SlotId :=
  (cn.slots.filter (fun p => match p.2.mintedFrom with
                              | some m => roots.contains m
                              | none => false)).map Prod.fst

/-- One round of closure growth: union the current frontier with its direct children. -/
def expand (cn : CNode) (cur : List SlotId) : List SlotId :=
  cur ++ (directChildren cn cur).filter (fun c => ¬ cur.contains c)

/-- Fuel-bounded transitive closure of the `mintedFrom` relation from `roots`: iterate `expand`
`fuel` times. With `fuel = |slots|` the closure saturates (each round adds ≥ 1 node until fixpoint,
and there are at most `|slots|` nodes). -/
def closureFueled (cn : CNode) (roots : List SlotId) : Nat → List SlotId
  | 0 => roots
  | n + 1 => closureFueled cn (expand cn roots) n

/-- **`doomedSet s`** — the slot `s` plus its entire transitive mint-subtree: the set
`LocalBacking::revoke` removes. Fuel = `|slots|` (saturates). Mirrors the Rust worklist
(`local.rs:128`–`139`). -/
def doomedSet (cn : CNode) (s : SlotId) : List SlotId :=
  closureFueled cn [s] cn.slots.length

/-- **`revoke s`** — `seL4_CNode_Revoke`: SYNCHRONOUS, immediate, transitive. Remove `s` AND its
whole derived subtree (`doomedSet s`) atomically; return the count removed and the updated CNode.
There is no in-flight window — the cap and every descendant are gone the instant this returns (the
n=1 immediacy under the held kernel `Mutex`). Mirrors `EmulatedKernel::revoke` → `LocalBacking::revoke`
(`local.rs:127`). -/
def revoke (cn : CNode) (s : SlotId) : Nat × CNode :=
  let doomed := cn.doomedSet s
  let kept := cn.slots.filter (fun p => ¬ doomed.contains p.1)
  let removed := cn.slots.length - kept.length
  (removed, { slots := kept, nextSlot := cn.nextSlot })

end CNode

/-! ## §2 — The Notification: the badge-OR accumulator.

Mirrors `Notification` (`emulated_kernel.rs:138`): one `badge : u64` accumulator. `Signal` ORs the
signaller's badge in; `Wait`/`poll` reads-and-clears (returns the OR of all signals since the last
wait, resets to zero). We model the accumulator as a `Nat` and the badge-OR as `Nat`-bitwise-or
(`Nat.lor`, `|||`); `signal`/`wait` are pure transitions on it — the functional spec the condvar-
backed Rust realizes (the BLOCKING is a scheduling concern; the observable VALUE is this). -/

/-- A Notification object — the badge-OR accumulator (`badge : u64`). Mirrors `Notification`
(`emulated_kernel.rs:138`). -/
structure Notification where
  /-- The OR-accumulated badge of all signals since the last successful wait. -/
  badge : Nat
  deriving Repr, DecidableEq

namespace Notification

/-- A fresh notification — `Notification::default` (badge `0`). -/
def empty : Notification := { badge := 0 }

/-- **`signal n badge`** — `seL4_Signal`: OR `badge` into the accumulator. Non-blocking (a signal
never parks). Mirrors `EmulatedKernel::signal` (`emulated_kernel.rs:388`): `n.badge |= badge`. -/
def signal (n : Notification) (badge : Nat) : Notification := { badge := n.badge ||| badge }

/-- **`wait n`** — `seL4_Wait`: read-and-clear. Returns the accumulated badge (the OR of all signals
since the last wait) and the RESET notification (badge `0`). The blocking-until-nonzero is the
scheduling shape; the observable result is this read-and-clear pair. Mirrors `EmulatedKernel::wait`
(`emulated_kernel.rs:403`, the `badge = n.badge; n.badge = 0; return badge`) and the non-blocking
`poll_notification` (`emulated_kernel.rs:422`) identically (same value semantics). -/
def wait (n : Notification) : Nat × Notification := (n.badge, { badge := 0 })

/-- Fold a sequence of signals into a notification — the kernel state after `signal`ing each badge
in `badges` in order (what the accumulator holds when a `Wait` finally runs). -/
def signalAll (n : Notification) (badges : List Nat) : Notification :=
  badges.foldl signal n

end Notification

/-! ## §3 — The Endpoint: the synchronous rendezvous.

Mirrors `Endpoint` (`emulated_kernel.rs:117`): a meeting point with at most a rendezvous's worth of
state (`pending_call`/`pending_reply` + `call_gen`/`reply_gen` so a caller waits for ITS reply). A
`Call` parks a message, a `Recv` takes it (observing EXACTLY it) and returns a `ReplyToken`
generation-bound to the call, a `Reply` parks the reply for that generation, and the `Call` returns
EXACTLY that reply. There is NO buffering — the endpoint is a meeting point, not a queue.

The Rust realizes the cross-thread rendezvous with a condvar; the OBSERVABLE round-trip (recv sees
the call message; the caller gets the matched reply) is captured here as pure relational/functional
specs. We model both the cross-thread staging (`recv` then `reply` matched by generation) AND the
emulator's inline `call_served_by` (`emulated_kernel.rs:528`), and prove the message round-trips. -/

/-- An IPC message — a label + a byte payload. Mirrors `Message` (`emulated_kernel.rs:166`): the
`seL4` `MessageInfo` label + the IPC-buffer message-register bytes. -/
structure Message where
  /-- The message label (the `MessageInfo` tag the receiver dispatches on). -/
  label : Nat
  /-- The inline message bytes (the message-register payload). -/
  bytes : List Nat
  deriving Repr, DecidableEq

/-- A synchronous Endpoint — the rendezvous state. Mirrors `Endpoint` (`emulated_kernel.rs:117`):
`pendingCall`/`pendingReply` (the in-flight rendezvous, `none` = nobody parked) + `callGen`/`replyGen`
(the generations so a caller waits for ITS reply). -/
structure Endpoint where
  /-- The in-flight call message awaiting a receiver (`none` = no caller parked). -/
  pendingCall : Option Message
  /-- The reply the receiver parked for the caller (`none` = not yet replied). -/
  pendingReply : Option Message
  /-- A monotone call generation — bumped on each `call` so a reply binds to THIS call. -/
  callGen : Nat
  /-- The generation of the parked reply — a `call` returns only when `replyGen = its callGen`. -/
  replyGen : Nat
  deriving Repr, DecidableEq

/-- The reply token a server holds between `recv` and `reply` — it names the caller's pending
rendezvous (the endpoint + the call generation) so the reply reaches the right `Call`. Mirrors
`ReplyToken` (`emulated_kernel.rs:593`). -/
structure ReplyToken where
  /-- The call generation this token is bound to (the reply must carry this generation). -/
  callGen : Nat
  deriving Repr, DecidableEq

namespace Endpoint

/-- A fresh endpoint — `Endpoint::default` (nobody parked, generations `0`). -/
def empty : Endpoint := { pendingCall := none, pendingReply := none, callGen := 0, replyGen := 0 }

/-- **`stageCall ep msg`** — the caller half of `seL4_Call` (the part before blocking): bump the
generation, park `msg` as the pending call. Returns the staged endpoint and THIS call's generation
(the token the caller waits on). Mirrors the staging in `EmulatedKernel::call`
(`emulated_kernel.rs:468`–`471`): `ep.call_gen += 1; my_gen = ep.call_gen; ep.pending_call =
Some(msg)`. -/
def stageCall (ep : Endpoint) (msg : Message) : Nat × Endpoint :=
  let g := ep.callGen + 1
  (g, { ep with callGen := g, pendingCall := some msg })

/-- **`recv ep`** — `seL4_Recv` (the SERVER half): take the parked call message and a `ReplyToken`
bound to its generation. Returns `none` if no call is parked, else `some (msg, token, ep')` with the
message TAKEN (`pendingCall := none`) and the token carrying `ep.callGen`. Mirrors
`EmulatedKernel::recv` (`emulated_kernel.rs:491`): `ep.pending_call.take()` + `ReplyToken { endpoint,
call_gen: ep.call_gen }`. -/
def recv (ep : Endpoint) : Option (Message × ReplyToken × Endpoint) :=
  match ep.pendingCall with
  | none => none
  | some msg => some (msg, { callGen := ep.callGen }, { ep with pendingCall := none })

/-- **`reply ep token rep`** — `seL4_Reply` (the SERVER half): park `rep` for the caller named by
`token`'s generation. Mirrors `EmulatedKernel::reply` (`emulated_kernel.rs:508`):
`ep.pending_reply = Some(reply); ep.reply_gen = token.call_gen`. -/
def reply (ep : Endpoint) (token : ReplyToken) (rep : Message) : Endpoint :=
  { ep with pendingReply := some rep, replyGen := token.callGen }

/-- **`takeReplyFor ep g`** — the caller half AFTER blocking: if the parked reply is for generation
`g` (`replyGen = g`), take it. Returns `none` if not yet replied to THIS call. Mirrors the wake
condition in `EmulatedKernel::call` (`emulated_kernel.rs:478`–`482`): `if ep.reply_gen == my_gen { if
let Some(reply) = ep.pending_reply.take() { return Ok(reply) } }`. -/
def takeReplyFor (ep : Endpoint) (g : Nat) : Option (Message × Endpoint) :=
  if ep.replyGen == g then
    match ep.pendingReply with
    | none => none
    | some rep => some (rep, { ep with pendingReply := none })
  else
    none

end Endpoint

/-- **`callServedBy serve msg`** — `seL4_Call` whose server runs INLINE (the emulator's
single-threaded dispatch convenience): stage the call, run the server body `serve` on the observed
message, return its reply. Mirrors `EmulatedKernel::call_served_by` (`emulated_kernel.rs:528`):
`serve(msg)` — still a SYNCHRONOUS call (the caller does not proceed until `serve` returns). The
point of the theorem below is that this inline form and the staged `recv`/`reply` form deliver the
SAME message round-trip. -/
def callServedBy (serve : Message → Message) (msg : Message) : Message := serve msg

/-! ## §4 — Untyped + Retype: the factory slot-caveat as a kernel invariant.

Mirrors `ObjectType` (`emulated_kernel.rs:69`), `Untyped` (`emulated_kernel.rs:152`), and
`EmulatedKernel::retype` (`emulated_kernel.rs:328`). An `Untyped` carries a `capacity`, the
`consumed` so far, and the ONE `permits` type it may be retyped into. `retype` enforces BOTH halves
of the slot-caveat: the TYPE (only `permits` — `WrongType` else) and the BUDGET (`consumed + size ≤
capacity` — `Exhausted` else). A factory granted only `CNode` retypes physically cannot mint a
`Frame`. -/

/-- The kind of seL4 kernel object an Untyped may be retyped into — the `seL4_Untyped_Retype` type
argument. Mirrors `ObjectType` (`emulated_kernel.rs:69`). -/
inductive ObjectType where
  /-- A CNode (a capability table) — what a `DirectoryFactory` retypes to back a new c-list. -/
  | cnode
  /-- A synchronous Endpoint (a rendezvous IPC port). -/
  | endpoint
  /-- A Notification (a badge-OR signal object). -/
  | notification
  /-- A Frame (a page of memory — a shared buffer / framebuffer tile). -/
  | frame
  deriving Repr, DecidableEq

namespace ObjectType

/-- The per-object size charged against an Untyped budget when retyped. Mirrors
`ObjectType::size_bytes` (`emulated_kernel.rs:86`): endpoint/notification `16`, CNode `64`, frame a
page `4096`. The budget ARITHMETIC (a factory exhausts after N objects) is real, not nominal. -/
def sizeBytes : ObjectType → Nat
  | .endpoint => 16
  | .notification => 16
  | .cnode => 64
  | .frame => 4096

end ObjectType

/-- An Untyped memory region + its retype budget — the seL4 `Untyped` cap. Mirrors `Untyped`
(`emulated_kernel.rs:152`): `capacity` total bytes, `consumed` so far, and the ONE `permits` type a
retype may produce. -/
structure Untyped where
  /-- The total byte budget this Untyped was carved with. -/
  capacity : Nat
  /-- The bytes already consumed by retypes. -/
  consumed : Nat
  /-- The ONLY object type this Untyped may be retyped into — the declared factory shape. -/
  permits : ObjectType
  deriving Repr, DecidableEq

/-- The error a `retype` returns — the kernel-enforced factory slot-caveat refusing. Mirrors
`RetypeError` (`emulated_kernel.rs:609`), minus the `NoSuchUntyped` variant (we model `retype` on a
present Untyped value directly, so a missing-id is not a case here). -/
inductive RetypeError where
  /-- The requested type is not the one this Untyped permits — the slot-caveat (a factory may only
  mint its declared shape). Carries the permitted + requested types. -/
  | wrongType (permitted requested : ObjectType)
  /-- The retype would exceed the Untyped's byte budget. Carries capacity / consumed / requested. -/
  | exhausted (capacity consumed requested : Nat)
  deriving Repr, DecidableEq

namespace Untyped

/-- Carve an Untyped with `capacity` bytes that may be retyped ONLY into `permits` objects. Mirrors
`EmulatedKernel::create_untyped` (`emulated_kernel.rs:309`). -/
def create (capacity : Nat) (permits : ObjectType) : Untyped :=
  { capacity, consumed := 0, permits }

/-- The remaining budget in bytes. Mirrors `EmulatedKernel::untyped_remaining`
(`emulated_kernel.rs:369`): `capacity - consumed`. -/
def remaining (u : Untyped) : Nat := u.capacity - u.consumed

/-- **`retype u ty`** — `seL4_Untyped_Retype`: mint EXACTLY the declared object type from the
budget. Enforces BOTH halves of the slot-caveat:
  * **type**: `ty ≠ permits` ⇒ `wrongType` (a CNode factory cannot mint a Frame);
  * **budget**: `consumed + sizeBytes ty > capacity` ⇒ `exhausted`.
On success returns the type minted (= `ty`, exactly) and the Untyped with the budget charged. Mirrors
`EmulatedKernel::retype` (`emulated_kernel.rs:328`): the `if ty != u.permits { WrongType } … if
u.consumed + need > u.capacity { Exhausted } … consumed += need`. We return the minted `ObjectType`
(the new object's TYPE — the load-bearing observable of "minted exactly the declared type"); the
opaque `ObjectId` the Rust hands back is a fresh `alloc_id` we do not need to model to state the
caveat. -/
def retype (u : Untyped) (ty : ObjectType) : Except RetypeError (ObjectType × Untyped) :=
  if ty ≠ u.permits then
    .error (.wrongType u.permits ty)
  else if u.consumed + ty.sizeBytes > u.capacity then
    .error (.exhausted u.capacity u.consumed ty.sizeBytes)
  else
    .ok (ty, { u with consumed := u.consumed + ty.sizeBytes })

end Untyped

/-! ## §5 — THEOREM 1: MINT-ATTENUATES-REFUSES-AMPLIFICATION.

`mint` installs a child cap with rights `≤` the parent's, and REFUSES an amplifying mint. We prove:
(a) a SUCCESSFUL mint's child rights are the requested `narrower` AND `narrower ⊆ parent.rights`
(the child genuinely attenuates the parent); (b) an AMPLIFYING mint (`¬ grantOk parent narrower`) is
REFUSED (`none`); (c) the child is recorded `mintedFrom = some parent` (the derivation edge the
revoke needs).

Refinement obligation FOR: `EmulatedKernel::mint` → `LocalBacking::mint` (`local.rs:106`) — exercised
by `mint_attenuates_and_refuses_amplification` (`local.rs:166`) and
`promoted_cnode_mint_revoke_still_green` (`emulated_kernel.rs:662`). -/

/-- **MINT ATTENUATES** (the positive polarity): when `mint` succeeds, the child holds EXACTLY the
requested `narrower` rights AND those are `⊆` the parent's held rights (`authNarrowerOrEqual narrower
parent.rights`) — a genuine attenuation, never an amplification. -/
theorem mint_child_attenuates_parent
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    cn'.rightsAt s = some narrower ∧ authNarrowerOrEqual narrower p.rights = true := by
  unfold CNode.mint at hmint
  rw [hp] at hmint
  by_cases hgate : grantOk p.rights narrower
  · simp only [hgate, if_true, Option.some.injEq, Prod.mk.injEq] at hmint
    obtain ⟨hs, hcn⟩ := hmint
    subst hs; subst hcn
    refine ⟨?_, ?_⟩
    · -- the child's rights are `narrower`: it is the freshly-inserted head slot
      simp [CNode.rightsAt, CNode.get]
    · -- `grantOk p.rights narrower = authNarrowerOrEqual narrower p.rights` (by def)
      simpa [grantOk] using hgate
  · simp [hgate] at hmint

/-- **MINT REFUSES AMPLIFICATION** (the negative polarity): a mint whose `narrower` is NOT `⊆` the
parent's held rights (`grantOk parent.rights narrower = false`) is REFUSED — `mint` returns `none`.
The `granted ⊆ held` law, enforced exactly as `seL4_CNode_Mint` rejects an over-broad rights mask. -/
theorem mint_refuses_amplification
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq)
    (hp : cn.get parent = some p)
    (hamp : grantOk p.rights narrower = false) :
    cn.mint parent narrower = none := by
  unfold CNode.mint
  rw [hp]
  simp [hamp]

/-- **MINT RECORDS THE DERIVATION EDGE**: a successful mint installs the child `mintedFrom = some
parent` — the edge the transitive revoke walks. Without this the derivation tree would be flat and
the transitive revoke would have nothing to follow. -/
theorem mint_records_parent
    (cn : CNode) (parent : SlotId) (p : Slot) (narrower : AuthReq) (s : SlotId) (cn' : CNode)
    (hp : cn.get parent = some p)
    (hmint : cn.mint parent narrower = some (s, cn')) :
    (cn'.get s).map Slot.mintedFrom = some (some parent) := by
  unfold CNode.mint at hmint
  rw [hp] at hmint
  by_cases hgate : grantOk p.rights narrower
  · simp only [hgate, if_true, Option.some.injEq, Prod.mk.injEq] at hmint
    obtain ⟨hs, hcn⟩ := hmint
    subst hs; subst hcn
    simp [CNode.get]
  · simp [hgate] at hmint

/-! ## §6 — THEOREM 2: REVOKE-SYNCHRONOUS-TRANSITIVE.

`revoke` removes the cap AND its entire derived subtree atomically — the n=1 immediate-dark property.
We prove on a concrete root→child→grandchild derivation chain (the exact shape the green Rust test
`revoke_is_synchronous_and_transitive` builds) that after `revoke root`: (a) ALL THREE slots are dead
(`isLive = false`) — no in-flight survivor; (b) exactly `3` slots were removed; (c) the count matches
the Rust assertion. The transitive closure is what makes the grandchild die from a root revoke.

We then prove the GENERAL atomicity shape: a revoke leaves NO slot of the doomed set live (a
universally-quantified "every descendant is dead at once"), so the immediacy is not a feature of the
one witness — it holds for the whole subtree by construction.

Refinement obligation FOR: `EmulatedKernel::revoke` → `LocalBacking::revoke` (`local.rs:127`) —
exercised by `revoke_is_synchronous_and_transitive` (`local.rs:180`) and
`bounds_local_is_genuinely_real_synchronous_revoke` (`emulated_kernel.rs:639`). -/

section RevokeWitness

/-- The concrete derivation chain the Rust test builds: `install` an Either root, `mint` a Signature
child of it, `mint` a Signature grandchild of the child. We name the three slot ids and the final
CNode so the theorems can speak about them. (Slots are `0, 1, 2` by the monotone allocator.) -/
def chainCNode : CNode :=
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .either
  match c0.mint root .signature with
  | some (child, c1) =>
    match c1.mint child .signature with
    | some (_gc, c2) => c2
    | none => c1
  | none => c0

/-- **REVOKE IS TRANSITIVE + SYNCHRONOUS (the witness).** Revoking the root of the chain removes ALL
THREE slots at once (root, child, grandchild all dead) and reports `3` removed — exactly the Rust
`assert_eq!(removed, 3)` + the three `assert!(!is_live(...))`. The grandchild dying from a ROOT revoke
is the transitivity; all three dead the instant `revoke` returns is the n=1 synchrony. -/
theorem revoke_chain_synchronous_transitive :
    let (removed, cn') := chainCNode.revoke 0
    removed = 3
      ∧ cn'.isLive 0 = false   -- root dead
      ∧ cn'.isLive 1 = false   -- child dead (direct derivation)
      ∧ cn'.isLive 2 = false   -- grandchild dead (TRANSITIVE derivation)
      := by decide

/-- Before the revoke, all three slots ARE live (so the revoke is not vacuously killing already-dead
slots — the chain genuinely exists, then genuinely vanishes). -/
theorem chain_all_live_before :
    chainCNode.isLive 0 = true ∧ chainCNode.isLive 1 = true ∧ chainCNode.isLive 2 = true := by
  decide

/-- **Revoking the CHILD (not the root) kills the grandchild but SPARES the root** — the revoke is
the subtree rooted at the revoked slot, not the whole tree. The root (slot `0`, the child's PARENT)
survives; the child (`1`) and grandchild (`2`) die. This is the directionality of the derivation
revoke: descendants die, ancestors live. -/
theorem revoke_child_spares_root :
    let (removed, cn') := chainCNode.revoke 1
    removed = 2
      ∧ cn'.isLive 0 = true    -- root (ancestor) SURVIVES
      ∧ cn'.isLive 1 = false   -- child dead
      ∧ cn'.isLive 2 = false   -- grandchild dead (transitive under the child)
      := by decide

end RevokeWitness

/-- **REVOKE LEAVES NO DOOMED SLOT LIVE (the general atomicity law).** After `revoke s`, every slot
in the doomed set (`s` + its transitive subtree) is NOT live in the resulting CNode — a
universally-quantified "the whole subtree is dark at once". The revoke filters out exactly the
doomed ids, so none can be looked up afterward: the n=1 immediacy as a structural property, not a
per-witness fact. -/
theorem revoke_kills_all_doomed (cn : CNode) (s : SlotId) (d : SlotId)
    (hd : (cn.doomedSet s).contains d = true) :
    (cn.revoke s).2.isLive d = false := by
  unfold CNode.revoke CNode.isLive CNode.get
  simp only
  -- after revoke, the slot list is `cn.slots.filter (¬ doomed.contains ·.1)`; `d` is doomed, so
  -- `find?` for `d` finds nothing.
  have : ((cn.slots.filter (fun p => ¬ (cn.doomedSet s).contains p.1)).find?
            (fun p => p.1 == d)) = none := by
    rw [List.find?_eq_none]
    intro p hp
    rw [List.mem_filter] at hp
    obtain ⟨_, hpd⟩ := hp
    -- `p` survived the filter ⇒ `¬ doomed.contains p.1`; if `p.1 = d` then `doomed.contains d`,
    -- contradicting `hpd`.
    simp only [decide_not, Bool.not_eq_true', decide_eq_false_iff_not] at hpd
    intro hpeq
    simp only [beq_iff_eq] at hpeq
    rw [hpeq] at hpd
    exact absurd (by simpa using hd) hpd
  rw [this]
  rfl

/-! ## §7 — THEOREM 3: RETYPE-MINTS-EXACTLY-DECLARED.

`retype` yields exactly the declared `ObjectType`, only within budget; a wrong-type retype REFUSES
(`wrongType`), an over-budget retype REFUSES (`exhausted`). We prove all three: (a) a retype of the
PERMITTED type within budget SUCCEEDS and the minted type is EXACTLY the requested one (and the
budget is charged); (b) a retype of a NON-permitted type REFUSES with `wrongType`; (c) a retype that
would exceed the budget REFUSES with `exhausted`.

Refinement obligation FOR: `EmulatedKernel::retype` (`emulated_kernel.rs:328`) — exercised by
`retype_mints_only_the_declared_type` (`emulated_kernel.rs:731`) and
`retype_exhausts_the_untyped_budget` (`emulated_kernel.rs:744`). This IS the
`DirectoryFactory → seL4_Untyped_Retype` slot-caveat as a theorem (`sel4/RBG-TO-SEL4.md`). -/

/-- **RETYPE MINTS EXACTLY THE DECLARED TYPE** (the positive polarity): a retype of the PERMITTED
type that fits the budget SUCCEEDS, and the object minted is EXACTLY that type, with the budget
charged by its size. "Minted exactly the declared `ObjectType`, nothing else." -/
theorem retype_mints_exactly_declared
    (u : Untyped) (ty : ObjectType)
    (hperm : ty = u.permits)
    (hbudget : u.consumed + ty.sizeBytes ≤ u.capacity) :
    u.retype ty = .ok (ty, { u with consumed := u.consumed + ty.sizeBytes }) := by
  unfold Untyped.retype
  simp only [hperm, ne_eq, not_true_eq_false, if_false]
  have hnotover : ¬ (u.consumed + u.permits.sizeBytes > u.capacity) := by
    rw [hperm] at hbudget; omega
  simp [hnotover]

/-- **RETYPE REFUSES THE WRONG TYPE** (the slot-caveat — TYPE half): a retype of any type OTHER than
the Untyped's `permits` is REFUSED with `wrongType`. A factory granted only `CNode` retypes
physically cannot mint a `Frame` — the slot-caveat as a kernel invariant, not a Rust check. -/
theorem retype_refuses_wrong_type
    (u : Untyped) (ty : ObjectType)
    (hwrong : ty ≠ u.permits) :
    u.retype ty = .error (.wrongType u.permits ty) := by
  unfold Untyped.retype
  simp [hwrong]

/-- **RETYPE REFUSES OVER-BUDGET** (the slot-caveat — BUDGET half): a retype of the permitted type
that would exceed the byte budget (`consumed + size > capacity`) is REFUSED with `exhausted`. The
factory exhausts its Untyped quota after N objects — real budget arithmetic. -/
theorem retype_refuses_over_budget
    (u : Untyped) (ty : ObjectType)
    (hperm : ty = u.permits)
    (hover : u.consumed + ty.sizeBytes > u.capacity) :
    u.retype ty = .error (.exhausted u.capacity u.consumed ty.sizeBytes) := by
  unfold Untyped.retype
  simp only [hperm, ne_eq, not_true_eq_false, if_false]
  rw [hperm] at hover
  simp [hover]

/-! ## §8 — THEOREM 4: ENDPOINT rendezvous (a Recv observes EXACTLY the Call's message).

The endpoint is a meeting point: a `Recv` observes EXACTLY the message a `Call` parked, and the reply
the `Call` ultimately receives is EXACTLY the one the server parked for THIS call's generation. We
prove the full staged round-trip: `stageCall` then `recv` observes the same message and returns a
generation-bound token; `reply` then `takeReplyFor` (at that generation) returns the same reply. And
the inline `callServedBy` delivers `serve` applied to the message — the same observable as the staged
form.

Refinement obligation FOR: `EmulatedKernel::recv`/`reply`/`call`/`call_served_by`
(`emulated_kernel.rs:452`+) — exercised by `endpoint_call_recv_reply_rendezvous_cross_thread`
(`emulated_kernel.rs:710`). -/

/-- **RECV OBSERVES EXACTLY THE CALL'S MESSAGE.** After `stageCall ep msg` parks `msg`, a `recv`
returns EXACTLY `msg` (no buffering, no mangling — the meeting point hands the receiver precisely the
caller's message) together with a `ReplyToken` bound to THIS call's generation. -/
theorem recv_observes_call_message (ep : Endpoint) (msg : Message) :
    let (g, ep₁) := ep.stageCall msg
    ∃ ep₂, ep₁.recv = some (msg, { callGen := g }, ep₂) := by
  simp only [Endpoint.stageCall, Endpoint.recv]
  exact ⟨_, rfl⟩

/-- **THE FULL RENDEZVOUS ROUND-TRIPS.** Stage a call with `msg`, the server `recv`s it (observing
exactly `msg`) and gets a token, `reply`s with `rep` bound to that token's generation, and the caller
`takeReplyFor` at its generation receives EXACTLY `rep`. The message went in, the matched reply came
out — the synchronous rendezvous, end to end, with the generation binding ensuring the caller gets
ITS reply. -/
theorem rendezvous_round_trips (ep : Endpoint) (msg rep : Message) :
    let (g, ep₁) := ep.stageCall msg
    ∃ token ep₂, ep₁.recv = some (msg, token, ep₂)
      ∧ (let ep₃ := ep₂.reply token rep
         ∃ ep₄, ep₃.takeReplyFor g = some (rep, ep₄)) := by
  simp only [Endpoint.stageCall, Endpoint.recv, Endpoint.reply, Endpoint.takeReplyFor]
  refine ⟨_, _, rfl, ?_⟩
  simp

/-- **THE INLINE FORM AGREES.** `callServedBy serve msg` returns `serve msg` — the same reply the
staged rendezvous delivers when the server's body is `serve` (i.e. `reply`s `serve msg`). The
single-threaded convenience and the two-thread rendezvous are the SAME observable round-trip; the
inline form is not a different semantics. -/
theorem inline_call_agrees_with_serve (serve : Message → Message) (msg : Message) :
    callServedBy serve msg = serve msg := rfl

/-- A genuine NON-IDENTITY round-trip: the server transforms the message (label `+1`, first byte
doubled — the exact transform the Rust `endpoint_call_recv_reply_rendezvous_cross_thread` test runs),
and the caller receives the transformed reply. Witnesses the round-trip carries real data, not a
trivial echo. -/
theorem rendezvous_transforms_message :
    callServedBy (fun m => { label := m.label + 1, bytes := (2 * m.bytes.headD 0) :: m.bytes.tail })
        { label := 7, bytes := [21, 0, 0] }
      = { label := 8, bytes := [42, 0, 0] } := by decide

/-! ## §9 — THEOREM 5: NOTIFICATION badge-OR (a Wait observes the OR of signalled badges).

A `Wait` after a sequence of `Signal`s observes the bitwise-OR of all signalled badges since the last
wait, then the object resets to zero (read-and-clear). We prove: (a) one signal then wait returns that
badge (and resets); (b) a SEQUENCE of signals then wait returns the OR of all of them; (c) a second
wait (no intervening signal) returns `0` — the clear is real.

Refinement obligation FOR: `EmulatedKernel::signal`/`wait`/`poll_notification`
(`emulated_kernel.rs:388`+) — exercised by `notification_badge_or_accumulates_and_clears`
(`emulated_kernel.rs:680`) and `notification_wait_blocks_until_signalled_cross_thread`
(`emulated_kernel.rs:691`). -/

/-- **ONE SIGNAL THEN WAIT** returns the signalled badge and RESETS the object to zero. The basic
read-and-clear. -/
theorem signal_then_wait (n : Notification) (badge : Nat) :
    ((n.signal badge).wait) = (n.badge ||| badge, { badge := 0 }) := by
  simp [Notification.signal, Notification.wait]

/-- **A SEQUENCE OF SIGNALS THEN WAIT** returns the bitwise-OR of all signalled badges (folded into
the accumulator), then resets. The seL4 accumulation: the returned badge is the OR of every signal
since the last wait. We prove it for the two-signal case the Rust test exercises (`0b001 | 0b100 =
0b101`), starting from an empty notification. -/
theorem wait_observes_badge_or :
    ((Notification.empty.signal 0b001).signal 0b100).wait = (0b101, { badge := 0 }) := by decide

/-- **THE CLEAR IS REAL**: after a `wait` consumes the badge, a SECOND `wait` (no intervening signal)
returns `0` — the object reset to zero, exactly the Rust `assert_eq!(poll_notification, 0)` after the
first read. So a badge is observed ONCE, not re-delivered. -/
theorem second_wait_is_zero (n : Notification) :
    (n.wait.2).wait = (0, { badge := 0 }) := by
  simp [Notification.wait]

/-! ## §10 — NON-VACUITY TEETH (`#guard`): both polarities BITE, on a concrete kernel.

The lattice (from `Exec.CapTPConcrete`): `none` ⊤ (broadest), `either` below it,
`signature`/`proof` below `either`, `impossible` ⊥. So `either → signature` is a NARROWING (mint
COMMITS) and `signature → either` / `signature → none` are WIDENINGS (mint REFUSES);
`signature → impossible` is a narrowing (COMMITS). Slot/object ids are already `Nat` (the Rust
`u32`/`u64`), so no abstract carrier is pinned — these ARE the kernel's identities.

These are the Lean mirrors of the green Rust tests:
`mint_attenuates_and_refuses_amplification`, `revoke_is_synchronous_and_transitive`,
`retype_mints_only_the_declared_type`, `retype_exhausts_the_untyped_budget`,
`notification_badge_or_accumulates_and_clears`, `endpoint_call_recv_reply_rendezvous_cross_thread`. -/

section Witnesses

/-! ### MINT — a narrowing COMMITS attenuated; an amplifying mint REFUSES. -/

-- A root with Either rights, then a mint to Signature (a NARROWING) COMMITS, and the child holds
-- exactly Signature.
#guard
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .either
  (c0.mint root .signature).isSome
#guard
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .either
  match c0.mint root .signature with
  | some (child, c1) => c1.rightsAt child == some .signature
  | none => false

-- An amplifying mint (Signature child → Either, a WIDENING) is REFUSED (`none`).
#guard
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .either
  match c0.mint root .signature with
  | some (child, c1) => (c1.mint child .either).isNone
  | none => false
-- The maximal widening (Signature → None, None being the top) is REFUSED too.
#guard
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .signature
  (c0.mint root .none).isNone
-- The OTHER polarity: Signature → Impossible (Impossible the bottom) is a narrowing, COMMITS — so
-- the mint gate is not constantly-`none`.
#guard
  let (root, c0) := CNode.empty.install "endpoint:ctrl" .signature
  (c0.mint root .impossible).isSome

/-! ### REVOKE — synchronous + transitive: a root revoke darkens the whole subtree at once. -/

-- Revoking the root of the root→child→grandchild chain removes all 3 and leaves none live.
#guard (chainCNode.revoke 0).1 == 3
#guard !(chainCNode.revoke 0).2.isLive 0
#guard !(chainCNode.revoke 0).2.isLive 1
#guard !(chainCNode.revoke 0).2.isLive 2   -- the grandchild — TRANSITIVE death from a root revoke
-- Before the revoke all three ARE live (the subtree genuinely existed).
#guard chainCNode.isLive 0 && chainCNode.isLive 1 && chainCNode.isLive 2
-- Revoking the CHILD spares the root (ancestor) but kills the grandchild (descendant).
#guard (chainCNode.revoke 1).1 == 2
#guard (chainCNode.revoke 1).2.isLive 0    -- root survives
#guard !(chainCNode.revoke 1).2.isLive 2   -- grandchild dies under the child

/-! ### RETYPE — exactly the declared type within budget; wrong-type / over-budget REFUSE. -/

-- A CNode factory: retype to CNode (the declared type) within budget SUCCEEDS, minting exactly CNode.
#guard match (Untyped.create 256 .cnode).retype .cnode with
  | .ok (ty, _) => ty == ObjectType.cnode
  | .error _ => false
-- Retype to ANY OTHER type (Frame) REFUSES with wrongType — the slot-caveat at the kernel.
#guard match (Untyped.create 256 .cnode).retype .frame with
  | .error (.wrongType p r) => p == ObjectType.cnode && r == ObjectType.frame
  | _ => false
-- Budget for exactly 2 endpoints (16 bytes each): two retypes SUCCEED, remaining hits 0, the third
-- REFUSES with exhausted (the exact Rust `retype_exhausts_the_untyped_budget` shape).
#guard match (Untyped.create 32 .endpoint).retype .endpoint with
  | .ok (_, u1) =>
    (match u1.retype .endpoint with
     | .ok (_, u2) => u2.remaining == 0 && (match u2.retype .endpoint with
                                            | .error (.exhausted ..) => true
                                            | _ => false)
     | .error _ => false)
  | .error _ => false

/-! ### ENDPOINT — the rendezvous round-trips a non-trivial message. -/

-- Recv observes exactly the staged call message.
#guard
  let (_g, ep₁) := Endpoint.empty.stageCall { label := 7, bytes := [21, 0, 0] }
  match ep₁.recv with
  | some (m, _, _) => m == ({ label := 7, bytes := [21, 0, 0] } : Message)
  | none => false
-- The inline call applies the server transform (label+1, first byte doubled) — the real round-trip.
#guard callServedBy (fun m => { label := m.label + 1, bytes := (2 * m.bytes.headD 0) :: m.bytes.tail })
    { label := 7, bytes := [21, 0, 0] }
  == ({ label := 8, bytes := [42, 0, 0] } : Message)

/-! ### NOTIFICATION — badge-OR accumulates then clears. -/

-- Two signals (0b001, 0b100) OR to 0b101 on a wait; a second wait reads 0 (cleared).
#guard (((Notification.empty.signal 0b001).signal 0b100).wait).1 == 0b101
#guard (((Notification.empty.signal 0b001).signal 0b100).wait).2.wait.1 == 0
-- Distinct bits genuinely OR (not overwrite): 0b001 then 0b100 is 0b101, not 0b100.
#guard ((Notification.empty.signal 0b001).signal 0b100).badge == 0b101

end Witnesses

/-! ## §11 — Axiom hygiene. Every load-bearing theorem is checked axiom-clean (no `sorry`, no extra
`axiom`, only the standard `propext`/`Classical.choice`/`Quot.sound`). -/

#assert_all_clean [
  mint_child_attenuates_parent,
  mint_refuses_amplification,
  mint_records_parent,
  revoke_chain_synchronous_transitive,
  chain_all_live_before,
  revoke_child_spares_root,
  revoke_kills_all_doomed,
  retype_mints_exactly_declared,
  retype_refuses_wrong_type,
  retype_refuses_over_budget,
  recv_observes_call_message,
  rendezvous_round_trips,
  inline_call_agrees_with_serve,
  rendezvous_transforms_message,
  signal_then_wait,
  wait_observes_badge_or,
  second_wait_is_zero
]

end Dregg2.Firmament.SeL4Kernel
