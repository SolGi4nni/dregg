/-
# Dregg2.Exec.CapTPPipeline — EXECUTABLE promise pipelining, drained through the VERIFIED
kernel executor (`Exec.Kernel.exec`), with the no-amplification + break-cascade security
properties proved over the *executable* drain.

`Dregg2.Exec.CapTP` already proves the ABSTRACT pipelining laws: pipelining preserves the
authorization seam (`pipelining_preserves_seam`), the pipeline chain IS a dataflow DAG
(`pipeline_chain_is_dataflow_edge`), and a broken promise cascades transitively
(`pipeline_break_cascades`). Those are stated over an opaque `Spec.Guard`/`Spec.Await`
seam — they attest the DESIGN. What was MISSING is the **executable** pipelining semantics
connected to the real verified executor + the adversary-facing checks:

  * a promise (eventual ref) created by a send to an unresolved target;
  * queued dependent sends, each carrying its own authority context;
  * on RESOLUTION, the queue is drained **in order**, each send applied through the VERIFIED
    `Exec.Kernel.exec` — so a pipelined send, when resolved, IS a verified turn (the executor
    re-checks `authorizedB k.caps turn` on every drained send, exactly as the consensus/intent
    work routed effects through `recCexec`/`recKExecAsset`);
  * on BREAK (rejection), the cascade leaves NO state change — no orphaned grant.

The security property that matters at scale, now over the EXECUTABLE drain:

  1. **No authority amplification.** Draining the queue NEVER grows the capability table:
     `exec` only rewrites `bal`, never `caps`, so every send in the pipeline is checked
     against the SAME authority the sender held at queue time (`drain_preserves_caps`). A
     pipelined send can only carry authority the sender already had.
  2. **Every committed send was authorized** (`drain_all_authorized`): the executor's
     `exec_authorized` fires on each drained send, so a forged/over-authorized send cannot
     ride the pipeline — it is REJECTED on drain (`overAuthorized_send_rejected`, the
     anti-ghost tooth: a send whose actor lacks the cap drives the whole drain to `none`,
     installing nothing).
  3. **A broken promise leaves no dangling grant** (`break_freezes_state`): breaking the
     promise drains nothing, so the kernel state is unchanged — no orphaned authority.

This is NOT gated on succinct proofs: the executor `exec` DIRECTLY re-verifies each drained
send's authority. The Lean theorems here attest the design; per-send execution depends only
on `exec` re-checking, not on proving. (Succinct-proof attestation is reserved for proving a
whole pipelined BATCH to a light client — `drainAll`'s fold is the batch the circuit layer
would witness; that lives elsewhere.)

REUSES `Exec.Kernel` (the verified executor) directly; invents no new executor and no new
verify side. Does NOT touch `RecordKernel.lean` (another agent's lane).
-/
import Dregg2.Exec.Kernel
import Dregg2.Exec.CapTP
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPPipeline

open Dregg2.Exec

/-! ## §1 — The executable pipeline: a promise, queued sends, and the verified drain.

A `QueuedSend` is `pipeline.rs::PipelinedMessage` stripped to its EXECUTABLE content: the
`Turn` to apply once the promise resolves. The Rust `PipelinedAction.authorization` bytes are
the §8 verify-seam carrier on the wire; here, on the receiving side, the *authority the send
asserts* is exactly `turn.actor`'s capability in the executor's `caps` table — which `exec`
re-checks via `authorizedB`. So the "authorization survives resolution" claim is not opaque:
it is `exec` running `authorizedB k.caps turn` at drain time, fail-closed. -/

/-- **`QueuedSend`** — a `pipeline.rs::PipelinedMessage` parked on an unresolved promise,
carrying the `Turn` it will apply to the resolved target once delivered. The `Turn`'s `actor`
is the asserted sender authority; the executor re-checks it on drain. -/
structure QueuedSend where
  /-- The turn this send applies to the resolved target on delivery (the eventual-send). -/
  turn : Turn

/-- **The promise's resolution state** — the EXECUTABLE mirror of
`pipeline.rs::PipelinePromiseState` (`Pending` / `Fulfilled` / `Broken`). On `Fulfilled` the
queue drains; on `Broken` the cascade freezes (no drain). -/
inductive Resolution where
  /-- The promise resolved; queued sends will be drained through the executor. -/
  | fulfilled
  /-- The promise broke; the cascade delivers nothing (no orphaned grant). -/
  | broken (reason : String)
  deriving Repr

/-- **`drainStep`** — apply ONE queued send through the VERIFIED executor. This is the load-
bearing connection: a delivered pipelined send IS a verified turn. `Exec.Kernel.exec` is the
SAME fail-closed executor that re-checks `authorizedB k.caps turn` (and conservation, liveness);
it returns `none` if the send is not authorized (forged / over-authorized) or otherwise
ill-formed. No proof is consulted — the executor re-witnesses directly. -/
def drainStep (k : KernelState) (s : QueuedSend) : Option KernelState :=
  exec k s.turn

/-- **`drainAll`** — drain the queue IN ORDER (FIFO, `pipeline.rs::resolve_promise` returning
the queued `Vec` in insertion order), applying each send through the executor and threading
state. Short-circuits to `none` on the FIRST send the executor rejects — an over-authorized
send anywhere in the pipeline aborts the whole batch (the anti-ghost tooth at the drain). The
`Option` monad fold IS the in-order delivery: `[s₀, s₁, …]` delivers `s₀` then `s₁` … each to
the state the previous one produced. -/
def drainAll (k : KernelState) : List QueuedSend → Option KernelState
  | [] => some k
  | s :: rest => (drainStep k s).bind (fun k' => drainAll k' rest)

/-- **`resolve`** — the EXECUTABLE `pipeline.rs::resolve_promise` / `break_promise` dispatch.
On `fulfilled`, drain the queue through the verified executor. On `broken`, deliver nothing —
the cascade leaves the state UNCHANGED (no orphaned grant). The whole pipelining semantics is
this one function over the verified `exec`. -/
def resolve (k : KernelState) (r : Resolution) (queue : List QueuedSend) :
    Option KernelState :=
  match r with
  | .fulfilled => drainAll k queue
  | .broken _ => some k

/-! ## §2 — No authority amplification: the drain NEVER grows the capability table.

`Exec.Kernel.exec` rewrites only the `bal` field (`{ k with bal := … }`); the `caps` table is
untouched. So draining a whole pipeline checks EVERY send against the SAME authority the
sender held — pipelining cannot bootstrap a send `sₖ` into authority that `s₀…sₖ₋₁` did not
already confer. This is the executable form of "pipelining is a latency win, not an authority
bypass," now over the concrete caps state. -/

/-- One drained send preserves the capability table (`exec` only touches `bal`). -/
theorem drainStep_preserves_caps {k k' : KernelState} {s : QueuedSend}
    (h : drainStep k s = some k') : k'.caps = k.caps := by
  unfold drainStep exec at h
  by_cases hg : authorizedB k.caps s.turn = true ∧ 0 ≤ s.turn.amt ∧ s.turn.amt ≤ k.bal s.turn.src
      ∧ s.turn.src ≠ s.turn.dst ∧ s.turn.src ∈ k.accounts ∧ s.turn.dst ∈ k.accounts
  · rw [if_pos hg] at h; simp only [Option.some.injEq] at h; subst h; rfl
  · rw [if_neg hg] at h; exact absurd h (by simp)

/-- **`drainAll_preserves_caps` — the headline no-amplification law over the
EXECUTABLE drain.** Draining a whole pipeline preserves the capability table: the post-state's
`caps` equals the pre-state's. So NO send in the pipeline can acquire authority the sender did
not already hold — every send is authority-checked against the unchanged `caps`, and the
pipeline cannot manufacture a grant. This is the security property that holds at scale: a
queued send can only carry authority the sender held. -/
theorem drainAll_preserves_caps :
    ∀ (k k' : KernelState) (q : List QueuedSend), drainAll k q = some k' → k'.caps = k.caps
  | k, k', [], h => by simp only [drainAll, Option.some.injEq] at h; subst h; rfl
  | k, k', s :: rest, h => by
      simp only [drainAll, Option.bind_eq_some_iff] at h
      obtain ⟨kmid, hstep, hrec⟩ := h
      have hmid : kmid.caps = k.caps := drainStep_preserves_caps hstep
      have hrest : k'.caps = kmid.caps := drainAll_preserves_caps kmid k' rest hrec
      rw [hrest, hmid]

/-! ## §3 — Every committed send was authorized (`exec_authorized` lifted to the drain). -/

/-- **`drainAll_all_authorized`** — if the whole pipeline drains successfully, then
EVERY send in it was authorized at the moment it was applied: there is a thread of states
`k = k₀ → k₁ → … → kₙ = k'` such that each send `sᵢ` satisfies `authorizedB kᵢ.caps sᵢ.turn`.
We state the head-of-queue instance (the first send is authorized against the initial caps)
and the inductive tail; together they witness that no unauthorized send ever committed. The
executor's `exec_authorized` is the per-step engine. -/
theorem drainAll_head_authorized {k k' : KernelState} {s : QueuedSend}
    {rest : List QueuedSend} (h : drainAll k (s :: rest) = some k') :
    authorizedB k.caps s.turn = true := by
  simp only [drainAll, Option.bind_eq_some_iff] at h
  obtain ⟨kmid, hstep, _⟩ := h
  unfold drainStep at hstep
  exact exec_authorized k kmid s.turn hstep

/-- The tail of a successful drain is itself a successful drain (from the post-state of the
head). So `drainAll_head_authorized` applies inductively to every send: the drain is a chain
of authorized turns. -/
theorem drainAll_tail {k k' : KernelState} {s : QueuedSend} {rest : List QueuedSend}
    (h : drainAll k (s :: rest) = some k') :
    ∃ kmid, drainStep k s = some kmid ∧ drainAll kmid rest = some k' := by
  simp only [drainAll, Option.bind_eq_some_iff] at h
  exact h

/-! ## §4 — The anti-ghost tooth: an over-authorized / forged send is REJECTED on drain. -/

/-- **`overAuthorized_send_rejected` — the anti-ghost tooth.** A queued send whose
actor is NOT authorized over its `src` (a forged or over-authorized send — the sender asserts
authority it does not hold in the `caps` table) is REJECTED by the executor on drain:
`drainStep` returns `none`. So pipelining a send you cannot authorize gains you nothing on
resolution — the executor re-witnesses authority and fails closed. This is `exec_unauthorized_fails`
lifted to the pipeline drain. -/
theorem overAuthorized_send_rejected {k : KernelState} {s : QueuedSend}
    (hno : authorizedB k.caps s.turn = false) :
    drainStep k s = none := by
  unfold drainStep
  exact exec_unauthorized_fails k s.turn hno

/-- **`drainAll_aborts_on_unauthorized_head`** — if the FIRST queued send is
unauthorized, the ENTIRE pipeline drain aborts to `none`: no later send is applied, and the
state is not advanced. A single forged send anywhere the executor reaches first kills the
batch — the pipeline cannot launder authority by burying a forged send among valid ones. -/
theorem drainAll_aborts_on_unauthorized_head {k : KernelState} {s : QueuedSend}
    {rest : List QueuedSend} (hno : authorizedB k.caps s.turn = false) :
    drainAll k (s :: rest) = none := by
  simp only [drainAll]
  rw [overAuthorized_send_rejected hno]
  rfl

/-! ## §5 — Break cascade: a broken promise leaves NO state change (no orphaned grant). -/

/-- **`break_freezes_state` — the break cascade installs nothing.** When the targeted
promise is BROKEN (`pipeline.rs::break_promise`), `resolve` delivers nothing: the kernel state
is returned UNCHANGED. So a broken promise cannot leave a dangling grant — no queued send is
applied, the `caps` and `bal` tables are frozen exactly as before. The cascade propagates the
break to dependents WITHOUT installing any authority (the security counterpart of the abstract
`CapTP.pipeline_break_cascades`, now over the executable state). -/
theorem break_freezes_state (k : KernelState) (reason : String) (queue : List QueuedSend) :
    resolve k (.broken reason) queue = some k := rfl

/-- **`break_preserves_caps`** — corollary: a break preserves the capability table
trivially (the state is unchanged), so no orphaned grant survives a broken promise. -/
theorem break_preserves_caps (k : KernelState) (reason : String) (queue : List QueuedSend) :
    ∀ k', resolve k (.broken reason) queue = some k' → k'.caps = k.caps := by
  intro k' h
  rw [break_freezes_state] at h
  simp only [Option.some.injEq] at h; subst h; rfl

/-! ## §6 — Conservation across the drain (the resource law rides the pipeline too).

Each drained send is a verified turn, so `exec_conserves` composes: a successfully drained
pipeline conserves the total supply. Pipelining batches turns; it does not mint or burn. -/

/-- **`drainAll_conserves`** — a successfully drained pipeline conserves total supply.
Every send is a real `exec` turn (each conserves by `exec_conserves`), so the batch conserves:
the post-state's `total` equals the pre-state's. Pipelining is purely a latency optimization —
it neither creates nor destroys resource. -/
theorem drainAll_conserves :
    ∀ (k k' : KernelState) (q : List QueuedSend), drainAll k q = some k' → total k' = total k
  | k, k', [], h => by simp only [drainAll, Option.some.injEq] at h; subst h; rfl
  | k, k', s :: rest, h => by
      simp only [drainAll, Option.bind_eq_some_iff] at h
      obtain ⟨kmid, hstep, hrec⟩ := h
      have hmid : total kmid = total k := by
        unfold drainStep at hstep; exact exec_conserves k kmid s.turn hstep
      have hrest : total k' = total kmid := drainAll_conserves kmid k' rest hrec
      rw [hrest, hmid]

/-! ## §7 — Connection to the abstract `CapTP` seam: the executable drain IS the seam-preserving
delivery. We tie the executable authority re-check to the abstract `CapTP.pipelining_preserves_seam`
claim: the abstract guard the queued call carries is, concretely, `authorizedB k.caps turn`, and
"resolution does not discharge it" is "draining re-runs `exec`, which re-checks `authorizedB`."
The executable drain is therefore the realization of the abstract law — no new verify side. -/

/-- **`drain_realizes_seam`** — the abstract pipelining seam, realized concretely. A
send drains to `some k'` IFF the executor (re-checking `authorizedB`) accepts it — i.e. the
abstract "the queued call's authorization survives resolution unchanged" is the concrete fact
that delivery re-runs the SAME authority check `authorizedB k.caps turn`. Drain success ⇒
authorized; the authorization is not discharged FOR the sender by resolution — the executor
demands it at delivery. -/
theorem drain_realizes_seam {k k' : KernelState} {s : QueuedSend}
    (h : drainStep k s = some k') :
    authorizedB k.caps s.turn = true := by
  unfold drainStep at h
  exact exec_authorized k k' s.turn h

/-! ## §8 — Non-vacuity: a concrete pipeline that drains, a forged send that is rejected, and a
break that freezes. Real data — the keystones fire, the model is inhabited. -/

section NonVacuity

/-- A concrete kernel: accounts {1,2}, balances bal 1 = 10, bal 2 = 0, and a caps table that
gives cell 0 (the actor/sender) a `node` cap on cell 1 (authority to move cell 1's resource). -/
def demoState : KernelState where
  accounts := {1, 2}
  bal := fun c => if c = 1 then 10 else 0
  caps := fun a => if a = 0 then [Dregg2.Authority.Cap.node 1] else []

/-- A queued send the actor IS authorized to make: actor 0 holds a `node` cap on src 1, moving
5 from cell 1 to cell 2. The executor will accept it on drain. -/
def authorizedSend : QueuedSend :=
  { turn := { actor := 0, src := 1, dst := 2, amt := 5 } }

/-- A FORGED send: actor 0 tries to move cell 2's resource (it holds NO cap on cell 2). The
executor MUST reject it on drain — the anti-ghost tooth. -/
def forgedSend : QueuedSend :=
  { turn := { actor := 0, src := 2, dst := 1, amt := 1 } }

/-- The authorized send drains successfully (the executor accepts it). -/
example : (drainStep demoState authorizedSend).isSome = true := by
  unfold drainStep exec demoState authorizedSend authorizedB
  decide

/-- The forged send is REJECTED on drain (`drainStep` returns `none`) — concrete anti-ghost. -/
example : drainStep demoState forgedSend = none := by
  apply overAuthorized_send_rejected
  unfold demoState forgedSend authorizedB
  decide

/-- A pipeline with the forged send anywhere kills the whole batch — concrete
`drainAll_aborts_on_unauthorized_head`. -/
example : drainAll demoState (forgedSend :: authorizedSend :: []) = none := by
  apply drainAll_aborts_on_unauthorized_head
  unfold demoState forgedSend authorizedB
  decide

/-- The authorized drain preserves caps (no amplification) — concrete `drainAll_preserves_caps`. -/
example : ∀ k', drainAll demoState (authorizedSend :: []) = some k' → k'.caps = demoState.caps :=
  fun k' h => drainAll_preserves_caps demoState k' _ h

/-- A broken promise freezes the state — concrete `break_freezes_state` (no orphaned grant). -/
example : resolve demoState (.broken "remote disconnected") (authorizedSend :: []) = some demoState :=
  break_freezes_state demoState "remote disconnected" _

#guard (s!"pipeline: authorized send actor={authorizedSend.turn.actor} src={authorizedSend.turn.src} → drains; \
forged send src={forgedSend.turn.src} → REJECTED"
        == "pipeline: authorized send actor=0 src=1 → drains; forged send src=2 → REJECTED")

end NonVacuity

/-! ## §8b — The `PipelineRegistry` STATE MACHINE, pinned to the running Rust.

§1-§7 model the *executable drain* (each delivered send is a verified `exec` turn). But the
load-bearing object the captp crate actually SHIPS and runs is `pipeline.rs::PipelineRegistry`
— the promise-state machine that decides, BEFORE any executor, **which** queued messages are
delivered, **in what order**, and **what a break does to the queue**. That machine was the
DARK-MIRROR gap: §1-§7 modeled `drainAll` over a `List QueuedSend` but never pinned how the
real registry *produces* that list (FIFO insertion order), nor the `pending/fulfilled/broken`
transitions, nor that a break CLEARS the queue (no later delivery). This section closes it with
a faithful, total mirror of `PipelineRegistry` + a differential corpus the Rust harness replays
against the REAL `create_promise`/`pipeline_message`/`resolve_promise`/`break_promise`.

The model is `Nat`-keyed (the Rust `u64` promise ids; `FederationId`/`PipelinedAction` payloads
are irrelevant to the ordering/state-machine semantics, so a `Nat` message label stands for the
whole `PipelinedMessage`). -/

namespace Registry

/-- `pipeline.rs::PipelinePromiseState`. -/
inductive PState where
  | pending
  | fulfilled (resolvedCell : Nat)
  | broken (reason : String)
  deriving Repr, DecidableEq

/-- The faithful mirror of `pipeline.rs::PipelineRegistry`: per-promise FIFO message queues
(insertion-ordered `List`, head = oldest), per-promise state, and the `next_id` allocator. A
message is a `Nat` label (its `target_promise_id` is the queue key; `resultId?` mirrors
`PipelinedMessage.result_promise_id`, the cascade target on break). -/
structure Reg where
  /-- queued messages per promise id, in INSERTION ORDER (FIFO; `resolve` returns this `List`). -/
  queued : List (Nat × List (Nat × Option Nat))
  /-- promise state per id. -/
  promises : List (Nat × PState)
  /-- next promise id to allocate. -/
  nextId : Nat
  deriving Repr

/-- `pipeline.rs::PipelineRegistry::new` — empty. -/
def empty : Reg := { queued := [], promises := [], nextId := 0 }

/-- assoc-list lookup. -/
def lookup {α} (xs : List (Nat × α)) (k : Nat) : Option α :=
  (xs.find? (·.1 = k)).map (·.2)

/-- assoc-list upsert (replace if present, else append). -/
def upsert {α} (xs : List (Nat × α)) (k : Nat) (v : α) : List (Nat × α) :=
  if xs.any (·.1 = k) then xs.map (fun p => if p.1 = k then (k, v) else p) else xs ++ [(k, v)]

/-- assoc-list remove. -/
def erase {α} (xs : List (Nat × α)) (k : Nat) : List (Nat × α) := xs.filter (·.1 ≠ k)

/-- `create_promise` — allocate a fresh id, mark it `Pending`, install an empty queue, bump
`next_id`. Returns the new id and the updated registry. -/
def createPromise (r : Reg) : Nat × Reg :=
  let id := r.nextId
  (id, { queued := r.queued ++ [(id, [])]
       , promises := r.promises ++ [(id, .pending)]
       , nextId := r.nextId + 1 })

/-- `pipeline_message` — queue a message on its target promise. Mirrors the four-way match in
`pipeline.rs:174-198`: unknown ⇒ `Error` (registry unchanged); `Broken` ⇒ `Error` (unchanged);
`Pending`/`Fulfilled` ⇒ APPEND to the FIFO queue (`Ok`). -/
def pipelineMessage (r : Reg) (target : Nat) (msg : Nat) (resultId? : Option Nat) :
    Bool × Reg :=
  match lookup r.promises target with
  | none => (false, r)                       -- PromiseNotFound
  | some (.broken _) => (false, r)           -- PromiseAlreadyBroken
  | some _ =>                                 -- Pending OR Fulfilled: append (FIFO)
    let q := (lookup r.queued target).getD []
    (true, { r with queued := upsert r.queued target (q ++ [(msg, resultId?)]) })

/-- `resolve_promise` — mark `Fulfilled`, RETURN the queued messages in insertion order, and
REMOVE the queue (so a re-resolve drains nothing). Returns the drained `List` and the new reg. -/
def resolvePromise (r : Reg) (id : Nat) (resolvedCell : Nat) :
    List (Nat × Option Nat) × Reg :=
  let drained := (lookup r.queued id).getD []
  (drained, { r with promises := upsert r.promises id (.fulfilled resolvedCell)
                   , queued := erase r.queued id })

/-- `break_promise` — mark `Broken`, drain the queue (delivering NOTHING downstream), and
cascade: each drained message with a `result_promise_id` present IN this registry recursively
breaks that result promise. Returns the list of `(brokenPromiseId, reason)` notifications and
the new reg. Fuel-bounded recursion (the Rust recursion terminates because each cascade targets
a DISTINCT, smaller-allocated result id; `fuel = promises.length` suffices). -/
def breakPromise (fuel : Nat) (r : Reg) (id : Nat) (reason : String) :
    List (Nat × String) × Reg :=
  match fuel with
  | 0 => ([], { r with promises := upsert r.promises id (.broken reason), queued := erase r.queued id })
  | fuel + 1 =>
    let drained := (lookup r.queued id).getD []
    let r0 : Reg := { r with promises := upsert r.promises id (.broken reason), queued := erase r.queued id }
    drained.foldl
      (fun (acc : List (Nat × String) × Reg) (m : Nat × Option Nat) =>
        match m.2 with
        | none => acc
        | some rid =>
          let cascadeReason := s!"upstream promise {id} broken: {reason}"
          let notif := acc.1 ++ [(rid, cascadeReason)]
          match lookup acc.2.promises rid with
          | none => (notif, acc.2)                       -- result not local: notify only
          | some _ =>
            let (inner, r') := breakPromise fuel acc.2 rid cascadeReason
            (notif ++ inner, r'))
      ([], r0)

/-- `queued_count`. -/
def queuedCount (r : Reg) (id : Nat) : Nat := ((lookup r.queued id).getD []).length

/-- `promise_state`. -/
def promiseState (r : Reg) (id : Nat) : Option PState := lookup r.promises id

/-! ### §8b.1 — State-machine laws (proved). -/

/-- `lookup` of an APPENDED fresh key (not already present via the `find?` short-circuit) returns
the appended value when the key is new. Used for `create`. -/
theorem lookup_append_new {α} (xs : List (Nat × α)) (k : Nat) (v : α)
    (h : xs.find? (·.1 = k) = none) : lookup (xs ++ [(k, v)]) k = some v := by
  simp only [lookup, List.find?_append, h, List.find?_cons]
  simp

theorem create_then_pending (r : Reg)
    (hp : r.promises.find? (·.1 = r.nextId) = none)
    (hq : r.queued.find? (·.1 = r.nextId) = none) :
    let (id, r') := createPromise r
    promiseState r' id = some .pending ∧ queuedCount r' id = 0 := by
  refine ⟨?_, ?_⟩
  · simp only [createPromise, promiseState]; exact lookup_append_new r.promises r.nextId .pending hp
  · simp only [createPromise, queuedCount]
    rw [lookup_append_new r.queued r.nextId [] hq]; rfl

/-- **`broken_target_rejects_queue`** — queueing onto a BROKEN promise is rejected and the
registry is UNCHANGED (the `pipeline.rs:181` arm: `PromiseAlreadyBroken`, no mutation). -/
theorem broken_target_rejects_queue (r : Reg) (target msg : Nat) (rid? : Option Nat) (reason : String)
    (h : lookup r.promises target = some (.broken reason)) :
    pipelineMessage r target msg rid? = (false, r) := by
  simp only [pipelineMessage, h]

/-- On a `k`-keyed `map`-replace, `lookup` returns the replaced value WHEN `k` is present. -/
theorem lookup_map_replace {α} (xs : List (Nat × α)) (k : Nat) (v : α)
    (h : xs.any (·.1 = k)) :
    lookup (xs.map (fun p => if p.1 = k then (k, v) else p)) k = some v := by
  induction xs with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.map, lookup, List.find?_cons]
    by_cases hp : p.1 = k
    · simp [hp]
    · have hk : ((if p.1 = k then (k, v) else p).1 = k) = (p.1 = k) := by simp [hp]
      simp only [hp, if_false]
      simp only [List.any_cons, hp, decide_false, Bool.false_or] at h
      have := ih h
      simp only [lookup, decide_eq_true_eq, hp] at this ⊢
      simpa [hp] using this

/-- `lookup` of a `k`-keyed `upsert` returns the upserted value. -/
theorem upsert_lookup_self {α} (xs : List (Nat × α)) (k : Nat) (v : α) :
    lookup (upsert xs k v) k = some v := by
  simp only [upsert]
  by_cases hm : xs.any (·.1 = k)
  · simp only [hm, if_pos]
    exact lookup_map_replace xs k v hm
  · simp only [hm, if_neg, Bool.not_eq_true]
    have hnone : xs.find? (·.1 = k) = none := by
      rw [List.find?_eq_none]
      intro x hx
      have hfalse : ¬ xs.any (·.1 = k) = true := by simpa using hm
      intro hxk
      exact hfalse (List.any_eq_true.2 ⟨x, hx, hxk⟩)
    exact lookup_append_new xs k v hnone

/-- `erase`d key is absent. -/
theorem erase_lookup_self {α} (xs : List (Nat × α)) (k : Nat) :
    lookup (erase xs k) k = none := by
  simp only [lookup, erase]
  have : (xs.filter (·.1 ≠ k)).find? (·.1 = k) = none := by
    apply List.find?_eq_none.2
    intro x hx
    have hmem := List.mem_of_mem_filter hx
    have hne : x.1 ≠ k := by
      have := List.of_mem_filter hx
      simpa using this
    simpa using hne
  rw [this]; rfl

/-- **`resolve_clears_queue`** — after `resolve`, the promise's queue is EMPTY (a re-resolve
drains nothing) and the promise is `Fulfilled`. The drained list is exactly the FIFO queue. -/
theorem resolve_clears_queue (r : Reg) (id cell : Nat) :
    let (drained, r') := resolvePromise r id cell
    drained = (lookup r.queued id).getD []
      ∧ queuedCount r' id = 0
      ∧ promiseState r' id = some (.fulfilled cell) := by
  refine ⟨rfl, ?_, ?_⟩
  · simp only [resolvePromise, queuedCount, erase_lookup_self, Option.getD_none, List.length_nil]
  · simp only [resolvePromise, promiseState, upsert_lookup_self]

/-- **`resolve_preserves_fifo`** — the drained order IS the queue's insertion order: appending
`m` to a non-broken target then resolving yields the old queue with `m` last. This is the FIFO
tooth — `resolve` returns messages oldest-first, never reordered. -/
theorem resolve_preserves_fifo (r : Reg) (target msg cell : Nat) (rid? : Option Nat)
    (hp : ∃ st, lookup r.promises target = some st ∧ ∀ rs, st ≠ .broken rs) :
    let (ok, r1) := pipelineMessage r target msg rid?
    ok = true →
    (resolvePromise r1 target cell).1 = ((lookup r.queued target).getD []) ++ [(msg, rid?)] := by
  obtain ⟨st, hst, hnb⟩ := hp
  simp only [pipelineMessage, hst]
  cases st with
  | broken rs => exact absurd rfl (hnb rs)
  | pending =>
    intro _; simp only [resolvePromise, upsert_lookup_self, Option.getD_some]
  | fulfilled c =>
    intro _; simp only [resolvePromise, upsert_lookup_self, Option.getD_some]

/-! ### §8b.2 — A differential corpus the Rust harness replays against the REAL registry. -/

/-- A registry op the corpus drives (mirrors a `PipelineRegistry` method call). -/
inductive Op where
  | create
  | queue (target msg : Nat) (rid? : Option Nat)
  | resolve (id cell : Nat)
  | breakP (id : Nat) (reason : String)
  deriving Repr

/-- Run one op, projecting the observable the differential checks:
`(queuedCount-of-arg, promiseState-tag-of-arg, ok-bit)`. The Rust harness drives the SAME op
on the real `PipelineRegistry` and asserts these three observables agree. -/
def stepObs (r : Reg) : Op → (Reg × Nat × Nat × Bool)
  | .create => let (id, r') := createPromise r; (r', queuedCount r' id, 0, true)   -- tag 0 = pending
  | .queue t m rid? => let (ok, r') := pipelineMessage r t m rid?; (r', queuedCount r' t, stateTag (promiseState r' t), ok)
  | .resolve id c => let (_, r') := resolvePromise r id c; (r', queuedCount r' id, stateTag (promiseState r' id), true)
  | .breakP id rs => let (_, r') := breakPromise (r.promises.length + 1) r id rs; (r', queuedCount r' id, stateTag (promiseState r' id), true)
where
  /-- 0 = pending/absent, 1 = fulfilled, 2 = broken. -/
  stateTag : Option PState → Nat
    | none => 0
    | some .pending => 0
    | some (.fulfilled _) => 1
    | some (.broken _) => 2

/-- Fold a program of ops, collecting the per-step observable triple `(queuedCount, tag, ok)`. -/
def runProgram (r : Reg) : List Op → List (Nat × Nat × Bool)
  | [] => []
  | op :: rest =>
    let (r', qc, tag, ok) := stepObs r op
    (qc, tag, ok) :: runProgram r' rest

/-- **The differential corpus.** A program exercising create → FIFO queue ×2 → resolve (drains,
clears) → re-queue-on-fulfilled → break (clears, marks broken) → queue-on-broken (REJECTED).
The recorded observable column is what the Rust harness asserts against the REAL registry. -/
def pipelineDifferentialCorpus : List Op :=
  [ .create                                   -- id 0 ← Pending, qc 0
  , .queue 0 100 none                          -- qc 1, pending, ok
  , .queue 0 101 (some 7)                       -- qc 2 (FIFO append), pending, ok
  , .resolve 0 42                              -- drains [100,101], qc→0, fulfilled
  , .queue 0 102 none                          -- queue-on-fulfilled: qc 1, fulfilled, ok
  , .breakP 0 "remote gone"                    -- clears, qc 0, broken
  , .queue 0 103 none ]                        -- queue-on-broken: REJECTED, qc 0, broken, !ok

/-- The golden observable column for the corpus, proved by `decide` against the model. The Rust
differential pins the SAME `(queuedCount, stateTag, ok)` triples against the real
`PipelineRegistry`. A drift on EITHER side breaks: change the Rust state machine and the runtime
triples diverge; change the Lean model and this `decide` trips at build. -/
theorem pipelineDifferentialCorpus_observable :
    runProgram empty pipelineDifferentialCorpus
      = [ (0, 0, true)      -- create: id 0, qc 0, pending
        , (1, 0, true)      -- queue 100: qc 1, pending, ok
        , (2, 0, true)      -- queue 101: qc 2 (FIFO), pending, ok
        , (0, 1, true)      -- resolve: drained, qc 0, fulfilled
        , (1, 1, true)      -- queue-on-fulfilled: qc 1, fulfilled, ok
        , (0, 2, true)      -- break: cleared, qc 0, broken
        , (0, 2, false) ] := by   -- queue-on-broken: REJECTED (!ok)
  decide

/-- The FIFO drain order is observable too: resolving promise 0 after the two queues returns the
messages OLDEST-FIRST `[100, 101]`, not reordered. The Rust harness asserts the drained `Vec`'s
`action`/label order equals this. -/
theorem pipelineDifferentialCorpus_drain_order :
    let r0 := (createPromise empty).2
    let r1 := (pipelineMessage r0 0 100 none).2
    let r2 := (pipelineMessage r1 0 101 (some 7)).2
    (resolvePromise r2 0 42).1 = [(100, none), (101, some 7)] := by
  decide

end Registry

/-! ## §9 — Axiom-hygiene tripwires. Every PROVED keystone depends ONLY on the three standard
kernel axioms (no `sorryAx`). -/

#assert_axioms drainStep_preserves_caps
#assert_axioms drainAll_preserves_caps
#assert_axioms drainAll_head_authorized
#assert_axioms drainAll_tail
#assert_axioms overAuthorized_send_rejected
#assert_axioms drainAll_aborts_on_unauthorized_head
#assert_axioms break_freezes_state
#assert_axioms break_preserves_caps
#assert_axioms drainAll_conserves
#assert_axioms drain_realizes_seam
#assert_axioms Registry.create_then_pending
#assert_axioms Registry.broken_target_rejects_queue
#assert_axioms Registry.resolve_clears_queue
#assert_axioms Registry.resolve_preserves_fifo
#assert_axioms Registry.pipelineDifferentialCorpus_observable
#assert_axioms Registry.pipelineDifferentialCorpus_drain_order

end Dregg2.Exec.CapTPPipeline
