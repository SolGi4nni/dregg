/-
# Dregg2.Calculus.LinearInteractionTrace — a checked linear tensor fragment

This file gives a second, resource-sensitive proof-object route beside
`InteractionNetTrace`.  It is an intentionally small multiplicative fragment:

* an endpoint is an offered or demanded ticket of a finite resource kind;
* tensor composes endpoints without contraction or weakening;
* a matched offer/demand pair may interact, leaving a `closed` provenance node;
* exchange, associativity, and unit interactions only rearrange tensor structure;
* one-hole contexts locate a rule, and `replay` checks a finite local trace.

Two independent invariants make the linearity claim explicit.  `ticketCount`
counts the original endpoints represented by each ticket (a closed interaction
still accounts for both), while `ticketBalance` gives offers weight `+1` and
demands weight `-1`.  Every accepted trace preserves both observations and the
total provenance count.  In particular, the checker cannot silently duplicate,
erase, or close a mismatched resource.

This is not a complete interaction-net or proof-net formalism: it has no cut
elimination beyond the one matched endpoint interaction, no switching
criterion, exponentials, confluence, or normalization theorem.
-/
import Dregg2.Tactics

namespace Dregg2.Calculus.LinearInteractionTrace

/-! ## Typed resources and finite tensor nets -/

/-- A finite collection of resource wire types. -/
inductive ResourceKind where
  | coin
  | note
  | gas
  deriving DecidableEq, Repr

/-- The two endpoint polarities of a resource interaction. -/
inductive Polarity where
  | offer
  | demand
  deriving DecidableEq, Repr

/-- A resource wire is typed by its kind, ticket, and polarity.  Tickets prevent
an offer for one resource occurrence from closing an unrelated demand. -/
structure Port where
  kind : ResourceKind
  ticket : Nat
  polarity : Polarity
  deriving DecidableEq, Repr

/-- Finite sharing-free multiplicative nets.  `closed k i` is an explicit
receipt that the two endpoints of ticket `(k,i)` interacted; it is not an
erasure of their provenance. -/
inductive Net where
  | unit
  | port (wire : Port)
  | closed (kind : ResourceKind) (ticket : Nat)
  | tensor (left right : Net)
  deriving DecidableEq, Repr

/-- Structural size proves that every proof state is finite. -/
def Net.nodeCount : Net → Nat
  | .unit => 1
  | .port _ => 1
  | .closed _ _ => 1
  | .tensor l r => l.nodeCount + r.nodeCount + 1

/-- Number of original endpoints represented for one typed ticket.  A live port
represents one endpoint; a closed receipt represents the matched pair. -/
def Net.ticketCount : Net → ResourceKind → Nat → Nat
  | .unit, _, _ => 0
  | .port p, kind, ticket =>
      if p.kind = kind ∧ p.ticket = ticket then 1 else 0
  | .closed k i, kind, ticket =>
      if k = kind ∧ i = ticket then 2 else 0
  | .tensor l r, kind, ticket =>
      l.ticketCount kind ticket + r.ticketCount kind ticket

/-- Signed live balance for one typed ticket.  A matched closed pair has net
balance zero, just like the offer/demand pair from which it arose. -/
def Net.ticketBalance : Net → ResourceKind → Nat → Int
  | .unit, _, _ => 0
  | .port p, kind, ticket =>
      if p.kind = kind ∧ p.ticket = ticket then
        match p.polarity with
        | .offer => 1
        | .demand => -1
      else 0
  | .closed _ _, _, _ => 0
  | .tensor l r, kind, ticket =>
      l.ticketBalance kind ticket + r.ticketBalance kind ticket

/-- Total endpoint provenance represented by a net.  Unlike live-port count,
this remains two after a pair closes. -/
def Net.resourceCount : Net → Nat
  | .unit => 0
  | .port _ => 1
  | .closed _ _ => 2
  | .tensor l r => l.resourceCount + r.resourceCount

/-- Extensional resource semantics: every observer sees the endpoint count and
signed balance for every typed ticket. -/
def Net.denote (n : Net) : ResourceKind → Nat → Nat × Int :=
  fun kind ticket => (n.ticketCount kind ticket, n.ticketBalance kind ticket)

/-! ## Primitive local interactions -/

/-- Primitive multiplicative interactions.  Only `close` changes active
endpoints, and its constructor itself requires the same kind and ticket on both
sides.  The remaining rules are tensor coherence steps. -/
inductive ActiveRule where
  | close (kind : ResourceKind) (ticket : Nat)
  | exchange (left right : Net)
  | associateRight (left middle right : Net)
  | associateLeft (left middle right : Net)
  | unitLeft (body : Net)
  | unitRight (body : Net)
  deriving DecidableEq, Repr

def ActiveRule.lhs : ActiveRule → Net
  | .close kind ticket =>
      .tensor (.port ⟨kind, ticket, .offer⟩) (.port ⟨kind, ticket, .demand⟩)
  | .exchange l r => .tensor l r
  | .associateRight l m r => .tensor (.tensor l m) r
  | .associateLeft l m r => .tensor l (.tensor m r)
  | .unitLeft n => .tensor .unit n
  | .unitRight n => .tensor n .unit

def ActiveRule.rhs : ActiveRule → Net
  | .close kind ticket => .closed kind ticket
  | .exchange l r => .tensor r l
  | .associateRight l m r => .tensor l (.tensor m r)
  | .associateLeft l m r => .tensor (.tensor l m) r
  | .unitLeft n => n
  | .unitRight n => n

theorem activeRule_ticketCount (r : ActiveRule) (kind : ResourceKind) (ticket : Nat) :
    r.rhs.ticketCount kind ticket = r.lhs.ticketCount kind ticket := by
  cases r with
  | close k i =>
      by_cases h : k = kind ∧ i = ticket
      · simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount, h]
      · simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount, h]
  | exchange l r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount, Nat.add_comm]
  | associateRight l m r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount, Nat.add_assoc]
  | associateLeft l m r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount, Nat.add_assoc]
  | unitLeft n => simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount]
  | unitRight n => simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketCount]

theorem activeRule_ticketBalance (r : ActiveRule) (kind : ResourceKind) (ticket : Nat) :
    r.rhs.ticketBalance kind ticket = r.lhs.ticketBalance kind ticket := by
  cases r with
  | close k i =>
      by_cases h : k = kind ∧ i = ticket
      · simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance, h]
      · simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance, h]
  | exchange l r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance, add_comm]
  | associateRight l m r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance, add_assoc]
  | associateLeft l m r =>
      simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance, add_assoc]
  | unitLeft n => simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance]
  | unitRight n => simp [ActiveRule.lhs, ActiveRule.rhs, Net.ticketBalance]

theorem activeRule_resourceCount (r : ActiveRule) :
    r.rhs.resourceCount = r.lhs.resourceCount := by
  cases r <;>
    simp [ActiveRule.lhs, ActiveRule.rhs, Net.resourceCount,
      Nat.add_comm, Nat.add_assoc]

/-- Every primitive interaction preserves the extensional resource meaning. -/
theorem activeRule_preserves (r : ActiveRule) : r.rhs.denote = r.lhs.denote := by
  funext kind ticket
  exact Prod.ext (activeRule_ticketCount r kind ticket)
    (activeRule_ticketBalance r kind ticket)

/-! ## One-hole tensor contexts -/

/-- A zipper locating one active pair in a larger tensor net. -/
inductive Context where
  | hole
  | tensorLeft (inside : Context) (right : Net)
  | tensorRight (left : Net) (inside : Context)
  deriving DecidableEq, Repr

def Context.plug : Context → Net → Net
  | .hole, n => n
  | .tensorLeft c r, n => .tensor (c.plug n) r
  | .tensorRight l c, n => .tensor l (c.plug n)

theorem Context.plug_ticketCount_eq (c : Context) {before after : Net}
    (h : before.ticketCount kind ticket = after.ticketCount kind ticket) :
    (c.plug before).ticketCount kind ticket =
      (c.plug after).ticketCount kind ticket := by
  induction c with
  | hole => exact h
  | tensorLeft c right ih =>
      simpa [Context.plug, Net.ticketCount] using congrArg (fun n => n + right.ticketCount kind ticket) ih
  | tensorRight left c ih =>
      simpa [Context.plug, Net.ticketCount] using congrArg (fun n => left.ticketCount kind ticket + n) ih

theorem Context.plug_ticketBalance_eq (c : Context) {before after : Net}
    (h : before.ticketBalance kind ticket = after.ticketBalance kind ticket) :
    (c.plug before).ticketBalance kind ticket =
      (c.plug after).ticketBalance kind ticket := by
  induction c with
  | hole => exact h
  | tensorLeft c right ih =>
      simpa [Context.plug, Net.ticketBalance] using
        congrArg (fun n => n + right.ticketBalance kind ticket) ih
  | tensorRight left c ih =>
      simpa [Context.plug, Net.ticketBalance] using
        congrArg (fun n => left.ticketBalance kind ticket + n) ih

theorem Context.plug_resourceCount_eq (c : Context) {before after : Net}
    (h : before.resourceCount = after.resourceCount) :
    (c.plug before).resourceCount = (c.plug after).resourceCount := by
  induction c with
  | hole => exact h
  | tensorLeft c right ih =>
      simpa [Context.plug, Net.resourceCount] using
        congrArg (fun n => n + right.resourceCount) ih
  | tensorRight left c ih =>
      simpa [Context.plug, Net.resourceCount] using
        congrArg (fun n => left.resourceCount + n) ih

theorem contextualRule_ticketCount (c : Context) (r : ActiveRule)
    (kind : ResourceKind) (ticket : Nat) :
    (c.plug r.rhs).ticketCount kind ticket =
      (c.plug r.lhs).ticketCount kind ticket :=
  c.plug_ticketCount_eq (activeRule_ticketCount r kind ticket)

theorem contextualRule_ticketBalance (c : Context) (r : ActiveRule)
    (kind : ResourceKind) (ticket : Nat) :
    (c.plug r.rhs).ticketBalance kind ticket =
      (c.plug r.lhs).ticketBalance kind ticket :=
  c.plug_ticketBalance_eq (activeRule_ticketBalance r kind ticket)

theorem contextualRule_resourceCount (c : Context) (r : ActiveRule) :
    (c.plug r.rhs).resourceCount = (c.plug r.lhs).resourceCount :=
  c.plug_resourceCount_eq (activeRule_resourceCount r)

/-- A local interaction remains semantically sound under every tensor frame. -/
theorem contextualRule_preserves (c : Context) (r : ActiveRule) :
    (c.plug r.rhs).denote = (c.plug r.lhs).denote := by
  funext kind ticket
  exact Prod.ext (contextualRule_ticketCount c r kind ticket)
    (contextualRule_ticketBalance c r kind ticket)

/-! ## Executable local certificates and traces -/

/-- A checkable local step identifies both the rule and its exact tensor frame. -/
structure LocalCert where
  context : Context
  rule : ActiveRule
  deriving DecidableEq, Repr

def LocalCert.before (c : LocalCert) : Net := c.context.plug c.rule.lhs
def LocalCert.after (c : LocalCert) : Net := c.context.plug c.rule.rhs

def LocalCert.check (c : LocalCert) (before after : Net) : Bool :=
  decide (before = c.before ∧ after = c.after)

theorem localCheck_exact (c : LocalCert) (before after : Net) :
    c.check before after = true ↔ before = c.before ∧ after = c.after := by
  simp [LocalCert.check]

theorem localCheck_sound {c : LocalCert} {before after : Net}
    (h : c.check before after = true) : after.denote = before.denote := by
  rcases (localCheck_exact c before after).mp h with ⟨rfl, rfl⟩
  exact contextualRule_preserves c.context c.rule

theorem localCheck_preserves_resourceCount {c : LocalCert} {before after : Net}
    (h : c.check before after = true) :
    after.resourceCount = before.resourceCount := by
  rcases (localCheck_exact c before after).mp h with ⟨rfl, rfl⟩
  exact contextualRule_resourceCount c.context c.rule

/-- Apply a certificate only to its exact exposed source.  A rule with the
right name but wrong ticket, polarity, or location fails closed. -/
def applyCert (current : Net) (c : LocalCert) : Option Net :=
  if current = c.before then some c.after else none

theorem applyCert_sound {current next : Net} {c : LocalCert}
    (h : applyCert current c = some next) : next.denote = current.denote := by
  unfold applyCert at h
  split at h
  next heq =>
    simp only [Option.some.injEq] at h
    subst next
    rw [heq]
    exact contextualRule_preserves c.context c.rule
  next => contradiction

theorem applyCert_preserves_resourceCount {current next : Net} {c : LocalCert}
    (h : applyCert current c = some next) :
    next.resourceCount = current.resourceCount := by
  unfold applyCert at h
  split at h
  next heq =>
    simp only [Option.some.injEq] at h
    subst next
    rw [heq]
    exact contextualRule_resourceCount c.context c.rule
  next => contradiction

/-- Replay reconstructs every intermediate net and refuses at the first
certificate whose source does not exactly match the current state. -/
def replay : Net → List LocalCert → Option Net
  | current, [] => some current
  | current, c :: cs =>
      match applyCert current c with
      | none => none
      | some next => replay next cs

theorem replay_preserves : ∀ (certs : List LocalCert) (start finish : Net),
    replay start certs = some finish → finish.denote = start.denote := by
  intro certs
  induction certs with
  | nil =>
      intro start finish h
      simp only [replay, Option.some.injEq] at h
      subst finish
      rfl
  | cons c cs ih =>
      intro start finish h
      cases hstep : applyCert start c with
      | none => simp [replay, hstep] at h
      | some middle =>
          have htail : replay middle cs = some finish := by
            simpa [replay, hstep] using h
          exact (ih middle finish htail).trans (applyCert_sound hstep)

theorem replay_preserves_resourceCount :
    ∀ (certs : List LocalCert) (start finish : Net),
      replay start certs = some finish →
      finish.resourceCount = start.resourceCount := by
  intro certs
  induction certs with
  | nil =>
      intro start finish h
      simp only [replay, Option.some.injEq] at h
      subst finish
      rfl
  | cons c cs ih =>
      intro start finish h
      cases hstep : applyCert start c with
      | none => simp [replay, hstep] at h
      | some middle =>
          have htail : replay middle cs = some finish := by
            simpa [replay, hstep] using h
          exact (ih middle finish htail).trans
            (applyCert_preserves_resourceCount hstep)

def checkTrace (start : Net) (certs : List LocalCert) (finish : Net) : Bool :=
  decide (replay start certs = some finish)

theorem checkTrace_exact (start : Net) (certs : List LocalCert) (finish : Net) :
    checkTrace start certs finish = true ↔ replay start certs = some finish := by
  simp [checkTrace]

/-- Semantic soundness of accepted linear proof objects. -/
theorem checkTrace_sound {start finish : Net} {certs : List LocalCert}
    (h : checkTrace start certs finish = true) :
    finish.denote = start.denote :=
  replay_preserves certs start finish ((checkTrace_exact start certs finish).mp h)

/-- The requested global resource invariant: every accepted trace accounts for
exactly the same number of original endpoints at its finish as at its start. -/
theorem checkTrace_preserves_resourceCount
    {start finish : Net} {certs : List LocalCert}
    (h : checkTrace start certs finish = true) :
    finish.resourceCount = start.resourceCount :=
  replay_preserves_resourceCount certs start finish
    ((checkTrace_exact start certs finish).mp h)

/-- The stronger per-ticket linearity law exposed by semantic soundness. -/
theorem checkTrace_preserves_ticket
    {start finish : Net} {certs : List LocalCert}
    (h : checkTrace start certs finish = true)
    (kind : ResourceKind) (ticket : Nat) :
    finish.ticketCount kind ticket = start.ticketCount kind ticket ∧
      finish.ticketBalance kind ticket = start.ticketBalance kind ticket := by
  have hs := congrFun (congrFun (checkTrace_sound h) kind) ticket
  exact ⟨congrArg Prod.fst hs, congrArg Prod.snd hs⟩

/-! ## Non-vacuity and fail-closed refusals -/

namespace Reference

def offeredCoin7 : Net := .port ⟨.coin, 7, .offer⟩
def demandedCoin7 : Net := .port ⟨.coin, 7, .demand⟩
def gas9 : Net := .port ⟨.gas, 9, .offer⟩

def start : Net := .tensor (.tensor offeredCoin7 demandedCoin7) gas9
def middle : Net := .tensor (.closed .coin 7) gas9
def finish : Net := .tensor gas9 (.closed .coin 7)

def closeCoin7 : LocalCert :=
  ⟨.tensorLeft .hole gas9, .close .coin 7⟩

def exchangeClosed : LocalCert :=
  ⟨.hole, .exchange (.closed .coin 7) gas9⟩

theorem trace_checks :
    checkTrace start [closeCoin7, exchangeClosed] finish = true := by
  decide

theorem trace_preserves_resourceCount :
    finish.resourceCount = start.resourceCount :=
  checkTrace_preserves_resourceCount trace_checks

theorem trace_preserves_coin7 :
    finish.ticketCount .coin 7 = start.ticketCount .coin 7 ∧
      finish.ticketBalance .coin 7 = start.ticketBalance .coin 7 :=
  checkTrace_preserves_ticket trace_checks .coin 7

/-- A coin offer cannot close against a gas demand: the typed ticket mismatch is
part of the checked source graph, so replay refuses it. -/
def mismatchedStart : Net :=
  .tensor (.port ⟨.coin, 7, .offer⟩) (.port ⟨.gas, 7, .demand⟩)

theorem mismatched_kind_refused :
    checkTrace mismatchedStart [⟨.hole, .close .coin 7⟩] (.closed .coin 7) = false := by
  decide

/-- A certificate cannot be replayed at a different tensor location. -/
theorem wrong_location_refused :
    checkTrace start [⟨.hole, .close .coin 7⟩] middle = false := by
  decide

/-- There is no weakening certificate hidden in the rule table: claiming that
the unrelated gas endpoint disappeared is rejected even after a valid close. -/
theorem resource_erasure_refused :
    checkTrace start [closeCoin7] (.closed .coin 7) = false := by
  decide

end Reference

#assert_all_clean [
  activeRule_ticketCount,
  activeRule_ticketBalance,
  activeRule_resourceCount,
  activeRule_preserves,
  Context.plug_ticketCount_eq,
  Context.plug_ticketBalance_eq,
  Context.plug_resourceCount_eq,
  contextualRule_ticketCount,
  contextualRule_ticketBalance,
  contextualRule_resourceCount,
  contextualRule_preserves,
  localCheck_exact,
  localCheck_sound,
  localCheck_preserves_resourceCount,
  applyCert_sound,
  applyCert_preserves_resourceCount,
  replay_preserves,
  replay_preserves_resourceCount,
  checkTrace_exact,
  checkTrace_sound,
  checkTrace_preserves_resourceCount,
  checkTrace_preserves_ticket,
  Reference.trace_checks,
  Reference.trace_preserves_resourceCount,
  Reference.trace_preserves_coin7,
  Reference.mismatched_kind_refused,
  Reference.wrong_location_refused,
  Reference.resource_erasure_refused
]

end Dregg2.Calculus.LinearInteractionTrace
