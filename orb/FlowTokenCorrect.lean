import H2.FlowControl

/-!
# Correctness of flow-control credit accounting (RFC 9113 §5.2.1, §6.9, §6.9.1)

A credit-based flow-control scheme keeps, per window, a running account of how
much data the peer has authorised. The account is a ledger of three integers:

* the credit **granted** so far — the initial `SETTINGS_INITIAL_WINDOW_SIZE`
  plus every `WINDOW_UPDATE` increment received;
* the credit **consumed** so far — the total DATA payload octets charged;
* the credit **available** now — what remains sendable.

The specification the account must satisfy is *conservation*:

    available = granted − consumed,   and   available ≥ 0,

with the two update laws that give the ledger its arithmetic meaning:

* **grant of `g`** (a `WINDOW_UPDATE`, RFC 9113 §6.9) adds *exactly* `g` to both
  `available` and `granted`;
* **consume of `d`** (emitting a DATA frame of length `d`, RFC 9113 §6.9.1)
  subtracts *exactly* `d` from `available` and adds *exactly* `d` to `consumed`;

and the sendability rule (RFC 9113 §5.2.1 / §6.9.1): a consume of `d` is
**blocked** — the sender MUST NOT emit it — precisely when `d` exceeds the
available credit.

The companion `H2FlowCorrect` refines the *window value* arithmetic (that a
`WINDOW_UPDATE` of `N` moves the window by `N`, that a DATA charge moves it by the
frame length, that the sender never over-sends) but states, in its own words,
that it "says nothing about the ledger". This module supplies exactly that
missing piece: an **independent credit-ledger specification** — the
`granted`/`consumed`/`available` account and its conservation law, with no
reference to the implementation's `Window` structure, its `Except` result type,
or its per-operation window arithmetic — and a **refinement** proving the
deployed `H2.FlowControl` accounting realises it: the deployed window's projected
ledger is conserved and non-negative at every reachable state under any
interleaving of grants and sends, a grant adds exactly `g` to the granted total,
a consume subtracts exactly `d` from available, and a send is blocked exactly when
it exceeds credit.

The ledger integers are `Int`. Over `Nat`, "available never goes negative" would
be vacuous; the point of the safety half of conservation is that the signed
decrement stays non-negative.

## The RFC text specified here

* **RFC 9113 §5.2.1 (Flow-Control Principles):** "Senders … send data up to the
  limit their receiver allows." — a send is blocked when it exceeds the credit.
* **RFC 9113 §6.9 (WINDOW_UPDATE):** "the number of octets that the sender can
  transmit in addition to the existing flow-control window." — a grant of `g`
  adds exactly `g` to the credit.
* **RFC 9113 §6.9.1 (The Flow-Control Window):** "the sender reduces the space
  available … by the length of the transmitted frame." — a consume of `d`
  subtracts exactly `d`. "The sender MUST NOT send a flow-controlled frame with a
  length that exceeds the space available." The account is therefore the running
  identity `available = granted − consumed`, kept non-negative.
-/

namespace FlowCreditSpec

/-! ## The independent specification (RFC 9113 §5.2.1, §6.9, §6.9.1), over a plain
integer ledger — no reference to the implementation. -/

/-- The three-integer credit account. `available` is the live sendable credit;
`granted` is the total credit ever advertised (initial window plus every
`WINDOW_UPDATE` increment); `consumed` is the total DATA octets ever charged. -/
structure Ledger where
  /-- Currently sendable credit. -/
  available : Int
  /-- Total credit ever granted (initial + every `WINDOW_UPDATE`). -/
  granted : Int
  /-- Total DATA octets ever consumed. -/
  consumed : Int
deriving Repr, DecidableEq

/-- **The conservation law (RFC 9113 §6.9.1).** The credit available now equals
the total granted minus the total consumed. -/
def Ledger.Conserved (l : Ledger) : Prop := l.available = l.granted - l.consumed

/-- **Grant of `g` (RFC 9113 §6.9).** A `WINDOW_UPDATE` of `g` adds *exactly* `g`
to the available credit and to the granted total; it consumes nothing. -/
def Ledger.grant (l : Ledger) (g : Int) : Ledger :=
  ⟨l.available + g, l.granted + g, l.consumed⟩

/-- **Consume of `d` (RFC 9113 §6.9.1).** Emitting a DATA frame of length `d`
subtracts *exactly* `d` from the available credit and adds *exactly* `d` to the
consumed total; it grants nothing. -/
def Ledger.consume (l : Ledger) (d : Int) : Ledger :=
  ⟨l.available - d, l.granted, l.consumed + d⟩

/-- **Blocked (RFC 9113 §5.2.1 / §6.9.1).** A consume of `d` is blocked — the
sender MUST NOT emit it — exactly when `d` exceeds the available credit. -/
def Ledger.blocked (l : Ledger) (d : Int) : Prop := l.available < d

/-! ### The specification is internally coherent: the laws are the RFC's, and
conservation is preserved by both operations. -/

/-- A grant adds exactly `g` to the available credit. -/
theorem grant_available (l : Ledger) (g : Int) :
    (l.grant g).available = l.available + g := rfl

/-- A grant adds exactly `g` to the granted total and leaves consumed untouched. -/
theorem grant_ledger (l : Ledger) (g : Int) :
    (l.grant g).granted = l.granted + g ∧ (l.grant g).consumed = l.consumed :=
  ⟨rfl, rfl⟩

/-- A consume subtracts exactly `d` from the available credit. -/
theorem consume_available (l : Ledger) (d : Int) :
    (l.consume d).available = l.available - d := rfl

/-- A consume adds exactly `d` to the consumed total and leaves granted untouched. -/
theorem consume_ledger (l : Ledger) (d : Int) :
    (l.consume d).consumed = l.consumed + d ∧ (l.consume d).granted = l.granted :=
  ⟨rfl, rfl⟩

/-- **Grants preserve conservation.** -/
theorem grant_conserved {l : Ledger} (g : Int) (h : l.Conserved) :
    (l.grant g).Conserved := by
  unfold Ledger.Conserved at h ⊢; unfold Ledger.grant; simp; omega

/-- **Consumes preserve conservation.** -/
theorem consume_conserved {l : Ledger} (d : Int) (h : l.Conserved) :
    (l.consume d).Conserved := by
  unfold Ledger.Conserved at h ⊢; unfold Ledger.consume; simp; omega

/-- **A non-blocked consume keeps available non-negative** (RFC 9113 §6.9.1: the
sender never drives the window below zero). -/
theorem consume_nonneg {l : Ledger} (d : Int)
    (_hlo : 0 ≤ l.available) (hok : ¬ l.blocked d) : 0 ≤ (l.consume d).available := by
  unfold Ledger.blocked at hok
  show (0 : Int) ≤ l.available - d
  omega

/-- **Conservation is the accounting identity the SPEC names**: consumed equals
granted minus available. -/
theorem consumed_eq {l : Ledger} (h : l.Conserved) :
    l.consumed = l.granted - l.available := by
  unfold Ledger.Conserved at h; omega

/-! ### Non-vacuity of the specification: the laws genuinely discriminate. A
specification realised by wrong arithmetic would be useless; these show the RFC
laws reject mis-accounting. -/

/-- The grant law is non-trivial: a mutant that added `2·g` (double-counted a
`WINDOW_UPDATE`) contradicts it whenever `g ≠ 0`. -/
theorem doubling_grant_violates :
    ¬ ∀ (l : Ledger) (g : Int), (l.grant g).available = l.available + 2 * g := by
  intro h
  have := h ⟨0, 0, 0⟩ 1
  simp [Ledger.grant] at this

/-- The consume law is non-trivial: a mutant that subtracted `d − 1` (undercounted
an emitted frame) contradicts it whenever `d ≠ 0`. -/
theorem undercount_consume_violates :
    ¬ ∀ (l : Ledger) (d : Int), (l.consume d).available = l.available - (d - 1) := by
  intro h
  have := h ⟨0, 0, 0⟩ 1
  simp [Ledger.consume] at this

/-- Blocked genuinely discriminates: sending 5 against 3 credit is blocked, sending
2 is not. A sender that emitted the 5-octet frame would over-send. -/
theorem blocked_discriminates :
    (⟨3, 0, 0⟩ : Ledger).blocked 5 ∧ ¬ (⟨3, 0, 0⟩ : Ledger).blocked 2 := by
  unfold Ledger.blocked; decide

/-- **Over-sending breaks conservation-with-safety.** A consume of `d` strictly
greater than the available credit (a blocked send emitted anyway) drives available
negative — the state the RFC forbids. -/
theorem oversend_goes_negative {l : Ledger} (d : Int)
    (_hlo : 0 ≤ l.available) (hblk : l.blocked d) : (l.consume d).available < 0 := by
  unfold Ledger.blocked at hblk
  show l.available - d < 0
  omega

end FlowCreditSpec

/-! ## The refinement: the deployed `H2.FlowControl` accounting realises the credit
ledger specification.

The deployed credit primitives are `H2.FlowControl.Window` (a live window plus its
`initial`/`increments`/`consumed` ledger fields), the grant primitive
`H2.FlowControl.windowUpdate`, the consume primitive `H2.FlowControl.Window.charge`,
and the two-window send transition system `H2.FlowControl.Send` that the HTTP/2 send
path steps. The refinement projects each deployed window onto a `FlowCreditSpec.Ledger`
and shows the projection obeys every SPEC law on all inputs, and that the projection
is conserved and non-negative at every reachable state of the deployed transition
system. -/

namespace FlowTokenCorrect

open FlowCreditSpec
open H2.FlowControl

/-- **The abstraction map.** The credit ledger a deployed `Window` presents:
available = the live window; granted = the initial window plus every applied
`WINDOW_UPDATE` increment; consumed = the charged DATA total. It forgets nothing
the SPEC observes and adds nothing. -/
def creditOf (w : Window) : Ledger :=
  ⟨w.window, w.initial + w.increments, w.consumed⟩

/-- **Refinement 0 — the deployed conservation invariant IS the SPEC's.** The
implementation's `Window.Conserved` holds exactly when the projected ledger is
`FlowCreditSpec`-conserved: `available = granted − consumed`. -/
theorem creditOf_conserved_iff (w : Window) :
    (creditOf w).Conserved ↔ w.Conserved := Iff.rfl

/-- **Refinement A — a DATA charge is a SPEC consume (RFC 9113 §6.9.1).** The
deployed `Window.charge d` projects to exactly `(creditOf w).consume d`: it
subtracts exactly `d` from available and adds exactly `d` to consumed, granting
nothing. A `charge` that moved the window by anything but `d`, or that disturbed
the granted total, would break this equality. -/
theorem charge_refines_consume (w : Window) (d : Int) :
    creditOf (w.charge d) = (creditOf w).consume d := rfl

/-- **Refinement B — a `WINDOW_UPDATE` is a SPEC grant (RFC 9113 §6.9).** When the
deployed `windowUpdate w g` accepts, the successor projects to exactly
`(creditOf w).grant g`: it adds exactly `g` to available and to the granted total,
consuming nothing. A grant that credited anything but `g` would break this. -/
theorem windowUpdate_refines_grant {w w' : Window} {g : Int}
    (hok : windowUpdate w g = .ok w') : creditOf w' = (creditOf w).grant g := by
  unfold windowUpdate at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · rw [Except.ok.injEq] at hok
      subst hok
      show (⟨w.window + g, w.initial + (w.increments + g), w.consumed⟩ : Ledger)
        = ⟨w.window + g, (w.initial + w.increments) + g, w.consumed⟩
      simp [Ledger.grant]; omega

/-- **Refinement C — a created window is a conserved, non-negative ledger**
(RFC 9113 §6.5.2 / §6.9.1). The window created from a valid
`SETTINGS_INITIAL_WINDOW_SIZE` projects to a ledger with `available = granted` and
`consumed = 0`, conserved and non-negative. -/
theorem create_refines {initSize : Int} {w : Window} (h : create initSize = .ok w) :
    (creditOf w).Conserved ∧ 0 ≤ (creditOf w).available ∧ (creditOf w).consumed = 0 := by
  obtain ⟨hcons, hlo, _⟩ := create_WF h
  exact ⟨hcons, hlo, by
    unfold create at h
    split at h
    · exact absurd h (by simp)
    · rw [Except.ok.injEq] at h; subst h; rfl⟩

/-! ### The blocked characterisation on the deployed send path. -/

/-- **The deployed sendable credit** projected as a SPEC ledger's `available`:
`Send.credit = max 0 (min conn stream)`, the smaller of the two windows floored at
zero. -/
def sendLedger (s : Send) : Ledger := ⟨s.credit, 0, 0⟩

/-- **Refinement D — a send is blocked exactly when it exceeds credit**
(RFC 9113 §5.2.1 / §6.9.1). For a non-negative offer `d`, the deployed
`Send.sendData` parks a nonzero remainder — i.e. cannot emit the whole frame —
precisely when `d` exceeds the available credit (`Ledger.blocked`). Contrapositive:
the frame emits in full exactly when it fits under the credit. -/
theorem sendData_blocked_iff (s : Send) (d : Int) (_hd : 0 ≤ d) :
    0 < (s.sendData d).parked ↔ (sendLedger s).blocked d := by
  have hcn := s.credit_nonneg
  unfold Ledger.blocked sendLedger Send.sendData Send.credit
  show 0 < d - min d (max 0 (min s.conn.window s.stream.window)) ↔
    max 0 (min s.conn.window s.stream.window) < d
  omega

/-- **Refinement E — a send never over-consumes credit** (RFC 9113 §6.9.1). The
octets the deployed send actually emits — the amount charged against each window —
never exceed the available credit. Combined with Refinement A this is exactly
"consume of `emitted` is not blocked", so the emitted charge keeps available
non-negative. -/
theorem sendData_emitted_le_credit (s : Send) (d : Int) :
    (s.sendData d).emitted ≤ s.credit := by
  have hcn := s.credit_nonneg
  show min d s.credit ≤ s.credit
  omega

/-! ### Trace-level conservation: the deployed transition system stays a conserved,
non-negative ledger under any interleaving of grants and sends. -/

/-- **Refinement F — every reachable deployed state is a conserved ledger**
(RFC 9113 §6.9.1, whole-of-trace). From a well-formed start, under any sequence of
valid operations (DATA sends and connection/stream `WINDOW_UPDATE`s), both the
connection and the stream windows project to `FlowCreditSpec`-conserved ledgers:
`available = granted − consumed`. -/
theorem run_credit_conserved {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    (creditOf (s.run ops).conn).Conserved ∧ (creditOf (s.run ops).stream).Conserved := by
  obtain ⟨hc, hs⟩ := Send.run_conserved hwf hv
  exact ⟨(creditOf_conserved_iff _).mpr hc, (creditOf_conserved_iff _).mpr hs⟩

/-- **Refinement G — every reachable deployed state has non-negative credit**
(RFC 9113 §6.9.1, whole-of-trace). No send ever drives either projected ledger's
`available` below zero, under any interleaving. -/
theorem run_credit_nonneg {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    0 ≤ (creditOf (s.run ops).conn).available ∧
    0 ≤ (creditOf (s.run ops).stream).available :=
  Send.run_windows_nonneg hwf hv

/-- **Refinement H — the accounting identity at every reachable state**
(RFC 9113 §6.9.1): total consumed = total granted − available, for both windows.
This is the SPEC's headline conservation claim, discharged against the deployed
run. -/
theorem run_consumed_eq {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    (creditOf (s.run ops).conn).consumed =
        (creditOf (s.run ops).conn).granted - (creditOf (s.run ops).conn).available ∧
    (creditOf (s.run ops).stream).consumed =
        (creditOf (s.run ops).stream).granted - (creditOf (s.run ops).stream).available := by
  obtain ⟨hc, hs⟩ := run_credit_conserved hwf hv
  exact ⟨consumed_eq hc, consumed_eq hs⟩

/-! ### Refinement on concrete vectors, and mutant rejection. The equalities above
are universally quantified; these ground them and exhibit the discrimination — the
deployed accounting hits the SPEC value, and named wrong outputs miss it. -/

/-- A grant of 50 against a live window of 100 projects to the SPEC grant: available
150, granted total 150. A double-counting mutant (granted 200) is not this value. -/
example :
    creditOf (match windowUpdate ⟨100, 100, 0, 0⟩ 50 with | .ok w => w | .error _ => ⟨0,0,0,0⟩)
      = (creditOf ⟨100, 100, 0, 0⟩).grant 50
    ∧ (creditOf ⟨100, 100, 0, 0⟩).grant 50 = ⟨150, 150, 0⟩
    ∧ ((⟨100, 100, 0⟩ : Ledger).available + 2 * 50) ≠ 150 := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- A DATA charge of 40 projects to the SPEC consume: available 60, consumed 40. An
undercounting mutant (available 61, as if only 39 were charged) is not this value. -/
example :
    creditOf ((⟨100, 100, 0, 0⟩ : Window).charge 40) = (creditOf ⟨100, 100, 0, 0⟩).consume 40
    ∧ (creditOf ⟨100, 100, 0, 0⟩).consume 40 = ⟨60, 100, 40⟩
    ∧ ((⟨60, 100, 40⟩ : Ledger).available) ≠ 61 := by
  refine ⟨rfl, rfl, ?_⟩; decide

/-- A send offered 50 octets against 30 credit is blocked (parks a remainder) and
emits exactly the 30 the credit allows; emitting the full 50 would over-consume
(`Ledger.blocked` holds), and consuming 50 against 30 credit drives available to
`-20 < 0`. The deployed send refuses precisely that. -/
example :
    0 < (Send.sendData ⟨⟨30, 100, 0, 70⟩, ⟨100, 100, 0, 0⟩⟩ 50).parked
    ∧ (Send.sendData ⟨⟨30, 100, 0, 70⟩, ⟨100, 100, 0, 0⟩⟩ 50).emitted = 30
    ∧ ((⟨30, 30, 0⟩ : Ledger).consume 50).available = -20 := by
  refine ⟨by decide, by decide, by decide⟩

end FlowTokenCorrect
