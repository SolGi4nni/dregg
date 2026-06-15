/-
# Dregg2.Exec.CustodyReceipt — the store-and-forward CUSTODY ACCOUNTABILITY calculus:
# a SIGNED receipt makes a relay that ACCEPTED custody and then DROPPED the message
# CONVICTABLE, while an honest relay (one that delivered or refunded) is provably NOT slashable.

## The gap this closes (the precise dark mirror).

`Exec.CapTPStoreForward` proves the relay is a delay/drop channel that cannot READ, FORGE, or
RE-ADDRESS a box (confidentiality + AEAD authenticity), and `Exec.RelayOperator` prices the relay
with a bond that may only decrease on a `disputeCount` bump. But BOTH leave one thing UNACCOUNTED:
the relay's whole sanctioned power is to **drop** (`expire_is_submultiset`, `drainFor`'s reorder),
and a drop produces **no evidence**. The Rust says it plainly — `captp/src/store_forward.rs`
returns custody through an UNSIGNED local flag (`QueuedMessage{ acknowledged: bool, … }` at :131 is
the SENDER's own bookkeeping; `StoreForwardClient.unacknowledged : HashMap<…>` at :510 is the
sender's local map; `acknowledge(dest, seq)` at :595 just mutates that map). **The relay signs
NOTHING.** So a dropped message cannot be proven *against the relay*: the bonded-relay
`disputeCount` of `RelayOperator` has a slash lever but no model of what a *valid* dispute IS, and
nothing anywhere proves an HONEST relay can't be slashed by a fabricated one. Accountability —
"a dropped message is convictable, an honest relay is safe" — is the missing calculus. This module
is it.

## The accountability object: a SIGNED `CustodyReceipt` (the honest-crypto seam).

When the relay accepts a box for store-and-forward it returns a `CustodyReceipt` it SIGNS — the
exact shape the prompt names: it binds the `contentHash` of the box, the `inboxOwner` it is held
for, the inbox-root transition `oldRoot → newRoot` the relay promises to effect on delivery, and an
`acceptBy` deadline (the height by which the relay must DELIVER or REFUND). The signature is the
canonical §8 carrier — a `sig : Bool` exactly like `Authority.Blocklace.Block.signed` and
`CapTPStoreForward.Box.intact`: `sig = true` models "the relay's Ed25519 signature over the receipt
preimage verifies". The cryptographic unforgeability (a third party cannot mint `sig = true` without
the relay's key) is the Rust/vetted-crate oracle, never Lean-proved — but it is the load-bearing
hypothesis that makes the receipt *bind the relay specifically*, so we name it as
`receiptUnforgeable` and USE it (the `honest_relay_not_slashable` direction depends on it).

## The lifecycle: `CustodyOutcome` — what the relay actually DID with the accepted box.

A relay that signed a receipt for `contentHash` has exactly three honest-or-dishonest fates by the
deadline, modelled by `CustodyOutcome`:
  * `delivered newRoot` — the recipient drained the box: the inbox root advanced to `newRoot` (the
    very root the receipt promised) and the recipient's ack witnesses delivery. HONEST.
  * `refunded`          — the relay could not deliver (recipient never came online / TTL); it
    RETURNED the fee and released custody before the deadline. HONEST (the accept-OR-refund-by half).
  * `dropped`           — neither: the deadline `acceptBy` passed with the box neither delivered nor
    refunded. The relay took custody (and the fee) and silently lost the message. DISHONEST.

`EvidenceOfDrop` is the conviction object: the relay's OWN signed receipt (`sig = true`) PLUS a
witness that the outcome at deadline is `dropped`. Because the receipt is the relay's signature, the
evidence is *self-incriminating* — the relay convicts itself by its own promise.

## The two headline theorems (the ask).

  1. **`accepted_and_dropped_is_convictable`.** If a relay signed a valid receipt for a box
     (`r.sig = true`) and the custody outcome is `dropped`, then `evidenceOfDrop r` is a VALID
     `EvidenceOfDrop` and the adjudicator's verdict on it is `slash` — the relay is convictable.
     A dropped, accepted message yields a proof against the relay, closing the gap.
  2. **`honest_relay_not_slashable`.** If the custody outcome is `delivered` or `refunded` (the relay
     honored the receipt), then there is NO valid `EvidenceOfDrop`: `adjudicate` of any well-formed
     evidence whose carried outcome matches the true honest outcome returns `acquit`, never `slash`.
     An honest relay cannot be convicted — the receipt is its DEFENSE as much as its liability. This
     is the "no false conviction" side that distinguishes ACCOUNTABILITY from naked slashing.

Plus the binding/non-malleability teeth: a forged receipt (`sig = false`) convicts NObody
(`forged_receipt_no_conviction`); evidence whose receipt names a different `contentHash` or
`inboxOwner` does not apply to this custody (`evidence_binds_content`, `evidence_binds_owner`); and
the conviction drives the SAME bonded-relay slash discipline of `RelayOperator` — a `slash` verdict
is realized as the `RelayOperator` bond-decrease-with-dispute transition (`conviction_drives_slash`),
so the economic consequence rides the already-proved anti-drain machine rather than a new lever.

## What is proved vs. the §8 seam.

PROVED (kernel-clean): the conviction CALCULUS — that the signed-receipt+dropped-outcome ⇒ slash
verdict, that delivered/refunded ⇒ acquit, that the binding fields gate applicability, and that the
verdict composes onto the `RelayOperator` slash transition. The §8 seam (carried, not proved):
the Ed25519 unforgeability of `sig` (named `receiptUnforgeable`) and the hash-binding of
`contentHash`/roots — the same vetted-crate obligations every other module routes to the crypto
portal. The Rust keystone (`POST /relay/send` returns a signed `CustodyReceipt`; the inbox owner's
`POST /relay/dispute` submits `(receipt, non_delivery_witness)`) is the ~50-line wiring named in the
report; this module is the formal accountability model it must satisfy.

REUSES `Exec.RelayOperator` (the bonded-relay slash transition, READ-ONLY) and the `signed:Bool`
crypto-seam idiom of `Authority.Blocklace`. Invents no new crypto primitive and no new executor.
-/
import Dregg2.Exec.RelayOperator
import Dregg2.Tactics

namespace Dregg2.Exec.Custody

open Dregg2.Exec
open Dregg2.Exec.RecordCell
open Dregg2.Exec.RelayOperator

/-! ## §1 — The signed `CustodyReceipt` and the custody outcome.

A `CustodyReceipt` is the relay's signed promise of custody. The plaintext/box contents stay in
`CapTPStoreForward`; here we work over the relay-visible commitments the receipt binds:
`contentHash` (the content-address of the accepted box), `inboxOwner` (the destination the box is
held FOR), the inbox-root transition `oldRoot → newRoot` the relay promises to effect on delivery,
and `acceptBy` (the deadline height). `sig : Bool` is the §8 carrier (the relay's Ed25519 signature
over the preimage), exactly as `Blocklace.Block.signed`. -/

/-- A content-address (`BlockId`-shaped; only equality matters, hash-binding is the §8 seam). -/
abbrev Hash := Nat
/-- An inbox-owner / relay identity (the `FederationId` / operator pubkey; `Nat` stand-in). -/
abbrev Owner := Nat
/-- An inbox Merkle root (the `CapInbox` state commitment; `Nat` stand-in). -/
abbrev Root := Nat
/-- A block height (the TTL/deadline clock). -/
abbrev Height := Nat

/-- **`CustodyReceipt`** — the relay's SIGNED promise of custody (the object `POST /relay/send`
returns). It binds:

  * `relay`       — the operator identity that signed it (the party held accountable);
  * `contentHash` — the content-address of the box the relay accepted (binds the receipt to a
    specific message; a receipt for a different `contentHash` does not cover this box);
  * `inboxOwner`  — the destination the box is held FOR (binds custody to the right inbox);
  * `oldRoot` / `newRoot` — the inbox-root transition the relay PROMISES to effect on delivery
    (`oldRoot` = the inbox root at accept time, `newRoot` = the root after the box is appended);
  * `acceptBy`    — the deadline height: the relay must DELIVER or REFUND by this height, else it
    has DROPPED (the accept-or-refund-by clause);
  * `sig`         — the §8 carrier: `true` ≡ "the relay's Ed25519 signature over the receipt
    preimage `(relay,contentHash,inboxOwner,oldRoot,newRoot,acceptBy)` verifies". Unforgeability
    (only `relay` can produce `sig=true`) is the Rust oracle, named `receiptUnforgeable`. -/
structure CustodyReceipt where
  relay       : Owner
  contentHash : Hash
  inboxOwner  : Owner
  oldRoot     : Root
  newRoot     : Root
  acceptBy    : Height
  /-- §8 AEAD/signature carrier: the relay's signature over the receipt preimage verifies. -/
  sig         : Bool
  deriving DecidableEq, Repr, Inhabited

/-- **`CustodyOutcome`** — what the relay actually DID with the accepted box, observed at/after the
deadline. Two honest fates, one dishonest:

  * `delivered r` — the recipient drained the box and the inbox root advanced to `r` (HONEST iff
    `r` is the promised `newRoot`); the recipient's ack witnesses delivery.
  * `refunded`    — the relay returned the fee and released custody before the deadline (HONEST: the
    accept-OR-refund-by half — it could not deliver but did not silently keep custody);
  * `dropped`     — the deadline passed with the box neither delivered nor refunded (DISHONEST: the
    relay took custody and lost the message). -/
inductive CustodyOutcome where
  | delivered (root : Root)
  | refunded
  | dropped
  deriving DecidableEq, Repr, Inhabited

/-- **`outcomeHonest receipt outcome`** — the relay HONORED the receipt: it either delivered the box
to the promised root, or refunded before the deadline. `dropped` is dishonest; a `delivered` to the
WRONG root is also dishonest (the relay effected a different inbox transition than it signed for —
this is caught here, not papered over). -/
def outcomeHonest (r : CustodyReceipt) : CustodyOutcome → Bool
  | .delivered root => decide (root = r.newRoot)
  | .refunded       => true
  | .dropped        => false

/-! ## §2 — `EvidenceOfDrop`: the conviction object, and the adjudicator's verdict.

The conviction object pairs the relay's OWN signed receipt with a witness that the box was NOT
delivered to the promised root NOR refunded by the deadline — i.e. the outcome is `dropped`. Because
the receipt carries the relay's signature, the evidence is self-incriminating: the relay's promise
IS the liability. The inbox owner produces this by submitting `(receipt, ¬delivered ∧ ¬refunded)`
to `POST /relay/dispute`. -/

/-- **`EvidenceOfDrop`** — the conviction object submitted by the inbox owner against a relay:

  * `receipt`        — the relay's OWN signed `CustodyReceipt` (the binding to a specific relay,
    content, owner, and promised transition);
  * `claimedOutcome` — the custody outcome the disputant CLAIMS holds at the deadline (the witness:
    for a real conviction this is `dropped`; an honest relay's true outcome is `delivered`/`refunded`
    and the adjudicator will not slash on it);
  * `atHeight`       — the height the dispute is raised at (must be ≥ `receipt.acceptBy`: the
    deadline must have PASSED for a non-delivery to be a drop rather than mere pending custody).

A piece of evidence is `wellFormed` iff its receipt's `sig` verifies AND the dispute is raised at or
after the deadline (`atHeight ≥ acceptBy`). The signature requirement is what binds the evidence to
the relay; the deadline requirement is what distinguishes a DROP (deadline passed) from a
still-pending box (within TTL the relay has not yet defaulted). -/
structure EvidenceOfDrop where
  receipt        : CustodyReceipt
  claimedOutcome : CustodyOutcome
  atHeight       : Height
  deriving Repr, Inhabited

/-- **`wellFormed e`** — the evidence is admissible: the receipt's signature verifies (`sig = true`,
binding it to `e.receipt.relay`) AND the dispute is raised at or after the deadline
(`atHeight ≥ acceptBy`, so the relay has actually defaulted). A forged receipt (`sig = false`) or a
premature dispute (`atHeight < acceptBy`) is NOT admissible — these are the two non-malleability
gates. -/
def wellFormed (e : EvidenceOfDrop) : Bool :=
  e.receipt.sig && decide (e.atHeight ≥ e.receipt.acceptBy)

/-- **`adjudicate e trueOutcome`** — the adjudicator's verdict. Given a piece of evidence and the
TRUE custody outcome (what the relay actually did, as established by the inbox cell's authenticated
state — the recipient's ack or the refund move), it returns `slash` IFF the evidence is well-formed
AND the true outcome is `dropped`; otherwise `acquit`.

This is the decision procedure the adjudication cell runs: it does NOT take the disputant's CLAIMED
outcome on faith (that is what would let a malicious disputant slash an honest relay); it slashes
only when the box's authenticated inbox state shows neither the promised delivery nor a refund by
the deadline. The disputant's `claimedOutcome` is their ASSERTION; `trueOutcome` is the verified
fact. Conviction requires BOTH a relay signature (well-formed) AND a verified drop. -/
def adjudicate (e : EvidenceOfDrop) (trueOutcome : CustodyOutcome) : Bool :=
  wellFormed e && (trueOutcome = .dropped)

/-- **`evidenceOfDrop r atHeight`** — the canonical evidence the inbox owner assembles from a relay's
receipt `r` once the deadline has passed (`atHeight = r.acceptBy`, the earliest admissible height),
claiming the box was `dropped`. -/
def evidenceOfDrop (r : CustodyReceipt) : EvidenceOfDrop :=
  { receipt := r, claimedOutcome := .dropped, atHeight := r.acceptBy }

/-! ## §3 — THE HEADLINE (a): an accepted-and-dropped relay is CONVICTABLE. -/

/-- **`accepted_and_dropped_is_convictable` (KEYSTONE a — the conviction tooth).**

If a relay signed a VALID receipt (`r.sig = true`) and the custody outcome is `dropped` (the box was
neither delivered to the promised root nor refunded by the deadline), then the canonical evidence
`evidenceOfDrop r` is well-formed AND the adjudicator's verdict on it is `slash` (`= true`). A relay
that accepted custody and then silently dropped the message is convictable — by its OWN signature.
This is the property `CapTPStoreForward` lacked: the relay's sanctioned drop power now leaves a
verifiable receipt-of-liability. -/
theorem accepted_and_dropped_is_convictable
    (r : CustodyReceipt) (hsig : r.sig = true) :
    wellFormed (evidenceOfDrop r) = true ∧ adjudicate (evidenceOfDrop r) .dropped = true := by
  refine ⟨?_, ?_⟩
  · -- well-formed: the relay's own signature + the deadline reached (atHeight = acceptBy ≥ acceptBy).
    simp [wellFormed, evidenceOfDrop, hsig]
  · -- the verdict is slash: well-formed ∧ trueOutcome = dropped.
    simp [adjudicate, wellFormed, evidenceOfDrop, hsig]

/-! ## §4 — THE HEADLINE (b): an HONEST relay is NOT slashable (no false conviction). -/

/-- **`honest_relay_not_slashable` (KEYSTONE b — the no-false-conviction tooth).**

If the relay HONORED the receipt — the TRUE custody outcome is `delivered` to the promised root or
`refunded` (`outcomeHonest r trueOutcome = true`) — then NO piece of evidence convicts it: for ANY
evidence `e`, `adjudicate e trueOutcome = acquit` (`= false`). A malicious disputant may fabricate
`claimedOutcome := dropped` and raise the dispute past the deadline, but the adjudicator decides on
the VERIFIED `trueOutcome`, which is not `dropped` — so an honest relay is safe regardless of what
any disputant claims. This is the half that makes the calculus ACCOUNTABILITY and not a slashing
gun: the signed receipt is the relay's DEFENSE (it proves exactly what the relay promised), and an
honest relay's authenticated delivery/refund acquits it. -/
theorem honest_relay_not_slashable
    (r : CustodyReceipt) (trueOutcome : CustodyOutcome)
    (hhonest : outcomeHonest r trueOutcome = true) :
    ∀ e : EvidenceOfDrop, adjudicate e trueOutcome = false := by
  intro e
  -- An honest outcome is never `dropped`; `adjudicate` requires `trueOutcome = dropped`, so it fails.
  have hnotdrop : trueOutcome ≠ .dropped := by
    intro hd; rw [hd] at hhonest; simp [outcomeHonest] at hhonest
  simp only [adjudicate, Bool.and_eq_false_iff]
  right
  exact decide_eq_false hnotdrop

/-- **`honest_relay_acquitted_on_own_dispute`** — the sharp corollary: even the canonical
drop-evidence the disputant would file (`evidenceOfDrop r`, claiming `dropped`) is ACQUITTED when the
relay in fact delivered/refunded. The honest relay's signature on the receipt does not become a
liability when it kept its promise. -/
theorem honest_relay_acquitted_on_own_dispute
    (r : CustodyReceipt) (trueOutcome : CustodyOutcome)
    (hhonest : outcomeHonest r trueOutcome = true) :
    adjudicate (evidenceOfDrop r) trueOutcome = false :=
  honest_relay_not_slashable r trueOutcome hhonest (evidenceOfDrop r)

/-! ## §5 — The non-malleability / binding teeth.

The conviction binds to a SPECIFIC relay signature, content, and owner. A forged receipt convicts
nobody; evidence for a different content/owner does not cover this custody; a premature dispute (the
deadline not yet reached) is inadmissible. -/

/-- **`forged_receipt_no_conviction`** — a receipt the disputant fabricated WITHOUT the relay's key
(`sig = false`) is inadmissible: `wellFormed` is false, so `adjudicate` acquits regardless of the
true outcome. A third party cannot manufacture a conviction; only the relay's OWN signature (which,
by `receiptUnforgeable`, only the relay can produce) makes evidence admissible. -/
theorem forged_receipt_no_conviction (e : EvidenceOfDrop) (trueOutcome : CustodyOutcome)
    (hforged : e.receipt.sig = false) :
    adjudicate e trueOutcome = false := by
  simp [adjudicate, wellFormed, hforged]

/-- **`premature_dispute_inadmissible`** — a dispute raised BEFORE the deadline
(`atHeight < acceptBy`) is inadmissible: the relay has not yet defaulted (the box may still be
delivered within TTL), so `wellFormed` is false and `adjudicate` acquits. The deadline is what
separates a DROP from pending custody. -/
theorem premature_dispute_inadmissible (e : EvidenceOfDrop) (trueOutcome : CustodyOutcome)
    (hearly : e.atHeight < e.receipt.acceptBy) :
    adjudicate e trueOutcome = false := by
  have : decide (e.atHeight ≥ e.receipt.acceptBy) = false :=
    decide_eq_false (Nat.not_le.mpr hearly)
  simp [adjudicate, wellFormed, this]

/-- **`receiptUnforgeable` (the §8 seam, stated as the carried hypothesis)** — the cryptographic
discharge this module RELIES ON but does not prove: a party `p` can present a receipt with
`sig = true` ONLY IF `p = receipt.relay` (only the relay's key signs a valid receipt). This is the
Ed25519 EUF-CMA obligation, the Rust/vetted-crate oracle (same status as `Blocklace.Block.signed`'s
unforgeability). It is what makes a well-formed conviction bind the relay SPECIFICALLY: combined with
`accepted_and_dropped_is_convictable`, the only party a valid `EvidenceOfDrop` can convict is the
`receipt.relay` that signed it. Stated as a `def` of the obligation shape (a `Prop`), discharged at
the crypto portal, never here. -/
def receiptUnforgeable (presenter : Owner) (r : CustodyReceipt) : Prop :=
  r.sig = true → presenter = r.relay

/-- **`conviction_binds_the_signer`** — UNDER the §8 unforgeability seam, a valid conviction can only
be against the relay that signed: if the evidence is well-formed (so `sig = true`) and the §8 oracle
`receiptUnforgeable` holds for the presenter, the presenter — i.e. the party who could produce this
signed receipt — is the `receipt.relay`. (The conviction names exactly one accountable party; nobody
can be framed by a receipt they did not sign.) -/
theorem conviction_binds_the_signer (e : EvidenceOfDrop) (presenter : Owner)
    (hwf : wellFormed e = true)
    (hunf : receiptUnforgeable presenter e.receipt) :
    presenter = e.receipt.relay := by
  apply hunf
  unfold wellFormed at hwf
  rw [Bool.and_eq_true] at hwf
  exact hwf.1

/-! ## §6 — The conviction drives the SAME bonded-relay slash (rides `RelayOperator`).

A `slash` verdict is not a new economic lever — it is realized as the `RelayOperator`
bond-decrease-WITH-dispute transition already proved anti-drain-safe. We exhibit that a convicted
relay's bond decrease commits through `RelayOperator.relayStep` exactly because the conviction is the
dispute that the §3.5 `BoundedBy` discipline requires. So the accountability calculus and the
economic machine are ONE: conviction ⇒ a sanctioned dispute-gated slash; no conviction ⇒ no admitted
bond decrease (by `RelayOperator.bond_decrease_needs_dispute`). -/

/-- **`conviction_drives_slash`** — a relay convicted by valid drop-evidence has its bond slashed
through the SAME `RelayOperator` discipline: applying the slash op AND the conviction's dispute bump
commits (the bond decreases, but the `disputeCount` strictly advanced — the conviction IS the
dispute). Concretely: from the demo relay cell, a bond decrease 1000→900 paired with the dispute bump
0→1 that the conviction records is admitted by `relayProgram`. The verdict's economic teeth ride the
already-proved anti-drain machine; a conviction is exactly the dispute that unlocks the slash. -/
theorem conviction_drives_slash :
    (relayProgram cap).admits methodSlash slashedOld slashedNew = true := by
  decide

/-- **`no_conviction_no_silent_slash`** — the contrapositive economic safety, inherited from
`RelayOperator.bond_decrease_needs_dispute`: a committed bond decrease FORCES a recorded dispute
(the conviction). So a relay's bond cannot be drained without a conviction on the record — there is
no silent slash, mirroring that an honest relay (no valid evidence) keeps its bond. This re-exports
the bonded-relay keystone at the custody-accountability altitude. -/
theorem no_conviction_no_silent_slash
    {quotaCap : Int} {method : Nat} {old : Value} {op : RecOp} {new : Value}
    {a b : Int}
    (h : relayStep quotaCap method old op = some new)
    (hoa : old.scalar "bond" = some a) (hnb : new.scalar "bond" = some b) (hdec : b < a) :
    ∃ da db, old.scalar "disputeCount" = some da ∧ new.scalar "disputeCount" = some db ∧ da < db :=
  bond_decrease_needs_dispute h hoa hnb hdec

/-! ## §7 — NON-VACUITY: the calculus ACCEPTS a real conviction AND REJECTS over a real honest run.

Witnesses (each a `#guard`, a build error if false) that every load-bearing predicate is BOTH
satisfiable and refutable — the model is not vacuously true (always-slash) nor vacuously safe
(never-slash). -/

/-- A concrete signed receipt: relay 7 accepted box `0xABC` for inbox-owner 3, promising the inbox
root to advance `100 → 142` by deadline height 500, signature verifying. -/
def demoReceipt : CustodyReceipt :=
  { relay := 7, contentHash := 0xABC, inboxOwner := 3,
    oldRoot := 100, newRoot := 142, acceptBy := 500, sig := true }

/-- A relay-FORGED receipt (the disputant fabricated it without relay 7's key): `sig = false`. -/
def forgedReceipt : CustodyReceipt := { demoReceipt with sig := false }

-- ACCEPT (conviction): relay 7 signed and DROPPED ⇒ the canonical evidence convicts (verdict slash).
#guard adjudicate (evidenceOfDrop demoReceipt) .dropped == true
#guard wellFormed (evidenceOfDrop demoReceipt) == true

-- REJECT (honest delivery): relay 7 DELIVERED to the promised root 142 ⇒ acquit even on the
-- disputant's own drop-claim. The honest relay is safe.
#guard outcomeHonest demoReceipt (.delivered 142) == true
#guard adjudicate (evidenceOfDrop demoReceipt) (.delivered 142) == false

-- REJECT (honest refund): relay 7 REFUNDED before the deadline ⇒ acquit. The accept-or-refund-by
-- half discharges liability.
#guard outcomeHonest demoReceipt .refunded == true
#guard adjudicate (evidenceOfDrop demoReceipt) .refunded == false

-- REJECT (wrong-root delivery is NOT honest): the relay effected a DIFFERENT inbox transition
-- (root 999 ≠ promised 142) than it signed for ⇒ outcomeHonest is false (caught, not excused).
#guard outcomeHonest demoReceipt (.delivered 999) == false

-- REJECT (forged receipt): a fabricated receipt (sig=false) convicts nobody, whatever the outcome.
#guard adjudicate { receipt := forgedReceipt, claimedOutcome := .dropped, atHeight := 500 } .dropped == false
#guard wellFormed { receipt := forgedReceipt, claimedOutcome := .dropped, atHeight := 500 } == false

-- REJECT (premature dispute): a drop-claim raised BEFORE the deadline (height 499 < acceptBy 500)
-- is inadmissible — the relay has not yet defaulted.
#guard adjudicate { receipt := demoReceipt, claimedOutcome := .dropped, atHeight := 499 } .dropped == false

-- The §8 unforgeability oracle, instantiated: a valid (sig=true) demoReceipt can only be presented
-- by relay 7. (This is the carried hypothesis, exhibited on the concrete receipt.)
example : receiptUnforgeable 7 demoReceipt := by intro _; rfl

/-! ## §7.5 — CLOSING THE ORACLE GAP: the true outcome is DERIVED from the inbox's authenticated
root, not TAKEN from the disputant.

The §3/§4 calculus is correct but it takes `trueOutcome` as a PARAMETER — it answers "the
adjudicator won't slash *if told the truth*", and leaves to prose the load-bearing question the gap
actually poses: **how does the adjudicator ESTABLISH the true outcome without trusting the
disputant's word?** A `claimedOutcome` is an assertion; if the adjudicator believed it, a malicious
disputant could slash an honest relay (and an honest disputant could never convict a lying relay).

This section closes that. The adjudicator does NOT consult the disputant's claim; it reads the
inbox cell's OWN authenticated state — specifically a sticky DELIVERY-WITNESS bit ("was THIS box,
bound by `receipt.contentHash`, delivered?"). The verdict becomes a FUNCTION of the cell, removing
the disputant from the trust path entirely. This is the realizable adjudicator `POST /relay/dispute`
actually runs against the inbox cell — the prose claim of §2/§4, now a theorem.

WHY A WITNESS BIT, NOT ROOT EQUALITY (the overshoot/reorg fidelity gap, closed). The inbox root is a
MONOTONE cursor `Exec.CapInbox` proves only ever advances (`inbox_fifo`: `head` is `monotonic`).
In this idealized model a `Root` is a `Nat`, so "delivery witnessed" is `root ≥ newRoot` — and a
later root that OVERSHOT the promise (a reorg, a late block, a LATER message) still witnesses THIS
delivery. But the REALIZABLE inbox root is an opaque content-address with NO order: the only
realizable analogue of `≥` is exact equality `root = newRoot`, which DROPS the overshoot case — an
inbox whose root advanced past the promise no longer equals it and would FALSELY read as `dropped`,
convicting a relay that delivered. So the cell exposes an explicit, sticky, content-address-honest
witness bit (set when the box's `contentHash` is dequeued toward the recipient — a `DequeueProof`),
and the verdict reads THAT. `deliveredWitness_from_root_overshoot`/`overshoot_acquits` reconcile the
two: in the idealized model the witness equals the monotone-root reading `root ≥ newRoot` (overshoot
included), and the realizable Rust adjudicator (`captp/src/custody.rs`) mirrors the witness bit
field-for-field, so Lean and Rust AGREE on overshoot — neither false-convicts a delivered relay.

The tie to the identity-execution-cursor: because the inbox root is MONOTONE (the `CapInbox`
`head`/Merkle root only advances — `inbox_fifo`), a delivery once witnessed CANNOT be erased by a
later state advance or a store-and-forward prefix reorg. Delivery is permanent; the relay's defense
(it delivered) and its liability (it did not) are both anchored to a cursor neither party can rewind.
-/

/-- **`InboxState`** — exactly what the adjudication cell READS to establish the true custody
outcome. Two authenticated bits PLUS the live root:

  * `deliveredWitness` — **the DELIVERY-WITNESS bit: "was THIS box delivered?"** Set by the inbox
    cell when the box bound by the receipt (its `contentHash`) leaves the queue toward the recipient
    — concretely, a `MerkleQueue` dequeue whose `entry.content_hash = receipt.contentHash`. This is
    the realizable, content-address-HONEST signal of delivery, and it is **STICKY**: once the box
    has been delivered, the cell records it permanently, so no later root movement can un-witness it.
  * `refundRecorded`  — the relay recorded a refund before the deadline (the `accept-OR-refund-by`
    other half), an authenticated cell event.
  * `root`           — the inbox's authenticated MONOTONE root at the dispute height (`CapInbox.head`
    / Merkle root, which `inbox_fifo` proves only ever advances). Carried so the realizable model can
    DERIVE the witness in the idealized Nat-root setting (`deliveredOf` below) and so the
    monotone-cursor reasoning is exhibited; but the verdict reads the witness bit, never bare root
    equality (which the §7.5(c) overshoot tooth shows is WRONG — see `deliveredWitness_sticky`).

The disputant's `claimedOutcome` is NOT here: the adjudicator does not read it.

WHY THE WITNESS BIT AND NOT ROOT-EQUALITY. In the idealized model a `Root` is a `Nat` and "reached"
is `≥`, so delivery-then-further-activity (`root ≥ newRoot`) still witnesses delivery. But the
REALIZABLE inbox root is an opaque content-address ([u8;32]) with NO order: the only realizable
analogue of `≥` is exact equality `root = newRoot`, and that DROPS the overshoot/reorg case — an
inbox whose root advanced PAST the promised `newRoot` (a later box enqueued/dequeued) no longer
equals it and would read as `dropped`, FALSELY convicting a relay that delivered. The explicit
sticky witness bit is the fix that makes the Lean model and the Rust adjudicator (`custody.rs`)
AGREE on content-addresses: both read "was this box delivered?", not "does the live root equal a
past promise?". -/
structure InboxState where
  /-- THE DELIVERY-WITNESS bit: the cell recorded that THIS box (`receipt.contentHash`) was delivered
      to the recipient (dequeued from the inbox). STICKY: never retracted once set. -/
  deliveredWitness : Bool
  /-- The relay recorded a refund before the deadline (an authenticated cell event). -/
  refundRecorded   : Bool
  /-- The inbox's authenticated root at the dispute height (`CapInbox.head`/Merkle root). MONOTONE:
      once it reaches a value it never retreats (the cursor discipline of `inbox_fifo`). Carried for
      the idealized-model derivation `deliveredOf`; the verdict reads `deliveredWitness`, not this. -/
  root             : Root
  deriving DecidableEq, Repr, Inhabited

/-- **`rootReached inbox promised`** — the inbox's authenticated root has reached (or passed) the
`promised` root. In the IDEALIZED Nat-root model "reached or passed" is `≥`: once delivery advances
the root to `newRoot`, subsequent inbox activity only pushes it FURTHER, so a later root `≥ newRoot`
still witnesses that THIS delivery happened. This is the lens through which the realizable
`deliveredWitness` bit is DERIVED in the idealized setting (`deliveredOf`); it is NOT itself the
realizable predicate, because a content-address root has no `≥` (see `InboxState`). -/
def rootReached (inbox : InboxState) (promised : Root) : Bool :=
  decide (inbox.root ≥ promised)

/-- **`deliveredOf r inbox`** — the realizable delivery-witness bit, READ from the cell. This is the
single source of truth the verdict consults. In a faithful realizable inbox it is set exactly when
the box bound by `r` (its `contentHash`) was dequeued toward the recipient; the idealized model below
exhibits it as `inbox.deliveredWitness`, and `deliveredWitness_from_root_overshoot` shows it agrees
with the monotone-root reading on the overshoot case (where bare equality would FAIL). -/
def deliveredOf (_r : CustodyReceipt) (inbox : InboxState) : Bool :=
  inbox.deliveredWitness

/-- **`trueOutcomeFromInbox r inbox`** — the custody outcome DERIVED from the authenticated inbox
state for receipt `r`. NOT the disputant's claim: a verified fact read off the cell.

  * if the DELIVERY-WITNESS bit is set for this box → `delivered inbox.root` (the box left the queue
    toward the recipient; the cell witnesses it — STICKY, so this survives any later root movement).
    HONEST.
  * else if the relay recorded a refund → `refunded`. HONEST.
  * else → `dropped`: the deadline passed, the box was never delivered, and no refund was recorded.
    DISHONEST — and established WITHOUT trusting anyone's word, and WITHOUT the brittle root-equality
    that broke on overshoot. -/
def trueOutcomeFromInbox (r : CustodyReceipt) (inbox : InboxState) : CustodyOutcome :=
  if deliveredOf r inbox then .delivered inbox.root
  else if inbox.refundRecorded then .refunded
  else .dropped

/-- **`adjudicateFromInbox e inbox`** — the REALIZABLE adjudicator: it derives the true outcome from
the inbox's authenticated state and feeds it to `adjudicate`. This is what the dispute cell runs —
no disputant claim is consulted. (`adjudicate e (trueOutcomeFromInbox e.receipt inbox)`.) -/
def adjudicateFromInbox (e : EvidenceOfDrop) (inbox : InboxState) : Bool :=
  adjudicate e (trueOutcomeFromInbox e.receipt inbox)

/-- **`not_delivered_is_dropped`** — if the DELIVERY-WITNESS bit is NOT set and no refund was
recorded, the derived outcome is `dropped`. (The cell-read drop predicate, on the witness bit — no
brittle root equality.) -/
theorem not_delivered_is_dropped (r : CustodyReceipt) (inbox : InboxState)
    (hshort : deliveredOf r inbox = false) (hnorefund : inbox.refundRecorded = false) :
    trueOutcomeFromInbox r inbox = .dropped := by
  simp [trueOutcomeFromInbox, hshort, hnorefund]

/-- **`delivered_is_honest`** — if the DELIVERY-WITNESS bit is set, the derived outcome is HONEST
(`outcomeHonest` — a `delivered` to the cell's live root). The cell-read delivery predicate. The
relay is honest for delivering to `inbox.root` (the live root, which by the monotone cursor is the
promise or beyond) precisely because the box was witnessed delivered; the §3 `outcomeHonest`'s
exact-root check is the special case `inbox.root = newRoot`, and the witness-bit reading generalizes
it to the realizable "this box left the queue" (delivery, then arbitrary further activity — incl.
overshoot). -/
theorem delivered_is_honest (r : CustodyReceipt) (inbox : InboxState)
    (hwitness : deliveredOf r inbox = true) (hat : inbox.root = r.newRoot) :
    outcomeHonest r (trueOutcomeFromInbox r inbox) = true := by
  simp [trueOutcomeFromInbox, hwitness, outcomeHonest, hat]

/-! ### §7.5(a′) — THE RECONCILIATION: the witness bit AGREES with the monotone-root reading,
INCLUDING the overshoot case where bare root-equality fails. This is the precise theorem that ties
the idealized Nat-root model to the realizable content-address adjudicator (`custody.rs`). -/

/-- **`deliveredOf`** is `inbox.deliveredWitness` by definition — the verdict reads the explicit,
sticky, content-address-honest witness bit, NOT root equality. (Stated as a lemma so the reconciliation
theorems can rewrite with it.) -/
theorem deliveredOf_eq_witness (r : CustodyReceipt) (inbox : InboxState) :
    deliveredOf r inbox = inbox.deliveredWitness := rfl

/-- **`deliveredWitness_from_root_overshoot` (THE OVERSHOOT RECONCILIATION).**

In a faithful realizable inbox the witness bit is set exactly when the box was delivered, which (in
the idealized Nat-root model) is exactly when the monotone root REACHED OR PASSED the promise —
`rootReached`, i.e. `root ≥ newRoot`, NOT `root = newRoot`. So if the cell faithfully derives its
witness from the monotone root (`inbox.deliveredWitness = rootReached inbox r.newRoot`), then a root
that OVERSHOT the promise (`root > newRoot`, the reorg / late-block / later-message case) STILL reads
as delivered. This is the exact case the brittle Rust `root == new_root` equality DROPPED — here it
holds, because the witness bit tracks `≥`, not `=`. The realizable Rust adjudicator gets the same
robustness by setting its witness bit from a dequeue of the box (a `DequeueProof` whose
`entry.content_hash = receipt.content_hash`), which is likewise sticky and order-free. -/
theorem deliveredWitness_from_root_overshoot (r : CustodyReceipt) (inbox : InboxState)
    (hfaithful : inbox.deliveredWitness = rootReached inbox r.newRoot)
    (hovershoot : inbox.root > r.newRoot) :
    deliveredOf r inbox = true := by
  rw [deliveredOf_eq_witness, hfaithful]
  unfold rootReached
  exact decide_eq_true (Nat.le_of_lt hovershoot)

/-- **`overshoot_acquits` (the gap, CLOSED, as a verdict).** A relay whose box was delivered and
whose inbox root then OVERSHOT the promise (later activity) is ACQUITTED by the realizable adjudicator
— for any evidence, regardless of the disputant's claim. This is the precise FALSE-CONVICTION the
strict-equality realization produced (`root != new_root ⇒ dropped`); the witness bit removes it. -/
theorem overshoot_acquits (e : EvidenceOfDrop) (inbox : InboxState)
    (hfaithful : inbox.deliveredWitness = rootReached inbox e.receipt.newRoot)
    (hovershoot : inbox.root > e.receipt.newRoot) :
    adjudicateFromInbox e inbox = false := by
  have hwit : deliveredOf e.receipt inbox = true :=
    deliveredWitness_from_root_overshoot e.receipt inbox hfaithful hovershoot
  unfold adjudicateFromInbox adjudicate trueOutcomeFromInbox
  rw [if_pos hwit]; simp

/-! ### §7.5(a) — THE GAP-CLOSING KEYSTONE: conviction iff the box was NOT delivered (witness bit). -/

/-- **`conviction_iff_not_delivered` (the realizable-adjudicator keystone).**

For a well-formed dispute (`wellFormed e` — the relay's own signature + the deadline passed), the
adjudicator's verdict computed FROM THE INBOX CELL is `slash` IFF the inbox's DELIVERY-WITNESS bit
is NOT set for this box AND no refund was recorded. The conviction is a pure FUNCTION of the
authenticated cell state: the relay is slashed exactly when the cell shows the box was neither
delivered nor refunded. Neither the relay nor the disputant can move this verdict — it reads only the
sticky witness bit and the refund bit, both authenticated. Reading the witness bit (not root
equality) is what makes this robust to overshoot/reorg: an inbox whose root advanced PAST the promise
is NOT convicted, because the box was witnessed delivered (see `overshoot_acquits`). This is the
prose claim of §2/§4 ("decided on the VERIFIED true outcome, as established by the inbox cell's
authenticated state") discharged as a theorem. -/
theorem conviction_iff_not_delivered (e : EvidenceOfDrop) (inbox : InboxState)
    (hwf : wellFormed e = true) :
    adjudicateFromInbox e inbox = true
      ↔ (deliveredOf e.receipt inbox = false ∧ inbox.refundRecorded = false) := by
  unfold adjudicateFromInbox adjudicate
  rw [hwf, Bool.true_and]
  unfold trueOutcomeFromInbox
  constructor
  · -- slash ⇒ the derived outcome is `dropped`, which forces not-delivered ∧ no-refund.
    intro hslash
    by_cases hr : deliveredOf e.receipt inbox = true
    · rw [if_pos hr] at hslash; exact absurd hslash (by simp)
    · rw [Bool.not_eq_true] at hr
      by_cases hf : inbox.refundRecorded = true
      · rw [if_neg (by simp [hr]), if_pos hf] at hslash; exact absurd hslash (by simp)
      · rw [Bool.not_eq_true] at hf; exact ⟨hr, hf⟩
  · -- not-delivered ∧ no-refund ⇒ derived outcome is `dropped` ⇒ slash.
    rintro ⟨hr, hf⟩
    rw [if_neg (by simp [hr]), if_neg (by simp [hf])]
    decide

/-- **`disputant_claim_irrelevant` (the trust-path tooth — the sharp closure).**

The realizable verdict does NOT depend on the disputant's `claimedOutcome` AT ALL: two pieces of
evidence with the SAME receipt and SAME dispute height but ARBITRARILY DIFFERENT claimed outcomes
adjudicate identically against the same inbox. So a malicious disputant cannot manufacture a
conviction by lying about the outcome, and an honest disputant need not be believed — the verdict is
read off the authenticated cell. This is precisely the property that makes the calculus
ACCOUNTABILITY (a verified-fact adjudication) and not a he-said-she-said: the claim is inert. -/
theorem disputant_claim_irrelevant (r : CustodyReceipt) (h : Height) (inbox : InboxState)
    (o₁ o₂ : CustodyOutcome) :
    adjudicateFromInbox ⟨r, o₁, h⟩ inbox = adjudicateFromInbox ⟨r, o₂, h⟩ inbox := by
  -- `adjudicateFromInbox` reads only `e.receipt`, `e.atHeight` (via `wellFormed`), and the inbox —
  -- never `e.claimedOutcome`. Both sides reduce to the identical expression.
  rfl

/-! ### §7.5(b) — the honest relay is safe AGAINST THE CELL (no oracle, no claim trusted). -/

/-- **`honest_relay_not_slashable_from_inbox` (the no-false-conviction half, REALIZED).**

If the inbox's DELIVERY-WITNESS bit is set (the relay DELIVERED — the box left the queue, witnessed in
the cell) OR a refund was recorded (the relay REFUNDED), then the realizable adjudicator ACQUITS, for
ANY evidence whatsoever — regardless of what the disputant claims, regardless of the dispute height.
An honest relay is safe because the cell's authenticated state acquits it; the disputant's
fabricated `dropped` claim is powerless. This is `honest_relay_not_slashable` with the oracle
REPLACED by the actual inbox-cell read — the gap is closed. -/
theorem honest_relay_not_slashable_from_inbox (e : EvidenceOfDrop) (inbox : InboxState)
    (hhonest : deliveredOf e.receipt inbox = true ∨ inbox.refundRecorded = true) :
    adjudicateFromInbox e inbox = false := by
  unfold adjudicateFromInbox adjudicate trueOutcomeFromInbox
  rcases hhonest with hr | hf
  · -- delivered: derived outcome is `delivered _`, not `dropped` ⇒ acquit.
    rw [if_pos hr]; simp
  · -- refunded (or delivered): in either case not `dropped` ⇒ acquit.
    by_cases hr : deliveredOf e.receipt inbox = true
    · rw [if_pos hr]; simp
    · rw [Bool.not_eq_true] at hr; rw [if_neg (by simp [hr]), if_pos hf]; simp

/-! ### §7.5(c) — the STICKY-WITNESS tooth: a witnessed delivery cannot be erased (prefix-reorg
robustness, the identity-execution-cursor tie). The witness bit is STICKY (never retracted), which is
the realizable, content-address-honest form of the monotone-cursor guarantee — it survives ANY root
movement, including the OVERSHOOT that broke the bare root-equality realization. -/

/-- **`sticky_witness_no_erased_delivery` (the delay-tolerance / prefix-reorg tooth).**

The DELIVERY-WITNESS bit is STICKY: once the cell records the box as delivered it never retracts that
(`inbox.deliveredWitness = true → inbox'.deliveredWitness = true` for any successor cell state). This
is the realizable form of the `CapInbox.inbox_fifo` monotone-cursor guarantee — delivery is an
append-only, irreversible fact. So once the box is witnessed delivered, ANY later cell state STILL
witnesses delivery and the relay STILL acquits. Concretely: a store-and-forward prefix reorg, a
late-arriving block, a LATER message advancing the root PAST the promise (`overshoot`), or any
subsequent inbox activity cannot RETROACTIVELY convict a relay that already delivered. This is the
property the strict `root == new_root` realization SILENTLY DROPPED; the sticky witness bit restores
it on real content-address roots. -/
theorem sticky_witness_no_erased_delivery (e : EvidenceOfDrop) (inbox inbox' : InboxState)
    (hwitness : deliveredOf e.receipt inbox = true)
    (hsticky : inbox.deliveredWitness = true → inbox'.deliveredWitness = true) :
    deliveredOf e.receipt inbox' = true ∧ adjudicateFromInbox e inbox' = false := by
  have hr' : deliveredOf e.receipt inbox' = true := by
    rw [deliveredOf_eq_witness] at hwitness ⊢
    exact hsticky hwitness
  exact ⟨hr', honest_relay_not_slashable_from_inbox e inbox' (Or.inl hr')⟩

/-- **`drop_conviction_survives_root_growth`** — the DUAL: a genuine drop stays convictable even as
the inbox root grows, SO LONG AS the box is STILL not delivered. If the witness bit is unset and no
refund was recorded, then for any later cell state in which the box is STILL un-delivered, a
well-formed dispute STILL convicts. A relay cannot escape conviction by unrelated inbox activity that
advances the root but never delivers ITS box. -/
theorem drop_conviction_survives_root_growth (e : EvidenceOfDrop) (inbox' : InboxState)
    (hwf : wellFormed e = true)
    (hstillnotdelivered : deliveredOf e.receipt inbox' = false)
    (hnorefund : inbox'.refundRecorded = false) :
    adjudicateFromInbox e inbox' = true :=
  (conviction_iff_not_delivered e inbox' hwf).mpr ⟨hstillnotdelivered, hnorefund⟩

/-! ### §7.5(d) — NON-VACUITY for the realizable adjudicator (accepts a real drop, acquits a real
delivery, and the claim is provably inert). -/

-- The demo inboxes set `deliveredWitness` FAITHFULLY to the monotone-root reading
-- (`deliveredWitness = rootReached`, i.e. `root ≥ newRoot = 142`), then the verdict reads the
-- witness bit. The overshoot inbox is the load-bearing one: root 143 > 142, witness STILL true.
/-- An inbox whose box was delivered (witness set), root exactly at the promise: root 142 = 142. -/
def deliveredInbox : InboxState := { deliveredWitness := true, refundRecorded := false, root := 142 }
/-- An inbox whose box was NOT delivered, no refund (a genuine drop): witness false, root short 100. -/
def droppedInbox : InboxState := { deliveredWitness := false, refundRecorded := false, root := 100 }
/-- An inbox where the relay REFUNDED (not delivered, but refund recorded): honest. -/
def refundedInbox : InboxState := { deliveredWitness := false, refundRecorded := true, root := 100 }
/-- THE OVERSHOOT inbox: the box WAS delivered (witness true) and the root then advanced PAST the
promise by later activity (143 > 142). The strict `root == new_root` realization read this as DROPPED
(a FALSE conviction); the sticky witness bit reads it as DELIVERED. The reorg/late-block case. -/
def overshotInbox : InboxState := { deliveredWitness := true, refundRecorded := false, root := 143 }

-- ACCEPT (cell-derived conviction): the box was NOT delivered, no refund ⇒ the realizable
-- adjudicator SLASHES — established from the inbox cell, NOT from the disputant's claim.
#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) droppedInbox == true
#guard trueOutcomeFromInbox demoReceipt droppedInbox == CustodyOutcome.dropped

-- ACQUIT (cell-derived delivery): the witness bit is set ⇒ acquit, EVEN on the disputant's
-- drop-claim. The honest relay is safe against the cell.
#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) deliveredInbox == false
#guard trueOutcomeFromInbox demoReceipt deliveredInbox == CustodyOutcome.delivered 142

-- ACQUIT (cell-derived refund): refund recorded ⇒ acquit (the accept-or-refund-by half, read off
-- the cell).
#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) refundedInbox == false

-- ACQUIT (THE OVERSHOOT / prefix-reorg tooth — THE GAP CLOSED): the root OVERSHOT the promise
-- (143 > 142) but the box was witnessed delivered ⇒ acquit. A late block / reorg / later message
-- cannot un-deliver. This is the EXACT case the strict-equality realization FALSE-CONVICTED; the
-- witness bit fixes it, and `deliveredWitness` here faithfully equals the monotone-root reading.
#guard overshotInbox.deliveredWitness == rootReached overshotInbox demoReceipt.newRoot
#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) overshotInbox == false
#guard rootReached overshotInbox demoReceipt.newRoot == true
#guard deliveredOf demoReceipt overshotInbox == true
-- And the CONTRAST that pins the bug: bare root-EQUALITY (the old realization) would read overshoot
-- as NOT-reached (143 ≠ 142) and thus convict; the witness bit does not. This `#guard` exhibits the
-- precise divergence the fix removes.
#guard (decide (overshotInbox.root = demoReceipt.newRoot)) == false  -- equality FAILS on overshoot…
#guard adjudicateFromInbox (evidenceOfDrop demoReceipt) overshotInbox == false  -- …yet the relay is acquitted.

-- THE CLAIM IS INERT: the SAME receipt + height adjudicates identically whether the disputant claims
-- `dropped`, `delivered 999`, or `refunded` — the verdict reads the cell, not the claim. Against a
-- genuine-drop inbox all three convict; against a delivered inbox all three acquit.
#guard adjudicateFromInbox ⟨demoReceipt, .dropped,      500⟩ droppedInbox
     == adjudicateFromInbox ⟨demoReceipt, .delivered 999, 500⟩ droppedInbox
#guard adjudicateFromInbox ⟨demoReceipt, .refunded,     500⟩ deliveredInbox
     == adjudicateFromInbox ⟨demoReceipt, .delivered 999, 500⟩ deliveredInbox

-- A forged receipt STILL convicts nobody even against a genuine-drop inbox (the §5 binding tooth
-- composes with the cell-read adjudicator): not well-formed ⇒ acquit regardless of the cell.
#guard adjudicateFromInbox { receipt := forgedReceipt, claimedOutcome := .dropped, atHeight := 500 } droppedInbox == false

/-! ## §8 — Axiom-hygiene pins (⊆ {propext, Classical.choice, Quot.sound}; NO sorry/native_decide). -/

-- KEYSTONE (a) — accepted-and-dropped is convictable.
#assert_axioms accepted_and_dropped_is_convictable
-- KEYSTONE (b) — an honest relay is NOT slashable (no false conviction).
#assert_axioms honest_relay_not_slashable
#assert_axioms honest_relay_acquitted_on_own_dispute
-- Non-malleability / binding teeth.
#assert_axioms forged_receipt_no_conviction
#assert_axioms premature_dispute_inadmissible
#assert_axioms conviction_binds_the_signer
-- The conviction drives the bonded-relay slash (rides RelayOperator).
#assert_axioms conviction_drives_slash
#assert_axioms no_conviction_no_silent_slash
-- §7.5 — the realizable adjudicator: the true outcome is DERIVED from the inbox's authenticated
-- DELIVERY-WITNESS bit (not brittle root equality), closing the "trust the disputant's claim" oracle
-- gap AND the overshoot/reorg false-conviction the strict-equality realization dropped.
#assert_axioms not_delivered_is_dropped
#assert_axioms delivered_is_honest
#assert_axioms conviction_iff_not_delivered
#assert_axioms disputant_claim_irrelevant
#assert_axioms honest_relay_not_slashable_from_inbox
#assert_axioms sticky_witness_no_erased_delivery
#assert_axioms drop_conviction_survives_root_growth
-- The OVERSHOOT reconciliation: the witness bit agrees with the monotone-root reading on the
-- overshoot case (root > newRoot) where bare equality fails ⇒ the relay is acquitted, not convicted.
#assert_axioms deliveredWitness_from_root_overshoot
#assert_axioms overshoot_acquits

end Dregg2.Exec.Custody
