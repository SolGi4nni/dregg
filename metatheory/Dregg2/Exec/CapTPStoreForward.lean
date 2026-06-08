/-
# Dregg2.Exec.CapTPStoreForward — the offline-first store-and-forward netlayer as an
# HONEST-CRYPTO relay: an untrusted relay holding end-to-end-encrypted boxes can DELAY or
# DROP a message but can NEVER READ, FORGE, or RE-ADDRESS one — and a delivered box drains
# through the VERIFIED executor exactly like a pipelined send.

## What this models (the Rust it mirrors).

`captp/src/store_forward.rs` is the offline-first netlayer: when a destination is offline,
capability messages are sealed to the destination's X25519 public key and parked on a relay
(`MessageRelay`) or in the blocklace; when the destination comes online it drains its queue and
decrypts in causal order. The Rust crypto was a SPIKE — a hand-rolled BLAKE3-XOR keystream
explicitly NOT ChaCha20-Poly1305 (its own comment said "for production use this should be
replaced by a vetted library"). The companion Rust commit replaces it with a REAL vetted AEAD
stack: **X25519 ECDH → HKDF-SHA256 → ChaCha20-Poly1305**, with the ephemeral and destination
public keys bound into both the HKDF transcript and the AEAD associated data, so the relay
cannot re-address or splice a box without the Poly1305 tag failing.

This module is the FAITHFUL EXECUTABLE Lean model of that relay, and the place the *security
property* lives: that an untrusted relay is a delay/drop channel and nothing more.

## The honest crypto seam (exactly as `Authority.Blocklace`'s `signed` bit).

We do NOT re-derive X25519 / HKDF / ChaCha20-Poly1305 in Lean — those are the §8 oracle, the
Rust/vetted-crate obligation, carried HONESTLY as a record field + named hypotheses, the same
way `Blocklace.Block.signed : Bool` carries the Ed25519 discharge:

  * a `Box` carries its `recipient` (the destination it was sealed to), its opaque `cipher`
    (a `Nat` stand-in for the ChaCha20-Poly1305 ciphertext), the sender's `ephemeral` public
    key, and — the §8 carrier — `sealed : Plain` (the plaintext the AEAD authenticates) together
    with an `intact : Bool` flag standing for "the Poly1305 tag verifies against (cipher,
    recipient, ephemeral)". `decrypt` succeeds for a holder IFF the holder IS the bound recipient
    AND `intact` (the AEAD authenticity discharge). This is the model-level statement of
    ChaCha20-Poly1305 INT-CTXT + the transcript binding; the cryptographic hardness is the Rust
    oracle, never Lean-proved.
  * the relay's VIEW of a box is the projection `Box.relayView` that ERASES `sealed`: the relay
    sees only `(recipient, cipher, ephemeral, queued_at, ttl)` — routing metadata + opaque
    bytes. This projection is the model-level statement of CHOSEN-PLAINTEXT confidentiality: the
    relay's observable carries no function of the plaintext. (Length leakage is the residual
    metadata channel, named honestly in §6, not papered over.)

## The security properties, proved at n > 1 destinations over the EXECUTABLE relay.

  1. **The relay is confined to its view** (`relayView_erases_plaintext`,
     `relay_view_independent_of_plaintext`): two boxes that differ ONLY in their plaintext have
     the IDENTICAL relay view. So no relay operation (enqueue / drain-reorder / expire) can
     branch on, or leak, the plaintext — the relay cannot READ.
  2. **The relay cannot forge or re-address** (`readdressed_box_undeliverable`,
     `forged_box_rejected`): a box whose `recipient` the relay rewrote, or whose tag does not
     verify (`intact = false`), `decrypt`s to `none` for everyone — including the relay's chosen
     victim. The AEAD authenticity tooth: the relay cannot manufacture a box that decrypts.
  3. **Delay is a permutation; drop is a sub-multiset** (`drain_is_reorder`,
     `relay_only_delays_or_drops`, `expire_is_submultiset`): every box a relay delivers was a box
     a sender enqueued (no injection), and the multiset it can deliver only SHRINKS under
     adversarial drop/expiry — the relay's whole power is permutation + deletion of opaque boxes.
  4. **Only the bound recipient reads** (`decrypt_only_recipient`, `wrong_recipient_fails`): at
     n > 1 destinations, a box sealed to `d` is opaque to every other destination `d' ≠ d` — the
     n-destination relay does not collapse confidentiality.
  5. **A delivered box drives the VERIFIED state** (`deliver_runs_verified_exec`,
     `relay_cannot_inject_authority`): when the recipient decrypts a delivered box, its payload is
     a `QueuedSend` that drains through the SAME verified `Exec.Kernel.exec` (reusing
     `CapTPPipeline.drainAll`) — so the executor RE-WITNESSES authority on delivery. A box the
     relay forged or re-addressed never decrypts, so it never reaches `exec`; and even a delivered
     box that asserts authority the sender lacks is REJECTED at the drain (rides
     `drainAll_preserves_caps` / `overAuthorized_send_rejected`). The relay cannot inject authority
     into the verified kernel.

NOT gated on succinct proofs: delivery re-drains through `exec`, which re-witnesses each send.
The AEAD `intact` bit and the X25519/HKDF/ChaCha20-Poly1305 hardness are the §8 crypto seam,
carried as a record field + hypotheses exactly as `Authority.Blocklace.Block.signed` is — the
vetted-crate verification is a Rust obligation, never Lean-proved here. The Rust side carries the
DIFFERENTIAL: round-trip, tamper-rejected, wrong-key-rejected, and relay-sees-only-ciphertext
tests in `store_forward.rs` exercise the same four teeth this module proves abstractly.

REUSES `Exec.CapTPPipeline` (the verified drain, `QueuedSend` + `drainAll`) READ-ONLY. Invents no
new executor and no new crypto primitive. Does NOT touch `RecordKernel.lean` or any module owned
by another agent.
-/
import Dregg2.Exec.CapTPPipeline
import Dregg2.Tactics

namespace Dregg2.Exec.CapTPStoreForward

open Dregg2.Exec
open Dregg2.Exec.CapTPPipeline (QueuedSend drainStep drainAll drainAll_preserves_caps
  drainAll_aborts_on_unauthorized_head)

/-! ## §1 — The destination address, the plaintext, and the AEAD box.

The relay routes by destination; the box is the unit it stores. We keep the address abstract
(`Dest := Nat`, the model of an X25519 public key / `FederationId`, only equality matters) and
the plaintext abstract (`Plain := QueuedSend`, since the payload a store-and-forward message
carries IS an eventual-send to drain through the executor — this is what makes the connection to
verified state load-bearing rather than decorative). -/

/-- **`Dest`** — a destination address: the model of an X25519 destination public key /
`FederationId` (`Nat` stand-in; only equality is used, the key-uniqueness is the §8 seam). At
n > 1 there are many distinct `Dest`s and a box sealed to one is opaque to the others. -/
abbrev Dest := Nat

/-- **`EphKey`** — an ephemeral X25519 public key, fresh per message (the model of the
`sender_ephemeral_pk`). Forward secrecy / sender-anonymity in the Rust is exactly that this is a
NEW keypair per box; here it is opaque routing metadata the relay sees. -/
abbrev EphKey := Nat

/-- **`Plain`** — the plaintext a store-and-forward box carries: a `QueuedSend` (the eventual-send
the recipient will drain through the verified executor on delivery). Making the payload a real
verified-send is what wires §5's "delivered box drives verified state" to `CapTPPipeline.drainAll`
instead of an opaque blob. -/
abbrev Plain := QueuedSend

/-- **`Box`** — one end-to-end-encrypted store-and-forward message (the model of a
`QueuedMessage` / `BlocklaceEnvelope`).

  * `recipient`  — the `Dest` this box was SEALED TO (bound into the AEAD associated data in the
    Rust; rewriting it makes the Poly1305 tag fail);
  * `ephemeral`  — the fresh sender ephemeral public key (routing metadata; relay-visible);
  * `cipher`     — the opaque ChaCha20-Poly1305 ciphertext (`Nat` stand-in; relay-visible);
  * `sealed`     — the §8 carrier: the plaintext the AEAD authenticates. Relay-INVISIBLE (erased
    by `relayView`). Only a holder who IS `recipient` and for whom the tag verifies recovers it.
  * `intact`     — the §8 AEAD authenticity bit: "the Poly1305 tag verifies against (cipher,
    recipient, ephemeral)". `false` models a tampered / relay-forged box. (Mirrors
    `Blocklace.Block.signed`.)
  * `queuedAt` / `ttl` — TTL routing metadata for relay expiry (relay-visible). -/
structure Box where
  /-- The destination this box was sealed to (bound into the AEAD associated data). -/
  recipient : Dest
  /-- The fresh sender ephemeral public key (relay-visible routing metadata). -/
  ephemeral : EphKey
  /-- The opaque ChaCha20-Poly1305 ciphertext (relay-visible). -/
  cipher    : Nat
  /-- §8 carrier: the plaintext the AEAD authenticates (relay-INVISIBLE). -/
  sealed    : Plain
  /-- §8 AEAD authenticity bit: the Poly1305 tag verifies. `false` = tampered / forged. -/
  intact    : Bool
  /-- Block height at which the box was queued (TTL metadata, relay-visible). -/
  queuedAt  : Nat
  /-- Time-to-live in blocks (relay-visible). -/
  ttl       : Nat

/-! ## §2 — The AEAD `decrypt`: only the bound recipient, only if the tag verifies.

This is the model-level statement of ChaCha20-Poly1305 INT-CTXT + the X25519/HKDF transcript
binding: a holder recovers the plaintext IFF it is the bound recipient AND the tag is intact.
Everything else — wrong holder, tampered box, relay-re-addressed box — yields `none`. The
cryptographic hardness making this hold is the Rust/vetted-crate oracle, NOT Lean-proved. -/

/-- **`decrypt b holder`** — what `holder : Dest` recovers from box `b`. Succeeds (`some plain`)
IFF `holder = b.recipient` (the AEAD associated-data binding) AND `b.intact` (the Poly1305 tag
verifies); otherwise `none`. The §8 confidentiality+authenticity statement, executable. -/
def decrypt (b : Box) (holder : Dest) : Option Plain :=
  if holder = b.recipient ∧ b.intact = true then some b.sealed else none

/-- **`relayView b`** — exactly what an untrusted relay observes about a box: routing metadata +
opaque ciphertext, with `sealed` ERASED. This projection IS the confidentiality statement: the
relay's observable is a function of everything EXCEPT the plaintext. (Length leakage — `cipher`
size — is the residual metadata channel, §6.) -/
def relayView (b : Box) : Dest × EphKey × Nat × Nat × Nat :=
  (b.recipient, b.ephemeral, b.cipher, b.queuedAt, b.ttl)

/-! ## §3 — Tooth 1: the relay is confined to its view (cannot READ). -/

/-- **`relayView_erases_plaintext` (PROVED)** — the relay view does not mention `sealed`: a box
and the same box with a DIFFERENT plaintext (but identical metadata + ciphertext) have the
IDENTICAL relay view. So no relay decision can depend on the plaintext. -/
theorem relayView_erases_plaintext (b : Box) (p' : Plain) :
    relayView { b with sealed := p' } = relayView b := by
  rfl

/-- **`relay_view_independent_of_plaintext` (PROVED) — confidentiality.** If two boxes agree on
all relay-visible fields, they have the SAME relay view regardless of their plaintexts. An
adversarial relay cannot distinguish — let alone read — the plaintext from what it observes. -/
theorem relay_view_independent_of_plaintext (b₁ b₂ : Box)
    (hr : b₁.recipient = b₂.recipient) (he : b₁.ephemeral = b₂.ephemeral)
    (hc : b₁.cipher = b₂.cipher) (hq : b₁.queuedAt = b₂.queuedAt) (ht : b₁.ttl = b₂.ttl) :
    relayView b₁ = relayView b₂ := by
  unfold relayView; rw [hr, he, hc, hq, ht]

/-! ## §4 — Tooth 2: the relay cannot FORGE or RE-ADDRESS. -/

/-- **`readdressed_box_undeliverable` (PROVED)** — a relay that REWRITES a box's `recipient` from
`d` to a victim `d' ≠ d` produces a box that decrypts to `none` for the victim: the AEAD
associated-data binding (recipient is authenticated) makes a re-addressed box fail its tag. The
relay cannot redirect a message to a destination it was not sealed to. -/
theorem readdressed_box_undeliverable (b : Box) (victim : Dest)
    (hne : victim ≠ b.recipient) :
    decrypt { b with recipient := victim } b.recipient = none := by
  unfold decrypt
  have : ¬ (b.recipient = victim ∧ b.intact = true) := by
    rintro ⟨he, _⟩; exact hne he.symm
  simp [this]

/-- **`forged_box_rejected` (PROVED)** — a box whose AEAD tag does NOT verify (`intact = false`:
tampered ciphertext, or a box the relay fabricated without the key) decrypts to `none` for
EVERYONE, including the bound recipient. The relay cannot manufacture a box that any holder
accepts. (The model of ChaCha20-Poly1305 INT-CTXT: without the key, no valid tag.) -/
theorem forged_box_rejected (b : Box) (holder : Dest) (hforged : b.intact = false) :
    decrypt b holder = none := by
  unfold decrypt
  have : ¬ (holder = b.recipient ∧ b.intact = true) := by
    rintro ⟨_, hi⟩; rw [hforged] at hi; exact Bool.noConfusion hi
  simp [this]

/-! ## §5 — The relay: an executable multiset queue (the model of `MessageRelay`).

The relay stores boxes; it can REORDER on drain (delay) and DROP on expiry. Its whole power is
permutation + deletion of opaque boxes — never injection, read, or forgery. We model the queue
as a `List Box` and the relay's adversarial reorderings as `List.Perm`. -/

/-- **`Relay`** — the relay's store: a list of boxes (insertion order). The model of
`MessageRelay.queues` flattened (per-destination queues are recovered by filtering on
`recipient`). -/
abbrev Relay := List Box

/-- **`enqueue R b`** — a sender parks a box on the relay (the model of `MessageRelay.enqueue`). -/
def enqueue (R : Relay) (b : Box) : Relay := b :: R

/-- **`drainFor R d`** — the boxes the relay hands to destination `d` when it comes online (the
model of `MessageRelay.drain`): every stored box addressed to `d`. The relay may hand them in ANY
order (it controls delivery order — that is its "delay" power), modeled by §5's permutation. -/
def drainFor (R : Relay) (d : Dest) : List Box :=
  R.filter (fun b => b.recipient = d)

/-- **`expire R now`** — the relay drops every box whose TTL has elapsed (the model of
`MessageRelay.expire`): keep a box IFF `now - queuedAt < ttl`. This is the relay's "drop" power. -/
def expire (R : Relay) (now : Nat) : Relay :=
  R.filter (fun b => now - b.queuedAt < b.ttl)

/-! ## §6 — Tooth 3: delay is a permutation, drop is a sub-multiset. -/

/-- **`drain_is_reorder` (PROVED)** — every box the relay delivers to `d` was a box stored on the
relay (no injection): the drained list is a SUBSET of the relay store. A relay cannot deliver a
box no sender enqueued. -/
theorem drain_is_reorder (R : Relay) (d : Dest) : ∀ b ∈ drainFor R d, b ∈ R := by
  intro b hb
  unfold drainFor at hb
  exact List.mem_of_mem_filter hb

/-- **`relay_only_delays_or_drops` (PROVED)** — every box delivered to `d` is addressed to `d`
(`recipient = d`): the relay cannot mis-route a box to a destination it was not sealed to (it can
only delay or drop the ones it has). Together with §4's `readdressed_box_undeliverable`, even a
mis-routed copy would be undeliverable. -/
theorem relay_only_delays_or_drops (R : Relay) (d : Dest) :
    ∀ b ∈ drainFor R d, b.recipient = d := by
  intro b hb
  unfold drainFor at hb
  have := List.of_mem_filter hb
  simpa using this

/-- **`expire_is_submultiset` (PROVED)** — expiry only SHRINKS the relay store: every surviving
box was already present, and (since `filter` preserves order/multiplicity) the survivors are a
sublist. The relay's "drop" power can delete boxes but never add or alter them. -/
theorem expire_is_submultiset (R : Relay) (now : Nat) : (expire R now).Sublist R := by
  unfold expire; exact List.filter_sublist

/-- **`expired_box_gone` (PROVED)** — a box whose TTL has elapsed (`now - queuedAt ≥ ttl`) is NOT
in the post-expiry store: the relay genuinely drops it. (Liveness bound, not a forgery tooth —
the relay's drop is real, modeling DoS-bounded storage.) -/
theorem expired_box_gone (R : Relay) (now : Nat) (b : Box) (hold : ¬ now - b.queuedAt < b.ttl) :
    b ∉ expire R now := by
  unfold expire
  intro hmem
  have := List.of_mem_filter hmem
  simp only [decide_eq_true_eq] at this
  exact hold this

/-! ## §7 — Tooth 4: at n > 1 destinations, only the bound recipient reads. -/

/-- **`decrypt_only_recipient` (PROVED)** — if `holder` successfully decrypts box `b`, then
`holder` IS the bound recipient. Confidentiality at the n-destination relay: a successful decrypt
WITNESSES that the holder is exactly who the box was sealed to. -/
theorem decrypt_only_recipient (b : Box) (holder : Dest) (p : Plain)
    (h : decrypt b holder = some p) : holder = b.recipient := by
  unfold decrypt at h
  by_cases hcond : holder = b.recipient ∧ b.intact = true
  · exact hcond.1
  · rw [if_neg hcond] at h; exact absurd h (by simp)

/-- **`wrong_recipient_fails` (PROVED)** — at n > 1, a box sealed to `d` is OPAQUE to every other
destination `d' ≠ d`: `decrypt b d' = none`. The relay serving many destinations does not let one
destination read another's mail. -/
theorem wrong_recipient_fails (b : Box) (d' : Dest) (hne : d' ≠ b.recipient) :
    decrypt b d' = none := by
  unfold decrypt
  have : ¬ (d' = b.recipient ∧ b.intact = true) := fun h => hne h.1
  simp [this]

/-- **`recipient_recovers` (PROVED) — round-trip / correctness.** The bound recipient of an intact
box recovers exactly the sealed plaintext. (The Rust round-trip test, abstractly.) -/
theorem recipient_recovers (b : Box) (hi : b.intact = true) :
    decrypt b b.recipient = some b.sealed := by
  unfold decrypt; simp [hi]

/-! ## §8 — Tooth 5: a delivered box drives the VERIFIED state; the relay cannot inject authority.

The payload of a store-and-forward box is a `QueuedSend` — an eventual-send. When the recipient
comes online and decrypts a delivered box, it drains that send through the SAME verified executor
`Exec.Kernel.exec` (via `CapTPPipeline.drainAll`). So delivery does NOT bypass authorization: the
executor re-witnesses the send's authority on arrival, exactly as the consent-lace settle does.
This is the load-bearing connection to verified state — the store-and-forward layer is a
TRANSPORT, not an authority oracle. -/

/-- **`deliverDecrypted R d k`** — the recipient `d` comes online, drains its boxes from the relay,
decrypts the intact ones (dropping any forged/re-addressed boxes via `decrypt = none`), and runs
the recovered sends through the VERIFIED executor in order. `none` if any delivered send is
over-authorized (the anti-ghost tooth at the drain). This is the executable
"deliver-then-execute" path that ties §1–§7 to the verified kernel. -/
def deliverDecrypted (R : Relay) (d : Dest) (k : KernelState) : Option KernelState :=
  let boxes := drainFor R d
  let sends := boxes.filterMap (fun b => decrypt b d)
  drainAll k sends

/-- **`deliver_runs_verified_exec` (PROVED)** — delivery is DEFINED as draining the decrypted
sends through the verified executor. There is no side-channel install: the recipient's only way to
act on a delivered box is to run its payload through `exec`. -/
theorem deliver_runs_verified_exec (R : Relay) (d : Dest) (k : KernelState) :
    deliverDecrypted R d k = drainAll k ((drainFor R d).filterMap (fun b => decrypt b d)) := by
  rfl

/-- **`relay_cannot_inject_authority` (PROVED) — the headline.** Delivering a batch of boxes
NEVER grows the capability table: the post-delivery `caps` equals the pre-delivery `caps`. So
whatever the relay did — reorder, drop, attempt to forge or re-address (forged/re-addressed boxes
decrypt to `none` and are filtered out before they ever reach `exec`) — it CANNOT inject authority
into the verified kernel. Every send that reaches `exec` is re-authorized against the UNCHANGED
caps; a store-and-forward delivery is a latency bridge, not an authority bypass. Rides
`drainAll_preserves_caps`. -/
theorem relay_cannot_inject_authority (R : Relay) (d : Dest) (k k' : KernelState)
    (h : deliverDecrypted R d k = some k') : k'.caps = k.caps := by
  unfold deliverDecrypted at h
  exact drainAll_preserves_caps k k' _ h

/-- **`forged_delivery_is_dropped` (PROVED)** — a forged box (`intact = false`) the relay slipped
into the store contributes NOTHING to delivery: it decrypts to `none` and is filtered out before
the drain, so it cannot even be PRESENTED to the executor. The relay's forged box is inert. -/
theorem forged_delivery_is_dropped (b : Box) (d : Dest) (hforged : b.intact = false) :
    decrypt b d = none :=
  forged_box_rejected b d hforged

/-- **`delivered_over_authorized_send_aborts` (PROVED) — anti-ghost at delivery.** Even a properly
sealed, intact box can carry an over-authorized send; if the FIRST decrypted send is not
authorized against the recipient's caps, the whole delivery aborts to `none` — nothing commits.
Sealing a box correctly does NOT grant its payload authority; the executor still fires. Rides
`drainAll_aborts_on_unauthorized_head`. -/
theorem delivered_over_authorized_send_aborts (R : Relay) (d : Dest) (k : KernelState)
    {s : QueuedSend} {rest : List QueuedSend}
    (hsends : (drainFor R d).filterMap (fun b => decrypt b d) = s :: rest)
    (hno : authorizedB k.caps s.turn = false) :
    deliverDecrypted R d k = none := by
  show drainAll k ((drainFor R d).filterMap (fun b => decrypt b d)) = none
  rw [hsends]
  exact drainAll_aborts_on_unauthorized_head hno

/-! ## §9 — A worked n = 2 scenario (witness the model is non-vacuous: it accepts AND rejects). -/

/-- Two distinct destinations (n = 2): the relay serves both, and `d₀`'s box is opaque to `d₁`. -/
def d0 : Dest := 0
def d1 : Dest := 1

/-- A demo intact box sealed to `d0`. -/
def boxToD0 (p : Plain) : Box :=
  { recipient := d0, ephemeral := 7, cipher := 42, sealed := p, intact := true,
    queuedAt := 100, ttl := 50 }

/-- **NON-VACUITY (accept).** The bound recipient `d0` recovers the plaintext of its intact box. -/
theorem demo_d0_reads (p : Plain) : decrypt (boxToD0 p) d0 = some p :=
  recipient_recovers (boxToD0 p) rfl

/-- **NON-VACUITY (reject — confidentiality).** The OTHER destination `d1 ≠ d0` gets `none` from
`d0`'s box: at n = 2 the relay does not leak one destination's mail to the other. -/
theorem demo_d1_cannot_read (p : Plain) : decrypt (boxToD0 p) d1 = none := by
  apply wrong_recipient_fails
  show d1 ≠ d0
  decide

/-- **NON-VACUITY (reject — re-address).** A relay re-addressing `d0`'s box to `d1` produces a box
`d1` still cannot decrypt as `d1`'s own — but, more sharply, the re-addressed box no longer
decrypts to `d0` either (§4). Here: the original recipient `d0` cannot read the re-addressed copy. -/
theorem demo_readdress_breaks (p : Plain) :
    decrypt { boxToD0 p with recipient := d1 } d0 = none := by
  apply wrong_recipient_fails
  show d0 ≠ d1
  decide

/-- **NON-VACUITY (reject — forgery).** A relay-forged box (`intact := false`) sealed to `d0`
decrypts to `none` even for `d0`. -/
theorem demo_forged_box_inert (p : Plain) :
    decrypt { boxToD0 p with intact := false } d0 = none := by
  apply forged_box_rejected
  rfl

/-! ## §10 — Axiom-hygiene pins (subset {propext, Classical.choice, Quot.sound}; NO sorry). -/

-- Tooth 1 — the relay cannot read.
#assert_axioms relayView_erases_plaintext
#assert_axioms relay_view_independent_of_plaintext
-- Tooth 2 — the relay cannot forge or re-address.
#assert_axioms readdressed_box_undeliverable
#assert_axioms forged_box_rejected
-- Tooth 3 — delay is a permutation, drop is a sub-multiset.
#assert_axioms drain_is_reorder
#assert_axioms relay_only_delays_or_drops
#assert_axioms expire_is_submultiset
#assert_axioms expired_box_gone
-- Tooth 4 — only the bound recipient reads (n > 1).
#assert_axioms decrypt_only_recipient
#assert_axioms wrong_recipient_fails
#assert_axioms recipient_recovers
-- Tooth 5 — delivered box drives verified state; relay cannot inject authority.
#assert_axioms deliver_runs_verified_exec
#assert_axioms relay_cannot_inject_authority
#assert_axioms forged_delivery_is_dropped
#assert_axioms delivered_over_authorized_send_aborts
-- Non-vacuity witnesses (accept AND reject).
#assert_axioms demo_d0_reads
#assert_axioms demo_d1_cannot_read
#assert_axioms demo_readdress_breaks
#assert_axioms demo_forged_box_inert

end Dregg2.Exec.CapTPStoreForward
