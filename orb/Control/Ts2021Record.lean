import Control
import Crypto
import Control.Ts2021Core
import Control.Channel
import Control.Ts2021Wire

/-!
# Control.Ts2021Record — the ts2021 transport **record** layer

After the `Noise_IK` handshake (`Control.Ts2021Core`) both ends hold a pair of
directional transport keys. Every subsequent control message rides as an
AEAD-sealed **record**, and each direction keeps its own record counter.

★ The record counter is encoded **big-endian** (`Ts2021Wire.recordNonce`), unlike
the handshake's little-endian Noise counter (`Ts2021Wire.noiseNonce`). This
module exists so that the record layer has exactly one entry point and that entry
point cannot be handed the handshake nonce: `RecordState` carries a *counter*,
never a nonce, and turns it into bytes itself. `sealRecord_nonce` /
`openRecord_nonce` are the definitional guarantee that the encoding used is
`recordNonce`.

Cross-checked against github.com/tailscale/tailscale (BSD-3)
`control/controlbase/conn.go` at `main` — see `Ts2021Wire.recordNonce`'s
docstring for the quoted `nonce.Valid` / `nonce.Increment` (lines 385-396) and
the `encryptLocked` / read-path call sites (lines 162-175 / 142-147). The AEAD
runs with empty additional data there (`Seal(..., plaintext, nil)`), which is
what `Control.Channel.sealFrame` passes.
-/

namespace Control.Ts2021Record

open Control (Bytes)
open Control.Ts2021Wire (recordNonce recordNonceValid invalidNonce)

/-- One direction of the transport: a key and the record counter under it.
Holding the *counter* (not a nonce) is what makes the wrong encoding
unreachable — only `recordNonce` ever turns it into bytes. -/
structure RecordState where
  key : ByteArray
  ctr : Nat
  deriving Inhabited

/-- `nonce.Increment()`. -/
def RecordState.bump (s : RecordState) : RecordState := { s with ctr := s.ctr + 1 }

@[simp] theorem RecordState.bump_key (s : RecordState) : s.bump.key = s.key := rfl
@[simp] theorem RecordState.bump_ctr (s : RecordState) : s.bump.ctr = s.ctr + 1 := rfl

/-- Seal one record and advance the counter (`encryptLocked` then `Increment`). -/
def sealRecord (s : RecordState) (payload : Bytes) : Option (Bytes × RecordState) :=
  (Control.Channel.sealFrame s.key (recordNonce s.ctr) payload).map (fun f => (f, s.bump))

/-- Open one record and advance the counter (`decryptLocked` then `Increment`). -/
def openRecord (s : RecordState) (frame : Bytes) : Option (Bytes × RecordState) :=
  (Control.Channel.openFrame s.key (recordNonce s.ctr) frame).map (fun p => (p, s.bump))

/-! ## The record layer uses the big-endian nonce (definitional) -/

/-- **The send path's nonce is `recordNonce s.ctr`** — true by definition, so no
call site can substitute `noiseNonce`. -/
theorem sealRecord_nonce (s : RecordState) (payload : Bytes) :
    sealRecord s payload
      = (Control.Channel.sealFrame s.key (recordNonce s.ctr) payload).map
          (fun f => (f, s.bump)) := rfl

/-- **The receive path's nonce is `recordNonce s.ctr`.** -/
theorem openRecord_nonce (s : RecordState) (frame : Bytes) :
    openRecord s frame
      = (Control.Channel.openFrame s.key (recordNonce s.ctr) frame).map
          (fun p => (p, s.bump)) := rfl

/-- The counter advances by exactly one per sealed record. -/
theorem sealRecord_ctr {s : RecordState} {payload f : Bytes} {s' : RecordState}
    (h : sealRecord s payload = some (f, s')) : s'.ctr = s.ctr + 1 ∧ s'.key = s.key := by
  unfold sealRecord at h
  cases hc : Control.Channel.sealFrame s.key (recordNonce s.ctr) payload with
  | none => rw [hc] at h; simp at h
  | some ct => rw [hc] at h
               simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
               rw [← h.2]; exact ⟨rfl, rfl⟩

/-- The counter advances by exactly one per opened record. -/
theorem openRecord_ctr {s : RecordState} {frame p : Bytes} {s' : RecordState}
    (h : openRecord s frame = some (p, s')) : s'.ctr = s.ctr + 1 ∧ s'.key = s.key := by
  unfold openRecord at h
  cases hc : Control.Channel.openFrame s.key (recordNonce s.ctr) frame with
  | none => rw [hc] at h; simp at h
  | some pt => rw [hc] at h
               simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
               rw [← h.2]; exact ⟨rfl, rfl⟩

/-! ## Round-trip -/

/-- **One record round-trips at any counter.** A record sealed at counter `n`
under the sender's key opens, at the *same* counter `n` under the matching
receive key, to exactly the payload — and both sides land on `n + 1`.

The hypothesis `sk = rk` is discharged for a real channel by
`Control.Channel.channel_established_keys_agree`; the AEAD round-trip itself
rests on `Crypto.Assumptions.chacha_open_seal_roundtrip` (an explicit assumption
about the EverCrypt binding, not a proof of it). -/
theorem record_roundtrip (sk rk : ByteArray) (hk : sk = rk) (n : Nat)
    (payload f : Bytes) {s' : RecordState}
    (hs : sealRecord ⟨sk, n⟩ payload = some (f, s')) :
    openRecord ⟨rk, n⟩ f = some (payload, ⟨rk, n + 1⟩) := by
  subst hk
  unfold sealRecord at hs
  cases hc : Control.Channel.sealFrame sk (recordNonce n) payload with
  | none => rw [hc] at hs; simp at hs
  | some ct =>
    rw [hc] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    have hopen : Control.Channel.openFrame sk (recordNonce n) f = some payload := by
      rw [← hs.1]; exact Control.Channel.seal_open sk sk (recordNonce n) payload rfl hc
    simp [openRecord, hopen, RecordState.bump]

/-! ## Streams: the counters stay in lockstep -/

/-- Seal a whole sequence of payloads, threading the counter. -/
def sealStream (s : RecordState) : List Bytes → Option (List Bytes × RecordState)
  | [] => some ([], s)
  | p :: ps =>
    match sealRecord s p with
    | some (f, s') => (sealStream s' ps).map (fun r => (f :: r.1, r.2))
    | none => none

/-- Open a whole sequence of frames, threading the counter. -/
def openStream (s : RecordState) : List Bytes → Option (List Bytes × RecordState)
  | [] => some ([], s)
  | f :: fs =>
    match openRecord s f with
    | some (p, s') => (openStream s' fs).map (fun r => (p :: r.1, r.2))
    | none => none

/-- **A whole record stream round-trips, and the receiver's counter tracks the
sender's.** Starting from counter `n`, if the sender seals `ps` into frames `fs`,
the receiver starting at the *same* `n` recovers exactly `ps` and ends at
`n + ps.length`. This is the counter-monotonicity / no-nonce-reuse property in
operational form: frame `i` is sealed and opened under `recordNonce (n + i)`, and
`recordNonce_injective` says those are pairwise distinct. -/
theorem stream_roundtrip (sk rk : ByteArray) (hk : sk = rk) :
    ∀ (ps : List Bytes) (n : Nat) (fs : List Bytes) (s' : RecordState),
      sealStream ⟨sk, n⟩ ps = some (fs, s') →
      openStream ⟨rk, n⟩ fs = some (ps, ⟨rk, n + ps.length⟩) := by
  subst hk
  intro ps
  induction ps with
  | nil =>
    intro n fs s' h
    simp only [sealStream, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; simp [openStream]
  | cons p ps ih =>
    intro n fs s' h
    simp only [sealStream] at h
    cases hsr : sealRecord (⟨sk, n⟩ : RecordState) p with
    | none => rw [hsr] at h; simp at h
    | some r =>
      obtain ⟨f, s1⟩ := r
      rw [hsr] at h
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨rest, hrest, hEq⟩ := h
      rw [Prod.mk.injEq] at hEq
      obtain ⟨hfs, _⟩ := hEq
      subst hfs
      have hs1 := sealRecord_ctr hsr
      have hopen1 : openRecord (⟨sk, n⟩ : RecordState) f = some (p, ⟨sk, n + 1⟩) :=
        record_roundtrip sk sk rfl n p f hsr
      have hs1eq : s1 = (⟨sk, n + 1⟩ : RecordState) := by
        cases s1; simp only [RecordState.mk.injEq]; exact ⟨hs1.2, hs1.1⟩
      subst hs1eq
      have hih := ih (n + 1) rest.1 rest.2 hrest
      have hlen : n + 1 + ps.length = n + (p :: ps).length := by
        simp only [List.length_cons]; omega
      rw [openStream, hopen1]
      simp only [hih, hlen, Option.map_some]

/-! ## Exhaustion

`controlbase` refuses to encrypt once the counter would pass `invalidNonce`
(`errCipherExhausted`). We do not model the refusal in `sealRecord` (the FSM that
owns the connection lifecycle does); we state the predicate so a call site can
check it, and record that every counter reachable below it is a valid `uint64`. -/

theorem recordNonceValid_of_lt {n : Nat} (h : n < invalidNonce) : recordNonceValid n = true := by
  show (n != invalidNonce) = true
  exact bne_iff_ne.mpr (Nat.ne_of_lt h)

/-! ## The exhaustion-checked entry point — what the LIVE connection drives

`sealRecord` / `openRecord` above are total: they will happily seal at any
counter. But `controlbase` refuses once the counter reaches `invalidNonce`
(`2^64-1`): `nonce.Increment()` *panics* (`conn.go`), and the connection is
declared exhausted (`errCipherExhausted`). The live post-handshake connection
must therefore drive a checked entry point that turns that panic into an explicit
refusal — so no frame is ever emitted under an out-of-range (would-repeat)
counter. `sealChecked` / `openChecked` are that entry point; the FSM/driver holds
one `RecordState` per direction and threads it through these. -/

/-- Why a checked record op refused. `exhausted` is `controlbase`'s
`errCipherExhausted` — the counter reached `invalidNonce`; `aead` is a failure at
the AEAD itself (bad key/nonce size, or — on open — authentication failure,
indistinguishable per the cipher's contract). -/
inductive RecordErr where
  | exhausted
  | aead
  deriving DecidableEq, Repr, Inhabited

/-- **Seal through the record state, refusing at exhaustion.** Below
`invalidNonce` this is exactly `sealRecord` (advancing the counter); at the
exhausted counter it emits no frame and returns `errCipherExhausted`. -/
def sealChecked (s : RecordState) (payload : Bytes) :
    Except RecordErr (Bytes × RecordState) :=
  match recordNonceValid s.ctr with
  | true  => match sealRecord s payload with
             | some r => .ok r
             | none   => .error .aead
  | false => .error .exhausted

/-- **Open through the record state, refusing at exhaustion.** -/
def openChecked (s : RecordState) (frame : Bytes) :
    Except RecordErr (Bytes × RecordState) :=
  match recordNonceValid s.ctr with
  | true  => match openRecord s frame with
             | some r => .ok r
             | none   => .error .aead
  | false => .error .exhausted

/-- **The exhausted send path refuses.** At `invalidNonce` (`errCipherExhausted`)
`sealChecked` returns the exhaustion error and emits no frame — the
`nonce.Increment()` panic, made total. This is the enforcement the live loop
relies on: it cannot be handed a valid frame past the counter's range. -/
theorem sealChecked_exhausted (s : RecordState) (payload : Bytes)
    (h : s.ctr = invalidNonce) : sealChecked s payload = .error .exhausted := by
  simp [sealChecked, recordNonceValid, h]

/-- Likewise the receive path refuses at exhaustion. -/
theorem openChecked_exhausted (s : RecordState) (frame : Bytes)
    (h : s.ctr = invalidNonce) : openChecked s frame = .error .exhausted := by
  simp [openChecked, recordNonceValid, h]

/-- Below the exhaustion bound `sealChecked` is exactly `sealRecord` lifted into
`Except`: a valid counter never refuses for exhaustion, only the AEAD can. -/
theorem sealChecked_ok (s : RecordState) {payload f : Bytes} {s' : RecordState}
    (hv : recordNonceValid s.ctr = true) (h : sealRecord s payload = some (f, s')) :
    sealChecked s payload = .ok (f, s') := by
  simp [sealChecked, hv, h]

/-- **The exhaustion-checked live path round-trips.** A record the send side
*accepts* (counter valid, seal succeeded) opens on the receive side under the
matching key at the same counter, recovering the payload and advancing both
counters — `record_roundtrip`, now over the checked entry point the live
connection drives. So the record-layer correctness is load-bearing for the LIVE
path, not just the total `sealRecord`. -/
theorem checked_roundtrip (sk rk : ByteArray) (hk : sk = rk) (n : Nat)
    (payload f : Bytes) {s' : RecordState}
    (hv : recordNonceValid n = true)
    (hs : sealChecked ⟨sk, n⟩ payload = .ok (f, s')) :
    openChecked ⟨rk, n⟩ f = .ok (payload, ⟨rk, n + 1⟩) := by
  simp only [sealChecked, hv] at hs
  cases hc : sealRecord (⟨sk, n⟩ : RecordState) payload with
  | none => rw [hc] at hs; simp at hs
  | some r =>
    rw [hc] at hs
    simp only [Except.ok.injEq] at hs
    have hsr : sealRecord (⟨sk, n⟩ : RecordState) payload = some (f, s') := by rw [hc, hs]
    have hopen := record_roundtrip sk rk hk n payload f hsr
    simp only [openChecked, hv, hopen]

/-! ## Typed control messages over the checked record state

The live connection carries typed control messages (`RegisterRequest`,
`MapRequest`, `MapResponse`). `sealMsg` / `openMsg` seal an encoded message
through the exhaustion-checked record state and thread the counter, so a whole
directional exchange (register **then** map-poll on the node→coord counter, the
map response on the coord→node counter) advances one big-endian nonce per frame
with no reuse. -/

/-- Seal a message: encode it, then seal the bytes through the checked state. -/
def sealMsg {α} (enc : α → Bytes) (s : RecordState) (m : α) :
    Except RecordErr (Bytes × RecordState) := sealChecked s (enc m)

/-- Open a frame as a message: open through the checked state, then decode. -/
def openMsg {α} (dec : Bytes → Option (α × Bytes)) (s : RecordState) (frame : Bytes) :
    Except RecordErr (α × RecordState) :=
  match openChecked s frame with
  | .ok (bs, s') =>
    match dec bs with
    | some (m, _) => .ok (m, s')
    | none        => .error .aead
  | .error e => .error e

/-- **A typed message round-trips through the checked record layer.** Given a
codec whose decode inverts its encode (the `getX_put` round-trips already proven
in `Control` / `Control.Channel`), a message sealed at a valid counter `n` on one
side opens on the peer at the same `n` to exactly that message, both counters
landing on `n+1`. Instantiated below for `RegisterRequest`, `MapRequest`, and
`MapResponse` — the three messages the live exchange carries. -/
theorem msg_roundtrip {α} (enc : α → Bytes) (dec : Bytes → Option (α × Bytes))
    (hrt : ∀ (m : α) (t : Bytes), dec (enc m ++ t) = some (m, t))
    (sk rk : ByteArray) (hk : sk = rk) (n : Nat) (m : α)
    (hv : recordNonceValid n = true) {f : Bytes} {s' : RecordState}
    (hs : sealMsg enc ⟨sk, n⟩ m = .ok (f, s')) :
    openMsg dec ⟨rk, n⟩ f = .ok (m, ⟨rk, n + 1⟩) := by
  unfold sealMsg at hs
  have hopen := checked_roundtrip sk rk hk n (enc m) f hv hs
  have hg : dec (enc m) = some (m, []) := by
    have := hrt m []; rwa [List.append_nil] at this
  simp only [openMsg, hopen, hg]

/-! ## The REAL ts2021 wire record — `[type=4][u16 BE len][raw ciphertext]`

★ Everything above frames a ciphertext through `Control.Channel.sealFrame`, whose
`encodeFrame ct = recordTag(3) :: putBytes ct` is a **drorb-native** tag + uvarint
length — NOT the ts2021 wire. A stock `controlbase` record is the 3-byte header
`[msgTypeRecord=4][u16 BE ciphertext-length]` followed by the **raw** AEAD
ciphertext (no recordTag, no uvarint), cross-checked byte-for-byte against
`github.com/tailscale/tailscale` (BSD-3) at **v1.98.8**:

* `control/controlbase/messages.go` L21 `msgTypeRecord = 4`, L24 `headerLen = 3`.
* `control/controlbase/conn.go` `encryptLocked` L169-171:
  `buf[0] = msgTypeRecord`;
  `binary.BigEndian.PutUint16(buf[1:headerLen], uint16(len(plaintext)+chp.Overhead))`;
  `ret := c.tx.cipher.Seal(buf[:headerLen], c.tx.nonce[:], plaintext, nil)` —
  i.e. `[4][u16 BE (ptlen+16)]` then the ciphertext appended after the header, with
  **empty** additional data (the trailing `nil`).
* `decryptLocked` L134/L140: require `msg[0] == msgTypeRecord`, then
  `ciphertext := msg[headerLen:]` (raw, the length field already consumed by the
  reader). Frame parse L188/L230: `headerLen + int(binary.BigEndian.Uint16(bs[1:3]))`.

`Control.Ts2021Wire.encodeRecord` / `parseRecord` is exactly that framing and is
already proven (`Ts2021Wire.parseRecord_encodeRecord`, `Ts2021Wire.record_seal_open`).
`sealRecordTs2021` / `openRecordTs2021` are the **counter-managed** record-state
entry points over that real framing: the live connection drives these instead of
the raw AEAD workaround, and — exactly as with `sealRecord` — `RecordState` carries
a *counter*, never a nonce, so only `recordNonce s.ctr` ever becomes nonce bytes. -/

/-- Seal one record onto the REAL ts2021 wire and advance the counter:
`Ts2021Wire.sealRecord` (3-byte controlbase header + raw ciphertext) at
`recordNonce s.ctr`, then `Increment`. -/
def sealRecordTs2021 (s : RecordState) (payload : Bytes) : Option (Bytes × RecordState) :=
  (Control.Ts2021Wire.sealRecord s.key (recordNonce s.ctr) payload).map (fun f => (f, s.bump))

/-- Open one real-wire ts2021 record and advance the counter. -/
def openRecordTs2021 (s : RecordState) (frame : Bytes) : Option (Bytes × RecordState) :=
  (Control.Ts2021Wire.openRecord s.key (recordNonce s.ctr) frame).map (fun p => (p, s.bump))

/-- **The send path's nonce is `recordNonce s.ctr`** — definitional, so no call
site can substitute `noiseNonce`. -/
theorem sealRecordTs2021_nonce (s : RecordState) (payload : Bytes) :
    sealRecordTs2021 s payload
      = (Control.Ts2021Wire.sealRecord s.key (recordNonce s.ctr) payload).map
          (fun f => (f, s.bump)) := rfl

/-- **The receive path's nonce is `recordNonce s.ctr`.** -/
theorem openRecordTs2021_nonce (s : RecordState) (frame : Bytes) :
    openRecordTs2021 s frame
      = (Control.Ts2021Wire.openRecord s.key (recordNonce s.ctr) frame).map
          (fun p => (p, s.bump)) := rfl

/-- The counter advances by exactly one per sealed real-wire record. -/
theorem sealRecordTs2021_ctr {s : RecordState} {payload f : Bytes} {s' : RecordState}
    (h : sealRecordTs2021 s payload = some (f, s')) : s'.ctr = s.ctr + 1 ∧ s'.key = s.key := by
  unfold sealRecordTs2021 at h
  cases hc : Control.Ts2021Wire.sealRecord s.key (recordNonce s.ctr) payload with
  | none => rw [hc] at h; simp at h
  | some ct => rw [hc] at h
               simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
               rw [← h.2]; exact ⟨rfl, rfl⟩

/-- The counter advances by exactly one per opened real-wire record. -/
theorem openRecordTs2021_ctr {s : RecordState} {frame p : Bytes} {s' : RecordState}
    (h : openRecordTs2021 s frame = some (p, s')) : s'.ctr = s.ctr + 1 ∧ s'.key = s.key := by
  unfold openRecordTs2021 at h
  cases hc : Control.Ts2021Wire.openRecord s.key (recordNonce s.ctr) frame with
  | none => rw [hc] at h; simp at h
  | some pt => rw [hc] at h
               simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
               rw [← h.2]; exact ⟨rfl, rfl⟩

/-- **One REAL-wire record round-trips at any counter.** Sealed at counter `n`
under the sender key it opens at the same `n` under the matching receive key to
exactly the payload, both sides landing on `n + 1` — over the byte-exact
`controlbase` framing. The side condition `hlen` is that the sealed ciphertext
fits a `uint16` (records are length-bounded on the wire — `conn.go` L28
`maxMessageSize = 4096`, so every real record satisfies it); the AEAD round-trip
is `Ts2021Wire.record_seal_open`, resting on the same
`Crypto.Assumptions.chacha_open_seal_roundtrip` assumption as `record_roundtrip`. -/
theorem record_roundtrip_ts2021 (sk rk : ByteArray) (hk : sk = rk) (n : Nat)
    (payload f : Bytes) {s' : RecordState}
    (hlen : ∀ ct, Crypto.chachaSeal sk (recordNonce n) ByteArray.empty
              (Control.Channel.baOf payload) = some ct →
              (Control.Channel.bytesOf ct).length < 65536)
    (hs : sealRecordTs2021 ⟨sk, n⟩ payload = some (f, s')) :
    openRecordTs2021 ⟨rk, n⟩ f = some (payload, ⟨rk, n + 1⟩) := by
  subst hk
  unfold sealRecordTs2021 at hs
  cases hc : Control.Ts2021Wire.sealRecord sk (recordNonce n) payload with
  | none => rw [hc] at hs; simp at hs
  | some ct =>
    rw [hc] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    have hof : Control.Ts2021Wire.openRecord sk (recordNonce n) f = some payload := by
      rw [← hs.1]
      exact Control.Ts2021Wire.record_seal_open sk sk (recordNonce n) payload rfl hc hlen
    simp [openRecordTs2021, hof, RecordState.bump]

/-! ## The exhaustion-checked real-wire entry point — what the LIVE path drives -/

/-- **Seal through the record state onto the real wire, refusing at exhaustion.**
Below `invalidNonce` this is exactly `sealRecordTs2021`; at the exhausted counter
it emits no frame (`errCipherExhausted`, the `nonce.Increment()` panic made
total). -/
def sealCheckedTs2021 (s : RecordState) (payload : Bytes) :
    Except RecordErr (Bytes × RecordState) :=
  match recordNonceValid s.ctr with
  | true  => match sealRecordTs2021 s payload with
             | some r => .ok r
             | none   => .error .aead
  | false => .error .exhausted

/-- **Open through the record state from the real wire, refusing at exhaustion.** -/
def openCheckedTs2021 (s : RecordState) (frame : Bytes) :
    Except RecordErr (Bytes × RecordState) :=
  match recordNonceValid s.ctr with
  | true  => match openRecordTs2021 s frame with
             | some r => .ok r
             | none   => .error .aead
  | false => .error .exhausted

/-- The exhausted send path refuses (`errCipherExhausted`) and emits no frame. -/
theorem sealCheckedTs2021_exhausted (s : RecordState) (payload : Bytes)
    (h : s.ctr = invalidNonce) : sealCheckedTs2021 s payload = .error .exhausted := by
  simp [sealCheckedTs2021, recordNonceValid, h]

/-- The exhausted receive path likewise refuses. -/
theorem openCheckedTs2021_exhausted (s : RecordState) (frame : Bytes)
    (h : s.ctr = invalidNonce) : openCheckedTs2021 s frame = .error .exhausted := by
  simp [openCheckedTs2021, recordNonceValid, h]

/-- **The exhaustion-checked real-wire path round-trips.** A record the send side
*accepts* (counter valid, seal succeeded) opens on the receive side under the
matching key at the same counter — `record_roundtrip_ts2021` over the checked
entry point the LIVE connection drives, so the real-framing correctness is
load-bearing for the live path, not just the total `sealRecordTs2021`. -/
theorem checked_roundtrip_ts2021 (sk rk : ByteArray) (hk : sk = rk) (n : Nat)
    (payload f : Bytes) {s' : RecordState}
    (hv : recordNonceValid n = true)
    (hlen : ∀ ct, Crypto.chachaSeal sk (recordNonce n) ByteArray.empty
              (Control.Channel.baOf payload) = some ct →
              (Control.Channel.bytesOf ct).length < 65536)
    (hs : sealCheckedTs2021 ⟨sk, n⟩ payload = .ok (f, s')) :
    openCheckedTs2021 ⟨rk, n⟩ f = .ok (payload, ⟨rk, n + 1⟩) := by
  simp only [sealCheckedTs2021, hv] at hs
  cases hc : sealRecordTs2021 (⟨sk, n⟩ : RecordState) payload with
  | none => rw [hc] at hs; simp at hs
  | some r =>
    rw [hc] at hs
    simp only [Except.ok.injEq] at hs
    have hsr : sealRecordTs2021 (⟨sk, n⟩ : RecordState) payload = some (f, s') := by rw [hc, hs]
    have hopen := record_roundtrip_ts2021 sk rk hk n payload f hlen hsr
    simp only [openCheckedTs2021, hv, hopen]

/-! ## Typed control messages over the real-wire checked record state -/

/-- Seal a message onto the real wire: encode, then seal through the checked
state. This is the entry point the live node→coord / coord→node exchange drives
(swapping the raw workaround for the proven layer). -/
def sealMsgTs2021 {α} (enc : α → Bytes) (s : RecordState) (m : α) :
    Except RecordErr (Bytes × RecordState) := sealCheckedTs2021 s (enc m)

/-- Open a real-wire frame as a message: open through the checked state, decode. -/
def openMsgTs2021 {α} (dec : Bytes → Option (α × Bytes)) (s : RecordState) (frame : Bytes) :
    Except RecordErr (α × RecordState) :=
  match openCheckedTs2021 s frame with
  | .ok (bs, s') =>
    match dec bs with
    | some (m, _) => .ok (m, s')
    | none        => .error .aead
  | .error e => .error e

/-- **A typed message round-trips through the real-wire checked record layer.**
Given a codec whose decode inverts its encode, a message sealed at a valid
counter `n` opens on the peer at the same `n` to exactly that message, both
counters landing on `n+1` — the `RegisterRequest` / `MapRequest` / `MapResponse`
exchange the live path carries, now over the byte-exact `controlbase` frame. -/
theorem msg_roundtrip_ts2021 {α} (enc : α → Bytes) (dec : Bytes → Option (α × Bytes))
    (hrt : ∀ (m : α) (t : Bytes), dec (enc m ++ t) = some (m, t))
    (sk rk : ByteArray) (hk : sk = rk) (n : Nat) (m : α)
    (hv : recordNonceValid n = true)
    (hlen : ∀ ct, Crypto.chachaSeal sk (recordNonce n) ByteArray.empty
              (Control.Channel.baOf (enc m)) = some ct →
              (Control.Channel.bytesOf ct).length < 65536)
    {f : Bytes} {s' : RecordState}
    (hs : sealMsgTs2021 enc ⟨sk, n⟩ m = .ok (f, s')) :
    openMsgTs2021 dec ⟨rk, n⟩ f = .ok (m, ⟨rk, n + 1⟩) := by
  unfold sealMsgTs2021 at hs
  have hopen := checked_roundtrip_ts2021 sk rk hk n (enc m) f hv hlen hs
  have hg : dec (enc m) = some (m, []) := by
    have := hrt m []; rwa [List.append_nil] at this
  simp only [openMsgTs2021, hopen, hg]

end Control.Ts2021Record

/-! ## Axiom audit -/
#print axioms Control.Ts2021Wire.recordNonceCounter_recordNonce
#print axioms Control.Ts2021Wire.recordNonce_injective
#print axioms Control.Ts2021Wire.recordNonce_ne_noiseNonce
#print axioms Control.Ts2021Record.sealRecord_nonce
#print axioms Control.Ts2021Record.openRecord_nonce
#print axioms Control.Ts2021Record.record_roundtrip
#print axioms Control.Ts2021Record.stream_roundtrip
#print axioms Control.Ts2021Record.sealChecked_exhausted
#print axioms Control.Ts2021Record.openChecked_exhausted
#print axioms Control.Ts2021Record.checked_roundtrip
-- the REAL ts2021 wire record layer ([type=4][u16 BE len][raw ct]):
#print axioms Control.Ts2021Record.sealRecordTs2021_nonce
#print axioms Control.Ts2021Record.openRecordTs2021_nonce
#print axioms Control.Ts2021Record.sealRecordTs2021_ctr
#print axioms Control.Ts2021Record.record_roundtrip_ts2021
#print axioms Control.Ts2021Record.sealCheckedTs2021_exhausted
#print axioms Control.Ts2021Record.openCheckedTs2021_exhausted
#print axioms Control.Ts2021Record.checked_roundtrip_ts2021
#print axioms Control.Ts2021Record.msg_roundtrip_ts2021
#print axioms Control.Ts2021Record.msg_roundtrip
