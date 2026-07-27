/-
# TlsHandshake.Post — the established-phase record driver (RFC 8446 §4.6, §5, §6)

`TlsHandshake.serverStep` ends at `established`; this module is what runs
*after*: the application-data record path over the application traffic secrets,
and the post-handshake messages of RFC 8446 §4.6 that arrive on it.

* **Application traffic keys** (§7.1/§7.3): entering the application phase
  derives `server/client_application_traffic_secret_0` and the resumption
  master secret from the established schedule — pure functions of the DHE and
  the transcript, like everything else in the schedule.
* **Record processing** (§5): each wire record is opened at the receive
  sequence number, its §5.4 padding stripped, and dispatched on the inner
  content type. A record that fails deprotection is fatal `bad_record_mac`
  (§5.2); an inner type this phase does not expect is `unexpected_message`.
* **KeyUpdate** (§4.6.3): `update_not_requested` advances the receive
  direction to the next-generation secret (§7.2) and resets its sequence;
  `update_requested` additionally replies with the server's own KeyUpdate —
  sealed under the *current* send keys, as the RFC requires — and then
  advances the send direction too.
* **close_notify** (§6.1): reciprocated, then the connection closes.

The theorems pin the §4.6.3/§7.2 behavior: which direction rekeys on which
message, that the reply to `update_requested` is sealed under the pre-update
keys, and that rekeying resets the sequence — each an equation about
`postHsMessage`, not a tautology.
-/
import TlsHandshake

namespace TlsHandshake

open Crypto TlsCrypto

/-- An established application-phase connection: the current (generation-N)
per-direction application traffic secrets, the record sequence numbers, and
the resumption master secret. Keys are derived from the secrets on use, so a
KeyUpdate is just a secret replacement. -/
structure AppConn where
  /-- The negotiated suite's record AEAD. -/
  aead : TlsCrypto.Aead
  /-- server_application_traffic_secret_N. -/
  txSecret : ByteArray
  /-- client_application_traffic_secret_N. -/
  rxSecret : ByteArray
  /-- Send-direction record sequence number. -/
  txSeq : Nat := 0
  /-- Receive-direction record sequence number. -/
  rxSeq : Nat := 0
  /-- resumption_master_secret (§7.1) — the PSK source for session tickets. -/
  resumptionMaster : ByteArray := ByteArray.empty
  /-- The negotiated ALPN protocol, if any. -/
  alpnProto : Option Tls.Bytes := none

/-- The send-direction record keys of the current generation. -/
def AppConn.txKeys (c : AppConn) : RecordKeys :=
  (trafficKeysA c.aead c.txSecret).getD defaultKeys

/-- The receive-direction record keys of the current generation. -/
def AppConn.rxKeys (c : AppConn) : RecordKeys :=
  (trafficKeysA c.aead c.rxSecret).getD defaultKeys

/-- Enter the application phase from an established handshake: derive both
directions' `application_traffic_secret_0` and the resumption master secret
from the schedule (RFC 8446 §7.1 — the traffic secrets over
Transcript-Hash(CH..server Finished), `res master` over the transcript through
the client Finished, which `serverStep` appended at establishment). -/
def mkAppConn (est : Established) : AppConn :=
  let ms := est.schedule.master.getD (zeros hashLen)
  { aead := suiteAead est.suite
    txSecret := est.schedule.serverAp.getD (zeros hashLen)
    rxSecret := est.schedule.clientAp.getD (zeros hashLen)
    resumptionMaster :=
      (deriveSecret ms "res master".toUTF8 (sha256 est.transcript)).getD (zeros hashLen)
    alpnProto := est.alpnProto }

/-- The next-generation traffic secret (§7.2), total form. -/
def nextGen (secret : ByteArray) : ByteArray :=
  (nextTrafficSecret secret).getD secret

/-- Rekey the receive direction (peer KeyUpdate, §4.6.3): next-generation
secret, sequence reset. -/
def AppConn.rekeyRx (c : AppConn) : AppConn :=
  { c with rxSecret := nextGen c.rxSecret, rxSeq := 0 }

/-- Rekey the send direction (after sending our KeyUpdate, §4.6.3). -/
def AppConn.rekeyTx (c : AppConn) : AppConn :=
  { c with txSecret := nextGen c.txSecret, txSeq := 0 }

theorem rekeyRx_resets_seq (c : AppConn) : c.rekeyRx.rxSeq = 0 := rfl
theorem rekeyRx_advances (c : AppConn) : c.rekeyRx.rxSecret = nextGen c.rxSecret := rfl
theorem rekeyRx_keeps_tx (c : AppConn) :
    c.rekeyRx.txSecret = c.txSecret ∧ c.rekeyRx.txSeq = c.txSeq := ⟨rfl, rfl⟩
theorem rekeyTx_keeps_rx (c : AppConn) :
    c.rekeyTx.rxSecret = c.rxSecret ∧ c.rekeyTx.rxSeq = c.rxSeq := ⟨rfl, rfl⟩

/-- Seal one application-phase record under the current send keys at the send
sequence, advancing it. Returns an empty wire only on a seal size error. -/
def appSeal (c : AppConn) (ctype : Nat) (content : ByteArray) :
    AppConn × ByteArray :=
  match sealRecordAt c.txKeys c.txSeq ctype content with
  | some wire => ({ c with txSeq := c.txSeq + 1 }, wire)
  | none => (c, ByteArray.empty)

/-- `appSeal` touches only the send direction: the receive secret and sequence
survive it unchanged. -/
theorem appSeal_preserves_rx (c : AppConn) (ctype : Nat) (content : ByteArray) :
    (appSeal c ctype content).1.rxSecret = c.rxSecret
    ∧ (appSeal c ctype content).1.rxSeq = c.rxSeq := by
  unfold appSeal
  split <;> exact ⟨rfl, rfl⟩

/-- The KeyUpdate handshake message (§4.6.3). -/
def keyUpdateMsg (requested : Bool) : ByteArray :=
  hsMsg 24 (u8 (if requested then 1 else 0))

/-- A `close_notify` alert body (warning level). -/
def closeNotifyPayload : ByteArray := ByteArray.mk #[0x01, 0x00]

/-- A fatal alert body. -/
def fatalPayload (desc : Nat) : ByteArray := ByteArray.mk #[0x02, UInt8.ofNat desc]

/-- What one post-handshake record meant. -/
inductive AppEvent where
  /-- Application data for the application layer. -/
  | deliver (content : Tls.Bytes)
  /-- The peer closed (close_notify); the reply is our reciprocal close. -/
  | close
  /-- A KeyUpdate was processed. -/
  | keyUpdated
  /-- A fatal condition; the reply is the alert, then the connection closes. -/
  | fatal (desc : Nat)
deriving Repr

/-- Process one post-handshake **handshake** message (inner type `0x16`).
KeyUpdate is the only §4.6 message this server accepts from an
already-authenticated client; anything else is `unexpected_message`. -/
def postHsMessage (c : AppConn) (msg : List UInt8) : AppConn × AppEvent × ByteArray :=
  match msg with
  | [0x18, 0x00, 0x00, 0x01, 0x00] =>
    -- update_not_requested: advance the peer's (receive) direction only.
    (c.rekeyRx, .keyUpdated, ByteArray.empty)
  | [0x18, 0x00, 0x00, 0x01, 0x01] =>
    -- update_requested: reply with our own KeyUpdate under the CURRENT send
    -- keys, then advance both directions (§4.6.3).
    let (c1, reply) := appSeal c 0x16 (keyUpdateMsg false)
    (c1.rekeyRx.rekeyTx, .keyUpdated, reply)
  | _ =>
    let (c1, alert) := appSeal c 0x15 (fatalPayload unexpectedMessageDesc)
    (c1, .fatal unexpectedMessageDesc, alert)

/-- **KeyUpdate rekeys exactly the announced direction** (§4.6.3):
`update_not_requested` advances the receive secret one generation and leaves
the send secret untouched. -/
theorem keyupdate_rekeys_rx_only (c : AppConn) :
    (postHsMessage c [0x18, 0x00, 0x00, 0x01, 0x00]).1.rxSecret = nextGen c.rxSecret
    ∧ (postHsMessage c [0x18, 0x00, 0x00, 0x01, 0x00]).1.txSecret = c.txSecret :=
  ⟨rfl, rfl⟩

/-- **`update_requested` advances both directions** — receive because the peer
updated, send because the RFC requires the reply-then-rekey. The send secret
becomes the next generation of the (unchanged-secret) post-reply connection. -/
theorem keyupdate_requested_rekeys_both (c : AppConn) :
    (postHsMessage c [0x18, 0x00, 0x00, 0x01, 0x01]).1.rxSecret = nextGen c.rxSecret
    ∧ (postHsMessage c [0x18, 0x00, 0x00, 0x01, 0x01]).1.txSecret
        = nextGen (appSeal c 0x16 (keyUpdateMsg false)).1.txSecret := by
  have hpre := appSeal_preserves_rx c 0x16 (keyUpdateMsg false)
  show ((appSeal c 0x16 (keyUpdateMsg false)).1.rekeyRx.rekeyTx).rxSecret = _
     ∧ ((appSeal c 0x16 (keyUpdateMsg false)).1.rekeyRx.rekeyTx).txSecret = _
  refine ⟨?_, rfl⟩
  show nextGen (appSeal c 0x16 (keyUpdateMsg false)).1.rxSecret = nextGen c.rxSecret
  rw [hpre.1]

/-- **The KeyUpdate reply goes out under the pre-update keys** (§4.6.3: "The
KeyUpdate message itself is protected under the old keys"): the reply bytes are
exactly `appSeal` at the connection's *current* send secret and sequence. -/
theorem keyupdate_reply_under_old_keys (c : AppConn) :
    (postHsMessage c [0x18, 0x00, 0x00, 0x01, 0x01]).2.2
      = (appSeal c 0x16 (keyUpdateMsg false)).2 := by
  show (let (_, reply) := appSeal c 0x16 (keyUpdateMsg false)
        reply) = (appSeal c 0x16 (keyUpdateMsg false)).2
  obtain ⟨c1, reply⟩ := appSeal c 0x16 (keyUpdateMsg false)
  rfl

/-- Process one wire record in the application phase: open at the receive
sequence, strip padding, dispatch on the inner content type. Returns the
successor connection, the event, and bytes to send in reply (possibly empty). -/
def appStep (c : AppConn) (wire : Tls.Bytes) : AppConn × AppEvent × ByteArray :=
  match openRecordAt c.rxKeys c.rxSeq wire with
  | none =>
    -- §5.2: a record that fails deprotection is fatal bad_record_mac.
    let (c1, alert) := appSeal c 0x15 (fatalPayload badRecordMacDesc)
    (c1, .fatal badRecordMacDesc, alert)
  | some (t, content) =>
    let c := { c with rxSeq := c.rxSeq + 1 }
    if t == 0x17 then
      (c, .deliver content.toList, ByteArray.empty)
    else if t == 0x15 then
      -- An alert. close_notify is reciprocated (§6.1); a fatal alert closes.
      let (c1, reply) := appSeal c 0x15 closeNotifyPayload
      (c1, .close, reply)
    else if t == 0x16 then
      postHsMessage c content.toList
    else
      let (c1, alert) := appSeal c 0x15 (fatalPayload unexpectedMessageDesc)
      (c1, .fatal unexpectedMessageDesc, alert)

/-- **The application phase enforces the receive sequence.** A delivered record
advances `rxSeq` by exactly one — the AEAD nonce for record N+1 differs from
record N's, so a replayed record cannot open twice (`record_forgery_fails`
at the new nonce). -/
theorem appStep_deliver_advances_seq (c : AppConn) (wire : Tls.Bytes)
    (content : Tls.Bytes)
    (h : (appStep c wire).2.1 = AppEvent.deliver content) :
    (appStep c wire).1.rxSeq = c.rxSeq + 1 := by
  -- Only the `t == 0x17` (application_data) branch of `appStep` produces a
  -- `deliver` event, and that branch's connection is `c` with `rxSeq + 1`.
  unfold appStep at h ⊢
  -- Enumerate every branch of `appStep`; the `deliver` event arises only in the
  -- application_data branch, whose successor is `c` with `rxSeq + 1`.
  revert h
  split
  · intro h; exact absurd h (by simp [appSeal])
  · split
    · intro _; rfl
    · split
      · intro h; exact absurd h (by simp [appSeal])
      · split
        · unfold postHsMessage
          split
          · intro h; exact absurd h (by simp)
          · intro h; exact absurd h (by simp [appSeal])
          · intro h; exact absurd h (by simp [appSeal])
        · intro h; exact absurd h (by simp [appSeal])

/-- The minimal HTTP/1.1 responder served over the established connection —
the fixed 200 any complete request receives, carrying the standard security
response headers (HSTS per RFC 6797, a deny-all CSP, nosniff, frame denial,
and a no-referrer policy). -/
def httpResponse : ByteArray :=
  ("HTTP/1.1 200 OK\r\nContent-Type: text/plain; charset=utf-8\r\n"
    ++ "Content-Length: 12\r\nConnection: keep-alive\r\n"
    ++ "Strict-Transport-Security: max-age=31536000; includeSubDomains\r\n"
    ++ "Content-Security-Policy: default-src 'none'; frame-ancestors 'none'\r\n"
    ++ "X-Content-Type-Options: nosniff\r\n"
    ++ "X-Frame-Options: DENY\r\n"
    ++ "Referrer-Policy: no-referrer\r\n"
    ++ "Cross-Origin-Resource-Policy: same-origin\r\n"
    ++ "Cache-Control: no-store\r\n\r\nhello, tls\r\n").toUTF8

/-- Does the accumulated request contain the end-of-headers CRLFCRLF? -/
def hasCrlfCrlf : List UInt8 → Bool
  | 13 :: 10 :: 13 :: 10 :: _ => true
  | _ :: rest => hasCrlfCrlf rest
  | [] => false

end TlsHandshake
