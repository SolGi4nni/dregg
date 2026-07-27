import Derp.Frame
/-!
# The DERP HTTP upgrade — the crossing the proven frame codec sits behind

`Derp.lean` proves the frame envelope and `Derp.Server.dispatch` proves the relay's
routing decision, but neither says anything about how a connection BECOMES a frame
stream. A real client does not open a socket and start writing frames: it speaks one
HTTP request first —

    GET /derp HTTP/1.1
    Host: <host>
    Upgrade: DERP
    Connection: Upgrade
    [Derp-Fast-Start: 1]
    <CRLF>

— and only the bytes AFTER that header block are frames. The live relay used to do
this by hand (`drainUpgrade`: read chunks until some CRLF CRLF appears anywhere in the
accumulator, then throw the accumulator away). That is the SPEC GAP, and it is not
cosmetic: the read that completes the header block can, and over a TLS record stream
routinely does, also carry the first frame bytes. Discarding the accumulator DROPS
them, and the frame reader then resynchronises on the middle of a frame.

This module closes the gap in the model. The upgrade is a total function on the
byte stream

    splitHead? : Bytes → Option (Bytes × Bytes)

that returns the header block (terminator included) and the **residue**, and the
theorems below say the residue is exactly the un-consumed suffix — `upgrade_no_loss`
(`s = hd ++ rest`) — so composing the upgrade with the proven codec
(`upgrade_residue_is_frame_stream`) parses the client's first frame verbatim. The
relay's reply is a function of the request (`serveUpgrade`): a stock client gets the
`101 Switching Protocols` it blocks on, a `Derp-Fast-Start` client gets NO HTTP bytes
at all (`serveUpgrade_faststart_silent`), which is what makes drorb's own fast-start
client and a stock client both work against one relay.

Nothing here weakens the codec: it is an additive layer that ends exactly where
`Derp.decodeFrame` begins.
-/

namespace Derp.Upgrade

/-! ## Byte-level helpers -/

/-- ASCII/UTF-8 bytes of a literal — the wire constants below are written as text. -/
def strBytes (s : String) : Bytes := s.toUTF8.data.toList

/-- `p` is a prefix of `s`. -/
def isPrefixB : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: p, b :: s => a == b && isPrefixB p s

/-- `n` occurs somewhere in `h`. -/
def isInfixB (n : Bytes) : Bytes → Bool
  | [] => isPrefixB n []
  | b :: t => isPrefixB n (b :: t) || isInfixB n t

theorem isPrefixB_sound : ∀ {p s : Bytes}, isPrefixB p s = true → ∃ t, s = p ++ t
  | [], s, _ => ⟨s, rfl⟩
  | _ :: _, [], h => by simp [isPrefixB] at h
  | a :: p, b :: s, h => by
    simp only [isPrefixB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hp⟩ := h
    obtain ⟨t, rfl⟩ := isPrefixB_sound hp
    exact ⟨t, rfl⟩

theorem isInfixB_sound : ∀ {n h : Bytes}, isInfixB n h = true → ∃ a b, h = a ++ n ++ b
  | n, [], hh => by
    have : isPrefixB n [] = true := by simpa [isInfixB] using hh
    obtain ⟨t, ht⟩ := isPrefixB_sound this
    exact ⟨[], t, by simpa using ht⟩
  | n, b :: t, hh => by
    simp only [isInfixB, Bool.or_eq_true] at hh
    rcases hh with hp | hi
    · obtain ⟨r, hr⟩ := isPrefixB_sound hp
      exact ⟨[], r, by simpa using hr⟩
    · obtain ⟨a, r, hr⟩ := isInfixB_sound hi
      exact ⟨b :: a, r, by simp [hr]⟩

/-! ## The header block -/

/-- The HTTP header-block terminator, `CRLF CRLF`. -/
def crlf2 : Bytes := [13, 10, 13, 10]

/-- **The upgrade parser.** Split a received byte stream at the FIRST `CRLF CRLF`:
`some (hd, rest)` where `hd` is the header block INCLUDING its terminator and `rest`
is every byte after it — the frame stream. `none` means the header block has not
arrived yet (the caller reads more), never "give up and drop what you have".

A stream shorter than four bytes cannot contain the terminator, so the short cases
are `none` by construction rather than by a length guard. -/
def splitHead? : Bytes → Option (Bytes × Bytes)
  | a :: b :: c :: d :: rest =>
      if a == 13 && b == 10 && c == 13 && d == 10 then
        some (crlf2, rest)
      else
        (splitHead? (b :: c :: d :: rest)).map (fun hr => (a :: hr.1, hr.2))
  | _ => none

/-- **NO BYTE IS LOST AND NONE IS INVENTED.** Whenever the upgrade parser accepts,
the header block it consumed followed by the residue it hands on is *exactly* the
stream that arrived. This is the property the hand-written `drainUpgrade` did not
have — it returned the accumulator and the caller dropped everything past the
terminator, so a read that carried the header block plus the first frame bytes lost
those frame bytes. -/
theorem upgrade_no_loss : ∀ {s hd rest : Bytes},
    splitHead? s = some (hd, rest) → s = hd ++ rest := by
  intro s
  fun_induction splitHead? s with
  | case1 a b c d rest hterm =>
    intro hd r h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Bool.and_eq_true, beq_iff_eq] at hterm
    obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩ := hterm
    rfl
  | case2 a b c d rest hterm ih =>
    intro hd r h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨hd', r'⟩, hsub, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have := ih hsub
    simp [this]
  | case3 s _ => intro hd r h; simp at h

/-- **The header block is terminated.** Whatever the parser returns as the header
block ends with `CRLF CRLF` — it never reports a partial head. -/
theorem upgrade_head_terminated : ∀ {s hd rest : Bytes},
    splitHead? s = some (hd, rest) → ∃ p, hd = p ++ crlf2 := by
  intro s
  fun_induction splitHead? s with
  | case1 a b c d rest hterm =>
    intro hd r h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [h.1]⟩
  | case2 a b c d rest hterm ih =>
    intro hd r h
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨hd', r'⟩, hsub, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨p, hp⟩ := ih hsub
    exact ⟨a :: p, by simp [hp]⟩
  | case3 s _ => intro hd r h; simp at h

/-- **The residue IS the frame stream.** Compose the upgrade with the proven codec:
if the bytes after the header block begin with an encoded frame, the relay reads back
exactly that frame and exactly the untouched tail — the upgrade crossing is
frame-transparent. This is the statement the live relay's read path now rests on, and
it is the one the old `drainUpgrade` falsified whenever a read straddled the boundary. -/
theorem upgrade_residue_is_frame_stream {s hd rest tail : Bytes} {f : Frame}
    (hsplit : splitHead? s = some (hd, rest))
    (hrest : rest = encodeFrame f ++ tail)
    (hcap : f.payload.length ≤ maxFrameSize)
    (hnamed : ∀ b, f.ftype ≠ FrameType.unknown b) :
    s = hd ++ encodeFrame f ++ tail ∧ decodeFrame rest = some (f, tail) := by
  constructor
  · rw [upgrade_no_loss hsplit, hrest, List.append_assoc]
  · rw [hrest]; exact derp_frame_roundtrip_named f tail hcap hnamed

/-! ## The relay's reply -/

/-- The header a client sets to say "do not send me an HTTP response; send the
`ServerKey` frame immediately". drorb's own client (`DerpRelayLive.upgradeRequest`)
sets it; a stock `tailscale` client does not, and blocks reading an HTTP response. -/
def fastStartTag : Bytes := strBytes "Derp-Fast-Start"

/-- The `101 Switching Protocols` head a non-fast-start client requires before the
first frame. -/
def resp101 : Bytes :=
  strBytes "HTTP/1.1 101 Switching Protocols\r\nUpgrade: DERP\r\nConnection: Upgrade\r\n\r\n"

/-- Did the upgrade request ask for fast start? -/
def hasFastStart (hd : Bytes) : Bool := isInfixB fastStartTag hd

/-- **The relay's upgrade step.** From the received stream: the bytes to send back
(none at all for a fast-start client) and the residual frame stream. -/
def serveUpgrade (s : Bytes) : Option (Bytes × Bytes) :=
  (splitHead? s).map (fun hr => (if hasFastStart hr.1 then [] else resp101, hr.2))

/-- The upgrade step never consumes a frame byte either: its residue is the parser's
residue, and head ++ residue is the received stream. -/
theorem serveUpgrade_no_loss {s out rest : Bytes} (h : serveUpgrade s = some (out, rest)) :
    ∃ hd, s = hd ++ rest ∧ splitHead? s = some (hd, rest) := by
  simp only [serveUpgrade, Option.map_eq_some_iff] at h
  obtain ⟨⟨hd, r⟩, hsplit, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  exact ⟨hd, upgrade_no_loss hsplit, hsplit⟩

/-- **A fast-start client gets NO HTTP bytes.** The first byte drorb's own client
sees after its request is the `ServerKey` frame, exactly as before this layer existed —
so adding stock-client support cannot break the fast-start path. -/
theorem serveUpgrade_faststart_silent {s hd rest : Bytes}
    (hsplit : splitHead? s = some (hd, rest)) (hfs : hasFastStart hd = true) :
    serveUpgrade s = some ([], rest) := by
  simp [serveUpgrade, hsplit, hfs]

/-- **A stock client gets the 101.** No `Derp-Fast-Start` header ⇒ the relay emits
exactly `resp101` before any frame — the response `derphttp.Client` blocks on and
checks for `StatusCode == 101`. -/
theorem serveUpgrade_stock_101 {s hd rest : Bytes}
    (hsplit : splitHead? s = some (hd, rest)) (hfs : hasFastStart hd = false) :
    serveUpgrade s = some (resp101, rest) := by
  simp [serveUpgrade, hsplit, hfs]

/-- **Fast start is decided by the request, and only by the request** — the residue is
the same frame stream either way, so the two client kinds differ in the reply bytes
alone. -/
theorem serveUpgrade_residue_independent {s hd rest : Bytes}
    (hsplit : splitHead? s = some (hd, rest)) :
    ∃ out, serveUpgrade s = some (out, rest) :=
  ⟨if hasFastStart hd then [] else resp101, by simp [serveUpgrade, hsplit]⟩

/-! ## Evaluation — the layer on concrete wire bytes (non-vacuous) -/

-- A stock tailscale upgrade request, with the first frame bytes PIPELINED behind it
-- (the case the old hand-written drain dropped): the head is returned terminated and
-- the frame bytes come back untouched.
#guard splitHead? (strBytes "GET /derp HTTP/1.1\r\nHost: h\r\nUpgrade: DERP\r\nConnection: Upgrade\r\n\r\n"
                     ++ [0x01, 0x00, 0x00, 0x00, 0x02, 0xAA, 0xBB])
     = some (strBytes "GET /derp HTTP/1.1\r\nHost: h\r\nUpgrade: DERP\r\nConnection: Upgrade\r\n\r\n",
             [0x01, 0x00, 0x00, 0x00, 0x02, 0xAA, 0xBB])

-- An incomplete header block: keep reading, do not guess.
#guard splitHead? (strBytes "GET /derp HTTP/1.1\r\nUpgrade: DERP\r\n") = none

-- The stock client is answered with the 101; the fast-start client with nothing.
#guard (serveUpgrade (strBytes "GET /derp HTTP/1.1\r\nUpgrade: DERP\r\n\r\n")).map (·.1) = some resp101
#guard (serveUpgrade (strBytes "GET /derp HTTP/1.1\r\nDerp-Fast-Start: 1\r\n\r\n")).map (·.1) = some []

-- The reply really is a 101 whose Upgrade token is DERP.
#guard resp101.take 12 = strBytes "HTTP/1.1 101"
#guard isInfixB (strBytes "Upgrade: DERP") resp101 = true

end Derp.Upgrade
