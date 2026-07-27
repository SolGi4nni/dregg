import Dns.Wire
import Proto.RequestSerialize

/-!
# DNS-over-HTTPS (RFC 8484) — the encapsulation, proven faithful

DoH carries a DNS message inside an HTTP request/response. RFC 8484 §4.1 gives
two forms:

* **POST** — `POST /dns-query`, `Content-Type: application/dns-message`, the
  request *body* is the raw DNS wire message (RFC 1035 §4.1), and the response
  body is the raw DNS wire response.
* **GET** — `GET /dns-query?dns=<v>`, where `<v>` is the **base64url** encoding
  of the DNS wire message with padding removed (RFC 8484 §6, RFC 4648 §5).

Nothing here re-implements the DNS codec: the payload is exactly the bytes the
already-proven `Dns.parseMsg` / `Dns.encodeMsg` accept. What this module adds is
the HTTP *envelope* and the proof that the envelope is transparent — the DNS
message wrapped into a DoH request is recovered byte-for-byte by unwrapping, so
composing DoH with the DNS codec parses the same query/response.

## What is proven

* `B64Url.decode_encode` — base64url is a left inverse of itself on any byte
  string (the RFC 4648 §5 alphabet, padding-free per RFC 8484 §6).
* `doh_wrap_unwrap` — **the headline.** For every DNS message `msg`,
  `unwrapPost (wrapPost msg) = msg` *and* `unwrapGet (wrapGet msg) = some msg`:
  the DNS bytes survive the HTTP envelope unchanged, both POST body and GET
  base64url.
* `doh_post_preserves_dns` / `doh_get_preserves_dns` — composed with the DNS
  codec: the unwrapped bytes parse to exactly the same `Dns.Msg`.
* `httpGet_roundtrip` — the GET form is a genuine, wire-faithful HTTP request:
  the client's own `Proto.RequestSerialize` serializes and parses it back
  unchanged (the target carries no `SP`/`CR`, so `WF` holds).
* `dohGetExample_*` — non-vacuity on a real `example.com IN A` query.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`. Strictly beyond
the reference DNS client (plain UDP/TCP only — no DoH).
-/

namespace Dns

/-! ## base64url (RFC 4648 §5), padding-free (RFC 8484 §6)

The codec is built in two layers so the round-trip is an easy induction:

1. **sextet layer** (`encN`/`decN`) — pure `Nat` arithmetic turning bytes
   (`< 256`) into six-bit groups (`< 64`) three-at-a-time, `4` sextets per `3`
   bytes, with `2`- and `3`-sextet tails for the `1`- and `2`-byte remainders
   (no padding octets are emitted, per RFC 8484 §6);
2. **alphabet layer** (`enc1`/`dec1`) — the URL-safe alphabet `A–Z a–z 0–9 - _`.
-/

namespace B64Url

/-- Bytes (`< 256`) → six-bit groups (`< 64`), `4` sextets per `3` input bytes.
Padding-free: a `1`-byte tail yields `2` sextets, a `2`-byte tail yields `3`. -/
def encN : List Nat → List Nat
  | [] => []
  | [a] => [a / 4, (a % 4) * 16]
  | [a, b] => [a / 4, (a % 4) * 16 + b / 16, (b % 16) * 4]
  | a :: b :: c :: rest =>
      a / 4 :: ((a % 4) * 16 + b / 16) :: ((b % 16) * 4 + c / 64) :: (c % 64) :: encN rest

/-- Six-bit groups → bytes, inverting `encN`. A lone leftover sextet (a
`length % 4 = 1` stream `encN` never produces) contributes nothing. -/
def decN : List Nat → List Nat
  | [] => []
  | [_] => []
  | [s0, s1] => [s0 * 4 + s1 / 16]
  | [s0, s1, s2] => [s0 * 4 + s1 / 16, (s1 % 16) * 16 + s2 / 4]
  | s0 :: s1 :: s2 :: s3 :: rest =>
      (s0 * 4 + s1 / 16) :: ((s1 % 16) * 16 + s2 / 4) :: ((s2 % 4) * 64 + s3) :: decN rest

/-- **Sextet round-trip.** Bytes recombine exactly from the groups `encN` split
them into. -/
theorem decN_encN : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → decN (encN bs) = bs := by
  intro bs
  induction bs using encN.induct with
  | case1 => intro _; rfl
  | case2 a => intro h; have ha := h a (by simp); simp only [encN, decN]; congr 1; omega
  | case3 a b =>
      intro h
      have hb := h b (by simp)
      simp only [encN, decN]
      refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
      exact List.cons_eq_cons.mpr ⟨by omega, rfl⟩
  | case4 a b c rest ih =>
      intro h
      have hb := h b (by simp)
      have hc := h c (by simp)
      simp only [encN, decN]
      refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
      refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
      refine List.cons_eq_cons.mpr ⟨by omega, ?_⟩
      exact ih (fun x hx => h x (by simp [hx]))

/-- Every group `encN` emits is a genuine six-bit value. -/
theorem encN_lt64 : ∀ (bs : List Nat), (∀ b ∈ bs, b < 256) → ∀ s ∈ encN bs, s < 64 := by
  intro bs
  induction bs using encN.induct with
  | case1 => intro _ s hs; simp [encN] at hs
  | case2 a =>
      intro h s hs
      have ha := h a (by simp)
      simp only [encN, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
      rcases hs with h1 | h1 <;> subst h1 <;> omega
  | case3 a b =>
      intro h s hs
      have ha := h a (by simp); have hb := h b (by simp)
      simp only [encN, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
      rcases hs with h1 | h1 | h1 <;> subst h1 <;> omega
  | case4 a b c rest ih =>
      intro h s hs
      have ha := h a (by simp); have hb := h b (by simp); have hc := h c (by simp)
      simp only [encN, List.mem_cons] at hs
      rcases hs with h1 | h1 | h1 | h1 | h1
      · subst h1; omega
      · subst h1; omega
      · subst h1; omega
      · subst h1; omega
      · exact ih (fun x hx => h x (by simp [hx])) s h1

/-- A six-bit value (`< 64`) → its URL-safe alphabet octet (RFC 4648 §5). -/
def enc1 (n : Nat) : UInt8 :=
  if n < 26 then UInt8.ofNat (65 + n)          -- 'A'..'Z'
  else if n < 52 then UInt8.ofNat (97 + (n - 26)) -- 'a'..'z'
  else if n < 62 then UInt8.ofNat (48 + (n - 52)) -- '0'..'9'
  else if n = 62 then 45                          -- '-'
  else 95                                          -- '_'

/-- An alphabet octet → its six-bit value; `none` for a non-alphabet octet. -/
def dec1 (c : UInt8) : Option Nat :=
  let v := c.toNat
  if 65 ≤ v ∧ v ≤ 90 then some (v - 65)
  else if 97 ≤ v ∧ v ≤ 122 then some (v - 97 + 26)
  else if 48 ≤ v ∧ v ≤ 57 then some (v - 48 + 52)
  else if v = 45 then some 62
  else if v = 95 then some 63
  else none

/-- The alphabet is invertible on every six-bit value. -/
theorem dec1_enc1 (n : Nat) (hn : n < 64) : dec1 (enc1 n) = some n := by
  have h : ∀ m : Fin 64, dec1 (enc1 m.1) = some m.1 := by decide
  exact h ⟨n, hn⟩

/-- Decoding recovers a list of six-bit values from its alphabet encoding. -/
theorem mapM_dec1_enc1 :
    ∀ (l : List Nat), (∀ x ∈ l, x < 64) → (l.map enc1).mapM dec1 = some l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    have hx : x < 64 := h x (by simp)
    have htail : (xs.map enc1).mapM dec1 = some xs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.mapM_cons, dec1_enc1 x hx, htail]
    rfl

/-- **base64url encode** (RFC 4648 §5, padding-free per RFC 8484 §6). -/
def encode (bs : Bytes) : Bytes := (encN (bs.map (·.toNat))).map enc1

/-- **base64url decode**; `none` on any non-alphabet octet. -/
def decode (cs : Bytes) : Option Bytes :=
  (cs.mapM dec1).map (fun sext => (decN sext).map UInt8.ofNat)

/-- **The base64url round-trip.** Decoding recovers the exact bytes encoded —
`decode ∘ encode = some`, for every byte string. -/
theorem decode_encode (bs : Bytes) : decode (encode bs) = some bs := by
  have hbnd : ∀ b ∈ bs.map (·.toNat), b < 256 := by
    intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨u, _, rfl⟩ := hb
    exact Dns.u8_lt u
  have h64 : ∀ s ∈ encN (bs.map (·.toNat)), s < 64 := encN_lt64 _ hbnd
  unfold decode encode
  rw [mapM_dec1_enc1 _ h64, Option.map_some, decN_encN _ hbnd]
  simp [List.map_map, Function.comp_def, UInt8.ofNat_toNat]

end B64Url

/-! ## The DoH envelope (RFC 8484 §4.1) -/

namespace Doh

/-- The RFC 8484 endpoint path `/dns-query`, as ASCII octets. -/
def dnsQueryPath : Bytes := [47, 100, 110, 115, 45, 113, 117, 101, 114, 121]

/-- The GET query-string lead-in `?dns=` (RFC 8484 §4.1, §6), as ASCII octets. -/
def dnsParam : Bytes := [63, 100, 110, 115, 61]

/-- `POST` / `GET` methods, as ASCII octets. -/
def mPost : Bytes := [80, 79, 83, 84]
def mGet : Bytes := [71, 69, 84]

/-- A DoH request envelope: the HTTP method and target, plus the body (the raw
DNS wire message for POST; empty for GET, whose message rides in the target). -/
structure Request where
  method : Bytes
  target : Bytes
  body : Bytes
  deriving Repr, DecidableEq

/-- **POST wrap** (RFC 8484 §4.1): the DNS wire message is the request body,
sent to `/dns-query`. -/
def wrapPost (msg : Bytes) : Request :=
  { method := mPost, target := dnsQueryPath, body := msg }

/-- **POST unwrap**: the DNS wire message is exactly the request body. -/
def unwrapPost (r : Request) : Bytes := r.body

/-- **GET wrap** (RFC 8484 §4.1, §6): `/dns-query?dns=<base64url(message)>`,
no body. -/
def wrapGet (msg : Bytes) : Request :=
  { method := mGet, target := dnsQueryPath ++ dnsParam ++ B64Url.encode msg, body := [] }

/-- Strip an exact byte prefix; `none` if `p` is not a prefix of the input. -/
def stripPrefix : Bytes → Bytes → Option Bytes
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys => if x == y then stripPrefix xs ys else none

theorem stripPrefix_append (p ys : Bytes) : stripPrefix p (p ++ ys) = some ys := by
  induction p with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, stripPrefix]
    rw [if_pos (by simp)]
    exact ih

/-- **GET unwrap**: strip `/dns-query?dns=` off the target and base64url-decode
the rest back to the DNS wire message. -/
def unwrapGet (r : Request) : Option Bytes :=
  match stripPrefix (dnsQueryPath ++ dnsParam) r.target with
  | none => none
  | some v => B64Url.decode v

/-! ## Encapsulation faithfulness -/

/-- POST is transparent: the body is the message. -/
theorem doh_post_wrap_unwrap (msg : Bytes) : unwrapPost (wrapPost msg) = msg := rfl

/-- GET is transparent: base64url survives the query-string envelope. -/
theorem doh_get_wrap_unwrap (msg : Bytes) : unwrapGet (wrapGet msg) = some msg := by
  unfold unwrapGet wrapGet
  simp only
  rw [stripPrefix_append (dnsQueryPath ++ dnsParam) (B64Url.encode msg)]
  exact B64Url.decode_encode msg

/-- **The headline.** The DNS wire message drorb wraps into a DoH request is
recovered byte-for-byte by unwrapping — both the POST body and the GET
base64url form. The DNS codec is preserved across the HTTP envelope. -/
theorem doh_wrap_unwrap (msg : Bytes) :
    unwrapPost (wrapPost msg) = msg ∧ unwrapGet (wrapGet msg) = some msg :=
  ⟨doh_post_wrap_unwrap msg, doh_get_wrap_unwrap msg⟩

/-! ## Composition with the proven DNS codec

The unwrapped bytes are literally the wrapped bytes, so `Dns.parseMsg` sees the
same message it would see with no DoH envelope at all. -/

/-- POST-unwrapped bytes parse to the same `Dns.Msg`. -/
theorem doh_post_preserves_dns (msg : Bytes) :
    parseMsg (unwrapPost (wrapPost msg)) = parseMsg msg := by
  rw [doh_post_wrap_unwrap]

/-- GET-unwrapped bytes parse to the same `Dns.Msg`. -/
theorem doh_get_preserves_dns (msg : Bytes) :
    (unwrapGet (wrapGet msg)).map parseMsg = some (parseMsg msg) := by
  rw [doh_get_wrap_unwrap]; rfl

/-! ## The GET form as a genuine HTTP request

The GET envelope is rendered as a real `Proto.Request` and shown to round-trip
through the client's own request serializer — the base64url target carries no
`SP` or `CR`, so the RFC 9112 well-formedness `WF` holds. -/

/-- The DoH GET as a wire HTTP/1.1 request: `GET /dns-query?dns=… HTTP/1.1`
with a `Host` header. -/
def httpGet (host : Bytes) (msg : Bytes) : Proto.Request :=
  { method := mGet
    target := dnsQueryPath ++ dnsParam ++ B64Url.encode msg
    version := [72, 84, 84, 80, 47, 49, 46, 49]      -- "HTTP/1.1"
    headers := [([72, 111, 115, 116], host)] }        -- "Host: <host>"

/-- No six-bit alphabet octet is `SP` (32) or `CR` (13). -/
theorem enc1_no_sp_cr (n : Nat) (hn : n < 64) :
    B64Url.enc1 n ≠ 32 ∧ B64Url.enc1 n ≠ 13 := by
  have h : ∀ m : Fin 64, B64Url.enc1 m.1 ≠ 32 ∧ B64Url.enc1 m.1 ≠ 13 := by decide
  exact h ⟨n, hn⟩

/-- No base64url octet is `SP` — so a base64url target is `SP`-free. -/
theorem sp_not_mem_encode (msg : Bytes) : Proto.ResponseParse.SP ∉ B64Url.encode msg := by
  intro h
  unfold B64Url.encode at h
  rw [List.mem_map] at h
  obtain ⟨n, hn, he⟩ := h
  have hbnd : ∀ b ∈ msg.map (·.toNat), b < 256 := by
    intro b hb; rw [List.mem_map] at hb; obtain ⟨u, _, rfl⟩ := hb; exact Dns.u8_lt u
  have hlt : n < 64 := B64Url.encN_lt64 _ hbnd n hn
  exact (enc1_no_sp_cr n hlt).1 he

/-- **The GET form is a genuine, wire-faithful HTTP request.** Rendered as a
`Proto.Request` and pushed through the client's own request serializer, the DoH
GET round-trips unchanged — the base64url target is `SP`/`CR`-free, so RFC 9112
well-formedness holds (given a `CR`-free `Host` value). -/
theorem httpGet_roundtrip (host msg : Bytes)
    (hhost : Proto.ResponseParse.CR ∉ host) :
    Proto.RequestSerialize.parse (Proto.RequestSerialize.serialize (httpGet host msg))
      = some (httpGet host msg) := by
  apply Proto.RequestSerialize.parse_serialize
  unfold Proto.RequestSerialize.WF httpGet
  dsimp only
  refine ⟨by decide, ?_, by decide, ?_⟩
  · rw [List.append_assoc]
    intro h
    rcases List.mem_append.mp h with h1 | h2
    · revert h1; decide
    · rcases List.mem_append.mp h2 with h3 | h4
      · revert h3; decide
      · exact sp_not_mem_encode msg h4
  · intro kv hkv
    simp only [List.mem_singleton] at hkv
    subst hkv
    dsimp only
    exact ⟨by decide, by decide, hhost⟩

end Doh

/-! ## Non-vacuity: a real `example.com IN A` query -/

namespace Doh

/-- The DNS wire query `example.com IN A`, id `0xABCD`, RD set (flags `0x0100`).
This is a genuine RFC 1035 §4.1 message — see `dohExample_parses`. -/
def qExample : Bytes :=
  [ 0xAB, 0xCD, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
    0x00, 0x01, 0x00, 0x01 ]

/-- The query really is a well-formed DNS message: one question, `example.com`,
QTYPE `A` (1), QCLASS `IN` (1). -/
theorem dohExample_parses :
    parseMsg qExample
      = some
          { header := { id := 0xABCD, flags := 0x0100, qdCount := 1, anCount := 0,
                        nsCount := 0, arCount := 0 }
            questions := [{ qname := [[101, 120, 97, 109, 112, 108, 101], [99, 111, 109]],
                            qtype := 1, qclass := 1 }]
            answers := [], authority := [], additional := [] } := by decide

/-- **DoH POST, on the real query.** Wrapping `example.com IN A` as a POST body
and unwrapping recovers the exact query bytes. -/
theorem dohExample_post : unwrapPost (wrapPost qExample) = qExample := rfl

/-- **DoH GET, on the real query.** Wrapping the query as `?dns=base64url(…)`
and unwrapping recovers the exact query bytes — the base64url codec run on a
real DNS message. -/
theorem dohExample_get : unwrapGet (wrapGet qExample) = some qExample := by decide

/-- And the round-tripped GET bytes parse back to the same DNS query. -/
theorem dohExample_get_parses :
    (unwrapGet (wrapGet qExample)).map parseMsg = some (parseMsg qExample) :=
  doh_get_preserves_dns qExample

end Doh

end Dns
