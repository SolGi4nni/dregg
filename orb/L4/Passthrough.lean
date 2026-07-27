import TlsHandshake

/-!
# L4.Passthrough — TLS-passthrough SNI routing (layer-4, blind relay)

A TLS-passthrough listener never terminates TLS. It *peeks* the very first
client bytes — the plaintext TLS `ClientHello` that precedes every handshake —
reads the `server_name` (SNI) extension out of it, picks a backend from an
SNI-keyed routing table, dials it, and from then on moves the encrypted stream
verbatim in both directions. The proxy never holds a key, never decrypts a
record, never rewrites a byte: the only thing it ever inspects is the one
unencrypted field the protocol hands it in the clear (RFC 6066 §3 / RFC 8446
§4.2 `server_name`; the record framing is RFC 8446 §5.1, the handshake framing
§4, the ClientHello §4.1.2).

Three things are proven here, over the *shipped* ClientHello parser
(`TlsHandshake.parseClientHello` / `TlsHandshake.parseSni`) — nothing about the
wire format is re-derived:

* **`sni_peek_correct`** — the peek is faithful: for any host name placed in a
  well-formed `server_name` extension, the SNI the shipped parser extracts is
  exactly that host name, byte for byte. The peek cannot invent, truncate, or
  swap a name.

* **`passthrough_routes_by_sni`** — a connection's upstream is a pure function
  of the peeked SNI: `selectBySni table (peekSni clientHello)`. It is fixed the
  moment the ClientHello is seen and never moves as the encrypted stream flows —
  the router reads the SNI and *only* the SNI, so routing happens without
  decrypting anything.

* **`passthrough_blind`** — the relay is verbatim: the bytes forwarded upstream
  are exactly the raw client stream (the ClientHello followed by every later
  chunk, in order), and the bytes returned to the client are exactly the raw
  upstream stream. Nothing is stripped, transformed, reordered, or synthesised —
  a proxy that decrypted or rewrote a record would break this equation.
-/

namespace L4.Passthrough

/-- A byte string. Same representation the TLS layer uses (`Tls.Bytes`). -/
abbrev Bytes := List UInt8
/-- A host name, as raw label bytes (the `server_name` `HostName` opaque). -/
abbrev Host := Bytes

/-! ## The SNI peek — reusing the shipped ClientHello parser

`peekSni` is the whole of the proxy's read side: it runs the verified
`ClientHello` parser and projects the one field it is allowed to see. No TLS
state is created, no record is decrypted; the parser is `Option`-valued and
total, so a malformed or non-handshake first flight simply yields `none`. -/

/-- Peek the SNI host name out of a raw first flight. Runs the shipped
`TlsHandshake.parseClientHello` and returns its `server_name`, if any. -/
def peekSni (raw : Bytes) : Option Host :=
  (TlsHandshake.parseClientHello raw).bind (·.sni)

/-! ## SNI codec faithfulness

We show the peek recovers exactly what the wire carried by encoding a
`server_name` extension body around a host and running the shipped
`TlsHandshake.parseSni` on it. The encoding is the RFC 6066 §3 `ServerNameList`
shape: `list_length(2) ‖ name_type(1)=host_name(0) ‖ name_length(2) ‖ name`. -/

/-- Big-endian `uint16`. -/
def enc16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- A well-formed single-entry `server_name` extension body carrying `host`
(RFC 6066 §3): the `host_name(0)` `ServerName` inside a `ServerNameList`. -/
def serverNameExt (host : Host) : Bytes :=
  enc16 (3 + host.length) ++ [0x00] ++ enc16 host.length ++ host

/-- `UInt8.ofNat` round-trips through `.toNat` below 256. -/
theorem toNat_ofNat_lt {n : Nat} (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- **SNI peek faithfulness.** The SNI the shipped parser extracts from a
well-formed `server_name` extension carrying `host` is exactly `host` — for
every host name (DNS names are ≤ 253 bytes, well inside the `< 256` bound; the
general `uint16` length is the obvious extension). The peek cannot drop, pad, or
substitute the name; a parser that returned a different span would fail this. -/
theorem sni_peek_correct (host : Host) (h : host.length < 256) :
    TlsHandshake.parseSni (serverNameExt host) = some host := by
  have hlo : (UInt8.ofNat (host.length % 256)).toNat = host.length := by
    rw [Nat.mod_eq_of_lt h]; exact toNat_ofNat_lt h
  have hhi : (UInt8.ofNat (host.length / 256)).toNat = 0 := by
    have : host.length / 256 = 0 := Nat.div_eq_of_lt h
    rw [this]; rfl
  have hnlen :
      (UInt8.ofNat (host.length / 256)).toNat * 256
        + (UInt8.ofNat (host.length % 256)).toNat = host.length := by
    rw [hhi, hlo]; omega
  simp only [serverNameExt, enc16, TlsHandshake.parseSni, TlsHandshake.rd16,
    List.cons_append, List.nil_append, TlsHandshake.takeN]
  rw [hnlen]
  simp [Nat.lt_irrefl, List.take_length, List.drop_length]

/-! ## The SNI routing table

The table is SNI-keyed: an ordered list of `(pattern, upstream)` routes with a
default fallback. A pattern matches by exact host or by a leading `*.` wildcard
(RFC 6125 §6.4.3 left-most label), matching the reference L4 SNI router. When no
SNI is present (a non-TLS or extension-less first flight) or no route matches,
the fallback is used. -/

/-- An upstream target: address bytes and a port. -/
structure Upstream where
  host : Bytes
  port : Nat
deriving DecidableEq, Repr

/-- One SNI route: a host `pattern` and the `target` to dial on a match. -/
structure Route where
  /-- Exact host bytes, or `*.suffix` for a left-most-label wildcard. -/
  pattern : Host
  /-- The upstream to dial when `pattern` matches the peeked SNI. -/
  target  : Upstream
deriving Repr

/-- An SNI-passthrough listener's routing table. -/
structure Table where
  /-- Ordered SNI routes; first match wins. -/
  routes   : List Route
  /-- Default upstream when no route matches (or no SNI is offered). -/
  fallback : Option Upstream
deriving Repr

/-- Does `host` end with `suffix`? -/
def endsWith (suffix host : Host) : Bool := suffix.reverse.isPrefixOf host.reverse

/-- Does an SNI `pattern` match a peeked `host`? Exact match, or a `*.`
wildcard whose suffix (the bytes after `*.`) is a suffix of `host`. -/
def matchHost (pattern host : Host) : Bool :=
  (pattern == host) ||
    (match pattern with
     | 0x2a :: 0x2e :: suffix => endsWith suffix host
     | _ => false)

/-- **Select an upstream from a peeked SNI.** First matching route wins; absent
an SNI, or with no match, the fallback is used. This is the *entire* dependence
of routing on the connection — a pure function of the peeked SNI. -/
def selectBySni (t : Table) : Option Host → Option Upstream
  | none   => t.fallback
  | some h =>
    match t.routes.find? (fun r => matchHost r.pattern h) with
    | some r => some r.target
    | none   => t.fallback

/-- Route a connection: peek the ClientHello SNI, then select. -/
def routeConn (t : Table) (raw : Bytes) : Option Upstream :=
  selectBySni t (peekSni raw)

/-! ## The blind relay machine

A passthrough connection: the chosen upstream and the peeked SNI are fixed at
accept (from the ClientHello); afterwards each client chunk is appended verbatim
to the upstream-bound stream and each upstream chunk verbatim to the
client-bound stream. The ClientHello itself is part of the upstream stream — it
is forwarded, not consumed. -/

/-- A relay event: a chunk of client bytes, or a chunk of upstream bytes. -/
inductive Ev where
  /-- Encrypted client bytes to forward upstream, verbatim. -/
  | clientData (d : Bytes)
  /-- Encrypted upstream bytes to forward to the client, verbatim. -/
  | upstreamData (d : Bytes)
deriving Repr

/-- A passthrough connection's state. -/
structure Conn where
  /-- The upstream chosen from the peeked SNI (fixed at accept). -/
  target   : Option Upstream
  /-- Bytes forwarded upstream so far (starts with the ClientHello). -/
  upSent   : Bytes
  /-- Bytes forwarded to the client so far. -/
  downSent : Bytes
  /-- The SNI peeked from the ClientHello (evidence of what was routed on). -/
  peeked   : Option Host
deriving Repr

/-- Accept: peek + route off the ClientHello `raw`, and seed the upstream
stream with the ClientHello itself (it is relayed, never swallowed). -/
def start (t : Table) (raw : Bytes) : Conn :=
  { target := routeConn t raw, upSent := raw, downSent := [], peeked := peekSni raw }

/-- One relay step: append the chunk to its direction's stream, verbatim.
Neither the routing decision nor the peeked SNI is ever touched again. -/
def step (c : Conn) : Ev → Conn
  | .clientData d   => { c with upSent := c.upSent ++ d }
  | .upstreamData d => { c with downSent := c.downSent ++ d }

/-- Run a whole event trace against a freshly accepted connection. -/
def run (t : Table) (raw : Bytes) (evs : List Ev) : Conn :=
  evs.foldl step (start t raw)

/-- The client bytes a trace carries, in order (the upstream-bound payload after
the ClientHello). -/
def clientPayload : List Ev → Bytes
  | [] => []
  | .clientData d :: r => d ++ clientPayload r
  | _ :: r => clientPayload r

/-- The upstream bytes a trace carries, in order (the client-bound payload). -/
def upstreamPayload : List Ev → Bytes
  | [] => []
  | .upstreamData d :: r => d ++ upstreamPayload r
  | _ :: r => upstreamPayload r

/-! ## Routing is by SNI alone -/

/-- A relay step never disturbs the routing decision. -/
theorem step_target (c : Conn) (e : Ev) : (step c e).target = c.target := by
  cases e <;> rfl

/-- A relay step never disturbs the recorded SNI. -/
theorem step_peeked (c : Conn) (e : Ev) : (step c e).peeked = c.peeked := by
  cases e <;> rfl

/-- Folding the relay from any state never disturbs the routing decision. -/
theorem foldl_target (evs : List Ev) (s : Conn) :
    (evs.foldl step s).target = s.target := by
  induction evs generalizing s with
  | nil => rfl
  | cons e r ih => rw [List.foldl_cons, ih, step_target]

/-- The chosen upstream is invariant across a whole trace. -/
theorem run_target (t : Table) (raw : Bytes) (evs : List Ev) :
    (run t raw evs).target = (start t raw).target := by
  rw [run, foldl_target]

/-- **Routing is by SNI, without decrypting.** The upstream a connection uses is
exactly `selectBySni table (peekSni clientHello)` — a pure function of the SNI
peeked from the ClientHello, fixed at accept and unchanged as the encrypted
stream flows. The relay bytes (`evs`) never enter the decision: no upstream move
can come from anything but the one plaintext field, so the proxy routes without
ever decrypting a record. -/
theorem passthrough_routes_by_sni (t : Table) (raw : Bytes) (evs : List Ev) :
    (run t raw evs).target = selectBySni t (peekSni raw) := by
  rw [run_target]; rfl

/-! ## The relay is blind (verbatim) -/

/-- Folding the relay from any state appends the client payload verbatim. -/
theorem foldl_upSent (evs : List Ev) (s : Conn) :
    (evs.foldl step s).upSent = s.upSent ++ clientPayload evs := by
  induction evs generalizing s with
  | nil => simp [clientPayload]
  | cons e r ih =>
    cases e with
    | clientData d =>
      simp [List.foldl, step, ih, clientPayload, List.append_assoc]
    | upstreamData d =>
      simp [List.foldl, step, ih, clientPayload]

/-- Folding the relay from any state appends the upstream payload verbatim. -/
theorem foldl_downSent (evs : List Ev) (s : Conn) :
    (evs.foldl step s).downSent = s.downSent ++ upstreamPayload evs := by
  induction evs generalizing s with
  | nil => simp [upstreamPayload]
  | cons e r ih =>
    cases e with
    | clientData d =>
      simp [List.foldl, step, ih, upstreamPayload]
    | upstreamData d =>
      simp [List.foldl, step, ih, upstreamPayload, List.append_assoc]

/-- **The passthrough is blind.** The bytes relayed upstream are exactly the raw
client stream — the ClientHello followed by every later client chunk, in order,
byte for byte — and the bytes relayed to the client are exactly the raw upstream
stream. Nothing is decrypted, stripped, rewritten, reordered, or invented: a
proxy that touched a record's contents would change one of these two streams. -/
theorem passthrough_blind (t : Table) (raw : Bytes) (evs : List Ev) :
    (run t raw evs).upSent = raw ++ clientPayload evs
      ∧ (run t raw evs).downSent = upstreamPayload evs := by
  refine ⟨?_, ?_⟩
  · show (evs.foldl step (start t raw)).upSent = _
    rw [foldl_upSent]; rfl
  · show (evs.foldl step (start t raw)).downSent = _
    rw [foldl_downSent]; simp [start]

end L4.Passthrough
