/-
Proxy.UnixUpstream — Unix-domain-socket upstreams for the reverse proxy dial path.

A reverse proxy dials an upstream at a *target*. A target is exactly one of two
disjoint kinds:

  * a TCP peer  — an IP/host authority plus a port, and
  * a Unix-domain socket — a filesystem path used as a socket identity.

Configuration names an upstream with a single opaque address token. A `unix:`
scheme marker selects a Unix-domain socket whose path is the remainder of the
token, taken VERBATIM. Everything else is a TCP peer parsed as `host:port`
(an optional `tcp:` marker is accepted and stripped).

Two safety facts are the point of this file:

  * a `unix:` token always dials a Unix socket and NEVER a TCP address — an
    attacker cannot smuggle a network host through the socket path
    (`unix_upstream_target`);
  * the dialed socket path is a verbatim tail of the config token — the parser
    prepends no base directory and collapses no `..`, so the path is a socket
    IDENTITY, never a filesystem path resolved against a document root. With no
    root to resolve against, there is nothing to traverse out of
    (`unix_path_no_escape`).

A third structural fact records that the two kinds are mutually exclusive and
exhaustive — a dial target is unix XOR tcp (`unix_vs_tcp_disjoint`).

Everything here is a pure total function over an explicit list of characters;
the parse runs once per upstream, never per byte.
-/

namespace Proxy.UnixUpstream

/-- A resolved dial target: WHERE the reverse proxy opens the upstream
connection. Exactly two disjoint constructors. -/
inductive DialTarget where
  /-- A TCP peer: an authority (host / IP as characters) and a port. -/
  | tcp (host : List Char) (port : Nat)
  /-- A Unix-domain socket at an opaque filesystem path. -/
  | unix (path : List Char)
deriving DecidableEq, Repr

namespace DialTarget

/-- Is this target a Unix-domain socket? -/
def isUnix : DialTarget → Bool
  | unix _  => true
  | tcp _ _ => false

/-- Is this target a TCP peer? -/
def isTcp : DialTarget → Bool
  | tcp _ _ => true
  | unix _  => false

/-- The dialed socket path of a unix target (`none` for a TCP peer). -/
def unixPath? : DialTarget → Option (List Char)
  | unix p  => some p
  | tcp _ _ => none

end DialTarget

/-- The `unix:` scheme marker, as it appears verbatim in a config address. -/
def unixScheme : List Char := "unix:".toList

/-- The optional `tcp:` scheme marker. -/
def tcpScheme : List Char := "tcp:".toList

/-- Strip a single RFC-3986 empty-authority `//`, PRESERVING an absolute path's
leading slash. `"//" ++ p ↦ p`, `"///" ++ p ↦ "/" ++ p`, `"/" ++ p ↦ "/" ++ p`.
This is the only structural editing the unix branch performs; it never joins the
path to a base directory and never removes interior segments. -/
def stripEmptyAuthority : List Char → List Char
  | '/' :: '/' :: rest => rest
  | rest               => rest

/-- Value of a run of decimal digits (garbage-in / garbage-out on non-digits;
only ever fed the port segment). -/
def natOfDigits (ds : List Char) : Nat :=
  ds.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

/-- Split a `host:port` authority on the first colon; missing port ↦ 0. -/
def splitPort (s : List Char) : List Char × Nat :=
  let (host, rest) := s.span (fun c => c != ':')
  match rest with
  | ':' :: ds => (host, natOfDigits ds)
  | _         => (host, 0)

/-- Resolve a raw config upstream address into a dial target. A leading
`unix:` marker selects a Unix-domain socket whose path is the remainder taken
verbatim (after an optional empty-authority `//`); anything else is a TCP peer. -/
def resolve (raw : List Char) : DialTarget :=
  if unixScheme.isPrefixOf raw then
    .unix (stripEmptyAuthority (raw.drop unixScheme.length))
  else
    let body := if tcpScheme.isPrefixOf raw then raw.drop tcpScheme.length else raw
    let (host, port) := splitPort body
    .tcp host port

/-- An upstream as it appears in reverse-proxy configuration. Balancer metadata
(weight, tier, health) lives in `Proxy.Backend`; for dialing only the raw
address token is relevant. -/
structure Upstream where
  address : List Char
deriving DecidableEq, Repr

/-- The dial target a configured upstream resolves to. -/
def Upstream.dial (u : Upstream) : DialTarget := resolve u.address

/-! ### Supporting lemmas -/

/-- A list is a prefix of itself followed by anything. -/
theorem isPrefixOf_append (pre s : List Char) :
    List.isPrefixOf pre (pre ++ s) = true := by
  induction pre with
  | nil => simp [List.isPrefixOf]
  | cons a l ih => simp [List.isPrefixOf, ih]

/-- The empty-authority strip only ever DROPS a leading `//`; its output is
always a suffix of its input. No character is fabricated. -/
theorem stripEmptyAuthority_suffix (xs : List Char) :
    stripEmptyAuthority xs <:+ xs := by
  unfold stripEmptyAuthority
  split
  · exact (List.suffix_cons _ _).trans (List.suffix_cons _ _)
  · exact List.suffix_refl _

/-! ### Headline theorems -/

/-- **A `unix:` config upstream dials a Unix socket, never a TCP address.**
For every path, the upstream whose config address is `unix:` ++ path resolves to
a unix target and its TCP classifier is false — a socket path can never be
reinterpreted as a network host. -/
theorem unix_upstream_target (path : List Char) :
    (Upstream.dial ⟨unixScheme ++ path⟩).isUnix = true ∧
    (Upstream.dial ⟨unixScheme ++ path⟩).isTcp = false := by
  have hp : unixScheme.isPrefixOf (unixScheme ++ path) = true := isPrefixOf_append _ _
  unfold Upstream.dial resolve
  simp [hp, DialTarget.isUnix, DialTarget.isTcp]

/-- **The dialed socket path is a verbatim tail of the config token.** For any
config address carrying the `unix:` scheme, the resolved path is a suffix of the
raw address: every character comes from the config, in order, unchanged. The
parser prepends no base directory and collapses no `..`, so the path is used as
an opaque socket identity — with no document root to resolve against there is
nothing to traverse out of, and no host can be injected. -/
theorem unix_path_no_escape (raw : List Char)
    (h : unixScheme.isPrefixOf raw = true) :
    ∃ p, resolve raw = .unix p ∧ p <:+ raw := by
  refine ⟨stripEmptyAuthority (raw.drop unixScheme.length), ?_, ?_⟩
  · unfold resolve; simp [h]
  · have hd : raw.drop unixScheme.length <:+ raw :=
      ⟨raw.take unixScheme.length, List.take_append_drop _ _⟩
    exact (stripEmptyAuthority_suffix _).trans hd

/-- **A dial target is unix XOR tcp.** The two kinds are mutually exclusive and
exhaustive: exactly one classifier fires. There is no target that is both, and
none that is neither. -/
theorem unix_vs_tcp_disjoint (t : DialTarget) :
    (t.isUnix = true ∧ t.isTcp = false) ∨ (t.isUnix = false ∧ t.isTcp = true) := by
  cases t <;> simp [DialTarget.isUnix, DialTarget.isTcp]

/-! ### Non-vacuity witnesses

These `example`s exhibit both branches concretely and demonstrate the verbatim
property on a traversal-shaped path. They are not load-bearing; the headline
theorems above are the claims. -/

/-- A traversal-shaped path is carried through VERBATIM — the model does not
normalize or collapse `..`, because the path is a socket identity. -/
example :
    resolve "unix:/srv/../app.sock".toList = .unix "/srv/../app.sock".toList := by
  decide

/-- The `unix://` empty-authority form yields the same absolute path. -/
example :
    resolve "unix:///run/app.sock".toList = .unix "/run/app.sock".toList := by
  decide

/-- A non-`unix:` address reaches the TCP disjunct with a real host and port. -/
example :
    resolve "tcp:127.0.0.1:8080".toList = .tcp "127.0.0.1".toList 8080 := by
  decide

/-- Both classifiers are realized: a concrete unix target and a concrete tcp
target, so `unix_vs_tcp_disjoint` is non-vacuous in both disjuncts. -/
example : (DialTarget.unix "/x".toList).isUnix = true
    ∧ (DialTarget.tcp "h".toList 1).isTcp = true := by decide

end Proxy.UnixUpstream
