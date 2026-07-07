import Dsl.Deployment

/-!
# Dsl.Config.Parse — a textual deployment config, parsed to a `DeploymentConfig`

The deployed serve is generated from a `Dsl.DeploymentConfig` (`Dsl.Deployment`,
`Reactor.Deploy.servePipelineOf`). Until now the running host chose among a small
set of *named* deployments (`defaultDeployment` / `altDeployment`) by a selector
byte. This file closes the last mile: an operator writes an ARBITRARY textual
config, and the host parses it into a `DeploymentConfig` the running serve then
executes — correct-by-construction, anchored by a parse-soundness theorem.

## What the config format covers

A config is four lines (whitespace-insensitive: any run of spaces / newlines
separates tokens):

```
listener <addr> <port>
pool <name> <lbPolicy>
l4 <none|tcp|udp>
tls <0rtt|no0rtt>
```

* `listener` — the accept surface (bind address + port) of the deployment's
  listener dimension (`Dsl.Cfg.ListenerCfg.addr` / `.port`);
* `pool` — the reverse-proxy upstream pool NAME the proxy route references, and
  the load-balancing policy (`Dsl.Cfg.LbPolicy`) selected over its members. This
  is the live knob: the running reverse-proxy dial runs whichever policy chain the
  config declares (`Dsl.Cfg.UpstreamCfg.dialChain`), so two configs differing only
  here reach different backends;
* `l4` — whether the listener is a layer-4 passthrough (`tcp` / `udp`) over that
  pool, or a plain HTTP listener (`none`) — the `DeploymentConfig.l4Listeners`
  projection the host binds;
* `tls` — the 0-RTT / early-data toggle of the listener's TLS profile
  (`Dsl.Cfg.TlsProfile.zeroRtt`), the `serverParamsFor` early-data verdict.

The upstream pool's backend set is the proven `Dsl.Cfg.loadedPool` (three
load-differentiated members), so a load-sensitive policy (`leastConn`) and a
key-sensitive one (`rendezvous`) demonstrably pick different backends over it.

## What it does NOT cover (vs the full declarative surface)

The routing dimension (`RouteCfg.routes` / `defaultHandler` / `routeKeyOf`) and the
middleware dimension (`MiddlewareCfg.chain : List Stage`) carry VERIFIED Lean
functions — the proven fourteen-stage byte pipeline and the real router. No textual
config can denote an arbitrary Lean function, and it should not: those are proven
code, not operator data. So `denote` layers the parsed DATA dimensions (listener
accept surface, upstream pool + LB policy, L4, TLS 0-RTT) on top of
`Reactor.Deploy.defaultDeployment`'s proven byte pipeline — exactly the shape
`altDeployment` populates by hand. A full pkl-parity grammar (arbitrary route
tables, named middleware libraries with per-route sub-chains, per-SNI cert
matrices, cipher/ALPN/mTLS surfaces) is larger; this format is the data subset that
drives the running IO-boundary behaviour.

## The parse-soundness theorem

`parseChars` / `renderChars` work on `List Char` (the kernel reduces them; `String`
operations do not), and `parse_render` proves a well-formed config round-trips:
`parseChars (renderChars pc) = some pc` for every `WF pc`. `Dsl.Config.parse` is the
`String` entry point (`parseChars ∘ String.data`), and the runtime config files are
generated as `render pc`, so the running host provably parses each to its intended
`ParsedConfig` — the correct-by-construction link. Malformed inputs return `none`
(`parse_malformed_*`).
-/

namespace Dsl.Config

open Dsl.Cfg (LbPolicy L4Mode)

/-! ## Whitespace + decimal-digit codec (kernel-reducible, on `List Char`) -/

/-- A separator character (space or newline). -/
def isWs (c : Char) : Bool := c = ' ' || c = '\n'

/-- The decimal digit character for `d < 10` (saturating at `'9'`). -/
def digitCh : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- The value of a decimal digit character, or `none` if not a digit. -/
def chDigit (c : Char) : Option Nat :=
  if c = '0' then some 0 else if c = '1' then some 1 else if c = '2' then some 2
  else if c = '3' then some 3 else if c = '4' then some 4 else if c = '5' then some 5
  else if c = '6' then some 6 else if c = '7' then some 7 else if c = '8' then some 8
  else if c = '9' then some 9 else none

theorem chDigit_digitCh (d : Nat) (h : d < 10) : chDigit (digitCh d) = some d := by
  rcases d with _|_|_|_|_|_|_|_|_|_|d <;> first | rfl | omega

/-- Every digit character (for `d < 10`) is neither a space nor a newline. -/
theorem digitCh_notWs (d : Nat) (h : d < 10) : digitCh d ≠ ' ' ∧ digitCh d ≠ '\n' := by
  rcases d with _|_|_|_|_|_|_|_|_|_|d <;> first | exact ⟨by decide, by decide⟩ | omega

/-- Render a `Nat` as MSB-first decimal characters (always at least one). -/
def renderNat (n : Nat) : List Char :=
  if n < 10 then [digitCh n]
  else renderNat (n / 10) ++ [digitCh (n % 10)]
decreasing_by omega

/-- Parse an all-digit character list left-to-right into a `Nat` (an empty list
parses to `acc`; a non-digit aborts). -/
def parseNatAux (acc : Nat) : List Char → Option Nat
  | [] => some acc
  | c :: cs => match chDigit c with
    | some d => parseNatAux (acc * 10 + d) cs
    | none => none

/-- The `Nat` parser: fold the whole digit token from zero. -/
def parseNat (cs : List Char) : Option Nat := parseNatAux 0 cs

theorem parseNatAux_snoc (xs : List Char) (v d : Nat) (c : Char)
    (hc : chDigit c = some d) : ∀ acc, parseNatAux acc xs = some v →
    parseNatAux acc (xs ++ [c]) = some (v * 10 + d) := by
  induction xs with
  | nil =>
    intro acc hxs
    simp only [parseNatAux] at hxs
    injection hxs with hv; subst hv
    simp only [List.nil_append, parseNatAux, hc]
  | cons x xs ih =>
    intro acc hxs
    simp only [parseNatAux] at hxs
    cases hx : chDigit x with
    | none => simp only [hx] at hxs; exact absurd hxs (by simp)
    | some dx =>
      simp only [hx] at hxs
      simp only [List.cons_append, parseNatAux, hx]
      exact ih _ hxs

/-- **Decimal round-trip.** Parsing the rendering of a `Nat` recovers it. -/
theorem parseNat_render (n : Nat) : parseNat (renderNat n) = some n := by
  unfold parseNat
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [renderNat]
    by_cases h : n < 10
    · simp only [h, if_true, parseNatAux, chDigit_digitCh n h]; congr 1; omega
    · simp only [h, if_false]
      have hlt : n / 10 < n := by omega
      have hmod : n % 10 < 10 := Nat.mod_lt n (by omega)
      rw [parseNatAux_snoc (renderNat (n/10)) (n/10) (n%10) (digitCh (n%10))
            (chDigit_digitCh _ hmod) 0 (ih (n/10) hlt)]
      congr 1; omega

/-- Every character of a rendered `Nat` is a (non-whitespace) digit. -/
theorem renderNat_notWs (n : Nat) : ∀ c ∈ renderNat n, c ≠ ' ' ∧ c ≠ '\n' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [renderNat]
    by_cases h : n < 10
    · simp only [h, if_true, List.mem_singleton]
      rintro c rfl; exact digitCh_notWs n h
    · simp only [h, if_false]
      have hlt : n / 10 < n := by omega
      have hmod : n % 10 < 10 := Nat.mod_lt n (by omega)
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n/10) hlt c hc
      · rw [List.mem_singleton.mp hc]; exact digitCh_notWs (n % 10) hmod

/-- A rendered `Nat` never contains a space. -/
theorem renderNat_no_sp (n : Nat) : ' ' ∉ renderNat n :=
  fun h => (renderNat_notWs n ' ' h).1 rfl

/-- A rendered `Nat` never contains a newline. -/
theorem renderNat_no_nl (n : Nat) : '\n' ∉ renderNat n :=
  fun h => (renderNat_notWs n '\n' h).2 rfl

/-! ## The single-separator splitter and its round-trip -/

/-- Split a character list on a separator, keeping empty fields. Structural, so
the kernel reduces it. -/
def splitOn1 (sep : Char) : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    let rest := splitOn1 sep cs
    if c = sep then [] :: rest
    else match rest with
      | [] => [[c]]
      | r :: rs => (c :: r) :: rs

theorem splitOn1_ne (sep : Char) (cs : List Char) : splitOn1 sep cs ≠ [] := by
  cases cs with
  | nil => simp [splitOn1]
  | cons c cs =>
    simp only [splitOn1]
    by_cases h : c = sep
    · simp [h]
    · simp only [h, if_false]; cases splitOn1 sep cs <;> simp

/-- Splitting a separator-free list yields the single field. -/
theorem splitOn1_no_sep (sep : Char) (a : List Char) (h : sep ∉ a) :
    splitOn1 sep a = [a] := by
  induction a with
  | nil => rfl
  | cons c cs ih =>
    have hc : c ≠ sep := fun e => h (by rw [e]; exact List.mem_cons_self _ _)
    have hcs : sep ∉ cs := fun e => h (List.mem_cons_of_mem _ e)
    simp only [splitOn1]; rw [if_neg hc, ih hcs]

/-- Splitting `a ++ sep :: b` (with `a` separator-free) peels off `a`. -/
theorem splitOn1_append (sep : Char) (a b : List Char) (h : sep ∉ a) :
    splitOn1 sep (a ++ sep :: b) = a :: splitOn1 sep b := by
  induction a with
  | nil => simp [splitOn1]
  | cons c cs ih =>
    have hc : c ≠ sep := fun e => h (by rw [e]; exact List.mem_cons_self _ _)
    have hcs : sep ∉ cs := fun e => h (List.mem_cons_of_mem _ e)
    simp only [List.cons_append, splitOn1, if_neg hc, ih hcs]

/-! ## Space-joined token lists (a variable-arity line codec)

The virtual-host route line carries a variable number of tokens (an optional method,
the path, optional `header`/`query` guard clauses, then the handler tail). Rather than a
fixed-arity `lineN` per shape, its line is the tokens joined by single spaces, and the
round-trip is one lemma: splitting a space-join of space-free tokens recovers the token
list. -/

/-- Join a token list with single spaces. -/
def joinSp : List (List Char) → List Char
  | []      => []
  | [t]     => t
  | t :: ts => t ++ ' ' :: joinSp ts

/-- **Join/split round-trip.** Splitting the space-join of a non-empty list of
space-free tokens recovers exactly the token list. -/
theorem joinSp_split : ∀ {toks : List (List Char)}, toks ≠ [] →
    (∀ t ∈ toks, ' ' ∉ t) → splitOn1 ' ' (joinSp toks) = toks := by
  intro toks
  induction toks with
  | nil => intro h _; exact absurd rfl h
  | cons t ts ih =>
    intro _ hmem
    have ht : ' ' ∉ t := hmem t (List.mem_cons_self _ _)
    cases ts with
    | nil => show splitOn1 ' ' t = [t]; exact splitOn1_no_sep ' ' t ht
    | cons u us =>
      have hne : (u :: us) ≠ [] := by simp
      have hmemts : ∀ x ∈ u :: us, ' ' ∉ x := fun x hx => hmem x (List.mem_cons_of_mem _ hx)
      show splitOn1 ' ' (t ++ ' ' :: joinSp (u :: us)) = t :: u :: us
      rw [splitOn1_append ' ' t _ ht, ih hne hmemts]

/-- A space-join whose head token is non-empty is itself non-empty. -/
theorem joinSp_cons_ne (t : List Char) (ts : List (List Char)) (ht : t ≠ []) :
    joinSp (t :: ts) ≠ [] := by
  cases ts with
  | nil => simpa [joinSp] using ht
  | cons u us => simp [joinSp]

/-- A space-join of newline-free tokens carries no newline (only spaces are inserted). -/
theorem joinSp_no_nl : ∀ {toks : List (List Char)}, (∀ t ∈ toks, '\n' ∉ t) →
    '\n' ∉ joinSp toks := by
  intro toks
  induction toks with
  | nil => intro _; simp [joinSp]
  | cons t ts ih =>
    intro h
    have ht : '\n' ∉ t := h t (List.mem_cons_self _ _)
    cases ts with
    | nil => simpa [joinSp] using ht
    | cons u us =>
      have hrest := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      show '\n' ∉ t ++ ' ' :: joinSp (u :: us)
      simp only [List.mem_append, List.mem_cons]
      rintro (hh | hh | hh)
      · exact ht hh
      · exact absurd hh (by decide)
      · exact hrest hh

/-! ## Field codecs: LB policy, L4 mode, TLS 0-RTT -/

/-- The token for each LB policy. -/
def lbTok : LbPolicy → List Char
  | .roundRobin        => ['r','o','u','n','d','R','o','b','i','n']
  | .leastConn         => ['l','e','a','s','t','C','o','n','n']
  | .weightedLeastConn => ['w','l','e','a','s','t','C','o','n','n']
  | .ipHash            => ['i','p','H','a','s','h']
  | .stickyCookie      => ['s','t','i','c','k','y','C','o','o','k','i','e']
  | .rendezvous        => ['r','e','n','d','e','z','v','o','u','s']

/-- Parse an LB-policy token. -/
def parseLb (t : List Char) : Option LbPolicy :=
  if t = lbTok .roundRobin then some .roundRobin
  else if t = lbTok .leastConn then some .leastConn
  else if t = lbTok .weightedLeastConn then some .weightedLeastConn
  else if t = lbTok .ipHash then some .ipHash
  else if t = lbTok .stickyCookie then some .stickyCookie
  else if t = lbTok .rendezvous then some .rendezvous
  else none

theorem parseLb_lbTok (p : LbPolicy) : parseLb (lbTok p) = some p := by
  cases p <;> rfl

theorem lbTok_no_ws (p : LbPolicy) : ' ' ∉ lbTok p ∧ '\n' ∉ lbTok p := by
  cases p <;> exact ⟨by decide, by decide⟩

/-- The token for an optional L4 mode. -/
def l4Tok : Option L4Mode → List Char
  | none      => ['n','o','n','e']
  | some .tcp => ['t','c','p']
  | some .udp => ['u','d','p']

/-- Parse an L4-mode token. -/
def parseL4 (t : List Char) : Option (Option L4Mode) :=
  if t = l4Tok none then some none
  else if t = l4Tok (some .tcp) then some (some .tcp)
  else if t = l4Tok (some .udp) then some (some .udp)
  else none

theorem parseL4_l4Tok (m : Option L4Mode) : parseL4 (l4Tok m) = some m := by
  rcases m with _ | m
  · rfl
  · cases m <;> rfl

theorem l4Tok_no_ws (m : Option L4Mode) : ' ' ∉ l4Tok m ∧ '\n' ∉ l4Tok m := by
  rcases m with _ | m
  · exact ⟨by decide, by decide⟩
  · cases m <;> exact ⟨by decide, by decide⟩

/-- The token for the 0-RTT toggle. -/
def zTok : Bool → List Char
  | true  => ['0','r','t','t']
  | false => ['n','o','0','r','t','t']

/-- Parse a 0-RTT toggle token. -/
def parseZ (t : List Char) : Option Bool :=
  if t = zTok true then some true
  else if t = zTok false then some false
  else none

theorem parseZ_zTok (b : Bool) : parseZ (zTok b) = some b := by cases b <;> rfl

theorem zTok_no_ws (b : Bool) : ' ' ∉ zTok b ∧ '\n' ∉ zTok b := by
  cases b <;> exact ⟨by decide, by decide⟩

/-! ## Route / handler keyword tokens

Defined up here (ahead of the handler-subset AST) because the virtual-host route
well-formedness condition references them: a vhost path token must not collide with a
handler keyword, so the whitespace grammar's optional-method disambiguation is
unambiguous. -/

def kwRoute    : List Char := ['r','o','u','t','e']
def kwProxy    : List Char := ['p','r','o','x','y']
def kwRedirect : List Char := ['r','e','d','i','r','e','c','t']
def kwRespond  : List Char := ['r','e','s','p','o','n','d']
def kwStatic   : List Char := ['s','t','a','t','i','c']
def kwHost     : List Char := ['h','o','s','t']
def kwHeader   : List Char := ['h','e','a','d','e','r']
def kwQuery    : List Char := ['q','u','e','r','y']
def kwMiddleware : List Char := ['m','i','d','d','l','e','w','a','r','e']

/-- Is `t` one of the clause/handler keywords the vhost-route grammar scans for? The
`[method] path` prefix of a route line is exactly the run of tokens before the first
such keyword, so method/path tokens must NOT be stop keywords (`NotStopKw`). -/
def isStopKw (t : List Char) : Bool :=
  (t == kwMiddleware) || (t == kwHeader) || (t == kwQuery) || (t == kwStatic) || (t == kwProxy)
    || (t == kwRedirect) || (t == kwRespond)

/-! ## The route dimension (the config-representable handler subset)

The deployed `Reactor.App.Handler` inductive carries four **data-parameterized**
(config-representable) variants — a reverse-proxy over a named pool, a redirect
(status + Location), a fixed local response (status + body), and the embedded
static-file handler. Those are exactly what a textual `route <pattern> <handler>`
line can denote. The remaining handlers (`cgi` — a Lean-run child process,
`hostGlob` — a Lean virtual-host table) carry Lean functions / opaque tables and
are NOT config-representable; they stay authored in Lean. -/

/-- A config-representable handler: the token-denotable subset of
`Reactor.App.Handler`. -/
inductive HandlerSpec where
  /-- Reverse-proxy this route to the named upstream pool. -/
  | proxy (pool : List Char)
  /-- Redirect with a `3xx` status to the given `Location`. -/
  | redirect (status : Nat) (location : List Char)
  /-- Answer locally with a fixed status + body. -/
  | respond (status : Nat) (body : List Char)
  /-- Serve the embedded static-file handler. -/
  | static
deriving DecidableEq, Repr

/-- One config route: the path pattern token as written (e.g. `/api` for an exact
match, `/static/*` for a prefix match), and the config-handler it maps to. -/
structure RouteSpec where
  /-- The path pattern token (a trailing `*` ⇒ prefix match, else exact). -/
  pathTok : List Char
  /-- The config-handler this route serves. -/
  handler : HandlerSpec
deriving DecidableEq, Repr

/-- A handler's free-text tokens carry no separator (a round-trip precondition). -/
def HandlerWF : HandlerSpec → Prop
  | .proxy pool     => ' ' ∉ pool ∧ '\n' ∉ pool
  | .redirect _ loc => ' ' ∉ loc ∧ '\n' ∉ loc
  | .respond _ body => ' ' ∉ body ∧ '\n' ∉ body
  | .static         => True

/-- A route is well-formed when its path token and its handler tokens carry no
separator. -/
def RouteWF (r : RouteSpec) : Prop :=
  (' ' ∉ r.pathTok ∧ '\n' ∉ r.pathTok) ∧ HandlerWF r.handler

/-! ## The virtual-host dimension (HOST-scoped, METHOD-guarded routes)

The route dimension above is the flat, host-agnostic `Route.Match.bestMatch` table.
The virtual-host dimension is a two-level table keyed on the request authority: an
operator writes `host <hostname>` to open a block, then `route [<method>] <path>
respond <status> <body>` lines that apply ONLY to requests whose `Host` header
selects that block. This denotes onto the deployed `Reactor.App.Handler.hostGlob`
handler — the PROVEN `RouteAdvanced.dispatch` (host selection, method matching, glob
paths, RFC 9110 §7.4 host isolation `route_host_isolation`). The block answers carry
a `(status, body)` — the config-representable subset of a vhost route (matching the
`(Nat × Bytes)` a `hostGlob` block route holds); per-vhost proxy/redirect and
header/query guards stay named follow-ons (a richer block-handler type). -/

/-- One virtual-host route: an OPTIONAL method guard (`none` ⇒ any method), a path
pattern token (a trailing `*` ⇒ prefix/glob, `/` ⇒ the host catch-all, else an exact
single-segment match), OPTIONAL `header <name>` and/or `query <name>` guard clauses
(denoted onto the PROVEN `RouteAdvanced.headerPresent` / `queryPresent` guards, which a
route already enforces via `headerRequired_blocks` / `queryRequired_blocks`), and the
WIDENED, config-representable answer it serves — reusing the flat `HandlerSpec` (proxy /
redirect / respond / static). This is the homelab multi-service case: `host jelly.home`
then `route / proxy jellypool`, `host blog.home` then `route / respond 200 BLOG`, and
`route GET /admin header X-Auth-Token respond 200 ok` (matches only with the header
present), PER HOST. -/
structure VRouteSpec where
  /-- The method guard token (`none` ⇒ any method; `some "GET"` ⇒ only `GET`). -/
  method : Option (List Char)
  /-- The path pattern token (`/` ⇒ host catch-all, trailing `*` ⇒ prefix, else exact). -/
  pathTok : List Char
  /-- The ordered per-route MIDDLEWARE chain: each `middleware <name>` clause's name
  token, run BEFORE the handler. `bearer-auth` denotes the proven `Jwt.authenticate`
  bearer gate (a rejected token ⇒ 401); an unrecognized name is a fail-closed residual
  (`Reactor.RouteMw.mwOfName`). Empty ⇒ no middleware (byte-identical to a bare route). -/
  middleware : List (List Char)
  /-- `some name` ⇒ require request header `name` to be present (a `header <name>` clause). -/
  headerGuard : Option (List Char)
  /-- `some key` ⇒ require request query key `key` to be present (a `query <key>` clause). -/
  queryGuard : Option (List Char)
  /-- The config-handler this virtual-host route serves. -/
  handler : HandlerSpec
deriving DecidableEq, Repr

/-- A vhost config item: either a `host <hostname>` block header opening a new
virtual-host block, or a `route …` line scoped to the most recently opened block. -/
inductive VItem where
  /-- Open a virtual-host block for `Host: <hostname>` (`*` ⇒ the fallback anyHost). -/
  | host (hostname : List Char)
  /-- A route scoped to the current block. -/
  | route (r : VRouteSpec)
deriving DecidableEq, Repr

/-- The method and path tokens must not be clause/handler keywords, so the prefix
(`[method] path`) is exactly the run of tokens before the first `header`/`query`/handler
keyword — the optional-method + optional-guard grammar is then recovered unambiguously.
Guard NAMES and handler args are consumed positionally after their keyword, so they
carry no such restriction. -/
def NotStopKw (t : List Char) : Prop := isStopKw t = false

/-- A vhost route is well-formed when its free-text tokens carry no separator, and the
method (if present) and path tokens are not clause/handler keywords — so the scanner
splits `[method] path [header <name>] [query <name>] <handler…>` unambiguously. Real
method/path tokens (`GET`, `/`, `/old`, `/admin`, …) satisfy this. -/
def VRouteWF (r : VRouteSpec) : Prop :=
  (' ' ∉ r.pathTok ∧ '\n' ∉ r.pathTok) ∧ NotStopKw r.pathTok
    ∧ (match r.method with | none => True | some m => (' ' ∉ m ∧ '\n' ∉ m) ∧ NotStopKw m)
    ∧ (match r.headerGuard with | none => True | some h => ' ' ∉ h ∧ '\n' ∉ h)
    ∧ (match r.queryGuard with | none => True | some q => ' ' ∉ q ∧ '\n' ∉ q)
    ∧ (∀ n ∈ r.middleware, ' ' ∉ n ∧ '\n' ∉ n)
    ∧ HandlerWF r.handler

/-- A vhost item is well-formed when its tokens carry no separator. -/
def VItemWF : VItem → Prop
  | .host h  => ' ' ∉ h ∧ '\n' ∉ h
  | .route r => VRouteWF r

/-- The vhost section, if non-empty, begins with a `host` header (every scoped route
follows the block it belongs to). This is the shape `render` always produces and the
only condition the vhost-section split in the round-trip needs. -/
def VItemsHeadWF : List VItem → Prop
  | []            => True
  | .host _ :: _  => True
  | .route _ :: _ => False

/-! ## The parsed-config AST (pure data) -/

/-- The parseable data dimensions of a deployment: the listener accept surface, the
reverse-proxy pool name + LB policy, the L4 passthrough mode, the TLS 0-RTT toggle,
and the declared **route table**. Denoted onto `defaultDeployment`'s proven byte
pipeline by `denote`. -/
structure ParsedConfig where
  /-- Listener bind address (host). -/
  addr : List Char
  /-- Listener bind port. -/
  port : Nat
  /-- Reverse-proxy upstream pool name. -/
  poolName : List Char
  /-- Load-balancing policy over the pool. -/
  lb : LbPolicy
  /-- `some m` ⇒ a layer-4 passthrough listener (mode `m`) over the pool; `none`
  ⇒ a plain HTTP listener. -/
  l4 : Option L4Mode
  /-- The listener TLS profile's 0-RTT / early-data toggle. -/
  zeroRtt : Bool
  /-- The declared route table (empty ⇒ keep the base deployment's route table). -/
  routes : List RouteSpec := []
  /-- The declared virtual-host dimension: `host`/`route` items, denoted onto the
  deployed `Handler.hostGlob` (host + method + glob dispatch). Empty ⇒ no vhosts. -/
  vitems : List VItem := []
deriving DecidableEq, Repr

/-- A config is well-formed when its free-text tokens (bind address, pool name, and
every route's path + handler tokens) carry no separator character — the only
condition a round-trip needs. -/
def WF (pc : ParsedConfig) : Prop :=
  ' ' ∉ pc.addr ∧ '\n' ∉ pc.addr ∧ ' ' ∉ pc.poolName ∧ '\n' ∉ pc.poolName
    ∧ (∀ r ∈ pc.routes, RouteWF r)
    ∧ (∀ it ∈ pc.vitems, VItemWF it)
    ∧ VItemsHeadWF pc.vitems

/-! ## Rendering -/

/-- The four keyword tokens. -/
def kwListener : List Char := ['l','i','s','t','e','n','e','r']
def kwPool     : List Char := ['p','o','o','l']
def kwL4       : List Char := ['l','4']
def kwTls      : List Char := ['t','l','s']

/-- A three-token line `a b c`. -/
def line3 (a b c : List Char) : List Char := a ++ ' ' :: (b ++ ' ' :: c)
/-- A two-token line `a b`. -/
def line2 (a b : List Char) : List Char := a ++ ' ' :: b
/-- A four-token line `a b c d`. -/
def line4 (a b c d : List Char) : List Char := a ++ ' ' :: (b ++ ' ' :: (c ++ ' ' :: d))
/-- A five-token line `a b c d e`. -/
def line5 (a b c d e : List Char) : List Char :=
  a ++ ' ' :: (b ++ ' ' :: (c ++ ' ' :: (d ++ ' ' :: e)))
/-- A six-token line `a b c d e f`. -/
def line6 (a b c d e f : List Char) : List Char :=
  a ++ ' ' :: (b ++ ' ' :: (c ++ ' ' :: (d ++ ' ' :: (e ++ ' ' :: f))))

/-! ### Route-line tokens (the keyword constants are defined earlier) -/

/-- Render one route as a whitespace-separated line: `route <path> <handler…>`. -/
def routeLine (r : RouteSpec) : List Char :=
  match r.handler with
  | .proxy pool      => line4 kwRoute r.pathTok kwProxy pool
  | .redirect st loc => line5 kwRoute r.pathTok kwRedirect (renderNat st) loc
  | .respond st body => line5 kwRoute r.pathTok kwRespond (renderNat st) body
  | .static          => line3 kwRoute r.pathTok kwStatic

/-- Render a route table as newline-prefixed lines (empty for no routes, so a
routeless config renders byte-identically to the original four-line form). -/
def renderRoutes : List RouteSpec → List Char
  | []      => []
  | r :: rs => '\n' :: (routeLine r ++ renderRoutes rs)

/-! ### Virtual-host item lines -/

/-- Render a `host <hostname>` block-header line. -/
def hostHdrLine (h : List Char) : List Char := line2 kwHost h

/-- The handler tail tokens: `static` / `proxy <pool>` / `redirect <status> <loc>` /
`respond <status> <body>`. Always non-empty and led by a handler keyword. -/
def handlerToks : HandlerSpec → List (List Char)
  | .static          => [kwStatic]
  | .proxy pool      => [kwProxy, pool]
  | .redirect st loc => [kwRedirect, renderNat st, loc]
  | .respond st body => [kwRespond, renderNat st, body]

/-- The middleware-chain tokens: `middleware <name>` per declared middleware, in order. -/
def middlewareToks : List (List Char) → List (List Char)
  | []      => []
  | n :: ns => kwMiddleware :: n :: middlewareToks ns

/-- The optional guard-clause tokens: `header <name>` then `query <key>`, each present
only when its guard is. -/
def guardToks (r : VRouteSpec) : List (List Char) :=
  (match r.headerGuard with | none => [] | some h => [kwHeader, h])
    ++ (match r.queryGuard with | none => [] | some q => [kwQuery, q])

/-- The `[method] path` prefix tokens (method rendered only when present). -/
def prefixToks (r : VRouteSpec) : List (List Char) :=
  (match r.method with | none => [] | some m => [m]) ++ [r.pathTok]

/-- The full token list of a vhost route line:
`route [<method>] <path> [middleware <name>]… [header <name>] [query <key>] <handler…>`. -/
def tokensOfVRoute (r : VRouteSpec) : List (List Char) :=
  kwRoute :: (prefixToks r ++ (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)))

/-- Render one virtual-host route line as its space-joined tokens. The method guard and
each of the `header`/`query` guard clauses are rendered only when present. -/
def vrouteLine (r : VRouteSpec) : List Char := joinSp (tokensOfVRoute r)

/-- Render one vhost item to its line. -/
def vitemLine : VItem → List Char
  | .host h  => hostHdrLine h
  | .route r => vrouteLine r

/-- A generic newline-prefixed line renderer: one `\n`-prefixed chunk per line. Both
`renderRoutes` and the vhost section are instances (`renderRoutes_eq`), which is what
lets the outer newline split peel the base tail line then every route and vhost line
uniformly. -/
def renderLines : List (List Char) → List Char
  | []      => []
  | l :: ls => '\n' :: (l ++ renderLines ls)

/-- Render the vhost section as newline-prefixed lines (empty ⇒ byte-identical to a
config with no vhost dimension). -/
def renderVItems (its : List VItem) : List Char := renderLines (its.map vitemLine)

theorem renderLines_append (a b : List (List Char)) :
    renderLines (a ++ b) = renderLines a ++ renderLines b := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, renderLines, ih, List.append_assoc]

/-- `renderRoutes` is `renderLines` over the mapped route lines. -/
theorem renderRoutes_eq (routes : List RouteSpec) :
    renderRoutes routes = renderLines (routes.map routeLine) := by
  induction routes with
  | nil => rfl
  | cons r rs ih => simp only [renderRoutes, renderLines, List.map_cons, ih]

/-! ### Every rendered line is non-empty

Each `lineN` inserts a literal separator, so it is non-empty whatever its tokens;
`routeLine` is one such line. This is what lets `parseChars` drop empty lines (a
trailing newline, blank lines) without ever dropping a meaningful one. -/

theorem line2_ne (a b : List Char) : line2 a b ≠ [] := by cases a <;> simp [line2]
theorem line3_ne (a b c : List Char) : line3 a b c ≠ [] := by cases a <;> simp [line3]
theorem line4_ne (a b c d : List Char) : line4 a b c d ≠ [] := by cases a <;> simp [line4]
theorem line5_ne (a b c d e : List Char) : line5 a b c d e ≠ [] := by cases a <;> simp [line5]
theorem line6_ne (a b c d e f : List Char) : line6 a b c d e f ≠ [] := by cases a <;> simp [line6]

theorem routeLine_ne (r : RouteSpec) : routeLine r ≠ [] := by
  cases hh : r.handler <;> simp only [routeLine, hh]
  · exact line4_ne _ _ _ _
  · exact line5_ne _ _ _ _ _
  · exact line5_ne _ _ _ _ _
  · exact line3_ne _ _ _

/-- The four config lines of a parsed config. -/
def l1 (pc : ParsedConfig) : List Char := line3 kwListener pc.addr (renderNat pc.port)
def l2 (pc : ParsedConfig) : List Char := line3 kwPool pc.poolName (lbTok pc.lb)
def l3 (pc : ParsedConfig) : List Char := line2 kwL4 (l4Tok pc.l4)
def l4line (pc : ParsedConfig) : List Char := line2 kwTls (zTok pc.zeroRtt)

/-- **Render** a parsed config to characters: the four base lines, then one
newline-prefixed line per declared route. -/
def renderChars (pc : ParsedConfig) : List Char :=
  l1 pc ++ '\n' :: (l2 pc ++ '\n' :: (l3 pc ++ '\n' ::
    (l4line pc ++ (renderRoutes pc.routes ++ renderVItems pc.vitems))))

/-- The `String` rendering, for generating config files. -/
def render (pc : ParsedConfig) : String := ⟨renderChars pc⟩

/-! ## Parsing -/

def parseListenerLine (l : List Char) : Option (List Char × Nat) :=
  match splitOn1 ' ' l with
  | [kw, a, p] => if kw = kwListener then (parseNat p).map (fun n => (a, n)) else none
  | _ => none

def parsePoolLine (l : List Char) : Option (List Char × LbPolicy) :=
  match splitOn1 ' ' l with
  | [kw, n, lbt] => if kw = kwPool then (parseLb lbt).map (fun p => (n, p)) else none
  | _ => none

def parseL4Line (l : List Char) : Option (Option L4Mode) :=
  match splitOn1 ' ' l with
  | [kw, m] => if kw = kwL4 then parseL4 m else none
  | _ => none

def parseTlsLine (l : List Char) : Option Bool :=
  match splitOn1 ' ' l with
  | [kw, z] => if kw = kwTls then parseZ z else none
  | _ => none

/-- Parse one route line back to a `RouteSpec`. Shapes: `route <path> static`,
`route <path> proxy <pool>`, `route <path> redirect <status> <loc>`,
`route <path> respond <status> <body>`. -/
def parseRouteLine (l : List Char) : Option RouteSpec :=
  match splitOn1 ' ' l with
  | [kw, path, k] =>
    if kw = kwRoute ∧ k = kwStatic then some ⟨path, .static⟩ else none
  | [kw, path, k, a] =>
    if kw = kwRoute ∧ k = kwProxy then some ⟨path, .proxy a⟩ else none
  | [kw, path, k, st, a] =>
    if kw = kwRoute then
      if k = kwRedirect then (parseNat st).map (fun n => ⟨path, .redirect n a⟩)
      else if k = kwRespond then (parseNat st).map (fun n => ⟨path, .respond n a⟩)
      else none
    else none
  | _ => none

/-- Parse the trailing route lines into a route table (`none` if any line is
malformed). -/
def parseRoutes : List (List Char) → Option (List RouteSpec)
  | []      => some []
  | l :: ls =>
    match parseRouteLine l, parseRoutes ls with
    | some r, some rs => some (r :: rs)
    | _, _ => none

/-! ### Virtual-host item parsing -/

/-- Split a token list at the first stop keyword: the tokens before it (the
`[method] path` prefix), and the keyword-led remainder (the guard clauses + handler). -/
def spanBeforeStop : List (List Char) → List (List Char) × List (List Char)
  | []      => ([], [])
  | t :: ts =>
    match isStopKw t with
    | true  => ([], t :: ts)
    | false => let p := spanBeforeStop ts; (t :: p.1, p.2)

/-- Parse the handler tail tokens back to a `HandlerSpec`. -/
def parseHandlerToks : List (List Char) → Option HandlerSpec
  | [k]        => if k = kwStatic then some .static else none
  | [k, a]     => if k = kwProxy then some (.proxy a) else none
  | [k, st, a] =>
    if k = kwRedirect then (parseNat st).map (fun n => .redirect n a)
    else if k = kwRespond then (parseNat st).map (fun n => .respond n a)
    else none
  | _ => none

/-- Peel the leading `middleware <name>` clauses off `suf` (a chain, in order): each
`middleware <name>` pair contributes `name`; the scan stops at the first token that is
not `middleware`. -/
def peelMiddleware : List (List Char) → List (List Char) × List (List Char)
  | k :: name :: rest =>
    if k = kwMiddleware then
      let p := peelMiddleware rest
      (name :: p.1, p.2)
    else ([], k :: name :: rest)
  | suf => ([], suf)

/-- Peel an optional leading `header <name>` clause off `suf`. -/
def peelHeader (suf : List (List Char)) : Option (List Char) × List (List Char) :=
  match suf with
  | k :: name :: rest => if k = kwHeader then (some name, rest) else (none, suf)
  | _                 => (none, suf)

/-- Peel an optional leading `query <key>` clause off `suf`. -/
def peelQuery (suf : List (List Char)) : Option (List Char) × List (List Char) :=
  match suf with
  | k :: name :: rest => if k = kwQuery then (some name, rest) else (none, suf)
  | _                 => (none, suf)

/-- Given the parsed method + path, consume the optional `header`/`query` clauses then
the handler tail. -/
def parseClauses (method : Option (List Char)) (path : List Char)
    (suf : List (List Char)) : Option VRouteSpec :=
  let mw := peelMiddleware suf
  let hdr := peelHeader mw.2
  let qry := peelQuery hdr.2
  (parseHandlerToks qry.2).map (fun h => ⟨method, path, mw.1, hdr.1, qry.1, h⟩)

/-- Parse a `route …` token list: `route [<method>] <path> [header <name>]
[query <key>] <handler…>`. The `[method] path` prefix is the run of tokens before the
first clause/handler keyword (`spanBeforeStop`); a well-formed method/path is never a
keyword (`VRouteWF`), so the prefix is recovered unambiguously. -/
def parseVRouteToks : List (List Char) → Option VRouteSpec
  | []        => none
  | _ :: rest =>
    match spanBeforeStop rest with
    | ([path], suf)         => parseClauses none path suf
    | ([method, path], suf) => parseClauses (some method) path suf
    | _                     => none

/-- Parse one vhost item line: `host <hostname>` (a two-token block header) or a scoped
route line (`route …`, `parseVRouteToks`). The leading keyword selects: `host` opens a
block, anything else is parsed as a route line. -/
def parseVItemLine (l : List Char) : Option VItem :=
  match splitOn1 ' ' l with
  | []        => none
  | kw :: rest =>
    if kw = kwHost then
      match rest with
      | [h] => some (.host h)
      | _   => none
    else
      (parseVRouteToks (kw :: rest)).map (fun r => .route r)

/-- Parse the vhost section lines into an item list (`none` if any line is malformed). -/
def parseVItems : List (List Char) → Option (List VItem)
  | []      => some []
  | l :: ls =>
    match parseVItemLine l, parseVItems ls with
    | some it, some its => some (it :: its)
    | _, _ => none

/-- Is `l` a `host <hostname>` block-header line? (Exactly two tokens, first `host`.)
Route lines (three-plus tokens) and every base line are NOT host lines, so this cleanly
marks the boundary between the flat-route section and the vhost section. -/
def isHostLine (l : List Char) : Bool :=
  match splitOn1 ' ' l with
  | [kw, _] => decide (kw = kwHost)
  | _       => false

/-- Parse the tail lines (after the four base lines): flat `route …` lines up to the
first `host` header, then the whole vhost section from that header on. So the flat
route table and the virtual-host dimension are recovered from one line stream. -/
def parseTail : List (List Char) → Option (List RouteSpec × List VItem)
  | []      => some ([], [])
  | l :: ls =>
    if isHostLine l then
      (parseVItems (l :: ls)).map (fun vs => ([], vs))
    else
      match parseRouteLine l, parseTail ls with
      | some r, some (rs, vs) => some (r :: rs, vs)
      | _, _ => none

/-- **Parse** characters to a parsed config (`none` on any malformed line/shape).
The first four lines are the base dimensions; the tail is the flat route table
followed by the virtual-host section (`parseTail`).

Empty lines are dropped before the shape match, so a config an editor saved with a
trailing newline (or with blank separator lines) still parses: `splitOn1 '\n'` of a
`…\n`-terminated file yields a trailing empty segment, which the filter removes.
Every RENDERED line is non-empty (`line{2,3,4,5,6}_ne`, `routeLine_ne`, `vitemLine_ne`),
so this never drops a meaningful line — the round-trip (`parse_render`) is preserved. -/
def parseChars (cs : List Char) : Option ParsedConfig :=
  match (splitOn1 '\n' cs).filter (fun l => !l.isEmpty) with
  | ln1 :: ln2 :: ln3 :: ln4 :: rest =>
    match parseListenerLine ln1, parsePoolLine ln2, parseL4Line ln3, parseTlsLine ln4,
          parseTail rest with
    | some (a, p), some (n, lb), some l4, some z, some (routes, vitems) =>
      some { addr := a, port := p, poolName := n, lb := lb, l4 := l4, zeroRtt := z,
             routes := routes, vitems := vitems }
    | _, _, _, _, _ => none
  | _ => none

/-! ## The round-trip (parse-soundness) -/

/-- Keywords carry no separator. -/
theorem kw_no_sp : ' ' ∉ kwListener ∧ ' ' ∉ kwPool ∧ ' ' ∉ kwL4 ∧ ' ' ∉ kwTls :=
  ⟨by decide, by decide, by decide, by decide⟩
theorem kw_no_nl : '\n' ∉ kwListener ∧ '\n' ∉ kwPool ∧ '\n' ∉ kwL4 ∧ '\n' ∉ kwTls :=
  ⟨by decide, by decide, by decide, by decide⟩

theorem split_line3 (a b c : List Char)
    (ha : ' ' ∉ a) (hb : ' ' ∉ b) (hc : ' ' ∉ c) :
    splitOn1 ' ' (line3 a b c) = [a, b, c] := by
  unfold line3
  rw [splitOn1_append ' ' a _ ha, splitOn1_append ' ' b c hb, splitOn1_no_sep ' ' c hc]

theorem split_line2 (a b : List Char) (ha : ' ' ∉ a) (hb : ' ' ∉ b) :
    splitOn1 ' ' (line2 a b) = [a, b] := by
  unfold line2; rw [splitOn1_append ' ' a b ha, splitOn1_no_sep ' ' b hb]

/-- A `line3`'s characters contain no newline (its tokens don't). -/
theorem line3_no_nl (a b c : List Char)
    (ha : '\n' ∉ a) (hb : '\n' ∉ b) (hc : '\n' ∉ c) : '\n' ∉ line3 a b c := by
  simp only [line3, List.mem_append, List.mem_cons]
  rintro (h | h | h | h | h)
  · exact ha h
  · exact absurd h (by decide)
  · exact hb h
  · exact absurd h (by decide)
  · exact hc h

/-- A `line2`'s characters contain no newline. -/
theorem line2_no_nl (a b : List Char)
    (ha : '\n' ∉ a) (hb : '\n' ∉ b) : '\n' ∉ line2 a b := by
  simp only [line2, List.mem_append, List.mem_cons]
  rintro (h | h | h)
  · exact ha h
  · exact absurd h (by decide)
  · exact hb h

/-! ### Route-line round-trip lemmas -/

theorem split_line4 (a b c d : List Char)
    (ha : ' ' ∉ a) (hb : ' ' ∉ b) (hc : ' ' ∉ c) (hd : ' ' ∉ d) :
    splitOn1 ' ' (line4 a b c d) = [a, b, c, d] := by
  unfold line4
  rw [splitOn1_append ' ' a _ ha, splitOn1_append ' ' b _ hb,
      splitOn1_append ' ' c d hc, splitOn1_no_sep ' ' d hd]

theorem split_line5 (a b c d e : List Char)
    (ha : ' ' ∉ a) (hb : ' ' ∉ b) (hc : ' ' ∉ c) (hd : ' ' ∉ d) (he : ' ' ∉ e) :
    splitOn1 ' ' (line5 a b c d e) = [a, b, c, d, e] := by
  unfold line5
  rw [splitOn1_append ' ' a _ ha, splitOn1_append ' ' b _ hb,
      splitOn1_append ' ' c _ hc, splitOn1_append ' ' d e hd, splitOn1_no_sep ' ' e he]

theorem line4_no_nl (a b c d : List Char)
    (ha : '\n' ∉ a) (hb : '\n' ∉ b) (hc : '\n' ∉ c) (hd : '\n' ∉ d) :
    '\n' ∉ line4 a b c d := by
  simp only [line4, List.mem_append, List.mem_cons]
  rintro (h | h | h | h | h | h | h)
  · exact ha h
  · exact absurd h (by decide)
  · exact hb h
  · exact absurd h (by decide)
  · exact hc h
  · exact absurd h (by decide)
  · exact hd h

theorem line5_no_nl (a b c d e : List Char)
    (ha : '\n' ∉ a) (hb : '\n' ∉ b) (hc : '\n' ∉ c) (hd : '\n' ∉ d) (he : '\n' ∉ e) :
    '\n' ∉ line5 a b c d e := by
  simp only [line5, List.mem_append, List.mem_cons]
  rintro (h | h | h | h | h | h | h | h | h)
  · exact ha h
  · exact absurd h (by decide)
  · exact hb h
  · exact absurd h (by decide)
  · exact hc h
  · exact absurd h (by decide)
  · exact hd h
  · exact absurd h (by decide)
  · exact he h

theorem routekw_no_sp :
    ' ' ∉ kwRoute ∧ ' ' ∉ kwProxy ∧ ' ' ∉ kwRedirect ∧ ' ' ∉ kwRespond ∧ ' ' ∉ kwStatic := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide
theorem routekw_no_nl :
    '\n' ∉ kwRoute ∧ '\n' ∉ kwProxy ∧ '\n' ∉ kwRedirect ∧ '\n' ∉ kwRespond ∧ '\n' ∉ kwStatic := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- A rendered route line carries no newline (its tokens don't). -/
theorem routeLine_no_nl (r : RouteSpec) (h : RouteWF r) : '\n' ∉ routeLine r := by
  obtain ⟨⟨_, hpath⟩, hh⟩ := h
  cases hhd : r.handler with
  | proxy pool =>
    have hpool : '\n' ∉ pool := (hhd ▸ hh).2
    simp only [routeLine, hhd]
    exact line4_no_nl _ _ _ _ routekw_no_nl.1 hpath routekw_no_nl.2.1 hpool
  | redirect st loc =>
    have hloc : '\n' ∉ loc := (hhd ▸ hh).2
    simp only [routeLine, hhd]
    exact line5_no_nl _ _ _ _ _ routekw_no_nl.1 hpath routekw_no_nl.2.2.1
      (renderNat_no_nl _) hloc
  | respond st body =>
    have hbody : '\n' ∉ body := (hhd ▸ hh).2
    simp only [routeLine, hhd]
    exact line5_no_nl _ _ _ _ _ routekw_no_nl.1 hpath routekw_no_nl.2.2.2.1
      (renderNat_no_nl _) hbody
  | static =>
    simp only [routeLine, hhd]
    exact line3_no_nl _ _ _ routekw_no_nl.1 hpath routekw_no_nl.2.2.2.2

/-- Splitting `base ++ renderRoutes routes` on newlines peels `base`, then one line
per route — the outer newline split recovers the base tail line and every route
line. -/
theorem split_renderRoutes (base : List Char) (routes : List RouteSpec)
    (hbase : '\n' ∉ base) (hr : ∀ r ∈ routes, '\n' ∉ routeLine r) :
    splitOn1 '\n' (base ++ renderRoutes routes) = base :: routes.map routeLine := by
  induction routes generalizing base with
  | nil =>
    simp only [renderRoutes, List.append_nil, List.map_nil]
    rw [splitOn1_no_sep '\n' base hbase]
  | cons r rs ih =>
    have hrr : '\n' ∉ routeLine r := hr r (List.mem_cons_self _ _)
    have hrest : ∀ r' ∈ rs, '\n' ∉ routeLine r' :=
      fun r' hr' => hr r' (List.mem_cons_of_mem _ hr')
    show splitOn1 '\n' (base ++ '\n' :: (routeLine r ++ renderRoutes rs)) = _
    rw [splitOn1_append '\n' base _ hbase, ih (routeLine r) hrr hrest]
    simp only [List.map_cons]

/-- One rendered route line parses back to its `RouteSpec`. -/
theorem parseRouteLine_render (r : RouteSpec) (h : RouteWF r) :
    parseRouteLine (routeLine r) = some r := by
  obtain ⟨⟨hpath, _⟩, hh⟩ := h
  cases hhd : r.handler with
  | proxy pool =>
    have hpool : ' ' ∉ pool := (hhd ▸ hh).1
    have hsplit : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwProxy, pool] := by
      simp only [routeLine, hhd]
      exact split_line4 _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.1 hpool
    simp [parseRouteLine, hsplit, ← hhd]
  | redirect st loc =>
    have hloc : ' ' ∉ loc := (hhd ▸ hh).1
    have hsplit : splitOn1 ' ' (routeLine r)
        = [kwRoute, r.pathTok, kwRedirect, renderNat st, loc] := by
      simp only [routeLine, hhd]
      exact split_line5 _ _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.1
        (renderNat_no_sp _) hloc
    simp [parseRouteLine, hsplit, parseNat_render, ← hhd]
  | respond st body =>
    have hbody : ' ' ∉ body := (hhd ▸ hh).1
    have hsplit : splitOn1 ' ' (routeLine r)
        = [kwRoute, r.pathTok, kwRespond, renderNat st, body] := by
      simp only [routeLine, hhd]
      exact split_line5 _ _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.2.1
        (renderNat_no_sp _) hbody
    have hne : ¬ (kwRespond = kwRedirect) := by decide
    simp [parseRouteLine, hsplit, parseNat_render, ← hhd, hne]
  | static =>
    have hsplit : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwStatic] := by
      simp only [routeLine, hhd]
      exact split_line3 _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.2.2
    simp [parseRouteLine, hsplit, ← hhd]

/-- The whole route table round-trips: parsing the rendered route lines recovers
the route list. -/
theorem parseRoutes_render (routes : List RouteSpec) (h : ∀ r ∈ routes, RouteWF r) :
    parseRoutes (routes.map routeLine) = some routes := by
  induction routes with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, parseRoutes,
      parseRouteLine_render r (h r (List.mem_cons_self _ _)),
      ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

/-! ### Virtual-host round-trip lemmas -/

theorem split_line6 (a b c d e f : List Char)
    (ha : ' ' ∉ a) (hb : ' ' ∉ b) (hc : ' ' ∉ c) (hd : ' ' ∉ d) (he : ' ' ∉ e) (hf : ' ' ∉ f) :
    splitOn1 ' ' (line6 a b c d e f) = [a, b, c, d, e, f] := by
  unfold line6
  rw [splitOn1_append ' ' a _ ha, splitOn1_append ' ' b _ hb,
      splitOn1_append ' ' c _ hc, splitOn1_append ' ' d _ hd,
      splitOn1_append ' ' e f he, splitOn1_no_sep ' ' f hf]

theorem line6_no_nl (a b c d e f : List Char)
    (ha : '\n' ∉ a) (hb : '\n' ∉ b) (hc : '\n' ∉ c) (hd : '\n' ∉ d) (he : '\n' ∉ e) (hf : '\n' ∉ f) :
    '\n' ∉ line6 a b c d e f := by
  simp only [line6, List.mem_append, List.mem_cons]
  rintro (h | h | h | h | h | h | h | h | h | h | h)
  · exact ha h
  · exact absurd h (by decide)
  · exact hb h
  · exact absurd h (by decide)
  · exact hc h
  · exact absurd h (by decide)
  · exact hd h
  · exact absurd h (by decide)
  · exact he h
  · exact absurd h (by decide)
  · exact hf h

theorem kwHost_no_sp : ' ' ∉ kwHost := by decide
theorem kwHost_no_nl : '\n' ∉ kwHost := by decide

/-! ### Token-level well-formedness of a vhost route line -/

/-- Every handler-tail token is space-free (from `HandlerWF`). -/
theorem handlerToks_no_sp (hd : HandlerSpec) (h : HandlerWF hd) :
    ∀ t ∈ handlerToks hd, ' ' ∉ t := by
  cases hd with
  | static =>
    intro t ht; simp only [handlerToks, List.mem_singleton] at ht; subst ht
    exact routekw_no_sp.2.2.2.2
  | proxy pool =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact routekw_no_sp.2.1
    · exact h.1
  | redirect st loc =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact routekw_no_sp.2.2.1
    · exact renderNat_no_sp _
    · exact h.1
  | respond st body =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact routekw_no_sp.2.2.2.1
    · exact renderNat_no_sp _
    · exact h.1

/-- Every handler-tail token is newline-free (from `HandlerWF`). -/
theorem handlerToks_no_nl (hd : HandlerSpec) (h : HandlerWF hd) :
    ∀ t ∈ handlerToks hd, '\n' ∉ t := by
  cases hd with
  | static =>
    intro t ht; simp only [handlerToks, List.mem_singleton] at ht; subst ht
    exact routekw_no_nl.2.2.2.2
  | proxy pool =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact routekw_no_nl.2.1
    · exact h.2
  | redirect st loc =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact routekw_no_nl.2.2.1
    · exact renderNat_no_nl _
    · exact h.2
  | respond st body =>
    intro t ht
    simp only [handlerToks, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact routekw_no_nl.2.2.2.1
    · exact renderNat_no_nl _
    · exact h.2

/-- The `[method] path` prefix tokens carry no `sep` (from the method/path WF facts). -/
theorem prefixToks_no_sep (sep : Char) (r : VRouteSpec) (hp : sep ∉ r.pathTok)
    (hm : match r.method with | none => True | some m => sep ∉ m) :
    ∀ t ∈ prefixToks r, sep ∉ t := by
  intro t ht
  cases hmm : r.method with
  | none =>
    simp only [prefixToks, hmm, List.nil_append, List.mem_singleton] at ht; subst ht; exact hp
  | some m =>
    simp only [prefixToks, hmm, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at ht
    simp only [hmm] at hm
    rcases ht with rfl | rfl
    · exact hm
    · exact hp

/-- The `header`/`query` guard-clause tokens carry no `sep` (the keyword tokens and each
present guard name). -/
theorem guardToks_no_sep (sep : Char) (r : VRouteSpec)
    (hkH : sep ∉ kwHeader) (hkQ : sep ∉ kwQuery)
    (hh : match r.headerGuard with | none => True | some h => sep ∉ h)
    (hq : match r.queryGuard with | none => True | some q => sep ∉ q) :
    ∀ t ∈ guardToks r, sep ∉ t := by
  intro t ht
  cases hgg : r.headerGuard with
  | none =>
    cases hqq : r.queryGuard with
    | none => simp [guardToks, hgg, hqq] at ht
    | some q =>
      simp only [guardToks, hgg, hqq, List.nil_append, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ht
      simp only [hqq] at hq
      rcases ht with rfl | rfl
      · exact hkQ
      · exact hq
  | some hn =>
    simp only [hgg] at hh
    cases hqq : r.queryGuard with
    | none =>
      simp only [guardToks, hgg, hqq, List.append_nil, List.mem_cons, List.mem_singleton,
        List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl
      · exact hkH
      · exact hh
    | some q =>
      simp only [hqq] at hq
      simp only [guardToks, hgg, hqq, List.cons_append, List.nil_append, List.mem_cons,
        List.mem_singleton, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl
      · exact hkH
      · exact hh
      · exact hkQ
      · exact hq

/-- The middleware-chain tokens carry no `sep` (the `middleware` keyword and each name). -/
theorem middlewareToks_no_sep (sep : Char) (names : List (List Char))
    (hkM : sep ∉ kwMiddleware) :
    (∀ n ∈ names, sep ∉ n) → ∀ t ∈ middlewareToks names, sep ∉ t := by
  induction names with
  | nil => intro _ t ht; simp [middlewareToks] at ht
  | cons a as ih =>
    intro hn t ht
    simp only [middlewareToks, List.mem_cons] at ht
    rcases ht with he | he | ht
    · rw [he]; exact hkM
    · rw [he]; exact hn a (List.mem_cons_self _ _)
    · exact ih (fun n' hn' => hn n' (List.mem_cons_of_mem _ hn')) t ht

/-- Every token of a vhost route line carries no `sep`, given the per-source facts. -/
theorem tokensOfVRoute_no_sep (sep : Char) (r : VRouteSpec)
    (hkR : sep ∉ kwRoute) (hkH : sep ∉ kwHeader) (hkQ : sep ∉ kwQuery)
    (hkM : sep ∉ kwMiddleware)
    (hp : sep ∉ r.pathTok)
    (hm : match r.method with | none => True | some m => sep ∉ m)
    (hh : match r.headerGuard with | none => True | some h => sep ∉ h)
    (hq : match r.queryGuard with | none => True | some q => sep ∉ q)
    (hmw : ∀ n ∈ r.middleware, sep ∉ n)
    (hhand : ∀ t ∈ handlerToks r.handler, sep ∉ t) :
    ∀ t ∈ tokensOfVRoute r, sep ∉ t := by
  intro t ht
  simp only [tokensOfVRoute, List.mem_cons, List.mem_append] at ht
  rcases ht with rfl | ht | ht | ht | ht
  · exact hkR
  · exact prefixToks_no_sep sep r hp hm t ht
  · exact middlewareToks_no_sep sep r.middleware hkM hmw t ht
  · exact guardToks_no_sep sep r hkH hkQ hh hq t ht
  · exact hhand t ht

/-- Every token of a well-formed vhost route line is space-free. -/
theorem tokensOfVRoute_no_sp (r : VRouteSpec) (h : VRouteWF r) :
    ∀ t ∈ tokensOfVRoute r, ' ' ∉ t := by
  obtain ⟨⟨hpsp, _⟩, _, hmeth, hhdr, hqry, hmwWF, hhWF⟩ := h
  refine tokensOfVRoute_no_sep ' ' r (by decide) (by decide) (by decide) (by decide) hpsp ?_ ?_ ?_ ?_
    (handlerToks_no_sp r.handler hhWF)
  · cases hm : r.method with
    | none => simp [hm]
    | some m => simp only [hm] at hmeth ⊢; exact hmeth.1.1
  · cases hg : r.headerGuard with
    | none => simp [hg]
    | some hn => simp only [hg] at hhdr ⊢; exact hhdr.1
  · cases hqg : r.queryGuard with
    | none => simp [hqg]
    | some qn => simp only [hqg] at hqry ⊢; exact hqry.1
  · intro n hn; exact (hmwWF n hn).1

/-- Every token of a well-formed vhost route line is newline-free. -/
theorem tokensOfVRoute_no_nl (r : VRouteSpec) (h : VRouteWF r) :
    ∀ t ∈ tokensOfVRoute r, '\n' ∉ t := by
  obtain ⟨⟨_, hpnl⟩, _, hmeth, hhdr, hqry, hmwWF, hhWF⟩ := h
  refine tokensOfVRoute_no_sep '\n' r (by decide) (by decide) (by decide) (by decide) hpnl ?_ ?_ ?_ ?_
    (handlerToks_no_nl r.handler hhWF)
  · cases hm : r.method with
    | none => simp [hm]
    | some m => simp only [hm] at hmeth ⊢; exact hmeth.1.2
  · cases hg : r.headerGuard with
    | none => simp [hg]
    | some hn => simp only [hg] at hhdr ⊢; exact hhdr.2
  · cases hqg : r.queryGuard with
    | none => simp [hqg]
    | some qn => simp only [hqg] at hqry ⊢; exact hqry.2
  · intro n hn; exact (hmwWF n hn).2

theorem vrouteLine_ne (r : VRouteSpec) : vrouteLine r ≠ [] := by
  show joinSp (tokensOfVRoute r) ≠ []
  simp only [tokensOfVRoute]
  exact joinSp_cons_ne kwRoute _ (by decide)

theorem vitemLine_ne (it : VItem) : vitemLine it ≠ [] := by
  cases it with
  | host h  => exact line2_ne _ _
  | route r => exact vrouteLine_ne r

/-- A rendered vhost route line carries no newline (its tokens don't). -/
theorem vrouteLine_no_nl (r : VRouteSpec) (h : VRouteWF r) : '\n' ∉ vrouteLine r :=
  joinSp_no_nl (tokensOfVRoute_no_nl r h)

theorem vitemLine_no_nl (it : VItem) (h : VItemWF it) : '\n' ∉ vitemLine it := by
  cases it with
  | host hn => exact line2_no_nl _ _ kwHost_no_nl h.2
  | route r => exact vrouteLine_no_nl r h

/-! ### Parsing a vhost route line back — the scanner round-trip -/

/-- The `[method] path` prefix tokens are never stop keywords (from `VRouteWF`). -/
theorem prefixToks_notStop (r : VRouteSpec) (hp : NotStopKw r.pathTok)
    (hm : match r.method with | none => True | some m => (' ' ∉ m ∧ '\n' ∉ m) ∧ NotStopKw m) :
    ∀ x ∈ prefixToks r, isStopKw x = false := by
  intro x hx
  simp only [prefixToks, List.mem_append, List.mem_singleton] at hx
  rcases hx with hmem | rfl
  · cases hmeth : r.method with
    | none => simp [hmeth] at hmem
    | some m =>
      simp only [hmeth, List.mem_singleton] at hmem; subst hmem
      simp only [hmeth] at hm; exact hm.2
  · exact hp

/-- The guard+handler suffix is non-empty and led by a stop keyword. -/
theorem guardHandlerSuf_head_stop (r : VRouteSpec) :
    (match (guardToks r ++ handlerToks r.handler) with
     | [] => True | y :: _ => isStopKw y = true) := by
  rcases hg : r.headerGuard with _ | hn <;>
    rcases hq : r.queryGuard with _ | qn <;>
    cases hh : r.handler <;>
    simp [guardToks, handlerToks, hg, hq, hh, isStopKw]

/-- The full middleware+guard+handler suffix is non-empty and led by a stop keyword:
`middleware` when the chain is non-empty, else the leading guard/handler keyword. -/
theorem stopSuf_head_stop (r : VRouteSpec) :
    (match (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)) with
     | [] => True | y :: _ => isStopKw y = true) := by
  cases hmw : r.middleware with
  | cons n ns => simp only [middlewareToks, List.cons_append]; decide
  | nil => simp only [middlewareToks, List.nil_append]; exact guardHandlerSuf_head_stop r

/-- The head of the guard+handler suffix is never the `middleware` keyword — so the
middleware peel stops exactly at the end of the chain. -/
theorem guardHandlerSuf_head_notMw (r : VRouteSpec) :
    ∀ k t, (guardToks r ++ handlerToks r.handler) = k :: t → k ≠ kwMiddleware := by
  intro k t hkt
  rcases hg : r.headerGuard with _ | hn <;>
    rcases hq : r.queryGuard with _ | qn <;>
    cases hh : r.handler <;>
    (simp only [guardToks, handlerToks, hg, hq, hh, List.nil_append, List.append_nil,
        List.cons_append, List.singleton_append] at hkt <;>
      obtain ⟨rfl, _⟩ := hkt <;> decide)

/-- `peelMiddleware` stops immediately on a suffix whose head is not `middleware`. -/
theorem peelMiddleware_stop (rest : List (List Char))
    (h : ∀ k t, rest = k :: t → k ≠ kwMiddleware) :
    peelMiddleware rest = ([], rest) := by
  cases rest with
  | nil => rfl
  | cons k t =>
    cases t with
    | nil => rfl
    | cons name rest' =>
      have hk : k ≠ kwMiddleware := h k _ rfl
      simp only [peelMiddleware, if_neg hk]

/-- **Middleware peel round-trip.** Peeling the rendered `middleware <name>` chain off
`middlewareToks names ++ rest` recovers exactly `names`, leaving `rest` — provided
`rest`'s head is not the `middleware` keyword (the guard/handler suffix). -/
theorem peelMiddleware_render (names rest : List (List Char))
    (h : ∀ k t, rest = k :: t → k ≠ kwMiddleware) :
    peelMiddleware (middlewareToks names ++ rest) = (names, rest) := by
  induction names with
  | nil => simpa [middlewareToks] using peelMiddleware_stop rest h
  | cons n ns ih =>
    show peelMiddleware (kwMiddleware :: n :: (middlewareToks ns ++ rest)) = (n :: ns, rest)
    unfold peelMiddleware
    rw [if_pos rfl, ih]

/-- **Prefix span.** With every prefix token a non-keyword and the suffix led by a stop
keyword, `spanBeforeStop` peels exactly the prefix. -/
theorem spanBeforeStop_prefix : ∀ (pre suf : List (List Char)),
    (∀ x ∈ pre, isStopKw x = false) →
    (match suf with | [] => True | y :: _ => isStopKw y = true) →
    spanBeforeStop (pre ++ suf) = (pre, suf) := by
  intro pre
  induction pre with
  | nil =>
    intro suf _ hsuf
    cases suf with
    | nil => rfl
    | cons y ys => simp only [List.nil_append, spanBeforeStop, hsuf]
  | cons x xs ih =>
    intro suf hpre hsuf
    have hx : isStopKw x = false := hpre x (List.mem_cons_self _ _)
    have hxs : ∀ z ∈ xs, isStopKw z = false := fun z hz => hpre z (List.mem_cons_of_mem _ hz)
    show spanBeforeStop (x :: (xs ++ suf)) = (x :: xs, suf)
    simp only [spanBeforeStop, hx, ih suf hxs hsuf]

/-- One handler tail round-trips. -/
theorem parseHandlerToks_render (hd : HandlerSpec) :
    parseHandlerToks (handlerToks hd) = some hd := by
  cases hd <;>
    simp [handlerToks, parseHandlerToks, parseNat_render, kwStatic, kwProxy, kwRedirect,
      kwRespond]

/-- The middleware chain + optional guard clauses + handler tail round-trip to the
middleware chain, the guards, and the handler. -/
theorem parseClauses_render (r : VRouteSpec) :
    parseClauses r.method r.pathTok
      (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)) = some r := by
  have hpeel : peelMiddleware
      (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler))
      = (r.middleware, guardToks r ++ handlerToks r.handler) :=
    peelMiddleware_render r.middleware _ (guardHandlerSuf_head_notMw r)
  obtain ⟨method, path, mws, hg, qg, hd⟩ := r
  simp only [parseClauses, hpeel]
  -- reduced to the guard/handler peel over the guard+handler suffix, filling `mws`
  cases hg <;> cases qg <;> cases hd <;>
    simp [peelHeader, peelQuery, guardToks, handlerToks, parseHandlerToks,
      parseNat_render, kwHeader, kwQuery, kwStatic, kwProxy, kwRedirect, kwRespond]

/-- A rendered vhost route line's token list parses back to the route. -/
theorem parseVRouteToks_render (r : VRouteSpec) (h : VRouteWF r) :
    parseVRouteToks (tokensOfVRoute r) = some r := by
  obtain ⟨hpsp_nl, hpNK, hmeth, hhdr, hqry, hmwWF, hhWF⟩ := h
  have hspan : spanBeforeStop
        (prefixToks r ++ (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)))
      = (prefixToks r, middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)) :=
    spanBeforeStop_prefix (prefixToks r)
      (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler))
      (prefixToks_notStop r hpNK hmeth) (stopSuf_head_stop r)
  show parseVRouteToks
      (kwRoute :: (prefixToks r ++ (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler)))) = some r
  simp only [parseVRouteToks, hspan]
  cases hm : r.method with
  | none =>
    simp only [prefixToks, hm, List.nil_append]
    rw [← hm]; exact parseClauses_render r
  | some m =>
    simp only [prefixToks, hm, List.cons_append, List.nil_append]
    rw [← hm]; exact parseClauses_render r

/-- One rendered vhost item line parses back to its `VItem`: a `host` header via the
two-token host branch, a route line via the `route`-token scanner (`parseVRouteToks`). -/
theorem parseVItemLine_render (it : VItem) (h : VItemWF it) :
    parseVItemLine (vitemLine it) = some it := by
  cases it with
  | host hn =>
    have e : splitOn1 ' ' (vitemLine (VItem.host hn)) = [kwHost, hn] :=
      split_line2 kwHost hn kwHost_no_sp h.1
    simp [parseVItemLine, e]
  | route r =>
    have hwf : VRouteWF r := h
    have hne : tokensOfVRoute r ≠ [] := by simp [tokensOfVRoute]
    have hs : splitOn1 ' ' (vrouteLine r) = tokensOfVRoute r :=
      joinSp_split hne (tokensOfVRoute_no_sp r hwf)
    show parseVItemLine (vrouteLine r) = some (VItem.route r)
    unfold parseVItemLine
    rw [hs]
    simp only [tokensOfVRoute, if_neg (show ¬ (kwRoute = kwHost) by decide)]
    rw [show (kwRoute :: (prefixToks r ++ (middlewareToks r.middleware ++ (guardToks r ++ handlerToks r.handler))))
          = tokensOfVRoute r from rfl, parseVRouteToks_render r hwf]
    rfl

/-- The whole vhost section round-trips: parsing the rendered item lines recovers
the item list. -/
theorem parseVItems_render (its : List VItem) (h : ∀ it ∈ its, VItemWF it) :
    parseVItems (its.map vitemLine) = some its := by
  induction its with
  | nil => rfl
  | cons it rest ih =>
    simp only [List.map_cons, parseVItems,
      parseVItemLine_render it (h it (List.mem_cons_self _ _)),
      ih (fun it' hit' => h it' (List.mem_cons_of_mem _ hit'))]

/-- Splitting `base ++ renderLines ls` on newlines peels `base`, then one line per
element of `ls`. -/
theorem split_renderLines (base : List Char) (ls : List (List Char))
    (hbase : '\n' ∉ base) (hl : ∀ l ∈ ls, '\n' ∉ l) :
    splitOn1 '\n' (base ++ renderLines ls) = base :: ls := by
  induction ls generalizing base with
  | nil =>
    simp only [renderLines, List.append_nil]
    rw [splitOn1_no_sep '\n' base hbase]
  | cons l rest ih =>
    have hl0 : '\n' ∉ l := hl l (List.mem_cons_self _ _)
    have hrest : ∀ l' ∈ rest, '\n' ∉ l' := fun l' hh => hl l' (List.mem_cons_of_mem _ hh)
    show splitOn1 '\n' (base ++ '\n' :: (l ++ renderLines rest)) = _
    rw [splitOn1_append '\n' base _ hbase, ih l hl0 hrest]

/-- A rendered `host` header line IS a host line. -/
theorem isHostLine_hostHdr (hn : List Char) (h : ' ' ∉ hn) :
    isHostLine (hostHdrLine hn) = true := by
  have e : splitOn1 ' ' (hostHdrLine hn) = [kwHost, hn] :=
    split_line2 kwHost hn kwHost_no_sp h
  rw [isHostLine, e]
  rfl

/-- A rendered route line is NOT a host line (its first token is `route`, not
`host`). -/
theorem isHostLine_routeLine (r : RouteSpec) (h : RouteWF r) :
    isHostLine (routeLine r) = false := by
  obtain ⟨⟨hpath, _⟩, hh⟩ := h
  cases hhd : r.handler with
  | proxy pool =>
    have hpool : ' ' ∉ pool := (hhd ▸ hh).1
    have e : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwProxy, pool] := by
      simp only [routeLine, hhd]
      exact split_line4 _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.1 hpool
    rw [isHostLine, e]
  | redirect st loc =>
    have hloc : ' ' ∉ loc := (hhd ▸ hh).1
    have e : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwRedirect, renderNat st, loc] := by
      simp only [routeLine, hhd]
      exact split_line5 _ _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.1 (renderNat_no_sp _) hloc
    rw [isHostLine, e]
  | respond st body =>
    have hbody : ' ' ∉ body := (hhd ▸ hh).1
    have e : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwRespond, renderNat st, body] := by
      simp only [routeLine, hhd]
      exact split_line5 _ _ _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.2.1 (renderNat_no_sp _) hbody
    rw [isHostLine, e]
  | static =>
    have e : splitOn1 ' ' (routeLine r) = [kwRoute, r.pathTok, kwStatic] := by
      simp only [routeLine, hhd]
      exact split_line3 _ _ _ routekw_no_sp.1 hpath routekw_no_sp.2.2.2.2
    rw [isHostLine, e]

/-- A vhost-only tail (no leading flat routes) parses back to `([], vitems)`. -/
theorem parseTail_vitems (vitems : List VItem)
    (hv : ∀ it ∈ vitems, VItemWF it) (hhead : VItemsHeadWF vitems) :
    parseTail (vitems.map vitemLine) = some ([], vitems) := by
  cases vitems with
  | nil => rfl
  | cons it rest =>
    cases it with
    | route r => simp only [VItemsHeadWF] at hhead
    | host hn =>
      have hh : ' ' ∉ hn := (hv _ (List.mem_cons_self _ _)).1
      have hpv : parseVItems ((VItem.host hn :: rest).map vitemLine)
          = some (VItem.host hn :: rest) := parseVItems_render _ hv
      show parseTail (vitemLine (VItem.host hn) :: rest.map vitemLine) = _
      rw [parseTail,
          if_pos (show isHostLine (vitemLine (VItem.host hn)) = true from isHostLine_hostHdr hn hh)]
      rw [show (vitemLine (VItem.host hn) :: rest.map vitemLine)
            = (VItem.host hn :: rest).map vitemLine from rfl, hpv]
      rfl

/-- The tail round-trips: parsing the rendered flat-route lines then vhost-item lines
recovers the flat route table AND the vhost item list. -/
theorem parseTail_render (routes : List RouteSpec) (vitems : List VItem)
    (hr : ∀ r ∈ routes, RouteWF r) (hv : ∀ it ∈ vitems, VItemWF it)
    (hhead : VItemsHeadWF vitems) :
    parseTail (routes.map routeLine ++ vitems.map vitemLine) = some (routes, vitems) := by
  induction routes with
  | nil =>
    rw [List.map_nil, List.nil_append]
    exact parseTail_vitems vitems hv hhead
  | cons r rs ih =>
    have hrr : RouteWF r := hr r (List.mem_cons_self _ _)
    have hrest : ∀ r' ∈ rs, RouteWF r' := fun r' hh => hr r' (List.mem_cons_of_mem _ hh)
    show parseTail (routeLine r :: (rs.map routeLine ++ vitems.map vitemLine)) = _
    rw [parseTail, if_neg (by simp [isHostLine_routeLine r hrr]),
        parseRouteLine_render r hrr, ih hrest]

/-- **Parse-soundness (round-trip).** A well-formed config renders to characters
that parse back to exactly that config — now including the declared route table. So
the running host, handed the rendering of a `ParsedConfig`, recovers that config
(routes and all) — the config the operator wrote drives the serve,
correct-by-construction. -/
theorem parse_render (pc : ParsedConfig) (h : WF pc) :
    parseChars (renderChars pc) = some pc := by
  obtain ⟨ha_sp, ha_nl, hn_sp, hn_nl, hroutes, hvitems, hhead⟩ := h
  -- newline-freedom of each base line
  have hl1 : '\n' ∉ l1 pc := line3_no_nl _ _ _ kw_no_nl.1 ha_nl (renderNat_no_nl _)
  have hl2 : '\n' ∉ l2 pc := line3_no_nl _ _ _ kw_no_nl.2.1 hn_nl (lbTok_no_ws pc.lb).2
  have hl3 : '\n' ∉ l3 pc := line2_no_nl _ _ kw_no_nl.2.2.1 (l4Tok_no_ws pc.l4).2
  have hl4 : '\n' ∉ l4line pc := line2_no_nl _ _ kw_no_nl.2.2.2 (zTok_no_ws pc.zeroRtt).2
  -- the tail is the route lines followed by the vhost item lines; none carries a newline
  have hlines : ∀ l ∈ (pc.routes.map routeLine ++ pc.vitems.map vitemLine), '\n' ∉ l := by
    intro l hl
    rcases List.mem_append.mp hl with hh | hh
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hh; exact routeLine_no_nl r (hroutes r hr)
    · obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hh; exact vitemLine_no_nl it (hvitems it hit)
  -- outer split on newlines recovers the four base lines then the tail lines
  have houter : splitOn1 '\n' (renderChars pc)
      = l1 pc :: l2 pc :: l3 pc :: l4line pc :: (pc.routes.map routeLine ++ pc.vitems.map vitemLine) := by
    unfold renderChars renderVItems
    rw [renderRoutes_eq, ← renderLines_append,
        splitOn1_append '\n' (l1 pc) _ hl1,
        splitOn1_append '\n' (l2 pc) _ hl2,
        splitOn1_append '\n' (l3 pc) _ hl3,
        split_renderLines (l4line pc) _ hl4 hlines]
  -- each base line parses to its field
  have p1 : parseListenerLine (l1 pc) = some (pc.addr, pc.port) := by
    unfold parseListenerLine
    rw [show splitOn1 ' ' (l1 pc) = [kwListener, pc.addr, renderNat pc.port] from
          split_line3 kwListener pc.addr (renderNat pc.port) kw_no_sp.1 ha_sp
            (renderNat_no_sp _)]
    simp [parseNat_render]
  have p2 : parsePoolLine (l2 pc) = some (pc.poolName, pc.lb) := by
    unfold parsePoolLine
    rw [show splitOn1 ' ' (l2 pc) = [kwPool, pc.poolName, lbTok pc.lb] from
          split_line3 kwPool pc.poolName (lbTok pc.lb) kw_no_sp.2.1 hn_sp
            (lbTok_no_ws pc.lb).1]
    simp [parseLb_lbTok]
  have p3 : parseL4Line (l3 pc) = some pc.l4 := by
    unfold parseL4Line
    rw [show splitOn1 ' ' (l3 pc) = [kwL4, l4Tok pc.l4] from
          split_line2 kwL4 (l4Tok pc.l4) kw_no_sp.2.2.1 (l4Tok_no_ws pc.l4).1]
    simp [parseL4_l4Tok]
  have p4 : parseTlsLine (l4line pc) = some pc.zeroRtt := by
    unfold parseTlsLine
    rw [show splitOn1 ' ' (l4line pc) = [kwTls, zTok pc.zeroRtt] from
          split_line2 kwTls (zTok pc.zeroRtt) kw_no_sp.2.2.2 (zTok_no_ws pc.zeroRtt).1]
    simp [parseZ_zTok]
  have p5 : parseTail (pc.routes.map routeLine ++ pc.vitems.map vitemLine)
      = some (pc.routes, pc.vitems) :=
    parseTail_render pc.routes pc.vitems hroutes hvitems hhead
  -- dropping empty lines is a no-op: every rendered line is non-empty
  have hfil : (splitOn1 '\n' (renderChars pc)).filter (fun l => !l.isEmpty)
      = l1 pc :: l2 pc :: l3 pc :: l4line pc :: (pc.routes.map routeLine ++ pc.vitems.map vitemLine) := by
    rw [houter]
    refine List.filter_eq_self.mpr ?_
    intro x hx
    have hxne : x ≠ [] := by
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | hx
      · exact line3_ne _ _ _
      · exact line3_ne _ _ _
      · exact line2_ne _ _
      · exact line2_ne _ _
      · rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx; exact routeLine_ne r
        · obtain ⟨it, _, rfl⟩ := List.mem_map.mp hx; exact vitemLine_ne it
    cases x with
    | nil => exact absurd rfl hxne
    | cons _ _ => rfl
  -- assemble
  unfold parseChars
  rw [hfil]
  simp only [p1, p2, p3, p4, p5]

/-! ## Malformed inputs -/

/-- The empty config parses to `none` (one line, wrong shape). -/
theorem parse_empty : parseChars [] = none := rfl

/-- A config with an unknown first keyword parses to `none`. -/
theorem parse_bad_keyword :
    parseChars (['x'] ++ '\n' :: (['p'] ++ '\n' :: (['q'] ++ '\n' :: ['r']))) = none := by
  decide

/-! ## Denotation — a parsed config as a `DeploymentConfig`

The parseable DATA dimensions layer onto a BASE deployment's proven byte pipeline
(routing + middleware). `denoteOn` takes that base (the running host passes
`Reactor.Deploy.defaultDeployment`), so the parsed config drives the IO-boundary
dimensions while the verified fourteen-stage fold and router are unchanged. -/

open Proxy (Policy)

/-- The single templated TLS profile a parsed config denotes: a well-formed
TLS-1.3 wildcard profile whose 0-RTT window follows `pc.zeroRtt`. -/
def denoteTls (pc : ParsedConfig) : Dsl.Cfg.TlsCfg :=
  { profiles :=
      [ { name := "profile"
          resumption :=
            { tickets := true, earlyData := pc.zeroRtt
              maxEarlyDataSize := if pc.zeroRtt then 16384 else 0 }
          certs := [ { sni := "*", certRef := "cert", keyRef := "key" } ] } ] }

/-- The single upstream pool a parsed config denotes: the parsed pool name + LB
policy over the proven load-differentiated `Dsl.Cfg.loadedPool` member set. -/
def denotePool (pc : ParsedConfig) : Dsl.Cfg.UpstreamPool :=
  { name := String.mk pc.poolName, pool := Dsl.Cfg.loadedPool, lb := pc.lb }

/-! ### The route dimension a config denotes -/

open Reactor.App (Handler)

/-- Compile a config path token to a `Route.Match.Pat`: a trailing `*` ⇒ a prefix
match over the `/`-split segments before it (empties dropped); otherwise an exact
match over those segments. -/
def patOfTok (t : List Char) : Route.Match.Pat :=
  let star := t.getLast? = some '*'
  let core := if star then t.dropLast else t
  let segs := ((String.mk core).splitOn "/").filter (fun s => s ≠ "")
  if star then Route.Match.Pat.«prefix» segs else Route.Match.Pat.exact segs

/-- Compile a config handler to the deployed `Reactor.App.Handler` it denotes:
`proxy` ⇒ a reverse-proxy over the proven `loadedPool`; `redirect` ⇒ the
`Location`-carrying redirect handler; `respond` ⇒ a fixed local response; `static`
⇒ the embedded static-file handler. -/
def handlerOfSpec : HandlerSpec → Handler
  | .proxy _         => Handler.proxy Dsl.Cfg.loadedPool
  | .redirect st loc => Handler.redirect st (String.mk loc).toUTF8.toList
  | .respond st body => Handler.static st (String.mk body).toUTF8.toList
  | .static          => Handler.staticFile

/-- Compile a config route to the deployed `Route.Match.Route` it denotes. -/
def routeOfSpec (r : RouteSpec) : Route.Match.Route Handler :=
  ⟨patOfTok r.pathTok, handlerOfSpec r.handler⟩

/-! ### The virtual-host dimension a config denotes

Denoted onto the deployed `Reactor.App.Handler.hostGlob` handler — the PROVEN
`RouteAdvanced.dispatch` (host selection `route_host_isolation`, method matching,
`*`/`**` globs). Each `host` opens a `RouteAdvanced.ServerBlock`; its scoped routes
become the block's WIDENED `Reactor.App.VHandler` answers (proxy / redirect / respond /
static), method-guarded — so a virtual host can reverse-proxy / redirect / serve-static
PER HOST, not only respond. -/

/-- Compile a config handler to the widened virtual-host block answer
(`Reactor.App.VHandler`): `proxy` ⇒ a reverse-proxy over the proven `loadedPool`;
`redirect` ⇒ the `Location`-carrying redirect; `respond` ⇒ a fixed local response;
`static` ⇒ the embedded static-file handler. This mirrors the flat `handlerOfSpec`. -/
def vhandlerOfSpec : HandlerSpec → Reactor.App.VHandler
  | .proxy _         => .proxy Dsl.Cfg.loadedPool
  | .redirect st loc => .redirect st (String.mk loc).toUTF8.toList
  | .respond st body => .respond st (String.mk body).toUTF8.toList
  | .static          => .static

/-- Compile a vhost path token to a `RouteAdvanced.PathPat`: a trailing `*` (or the
bare root `/`, which has no explicit segments) ⇒ a globstar prefix match (the host
catch-all); otherwise an exact match over the `/`-split literal segments. -/
def pathPatOf (t : List Char) : RouteAdvanced.PathPat :=
  let star := t.getLast? = some '*'
  let core := if star then t.dropLast else t
  let segs := (((String.mk core).splitOn "/").filter (fun s => s ≠ "")).map RouteAdvanced.SegPat.lit
  { segs := segs, globstar := star || segs.isEmpty }

/-- Compile a vhost method token to a `RouteAdvanced.MethodPat` (`none` ⇒ any method). -/
def methodPatOf : Option (List Char) → RouteAdvanced.MethodPat
  | none   => .anyMethod
  | some m => .exact (String.mk m)

/-- Compile a vhost hostname token to a `RouteAdvanced.HostPat`: `*` ⇒ the fallback
`anyHost`; otherwise an EXACT match over the `.`-split labels (the proven host
discriminator, `RouteAdvanced.route_host_isolation`). -/
def hostPatOf (h : List Char) : RouteAdvanced.HostPat :=
  if h = ['*'] then .anyHost
  else .exact ((String.mk h).splitOn ".")

/-- Compile the optional `header`/`query` guard clauses to the PROVEN
`RouteAdvanced` guards: a `header <name>` clause becomes a `headerPresent` guard on the
LOWER-CASED name (RFC 9110 §5.1 field-name case-insensitivity — deployed header names
arrive canonical lowercase, `Reactor.App.hostReqOf`), a `query <key>` clause becomes a
`queryPresent` guard on the (case-sensitive) key. A route carrying these guards cannot
match a request lacking the header/query (`RouteAdvanced.headerRequired_blocks` /
`queryRequired_blocks`). -/
def guardsOfV (r : VRouteSpec) : List RouteAdvanced.Guard :=
  (match r.headerGuard with
   | none   => []
   | some h => [RouteAdvanced.headerPresent (String.mk (h.map Char.toLower))])
  ++ (match r.queryGuard with
   | none   => []
   | some q => [RouteAdvanced.queryPresent (String.mk q)])

/-- Compile the `middleware <name>` chain to proven per-route middlewares: `bearer-auth`
⇒ the proven `Jwt.authenticate` bearer gate (a rejected token ⇒ 401); any other name ⇒
the fail-closed `501` residual (`Reactor.RouteMw.mwOfName`, the name is carried, not
faked). -/
def mwsOfV (r : VRouteSpec) : List Reactor.RouteMw.RouteMw :=
  r.middleware.map (fun n => Reactor.RouteMw.mwOfName (String.mk n))

/-- Compile a vhost route to the deployed `RouteAdvanced.Route Reactor.App.VHandler` a
`hostGlob` block carries: the method guard, the path pattern, the header/query guards
(`guardsOfV`), and the widened `VHandler` answer — wrapped in the declared per-route
MIDDLEWARE chain (`Reactor.App.VHandler.guarded`) when the route declares any, so the
effective answer is `middleware >>> handler`. A route with no `middleware` clause denotes
byte-identically to the bare handler. -/
def vrouteOf (r : VRouteSpec) : RouteAdvanced.Route Reactor.App.VHandler :=
  { method := methodPatOf r.method
    path := pathPatOf r.pathTok
    guards := guardsOfV r
    handler :=
      match r.middleware with
      | [] => vhandlerOfSpec r.handler
      | _  => Reactor.App.VHandler.guarded (mwsOfV r) (vhandlerOfSpec r.handler) }

/-- **Middleware is live from the parse.** A vhost route declaring a `middleware` chain
denotes to a `Reactor.App.VHandler.guarded` wrapping its handler with the compiled
proven middlewares — so the served answer (`Reactor.App.vhandlerResponse`) runs the
chain (e.g. the bearer gate's 401 on a rejected token) BEFORE the handler. -/
theorem vrouteOf_middleware (r : VRouteSpec) (h : r.middleware ≠ []) :
    (vrouteOf r).handler
      = Reactor.App.VHandler.guarded (mwsOfV r) (vhandlerOfSpec r.handler) := by
  show (match r.middleware with
        | [] => vhandlerOfSpec r.handler
        | _ => Reactor.App.VHandler.guarded (mwsOfV r) (vhandlerOfSpec r.handler)) = _
  cases hm : r.middleware with
  | nil => exact absurd hm h
  | cons a t => rfl

/-- A route with no `middleware` clause denotes byte-identically to its bare handler —
the no-middleware default is unchanged. -/
theorem vrouteOf_no_middleware (r : VRouteSpec) (h : r.middleware = []) :
    (vrouteOf r).handler = vhandlerOfSpec r.handler := by
  show (match r.middleware with
        | [] => vhandlerOfSpec r.handler
        | _ => Reactor.App.VHandler.guarded (mwsOfV r) (vhandlerOfSpec r.handler)) = _
  rw [h]

/-- **`bearer-auth` compiles to the PROVEN bearer gate.** The single-name middleware
chain `[bearer-auth]` denotes to `[Reactor.RouteMw.RouteMw.bearerAuth]` — the deployed
`Jwt.authenticate` gate, not a fresh unverified auth. -/
theorem mwsOfV_bearer (r : VRouteSpec)
    (h : r.middleware = [['b','e','a','r','e','r','-','a','u','t','h']]) :
    mwsOfV r = [Reactor.RouteMw.RouteMw.bearerAuth] := by
  unfold mwsOfV
  rw [h]; decide

/-- Fold one vhost item into the block list: a `host` header opens a new (empty)
block; a `route` appends to the current (most recently opened) block, or opens an
implicit `anyHost` block if none is open yet. -/
def pushVItem (acc : List (RouteAdvanced.ServerBlock Reactor.App.VHandler)) :
    VItem → List (RouteAdvanced.ServerBlock Reactor.App.VHandler)
  | .host h  => acc ++ [{ host := hostPatOf h, routes := [] }]
  | .route r =>
    match acc.reverse with
    | []      => [{ host := .anyHost, routes := [vrouteOf r] }]
    | b :: bs => bs.reverse ++ [{ b with routes := b.routes ++ [vrouteOf r] }]

/-- Denote the vhost item list to the deployed two-level virtual-host block table.
`RouteAdvanced.dispatch` over these blocks is the proven host + method + glob matcher
the `Handler.hostGlob` served path (`Reactor.App.responseOfReq`) drives. -/
def denoteVHosts (its : List VItem) : List (RouteAdvanced.ServerBlock Reactor.App.VHandler) :=
  its.foldl pushVItem []

/-! ### The proxy-vhost hostname projection (surfaced to the running host)

The `hostGlob` served path answers a `proxy` block route with a `502` placeholder; the
real reverse-proxy forward happens host-side, keyed on the request `Host`. So the
deployment surfaces the set of hostnames whose virtual-host block declares a `proxy`
route — the running host reads the request `Host` header and, when it names one of
these, forwards to the configured backend fleet (the proven `drorb_proxy_pick` still
chooses the backend). Fold the item stream tracking the open host block; emit a
hostname the first time a `proxy` route is seen under it. -/

/-- Accumulator step: `(current open host?, hosts-with-a-proxy-route)`. -/
def pushProxyHost (st : Option (List Char) × List (List Char)) :
    VItem → Option (List Char) × List (List Char)
  | .host h  => (some h, st.2)
  | .route r =>
    match r.handler, st.1 with
    | .proxy _, some h => (st.1, if st.2.contains h then st.2 else st.2 ++ [h])
    | _,        _      => st

/-- The hostnames (as strings) whose declared virtual-host block carries a reverse-proxy
route — surfaced to the running host so a request to that `Host` is forwarded. -/
def proxyVHostNames (its : List VItem) : List String :=
  (its.foldl pushProxyHost (none, [])).2.map String.mk

/-- The routing dimension a parsed config denotes onto `base`: the config's flat
routes (compiled to deployed handlers) REPLACE the base route table when the config
declares any, and a declared virtual-host dimension REPLACES the default handler with
the proven host/method/glob `Handler.hostGlob` over the denoted blocks. A config that
declares neither keeps `base`'s routing verbatim — the byte-identical default. -/
def denoteRoutes (base : DeploymentConfig) (pc : ParsedConfig) : Dsl.Cfg.RouteCfg :=
  match pc.routes, pc.vitems with
  | [],     []     => base.routing
  | _ :: _, []     => { base.routing with routes := pc.routes.map routeOfSpec }
  | [],     _ :: _ => { base.routing with defaultHandler := Handler.hostGlob (denoteVHosts pc.vitems) }
  | _ :: _, _ :: _ => { base.routing with routes := pc.routes.map routeOfSpec,
                                          defaultHandler := Handler.hostGlob (denoteVHosts pc.vitems) }

/-- **Denote a parsed config onto a base deployment.** The listener accept surface
(addr/port/L4), the upstream pool + LB policy, the TLS profile, and now the ROUTE
table come from the parsed data; the middleware dimension (the proven fourteen-stage
byte pipeline) is `base`'s, unchanged. A config that declares no routes keeps
`base`'s routing verbatim (the byte-identical default). -/
def denoteOn (base : DeploymentConfig) (pc : ParsedConfig) : DeploymentConfig :=
  { base with
    listener :=
      { base.listener with
        addr := String.mk pc.addr
        port := pc.port
        tlsProfile := some "profile"
        l4 := pc.l4.map (fun m => { upstream := String.mk pc.poolName, mode := m }) }
    routing := denoteRoutes base pc
    upstream := { pools := [denotePool pc] }
    tls := denoteTls pc }

/-- **No routing regression.** A config that declares no flat routes AND no
virtual-host dimension denotes to `base`'s routing dimension verbatim — the deployed
demo route table, default handler, and admission-key adapter are untouched (the
byte-identical default). -/
theorem denoteOn_routing_default (base : DeploymentConfig) (pc : ParsedConfig)
    (hr : pc.routes = []) (hv : pc.vitems = []) : (denoteOn base pc).routing = base.routing := by
  show denoteRoutes base pc = base.routing
  unfold denoteRoutes; rw [hr, hv]

/-- **The route table is live from the parse.** A config that declares flat routes
denotes to exactly those routes (compiled by `routeOfSpec`) as the deployed route
table — so the running `Reactor.App.handle` router selects among the operator's
declared routes, not the demo table. (Independent of the vhost dimension, which
touches only the default handler.) -/
theorem denoteOn_routes (base : DeploymentConfig) (pc : ParsedConfig)
    (h : pc.routes ≠ []) :
    (denoteOn base pc).routing.routes = pc.routes.map routeOfSpec := by
  show (denoteRoutes base pc).routes = _
  unfold denoteRoutes
  cases hpc : pc.routes with
  | nil => exact absurd hpc h
  | cons a t => cases pc.vitems <;> rfl

/-- **The virtual-host dimension is live from the parse.** A config that declares a
vhost dimension denotes its default handler to the proven host/method/glob
`Handler.hostGlob` over the denoted blocks — so an admitted-but-unmatched request is
routed by `RouteAdvanced.dispatch` (host selection, method guard, glob) over exactly
the operator's declared virtual hosts. -/
theorem denoteOn_vhosts (base : DeploymentConfig) (pc : ParsedConfig)
    (h : pc.vitems ≠ []) :
    (denoteOn base pc).routing.defaultHandler = Handler.hostGlob (denoteVHosts pc.vitems) := by
  show (denoteRoutes base pc).defaultHandler = _
  unfold denoteRoutes
  cases hv : pc.vitems with
  | nil => exact absurd hv h
  | cons a t => cases pc.routes <;> rfl

/-- **Parse a config string to a `DeploymentConfig`** over a base deployment. -/
def parseOn (base : DeploymentConfig) (s : String) : Option DeploymentConfig :=
  (parseChars s.data).map (denoteOn base)

/-- **Parse-soundness at the deployment level.** A well-formed parsed config
renders to a string `parseOn` maps to exactly its denotation — the running host
recovers the deployment the operator wrote. -/
theorem parseOn_render (base : DeploymentConfig) (pc : ParsedConfig) (h : WF pc) :
    parseOn base (render pc) = some (denoteOn base pc) := by
  unfold parseOn render
  show (parseChars (String.mk (renderChars pc)).data).map (denoteOn base) = _
  rw [show (String.mk (renderChars pc)).data = renderChars pc from rfl, parse_render pc h]
  rfl

/-- **The LB projection is live from the parse.** The denoted deployment's dial
chain for the parsed pool name is exactly the parsed LB policy's proven selector —
so the running reverse-proxy dial (`serveStepWith`) runs the config-declared
policy. -/
theorem denoteOn_dialChain (base : DeploymentConfig) (pc : ParsedConfig) :
    (denoteOn base pc).dialChain (String.mk pc.poolName) = [pc.lb.toProxy] := by
  show (denoteOn base pc).upstream.dialChain (String.mk pc.poolName) = _
  unfold denoteOn Dsl.Cfg.UpstreamCfg.dialChain Dsl.Cfg.UpstreamCfg.byName denotePool
  simp only [List.find?_cons, beq_self_eq_true, if_pos]
  rfl

/-! ## The proxy-policy byte codec — the seam value the host caches

The running host cannot hold a Lean `DeploymentConfig` across FFI calls, so at boot
it crosses `drorb_deployment_of_config` once, which emits the parsed pool's LB
policy as a single byte. Each proxied request then threads that byte to the step
seam, which decodes it back to the same proven `Policy` chain — `policyOfByte`
inverts `policyByteN`, so the running dial provably runs the config's policy. -/

/-- Encode a proven `Policy` as a byte value. -/
def policyByteN : Policy → Nat
  | .weightedRoundRobin        => 0
  | .leastConnections          => 1
  | .weightedLeastConnections  => 2
  | .rendezvousHash            => 3

/-- Decode a byte value back to a proven `Policy` (unknown ⇒ the default hash). -/
def policyOfByte : Nat → Policy
  | 0 => .weightedRoundRobin
  | 1 => .leastConnections
  | 2 => .weightedLeastConnections
  | _ => .rendezvousHash

/-- The single-link policy chain a byte denotes — the value threaded to
`serveStepWith`. -/
def dialChainOfByte (n : Nat) : List Policy := [policyOfByte n]

/-- **The byte codec round-trips.** Decoding the encoding of any policy recovers
it, so the running step dials the exact config-declared policy. -/
theorem policyOfByte_byteN (p : Policy) : policyOfByte (policyByteN p) = p := by
  cases p <;> rfl

/-- **The end-to-end config→dial link.** The chain the step seam runs from the
config's LB policy byte is exactly the denoted deployment's dial chain for the
parsed pool. -/
theorem dialChainOfByte_denote (base : DeploymentConfig) (pc : ParsedConfig) :
    dialChainOfByte (policyByteN pc.lb.toProxy) = (denoteOn base pc).dialChain (String.mk pc.poolName) := by
  rw [denoteOn_dialChain, dialChainOfByte, policyOfByte_byteN]

end Dsl.Config
