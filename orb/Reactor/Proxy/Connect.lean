import Proxy.Basic
import Proto.Kernel.Shortcuts

/-!
# Reactor.Proxy.Connect — the CONNECT-tunnel admission gate (default-deny) + blind relay

The HTTP `CONNECT` method asks the edge to open a bidirectional TCP tunnel to a
named `host:port` target and thereafter blindly forward bytes in both directions
(RFC 9110 §9.3.6). The dangerous part is *which* targets the edge will tunnel to:
"There are significant risks in establishing a tunnel to arbitrary servers …
Proxies that support CONNECT SHOULD restrict its use to a limited set of known
ports or a configurable list of safe request targets."

This module is the enforcement surface for that recommendation, split the same
way every other reactor decision is: the CORE decides *whether* a target is
admissible (a pure, proven predicate over an access-control list); the HOST owns
the socket and runs the byte pump once the core says `tunnel`.

## The gate

An `Acl` is `(allow, deny, defaultAllow)`. Admission (`Acl.check`) evaluates in a
fixed order that makes **deny authoritative** and the stance **default-deny**:

  1. **deny wins** — if any deny pattern matches the target, refuse (even if an
     allow pattern would also match, even if `defaultAllow`);
  2. **allow must match** — if the allow list is non-empty, admit iff at least
     one allow pattern matches;
  3. **fallthrough** — an empty allow list falls through to `defaultAllow`.

The canonical `Acl.denyAll` (`allow = deny = []`, `defaultAllow = false`) refuses
every target: an unconfigured edge tunnels to nothing.

## The relay

Once admitted the tunnel is a blind bidirectional pump. `Tunnel` tracks whether
the tunnel is `connected` plus the bytes delivered each way. The two guarantees:
no bytes cross before the tunnel is connected (`gated_no_relay_*`), and once
connected the relay is byte-faithful in both directions (`open_relay_faithful_*`)
— exactly RFC 9110's "blind forwarding of data, in both directions".

## Key theorems

* `deny_wins` — a target matching any deny pattern is refused unconditionally.
* `denyAll_refuses` / `default_deny` — the default ACL admits nothing; a target
  absent from a non-empty allow list (no deny match) is refused.
* `allow_admits` — a target matching an allow pattern (no deny match) is admitted.
* `decide_refused_iff` — `decide` opens a tunnel exactly when `check` holds, and
  refuses with `403` otherwise (a refusal never carries a tunnel).
* `gated_no_relay_up` / `gated_no_relay_down` — no byte escapes a gated tunnel.
* `open_relay_faithful_up` / `open_relay_faithful_down` — a connected tunnel
  relays exactly the input bytes, each direction.

## Boundaries

* Target *parsing* (splitting the request-line `host:port`) is a boundary; the
  byte-level export (`drorb_connect_gate`) does the split, the theorems speak
  over structured `Target`s. Host matching is exact-string / wildcard (glob and
  CIDR are a config-surface extension, not load-bearing here). The transport
  (DNS, TCP handshake) is the host's; the relay is modeled as byte lists.
-/

namespace Reactor.Proxy.Connect

/-- A CONNECT destination: host and TCP port. -/
structure Target where
  host : String
  port : Nat
deriving DecidableEq, Repr

/-- An ACL match pattern. `host = none` matches any host; `port = none` matches
any port. Both `none` is the catch-all pattern. -/
structure Pattern where
  host : Option String
  port : Option Nat
deriving DecidableEq, Repr

/-- Does a pattern match a target? Each axis matches iff it is a wildcard
(`none`) or equals the target's value. -/
def Pattern.matches (p : Pattern) (t : Target) : Bool :=
  (match p.host with | none => true | some h => h == t.host) &&
  (match p.port with | none => true | some q => q == t.port)

/-- An access-control list for CONNECT: an allow list, a deny list, and the
fallthrough stance for an empty allow list. -/
structure Acl where
  allow : List Pattern
  deny : List Pattern
  defaultAllow : Bool
deriving Repr

/-- The admission decision. Deny is authoritative; a non-empty allow list is
must-match-one; an empty allow list falls through to `defaultAllow`. -/
def Acl.check (a : Acl) (t : Target) : Bool :=
  if a.deny.any (·.matches t) then false
  else if a.allow.isEmpty then a.defaultAllow
  else a.allow.any (·.matches t)

/-- The default ACL: no allow, no deny, deny-by-default. Admits nothing. -/
def Acl.denyAll : Acl := { allow := [], deny := [], defaultAllow := false }

/-- An HTTPS-only ACL: admit any host on port 443, nothing else. -/
def Acl.httpsOnly : Acl :=
  { allow := [{ host := none, port := some 443 }], deny := [], defaultAllow := false }

/-- The gate verdict: open a tunnel to the target, or refuse with a status. -/
inductive Verdict where
  | tunnel (t : Target)
  | refused (status : Nat)
deriving DecidableEq, Repr

/-- The CONNECT decision: tunnel iff the ACL admits, else refuse `403`. -/
def decide (a : Acl) (t : Target) : Verdict :=
  if a.check t then .tunnel t else .refused 403

/-! ## Gate theorems -/

/-- **Deny is authoritative.** A target matching any deny pattern is refused,
regardless of the allow list or `defaultAllow`. -/
theorem deny_wins {a : Acl} {t : Target} (h : a.deny.any (·.matches t) = true) :
    a.check t = false := by
  simp only [Acl.check, h, if_true]

/-- A denied target never opens a tunnel. -/
theorem deny_no_tunnel {a : Acl} {t : Target}
    (h : a.deny.any (·.matches t) = true) : ∀ t', decide a t ≠ .tunnel t' := by
  intro t'
  simp only [decide, deny_wins h, Bool.false_eq_true, if_false]
  exact fun h => nomatch h

/-- **Default deny.** The canonical ACL refuses every target. -/
theorem denyAll_refuses (t : Target) : Acl.denyAll.check t = false := by
  simp [Acl.check, Acl.denyAll]

/-- **Default deny, decision level.** The default ACL always yields `refused 403`. -/
theorem denyAll_decide (t : Target) : decide Acl.denyAll t = .refused 403 := by
  simp [decide, denyAll_refuses]

/-- **Allow-list default-deny.** With a non-empty allow list and no deny match, a
target that matches *no* allow pattern is refused: the allow list is itself a
default-deny surface, not an addendum to a permissive base. -/
theorem allow_must_match {a : Acl} {t : Target}
    (hne : a.allow.isEmpty = false)
    (hdeny : a.deny.any (·.matches t) = false)
    (hallow : a.allow.any (·.matches t) = false) :
    a.check t = false := by
  simp [Acl.check, hdeny, hne, hallow]

/-- **Allow admits.** A target matching an allow pattern (and no deny pattern) is
admitted. -/
theorem allow_admits {a : Acl} {t : Target}
    (hdeny : a.deny.any (·.matches t) = false)
    (hallow : a.allow.any (·.matches t) = true) :
    a.check t = true := by
  have hne : a.allow.isEmpty = false := by
    cases hlist : a.allow with
    | nil => rw [hlist] at hallow; simp at hallow
    | cons _ _ => rfl
  simp [Acl.check, hdeny, hne, hallow]

/-- **`decide` tracks `check` exactly**: it opens a tunnel iff admission holds,
and a refusal always carries `403` and never a tunnel. -/
theorem decide_refused_iff {a : Acl} {t : Target} :
    decide a t = .refused 403 ↔ a.check t = false := by
  unfold decide
  cases h : a.check t <;> simp

theorem decide_tunnel_iff {a : Acl} {t : Target} :
    decide a t = .tunnel t ↔ a.check t = true := by
  unfold decide
  cases h : a.check t <;> simp

/-! ## Non-vacuity: concrete admit/deny -/

/-- A disallowed target under the default ACL: refused `403`. -/
example : decide Acl.denyAll { host := "evil.example", port := 22 } = .refused 403 := rfl

/-- An HTTPS target under `httpsOnly`: the tunnel opens. -/
example : decide Acl.httpsOnly { host := "api.internal", port := 443 }
    = .tunnel { host := "api.internal", port := 443 } := rfl

/-- A non-443 target under `httpsOnly`: refused (allow-list default-deny). -/
example : decide Acl.httpsOnly { host := "api.internal", port := 22 } = .refused 403 := rfl

/-- Deny beats allow: a target on both lists is refused. -/
example :
    let a : Acl := { allow := [{ host := none, port := none }],
                     deny := [{ host := some "blocked.example", port := none }],
                     defaultAllow := true }
    decide a { host := "blocked.example", port := 443 } = .refused 403 := rfl

/-! ## The blind bidirectional relay -/

/-- A CONNECT tunnel: whether it is connected, and the bytes delivered each way
(`c2u` client→upstream, `u2c` upstream→client). -/
structure Tunnel where
  connected : Bool
  c2u : List UInt8
  u2c : List UInt8
deriving DecidableEq, Repr

/-- A freshly admitted-but-not-yet-connected tunnel: gated, no bytes. -/
def Tunnel.gated : Tunnel := { connected := false, c2u := [], u2c := [] }

/-- Open the tunnel (the host reports the upstream TCP connect succeeded). -/
def Tunnel.opened : Tunnel := { connected := true, c2u := [], u2c := [] }

/-- Pump client→upstream bytes: appended iff connected, dropped otherwise. -/
def Tunnel.pumpUp (tun : Tunnel) (b : List UInt8) : Tunnel :=
  if tun.connected then { tun with c2u := tun.c2u ++ b } else tun

/-- Pump upstream→client bytes: appended iff connected, dropped otherwise. -/
def Tunnel.pumpDown (tun : Tunnel) (b : List UInt8) : Tunnel :=
  if tun.connected then { tun with u2c := tun.u2c ++ b } else tun

/-- **No relay before connect (up).** A gated tunnel drops client bytes. -/
theorem gated_no_relay_up (b : List UInt8) :
    (Tunnel.gated.pumpUp b).c2u = [] := by
  simp [Tunnel.pumpUp, Tunnel.gated]

/-- **No relay before connect (down).** A gated tunnel drops upstream bytes. -/
theorem gated_no_relay_down (b : List UInt8) :
    (Tunnel.gated.pumpDown b).u2c = [] := by
  simp [Tunnel.pumpDown, Tunnel.gated]

/-- **Faithful blind relay (up).** A connected tunnel delivers exactly the
client bytes upstream. -/
theorem open_relay_faithful_up (b : List UInt8) :
    (Tunnel.opened.pumpUp b).c2u = b := by
  simp [Tunnel.pumpUp, Tunnel.opened]

/-- **Faithful blind relay (down).** A connected tunnel delivers exactly the
upstream bytes to the client. -/
theorem open_relay_faithful_down (b : List UInt8) :
    (Tunnel.opened.pumpDown b).u2c = b := by
  simp [Tunnel.pumpDown, Tunnel.opened]

/-! ## The byte-level host seam -/

/-- Parse a `host:port` target from a line (split on the final colon). `none` on
a missing/non-numeric port. -/
def parseTarget (s : String) : Option Target :=
  match s.splitOn ":" with
  | [h, p] => (p.toNat?).map (fun n => { host := h, port := n })
  | _ => none

/-- Parse an allow-list pattern from a `host:port` line. `*` on either axis is a
wildcard. A malformed line becomes the catch-nothing pattern. -/
def parsePattern (s : String) : Pattern :=
  match s.splitOn ":" with
  | [h, p] =>
    { host := if h == "*" then none else some h,
      port := if p == "*" then none else p.toNat? }
  | _ => { host := some s, port := some 0 }

/-- **The proven CONNECT gate, byte seam.** Input is UTF-8, newline-separated:
line 0 is the `host:port` target, the remaining lines are the allow-list
patterns (`*` = wildcard). The stance is default-deny (empty deny list,
`defaultAllow = false`), so the host contributes only the configured allow
patterns and the parsed target — never the decision. Output is a single byte:
`1` ⇒ open the tunnel, `0` ⇒ refuse `403`. -/
@[export drorb_connect_gate]
def connectGate (input : ByteArray) : ByteArray :=
  let s := (String.fromUTF8? input).getD ""
  let lines := (s.splitOn "\n").filter (· ≠ "")
  match lines with
  | [] => ByteArray.mk #[0]
  | target :: allowLines =>
    match parseTarget target with
    | none => ByteArray.mk #[0]
    | some t =>
      let a : Acl := { allow := allowLines.map parsePattern, deny := [], defaultAllow := false }
      match decide a t with
      | .tunnel _ => ByteArray.mk #[1]
      | .refused _ => ByteArray.mk #[0]

/-! ## Byte-seam behaviour, discharged in the pure kernel

Each concrete `connectGate` verdict runs the whole byte seam — UTF-8 decode
(`String.fromUTF8?`), line/authority splitting (`String.splitOn`), port parsing
(`String.toNat?`), the allow-pattern map, and the ACL decision — end to end. Every
worker on that path bottoms out in a recursion opaque to `decide`/`rfl`, so these once
cost `native_decide` (the compiler, `Lean.ofReduceBool`, in the TCB).

They are closed instead by three PURE-KERNEL routes, in order of preference:

  1. **A library-witness lemma.** The decode is `Proto.Kernel.Shortcuts.fromUTF8?_toUTF8`
     — the round-trip discharged from the UTF-8 validity witness every `String` already
     carries. No byte loop is unrolled at all: the whole `validateUTF8`/`fromUTF8` decode
     collapses to one rewrite, independent of input length.
  2. **The §3 step kit** for `splitOnAux`, still a genuine per-position recursion, whose
     guards kernel-`decide` per step.
  3. **`cbv`** — call-by-value KERNEL evaluation under an explicit `cbv.maxSteps` budget
     — for the port parse, whose worker is a `Slice`/`Iterator` combinator with no step
     kit to unroll.

All three are kernel reduction; the compiler is nowhere.
Axioms ⊆ {propext, Classical.choice, Quot.sound}; no `native_decide`. -/

set_option cbv.maxSteps 20000 in
/-- The `"443".toNat?` port parse, kernel-evaluated (used by both allowed cases). -/
private theorem toNat?_443 : "443".toNat? = some 443 := by cbv

set_option cbv.maxSteps 20000 in
/-- The `"22".toNat?` port parse, kernel-evaluated. -/
private theorem toNat?_22 : "22".toNat? = some 22 := by cbv

open Proto.Kernel.Shortcuts in
/-- **The byte seam refuses an unparseable target line.** A line with no `host:port`
colon fails `parseTarget` and the gate emits the refuse byte `0`. -/
theorem gate_refuses_unparseable :
    (connectGate (String.toUTF8 "not-a-target")).toList = [0] := by
  have hs : String.fromUTF8? (String.toUTF8 "not-a-target") = some "not-a-target" :=
    fromUTF8?_toUTF8 _
  have hnl : "not-a-target".splitOn "\n" = ["not-a-target"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_miss]
  have hcol : "not-a-target".splitOn ":" = ["not-a-target"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_miss]
  have hpt : parseTarget "not-a-target" = none := by
    simp only [parseTarget, hcol]
  have hf : (["not-a-target"].filter (· ≠ "")) = ["not-a-target"] := by decide
  simp only [connectGate, hs, Option.getD_some, hnl, hf, hpt, ba_toList_eq]

open Proto.Kernel.Shortcuts in
/-- **The byte seam opens a tunnel for an allowed target.** `api.internal:443` parses,
the `*:443` allow pattern admits it (wildcard host, port `443`), and the gate emits the
open byte `1`. -/
theorem gate_opens_allowed :
    (connectGate (String.toUTF8 "api.internal:443\n*:443")).toList = [1] := by
  have hs : String.fromUTF8? (String.toUTF8 "api.internal:443\n*:443")
      = some "api.internal:443\n*:443" := fromUTF8?_toUTF8 _
  have hnl : "api.internal:443\n*:443".splitOn "\n" = ["api.internal:443", "*:443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have ht : "api.internal:443".splitOn ":" = ["api.internal", "443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have hp : "*:443".splitOn ":" = ["*", "443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have hpt : parseTarget "api.internal:443" = some { host := "api.internal", port := 443 } := by
    simp (config := { decide := true }) only [parseTarget, ht, toNat?_443, Option.map_some]
  have hpp : parsePattern "*:443" = { host := none, port := some 443 } := by
    simp (config := { decide := true }) only [parsePattern, hp, toNat?_443]
  have hf : (["api.internal:443", "*:443"].filter (· ≠ "")) = ["api.internal:443", "*:443"] := by
    decide
  simp only [connectGate, hs, Option.getD_some, hnl, hf, hpt, List.map_cons, List.map_nil,
    hpp, ba_toList_eq]
  decide

open Proto.Kernel.Shortcuts in
/-- **The byte seam refuses a target absent from the allow list.** `api.internal:22`
parses, but the only allow pattern is `*:443`; the port `22` matches nothing, so the
gate emits the refuse byte `0` (the allow list is a default-deny surface). -/
theorem gate_refuses_unlisted :
    (connectGate (String.toUTF8 "api.internal:22\n*:443")).toList = [0] := by
  have hs : String.fromUTF8? (String.toUTF8 "api.internal:22\n*:443")
      = some "api.internal:22\n*:443" := fromUTF8?_toUTF8 _
  have hnl : "api.internal:22\n*:443".splitOn "\n" = ["api.internal:22", "*:443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have ht : "api.internal:22".splitOn ":" = ["api.internal", "22"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have hp : "*:443".splitOn ":" = ["*", "443"] := by
    simp (config := { decide := true }) only [String.splitOn,
      splitOnAux_stop, splitOnAux_matchend, splitOnAux_miss]
  have hpt : parseTarget "api.internal:22" = some { host := "api.internal", port := 22 } := by
    simp (config := { decide := true }) only [parseTarget, ht, toNat?_22, Option.map_some]
  have hpp : parsePattern "*:443" = { host := none, port := some 443 } := by
    simp (config := { decide := true }) only [parsePattern, hp, toNat?_443]
  have hf : (["api.internal:22", "*:443"].filter (· ≠ "")) = ["api.internal:22", "*:443"] := by
    decide
  simp only [connectGate, hs, Option.getD_some, hnl, hf, hpt, List.map_cons, List.map_nil,
    hpp, ba_toList_eq]
  decide

end Reactor.Proxy.Connect

#print axioms Reactor.Proxy.Connect.gate_refuses_unparseable
#print axioms Reactor.Proxy.Connect.gate_opens_allowed
#print axioms Reactor.Proxy.Connect.gate_refuses_unlisted
