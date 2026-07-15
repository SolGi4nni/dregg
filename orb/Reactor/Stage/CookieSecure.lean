import Reactor.Pipeline

/-!
# Reactor.Stage.CookieSecure — Set-Cookie attribute hardening, as a pipeline stage (ck.1)

An edge that fronts an upstream application often hardens the cookies the upstream sets:
adding the `Secure`, `HttpOnly` and `SameSite` attributes an origin frequently forgets,
so a session cookie cannot be read by script (`HttpOnly`), sent over plaintext
(`Secure`), or attached to cross-site requests (`SameSite=Lax`). drorb modelled cookie
PARSING (`Header.lean`) but had no deployed hardening of the RESPONSE `Set-Cookie` —
this module adds it as a response-phase `Stage`.

Behaviour: the response phase rewrites every `Set-Cookie` header, appending each of the
three attributes THAT IS MISSING (case-insensitive), leaving the `name=value` and any
already-present attributes untouched. Non-`Set-Cookie` headers pass through.

## What is proved

* `harden_prefix` — hardening only APPENDS: the original cookie bytes are a prefix of
  the hardened cookie (the `name=value` and existing attributes are never mutated).
* `harden_has_secure` / `harden_has_httpOnly` / `harden_has_sameSite` — after hardening,
  the cookie contains ALL THREE attribute tokens (case-insensitive), for ANY input.
* `harden_idem` — hardening is idempotent: `harden (harden v) = harden v` (an
  already-hardened cookie is not double-decorated), for ANY input.
* `cookieSecureStage_effect` — the stage's response phase maps `harden` over the
  `Set-Cookie` headers of the finalized response, for ANY tail/handler.
* `demo_hardened` — a weak `Set-Cookie: sid=abc` is served with all three attributes
  (a concrete, non-vacuous end-to-end witness).

All theorems are general (quantified over arbitrary cookie bytes) except the concrete
witnesses; the substring facts ride on the append-monotonicity lemmas below.
-/

namespace Reactor.Stage.CookieSecure

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## Case-insensitive substring search -/

/-- ASCII-lowercase one byte. -/
def lowerByte (b : UInt8) : UInt8 := if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- Is `p` a prefix of `l`? -/
def isPrefix (p l : Bytes) : Bool := p == l.take p.length

/-- Does `needle` occur as a contiguous infix of `hay`? -/
def hasInfix (needle hay : Bytes) : Bool :=
  match hay with
  | [] => needle.isEmpty
  | _ :: t => isPrefix needle hay || hasInfix needle t

/-- Case-insensitive containment: is the (already-lowercase) token `tok` an infix of
`hay` ignoring case? -/
def containsTok (tok hay : Bytes) : Bool := hasInfix tok (lower hay)

/-! ### Append-monotonicity of substring search -/

/-- `lower` distributes over append. -/
theorem lower_append (a b : Bytes) : lower (a ++ b) = lower a ++ lower b := by
  simp [lower, List.map_append]

/-- A prefix of `a` is a prefix of `a ++ b`. -/
theorem isPrefix_append (p a b : Bytes) (h : isPrefix p a = true) :
    isPrefix p (a ++ b) = true := by
  simp only [isPrefix, beq_iff_eq] at h ⊢
  have hlen : p.length ≤ a.length := by
    have hl := congrArg List.length h
    rw [List.length_take] at hl
    omega
  rw [List.take_append_of_le_length hlen]
  exact h

/-- Infix membership survives appending on the right (`n ∈ a ⇒ n ∈ a ++ b`). -/
theorem hasInfix_append_left (n a b : Bytes) (h : hasInfix n a = true) :
    hasInfix n (a ++ b) = true := by
  induction a with
  | nil =>
    simp only [hasInfix, List.isEmpty_iff] at h
    subst h
    cases b with
    | nil => rfl
    | cons x t => simp [hasInfix, isPrefix]
  | cons x t ih =>
    simp only [List.cons_append, hasInfix, Bool.or_eq_true] at h ⊢
    rcases h with hp | hi
    · exact Or.inl (isPrefix_append n (x :: t) b hp)
    · exact Or.inr (ih hi)

/-- Infix membership survives appending on the left (`n ∈ b ⇒ n ∈ a ++ b`). -/
theorem hasInfix_append_right (n a b : Bytes) (h : hasInfix n b = true) :
    hasInfix n (a ++ b) = true := by
  induction a with
  | nil => simpa using h
  | cons x t ih =>
    simp only [List.cons_append, hasInfix, Bool.or_eq_true]
    exact Or.inr ih

/-! ## The attribute tokens and suffixes -/

-- Tokens/suffixes are explicit ASCII byte lists (NOT `String.toUTF8.toList`, which is
-- `@[extern]` and does not reduce in the kernel — `decide`/`rfl` need reducible bytes).

/-- Lowercase token searched for `Secure` (ASCII `"secure"`). -/
def secureTok : Bytes := [115, 101, 99, 117, 114, 101]
/-- Lowercase token searched for `HttpOnly` (ASCII `"httponly"`). -/
def httpOnlyTok : Bytes := [104, 116, 116, 112, 111, 110, 108, 121]
/-- Lowercase token searched for `SameSite` (ASCII `"samesite"`). -/
def sameSiteTok : Bytes := [115, 97, 109, 101, 115, 105, 116, 101]

/-- Appended when `Secure` is missing (ASCII `"; Secure"`). -/
def secureSuffix : Bytes := [59, 32, 83, 101, 99, 117, 114, 101]
/-- Appended when `HttpOnly` is missing (ASCII `"; HttpOnly"`). -/
def httpOnlySuffix : Bytes := [59, 32, 72, 116, 116, 112, 79, 110, 108, 121]
/-- Appended when `SameSite` is missing (ASCII `"; SameSite=Lax"`). -/
def sameSiteSuffix : Bytes := [59, 32, 83, 97, 109, 101, 83, 105, 116, 101, 61, 76, 97, 120]

/-- Append `suf` to `v` unless `v` already contains `tok` (case-insensitive). -/
def addIfMissing (tok suf v : Bytes) : Bytes :=
  if containsTok tok v then v else v ++ suf

/-- **Harden a cookie value.** Ensure `Secure`, `HttpOnly` and `SameSite` are present,
appending each missing attribute; present attributes and the `name=value` are untouched. -/
def harden (v : Bytes) : Bytes :=
  addIfMissing sameSiteTok sameSiteSuffix
    (addIfMissing httpOnlyTok httpOnlySuffix
      (addIfMissing secureTok secureSuffix v))

/-- `harden` unfolded to its three-step composition (definitional). -/
theorem harden_eq (v : Bytes) :
    harden v = addIfMissing sameSiteTok sameSiteSuffix
      (addIfMissing httpOnlyTok httpOnlySuffix
        (addIfMissing secureTok secureSuffix v)) := rfl

/-! ## General properties of `harden` -/

/-- Each suffix genuinely carries its token (kernel-decided). -/
theorem secureSuffix_has : containsTok secureTok secureSuffix = true := by decide
theorem httpOnlySuffix_has : containsTok httpOnlyTok httpOnlySuffix = true := by decide
theorem sameSiteSuffix_has : containsTok sameSiteTok sameSiteSuffix = true := by decide

/-- `addIfMissing` only appends: `v` is a prefix of its result. -/
theorem addIfMissing_prefix (tok suf v : Bytes) : v <+: addIfMissing tok suf v := by
  unfold addIfMissing
  by_cases h : containsTok tok v = true
  · rw [if_pos h]; exact List.prefix_refl v
  · rw [if_neg h]; exact List.prefix_append v suf

/-- `harden` only appends: `v` is a prefix of `harden v` (the `name=value` and existing
attributes are preserved verbatim). -/
theorem harden_prefix (v : Bytes) : v <+: harden v := by
  unfold harden
  exact ((addIfMissing_prefix secureTok secureSuffix v).trans
          (addIfMissing_prefix httpOnlyTok httpOnlySuffix _)).trans
          (addIfMissing_prefix sameSiteTok sameSiteSuffix _)

/-- After `addIfMissing tok suf`, the result contains `tok` — provided the suffix does. -/
theorem addIfMissing_contains (tok suf v : Bytes) (hsuf : containsTok tok suf = true) :
    containsTok tok (addIfMissing tok suf v) = true := by
  unfold addIfMissing
  by_cases h : containsTok tok v = true
  · rw [if_pos h]; exact h
  · rw [if_neg h]
    unfold containsTok at hsuf ⊢
    rw [lower_append]
    exact hasInfix_append_right tok (lower v) (lower suf) hsuf

/-- Containment of a token survives a later `addIfMissing` (which only appends). -/
theorem addIfMissing_preserves (tok tok' suf' v : Bytes)
    (h : containsTok tok v = true) :
    containsTok tok (addIfMissing tok' suf' v) = true := by
  unfold addIfMissing
  by_cases hc : containsTok tok' v = true
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]
    unfold containsTok at h ⊢
    rw [lower_append]
    exact hasInfix_append_left tok (lower v) (lower suf') h

/-- After hardening, the cookie contains the `SameSite` attribute (case-insensitive). -/
theorem harden_has_sameSite (v : Bytes) : containsTok sameSiteTok (harden v) = true := by
  unfold harden
  exact addIfMissing_contains sameSiteTok sameSiteSuffix _ sameSiteSuffix_has

/-- After hardening, the cookie contains the `HttpOnly` attribute (case-insensitive). -/
theorem harden_has_httpOnly (v : Bytes) : containsTok httpOnlyTok (harden v) = true := by
  unfold harden
  exact addIfMissing_preserves httpOnlyTok sameSiteTok sameSiteSuffix _
    (addIfMissing_contains httpOnlyTok httpOnlySuffix _ httpOnlySuffix_has)

/-- After hardening, the cookie contains the `Secure` attribute (case-insensitive). -/
theorem harden_has_secure (v : Bytes) : containsTok secureTok (harden v) = true := by
  unfold harden
  exact addIfMissing_preserves secureTok sameSiteTok sameSiteSuffix _
    (addIfMissing_preserves secureTok httpOnlyTok httpOnlySuffix _
      (addIfMissing_contains secureTok secureSuffix _ secureSuffix_has))

/-- `addIfMissing` is a no-op when the token is already present. -/
theorem addIfMissing_noop (tok suf v : Bytes) (h : containsTok tok v = true) :
    addIfMissing tok suf v = v := by
  unfold addIfMissing; rw [if_pos h]

/-- **Idempotence.** Hardening an already-hardened cookie changes nothing — no attribute
is double-appended, for ANY input. -/
theorem harden_idem (v : Bytes) : harden (harden v) = harden v := by
  rw [harden_eq (harden v),
      addIfMissing_noop secureTok secureSuffix (harden v) (harden_has_secure v),
      addIfMissing_noop httpOnlyTok httpOnlySuffix (harden v) (harden_has_httpOnly v),
      addIfMissing_noop sameSiteTok sameSiteSuffix (harden v) (harden_has_sameSite v)]

/-! ## The stage -/

/-- Lowercase token for the header name `Set-Cookie` (ASCII `"set-cookie"`). -/
def setCookieTok : Bytes := [115, 101, 116, 45, 99, 111, 111, 107, 105, 101]

/-- Is this header a `Set-Cookie` (case-insensitive)? -/
def isSetCookie (name : Bytes) : Bool := lower name == setCookieTok

/-- Harden one header: rewrite a `Set-Cookie` value, pass anything else through. -/
def hardenHeader (nv : Bytes × Bytes) : Bytes × Bytes :=
  if isSetCookie nv.1 then (nv.1, harden nv.2) else nv

/-- **The cookie-hardening stage.** Request phase: pass through. Response phase: map
`hardenHeader` over the response's headers (one affine `mapResp`), so every `Set-Cookie`
carries `Secure`/`HttpOnly`/`SameSite`. Never gates. -/
def cookieSecureStage : Stage where
  name := "cookie-secure"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp (fun r => { r with headers := r.headers.map hardenHeader })

/-- **The byte-effect.** The stage maps `hardenHeader` over the finalized response's
headers, for ANY tail and handler. -/
theorem cookieSecureStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (cookieSecureStage :: rest) h c).build).headers
      = ((runPipeline rest h c).build).headers.map hardenHeader := by
  rw [pipeline_stage_effect cookieSecureStage rest h c c rfl]
  rfl

/-! ## End-to-end witness -/

/-- A weak cookie the upstream sets with no security attributes (`Set-Cookie: sid=abc`),
as explicit ASCII bytes. -/
def weakName : Bytes := [83, 101, 116, 45, 67, 111, 111, 107, 105, 101]
def weakVal : Bytes := [115, 105, 100, 61, 97, 98, 99]

/-- A handler that sets exactly the weak cookie. -/
def cookieHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [(weakName, weakVal)], body := [] }

/-- An empty request context. -/
def demoCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- **End-to-end.** The single-stage pipeline serves the weak cookie hardened: the
finalized response's `Set-Cookie` is `harden "sid=abc"`, which carries all three
attributes — a concrete, non-vacuous witness. -/
theorem demo_hardened :
    ((runPipeline [cookieSecureStage] cookieHandler demoCtx).build).headers
      = [(weakName, harden weakVal)] := by
  rw [cookieSecureStage_effect]
  rfl

/-- The served hardened cookie genuinely carries all three attributes. -/
theorem demo_hardened_flags :
    containsTok secureTok (harden weakVal) = true
      ∧ containsTok httpOnlyTok (harden weakVal) = true
      ∧ containsTok sameSiteTok (harden weakVal) = true := by
  decide

end Reactor.Stage.CookieSecure
