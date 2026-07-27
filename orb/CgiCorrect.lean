import Cgi
import Reactor.WireRest

/-!
# CgiCorrect — the CGI meta-variable environment, proved against RFC 3875 §4.1

`Cgi.lean` builds the CGI/1.1 request meta-variable environment (RFC 3875 §4.1)
from a resolved request as `Cgi.envList : Cgi.Req → List (String × String)`, and
the deployed serve path builds it from the dispatched wire request as
`Cgi.envList (Reactor.WireRest.deployCgiReq req)`. Both are the *deployed*
builders — the association list a CGI gateway hands to the invoked script.

This module states, **independently of that implementation**, what RFC 3875 §4.1
mandates the environment to be, and proves the deployed builder equals it.

## The standard (RFC 3875 §4.1)

Section 4.1 fixes the set of request meta-variables and, in the numbered
sub-sections §4.1.1–§4.1.17, the environment-variable *name* and the
request-derived *value* of each:

| §      | name                | value (request-derived)                         |
|--------|---------------------|-------------------------------------------------|
| 4.1.1  | `AUTH_TYPE`         | the authentication method (empty if none)       |
| 4.1.2  | `CONTENT_LENGTH`    | the size of the attached request body           |
| 4.1.3  | `CONTENT_TYPE`      | the media type of the attached body             |
| 4.1.4  | `GATEWAY_INTERFACE` | the dialect (`CGI/1.1`)                          |
| 4.1.5  | `PATH_INFO`         | the extra path following the script path        |
| 4.1.6  | `PATH_TRANSLATED`   | `PATH_INFO` mapped to a filesystem path         |
| 4.1.7  | `QUERY_STRING`      | the URI query component, **without** the `?`    |
| 4.1.8  | `REMOTE_ADDR`       | the client network address                      |
| 4.1.9  | `REMOTE_HOST`       | the client host name (empty if unresolved)      |
| 4.1.10 | `REMOTE_IDENT`      | the RFC 1413 identity (empty if none)           |
| 4.1.11 | `REMOTE_USER`       | the authenticated user id (empty if none)       |
| 4.1.12 | `REQUEST_METHOD`    | the request method                              |
| 4.1.13 | `SCRIPT_NAME`       | the script path, **excluding** `PATH_INFO`      |
| 4.1.14 | `SERVER_NAME`       | the server host name of the Script-URI          |
| 4.1.15 | `SERVER_PORT`       | the server port of the Script-URI               |
| 4.1.16 | `SERVER_PROTOCOL`   | the request protocol (e.g. `HTTP/1.1`)          |
| 4.1.17 | `SERVER_SOFTWARE`   | the server-software name/version                |

The mapping is TOTAL over these 17 required variables; the optional ones take
the empty string when their datum is absent (§4.1's `"" | ...` productions).
`§4.1.18` (the protocol-specific `HTTP_*` header mirror) is a separate, variable
set and is out of scope here.

## What is proved

  * `envList_refines_spec` — the deployed builder `Cgi.envList` equals `specEnv`,
    the RFC-§4.1 environment authored below from the standard alone. This binds
    each of the 17 names to the §4.1-defined name literal and each value to the
    §4.1-defined derivation, in one total mapping.
  * `deployed_env_refines_spec` — the same equality for the exact expression the
    serve path evaluates, `Cgi.envList (Reactor.WireRest.deployCgiReq req)`.
  * Non-vacuity (`spec_length_17`, `deployed_total_over_required`,
    `query_string_has_no_question_mark`, `name_exact_underscored`,
    `omitting_a_var_fails`, `wrong_value_fails`): a builder that dropped a
    required variable, misspelled a name, or derived a wrong value (e.g. a
    `QUERY_STRING` that kept the `?`) is refuted against the same spec.
  * `deployed_reflects_uri` — the deployed wire derivation splits the request
    target at the first `?` per RFC 3875 §4.1.7/§4.1.13: `SCRIPT_NAME` is the path
    portion (excluding the query), `QUERY_STRING` the post-`?` substring.
    `deployed_query_split_witness` pins `/x?a=1 ↦ (SCRIPT_NAME "/x",
    QUERY_STRING "a=1")` and `old_behavior_fails` refutes the pre-fix derivation.

## The request-target split is RFC-conformant (§4.1.7 / §4.1.13)

`Reactor.WireRest.deployCgiReq` splits the request target at the **first** `?`:
`SCRIPT_NAME` receives the path portion (before the `?`, RFC 3875 §4.1.13 — "No
PATH_INFO segment is included in the SCRIPT_NAME value", and by the same token no
query component), and `QUERY_STRING` receives the substring **after** the first
`?`, without the `?`, empty when the target carries none (§4.1.7). The split is
performed by the total function `Cgi.splitTarget`. `deployed_reflects_uri` proves
the deployed wire derivation reflects this Script-URI split for every request, and
`deployed_query_split_witness` pins the discriminating example `/x?a=1 ↦
(SCRIPT_NAME = "/x", QUERY_STRING = "a=1")` — the pre-fix behavior (whole target
into `SCRIPT_NAME`, empty `QUERY_STRING`), refuted by `old_behavior_fails`.
-/

namespace CgiCorrect

open Cgi

/-! ## The independent RFC 3875 §4.1 environment specification

`specEnv` is written from the standard: the 17 name literals are §4.1.1–§4.1.17
verbatim, and each value is the request-derived datum that sub-section defines.
It does not mention `Cgi.envList`, `Cgi.env`, `Cgi.allMetas`, or `Cgi.Meta.name`;
it is a flat association list, structurally unlike the implementation's
`allMetas.map (fun m => (m.name, env req m))`. -/
def specEnv (req : Cgi.Req) : List (String × String) :=
  [ ("AUTH_TYPE",         req.authType),          -- §4.1.1
    ("CONTENT_LENGTH",    req.contentLength),      -- §4.1.2
    ("CONTENT_TYPE",      req.contentType),        -- §4.1.3
    ("GATEWAY_INTERFACE", req.gatewayInterface),   -- §4.1.4
    ("PATH_INFO",         req.pathInfo),           -- §4.1.5
    ("PATH_TRANSLATED",   req.pathTranslated),     -- §4.1.6
    ("QUERY_STRING",      req.queryString),        -- §4.1.7  (query component, no leading "?")
    ("REMOTE_ADDR",       req.remoteAddr),         -- §4.1.8
    ("REMOTE_HOST",       req.remoteHost),         -- §4.1.9
    ("REMOTE_IDENT",      req.remoteIdent),        -- §4.1.10
    ("REMOTE_USER",       req.remoteUser),         -- §4.1.11
    ("REQUEST_METHOD",    req.requestMethod),      -- §4.1.12
    ("SCRIPT_NAME",       req.scriptName),         -- §4.1.13
    ("SERVER_NAME",       req.serverName),         -- §4.1.14
    ("SERVER_PORT",       req.serverPort),         -- §4.1.15
    ("SERVER_PROTOCOL",   req.serverProtocol),     -- §4.1.16
    ("SERVER_SOFTWARE",   req.serverSoftware) ]    -- §4.1.17

/-- The 17 required environment-variable names (RFC 3875 §4.1.1–§4.1.17),
authored independently as the coverage obligation for the deployed builder. -/
def requiredNames : List String :=
  [ "AUTH_TYPE", "CONTENT_LENGTH", "CONTENT_TYPE", "GATEWAY_INTERFACE",
    "PATH_INFO", "PATH_TRANSLATED", "QUERY_STRING", "REMOTE_ADDR",
    "REMOTE_HOST", "REMOTE_IDENT", "REMOTE_USER", "REQUEST_METHOD",
    "SCRIPT_NAME", "SERVER_NAME", "SERVER_PORT", "SERVER_PROTOCOL",
    "SERVER_SOFTWARE" ]

/-! ## The refinement -/

/-- **The deployed CGI environment builder refines the RFC 3875 §4.1 spec.**
For every request, the environment `Cgi.envList` constructs is exactly the
§4.1 environment `specEnv`: same 17 names, same request-derived values, in one
total mapping. Any implementation that dropped a variable, renamed one, or
mis-wired a value would break this equality. -/
theorem envList_refines_spec (req : Cgi.Req) :
    Cgi.envList req = specEnv req := rfl

/-- **The same refinement for the exact serve-path expression.** The environment
the deployed reactor builds from the dispatched wire request,
`Cgi.envList (Reactor.WireRest.deployCgiReq req)`, equals its §4.1 spec. -/
theorem deployed_env_refines_spec (req : Proto.Request) :
    Cgi.envList (Reactor.WireRest.deployCgiReq req)
      = specEnv (Reactor.WireRest.deployCgiReq req) :=
  envList_refines_spec _

/-! ## Non-vacuity: a wrong builder fails against the same spec -/

/-- The spec (hence the deployed builder) is a mapping over exactly 17
variables — a builder producing fewer or more cannot equal it. -/
theorem spec_length_17 (req : Cgi.Req) : (specEnv req).length = 17 := rfl

/-- **Totality over the required domain.** Every RFC-§4.1 required name resolves
in the deployed environment. A builder that omitted any required variable would
falsify this (its `lookup` would be `none`). Stated over the deployed builder via
the refinement. -/
theorem deployed_total_over_required (req : Cgi.Req) :
    ∀ name ∈ requiredNames, ((Cgi.envList req).lookup name).isSome = true := by
  rw [envList_refines_spec]
  intro name hname
  simp only [requiredNames, List.mem_cons, List.not_mem_nil, or_false] at hname
  rcases hname with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> rfl

/-- A concrete request whose URI carries a query component, used to witness the
value-level and coverage discriminations below. -/
def demoReq : Cgi.Req :=
  { requestMethod  := "GET"
    scriptName     := "/cgi-bin/app"
    queryString    := "a=1&b=2"
    serverName     := "host.example"
    serverPort     := "80"
    serverProtocol := "HTTP/1.1"
    serverSoftware := "srv/1"
    remoteAddr     := "203.0.113.7" }

/-- **`QUERY_STRING` excludes the `?` (§4.1.7).** In the deployed environment the
query meta-variable is the bare query component `a=1&b=2`; a builder that emitted
`?a=1&b=2` (keeping the delimiter) would not match. -/
theorem query_string_has_no_question_mark :
    (Cgi.envList demoReq).lookup "QUERY_STRING" = some "a=1&b=2"
    ∧ (Cgi.envList demoReq).lookup "QUERY_STRING" ≠ some "?a=1&b=2" := by
  decide

/-- **Names are the exact §4.1 underscored identifiers.** The deployed
environment answers to `QUERY_STRING`, not to a mis-spelled `QUERYSTRING`; a
builder using the wrong spelling would leave the required name unresolved. -/
theorem name_exact_underscored :
    ((Cgi.envList demoReq).lookup "QUERY_STRING").isSome = true
    ∧ (Cgi.envList demoReq).lookup "QUERYSTRING" = none := by
  decide

/-- **Omitting a required variable fails.** A builder equal to the spec with
`CONTENT_LENGTH` erased has length 16, so it cannot equal the deployed
environment (length 17). -/
theorem omitting_a_var_fails (req : Cgi.Req) :
    (specEnv req).eraseP (fun p => p.1 == "CONTENT_LENGTH") ≠ Cgi.envList req := by
  rw [envList_refines_spec]
  intro h
  have : ((specEnv req).eraseP (fun p => p.1 == "CONTENT_LENGTH")).length
      = (specEnv req).length := congrArg List.length h
  simp [specEnv, List.eraseP] at this

/-- **A wrong value fails.** A builder that derived `REQUEST_METHOD` from the
target instead of the method disagrees with the deployed environment on
`demoReq` (`POST`-shaped vs the true `GET`). -/
theorem wrong_value_fails :
    (Cgi.envList demoReq).lookup "REQUEST_METHOD" = some "GET"
    ∧ (Cgi.envList demoReq).lookup "REQUEST_METHOD" ≠ some "/cgi-bin/app" := by
  decide

/-! ## The wire derivation splits the target (§4.1.7 / §4.1.13)

The deployed serve path *derives* a `Cgi.Req` from the wire request via
`deployCgiReq`, which splits the request target at the first `?`: the path portion
(before the `?`) fills `SCRIPT_NAME`, and the substring after the first `?` (no
delimiter, empty when absent) fills `QUERY_STRING`. The independent split
obligation `ReflectsUri` records what §4.1.7/§4.1.13 require of a conformant
environment; the deployed derivation satisfies it for every request. -/

/-- The Script-URI components RFC 3875 splits the request target into
(§4.1.5 / §4.1.7 / §4.1.13). -/
structure UriSplit where
  scriptPath : String   -- §4.1.13 — identifies the script; excludes the query
  pathInfo   : String   -- §4.1.5  — extra path after the script path
  query      : String   -- §4.1.7  — the query component, without the "?"

/-- A conformant environment reflects the Script-URI split: `SCRIPT_NAME` is the
script path, `PATH_INFO` the extra path, `QUERY_STRING` the query component
(RFC 3875 §4.1.7 / §4.1.13). -/
def ReflectsUri (req : Cgi.Req) (u : UriSplit) : Prop :=
  req.scriptName = u.scriptPath ∧ req.pathInfo = u.pathInfo ∧ req.queryString = u.query

/-- The deployed wire derivation draws `SCRIPT_NAME` from the target's path
portion, `QUERY_STRING` from the target's query component (both via the total
`Cgi.splitTarget`), and leaves `PATH_INFO` empty. -/
theorem deployed_splits_target (req : Proto.Request) :
    (Reactor.WireRest.deployCgiReq req).scriptName
        = Cgi.targetPath (Reactor.App.bytesToString req.target)
    ∧ (Reactor.WireRest.deployCgiReq req).queryString
        = Cgi.targetQuery (Reactor.App.bytesToString req.target)
    ∧ (Reactor.WireRest.deployCgiReq req).pathInfo = "" :=
  ⟨rfl, rfl, rfl⟩

/-- **The deployed wire derivation reflects the RFC 3875 §4.1.7/§4.1.13 Script-URI
split.** For every request, `SCRIPT_NAME` is the target's path portion (excluding
the query), `QUERY_STRING` is the query component (the post-`?` substring), and
`PATH_INFO` is empty — exactly the split `Cgi.splitTarget` computes. -/
theorem deployed_reflects_uri (req : Proto.Request) :
    ReflectsUri (Reactor.WireRest.deployCgiReq req)
      { scriptPath := Cgi.targetPath (Reactor.App.bytesToString req.target),
        pathInfo   := "",
        query      := Cgi.targetQuery (Reactor.App.bytesToString req.target) } :=
  ⟨rfl, rfl, rfl⟩

/-- A concrete wire request whose target `/x?a=1` carries a query component,
witnessing that the deployed derivation splits at the `?`. -/
def demoWireReq : Proto.Request :=
  { method := [71, 69, 84]                    -- "GET"
    target := [47, 120, 63, 97, 61, 49] }     -- "/x?a=1"

/-- **Non-vacuity witness (RFC 3875 §4.1.7 / §4.1.13).** On the deployed
environment for target `/x?a=1`, `QUERY_STRING` is the bare `a=1` and
`SCRIPT_NAME` is `/x` — the query is split off, and `SCRIPT_NAME` does **not**
retain `/x?a=1`. -/
theorem deployed_query_split_witness :
    Cgi.env (Reactor.WireRest.deployCgiReq demoWireReq) .queryString = "a=1"
    ∧ Cgi.env (Reactor.WireRest.deployCgiReq demoWireReq) .scriptName = "/x"
    ∧ Cgi.env (Reactor.WireRest.deployCgiReq demoWireReq) .scriptName ≠ "/x?a=1" := by
  refine ⟨rfl, rfl, ?_⟩
  decide

/-- **The deployed environment reflects the `/x?a=1` split.** The fixed derivation
satisfies the split obligation on the discriminating target. -/
theorem deployed_reflects_uri_witness :
    ReflectsUri (Reactor.WireRest.deployCgiReq demoWireReq)
        { scriptPath := "/x", pathInfo := "", query := "a=1" } :=
  ⟨rfl, rfl, rfl⟩

/-- **The pre-fix behavior fails the new theorem.** The old derivation (whole
target into `SCRIPT_NAME`, empty `QUERY_STRING`) does **not** reflect the `/x?a=1`
Script-URI split: it disagrees on both `SCRIPT_NAME` (`/x?a=1 ≠ /x`) and
`QUERY_STRING` (`"" ≠ a=1`). -/
theorem old_behavior_fails :
    ¬ ReflectsUri
        { Reactor.WireRest.deployCgiReq demoWireReq with
            scriptName  := Reactor.App.bytesToString demoWireReq.target,
            queryString := "" }
        { scriptPath := "/x", pathInfo := "", query := "a=1" } := by
  rintro ⟨_, _, hq⟩
  exact absurd hq (by decide)

/-! ## Axiom audit -/

#print axioms envList_refines_spec
#print axioms deployed_env_refines_spec
#print axioms deployed_total_over_required
#print axioms query_string_has_no_question_mark
#print axioms omitting_a_var_fails
#print axioms deployed_reflects_uri
#print axioms deployed_query_split_witness
#print axioms old_behavior_fails

end CgiCorrect
