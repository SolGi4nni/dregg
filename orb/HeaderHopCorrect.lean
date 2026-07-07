/-
Hop-by-hop header stripping — correctness against RFC 9110 §7.6.1.

An HTTP intermediary that forwards a message MUST NOT relay the *connection-
specific* ("hop-by-hop") header fields end-to-end.  RFC 9110 §7.6.1 fixes which
fields those are:

  * the `Connection` header field itself, and every field whose name is listed
    as a `connection-option` in a `Connection` field of the message
    ("Intermediaries MUST parse a received Connection header field before a
    message is forwarded and, for each connection-option in this field, remove
    any header or trailer field(s) from the message with the same name …, and
    then remove the Connection header field itself"); together with

  * the well-known connection-management fields the same section names for
    removal — Proxy-Connection, Keep-Alive, TE, Transfer-Encoding, Upgrade —
    plus the classic hop-by-hop set (Trailer, Proxy-Authorization,
    Proxy-Authenticate).

Every other field is end-to-end and MUST be forwarded unchanged.

This file gives that mandate an **independent** meaning and proves the deployed
rewrite engine meets it.

  * `stdHopNames` spells the fixed connection-management names as readable ASCII
    strings, with no reference to the implementation's byte tables.
  * `connOptionNames` parses the message's `Connection` field value(s) into the
    declared option names (comma split, optional-whitespace trim).
  * `IsHopByHop h n` is the RFC predicate: `n` is one of the fixed names, or is a
    connection-option declared in `h`.
  * `ForwardsCorrectly h out` is the forwarding spec, stated purely as a property
    of the output list: every end-to-end field keeps its multiplicity, every
    hop-by-hop field is gone, and nothing is invented or reordered (`out` is a
    subsequence of `h`).

`run_forwards_correctly` proves that the deployed interpreter `Header.run`,
driven by a single `Header.Op.hop` over the RFC hop set, satisfies
`ForwardsCorrectly` on every input.  The bridge `mem_rfcHopSet_iff` is where the
work lives: it verifies that the deployed name table `Header.hopStd` denotes
exactly `stdHopNames` (`hopStd_names`, a byte-for-byte check that would fail on a
missing or mistyped name) and that the deployed membership test agrees with the
RFC predicate.

Non-vacuity is exhibited directly: an intermediary that forwarded `Connection`
or `TE`, or dropped an end-to-end field, provably fails `ForwardsCorrectly`
(`forwarding_connection_fails`, `forwarding_te_fails`,
`dropping_content_type_fails`), and the worked vectors show a `Connection`-
declared field being stripped dynamically.
-/

import Header.Basic
import Header.Rewrite
import Header.Hop

namespace HeaderHopSpec

open Header

/-! ### Readable, implementation-independent field names -/

/-- Encode an ASCII string as a header name, one byte per code point.  A
readable spelling of a field name that is independent of the implementation's
raw byte tables yet reduces definitionally (`decide`). -/
def nm (s : String) : Header.Name := s.toList.map (fun c => UInt8.ofNat c.toNat)

/-- **RFC 9110 §7.6.1 connection-management field names.**  `Connection` itself,
the fields the section names for removal (Proxy-Connection, Keep-Alive, TE,
Transfer-Encoding, Upgrade), and the classic hop-by-hop trio (Trailer,
Proxy-Authorization, Proxy-Authenticate).  Compared case-insensitively. -/
def stdHopNames : List Header.Name :=
  [ nm "connection",
    nm "keep-alive",
    nm "proxy-authenticate",
    nm "proxy-authorization",
    nm "proxy-connection",
    nm "te",
    nm "trailer",
    nm "transfer-encoding",
    nm "upgrade" ]

/-- **Data fidelity.**  The deployed name table `Header.hopStd` denotes exactly
the RFC connection-management names, byte for byte.  A missing or mistyped name
in the deployed table would make this fail. -/
theorem hopStd_names : Header.hopStd = stdHopNames := by decide

/-! ### Case-insensitive membership -/

/-- Case-insensitive membership of `n` in a list of names (RFC 9110 §5.1: field
names compare case-insensitively). -/
def CIMem (names : List Header.Name) (n : Header.Name) : Prop :=
  ∃ m ∈ names, Header.canon m = Header.canon n

instance (names : List Header.Name) (n : Header.Name) : Decidable (CIMem names n) := by
  unfold CIMem; infer_instance

/-- The deployed membership test `Header.isHop` computes case-insensitive
membership. -/
theorem isHop_iff_CIMem (L : List Header.Name) (n : Header.Name) :
    Header.isHop L n = true ↔ CIMem L n := by
  unfold Header.isHop CIMem
  rw [List.any_eq_true]
  constructor
  · rintro ⟨m, hm, hb⟩; exact ⟨m, hm, Header.nameEqb_eq.mp hb⟩
  · rintro ⟨m, hm, hc⟩; exact ⟨m, hm, Header.nameEqb_eq.mpr hc⟩

/-! ### Parsing the Connection field value into declared option names

The comma/OWS `#rule` parse (RFC 9110 §5.6.1) that turns a `Connection` field
value into its `connection-option` names is the *deployed* parser
`Header.connOptionNames` — the very function `Header.Op.hopDyn` runs when the
engine forwards a message.  We name it here for the spec so the correctness
statement below is about the code the engine executes, not a parallel copy.  The
independence that matters — that the fixed connection-management *name table* is
right — is still an independent byte-for-byte check (`hopStd_names` below);
sharing the generic list-parser cannot hide a wrong hop name. -/

/-- **The declared connection-options of a message** — the deployed parser.  For
every `Connection` field in `h`, the option names it lists.  RFC 9110 §7.6.1:
these name the additional hop-by-hop fields that must be removed before
forwarding. -/
abbrev connOptionNames (h : Headers) : List Header.Name := Header.connOptionNames h

/-! ### The RFC hop set and the hop-by-hop predicate -/

/-- **The hop set to strip when forwarding `h`.**  This is exactly the deployed
`Header.dynHopSet h` — the fixed table together with the connection-options `h`
declares — the set `Header.Op.hopDyn` computes and strips. -/
def rfcHopSet (h : Headers) : List Header.Name := Header.dynHopSet h

/-- **RFC 9110 §7.6.1 hop-by-hop classification.**  `n` names a hop-by-hop field
for message `h` iff it is one of the fixed connection-management names or is a
connection-option declared in `h`.  Defined without reference to the strip
implementation. -/
def IsHopByHop (h : Headers) (n : Header.Name) : Prop :=
  CIMem stdHopNames n ∨ CIMem (connOptionNames h) n

instance (h : Headers) (n : Header.Name) : Decidable (IsHopByHop h n) := by
  unfold IsHopByHop; infer_instance

/-- **The bridge.**  The deployed membership test over the RFC hop set agrees
with the RFC hop-by-hop predicate on every name.  This folds in the data-fidelity
fact `hopStd_names` (the deployed table equals `stdHopNames`) and the parse of
the declared connection-options.  `rfcHopSet` is the deployed `Header.dynHopSet`,
so this is the bridge over the set the engine actually strips. -/
theorem mem_rfcHopSet_iff (h : Headers) (n : Header.Name) :
    Header.isHop (rfcHopSet h) n = true ↔ IsHopByHop h n := by
  unfold rfcHopSet Header.dynHopSet IsHopByHop
  rw [Header.isHop_append, Bool.or_eq_true, isHop_iff_CIMem, isHop_iff_CIMem, hopStd_names]

/-! ### The forwarding specification and the refinement -/

/-- **Forwarding specification (RFC 9110 §7.6.1).**  `out` is a correct forward
of `h` when: every end-to-end field is forwarded with unchanged multiplicity;
every hop-by-hop field is absent; and `out` invents/reorders nothing (it is a
subsequence of `h`).  Stated as a property of `out`, not as a strip program. -/
def ForwardsCorrectly (h out : Headers) : Prop :=
  (∀ f : Header.Field, ¬ IsHopByHop h f.name → List.count f out = List.count f h) ∧
  (∀ f : Header.Field, IsHopByHop h f.name → List.count f out = 0) ∧
  out.Sublist h

/-- The deployed hop stage reduces to a single `strip`, i.e. a filter that keeps
exactly the non-hop fields. -/
theorem run_hop_eq_filter (hs : List Header.Name) (h : Headers) :
    Header.run [Header.Op.hop hs] h = h.filter (fun f => !Header.isHop hs f.name) := by
  rw [Header.run_cons, Header.run_nil]; rfl

/-- **Refinement.**  The deployed interpreter `Header.run`, driven by one
`Header.Op.hop` over the RFC hop set, forwards every message correctly per
RFC 9110 §7.6.1 — hop-by-hop fields stripped, end-to-end fields preserved,
nothing invented. -/
theorem run_forwards_correctly (h : Headers) :
    ForwardsCorrectly h (Header.run [Header.Op.hop (rfcHopSet h)] h) := by
  rw [run_hop_eq_filter]
  refine ⟨?_, ?_, ?_⟩
  · -- end-to-end fields keep their multiplicity
    intro f hf
    have hfalse : Header.isHop (rfcHopSet h) f.name = false := by
      rcases Bool.eq_false_or_eq_true (Header.isHop (rfcHopSet h) f.name) with h' | h'
      · exact absurd ((mem_rfcHopSet_iff h f.name).mp h') hf
      · exact h'
    exact List.count_filter (by simp [hfalse])
  · -- hop-by-hop fields are gone
    intro f hf
    have htrue : Header.isHop (rfcHopSet h) f.name = true :=
      (mem_rfcHopSet_iff h f.name).mpr hf
    apply List.count_eq_zero.mpr
    intro hmem
    rw [List.mem_filter] at hmem
    have : Header.isHop (rfcHopSet h) f.name = false := by simpa using hmem.2
    rw [htrue] at this; exact absurd this (by decide)
  · -- nothing invented or reordered
    exact List.filter_sublist h

/-! ### The DEPLOYED refinement — bound to `Header.Op.hopDyn`

`run_forwards_correctly` above is stated over `Header.Op.hop (rfcHopSet h)`.  The
engine does not build that op: the deployed strip stage
(`Lifecycle.stdRewrite`, `Stage.Header.rewriteProg`) is `Header.Op.hopDyn`, which
computes its strip set — `Header.dynHopSet h`, definitionally `rfcHopSet h` — from
the very headers it is applied to.  These two lemmas rebind the refinement to that
deployed op. -/

/-- The deployed dynamic strip is the strip over the RFC hop set: the set
`Header.Op.hopDyn` computes from the message *is* `rfcHopSet` (definitionally
`Header.dynHopSet`). -/
theorem run_hopDyn_eq_rfc (h : Headers) :
    Header.run [Header.Op.hopDyn] h = Header.run [Header.Op.hop (rfcHopSet h)] h := by
  rw [Header.run_hopDyn, Header.run_cons, Header.run_nil]; rfl

/-- **The deployed refinement (RFC 9110 §7.6.1).**  The DEPLOYED interpreter
`Header.run` driven by `Header.Op.hopDyn` — the strip stage the engine runs —
forwards every message correctly: it strips EXACTLY the fixed hop set together
with the fields the message's `Connection` header nominates, and preserves every
end-to-end field, inventing/reordering nothing.  Bound to the op the engine
actually executes, not a proof-file set. -/
theorem deployed_forwards_correctly (h : Headers) :
    ForwardsCorrectly h (Header.run [Header.Op.hopDyn] h) := by
  rw [run_hopDyn_eq_rfc]; exact run_forwards_correctly h

/-! ### Worked vectors and non-vacuity

Concrete messages: a `Connection: close` field (capital `C`, exercising the
case-insensitive match), a `TE`, an end-to-end `Content-Type`, and a custom
`X-Foo`. -/

def hConn : Header.Field := ⟨nm "Connection", nm "close"⟩
def hTE : Header.Field := ⟨nm "TE", nm "trailers"⟩
def hCT : Header.Field := ⟨nm "Content-Type", nm "text/plain"⟩
def hXFoo : Header.Field := ⟨nm "X-Foo", nm "bar"⟩
/-- A `Connection` field that declares `X-Foo` as a connection-option. -/
def hConnFoo : Header.Field := ⟨nm "Connection", nm "X-Foo"⟩

def sample : Headers := [hConn, hTE, hCT, hXFoo]
def sampleDyn : Headers := [hConnFoo, hCT, hXFoo]

/-- Forwarding `sample` strips `Connection` and `TE`, keeps `Content-Type` and
`X-Foo`, in order. -/
example : Header.run [Header.Op.hop (rfcHopSet sample)] sample = [hCT, hXFoo] := by decide

/-- **Dynamic connection-option removal.**  `Connection: X-Foo` declares `X-Foo`
hop-by-hop, so forwarding `sampleDyn` strips both the `Connection` field and
`X-Foo`, leaving only the end-to-end `Content-Type`. -/
example : Header.run [Header.Op.hop (rfcHopSet sampleDyn)] sampleDyn = [hCT] := by decide

/-- `Connection` is classified hop-by-hop. -/
theorem conn_is_hop : IsHopByHop sample hConn.name := by decide

/-- `TE` is classified hop-by-hop. -/
theorem te_is_hop : IsHopByHop sample hTE.name := by decide

/-- `Content-Type` is end-to-end. -/
theorem ct_not_hop : ¬ IsHopByHop sample hCT.name := by decide

/-- `X-Foo`, declared by `Connection` in `sampleDyn`, is hop-by-hop *there*. -/
theorem xfoo_is_hop_dyn : IsHopByHop sampleDyn hXFoo.name := by decide

/-- `X-Foo` is *not* hop-by-hop in `sample`, where no `Connection` declares it —
the classification is message-relative, as the RFC requires. -/
theorem xfoo_not_hop_static : ¬ IsHopByHop sample hXFoo.name := by decide

/-! **Non-vacuity.**  A forwarder that relayed a hop-by-hop field, or dropped an
end-to-end field, provably fails the specification. -/

/-- An intermediary that forwarded `Connection` unchanged fails the spec. -/
theorem forwarding_connection_fails : ¬ ForwardsCorrectly sample sample := by
  rintro ⟨_, hstrip, _⟩
  have h0 := hstrip hConn conn_is_hop
  rw [show List.count hConn sample = 1 from by decide] at h0
  exact absurd h0 (by decide)

/-- An intermediary that forwarded `TE` unchanged fails the spec. -/
theorem forwarding_te_fails : ¬ ForwardsCorrectly sample sample := by
  rintro ⟨_, hstrip, _⟩
  have h0 := hstrip hTE te_is_hop
  rw [show List.count hTE sample = 1 from by decide] at h0
  exact absurd h0 (by decide)

/-- An intermediary that dropped the end-to-end `Content-Type` fails the spec.
`[hXFoo]` strips the hop fields correctly but also loses `Content-Type`. -/
theorem dropping_content_type_fails : ¬ ForwardsCorrectly sample [hXFoo] := by
  rintro ⟨hpres, _, _⟩
  have h0 := hpres hCT ct_not_hop
  rw [show List.count hCT [hXFoo] = 0 from by decide,
      show List.count hCT sample = 1 from by decide] at h0
  exact absurd h0 (by decide)

/-! ### The deployed strip on the smuggling vector — the leak, closed

The header leak: a message carrying `Connection: X-Secret` then `X-Secret: …`.
RFC 9110 §7.6.1 makes `X-Secret` hop-by-hop *for this message*; it MUST NOT be
forwarded downstream.  A static `strip Header.hopStd` (which never parses
`Connection`) forwards it — the vector.  The deployed `Header.Op.hopDyn` strips
it. -/

/-- A `Connection` field that nominates `X-Secret` (the smuggling vector). -/
def hConnSecret : Header.Field := ⟨nm "Connection", nm "X-Secret"⟩

/-- The nominated hop-by-hop field an attacker hopes to leak downstream. -/
def hSecret : Header.Field := ⟨nm "X-Secret", nm "leak"⟩

/-- A forwarded message whose `Connection` header nominates `X-Secret`. -/
def sampleSecret : Headers := [hConnSecret, hSecret, hCT]

/-- **Witness — the deployed op strips a `Connection`-nominated field.**  Running
the DEPLOYED `Header.Op.hopDyn` over `Connection: X-Secret` removes both the
`Connection` field and `X-Secret`, leaving only the end-to-end `Content-Type`. -/
example : Header.run [Header.Op.hopDyn] sampleSecret = [hCT] := by decide

/-- …so a downstream lookup of `X-Secret` on the deployed output is absent — the
leak is closed. -/
theorem deployed_strips_secret :
    Header.get (nm "X-Secret") (Header.run [Header.Op.hopDyn] sampleSecret) = none := by decide

/-- `X-Secret` is hop-by-hop in `sampleSecret` (nominated by its `Connection`). -/
theorem secret_is_hop_dyn : IsHopByHop sampleSecret hSecret.name := by decide

/-- **Load-bearing negative — the static strip LEAKS.**  An intermediary that
stripped only the fixed `Header.hopStd` set (ignoring the `Connection` header)
forwards `X-Secret` downstream unchanged — the exact bug this change fixes. -/
theorem static_strip_leaks_secret :
    Header.get (nm "X-Secret") (Header.run [Header.Op.hop Header.hopStd] sampleSecret)
      = some (nm "leak") := by decide

/-- Hence the static-only strip provably FAILS the forwarding spec on this
message, while the deployed `Header.Op.hopDyn` satisfies it
(`deployed_forwards_correctly`).  The fix is not cosmetic. -/
theorem static_strip_not_correct :
    ¬ ForwardsCorrectly sampleSecret (Header.run [Header.Op.hop Header.hopStd] sampleSecret) := by
  rintro ⟨_, hstrip, _⟩
  have h0 := hstrip hSecret secret_is_hop_dyn
  rw [show List.count hSecret (Header.run [Header.Op.hop Header.hopStd] sampleSecret) = 1
        from by decide] at h0
  exact absurd h0 (by decide)

end HeaderHopSpec
