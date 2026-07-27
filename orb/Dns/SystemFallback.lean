import Dns.Resolve

/-!
# System-resolver fallback (parity row dn.15)

The proven resolver (`Dns.answersOf`, RFC 1035 §7.3 answer matching + §3.3.1
CNAME chase) reads a *wire* response and extracts the records that answer the
query. When it extracts **nothing** — a SERVFAIL/NXDOMAIN response, a truncated
or mismatched message, or simply no answer of the queried type — a real
resolver falls back to the host's system resolver (`getaddrinfo`, which honours
`/etc/hosts`, nsswitch, and locally-configured DNS).

That syscall is an **untrusted seam**: `getaddrinfo` runs outside this codebase,
so its result is modelled here as an *oracle* — an arbitrary function from the
queried name to a list of candidate addresses. What this file proves is the
**decision logic** wrapped around that oracle, three obligations:

* `system_fallback_on_servfail` — when the proven resolver yields no answer, the
  request *does* consult the system oracle and the oracle's (validated) result
  is what is returned; `system_fallback_uses_result` shows a well-formed
  candidate actually reaches the output.
* `system_fallback_not_on_success` — when the proven resolver yields an answer,
  the oracle is **not** consulted: the result is exactly the proven answer and
  is invariant under replacing the oracle by any other oracle (the syscall is
  never even issued).
* `fallback_result_wellformed` / `fallback_used_result_wellformed` — every
  address that comes out of the fallback path was **validated** (a 32-bit A or a
  128-bit AAAA) before use; a candidate the oracle reports out of range is
  dropped, never trusted raw.

The oracle is untrusted; the *decision* — when to fall back, and to admit only
validated addresses — is proven.
-/

namespace Dns.SystemFallback

open Dns

/-- The two address families `getaddrinfo` can return that this resolver uses:
A (RFC 1035 §3.4.1, IPv4) and AAAA (RFC 3596, IPv6). -/
inductive Family where
  | v4
  | v6
deriving DecidableEq, Repr

/-- The `2^32` bound of a well-formed IPv4 (A) address. -/
def v4Bound : Nat := 4294967296

/-- The `2^128` bound of a well-formed IPv6 (AAAA) address. -/
def v6Bound : Nat := 340282366920938463463374607431768211456

/-- A raw candidate as reported by the `getaddrinfo` seam: a family tag and a
numeric address. **Untrusted** — the numeric value is whatever the syscall
handed back and is *not* assumed to be in range for its family. -/
structure SysAddr where
  family : Family
  value : Nat
deriving Repr

/-- Is a candidate a well-formed address for its family? A must fit in 32 bits,
AAAA in 128 bits. This is the validation gate the raw syscall result must pass. -/
def SysAddr.wellFormed (a : SysAddr) : Bool :=
  match a.family with
  | .v4 => a.value < v4Bound
  | .v6 => a.value < v6Bound

/-- Validate a raw candidate and, only if well-formed, admit it as a typed
`RData` (`.a`/`.aaaa`, exactly the shapes the proven resolver produces). An
out-of-range candidate becomes `none` — dropped, not coerced. -/
def SysAddr.toRData? (a : SysAddr) : Option RData :=
  match a.family with
  | .v4 => if a.value < v4Bound then some (.a a.value) else none
  | .v6 => if a.value < v6Bound then some (.aaaa a.value) else none

/-- The system resolver as an **oracle**: the untrusted `getaddrinfo` seam,
modelled as an arbitrary map from the queried name to candidate addresses.
Nothing about its output is assumed — the validation gate does the trusting. -/
abbrev Getaddrinfo := Name → List SysAddr

/-- The name a one-question query asks about, or `none` if the query bytes are
not a single-question query. This is the key the fallback hands to the oracle —
the *same* name the proven path was asked to resolve. -/
def queryHost (query : Bytes) : Option Name :=
  match parseMsg query with
  | none => none
  | some qm =>
    match qm.questions with
    | [q] => some q.qname
    | _ => none

/-- **The resolve-with-fallback decision.** Run the proven resolver on the wire
response. If it extracts any answer, return exactly that (the oracle is never
touched). Otherwise fall back to the system oracle on the queried name, admitting
only the candidates that pass validation. -/
def resolveWithFallback (gai : Getaddrinfo) (query resp : Bytes) : List RData :=
  match answersOf query resp with
  | [] =>
    match queryHost query with
    | some host => (gai host).filterMap SysAddr.toRData?
    | none => []
  | ans@(_ :: _) => ans

/-! ## Validation: only well-formed addresses leave the fallback path -/

/-- A validated candidate is a well-formed A or AAAA. -/
theorem toRData?_wellFormed (a : SysAddr) (d : RData) (h : a.toRData? = some d) :
    (∃ v, d = RData.a v ∧ v < v4Bound) ∨ (∃ v, d = RData.aaaa v ∧ v < v6Bound) := by
  unfold SysAddr.toRData? at h
  cases hf : a.family with
  | v4 =>
    rw [hf] at h
    by_cases hv : a.value < v4Bound
    · rw [if_pos hv] at h
      left; exact ⟨a.value, by injection h with h; exact h.symm, hv⟩
    · rw [if_neg hv] at h; exact absurd h (by simp)
  | v6 =>
    rw [hf] at h
    by_cases hv : a.value < v6Bound
    · rw [if_pos hv] at h
      right; exact ⟨a.value, by injection h with h; exact h.symm, hv⟩
    · rw [if_neg hv] at h; exact absurd h (by simp)

/-- **Validation obligation.** Every `RData` produced by the fallback path — the
oracle's candidates run through `toRData?` — is a validated well-formed A
(`< 2^32`) or AAAA (`< 2^128`). The raw syscall result is never trusted; a
candidate out of range for its family is dropped. -/
theorem fallback_result_wellformed (gai : Getaddrinfo) (host : Name) (d : RData)
    (hd : d ∈ (gai host).filterMap SysAddr.toRData?) :
    (∃ v, d = RData.a v ∧ v < v4Bound) ∨ (∃ v, d = RData.aaaa v ∧ v < v6Bound) := by
  rcases List.mem_filterMap.mp hd with ⟨a, _, hf⟩
  exact toRData?_wellFormed a d hf

/-! ## The fallback decision -/

/-- **Fallback IS taken on no-answer.** When the proven resolver extracts nothing
(SERVFAIL, NXDOMAIN, truncated, mismatched, or no record of the queried type —
everything `answersOf … = []` covers) and the query names a host, the result is
exactly the *validated* system-oracle answer. The syscall is consulted and its
vetted result is used. -/
theorem system_fallback_on_servfail (gai : Getaddrinfo) (query resp : Bytes)
    (host : Name) (hservfail : answersOf query resp = [])
    (hhost : queryHost query = some host) :
    resolveWithFallback gai query resp = (gai host).filterMap SysAddr.toRData? := by
  unfold resolveWithFallback
  rw [hservfail, hhost]

/-- **The fallback result actually reaches the output.** Under a no-answer proven
resolve, any well-formed candidate the oracle reports for the queried host is
present in the final result — the fallback is *used*, not merely reachable. -/
theorem system_fallback_uses_result (gai : Getaddrinfo) (query resp : Bytes)
    (host : Name) (hservfail : answersOf query resp = [])
    (hhost : queryHost query = some host)
    (a : SysAddr) (hmem : a ∈ gai host) (hwf : a.toRData? = some d) :
    d ∈ resolveWithFallback gai query resp := by
  rw [system_fallback_on_servfail gai query resp host hservfail hhost]
  exact List.mem_filterMap.mpr ⟨a, hmem, hwf⟩

/-- Every address that survives to the output under a no-answer proven resolve is
a validated well-formed A/AAAA — the end-to-end validation guarantee. -/
theorem fallback_used_result_wellformed (gai : Getaddrinfo) (query resp : Bytes)
    (host : Name) (hservfail : answersOf query resp = [])
    (hhost : queryHost query = some host)
    (d : RData) (hd : d ∈ resolveWithFallback gai query resp) :
    (∃ v, d = RData.a v ∧ v < v4Bound) ∨ (∃ v, d = RData.aaaa v ∧ v < v6Bound) := by
  rw [system_fallback_on_servfail gai query resp host hservfail hhost] at hd
  exact fallback_result_wellformed gai host d hd

/-- **Fallback is NOT taken on success, and the oracle is never consulted.** When
the proven resolver extracts an answer, the result is exactly that proven answer
*and* is invariant under replacing the oracle with any other oracle — the
`getaddrinfo` syscall is not issued at all on the success path. -/
theorem system_fallback_not_on_success (gai gai' : Getaddrinfo) (query resp : Bytes)
    (hok : answersOf query resp ≠ []) :
    resolveWithFallback gai query resp = answersOf query resp
      ∧ resolveWithFallback gai query resp = resolveWithFallback gai' query resp := by
  have h : ∀ g : Getaddrinfo, resolveWithFallback g query resp = answersOf query resp := by
    intro g
    unfold resolveWithFallback
    cases ha : answersOf query resp with
    | nil => exact absurd ha hok
    | cons x xs => rfl
  exact ⟨h gai, by rw [h gai, h gai']⟩

/-! ## Kernel-checked vectors: the decision on a real SERVFAIL wire message

These run the REAL proven resolver (`answersOf`) on hand-laid wire bytes and the
fallback decision on a concrete oracle, entirely by `decide` — no `native_decide`,
no I/O, no crypto. They witness that the hypotheses above are *satisfiable*: a
genuine SERVFAIL response drives the fallback, a genuine success does not. -/

/-- The query `up IN A`, id 0x1234 (the shared `Dns` test query). -/
def qUp : Bytes :=
  [ 0x12, 0x34, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01 ]

/-- A SERVFAIL response (flags 0x8182, RCODE 2) with a lying answer section. -/
def rServfail : Bytes :=
  [ 0x12, 0x34, 0x81, 0x82, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

/-- A successful A response: `up A 93.184.216.34`. -/
def rOk : Bytes :=
  [ 0x12, 0x34, 0x81, 0x80, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01,
    2, 117, 112, 0, 0x00, 0x01, 0x00, 0x01, 0x00, 0x00, 0x00, 0x3C, 0x00, 0x04,
    93, 184, 216, 34 ]

/-- The queried name is the single label `up`. -/
def hostUp : Name := [[117, 112]]

/-- The proven resolver really extracts nothing from the SERVFAIL response. -/
theorem answersOf_servfail_empty : answersOf qUp rServfail = [] := by decide

/-- The proven resolver really extracts the address from the OK response. -/
theorem answersOf_ok_nonempty : answersOf qUp rOk = [RData.a 1572395042] := by decide

/-- The query names host `up`. -/
theorem queryHost_qUp : queryHost qUp = some hostUp := by decide

/-- A concrete system oracle: it reports `10.0.0.7` for `up`, plus one candidate
that is out of range for A (value ≥ 2^32) which validation must drop. -/
def oracleUp : Getaddrinfo := fun h =>
  if h == hostUp then [⟨.v4, 167772167⟩, ⟨.v4, 9999999999⟩] else []

/-- **End-to-end fallback on the wire.** The SERVFAIL response drives the
fallback, the oracle is consulted, and only the *validated* address (`10.0.0.7`
= 167772167) survives — the out-of-range candidate is dropped. -/
theorem fallback_servfail_uses_validated :
    resolveWithFallback oracleUp qUp rServfail = [RData.a 167772167] := by decide

/-- **End-to-end success on the wire.** The OK response is answered by the proven
resolver; the oracle (which would report `10.0.0.7`) is never consulted. -/
theorem fallback_ok_no_oracle :
    resolveWithFallback oracleUp qUp rOk = [RData.a 1572395042] := by decide

end Dns.SystemFallback
