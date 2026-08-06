/-
Reactor.SerializeSanitize — DEFENSE-IN-DEPTH egress: response-splitting
impossible-by-construction.

`Reactor/SerializeFaithful.lean` proved the egress DUAL of parse-faithfulness
(`serialize_faithful`, `serialize_injective` on `Response.Wf`) and, crucially,
the REAL FINDING `serialize_response_splitting`: the deployed `serialize`
renders a header value VERBATIM, so a value carrying `CR LF` forges extra header
lines on the wire (HTTP response-splitting). That vector is PROVEN-not-live only
because INGRESS rejects CR/LF (`Arena.Parse.parse_rejects_ctl_in_value`), so no
attacker CR/LF reaches egress — a `Wf`-maintenance obligation discharged by the
parser, one stage away.

This file closes the G3-egress residual in
`docs/engine/review/ENGINE-ASSURANCE-STORY.md` with BELT-AND-SUSPENDERS: a
serializer `serializeSafe` that is safe WITHOUT relying on ingress. It is a
STRICT-REJECT guard — it decides `Response.Wf` (RFC 7230 §3.2: reason phrase and
every header name/value CR/LF-free, names colon-free) and, if the response is
malformed, emits a fixed well-formed fallback (`safeError`, a headerless `500`)
INSTEAD of the attacker-controlled bytes. So its output is ALWAYS the faithful
serialization of a well-formed response — no forged header line is representable,
whatever a future stage constructs.

What is proven (all additive; `Reactor/Serialize.lean` and
`Reactor/SerializeFaithful.lean` are untouched, built ON):

* `serializeSafe_wf` — for EVERY input `resp` (even non-`Wf`), there is a
  well-formed `r` with `serializeSafe resp = serialize r`. The emitted bytes are
  always the serialization of a `Wf` response.
* `serializeSafe_faithful` — the same, spelled through `serialize_faithful`: the
  safe output is ALWAYS `rfcStatusLine r ++ rfcHeaderBlock r ++ CRLF ++ r.body`
  for a `Wf r`, i.e. exactly the RFC-7230 `status-line · (field CRLF)* · CRLF ·
  body` encoding of well-formed (CR/LF-free) fields — the only CR/LFs on the
  wire are the structural terminators, so NO attacker-forged header line exists.
* `serializeSafe_faithful_on_wf` — on already-`Wf` responses, `serializeSafe =
  serialize` BYTE-IDENTICALLY. Wiring it changes NOTHING for well-formed
  responses (the whole deployed traffic), so it is a safe drop-in.
* Non-vacuity — `serializeSafe_prevents_split`: on the concrete `splitInjected`
  (CR/LF-in-value) that plain `serialize` splits (`serialize splitInjected =
  serialize splitHonest`, from `SerializeFaithful`), `serializeSafe` does NOT
  emit those forged bytes — it routes to `safeError`. Witnessed by literal wire
  bytes (`serialize_splitInjected_bytes`, `serialize_safeError_bytes`).

WIRING NOTE (NOT done this pass — `orb/Dataplane.lean` is another lane):
the deployed egress call site invokes `Reactor.serialize` (via
`serialize_eq_fast` / `SerializeFast`). To install this defense-in-depth,
replace that call with `Reactor.serializeSafe`. `serializeSafe_faithful_on_wf`
proves this is byte-identical on every `Wf` response, so it is a behavior-
preserving swap for well-formed traffic and a strict reject for the (currently
ingress-blocked) malformed case. A `serializeSafe`-vs-fast twin (the analogue of
`serialize_eq_fast`) would follow for the compiled path.

HONEST SCOPE: the live splitting vector is ALREADY mitigated at ingress; this is
defense-in-depth (belt-and-suspenders), not the fix of a live vuln.
-/
import Reactor.SerializeFaithful

namespace Reactor

open Proto (Bytes)

/-! ## Deciding well-formedness (RFC 7230 §3.2) -/

instance instDecidableNoCRLF (bs : Bytes) : Decidable (NoCRLF bs) := by
  unfold NoCRLF; infer_instance

instance instDecidableHdrOK (e : Bytes × Bytes) : Decidable (HdrOK e) := by
  unfold HdrOK; infer_instance

/-- `Response.Wf` is decidable: it is the conjunction of `NoCRLF` on the reason
phrase and `HdrOK` on every header (a bounded `∀` over the header list). -/
instance instDecidableWf (r : Response) : Decidable (Wf r) :=
  decidable_of_iff (NoCRLF r.reason ∧ ∀ e ∈ r.headers, HdrOK e)
    ⟨fun h => ⟨h.1, h.2⟩, fun w => ⟨w.reasonSafe, w.hdrOK⟩⟩

/-! ## The strict-reject fallback and the safe serializer -/

/-- The fixed well-formed fallback emitted for a malformed response: a headerless
`500` with an empty reason phrase and empty body. CR/LF-free by construction, so
`Wf`. (The wired deployment may choose any `Wf` error page here; the theorems
only need `safeError_wf`.) -/
def safeError : Response :=
  { status := 500, reason := [], headers := [], body := [] }

theorem safeError_wf : Wf safeError := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  intro e he
  simp only [safeError, List.not_mem_nil] at he

/-- **The defense-in-depth serializer.** Decides `Wf resp`; if the response is
well-formed it is serialized exactly as `serialize` would; otherwise the fixed
`safeError` bytes are emitted. STRICT REJECT: no CR/LF-bearing header value is
ever rendered, so response-splitting is impossible-by-construction — no reliance
on ingress. -/
def serializeSafe (resp : Response) : Bytes :=
  if Wf resp then serialize resp else serialize safeError

/-! ## The safety theorem: output is ALWAYS a well-formed serialization -/

/-- **`serializeSafe_wf` — no forged header line is representable.** For EVERY
input response (even non-`Wf`), the emitted bytes are the serialization of SOME
well-formed response. (For `Wf` input it is the input itself; for malformed
input it is the `safeError` fallback.) -/
theorem serializeSafe_wf (resp : Response) :
    ∃ r, Wf r ∧ serializeSafe resp = serialize r := by
  unfold serializeSafe
  by_cases h : Wf resp
  · exact ⟨resp, h, if_pos h⟩
  · exact ⟨safeError, safeError_wf, if_neg h⟩

/-- **`serializeSafe_faithful` — the safe output is ALWAYS the RFC-7230
encoding.** For every input, `serializeSafe resp` is exactly `status-line CRLF ·
(field CRLF)* · CRLF · body` of a WELL-FORMED response `r` (`serialize_faithful`
applied to the witness of `serializeSafe_wf`). Because `r` is `Wf`, every header
name/value and the reason phrase are CR/LF-free, so the ONLY CR/LFs on the wire
are the structural line terminators: no attacker-forged header line exists in
the output. This is the explicit anti-splitting statement. -/
theorem serializeSafe_faithful (resp : Response) :
    ∃ r, Wf r ∧ serializeSafe resp
          = rfcStatusLine r ++ rfcHeaderBlock r ++ crlf ++ r.body := by
  obtain ⟨r, hw, he⟩ := serializeSafe_wf resp
  exact ⟨r, hw, by rw [he, serialize_faithful]⟩

/-- **`serializeSafe_faithful_on_wf` — byte-identical on well-formed responses.**
On any `Wf resp`, `serializeSafe resp = serialize resp` exactly. Wiring
`serializeSafe` in place of `serialize` changes NOTHING for well-formed traffic;
it only diverts malformed responses to the safe fallback. So the swap is
behavior-preserving for the deployed (ingress-filtered) traffic. -/
theorem serializeSafe_faithful_on_wf {resp : Response} (w : Wf resp) :
    serializeSafe resp = serialize resp := by
  unfold serializeSafe
  rw [if_pos w]

/-! ## Non-vacuity: the concrete split is rejected, not rendered -/

theorem natToDec_500 : natToDec 500 = [53, 48, 48] := by
  rw [show (natToDec 500) = Proto.Dec.natToDec 500 from rfl, Proto.Dec.natToDec_eq]; decide

theorem natToDec_0 : natToDec 0 = [48] := by
  rw [show (natToDec 0) = Proto.Dec.natToDec 0 from rfl, Proto.Dec.natToDec_eq]; decide

/-- The literal wire bytes of the SAFE fallback: `HTTP/1.1 500 CRLF
Content-Length: 0 CRLF CRLF` (no caller headers, empty body). -/
def safeErrorBytes : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 53, 48, 48, 32, 13, 10,
   67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 48, 13, 10,
   13, 10]

theorem serialize_safeError_bytes : serialize safeError = safeErrorBytes := by
  simp only [serialize, serializeWire, build, statusLine, allHeaders, renderHeaders, headerLine,
    http11, clName, crlf, safeError, safeErrorBytes, List.length_cons, List.length_nil,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  rw [natToDec_500, natToDec_0]; rfl

/-- The literal wire bytes plain `serialize` emits for `splitInjected` — the
FORGED wire: the CR/LF embedded in the single header value renders verbatim as a
second header line `Y: b` (bytes `89 58 32 98`), exactly what `splitHonest`
carries as a real header (`serialize_response_splitting`). -/
def splitInjectedBytes : Bytes :=
  [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 79, 75, 13, 10,
   88, 58, 32, 97, 13, 10, 89, 58, 32, 98, 13, 10,
   67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104, 58, 32, 48, 13, 10,
   13, 10]

theorem serialize_splitInjected_bytes : serialize splitInjected = splitInjectedBytes := by
  simp only [serialize, serializeWire, build, statusLine, allHeaders, renderHeaders, headerLine,
    http11, clName, reasonOK, crlf, splitInjected, splitInjectedBytes, List.length_cons,
    List.length_nil, List.append_assoc, List.cons_append, List.nil_append, List.append_nil]
  rw [natToDec_200, natToDec_0]; rfl

/-- **`serializeSafe_prevents_split` — the finding is closed at egress.** On the
concrete `splitInjected` (a header value carrying `CR LF Y: b`), the deployed
`serialize` forges the split (`= splitInjectedBytes`, and by
`serialize_response_splitting` equal to `serialize splitHonest`). `serializeSafe`
does NOT emit those bytes: it detects the malformed value and emits the
headerless `safeError` fallback instead. The forged second header line never
reaches the wire. -/
theorem serializeSafe_prevents_split :
    serializeSafe splitInjected = serialize safeError
    ∧ serializeSafe splitInjected ≠ serialize splitInjected := by
  have hrej : serializeSafe splitInjected = serialize safeError := by
    unfold serializeSafe
    rw [if_neg splitInjected_not_wf]
  refine ⟨hrej, ?_⟩
  rw [hrej, serialize_safeError_bytes, serialize_splitInjected_bytes]
  decide

end Reactor
