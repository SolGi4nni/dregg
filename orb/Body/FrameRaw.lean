import Body.Framing

/-!
# Raw-buffer request framing — the whole boundary decision, in the core

`Body/Framing.lean` proves the framing *decision* smuggling-safe, but it takes an
already-parsed head: `frameFixed` is given the head length `headEnd` and the
parsed `Smuggling.Request`. The step from a **raw accumulation buffer** to that
decision — scan for `CRLFCRLF`, split the head into header fields, classify
`Content-Length`/`Transfer-Encoding` — was, until now, a reimplementation living
only in the trusted host (`crates/dataplane/src/http.rs::next_request` /
`body_frame`). That host code *decides where each HTTP/1.1 request ends* and
*whether the framing is a smuggling reject* — a semantic, correctness-critical
decision the proven core did not govern. A bug there is a request-smuggling
desync on the wire even though `frame_no_smuggle` is green: green-proof + wrong-
wire.

This file closes that gap by lifting the decision into the core. `frameRaw` is a
total `Bytes → Framing.Outcome` that takes the *raw* buffer and produces the
same `{needMore | reject | complete}` verdict, composing:

* `scanHeadEnd` — locate the octet just past the first `CRLFCRLF` (the head end);
* `parseFramingHead` — split the head block into `Smuggling.Header` fields
  (name before the first `:`, value the rest of the line), exactly the raw parse
  the host performed by hand;
* `Body.Framing.frameFixed` — the **already-proven** smuggling-safe boundary.

Everything downstream of the parse is reused unchanged, so `frameRaw` inherits
the smuggling safety and boundary faithfulness the `Body.Framing` theorems
established, now over *raw bytes* rather than a pre-parsed head:

* `frameRaw_no_smuggle` — whenever the parsed head frames both a `Content-Length`
  and a chunked `Transfer-Encoding`, `frameRaw` **rejects**; it is never
  `complete`. The boundary-over-raw-bytes form of `Body.Smuggling.no_desync`.
* `frameRaw_faithful` — a fixed-`Content-Length` framing consumes exactly
  `head ++ body` and leaves the next request verbatim; the boundary is a function
  of the head alone.
* `frameRaw_faithful_empty` — the same for a body-less request.
* `frameRaw_bounded` — a `complete` boundary never runs past the buffer.
* `frameRaw_complete_noBareLF` — an admitted head carries **no bare LF**, so the
  CRLF-only parse this core takes is the only parse RFC 9112 §2.2 permits of it
  (see (1b); `Reactor.ProxyForwardHead.splitLFLines_eq_splitCRLFLines` turns that
  into "the upstream cannot see a field the hop-by-hop strip could not").
* Concrete non-vacuity: a real CL.TE wire head (`clteBuf`) is parsed and
  **rejected** by `frameRaw`; a real body-less GET is framed to its exact
  boundary. The naive length-only host framer (`frameRawNaive`) *would* have
  split the CL.TE head into a 6-octet body and admitted the smuggled tail —
  `frameRaw` refuses it, so the contract is not vacuous.

`frameRequestExport` (`@[export drorb_frame_request]`) is the C-ABI seam the host
crosses instead of deciding framing itself: raw buffer in, an encoded `Outcome`
out (`0`=needMore, `1 r`=reject reason, `2 …le64`=complete count). The resource
cap (`REQUEST_CAP`) stays host-side — it is a DoS limit, not a framing decision.
-/

namespace Body
namespace FrameRaw

open Body Body.Framing Body.Smuggling

/-! ## Octet constants (kept local so this module opens no name-clashing scope) -/

/-- ASCII carriage return. -/
def CR : UInt8 := 13
/-- ASCII line feed. -/
def LF : UInt8 := 10
/-- ASCII colon, the header name/value separator. -/
def COLON : UInt8 := 58
/-- The two-octet line terminator. -/
def crlf : Bytes := [CR, LF]

/-! ## (1) Head-end scan: locate the octet past the first `CRLFCRLF` -/

/-- Does the buffer *begin* with `CRLFCRLF`? Structural cons match + `==` so it
reduces in the kernel (no numeric-literal patterns). -/
def crlfcrlfHere : Bytes → Bool
  | a :: b :: c :: d :: _ => a == CR && b == LF && c == CR && d == LF
  | _ => false

/-- Fuel-bounded scan for the first `CRLFCRLF`; returns the index just past it.
Fuel counts down one per octet consumed, so `buf.length + 1` always suffices.
Structural on the `Nat` fuel, so it reduces in the kernel (no well-founded
recursion) — the concrete-vector theorems below discharge by `decide`. -/
def scanHeadEndFuel : Nat → Nat → Bytes → Option Nat
  | 0, _, _ => none
  | fuel + 1, idx, bs =>
    if crlfcrlfHere bs then some (idx + 4)
    else match bs with
      | [] => none
      | _ :: rest => scanHeadEndFuel fuel (idx + 1) rest

/-- Locate the head end (octet just past the first `CRLFCRLF`), or `none` if the
buffer holds no complete head yet. -/
def scanHeadEnd (buf : Bytes) : Option Nat := scanHeadEndFuel (buf.length + 1) 0 buf

/-! ## (1b) Bare-LF heads: the two-parse hazard, refused

RFC 9112 §2.2: *"Although the line terminator for the start-line and fields is
the sequence CRLF, a recipient MAY recognize a single LF as a line terminator
and ignore any preceding CR."* Every line scan in this core takes the CRLF-only
reading — `takeLine` here, `Reactor.ServeStep.splitCRLFLines` on the proxy
forward path. So a head carrying a **bare LF** (an LF not immediately preceded
by CR) has *two* admissible parses, and the next hop is free to take the other
one: a field sitting after a bare LF is part of the previous field's VALUE to us
and a field-line of its own to an LF-tolerant recipient.

For an intermediary that is not a cosmetic difference. Measured against the
deployed proxy (`conformance/proxy/barelf_smuggle.py`), the head

    GET /api/probe HTTP/1.1 CRLF Host: 127.0.0.1 CRLF
    X-Probe: 1 LF Connection: keep-alive CRLF CRLF

was admitted, the RFC 9110 §7.6.1 hop-by-hop strip saw one field named
`x-probe`, and `Connection: keep-alive` — and, in the second vector,
`Transfer-Encoding: chunked` — arrived at the upstream **unstripped**. Two hops
disagreeing about where a message's fields (and hence its body) begin is RFC
9112 §11.2 request smuggling.

The gate therefore **fails closed**: it refuses the head rather than making the
splitter LF-tolerant. Rejecting is RFC 9112 §2.2's own advice for a recipient
that will forward, and it is the only choice that keeps a single parse: making
`splitCRLFLines` tolerant would merely move the disagreement to whatever hop
*is* CRLF-only. `Reactor.ProxyForwardHead.splitLFLines_eq_splitCRLFLines` proves
the payoff — on an admitted head the two admissible parses coincide. -/

/-- Is the block free of **bare LF** — is every `LF` in it immediately preceded
by `CR`? The case split mirrors `takeLine` / `Reactor.ServeStep.splitCRLFLines`
exactly: a `CRLF` pair is a line terminator (consume both), a leading `LF` is
bare (refuse), anything else is one ordinary octet. Structural on the list and a
tail call in every branch, so the compiler emits a loop (`O(1)` stack on the raw
accumulation buffer) and the kernel still reduces it for `decide`. -/
def noBareLF : Bytes → Bool
  | [] => true
  | 13 :: 10 :: rest => noBareLF rest
  | 10 :: _ => false
  | _ :: rest => noBareLF rest

/-- **The ordinary-octet step.** An octet that is neither a bare `LF` (`h2`) nor
the `CR` of a `CRLF` pair (`h1`) is skipped: exactly the fourth arm of `noBareLF`,
stated as a rewrite so the two-octet lookahead can be discharged once. -/
theorem noBareLF_cons_step (b : UInt8) (rest : Bytes) (h2 : b = 10 → False)
    (h1 : ∀ r, b = 13 → rest = 10 :: r → False) :
    noBareLF (b :: rest) = noBareLF rest := by
  rw [noBareLF.eq_def]
  split <;> simp_all

/-- **Prefix closure.** A block with no bare LF has no bare LF in any prefix.
(The head the proxy forwards is `buf.take headEnd` minus its trailing
`CRLFCRLF`, so the gate's verdict transfers to it.)

The only delicate case is the last octet of `bs`: `noBareLF`'s `CR`-`LF` arm
looks *two* octets ahead, so an octet innocent inside `bs` can be the `CR` of a
`CRLF` that straddles the join. Splitting on whether `bs`'s tail is empty settles
it — a straddling pair reads `noBareLF` past the join, where the hypothesis about
`bs` alone says nothing, and there the step lemma applies unconditionally. -/
theorem noBareLF_prefix (bs suf : Bytes) (h : noBareLF (bs ++ suf) = true) :
    noBareLF bs = true := by
  induction bs using noBareLF.induct with
  | case1 => rfl
  | case2 rest ih => exact ih (by simpa [noBareLF] using h)
  | case3 x => simp [noBareLF] at h
  | case4 b rest h1 h2 ih =>
    cases rest with
    | nil =>
      rw [noBareLF_cons_step b [] h2 (by intro r _ hr; exact absurd hr (by simp))]
      rfl
    | cons r rs =>
      have hb13 : b = 13 → r ≠ 10 := by
        intro hb hr; exact h1 rs hb (by rw [hr])
      have hstep : noBareLF (b :: (r :: rs ++ suf)) = noBareLF (r :: rs ++ suf) :=
        noBareLF_cons_step b (r :: rs ++ suf) h2 (by
          intro x hb hx
          injection hx with hx1 hx2
          exact hb13 hb hx1)
      have hgoal : noBareLF (b :: r :: rs) = noBareLF (r :: rs) :=
        noBareLF_cons_step b (r :: rs) h2 h1
      rw [hgoal]
      exact ih (by rw [← hstep]; simpa using h)

/-! ## (2) Head parse: raw head block → the framing header fields -/

/-- Read up to (and consume) the first `CRLF`: the bytes before it and the bytes
after. `none` if no `CRLF` occurs. Structural on the list. -/
def takeLine : Bytes → Option (Bytes × Bytes)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if a == CR && b == LF then some ([], rest)
    else (takeLine (b :: rest)).map (fun p => (a :: p.1, p.2))

/-! ### Bounded-stack head scans

`takeLine` / `splitColon` recurse *inside* `Option.map` and `headerFieldsFuel`
conses after its recursive call, so the compiled code pushes one C stack frame
per octet (per line for the fold) — recursion depth = line length, and this
framing decision runs on the RAW accumulation buffer for every request, before
any size gate can refuse it. Each gets a reverse-accumulator (tail-recursive)
twin the compiler emits as a loop — `O(1)` stack regardless of input —
installed as the compiled implementation by `@[csimp]`. The specs (and every
kernel-reduction `decide` theorem below) are untouched. -/

/-- Tail-recursive `takeLine`: the line accumulates in reverse, one loop
iteration per octet, constant stack. -/
def takeLineRevGo : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | _, [_] => none
  | acc, a :: b :: rest =>
    if a == CR && b == LF then some (acc.reverse, rest)
    else takeLineRevGo (a :: acc) (b :: rest)

/-- The reverse-accumulator scan equals `takeLine` under the flushed
accumulator. -/
theorem takeLineRevGo_eq (bs : Bytes) :
    ∀ acc, takeLineRevGo acc bs
        = (takeLine bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons a xs ih =>
    intro acc
    match xs, ih with
    | [], _ => rfl
    | b :: rest, ih =>
      show (if a == CR && b == LF then some (acc.reverse, rest)
              else takeLineRevGo (a :: acc) (b :: rest))
          = (takeLine (a :: b :: rest)).map (fun p => (acc.reverse ++ p.1, p.2))
      rw [takeLine]
      by_cases h : a == CR && b == LF
      · simp [h]
      · rw [if_neg h, if_neg h, ih (a :: acc), Option.map_map]
        rcases takeLine (b :: rest) with _ | ⟨pre, rest'⟩
        · rfl
        · simp

/-- The loop form `takeLine` compiles to. -/
def takeLineTail (bs : Bytes) : Option (Bytes × Bytes) := takeLineRevGo [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `takeLine`. -/
@[csimp] theorem takeLine_eq_tail : @takeLine = @takeLineTail := by
  funext bs
  rw [takeLineTail, takeLineRevGo_eq bs []]
  rcases takeLine bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Split a header line at the first `:`: the name (before it) and the value (the
rest of the line, colon consumed). `none` if the line carries no `:`. The value
keeps its leading whitespace; `Smuggling`'s own `trim` normalizes it, so the
classification matches the host's trimmed lookup. -/
def splitColon : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs =>
    if b == COLON then some ([], bs)
    else (splitColon bs).map (fun p => (b :: p.1, p.2))

/-- Tail-recursive `splitColon`: the name accumulates in reverse, one loop
iteration per octet, constant stack. -/
def splitColonRevGo : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | acc, b :: bs =>
    if b == COLON then some (acc.reverse, bs)
    else splitColonRevGo (b :: acc) bs

/-- The reverse-accumulator scan equals `splitColon` under the flushed
accumulator. -/
theorem splitColonRevGo_eq (bs : Bytes) :
    ∀ acc, splitColonRevGo acc bs
        = (splitColon bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons b t ih =>
    intro acc
    show (if b == COLON then some (acc.reverse, t) else splitColonRevGo (b :: acc) t)
        = (splitColon (b :: t)).map (fun p => (acc.reverse ++ p.1, p.2))
    rw [splitColon]
    by_cases h : b == COLON
    · simp [h]
    · rw [if_neg h, if_neg h, ih (b :: acc), Option.map_map]
      rcases splitColon t with _ | ⟨pre, rest⟩
      · rfl
      · simp

/-- The loop form `splitColon` compiles to. -/
def splitColonTail (bs : Bytes) : Option (Bytes × Bytes) := splitColonRevGo [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `splitColon`. -/
@[csimp] theorem splitColon_eq_tail : @splitColon = @splitColonTail := by
  funext bs
  rw [splitColonTail, splitColonRevGo_eq bs []]
  rcases splitColon bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Fold header lines out of the head block until the blank line. A line without
a `:` (the request line) is skipped — it carries no framing signal. Fuel-bounded
for kernel reduction; `head.length + 1` always suffices (each step consumes at
least a line's `CRLF`). -/
def headerFieldsFuel : Nat → Bytes → List Smuggling.Header
  | 0, _ => []
  | fuel + 1, bs =>
    match takeLine bs with
    | none => []
    | some ([], _) => []                      -- blank line: end of the head block
    | some (line, rest) =>
      match splitColon line with
      | none => headerFieldsFuel fuel rest     -- no colon (request line): skip
      | some (name, value) =>
        { name := name, value := value } :: headerFieldsFuel fuel rest

/-- Tail-recursive `headerFieldsFuel`: fields accumulate in reverse, one loop
iteration per header line, constant stack. -/
def headerFieldsFuelRevGo : Nat → Bytes → List Smuggling.Header → List Smuggling.Header
  | 0, _, acc => acc.reverse
  | fuel + 1, bs, acc =>
    match takeLine bs with
    | none => acc.reverse
    | some ([], _) => acc.reverse
    | some (line, rest) =>
      match splitColon line with
      | none => headerFieldsFuelRevGo fuel rest acc
      | some (name, value) =>
        headerFieldsFuelRevGo fuel rest ({ name := name, value := value } :: acc)

/-- The reverse-accumulator fold equals `headerFieldsFuel` under the flushed
accumulator. -/
theorem headerFieldsFuelRevGo_eq :
    ∀ (fuel : Nat) (bs : Bytes) (acc : List Smuggling.Header),
      headerFieldsFuelRevGo fuel bs acc = acc.reverse ++ headerFieldsFuel fuel bs := by
  intro fuel
  induction fuel with
  | zero => intro bs acc; simp [headerFieldsFuelRevGo, headerFieldsFuel]
  | succ f ih =>
    intro bs acc
    unfold headerFieldsFuelRevGo headerFieldsFuel
    rcases htl : takeLine bs with _ | ⟨line, rest⟩
    · simp [htl]
    · rcases line with _ | ⟨x, xs⟩
      · simp [htl]
      · rcases hsc : splitColon (x :: xs) with _ | ⟨name, value⟩ <;>
          simp [htl, hsc, ih rest]

/-- The loop form `headerFieldsFuel` compiles to. -/
def headerFieldsFuelTail (fuel : Nat) (bs : Bytes) : List Smuggling.Header :=
  headerFieldsFuelRevGo fuel bs []

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `headerFieldsFuel`. -/
@[csimp] theorem headerFieldsFuel_eq_tail : @headerFieldsFuel = @headerFieldsFuelTail := by
  funext fuel bs
  rw [headerFieldsFuelTail, headerFieldsFuelRevGo_eq fuel bs []]
  rfl

/-- Parse the framing-relevant head into a `Smuggling.Request`. The decision
classifiers (`clStatus`/`teStatus`) read only the `content-length` /
`transfer-encoding` fields, so carrying every field is faithful and harmless. -/
def parseFramingHead (head : Bytes) : Smuggling.Request :=
  { headers := headerFieldsFuel (head.length + 1) head }

/-! ## (3) The whole raw-buffer framing decision -/

/-- **`frameRaw`.** The complete request-framing decision over a *raw* buffer:
scan for the head end, parse the head, refuse a head whose line terminators are
not unambiguous (`noBareLF`, RFC 9112 §2.2 — see (1b)), and take the proven
smuggling-safe boundary `Body.Framing.frameFixed`. No head yet ⇒ `needMore`.
This is the decision the trusted host reimplemented in `http.rs`; here it is one
proven function of the bytes.

The CL/TE classification runs **first** so a smuggling reject keeps naming the
smuggling reason it always named (`frameRaw_no_smuggle` is unchanged); the
bare-LF refusal fires on every other bare-LF head, before any boundary is
computed and regardless of whether the body has arrived. -/
def frameRaw (buf : Bytes) : Framing.Outcome :=
  match scanHeadEnd buf with
  | none => .needMore
  | some headEnd =>
    match Smuggling.decide (parseFramingHead (buf.take headEnd)) with
    | .reject r => .reject r
    | _ =>
      if noBareLF (buf.take headEnd) then
        Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd))
      else
        .reject .bareLF

/-! ### The gate's two shapes -/

/-- On a head with unambiguous line terminators the gate is **exactly** the
proven boundary `frameFixed` — the bare-LF refusal adds a refusal and changes
nothing else. -/
theorem frameRaw_clean (buf : Bytes) (headEnd : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hclean : noBareLF (buf.take headEnd) = true) :
    frameRaw buf = Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd)) := by
  rw [frameRaw, hscan]
  cases hdec : Smuggling.decide (parseFramingHead (buf.take headEnd)) <;>
    simp [Framing.frameFixed, hdec, hclean]

/-- **The gate fails closed on a bare LF.** A head the scan locates that carries
a bare LF is rejected — never `complete`, never a boundary the host acts on. -/
theorem frameRaw_bareLF_rejected (buf : Bytes) (headEnd : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hbare : noBareLF (buf.take headEnd) = false) :
    (∃ r, frameRaw buf = .reject r) ∧ (∀ c, frameRaw buf ≠ .complete c) := by
  have hex : ∃ r, frameRaw buf = .reject r := by
    rw [frameRaw, hscan]
    cases hdec : Smuggling.decide (parseFramingHead (buf.take headEnd)) with
    | reject r => exact ⟨r, by simp [hdec]⟩
    | length n => exact ⟨Smuggling.Reason.bareLF, by simp [hdec, hbare]⟩
    | chunked => exact ⟨Smuggling.Reason.bareLF, by simp [hdec, hbare]⟩
    | empty => exact ⟨Smuggling.Reason.bareLF, by simp [hdec, hbare]⟩
  obtain ⟨r, hr⟩ := hex
  exact ⟨⟨r, hr⟩, by intro c h; rw [hr] at h; exact Framing.Outcome.noConfusion h⟩

/-- **★ The gate admits only unambiguously-terminated heads.** Whenever
`frameRaw` hands the host a complete request boundary, the head it framed
contains no bare LF: every line terminator in an admitted head is a full CRLF,
so this core's CRLF-only parse is the *only* parse RFC 9112 §2.2 permits of that
head. Nothing downstream — the hop-by-hop strip above all — can be shown a head
whose fields it reads differently from the next hop. -/
theorem frameRaw_complete_noBareLF (buf : Bytes) (c : Nat)
    (h : frameRaw buf = .complete c) :
    ∃ headEnd, scanHeadEnd buf = some headEnd ∧ noBareLF (buf.take headEnd) = true := by
  cases hscan : scanHeadEnd buf with
  | none => rw [frameRaw, hscan] at h; exact absurd h (by simp)
  | some headEnd =>
    refine ⟨headEnd, rfl, ?_⟩
    cases hclean : noBareLF (buf.take headEnd) with
    | false => exact absurd h ((frameRaw_bareLF_rejected buf headEnd hscan hclean).2 c)
    | true => rfl

/-! ## No smuggling: a CL/TE overlap in the raw bytes is never a length boundary -/

/-- **`frameRaw_no_smuggle` (headline).** If the head the scan locates parses to a
request that frames *both* a valid `Content-Length` and a chunked
`Transfer-Encoding`, `frameRaw` **rejects** the raw buffer — it is never
`complete`. So the host can never consume only the `Content-Length` octets while
leaving the chunked tail as a smuggled second request. The raw-buffer form of
`Body.Framing.frame_no_smuggle` (itself the boundary form of
`Body.Smuggling.no_desync`). -/
theorem frameRaw_no_smuggle (buf : Bytes) (headEnd n : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hcl : Smuggling.clStatus (parseFramingHead (buf.take headEnd)) = .present n)
    (hte : Smuggling.teStatus (parseFramingHead (buf.take headEnd)) = .chunked) :
    frameRaw buf = .reject .bothClAndTe
    ∧ (∀ c, frameRaw buf ≠ .complete c) := by
  have hdec : Smuggling.decide (parseFramingHead (buf.take headEnd)) = .reject .bothClAndTe := by
    simp only [Smuggling.decide, hcl, hte, Smuggling.decideOn]
  have hfr : frameRaw buf = .reject .bothClAndTe := by
    rw [frameRaw, hscan]; simp [hdec]
  exact ⟨hfr, by intro c h; rw [hfr] at h; exact Framing.Outcome.noConfusion h⟩

/-- **`frameRaw_no_smuggle_general`.** The full guarantee: whenever *any*
`Content-Length` field (valid, invalid, or duplicated) is present alongside a
chunked `Transfer-Encoding`, `frameRaw` rejects and is never `complete`. -/
theorem frameRaw_no_smuggle_general (buf : Bytes) (headEnd : Nat)
    (hscan : scanHeadEnd buf = some headEnd)
    (hcl : Smuggling.clStatus (parseFramingHead (buf.take headEnd)) ≠ .absent)
    (hte : Smuggling.teStatus (parseFramingHead (buf.take headEnd)) = .chunked) :
    (∃ r, frameRaw buf = .reject r) ∧ (∀ c, frameRaw buf ≠ .complete c) := by
  obtain ⟨⟨r, hr⟩, _⟩ :=
    Smuggling.no_desync_general (parseFramingHead (buf.take headEnd)) hcl hte
  have hfr : frameRaw buf = .reject r := by
    rw [frameRaw, hscan]; simp [hr]
  exact ⟨⟨r, hfr⟩, by intro c h; rw [hfr] at h; exact Framing.Outcome.noConfusion h⟩

/-! ## Faithfulness: the consumed prefix is exactly head ++ body -/

/-- **`frameRaw_faithful` (headline).** When the scan locates the head end and the
parsed head frames a fixed `Content-Length` of `n` octets, over a buffer
`head ++ body ++ rest` with `head` the located head (length `headEnd`) and `body`
exactly `n` octets, `frameRaw` reports `complete (headEnd + n)` and that boundary
splits the buffer exactly: the consumed prefix is `head ++ body`, the remainder
is `rest` verbatim. The boundary is a function of the head alone — no
attacker-chosen `body`/`rest` byte can shift it. -/
theorem frameRaw_faithful (head body rest : Bytes) (headEnd n : Nat)
    (hhead : head.length = headEnd) (hbody : body.length = n)
    (hscan : scanHeadEnd (head ++ body ++ rest) = some headEnd)
    (hclean : noBareLF head = true)
    (hdec : Smuggling.decide (parseFramingHead head) = .length n) :
    frameRaw (head ++ body ++ rest) = .complete (headEnd + n)
    ∧ (head ++ body ++ rest).take (headEnd + n) = head ++ body
    ∧ (head ++ body ++ rest).drop (headEnd + n) = rest := by
  have htakehead : (head ++ body ++ rest).take headEnd = head := by
    rw [List.append_assoc, ← hhead]; exact List.take_left
  have hfr : frameRaw (head ++ body ++ rest)
      = Framing.frameFixed (head ++ body ++ rest) headEnd (parseFramingHead head) := by
    rw [frameRaw_clean _ headEnd hscan (by rw [htakehead]; exact hclean), htakehead]
  have hff := Framing.framing_faithful head body rest headEnd n (parseFramingHead head)
    hhead hbody hdec
  exact ⟨hfr.trans hff.1, hff.2.1, hff.2.2⟩

/-- **`frameRaw_faithful_empty`.** A body-less request (the parsed head frames no
body) consumes exactly the located head; the whole remainder is the next request
verbatim. -/
theorem frameRaw_faithful_empty (head rest : Bytes) (headEnd : Nat)
    (hhead : head.length = headEnd)
    (hscan : scanHeadEnd (head ++ rest) = some headEnd)
    (hclean : noBareLF head = true)
    (hdec : Smuggling.decide (parseFramingHead head) = .empty) :
    frameRaw (head ++ rest) = .complete headEnd
    ∧ (head ++ rest).take headEnd = head
    ∧ (head ++ rest).drop headEnd = rest := by
  have htakehead : (head ++ rest).take headEnd = head := by
    rw [← hhead]; exact List.take_left
  have hfr : frameRaw (head ++ rest)
      = Framing.frameFixed (head ++ rest) headEnd (parseFramingHead head) := by
    rw [frameRaw_clean _ headEnd hscan (by rw [htakehead]; exact hclean), htakehead]
  have hff := Framing.framing_faithful_empty head rest headEnd (parseFramingHead head) hhead hdec
  exact ⟨hfr.trans hff.1, hff.2.1, hff.2.2⟩

/-! ## No overread: a complete boundary stays inside the buffer -/

/-- **`frameRaw_bounded`.** A `complete` framing never runs past the buffer: the
consumed count is at most the buffer length. -/
theorem frameRaw_bounded (buf : Bytes) (c : Nat) (h : frameRaw buf = .complete c) :
    c ≤ buf.length := by
  obtain ⟨headEnd, hscan, hclean⟩ := frameRaw_complete_noBareLF buf c h
  rw [frameRaw_clean buf headEnd hscan hclean] at h
  exact Framing.frame_bounded buf headEnd c (parseFramingHead (buf.take headEnd)) h

/-! ## Concrete non-vacuity: a real CL.TE wire head is rejected -/

/-- A real CL.TE request head on the wire:

    content-length: 6 CRLF
    transfer-encoding: chunked CRLF
    CRLF

built from the lower-case field-name constants and the `chunked` token. The
scan locates its `CRLFCRLF`; the parse recovers a `Content-Length: 6` and a
chunked `Transfer-Encoding`. -/
def clteHead : Bytes :=
  Smuggling.clName ++ [COLON, 32, 54] ++ crlf ++          -- "content-length: 6"
  Smuggling.teName ++ [COLON, 32] ++ Smuggling.chunkedToken ++ crlf ++  -- "transfer-encoding: chunked"
  crlf

/-- The raw CL.TE buffer: the head plus the attacker chunk terminator and the
smuggled tail (`0 CRLF SMUGGLED`). The tail is irrelevant to the reject (a
function of the head), but long enough that the naive length-only framer below
*would* compute a 6-octet-body boundary — the desync `frameRaw` refuses. -/
def clteBuf : Bytes :=
  clteHead ++ [48, CR, LF, 83, 77, 85, 71, 71, 76, 69, 68]   -- "0" CRLF "SMUGGLED"

/-- The scan locates the head end of the CL.TE buffer. -/
theorem clte_scan : scanHeadEnd clteBuf = some clteHead.length := by decide

/-- The parsed CL.TE head frames a valid `Content-Length: 6`. -/
theorem clte_parsed_cl :
    Smuggling.clStatus (parseFramingHead (clteBuf.take clteHead.length)) = .present 6 := by decide

/-- The parsed CL.TE head frames a chunked `Transfer-Encoding`. -/
theorem clte_parsed_te :
    Smuggling.teStatus (parseFramingHead (clteBuf.take clteHead.length)) = .chunked := by decide

/-- **`frameRaw` rejects the raw CL.TE buffer.** The smuggling decision now lives
in the core over raw bytes: the boundary is never computed for a CL/TE overlap,
so the `0`-terminated chunk tail is never split off as a separate request. -/
theorem clte_frameRaw_reject : frameRaw clteBuf = .reject .bothClAndTe :=
  (frameRaw_no_smuggle clteBuf clteHead.length 6 clte_scan clte_parsed_cl clte_parsed_te).1

/-- **`frameRaw` never frames the CL.TE buffer to the 6-octet-body boundary** —
the exact desync a length-only host framer would produce. -/
theorem clte_frameRaw_not_length (c : Nat) : frameRaw clteBuf ≠ .complete c :=
  (frameRaw_no_smuggle clteBuf clteHead.length 6 clte_scan clte_parsed_cl clte_parsed_te).2 c

/-! ## Concrete: a body-less GET is framed to its exact boundary -/

/-- A body-less request head:

    host: x CRLF
    CRLF

(the request line is elided; it carries no framing signal and the parser skips
lines without a `:`). -/
def getHead : Bytes :=
  [104, 111, 115, 116] ++ [COLON, 32, 120] ++ crlf ++      -- "host: x"
  crlf

/-- The parsed GET head frames no body. -/
theorem get_parsed_empty :
    Smuggling.decide (parseFramingHead getHead) = .empty := by decide

/-- The scan locates the GET head end. -/
theorem get_scan : scanHeadEnd getHead = some getHead.length := by decide

/-- **`frameRaw` frames the body-less GET to its exact boundary.** (The general
`frameRaw_faithful_empty` above extends this to any pipelined remainder once the
scan is located.) -/
theorem get_frameRaw_complete : frameRaw getHead = .complete getHead.length := by
  have h := frameRaw_faithful_empty getHead [] getHead.length rfl
    (by rw [List.append_nil]; exact get_scan) (by decide) get_parsed_empty
  rw [List.append_nil] at h
  exact h.1

/-! ## Concrete non-vacuity: the crafted bare-LF head the deployed proxy leaked

The exact vector `conformance/proxy/barelf_smuggle.py` sends. Before the
refusal, the gate ADMITTED it, the CRLF-only hop-by-hop strip saw a single field
named `x-probe`, and `Connection: keep-alive` reached the upstream. -/

/-- The crafted head:

    host: x CRLF
    x-probe: 1 LF connection: keep-alive CRLF
    CRLF

— the hop-by-hop field hides behind the bare LF, inside `x-probe`'s value. -/
def bareLFHead : Bytes :=
  [104, 111, 115, 116] ++ [COLON, 32, 120] ++ crlf ++                     -- "host: x"
  [120, 45, 112, 114, 111, 98, 101] ++ [COLON, 32, 49] ++ [LF] ++         -- "x-probe: 1" LF
  [99, 111, 110, 110, 101, 99, 116, 105, 111, 110] ++
    [COLON, 32, 107, 101, 101, 112, 45, 97, 108, 105, 118, 101] ++ crlf ++ -- "connection: keep-alive"
  crlf

/-- The scan locates the crafted head's end — it *is* a well-terminated head
block; only its interior line terminators are ambiguous. -/
theorem bareLF_scan : scanHeadEnd bareLFHead = some bareLFHead.length := by decide

/-- The crafted head is not unambiguously terminated. -/
theorem bareLF_not_clean : noBareLF bareLFHead = false := by decide

/-- **The gate refuses the crafted head.** -/
theorem bareLF_frameRaw_reject : frameRaw bareLFHead = .reject .bareLF := by decide

/-- **…and never frames it to a boundary**, so it never reaches the proxy
forward and the hidden `connection` field is never handed to an upstream. -/
theorem bareLF_frameRaw_not_complete (c : Nat) : frameRaw bareLFHead ≠ .complete c := by
  rw [bareLF_frameRaw_reject]; intro h; exact Framing.Outcome.noConfusion h

/-- The gate **as it shipped** — the same decision without the bare-LF refusal.

**Proof-only baseline. Nothing may call this.** It exists to witness that the
refusal above changes a real verdict (`bareLF_gate_not_vacuous`), i.e. as the
mutant the new theorem kills; it is the pre-2026-07-25 behaviour, which forwarded
a hop-by-hop field hidden behind a bare LF. It is referenced by exactly two
theorems in this file and by nothing else in the tree — no `@[export]`, no host
call site. The one seam the deployed reactor crosses is `frameRequestExport`
below, and it is literally `encodeOutcome ∘ frameRaw`; re-pointing it here would
change the seam payload, which `lenient_seam_differs` machine-checks. -/
def frameRawLenient (buf : Bytes) : Framing.Outcome :=
  match scanHeadEnd buf with
  | none => .needMore
  | some headEnd => Framing.frameFixed buf headEnd (parseFramingHead (buf.take headEnd))

/-- **The refusal is not vacuous, and this is the measured bug.** The gate as it
shipped ADMITS the crafted head to its exact boundary — which is how
`Connection: keep-alive` after a bare LF reached the upstream unstripped — and
the two gates disagree on it. -/
theorem bareLF_gate_not_vacuous :
    frameRawLenient bareLFHead = .complete bareLFHead.length
    ∧ frameRaw bareLFHead ≠ frameRawLenient bareLFHead := by
  have hn : frameRawLenient bareLFHead = .complete bareLFHead.length := by decide
  refine ⟨hn, ?_⟩
  rw [hn, bareLF_frameRaw_reject]
  intro h; exact Framing.Outcome.noConfusion h

/-- On a head with unambiguous terminators the refusal changes nothing: the two
gates agree on the body-less GET. -/
theorem clean_gates_agree : frameRaw getHead = frameRawLenient getHead := by decide

/-! ## The mutant the raw-boundary proof buys -/

/-- A naive host framer that consults only `Content-Length`, ignoring
`Transfer-Encoding` — the vulnerable behaviour `frameRaw` replaces. -/
def frameRawNaive (buf : Bytes) : Framing.Outcome :=
  match scanHeadEnd buf with
  | none => .needMore
  | some headEnd =>
    match Smuggling.clStatus (parseFramingHead (buf.take headEnd)) with
    | .present n => if headEnd + n ≤ buf.length then .complete (headEnd + n) else .needMore
    | _ => .needMore

/-- **The mutant desyncs on the raw CL.TE buffer.** The naive framer computes a
6-octet-body boundary — precisely the split `frameRaw` refuses
(`clte_frameRaw_reject`). The two disagree, so the raw-buffer contract is not
vacuous: a natural host mutant violates it. -/
theorem naive_would_smuggle_raw :
    frameRawNaive clteBuf = .complete (clteHead.length + 6)
    ∧ frameRaw clteBuf ≠ frameRawNaive clteBuf := by
  have hn : frameRawNaive clteBuf = .complete (clteHead.length + 6) := by decide
  refine ⟨hn, ?_⟩
  rw [hn, clte_frameRaw_reject]
  intro h; exact Framing.Outcome.noConfusion h

/-! ## (4) The host-facing C-ABI seam -/

/-- A framing reason as one wire byte (host reads it to pick a close/response). -/
def reasonByte : Smuggling.Reason → UInt8
  | .bothClAndTe => 0
  | .dupContentLength => 1
  | .invalidContentLength => 2
  | .chunkedNotLast => 3
  | .unsupportedTransferEncoding => 4
  | .bareLF => 5

/-- Little-endian 8-octet encoding of a consumed count (host reads the boundary). -/
def le64 (n : Nat) : Bytes :=
  (List.range 8).map (fun i => UInt8.ofNat (n / (256 ^ i) % 256))

/-- Encode a framing outcome for the host: `0`=needMore, `1 r`=reject reason,
`2 …le64`=complete count. -/
def encodeOutcome : Framing.Outcome → Bytes
  | .needMore => [0]
  | .reject r => [1, reasonByte r]
  | .complete c => 2 :: le64 c

/-- **`drorb_frame_request`.** The seam the host crosses instead of deciding
framing itself: the raw accumulation buffer in, the encoded `frameRaw` verdict
out. Total `ByteArray → ByteArray`. -/
@[export drorb_frame_request]
def frameRequestExport (input : ByteArray) : ByteArray :=
  ByteArray.mk (encodeOutcome (frameRaw input.toList)).toArray

/-- The encoder maps a CL/TE reject to the two host bytes `[1, 0]`. -/
theorem encode_reject_bothClAndTe :
    encodeOutcome (.reject .bothClAndTe) = [1, 0] := rfl

/-- **ABI check.** The exported seam's payload for the raw CL.TE buffer is the
reject encoding `[1, 0]`: the host is told to refuse, never handed a length
boundary. (`frameRequestExport` wraps exactly `encodeOutcome ∘ frameRaw`.) -/
theorem clte_encoded : encodeOutcome (frameRaw clteBuf) = [1, 0] := by
  rw [clte_frameRaw_reject]; rfl

/-- **ABI check for the bare-LF refusal.** The seam's payload for the crafted
bare-LF head is `[1, 5]` — a reject. The host reads byte `0` = `1` and closes;
it does not read the reason byte (`http.rs::next_request`), so the new reason
needs no host change. -/
theorem bareLF_encoded : encodeOutcome (frameRaw bareLFHead) = [1, 5] := by
  rw [bareLF_frameRaw_reject]; rfl

/-- **Regression guard on the seam.** The lenient gate and the shipped gate do
not merely differ as `Outcome`s — they differ in the *bytes crossing the C ABI*.
`frameRequestExport` is `encodeOutcome ∘ frameRaw`; anyone who re-points it at
`frameRawLenient` changes the host's verdict for the crafted head from "reject,
close" to "complete, forward", and this inequality is what says so. -/
theorem lenient_seam_differs :
    encodeOutcome (frameRawLenient bareLFHead) ≠ encodeOutcome (frameRaw bareLFHead) := by
  decide

end FrameRaw
end Body
