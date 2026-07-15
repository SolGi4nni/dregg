import Reactor.Serialize
import Proto.Decimal

/-!
# A proven HTTP/1.1 response parser — the client dual of the request parser

`Arena.Parse` parses an HTTP/1.1 *request* head (the server's inbound half).
This module is its outbound dual: it parses an HTTP/1.1 *response* — status
line (`HTTP/1.1 SP code SP reason`), header block, and body — the half a
verified *client* needs to read what an upstream sends back.

The design is the structural inverse of the response serializer
`Reactor.serialize`: `parse` strips the fixed `HTTP/1.1 ` prefix, reads the
decimal status token up to the first `SP`, the reason up to the first `CRLF`,
then each header line up to its `CRLF` until the blank line, and takes the rest
as the body. Every scan is a single left-to-right pass over the cons-list (no
`O(n²)` re-indexing), so the whole parse is linear.

## What is proven

`parse_serialize` — the client↔server round-trip: a response the server
*serializes* parses back to the same response (with the server-derived
`Content-Length` header made explicit by `wireForm`):

    parse (Reactor.serialize resp) = some (wireForm resp)

for every well-formed response (`WF`: the reason and header names/values carry
no bare `CR`, and header names carry no `:` — exactly the RFC 9112 field
discipline). The status code is recovered as a `Nat` (via the proven decimal
inverse `Proto.Dec.dval_natToDec`), so the client reads a real status code, not
just bytes. `parse_serialize_ok200` discharges `WF` on a concrete `200 OK`,
witnessing non-vacuity.

0 sorries; axioms ⊆ `{propext, Quot.sound, Classical.choice}`.
-/

namespace Proto
namespace ResponseParse

open Reactor (Response Wire build serialize serializeWire statusLine headerLine
  renderHeaders allHeaders crlf http11 clName natToDec)

abbrev Bytes := List UInt8

def CR : UInt8 := 13
def LF : UInt8 := 10
def SP : UInt8 := 32
def COLON : UInt8 := 58

/-! ## Byte-scanning primitives (single left-to-right pass each) -/

/-- Strip an exact literal prefix `p` from `bs`; `none` if `bs` does not start
with `p`. -/
def stripPrefix : Bytes → Bytes → Option Bytes
  | [], bs => some bs
  | _ :: _, [] => none
  | p :: ps, b :: bs => if p == b then stripPrefix ps bs else none

/-- Read up to (and consume) the first `sep`; returns the bytes before it and
the bytes after it. `none` if `sep` never occurs. -/
def takeUntil (sep : UInt8) : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs =>
    if b == sep then some ([], bs)
    else (takeUntil sep bs).map (fun p => (b :: p.1, p.2))

/-! ### Bounded-stack scans

Each list scan here recurses *inside* `Option.map` (or conses after the
recursive call), so the compiled code pushes one C stack frame per byte (or per
header line) — recursion depth = input length, and a large input exhausts the
thread stack before any byte gate can refuse it. Each scan gets a
reverse-accumulator (tail-recursive) twin that the compiler emits as a loop —
`O(1)` stack regardless of input — installed as the compiled implementation by
`@[csimp]`. Every theorem (the `*_append` inversion lemmas, the round-trips)
keeps referring to the unchanged spec. -/

/-- Tail-recursive `takeUntil`: the prefix accumulates in reverse, one loop
iteration per byte, constant stack. -/
def takeUntilRevGo (sep : UInt8) : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | acc, b :: bs =>
    if b == sep then some (acc.reverse, bs)
    else takeUntilRevGo sep (b :: acc) bs

/-- The reverse-accumulator scan equals `takeUntil` under the flushed
accumulator. -/
theorem takeUntilRevGo_eq (sep : UInt8) (bs : Bytes) :
    ∀ acc, takeUntilRevGo sep acc bs
        = (takeUntil sep bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons b t ih =>
    intro acc
    show (if b == sep then some (acc.reverse, t) else takeUntilRevGo sep (b :: acc) t)
        = (takeUntil sep (b :: t)).map (fun p => (acc.reverse ++ p.1, p.2))
    rw [takeUntil]
    by_cases h : b == sep
    · simp [h]
    · rw [if_neg h, if_neg h, ih (b :: acc), Option.map_map]
      rcases takeUntil sep t with _ | ⟨pre, rest⟩
      · rfl
      · simp

/-- The loop form `takeUntil` compiles to. -/
def takeUntilTail (sep : UInt8) (bs : Bytes) : Option (Bytes × Bytes) :=
  takeUntilRevGo sep [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `takeUntil`. -/
@[csimp] theorem takeUntil_eq_tail : @takeUntil = @takeUntilTail := by
  funext sep bs
  rw [takeUntilTail, takeUntilRevGo_eq sep bs []]
  rcases takeUntil sep bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Read up to (and consume) the first `CRLF`; returns the bytes before it and
the bytes after it. `none` if no `CRLF` occurs. -/
def takeUntilCrlf : Bytes → Option (Bytes × Bytes)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if a == CR && b == LF then some ([], rest)
    else (takeUntilCrlf (b :: rest)).map (fun p => (a :: p.1, p.2))

/-- Tail-recursive `takeUntilCrlf`: same reverse-accumulator loop shape as
`takeUntilRevGo`, constant stack. -/
def takeUntilCrlfRevGo : Bytes → Bytes → Option (Bytes × Bytes)
  | _, [] => none
  | _, [_] => none
  | acc, a :: b :: rest =>
    if a == CR && b == LF then some (acc.reverse, rest)
    else takeUntilCrlfRevGo (a :: acc) (b :: rest)

/-- The reverse-accumulator scan equals `takeUntilCrlf` under the flushed
accumulator. -/
theorem takeUntilCrlfRevGo_eq (bs : Bytes) :
    ∀ acc, takeUntilCrlfRevGo acc bs
        = (takeUntilCrlf bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  induction bs with
  | nil => intro acc; rfl
  | cons a xs ih =>
    intro acc
    match xs, ih with
    | [], _ => rfl
    | b :: rest, ih =>
      show (if a == CR && b == LF then some (acc.reverse, rest)
              else takeUntilCrlfRevGo (a :: acc) (b :: rest))
          = (takeUntilCrlf (a :: b :: rest)).map (fun p => (acc.reverse ++ p.1, p.2))
      rw [takeUntilCrlf]
      by_cases h : a == CR && b == LF
      · simp [h]
      · rw [if_neg h, if_neg h, ih (a :: acc), Option.map_map]
        rcases takeUntilCrlf (b :: rest) with _ | ⟨pre, rest'⟩
        · rfl
        · simp

/-- The loop form `takeUntilCrlf` compiles to. -/
def takeUntilCrlfTail (bs : Bytes) : Option (Bytes × Bytes) :=
  takeUntilCrlfRevGo [] bs

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `takeUntilCrlf`. -/
@[csimp] theorem takeUntilCrlf_eq_tail : @takeUntilCrlf = @takeUntilCrlfTail := by
  funext bs
  rw [takeUntilCrlfTail, takeUntilCrlfRevGo_eq bs []]
  rcases takeUntilCrlf bs with _ | ⟨pre, rest⟩
  · rfl
  · simp

/-- Parse one header line `name ":" SP value`: name up to the first `:`, then a
single `SP`, then the value (the rest of the line). -/
def parseHeaderLine (line : Bytes) : Option (Bytes × Bytes) := do
  let (name, rest) ← takeUntil COLON line
  let value ← stripPrefix [SP] rest
  some (name, value)

/-- Parse header lines until the blank line; returns the parsed headers and the
body (everything after the blank line). Fuel-bounded for totality; the entry
point `parseHeaders` supplies `bs.length`, always enough (each step consumes at
least the two `CRLF` bytes). The blank line is detected by `stripPrefix crlf`. -/
def parseHeadersFuel : Nat → Bytes → Option (List (Bytes × Bytes) × Bytes)
  | 0, _ => none
  | fuel + 1, bs =>
    match stripPrefix crlf bs with
    | some body => some ([], body)
    | none =>
      match takeUntilCrlf bs with
      | none => none
      | some (line, after) =>
        match parseHeaderLine line with
        | none => none
        | some hdr =>
          match parseHeadersFuel fuel after with
          | none => none
          | some (hs, body) => some (hdr :: hs, body)

/-- Tail-recursive `parseHeadersFuel`: parsed headers accumulate in reverse,
one loop iteration per header line, constant stack. -/
def parseHeadersFuelRevGo : Nat → Bytes → List (Bytes × Bytes) →
    Option (List (Bytes × Bytes) × Bytes)
  | 0, _, _ => none
  | fuel + 1, bs, acc =>
    match stripPrefix crlf bs with
    | some body => some (acc.reverse, body)
    | none =>
      match takeUntilCrlf bs with
      | none => none
      | some (line, after) =>
        match parseHeaderLine line with
        | none => none
        | some hdr => parseHeadersFuelRevGo fuel after (hdr :: acc)

/-- The reverse-accumulator pass equals `parseHeadersFuel` under the flushed
accumulator. -/
theorem parseHeadersFuelRevGo_eq :
    ∀ (fuel : Nat) (bs : Bytes) (acc : List (Bytes × Bytes)),
      parseHeadersFuelRevGo fuel bs acc
        = (parseHeadersFuel fuel bs).map (fun p => (acc.reverse ++ p.1, p.2)) := by
  intro fuel
  induction fuel with
  | zero => intro bs acc; rfl
  | succ f ih =>
    intro bs acc
    unfold parseHeadersFuelRevGo parseHeadersFuel
    rcases hsp : stripPrefix crlf bs with _ | body
    · rcases htc : takeUntilCrlf bs with _ | ⟨line, after⟩
      · simp [hsp, htc]
      · rcases hpl : parseHeaderLine line with _ | hdr
        · simp [hsp, htc, hpl]
        · rcases hpf : parseHeadersFuel f after with _ | ⟨hs, body⟩ <;>
            simp [hsp, htc, hpl, hpf, ih after (hdr :: acc)]
    · simp [hsp]

/-- The loop form `parseHeadersFuel` compiles to. -/
def parseHeadersFuelTail (fuel : Nat) (bs : Bytes) :
    Option (List (Bytes × Bytes) × Bytes) :=
  parseHeadersFuelRevGo fuel bs []

/-- **The loop/spec agreement.** Installs the constant-stack loop as the
compiled implementation of `parseHeadersFuel`. -/
@[csimp] theorem parseHeadersFuel_eq_tail : @parseHeadersFuel = @parseHeadersFuelTail := by
  funext fuel bs
  rw [parseHeadersFuelTail, parseHeadersFuelRevGo_eq fuel bs []]
  rcases parseHeadersFuel fuel bs with _ | ⟨hs, body⟩
  · rfl
  · simp

/-- Parse the header block (and split off the body). -/
def parseHeaders (bs : Bytes) : Option (List (Bytes × Bytes) × Bytes) :=
  parseHeadersFuel bs.length bs

/-- **The response parser.** Status line, header block, body → a `Response`
whose numeric `status` is decoded from its decimal token. -/
def parse (bs : Bytes) : Option Response := do
  let bs ← stripPrefix (http11 ++ [SP]) bs
  let (statusTok, bs) ← takeUntil SP bs
  let (reason, bs) ← takeUntilCrlf bs
  let (headers, body) ← parseHeaders bs
  some { status := Dec.dval 0 statusTok, reason := reason, headers := headers, body := body }

/-! ## Well-formedness and the wire form -/

/-- The RFC 9112 field discipline the round-trip needs: the reason and every
header name/value carry no bare `CR`, and header names carry no `:`. -/
def WF (resp : Response) : Prop :=
  CR ∉ resp.reason ∧
  ∀ kv ∈ resp.headers, COLON ∉ kv.1 ∧ CR ∉ kv.1 ∧ CR ∉ kv.2

/-- The response as it appears on the wire: identical to `resp` but with the
serializer-derived `Content-Length` header appended (the one header the server
adds by construction). `parse` recovers exactly this. -/
def wireForm (resp : Response) : Response :=
  { status := resp.status, reason := resp.reason,
    headers := resp.headers ++ [(clName, natToDec resp.body.length)],
    body := resp.body }

/-! ## Primitive-scan lemmas -/

theorem stripPrefix_append (p rest : Bytes) : stripPrefix p (p ++ rest) = some rest := by
  induction p with
  | nil => rfl
  | cons a t ih => simp only [List.cons_append, stripPrefix, beq_self_eq_true, if_true]; exact ih

/-- If `bs` does not start with `p`'s first byte, `stripPrefix p bs = none`. -/
theorem stripPrefix_cons_ne (a : UInt8) (ps bs : Bytes) (b : UInt8) (hb : (a == b) = false) :
    stripPrefix (a :: ps) (b :: bs) = none := by
  simp [stripPrefix, hb]

theorem takeUntil_append (sep : UInt8) (pre rest : Bytes) (h : sep ∉ pre) :
    takeUntil sep (pre ++ sep :: rest) = some (pre, rest) := by
  induction pre with
  | nil => simp [takeUntil]
  | cons a t ih =>
    have ha : (a == sep) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hEq; exact h (by simp [hEq])
    have ht : sep ∉ t := fun hmem => h (by simp [hmem])
    rw [List.cons_append, takeUntil]
    simp only [ha, Bool.false_eq_true, if_false, ih ht]
    rfl

theorem takeUntilCrlf_append (pre rest : Bytes) (h : CR ∉ pre) :
    takeUntilCrlf (pre ++ crlf ++ rest) = some (pre, rest) := by
  induction pre with
  | nil => simp [takeUntilCrlf, crlf, CR, LF]
  | cons a t ih =>
    have ha : (a == CR) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hEq; exact h (by simp [hEq])
    have ht : CR ∉ t := fun hmem => h (by simp [hmem])
    have hcons : (a :: t) ++ crlf ++ rest = a :: (t ++ crlf ++ rest) := by simp
    rw [hcons]
    cases hb : t ++ crlf ++ rest with
    | nil =>
      exfalso
      have : (t ++ crlf ++ rest).length = 0 := by rw [hb]; rfl
      simp [crlf] at this
    | cons b tl =>
      simp only [takeUntilCrlf, ha, Bool.false_and, if_false]
      have hrec : takeUntilCrlf (t ++ crlf ++ rest) = some (t, rest) := ih ht
      rw [hb] at hrec
      rw [hrec]; simp

/-- A header-line parse inverts the serializer's `headerLine` under `WF`. -/
theorem parseHeaderLine_headerLine (k v : Bytes) (hk : COLON ∉ k) :
    parseHeaderLine (headerLine (k, v)) = some (k, v) := by
  have hform : headerLine (k, v) = k ++ COLON :: (SP :: v) := by
    simp [headerLine, COLON, SP]
  simp only [parseHeaderLine, hform, takeUntil_append COLON k (SP :: v) hk, Option.bind_some]
  have hsp : stripPrefix [SP] (SP :: v) = some v := stripPrefix_append [SP] v
  simp [hsp]

/-! ## The header block: `blockOf` and its parse -/

/-- The header block as `⋃ (headerLine h ++ crlf)` — equal to
`renderHeaders hs ++ crlf` for nonempty `hs` (`renderHeaders_blockOf`). -/
def blockOf (hs : List (Bytes × Bytes)) : Bytes :=
  hs.flatMap (fun h => headerLine h ++ crlf)

theorem renderHeaders_blockOf : ∀ (hs : List (Bytes × Bytes)), hs ≠ [] →
    renderHeaders hs ++ crlf = blockOf hs
  | [_], _ => by simp [renderHeaders, blockOf]
  | h :: g :: t, _ => by
    have ih := renderHeaders_blockOf (g :: t) (by simp)
    simp only [renderHeaders, blockOf, List.flatMap_cons] at ih ⊢
    rw [← ih]; simp [List.append_assoc]

/-- `stripPrefix crlf` fails on a header line: it never starts with `CR`. -/
theorem stripPrefix_crlf_headerLine (k v tail : Bytes) (hcr : CR ∉ headerLine (k, v)) :
    stripPrefix crlf (headerLine (k, v) ++ tail) = none := by
  have hne : headerLine (k, v) ≠ [] := by simp [headerLine]
  cases hHL : headerLine (k, v) with
  | nil => exact absurd hHL hne
  | cons hb htl =>
    have hbne : (CR == hb) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro hEq; apply hcr; rw [hHL]; simp [← hEq]
    show stripPrefix crlf (hb :: (htl ++ tail)) = none
    simp only [crlf]
    exact stripPrefix_cons_ne CR [LF] (htl ++ tail) hb hbne

/-- Parsing the block `blockOf hs ++ crlf ++ body` recovers `(hs, body)` under
the header-field discipline. -/
theorem parseHeadersFuel_blockOf :
    ∀ (hs : List (Bytes × Bytes)) (body : Bytes) (fuel : Nat),
      (∀ kv ∈ hs, COLON ∉ kv.1 ∧ CR ∉ kv.1 ∧ CR ∉ kv.2) →
      (blockOf hs ++ crlf ++ body).length ≤ fuel →
      parseHeadersFuel fuel (blockOf hs ++ crlf ++ body) = some (hs, body)
  | [], body, fuel, _, hlen => by
    have hfuel : 0 < fuel := by
      simp only [blockOf, List.flatMap_nil, List.nil_append, crlf,
        List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    simp only [blockOf, List.flatMap_nil, List.nil_append, parseHeadersFuel]
    rw [stripPrefix_append crlf body]
  | (k, v) :: t, body, fuel, hwf, hlen => by
    obtain ⟨hcol, hcrk, hcrv⟩ := hwf (k, v) (by simp)
    have hcrline : CR ∉ headerLine (k, v) := by
      simp only [headerLine]
      intro hmem
      rcases List.mem_append.mp hmem with h1 | h1
      · rcases List.mem_append.mp h1 with h2 | h2
        · exact hcrk h2
        · simp [CR] at h2
      · exact hcrv h1
    have hshape : blockOf ((k, v) :: t) ++ crlf ++ body
        = headerLine (k, v) ++ crlf ++ (blockOf t ++ crlf ++ body) := by
      simp only [blockOf, List.flatMap_cons]; simp [List.append_assoc]
    have hfuel : 0 < fuel := by
      rw [hshape] at hlen
      simp only [List.length_append, crlf, List.length_cons, List.length_nil] at hlen
      omega
    obtain ⟨f, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fuel ≠ 0)
    rw [hshape]
    have hsp : stripPrefix crlf (headerLine (k, v) ++ crlf ++ (blockOf t ++ crlf ++ body)) = none := by
      rw [List.append_assoc]
      exact stripPrefix_crlf_headerLine k v (crlf ++ (blockOf t ++ crlf ++ body)) hcrline
    have hlen' : (blockOf t ++ crlf ++ body).length ≤ f := by
      rw [hshape] at hlen
      simp only [List.length_append, crlf, List.length_cons, List.length_nil] at hlen ⊢
      omega
    simp only [parseHeadersFuel, hsp,
      takeUntilCrlf_append (headerLine (k, v)) (blockOf t ++ crlf ++ body) hcrline,
      parseHeaderLine_headerLine k v hcol,
      parseHeadersFuel_blockOf t body f (fun kv hkv => hwf kv (by simp [hkv])) hlen']

/-! ## The status line -/

theorem SP_notMem_natToDec (n : Nat) : SP ∉ natToDec n := by
  intro hmem
  have := Dec.natToDec_isDigit n SP hmem
  simp [SP] at this

theorem CR_notMem_natToDec (n : Nat) : CR ∉ natToDec n := by
  intro hmem
  have := Dec.natToDec_isDigit n CR hmem
  simp [CR] at this

theorem CR_notMem_clName : CR ∉ clName := by decide
theorem COLON_notMem_clName : COLON ∉ clName := by decide

/-! ## The round-trip -/

/-- **Client↔server round-trip.** A response the server serializes parses back
to the same response (with the derived `Content-Length` header made explicit).
Non-vacuous (see `parse_serialize_ok200`). -/
theorem parse_serialize (resp : Response) (h : WF resp) :
    parse (serialize resp) = some (wireForm resp) := by
  obtain ⟨hreason, hhdrs⟩ := h
  have hAHne : allHeaders (build resp) ≠ [] := by simp [allHeaders]
  have hAHwf : ∀ kv ∈ allHeaders (build resp), COLON ∉ kv.1 ∧ CR ∉ kv.1 ∧ CR ∉ kv.2 := by
    intro kv hkv
    rw [allHeaders] at hkv
    rcases List.mem_append.mp hkv with h1 | h1
    · exact hhdrs kv h1
    · simp only [List.mem_singleton] at h1
      subst h1
      exact ⟨COLON_notMem_clName, CR_notMem_clName, CR_notMem_natToDec _⟩
  have hblock : renderHeaders (allHeaders (build resp)) ++ crlf ++ crlf ++ resp.body
      = blockOf (allHeaders (build resp)) ++ crlf ++ resp.body := by
    rw [renderHeaders_blockOf (allHeaders (build resp)) hAHne]
  have hser : serialize resp
      = (http11 ++ [SP]) ++ (natToDec resp.status ++ SP ::
          (resp.reason ++ crlf ++
            (renderHeaders (allHeaders (build resp)) ++ crlf ++ crlf ++ resp.body))) := by
    simp only [serialize, serializeWire, statusLine, build, SP, List.append_assoc,
      List.cons_append, List.singleton_append, List.nil_append]
  rw [parse]
  simp only [hser, stripPrefix_append,
    takeUntil_append SP (natToDec resp.status) _ (SP_notMem_natToDec _),
    takeUntilCrlf_append resp.reason _ hreason, Option.bind, Option.pure_def, bind, pure]
  rw [hblock]
  simp only [parseHeaders,
    parseHeadersFuel_blockOf (allHeaders (build resp)) resp.body _ hAHwf (Nat.le_refl _)]
  rw [show Dec.dval 0 (natToDec resp.status) = resp.status from Dec.dval_natToDec resp.status]
  simp only [wireForm, allHeaders, build]

/-- Non-vacuity: `WF` holds for a concrete `200 OK`, so the round-trip is not
vacuously about the empty set of responses. -/
theorem ok200_WF (body : Bytes) : WF (Reactor.ok200 body) := by
  refine ⟨?_, ?_⟩
  · simp [Reactor.ok200, Reactor.reasonOK, CR]
  · intro kv hkv; simp [Reactor.ok200] at hkv

/-- The round-trip, discharged concretely on `200 OK`. -/
theorem parse_serialize_ok200 (body : Bytes) :
    parse (serialize (Reactor.ok200 body)) = some (wireForm (Reactor.ok200 body)) :=
  parse_serialize _ (ok200_WF body)

end ResponseParse
end Proto
