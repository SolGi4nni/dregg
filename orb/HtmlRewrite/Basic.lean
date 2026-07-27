/-!
# Streaming HTML tokenizer

A minimal, honest tokenizer that splits a byte stream into `text` and `tag`
tokens (`tag` = a `<…>` span; everything else is `text`). It is modelled as a
byte-fold with a carried state, which is exactly what makes it *streaming*: the
per-byte transition is the same whether the input arrives whole or split into
chunks.

The theorems:

* **chunk-boundary safety** (`feedBytes_append`, `stream_eq_whole`) — feeding the
  input split at *any* boundary yields the same tokenizer state as feeding it
  whole. This is the property a naive chunk-at-a-time rewriter gets wrong; here
  it is `List.foldl_append`.
* **byte conservation** (`feed_conserves`, `bytesOf_tokenize`) — every input byte
  ends up in exactly one token (or the in-progress buffer); nothing is dropped
  or duplicated, so re-serializing recovers the input (`roundtrip`).
-/

namespace HtmlRewrite

abbrev Byte := UInt8

/-- `<` and `>` as bytes. -/
def lt : Byte := 60
def gt : Byte := 62

/-- A token: a run of text, or a `<…>` tag span. Both retain their exact bytes
(a tag includes its `<` and `>`), so tokenization is lossless. -/
inductive Token where
  | text (bytes : List Byte)
  | tag (bytes : List Byte)
deriving Repr, DecidableEq

/-- The bytes a token carries. -/
def Token.bytes : Token → List Byte
  | .text b => b
  | .tag b => b

/-- Tokenizer mode: scanning text, or inside a tag. -/
inductive Mode where
  | text
  | tag
deriving Repr, DecidableEq

/-- Tokenizer state: the mode, the bytes of the token under construction, and the
completed tokens so far (most recent first). -/
structure TState where
  mode : Mode
  cur : List Byte
  toks : List Token
deriving Repr

/-- The initial state. -/
def init : TState := { mode := .text, cur := [], toks := [] }

/-- Flush the current buffer as a token of the given kind, if non-empty. -/
def flush (mkTok : List Byte → Token) (cur : List Byte) (toks : List Token) : List Token :=
  if cur = [] then toks else mkTok cur :: toks

/-- Feed one byte. In text mode, `<` closes any text run and opens a tag; other
bytes extend the text. In tag mode, `>` closes the tag; other bytes extend it. -/
def feed (s : TState) (b : Byte) : TState :=
  match s.mode with
  | .text =>
    if b = lt then
      { mode := .tag, cur := [lt], toks := flush Token.text s.cur s.toks }
    else
      { s with cur := s.cur ++ [b] }
  | .tag =>
    if b = gt then
      { mode := .text, cur := [], toks := Token.tag (s.cur ++ [gt]) :: s.toks }
    else
      { s with cur := s.cur ++ [b] }

/-- Fold the tokenizer over a byte list from a given state. -/
def feedBytes (s : TState) (bs : List Byte) : TState := bs.foldl feed s

/-- Tokenize a whole input from the initial state. -/
def tokenize (bs : List Byte) : TState := feedBytes init bs

/-! ## Linear-time tokenizer (`tokenizeFast`) — proven byte-for-byte equal to `tokenize`

`feed` extends the in-progress buffer with `s.cur ++ [b]` — an O(|cur|) end-append
per byte, so folding it over an N-byte body is **O(N²)** (the response-body build
wall the perf audit measured). The fix keeps the in-progress buffer *reversed*
(newest byte first), so extending it is an O(1) cons instead of an O(|cur|) append;
the reversed buffer is flipped back only when a token is closed (total O(N) across
all runs) and once at the end. Everything else — the mode, the completed-token
list, the exact token bytes — is identical.

`tokenizeFast` produces the SAME `TState` as `tokenize` (`tokenizeFast_eq`), so the
whole existing theorem stack (byte conservation, chunk-boundary safety, the
correctness refinement) transfers unchanged: this is a faithful implementation
refinement, not a new spec. The deployed HTML-rewrite stage (`rewriteBytes`) runs
`tokenizeFast`; the abstract `feed`/`tokenize` remain the specification. -/

/-- Fast tokenizer state: identical to `TState`, but the in-progress buffer
`curRev` is held REVERSED (newest byte first) so extending it is an O(1) `cons`
rather than the O(|cur|) end-append `cur ++ [b]`. -/
structure FState where
  mode : Mode
  curRev : List Byte
  toks : List Token

/-- Recover the abstract `TState` from a fast state: flip the reversed buffer. -/
def FState.decode (s : FState) : TState :=
  { mode := s.mode, cur := s.curRev.reverse, toks := s.toks }

/-- One fast step. Extending the current run is `b :: s.curRev` (O(1)); a run is
flipped to forward order only when the run closes (`<` opens a tag, `>` closes
one). Mirrors `feed` exactly under `FState.decode`. -/
def feedF (s : FState) (b : Byte) : FState :=
  match s.mode with
  | .text =>
    if b = lt then
      { mode := .tag, curRev := [lt], toks := flush Token.text s.curRev.reverse s.toks }
    else
      { s with curRev := b :: s.curRev }
  | .tag =>
    if b = gt then
      { mode := .text, curRev := [], toks := Token.tag (gt :: s.curRev).reverse :: s.toks }
    else
      { s with curRev := b :: s.curRev }

/-- The initial fast state (`decode`s to `init`). -/
def initF : FState := { mode := .text, curRev := [], toks := [] }

/-- **Linear tokenizer.** Fold the O(1)-per-byte `feedF`, then `decode` once. Total
work is O(N): one cons per byte, plus O(run length) per closed run and one final
flip — no per-byte O(|cur|) append. -/
def tokenizeFast (bs : List Byte) : TState := (bs.foldl feedF initF).decode

/-- One fast step `decode`s to one abstract step — the per-byte simulation. -/
theorem feedF_decode (s : FState) (b : Byte) : (feedF s b).decode = feed s.decode b := by
  unfold feedF feed FState.decode
  cases hm : s.mode with
  | text =>
    by_cases hb : b = lt
    · simp [hm, hb]
    · simp [hm, hb, List.reverse_cons]
  | tag =>
    by_cases hb : b = gt
    · simp [hm, hb, List.reverse_cons]
    · simp [hm, hb, List.reverse_cons]

/-- Folding `feedF` then `decode`ing equals `decode`ing then folding `feed`. -/
theorem foldl_feedF_decode (bs : List Byte) (s : FState) :
    (bs.foldl feedF s).decode = bs.foldl feed s.decode := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons]
    rw [ih, feedF_decode]

/-- **`tokenizeFast` is byte-for-byte `tokenize`.** The fast, linear tokenizer
produces exactly the same `TState` (same mode, same in-progress buffer, same
completed tokens) as the abstract quadratic `tokenize`, so every theorem proved
about `tokenize` holds of `tokenizeFast`. This carries byte-equality across the
representation change: the deployed rewrite is unchanged in WHAT it computes, only
in that it is O(N) not O(N²). -/
@[simp] theorem tokenizeFast_eq (bs : List Byte) : tokenizeFast bs = tokenize bs := by
  unfold tokenizeFast tokenize feedBytes
  rw [foldl_feedF_decode]
  rfl

/-- **Chunk-boundary safety (fold form).** Feeding `a` then `b` from a state is
the same as feeding `a ++ b` — the boundary is invisible. -/
theorem feedBytes_append (s : TState) (a b : List Byte) :
    feedBytes s (a ++ b) = feedBytes (feedBytes s a) b := by
  unfold feedBytes
  rw [List.foldl_append]

/-- **Chunk-boundary safety (streaming = whole).** Splitting the input at any
single boundary and streaming the two chunks yields the same final state as
tokenizing the whole input at once. -/
theorem stream_eq_whole (a b : List Byte) :
    feedBytes (tokenize a) b = tokenize (a ++ b) := by
  unfold tokenize
  rw [feedBytes_append]

/-- The bytes captured by a state: completed tokens (in chronological order)
followed by the in-progress buffer. -/
def bytesOf (s : TState) : List Byte :=
  (s.toks.reverse.flatMap Token.bytes) ++ s.cur

/-- **Byte conservation (per step).** Feeding one byte appends exactly that byte
to the captured bytes — nothing is dropped or duplicated. -/
theorem feed_conserves (s : TState) (b : Byte) :
    bytesOf (feed s b) = bytesOf s ++ [b] := by
  unfold feed bytesOf flush
  cases s.mode with
  | text =>
    by_cases hb : b = lt
    · subst hb
      by_cases hc : s.cur = []
      · simp [hc, Token.bytes]
      · simp [hc, Token.bytes, List.append_assoc]
    · simp [hb, List.append_assoc]
  | tag =>
    by_cases hb : b = gt
    · subst hb
      simp [Token.bytes, List.append_assoc]
    · simp [hb, List.append_assoc]

/-- **Byte conservation (whole).** Tokenizing an input captures exactly its
bytes — a lossless split. -/
theorem bytesOf_feedBytes (s : TState) (bs : List Byte) :
    bytesOf (feedBytes s bs) = bytesOf s ++ bs := by
  induction bs generalizing s with
  | nil => simp [feedBytes, bytesOf]
  | cons b bs ih =>
    unfold feedBytes at *
    simp only [List.foldl_cons]
    rw [ih, feed_conserves]
    simp

/-- **Round-trip / losslessness.** Re-serializing the captured bytes of a
tokenized input recovers the input exactly (identity rewrite is the identity). -/
theorem roundtrip (bs : List Byte) : bytesOf (tokenize bs) = bs := by
  unfold tokenize
  rw [bytesOf_feedBytes]
  simp [bytesOf, init]

/-! **Totality is not a theorem in Lean.** `feed : TState → Byte → TState` is a plain `def`, so
totality is a TYPE-LEVEL fact — the elaborator admits no partial `def` of that
signature, and there is nothing left to prove. The theorem that stood here,
`feed_total : feed s b = feed s b`, was exactly that non-statement:
it holds of EVERY function of the same arity, so it constrained `feed` not at
all while wearing a name that claimed it did. The real facts about the tokenizer are `roundtrip` above and `text_stays_text` below. -/

/-- **Text safety.** In text mode a byte other than `<` is never treated as
markup — it just extends the current text run, and the mode stays `text`. -/
theorem text_stays_text (s : TState) (b : Byte) (hmode : s.mode = .text) (hb : b ≠ lt) :
    (feed s b).mode = .text := by
  simp [feed, hmode, hb]

def version : String := "0.1.0"

end HtmlRewrite
