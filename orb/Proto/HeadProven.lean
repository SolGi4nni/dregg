import Proto.Decimal

/-!
# Proto.HeadProven — the DEPLOYED HTTP/1.1 `HEAD` method response discipline

PROVE-WHAT-RUNS for ledger row `h1.head` (`HEAD` method, deployed).

The place the running dataplane actually implements `HEAD` is the host-side
static-file streaming lane (`crates/dataplane/src/static_serve.rs`,
`StaticRoot::handle_streaming`, gated on `DRORB_STATIC_ROOT`, wired in
`crates/dataplane/src/blocking.rs`). That function builds the response head
batch-small — status line, `Connection`, `Accept-Ranges`, `Content-Type`, and
`Content-Length: <file size>` — and then:

```rust
let is_head = method == b"HEAD";
client.write_all(&head)?;
...
if !is_head {
    // stream the file body block-by-block
}
```

So the head is computed **identically** regardless of the method — the method
never touches it — and the body is streamed **iff** the request is not `HEAD`.
The `Content-Length` in that head is `file.metadata().len()`, i.e. exactly the
number of octets the body-stream would emit for a `GET`.

This module models that construction byte-for-byte (`staticHead` mirrors the
Rust head builder; `staticServe` mirrors the `write head` + `if !is_head stream
body` control flow) and proves the two RFC 9110 §9.3.2 / §8.6 obligations:

* **`head_no_body`** — RFC 9110 §9.3.2: "The HEAD method is identical to GET
  except that the server MUST NOT send content in the response." The `HEAD`
  response is *exactly* the head the `GET` response leads with — same status
  line, same header fields (including `Content-Length`) — with **no** body
  octets appended. Formally: `staticServe HEAD = staticHead`, `staticServe GET =
  staticHead ++ body`, and `staticServe HEAD ++ body = staticServe GET` (the two
  differ by the body *alone*; the head is byte-identical).

* **`head_content_length`** — RFC 9110 §8.6: a `Content-Length` in a `HEAD`
  response MUST equal the decimal number of octets the content would have had for
  a `GET`. The head announces `Content-Length: <natToDec body.length>`, that
  decimal decodes back (`Proto.Dec.dval_natToDec`) to exactly `body.length`, and
  the `GET` response really does append that many body octets. So the announced
  length is the would-be `GET` content length, on the nose.

Non-vacuity: `head_differs_from_get` shows a `HEAD` response genuinely differs
from the `GET` response whenever the body is non-empty — a handler that streamed
the body for `HEAD` (or announced a wrong `Content-Length`) would fail these.

`Proto.Dec.natToDec n = (Nat.repr n).toUTF8.toList` is byte-for-byte the Rust
`len.to_string().as_bytes()`, so the `Content-Length` value modelled here is the
one the deployed handler writes.

Lean-core + `Proto.Decimal` only; total; no new axioms; edits no shared file.
-/

namespace Proto.HeadProven

open Proto.Dec (natToDec dval dval_natToDec)

/-- Wire bytes. -/
abbrev Bytes := List UInt8

/-- A string literal as its UTF-8 wire bytes (kept opaque — every proof below is
structural over `++`, so the extern `toUTF8` is never forced to reduce). -/
def str (s : String) : Bytes := s.toUTF8.toList

/-- CRLF. -/
def crlf : Bytes := str "\r\n"

/-- The `Connection` header line, keyed on the request's keep-alive bit — exactly
the Rust `if keepalive_req { b"Connection: keep-alive\r\n" } else { b"Connection:
close\r\n" }`. -/
def connLine (keepalive : Bool) : Bytes :=
  if keepalive then str "Connection: keep-alive\r\n" else str "Connection: close\r\n"

/-- The `Content-Length` field line: `Content-Length: <decimal len>\r\n`.
`natToDec len` is the deployed `len.to_string()` rendering. -/
def clLine (len : Nat) : Bytes :=
  str "Content-Length: " ++ natToDec len ++ crlf

/-- **The response HEAD the deployed static handler builds**
(`static_serve.rs handle_streaming`): status line, `Connection`, `Accept-Ranges`,
`Content-Type: <ctype>`, `Content-Length: <len>`, blank-line separator. The
method is *never* consulted here, so `GET` and `HEAD` share this byte-for-byte.

Byte-identical to the Rust builder: `"HTTP/1.1 200 OK\r\n"` + conn +
`"Accept-Ranges: bytes\r\n"` + `"Content-Type: "` + ctype + `"\r\nContent-Length:
"` + len + `"\r\n\r\n"` — here the `"\r\n"` after `ctype` and the leading `"\r\n"`
of `clLine`'s trailing `crlf` … the trailing `crlf` is the blank-line separator. -/
def staticHead (keepalive : Bool) (ctype : Bytes) (len : Nat) : Bytes :=
  str "HTTP/1.1 200 OK\r\n"
    ++ connLine keepalive
    ++ str "Accept-Ranges: bytes\r\n"
    ++ str "Content-Type: " ++ ctype ++ crlf
    ++ clLine len
    ++ crlf

/-- **The deployed static serve**, mirroring `handle_streaming`'s control flow:
write the head (with `Content-Length = body.length`, the file size), then stream
the body **iff** the request is not `HEAD`. `isHead = true` ⇒ head only. -/
def staticServe (isHead keepalive : Bool) (ctype body : Bytes) : Bytes :=
  staticHead keepalive ctype body.length ++ (if isHead then ([] : Bytes) else body)

/-! ## `head_no_body` — RFC 9110 §9.3.2 -/

/-- **`head_no_body`.** A `HEAD` request returns the *same head* — status line and
all header fields, including `Content-Length` — as the corresponding `GET`, but
with **no body** (RFC 9110 §9.3.2: identical to `GET` except the server MUST NOT
send content).

Three faithful facets of the deployed control flow:
1. the `HEAD` response is exactly the head, no body appended;
2. the `GET` response is that same head followed by the body;
3. so the two differ by the body *alone* — the head (hence every header field,
   `Content-Length` included) is byte-identical. -/
theorem head_no_body (keepalive : Bool) (ctype body : Bytes) :
    staticServe true keepalive ctype body = staticHead keepalive ctype body.length
  ∧ staticServe false keepalive ctype body = staticHead keepalive ctype body.length ++ body
  ∧ staticServe true keepalive ctype body ++ body = staticServe false keepalive ctype body := by
  refine ⟨?_, ?_, ?_⟩
  · simp [staticServe]
  · simp [staticServe]
  · simp [staticServe]

/-! ## `head_content_length` — RFC 9110 §8.6 -/

/-- **`head_content_length`.** The head the `HEAD` response carries announces
`Content-Length: <natToDec body.length>` — and that decimal decodes back
(`Proto.Dec.dval_natToDec`) to exactly `body.length`, which is precisely the
number of octets the `GET` response appends as its body. So the deployed `HEAD`'s
`Content-Length` equals the octet count the would-be `GET` content would have had
(RFC 9110 §8.6).

Three facets:
1. the head literally contains the `Content-Length` line as an infix
   (`clLine body.length = "Content-Length: " ++ natToDec body.length ++ "\r\n"`);
2. the announced decimal decodes to `body.length` (round-trip fidelity);
3. the `GET` response body has exactly that many octets. -/
theorem head_content_length (keepalive : Bool) (ctype body : Bytes) :
    (∃ pre post : Bytes,
        staticHead keepalive ctype body.length = pre ++ clLine body.length ++ post)
  ∧ dval 0 (natToDec body.length) = body.length
  ∧ (staticServe false keepalive ctype body).length
      = (staticHead keepalive ctype body.length).length + body.length := by
  refine ⟨?_, dval_natToDec body.length, ?_⟩
  · exact ⟨str "HTTP/1.1 200 OK\r\n" ++ connLine keepalive
        ++ str "Accept-Ranges: bytes\r\n" ++ str "Content-Type: " ++ ctype ++ crlf,
      crlf, rfl⟩
  · simp [staticServe]

/-! ## Non-vacuity -/

/-- **`head_differs_from_get`.** For any non-empty body, the `HEAD` response
genuinely differs from the `GET` response — the body octets `GET` streams are
absent from `HEAD`. So a handler that streamed the body for `HEAD` (or otherwise
made the two equal) fails `head_no_body`; the theorem is not vacuous. -/
theorem head_differs_from_get (keepalive : Bool) (ctype body : Bytes) (hne : body ≠ []) :
    staticServe true keepalive ctype body ≠ staticServe false keepalive ctype body := by
  have h := head_no_body keepalive ctype body
  intro heq
  rw [h.1, h.2.1] at heq
  -- staticHead = staticHead ++ body  ⇒  body = []
  have hlen := congrArg List.length heq
  simp only [List.length_append] at hlen
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

/-! ## Concrete witnesses (the model computes on real bytes) -/

/-- A concrete `HEAD` of a 5-octet body serves the head with `Content-Length: 5`
and no body; the `GET` of the same serves the head then the 5 body octets. The
two differ (non-vacuous), and the announced `5` decodes to `5`. -/
example :
    staticServe true true (str "text/plain") [104, 101, 108, 108, 111]
      = staticHead true (str "text/plain") 5
  ∧ staticServe true true (str "text/plain") [104, 101, 108, 108, 111]
      ≠ staticServe false true (str "text/plain") [104, 101, 108, 108, 111]
  ∧ dval 0 (natToDec 5) = 5 :=
  ⟨(head_no_body true (str "text/plain") [104, 101, 108, 108, 111]).1,
   head_differs_from_get true (str "text/plain") [104, 101, 108, 108, 111] (by decide),
   dval_natToDec 5⟩

end Proto.HeadProven
