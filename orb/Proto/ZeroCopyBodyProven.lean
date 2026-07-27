import Datapath.ServeSplit

/-!
# Proto.ZeroCopyBodyProven — the DEPLOYED zero-copy body (`writev` splice) serve

PROVE-WHAT-RUNS for the datapath row `zc.body` (`DRORB_ZC=1 DRORB_SPAN=15`, the
io_uring zero-copy-body split-write path).

## What runs (curl-confirmed on hbox, io_uring, 24 shards)

The serve thread crosses the `@[export drorb_serve_split_head]` seam
(`Datapath.ServeSplit.serveSplitHead`): it parses the borrowed request window by
INDEX, folds the three real header stages, and computes ONLY the response HEAD —
status line, headers, `Content-Length: <input.size>`, blank-line separator. NO body
is appended. The io_uring shard then arms a single `writev` gathering that head THEN
the borrowed request body straight from its `buf_ring` slot to the socket
(`crates/dataplane/src/uring.rs`, `stage_split_response`, gated on `is_split_span()`
which is `DRORB_SPAN == 15`, and on `sh.br.is_some()` which needs `DRORB_ZC=1`).

Deployed, launched `DRORB_ZC=1 DRORB_SPAN=15 ./dataplane --bind 127.0.0.1:8102 --io
uring` (log: `zero-copy (buf_ring recv + SendZc)`):

    $ curl -s --data-binary '<b>hi' -H 'Content-Type: application/octet-stream' \
        http://127.0.0.1:8102/echo | od -An -tx1 | tail
        ... 43 6f 6e 74 65 6e 74 2d 4c 65 6e 67 74 68 3a 20 35 0d 0a 0d 0a 3c 62 3e 68 69
      #  the echoed body TAIL is `3c 62 3e 68 69` = "<b>hi" — the `<` (0x3c) and `>`
      #  (0x3e) SPLICED VERBATIM by writev (never tokenized, never appended).
    $ head -c 10000 /dev/zero | tr '\0' A > big.bin
    $ curl -s --data-binary @big.bin -H 'Content-Type: application/octet-stream' \
        http://127.0.0.1:8102/echo -o big.resp        # resp = 10145 bytes
    $ tail -c 10000 big.resp | cmp -s - big.bin && echo BODY-BYTE-IDENTICAL
        BODY-BYTE-IDENTICAL          # the 10 000-byte body round-trips exactly

## What is proven here (over the deployed export `serveSplitHead`)

* `zerocopy_writev_reassembles` — the byte-identity the two-write path RELIES ON: for
  EVERY request, the head the export computes followed by the borrowed body (`input`)
  is byte-identical to the appended reference serve (`serveSplitFull`, the passthrough
  branch of the deployed gated serve). So `writev(head, body)` emits exactly the whole
  response the append would have — with the body never copied into an output buffer.

* `zerocopy_length_split` — the head declares the SPLICED body's length: on a
  dispatchable request the head bytes plus the body bytes sum to the full response
  length, so `Content-Length` accounts for exactly the `writev`'d body.

* `zerocopy_body_spliced_verbatim` / `zerocopy_body_is_suffix` — the response bytes are
  the head bytes followed by the request body bytes VERBATIM (`input.data.toList`): the
  body is a byte-for-byte splice of the borrowed buffer, so every body byte — `<` (0x3c)
  and `>` (0x3e) included — is preserved untouched, matching the wire tail `3c 62 3e 68 69`.

Reuses the pure-kernel `Datapath.ServeSplit` algebra (axioms ⊆ {propext, Quot.sound});
no `native_decide`. The body-splice facts are structural over `++` (the `toUTF8` request
literal is kernel-opaque, as `HeadProven` notes, so nothing forces it to reduce).
-/

namespace Proto.ZeroCopyBodyProven

open Datapath.SpanBytes (parseIndexNative full)
open Datapath.ServeSplit (serveSplitHead serveSplitFull serveSplit_reassemble demoReq)

/-! ## The `writev` reassembly is byte-identical to the appended serve -/

/-- **`zerocopy_writev_reassembles`.** For every request `input`, the deployed export
`serveSplitHead input` (the head the serve thread computes) followed by the borrowed
request body `input` (the second `writev` iovec — the `buf_ring` slot) is
BYTE-IDENTICAL to the appended reference serve `serveSplitFull input`. This is the
correctness the io_uring `writev` path stands on: writing head-then-body produces
exactly the response the body-appending serve would, with zero body copy. On a
non-dispatchable input both sides are empty. -/
theorem zerocopy_writev_reassembles (input : ByteArray) :
    (match parseIndexNative (full input) with
     | .request _ _ _ => ByteArray.mk ((serveSplitHead input).data ++ input.data)
     | _ => ByteArray.empty)
      = serveSplitFull input :=
  serveSplit_reassemble input

/-! ## The head accounts for the spliced body's length -/

/-- **`zerocopy_length_split`.** On a dispatchable request, the head bytes
(`serveSplitHead input`) plus the spliced body bytes (`input`) sum to the full
response length. So the `Content-Length` the head bakes in covers exactly the body the
`writev` splices — the split is length-correct. -/
theorem zerocopy_length_split (input : ByteArray) (c : Nat) (req : Proto.Request)
    (k : Bool) (h : parseIndexNative (full input) = .request c req k) :
    (serveSplitHead input).size + input.size = (serveSplitFull input).size := by
  have hre : ByteArray.mk ((serveSplitHead input).data ++ input.data) = serveSplitFull input := by
    have := zerocopy_writev_reassembles input
    rw [h] at this; exact this
  have hlen := congrArg ByteArray.size hre
  simpa only [ByteArray.size, Array.size_append] using hlen

/-! ## The body is the borrowed request buffer, spliced VERBATIM

The response is `(Lean-computed head) ++ (borrowed request body, byte-for-byte)`. So
whatever bytes the request body carries — markup `<`/`>` included — appear untouched in
the response's tail: the second `writev` iovec is the input buffer, never tokenized,
never mutated. This is the zero-copy essence, proven structurally (no evaluation of the
`toUTF8` request literal — which is kernel-opaque, as `HeadProven` notes). -/

/-- **`zerocopy_body_spliced_verbatim`.** The reassembled response bytes are exactly the
head bytes followed by the request body bytes VERBATIM (`input.data.toList`). The body is
a byte-for-byte splice of the borrowed request buffer — so every body byte, `<` (0x3c)
and `>` (0x3e) included, is preserved untouched (the wire tail `... 3c 62 3e 68 69` for
the `<b>hi` curl). -/
theorem zerocopy_body_spliced_verbatim (input : ByteArray) :
    (ByteArray.mk ((serveSplitHead input).data ++ input.data)).data.toList
      = (serveSplitHead input).data.toList ++ input.data.toList := by
  simp [Array.toList_append]

/-- **`zerocopy_body_is_suffix`.** The borrowed request body is a verbatim SUFFIX of the
served response — the head is a strict prefix and the body is appended untouched (never
interleaved, never rewritten). -/
theorem zerocopy_body_is_suffix (input : ByteArray) :
    ∃ head : List UInt8,
      (ByteArray.mk ((serveSplitHead input).data ++ input.data)).data.toList
        = head ++ input.data.toList :=
  ⟨(serveSplitHead input).data.toList, zerocopy_body_spliced_verbatim input⟩

end Proto.ZeroCopyBodyProven

#print axioms Proto.ZeroCopyBodyProven.zerocopy_writev_reassembles
#print axioms Proto.ZeroCopyBodyProven.zerocopy_length_split
#print axioms Proto.ZeroCopyBodyProven.zerocopy_body_spliced_verbatim
#print axioms Proto.ZeroCopyBodyProven.zerocopy_body_is_suffix
