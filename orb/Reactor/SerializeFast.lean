import Reactor.Serialize

/-!
# The `Wire`-typed flat head accumulator (`serializeHeadAcc`)

The compiled response serializer itself — the byte-direct push render
`serializeFast` and the `@[csimp] serialize_eq_fast` that installs it — lives
in `Reactor/Serialize.lean`, the spec's own module. It used to live here, and
that placement was a silent footgun: a `@[csimp]` is applied only to call
sites compiled with the theorem in scope, so every module that called
`serialize` without importing this leaf (the deployed pipeline modules did
exactly that) was code-generated against the allocating spec body. Housing
the csimp beside `serialize` makes that reversion impossible by construction —
no call site can exist without it visible.

What remains here is the `Wire`-typed flat head accumulator:
`serializeHeadAcc` builds the response head (status line, CRLF, header block
with the derived `Content-Length`, blank-line separator) into a flat
`Array UInt8`, and `serializeHeadAcc_toList` proves it reads back as exactly
the head of `serializeWire`. `Reactor.ServeArr` renders its flat `ByteArray`
response through it and bridges with this lemma.
-/

namespace Reactor

open Proto (Bytes)

/-- Header block rendered into a flat accumulator: mirrors `renderHeaders`
(no trailing `CRLF`), appending each `headerLine`/`crlf` fragment onto the
uniquely-owned `Array UInt8` (`++` here is `Array.appendList`, an amortized-`O(1)`
per-byte push) instead of allocating a fresh cons-spine per join. -/
def renderHeadersAcc (acc : Array UInt8) : List (Bytes × Bytes) → Array UInt8
  | []     => acc
  | [h]    => acc ++ headerLine h
  | h :: t => renderHeadersAcc ((acc ++ headerLine h) ++ crlf) t

/-- The response **head** serialized into a flat `Array UInt8` accumulator:
status line, CRLF, header block, then the blank-line separator (`CRLF CRLF`) —
everything up to but not including the body, built without per-join cons-list
copies. `Reactor.ServeArr` renders its flat `ByteArray` response through this. -/
def serializeHeadAcc (w : Wire) : Array UInt8 :=
  let acc : Array UInt8 := ((#[] : Array UInt8) ++ statusLine w) ++ crlf
  let acc := renderHeadersAcc acc (allHeaders w)
  (acc ++ crlf) ++ crlf

/-- Reading the accumulator back as a list, `renderHeadersAcc acc hs` prepends
exactly `renderHeaders hs` onto `acc` — the flat pass renders the same bytes. -/
theorem renderHeadersAcc_toList (hs : List (Bytes × Bytes)) :
    ∀ acc : Array UInt8, (renderHeadersAcc acc hs).toList = acc.toList ++ renderHeaders hs := by
  induction hs with
  | nil => intro acc; simp [renderHeadersAcc, renderHeaders]
  | cons h t ih =>
    intro acc
    cases t with
    | nil => simp [renderHeadersAcc, renderHeaders]
    | cons h2 t2 =>
      rw [show renderHeadersAcc acc (h :: h2 :: t2)
            = renderHeadersAcc ((acc ++ headerLine h) ++ crlf) (h2 :: t2) from rfl,
          ih ((acc ++ headerLine h) ++ crlf)]
      simp only [renderHeaders, Array.toList_appendList, List.append_assoc]

/-- The flat head accumulator reads back exactly the head of `serializeWire`
(`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF`), so appending the body
reconstructs the full wire byte sequence. -/
theorem serializeHeadAcc_toList (w : Wire) :
    (serializeHeadAcc w).toList
      = statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf := by
  unfold serializeHeadAcc
  simp only [Array.toList_appendList, renderHeadersAcc_toList, Array.toList_empty,
    List.nil_append, List.append_assoc]

#print axioms serializeHeadAcc_toList

end Reactor
