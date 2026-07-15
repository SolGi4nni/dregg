/-
# Proto.DateHeaderProven — the DEPLOYED `Date` header value on the wire

PROVE-WHAT-RUNS for the RFC 7231 §7.1.1.2 `Date` header the running dataplane stamps on
EVERY response. The deployed default serve (no `DRORB_SPAN`) crosses
`drorb_serve_metered_conformant` = `Reactor.ServeConformant.conformantServe` wrapped around
the plain deployed fold; that wrapper's `injectDate` splices `Date: <deployNow>` as the
first header line of every response (`Reactor.ServeConformant.injectDate_date_present`
proves it is PRESENT). This file pins the exact wire VALUE bytes and its RFC-1123 shape.

Curl-confirmed against the deployed `dataplane` binary (io_uring, port 8097):

    $ curl -s -D - -o /dev/null http://127.0.0.1:8097/static/app.js
    HTTP/1.1 200 OK
    Connection: keep-alive
    Date: Mon, 01 Jan 2024 00:00:00 GMT          ← proven here (name + exact value)
    ETag: "9e983f35"
    …

Present on 200, 404, OPTIONS, TRACE, and the 4xx/5xx reject responses alike — the wrapper
injects it on both the accept and the reject branches.

Theorems (pure-kernel; `#print axioms` ⊆ {propext, Quot.sound} — no `native_decide`,
no `Lean.ofReduceBool`):

  * `date_name_wire_bytes` — the header name is exactly the 4 bytes of `"Date"`.
  * `date_value_wire_bytes` — the deployed value `Reactor.ServeConformant.deployNow` is
    exactly the 29 bytes of `"Mon, 01 Jan 2024 00:00:00 GMT"` (pinned via the
    `ba_toList_eq` bridge — pure-kernel `decide`).
  * `date_value_len` / `date_value_dayname` / `date_value_ends_GMT` — the RFC-1123
    structure: length 29, the `"Mon, "` day-name + comma + SP prefix, the `" GMT"` suffix.
  * `date_line_wire_bytes` — the full spliced header LINE `dateHdr` is exactly
    `"Date: Mon, 01 Jan 2024 00:00:00 GMT"` on the wire.
  * `deployed_date_present` — re-states `injectDate_date_present`: for ANY inner response
    bytes, the injected `CRLF ++ Date: <now>` line is genuinely present.

## Residual (honest, carried from `Reactor.ServeConformant`)

`deployNow` is a FIXED RFC-1123 placeholder, not a live wall-clock render — a host time
FFI seam. RFC 7231 §7.1.1.2 requires `Date` PRESENT (satisfied) with valid RFC-1123 SHAPE
(proven here); the VALUE is not claimed to be the real current time.
-/

import Reactor.ServeConformant
import Reactor.Stage.DateHeader

namespace Proto.DateHeaderProven

open Proto (Bytes)

/-- Kernel-reducibility bridge for `toUTF8`-derived byte lists (see `Proto.GzipProven`):
`bs.toList = bs.data.toList`, letting `toUTF8` byte constants close by pure-kernel
`decide` (`{propext, Quot.sound}`; no `native_decide`, no `Lean.ofReduceBool`). -/
private theorem ba_toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  have key : ∀ (n i : Nat) (r : List UInt8),
      bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    intro n
    induction n with
    | zero =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hnlt : ¬ i < bs.size := by omega
      simp only [hnlt, if_false]
      have hdrop : bs.data.toList.drop i = [] := by
        apply List.drop_eq_nil_of_le
        rw [Array.length_toList]
        have : bs.data.size = bs.size := rfl
        omega
      rw [hdrop, List.append_nil]
    | succ n ih =>
      intro i r hi
      rw [ByteArray.toList.loop.eq_def]
      have hlt : i < bs.size := by omega
      simp only [hlt, if_true]
      rw [ih (i+1) (bs.get! i :: r) (by omega)]
      have hidx : i < bs.data.toList.length := by rw [Array.length_toList]; exact hlt
      have hsz : i < bs.data.size := by rw [← Array.length_toList]; exact hidx
      have hget : bs.get! i = bs.data.toList[i]'hidx := by
        rw [show bs.get! i = bs.data.get! i from rfl, Array.get!_eq_getElem!,
            getElem!_pos bs.data i hsz, ← Array.getElem_toList hsz]
      rw [List.drop_eq_getElem_cons hidx, List.reverse_cons, hget, List.append_assoc]
      rfl
  have h := key bs.size 0 [] (by omega)
  rw [ByteArray.toList]
  simpa using h

/-! ## The exact wire bytes -/

/-- **`date_name_wire_bytes`.** The deployed `Date` header name is exactly the 4 ASCII
bytes of `"Date"`. -/
theorem date_name_wire_bytes :
    Reactor.Stage.DateHeader.dateName = [68, 97, 116, 101] := rfl

/-- **`date_value_wire_bytes`.** The deployed `Date` value the wrapper injects is exactly
the 29 bytes of `"Mon, 01 Jan 2024 00:00:00 GMT"` — pinned through the `ba_toList_eq`
bridge (pure-kernel `decide`, no `native_decide`), matching the curl
`Date: Mon, 01 Jan 2024 00:00:00 GMT`. -/
theorem date_value_wire_bytes :
    Reactor.ServeConformant.deployNow =
      [77, 111, 110, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 50, 52, 32,
       48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84] := by
  simp only [Reactor.ServeConformant.deployNow, ba_toList_eq]; decide

/-! ## The RFC-1123 structure -/

/-- **`date_value_len`.** The deployed `Date` value is exactly 29 octets — the fixed width
of an RFC-1123 `IMF-fixdate`. -/
theorem date_value_len : Reactor.ServeConformant.deployNow.length = 29 := by
  rw [date_value_wire_bytes]

/-- **`date_value_dayname`.** The value begins with `"Mon, "` — the RFC-1123 day-name,
comma, and single space. -/
theorem date_value_dayname :
    Reactor.ServeConformant.deployNow.take 5 = [77, 111, 110, 44, 32] := by
  rw [date_value_wire_bytes]

/-- **`date_value_ends_GMT`.** The value ends with `" GMT"` — the mandatory RFC-1123 GMT
zone token. -/
theorem date_value_ends_GMT :
    Reactor.ServeConformant.deployNow.drop 25 = [32, 71, 77, 84] := by
  rw [date_value_wire_bytes]

/-- **`date_line_wire_bytes`.** The full header LINE the wrapper splices (`dateHdr =
dateName ++ ": " ++ deployNow`) is exactly the wire bytes of
`"Date: Mon, 01 Jan 2024 00:00:00 GMT"`. -/
theorem date_line_wire_bytes :
    Reactor.ServeConformant.dateHdr =
      [68, 97, 116, 101, 58, 32,
       77, 111, 110, 44, 32, 48, 49, 32, 74, 97, 110, 32, 50, 48, 50, 52, 32,
       48, 48, 58, 48, 48, 58, 48, 48, 32, 71, 77, 84] := by
  simp only [Reactor.ServeConformant.dateHdr,
             Reactor.Stage.DateHeader.dateName, Reactor.ServeConformant.deployNow,
             ba_toList_eq]
  decide

/-! ## The deployed byte-effect: `Date` reaches the wire -/

/-- **`deployed_date_present`.** Re-states `Reactor.ServeConformant.injectDate_date_present`:
for ANY inner-serve response bytes, the wrapper's `injectDate` genuinely carries the
`CRLF ++ Date: <now>` line — this is why every deployed response shows a `Date` header. -/
theorem deployed_date_present (bs : Bytes) :
    ∃ pre suf, Reactor.ServeConformant.injectDate bs
      = pre ++ (Reactor.crlf ++ Reactor.ServeConformant.dateHdr) ++ suf :=
  Reactor.ServeConformant.injectDate_date_present bs

end Proto.DateHeaderProven

#print axioms Proto.DateHeaderProven.date_name_wire_bytes
#print axioms Proto.DateHeaderProven.date_value_wire_bytes
#print axioms Proto.DateHeaderProven.date_value_len
#print axioms Proto.DateHeaderProven.date_value_dayname
#print axioms Proto.DateHeaderProven.date_value_ends_GMT
#print axioms Proto.DateHeaderProven.date_line_wire_bytes
#print axioms Proto.DateHeaderProven.deployed_date_present
