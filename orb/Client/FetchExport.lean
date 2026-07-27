import Client.H2
import Client.H2Receive
import HuffmanCorrect

/-!
# The C ABI seam for the HTTP/2 outbound (client) path

The dual of `Client.H1`'s `drorb_request_serialize` / `drorb_response_parse`, for
HTTP/2. A native host (`crates/dataplane/src/outbound.rs`) dials an upstream over
a real socket, writes the request octets this module produces, reads the response
frames, and crosses the receive seam to reassemble them — all through the proven
`Client.H2` submit path and `Client.H2Receive` reassembly.

* `drorb_h2_request` — input `aLen :: authority :: pLen :: path` (single-byte
  lengths for the two GET fields); output the exact octet stream
  `Client.H2.requestBytes` writes to open a connection and send a bodyless `GET`
  on stream 1 (the client preface, an empty SETTINGS, and the HPACK `HEADERS`
  frame). This is the proven client submit — `client_preface_sent` /
  `clientRequestHeadersFrame_faithful` hold of exactly these bytes.

* `drorb_h2_response` — input the raw response frame bytes; runs
  `Client.H2Receive.feed` (the CONTINUATION-assembling receive, whose
  faithfulness is `h2_client_receive_faithful`) with the **real** proven Huffman
  decoder (`H3.Qpack.huffmanDecode`, `huffmanDecode_huffEncode`) and reassembles
  the response. Output on success: `1 :: <ASCII status> :: 0 :: <body>`; on a
  failure (no complete response header block): the single byte `0`. The dual of
  `drorb_response_parse` for H2.
-/

namespace Proto
namespace Client
namespace FetchExport

open Proto.Client.H2Receive (feed initR reassemble)

/-- The real proven HPACK Huffman decoder for the H2 receive path: the RFC 7541
Appendix B code, verified round-trip in `HuffmanCorrect` (`huffmanDecode_huffEncode`). -/
def realHuffman : _root_.H2.Hpack.HuffmanDecoder := ⟨_root_.H3.Qpack.huffmanDecode⟩

/-- Build a bodyless `GET` `ClientRequest` for `authority`/`path` over `https`. -/
def getRequest (authority path : List UInt8) : Proto.Client.H2.ClientRequest :=
  { method := [0x47, 0x45, 0x54]                    -- "GET"
    scheme := [0x68, 0x74, 0x74, 0x70, 0x73]        -- "https"
    path := path
    authority := authority
    headers := []
    body := [] }

/-- **`drorb_h2_request`** — the proven H2 client submit octets for a GET on
stream 1. Input framing: `aLen :: authority :: pLen :: path`. Empty/short input ⇒
empty output. -/
@[export drorb_h2_request]
def h2RequestC (input : ByteArray) : ByteArray :=
  match input.toList with
  | aLen :: rest =>
    let authority := rest.take aLen.toNat
    let rest := rest.drop aLen.toNat
    match rest with
    | pLen :: rest =>
      let path := rest.take pLen.toNat
      ⟨(Proto.Client.H2.requestBytes (getRequest authority path) 1).toArray⟩
    | [] => ⟨#[]⟩
  | [] => ⟨#[]⟩

/-- **`drorb_h2_response`** — parse an upstream H2 response through the proven
receive + reassembly with the real Huffman decoder. Output: `1 :: status :: 0 ::
body` on success, the byte `0` on failure. -/
@[export drorb_h2_response]
def h2ResponseC (input : ByteArray) : ByteArray :=
  let (_, evs) := feed realHuffman initR input.toList
  match reassemble evs with
  | none => ⟨#[0]⟩
  | some resp => ⟨((1 : UInt8) :: (resp.status ++ (0 : UInt8) :: resp.body)).toArray⟩

end FetchExport
end Client
end Proto
