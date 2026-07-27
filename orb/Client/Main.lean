import Client.H1

/-!
# `h1-client` — the verified HTTP/1.1 client, driven on real bytes

A tiny host around the proven client core:

* `--emit-request` writes the wire bytes of a `GET / HTTP/1.1` request produced
  by the verified `Proto.RequestSerialize.serialize`;
* `--parse` reads an upstream response off stdin and parses it with the verified
  `Proto.ResponseParse.parse`, printing the recovered status / header count /
  body length.

Piped through a real socket (`… | nc host port | …`) this performs a genuine
outbound HTTP/1.1 exchange whose request bytes and response parse are both the
proven client code — a curl-equivalent through the verified client path.
-/

open Proto

/-- Read all of a stream's remaining bytes. -/
partial def readAll (s : IO.FS.Stream) (acc : ByteArray) : IO ByteArray := do
  let chunk ← s.read 65536
  if chunk.isEmpty then return acc else readAll s (acc ++ chunk)

/-- The demo request: `GET / HTTP/1.1` with `Host` and `Connection: close`
(so the upstream closes and the pipe terminates). -/
def demoReq : Proto.Request :=
  { method := "GET".toUTF8.toList,
    target := "/".toUTF8.toList,
    version := "HTTP/1.1".toUTF8.toList,
    headers := [("Host".toUTF8.toList, "localhost".toUTF8.toList),
                ("Connection".toUTF8.toList, "close".toUTF8.toList)] }

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit-request"] =>
    let bytes : ByteArray := ⟨(Proto.RequestSerialize.serialize demoReq).toArray⟩
    (← IO.getStdout).write bytes
  | ["--parse"] =>
    let data ← readAll (← IO.getStdin) ByteArray.empty
    match Proto.ResponseParse.parse data.toList with
    | none => IO.println "VERIFIED-CLIENT-PARSE fail"
    | some resp =>
      IO.println s!"VERIFIED-CLIENT-PARSE ok status={resp.status} headers={resp.headers.length} bodyLen={resp.body.length}"
  | _ =>
    IO.println "usage: h1-client [--emit-request | --parse]"
