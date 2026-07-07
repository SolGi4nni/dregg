import Stun
/-!
# STUN Binding-server harness (RFC 5389, RFC 5780, short-term credentials)

Serves `Stun.serve` — the proven authenticated Binding-server step — over a
line protocol so a UDP bridge can drive it with real datagrams from
off-the-shelf STUN and ICE clients.

Configuration, from the command line (all optional):
  `--username <hex>`   expected USERNAME value (short-term credential)
  `--key <hex>`        HMAC-SHA1 key (the password)
  `--primary <family>:<port>:<addrHex>`    the primary transport address
  `--alternate <family>:<port>:<addrHex>`  the alternate address (RFC 5780)

Input, one datagram per line:
  `<recvSock> <family> <port> <addrHex> <dataHex>`
where recvSock is 0..3 (bit 0x2 = alternate IP, bit 0x1 = alternate port —
which server socket received the datagram), family is 1 (IPv4) or 2 (IPv6),
addrHex the source address bytes, dataHex the raw datagram.

Output, one line per datagram: `<sendSock> <responseHex>` — the socket to send
from, in the same encoding — or `-` when the proven core stays silent
(malformed input, non-request message).

Run from the repository root:
  `lake env lean --run conformance/stun/harness.lean [config args]`
-/

def hexVal (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

partial def decodeHexAux (cs : List Char) (acc : List UInt8) : Option (List UInt8) :=
  match cs with
  | [] => some acc.reverse
  | hi :: lo :: rest => do
    let h ← hexVal hi
    let l ← hexVal lo
    decodeHexAux rest (UInt8.ofNat (h * 16 + l) :: acc)
  | [_] => none

def decodeHex (s : String) : Option (List UInt8) :=
  if s = "-" then some [] else decodeHexAux s.data []

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + n - 10)

def encodeHex (b : List UInt8) : String :=
  String.mk (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

/-- `<family>:<port>:<addrHex>` → endpoint. -/
def parseEndpoint (s : String) : Option Stun.Endpoint :=
  match s.splitOn ":" with
  | [famS, portS, addrH] => do
    let fam ← famS.toNat?
    let port ← portS.toNat?
    let addr ← decodeHex addrH
    pure { family := fam, port := port, addr := addr }
  | _ => none

/-- Fold the command-line arguments into a server configuration. -/
def parseConfig : List String → Option (List UInt8) → Option (List UInt8) →
    Stun.Config → Option Stun.Config
  | [], some u, some k, cfg => some { cfg with auth := some { username := u, key := k } }
  | [], none, none, cfg => some cfg
  | [], _, _, _ => none
  | "--username" :: v :: rest, _, k, cfg => do
    parseConfig rest (← decodeHex v) k cfg
  | "--key" :: v :: rest, u, _, cfg => do
    parseConfig rest u (← decodeHex v) cfg
  | "--primary" :: v :: rest, u, k, cfg => do
    parseConfig rest u k { cfg with primary := ← parseEndpoint v }
  | "--alternate" :: v :: rest, u, k, cfg => do
    parseConfig rest u k { cfg with alternate := ← parseEndpoint v }
  | _, _, _, _ => none

def sockOfNat (n : Nat) : Bool × Bool := (n / 2 % 2 == 1, n % 2 == 1)

def natOfSock : Bool × Bool → Nat
  | (ip, port) => (if ip then 2 else 0) + (if port then 1 else 0)

def handle (cfg : Stun.Config) (line : String) : String :=
  match line.trim.splitOn " " with
  | [sockS, famS, portS, addrH, dataH] =>
    match sockS.toNat?, famS.toNat?, portS.toNat?, decodeHex addrH, decodeHex dataH with
    | some sock, some fam, some port, some addr, some dat =>
      match Stun.serve cfg (sockOfNat sock) dat
          { family := fam, port := port, addr := addr } with
      | some (send, r) => s!"{natOfSock send} {encodeHex r}"
      | none => "-"
    | _, _, _, _, _ => "-"
  | _ => "-"

partial def loop (cfg : Stun.Config) (stdin : IO.FS.Stream)
    (stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then
    return ()
  else
    stdout.putStr (handle cfg line ++ "\n")
    stdout.flush
    loop cfg stdin stdout

def main (args : List String) : IO UInt32 := do
  match parseConfig args none none {} with
  | none =>
    (← IO.getStderr).putStrLn "harness: bad configuration arguments"
    return 1
  | some cfg =>
    loop cfg (← IO.getStdin) (← IO.getStdout)
    return 0
