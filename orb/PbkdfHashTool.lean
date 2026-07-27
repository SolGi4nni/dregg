/-
# pbkdf2-hash — mint a `basic_auth` credential-store hash (AWS-LC PBKDF2)

`pbkdf2-hash <password> [iterations]` derives an AWS-LC PBKDF2-HMAC-SHA256 hash of
`password` (default 600 000 iterations, OWASP-current) with a fresh 16-byte CSPRNG
salt and prints the stored modular string

    pbkdf2_sha256$<iterations>$<salt_hex>$<dk_hex>

Paste that value into a `Dsl.Config.Gateway` `basic_auth` credential entry
(`users := [(<user>, "<this string>")]`). The gate's `Reactor.RouteMw.basicVerify`
accepts it via `Crypto.pbkdf2Verify` (same AWS-LC backend), constant-time compare.
Each run prints a DIFFERENT hash (fresh salt) that still verifies the same password
— the demonstrable form of "the salt is per-hash random". This is the operator
helper for rotating the deployed credential; it draws no config and touches no
control-plane state (ts2021 owns that).
-/
import Crypto

/-- Decode a ByteArray of ASCII bytes (the stored hash is pure ASCII) to a String. -/
def asciiStr (b : ByteArray) : String :=
  String.ofList (b.toList.map (fun x => Char.ofNat x.toNat))

def main (args : List String) : IO UInt32 := do
  match args with
  | [pw] =>
    let h ← Crypto.pbkdf2Hash pw.toUTF8 600000
    IO.println (asciiStr h)
    return 0
  | [pw, iters] =>
    match iters.toNat? with
    | some n =>
      let h ← Crypto.pbkdf2Hash pw.toUTF8 (UInt32.ofNat n)
      IO.println (asciiStr h)
      return 0
    | none =>
      IO.eprintln "usage: pbkdf2-hash <password> [iterations]"
      return 1
  | _ =>
    IO.eprintln "usage: pbkdf2-hash <password> [iterations]"
    return 1
