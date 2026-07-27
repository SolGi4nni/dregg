/-
# acme-account — provision (or inspect) the durable ACME account key

`acme-account ensure <keyPath>` makes the account key at `keyPath` exist: it
reuses a valid stored key or generates and persists a fresh ES256 one, then
prints its RFC 7638 thumbprint (and the bound account URL, if recorded). Running
it twice prints the SAME thumbprint — the demonstrable form of "re-runs reuse the
account". The renewal scheduler passes the same `keyPath` (as
`DRORB_ACME_ACCOUNT_KEY`) to `acme-issue`, so issuance rides the same account.
-/
import Pki.AcmeAccount

open Pki.AcmeAccount Pki.Acme Pki.AcmeEs256

def main (args : List String) : IO UInt32 := do
  match args with
  | ["ensure", path] =>
    let s ← loadOrCreateScalar path
    match accountKeyOfScalar s with
    | some k =>
      IO.println s!"account key: ES256 (P-256), thumbprint {String.mk (thumbprint k)}"
      match ← loadAccountUrl path with
      | some u => IO.println s!"account url: {u}"
      | none => IO.println "account url: (not yet registered)"
      return 0
    | none =>
      IO.eprintln "could not derive account JWK from the stored scalar"
      return 1
  | _ =>
    IO.eprintln "usage: acme-account ensure <keyPath>"
    return 1
