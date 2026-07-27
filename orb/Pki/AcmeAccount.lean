/-
# Pki.AcmeAccount — durable ACME account-key persistence

The RFC 8555 driver (`AcmeIssue`) generates a fresh ES256 account key on every
run. A CA identifies an *account* by its key, so a fresh key each run registers a
NEW account every time — and CAs rate-limit new-account registration hard
(Let's Encrypt allows only a handful of new accounts per IP per few hours). For a
gateway that renews on a timer that is a defect: a later renewal is simply
refused.

This module persists the account signing scalar so re-runs reuse the SAME
account. The scalar is the 32-byte P-256 private key HACL* generated and
validated (`TlsCrypto.P256.pub` accepts it, `Pki.AcmeEs256.accountKeyOfScalar`
derives the JWK). At rest it is those raw bytes — the same representation the
certificate key already uses on disk (`ecdsa-key.bin`). No new primitive, no new
on-disk format, no cryptography beyond the HACL*/EverCrypt the account key was
minted with.
-/
import TlsCrypto.P256
import Pki.Acme
import Pki.AcmeEs256

namespace Pki.AcmeAccount

/-- Generate a P-256 scalar HACL* accepts (retries the vanishingly rare reject),
identical to the certificate-key generator in `AcmeIssue`. -/
partial def freshScalar : IO ByteArray := do
  let b ← IO.getRandomBytes 32
  match TlsCrypto.P256.pub b with
  | some _ => return b
  | none => freshScalar

/-- The directory component of `path`, for `createDirAll`. -/
private def parentDir (path : String) : Option String :=
  (System.FilePath.mk path).parent.map (·.toString)

/-- Load the persisted account scalar at `path`, or generate one and persist it.

A stored file is reused only when it is exactly 32 bytes AND HACL* still accepts
it (`accountKeyOfScalar` succeeds); anything else is replaced, so a truncated or
corrupt key self-heals into a fresh account rather than wedging every future
issuance. A freshly generated scalar is written back (creating the parent
directory first), so the NEXT run reuses THIS key — which is the whole point:
same key ⇒ same ACME account ⇒ no new-account rate-limit on renewal. -/
def loadOrCreateScalar (path : String) : IO ByteArray := do
  if ← System.FilePath.pathExists (System.FilePath.mk path) then
    let b ← IO.FS.readBinFile path
    if b.size == 32 && (Pki.AcmeEs256.accountKeyOfScalar b).isSome then
      return b
    else
      IO.eprintln s!"drorb-acme: account key {path} is unusable ({b.size} bytes); regenerating"
  let s ← freshScalar
  match parentDir path with
  | some d => IO.FS.createDirAll d
  | none => pure ()
  IO.FS.writeBinFile path s
  IO.eprintln s!"drorb-acme: persisted a new ES256 account key to {path}"
  return s

/-- The account-URL sidecar path for an account-key path. -/
def urlPath (keyPath : String) : String := keyPath ++ ".url"

/-- Record the account URL (the `kid`) the CA returned, beside the key, so a
re-run — and an operator — can see which account the key is bound to.
Best-effort: a write failure here never fails issuance. -/
def saveAccountUrl (keyPath : String) (url : String) : IO Unit := do
  try IO.FS.writeFile (urlPath keyPath) url catch _ => pure ()

/-- The persisted account URL for a key path, if one was recorded. -/
def loadAccountUrl (keyPath : String) : IO (Option String) := do
  let p := urlPath keyPath
  if ← System.FilePath.pathExists (System.FilePath.mk p) then
    return some (← IO.FS.readFile p)
  else
    return none

end Pki.AcmeAccount
