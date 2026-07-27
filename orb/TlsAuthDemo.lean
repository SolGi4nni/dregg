/-
# TlsAuthDemo — the real-CA authentication gate for the verified TLS client.

Drives `TlsClient.handshake` against a live TLS 1.3 endpoint and reports the
three verdicts that make up server authentication:

  * `certVerify` — the leaf's CertificateVerify signature over the transcript,
    checked with the audited HACL* verify dispatched by SignatureScheme
    (Ed25519 / ECDSA-P256-SHA256 / RSA-PSS-SHA256);
  * `finished`   — the server Finished HMAC;
  * `chain`      — the served certificate chain built to a PINNED trust root via
    the verified `Pki.ChainBuild.verifyPathW` with the audited signature oracle
    (HACL* for ECDSA-P256 / RSA-PSS / Ed25519 links; audited aws-lc for
    `sha256WithRSAEncryption` / PKCS#1 v1.5 links — the padding real RSA CA chains
    such as Let's Encrypt R10/R11 → ISRG Root X1 sign with).

Usage:
  tls-auth-demo <ip> <port> <sni> <rootCaDerPath> <nowYYYYMMDDHHMMSS>

Exit 0 iff all three verdicts hold. This is the gate's harness: pointed at a
genuine endpoint whose chain builds to the pinned root it prints ACCEPT (0);
pointed at a MITM / self-signed leaf whose chain does not build it prints REJECT
(nonzero). Nothing here parses TLS or holds a key — it only prints `TlsClient`'s
verdicts.
-/
import TlsClient

open TlsClient

def main (args : List String) : IO UInt32 := do
  match args with
  | [ip, portS, sni, rootPath, nowS] =>
    let port := (portS.toNat?.getD 443).toUInt16
    let now := nowS.toNat?.getD 0
    let rootBytes ← IO.FS.readBinFile rootPath
    let rootDer := rootBytes.toList
    IO.println s!"== drorb verified TLS client — real-CA authentication gate =="
    IO.println s!"   endpoint {ip}:{port}  SNI={sni}"
    IO.println s!"   trust root: {rootPath} ({rootDer.length} DER bytes)"
    IO.println s!"   now (YYYYMMDDHHMMSS): {now}"
    match ← handshake ip port sni with
    | .error e =>
      IO.eprintln s!"HANDSHAKE FAILED: {e}"
      return 2
    | .ok s =>
      TlsClient.tcpClose s.fd
      let nCerts := s.chainDers.length
      -- Per-cert diagnostics from the ChainBuild parse.
      let parsed := (s.chainDers ++ [rootDer]).mapM parseCert
      let chainOk := authenticateChain s.chainDers rootDer now
      IO.println s!"   certificates served: {nCerts}  (+1 pinned root appended)"
      match parsed with
      | some ps =>
        for p in ps do
          let schemeName :=
            if p.sigAlg == 0x0403 then "ecdsa-p256-sha256 (HACL*)"
            else if p.sigAlg == 0x0804 then "rsa-pss-sha256 (HACL*)"
            else if p.sigAlg == 0x0401 then "sha256WithRSAEncryption/pkcs1v1.5 (aws-lc, audited)"
            else if p.sigAlg == 0x0807 then "ed25519 (HACL*)"
            else "UNSUPPORTED"
          IO.println s!"     cert subjHash={p.abs.subject} issHash={p.abs.issuer} \
                         isCA={p.abs.isCA} sigAlg={schemeName} window=[{p.abs.notBefore},{p.abs.notAfter}]"
      | none => IO.println "     (chain parse failed)"
      IO.println s!"   certVerify (leaf key possession) : {s.certVerify}"
      IO.println s!"   finished   (server Finished HMAC) : {s.finished}"
      IO.println s!"   chain      (builds to pinned root): {chainOk}"
      if s.certVerify && s.finished && chainOk then
        IO.println "RESULT: ACCEPT — server authenticated (leaf + chain to trust root)."
        return 0
      else
        IO.println "RESULT: REJECT — server authentication failed."
        return 1
  | _ =>
    IO.eprintln "usage: tls-auth-demo <ip> <port> <sni> <rootCaDerPath> <nowYYYYMMDDHHMMSS>"
    return 3
