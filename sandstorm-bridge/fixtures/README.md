# sandstorm-bridge fixtures

Drop a real signed catalog `.spk` here as `sample.spk` to run the real-catalog
differential harness (`tests/real_spk_fixture.rs`). A representative one lives at
`snoopy:~/dregg-share/sample.spk` (canonical magic `8fc6cdef451aea96`); fetch it with:

```
scp snoopy:~/dregg-share/sample.spk sandstorm-bridge/fixtures/sample.spk
```

When `sample.spk` is absent the harness does **not** skip — it mints a
genuinely-signed, self-contained `.spk` in-test (via `SpkBuilder::pack`: real xz +
combined Ed25519/SHA-512 signature + real capnp `Archive`) and runs the full
parse/verify/manifest/grain + anti-tamper teeth against it, so the security
guarantee is always exercised (never a silent green). When the real `sample.spk`
is present it additionally asserts the "Simple Todos" catalog ground truth as a
differential and emits the signal for the Cap'n Proto `Archive`-wire swap (step ④
of `docs/SANDSTORM-DEVNET-READY.md`). `sample.spk` itself is intentionally not
committed (it is a third-party package; keep it out of git).
