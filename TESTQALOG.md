# TESTQALOG — the validation ledger

**APPEND-ONLY. NEVER rewrite or delete another entry — this file is written concurrently by many agents.**
Add your section at the END with a `## <date> — <lane> — <headline>` heading. Cite `file:line`. If you fix
something, say what you fixed and how you VERIFIED it. If you find something you did not fix, NAME it.

---

## The frame (ember, 2026-07-16) — read this before adding anything

> "testing is about **validation**, not verification, you know?"

- **Verification** (the Lean tree) proves *the model we wrote is internally coherent*. It says NOTHING
  about whether the deployed artifact matches that model, or whether the model matches reality.
- **Validation** (this ledger) is the scientific method applied to our correctness ASSUMPTIONS: state the
  assumption, then rig it so **it flags RED if we break it**. That is how a protocol this complex scales
  (ember's years at O(1) Labs on the OCaml integration frameworks — that discipline is why Mina scaled).
- **Dragon's Egg is MORE complex, and AI does not reduce the testing burden. Formal methods do not absolve
  us.** A machine-checked proof of a model is not evidence about the running system.

**ember's honest baseline (do not flatter it):** *"the repo hasn't seen coordinated testing attention from
me in several weeks, so all this stuff is old and extremely underpowered to have confidence in what we have
built."* Expect to find underimplemented, buggy, and sloppy things — in the tests AND in the code they
cover. You are EMPOWERED to make local / mid-scope improvements.

**THE TRAP — do not be deceived by SCALE.** A big test count is not power. Ask of every test: *what real
break would this catch?* Today's proof that scale lies (all found 2026-07-16):
- `tests/src/soundness.rs` — a suite literally named **soundness** was certifying the MOCK IVC. Its
  "tampered hash must fail" passes TRIVIALLY (mutating a field breaks a BLAKE3 digest match). The real
  attack — MINTING a consistent fake — was never tested. It would have passed forever (`61adf7e02`).
- `preflight/checks/*` — the devnet→testnet→mainnet PROMOTION GATE proved SYNTHETIC chains through a mock
  and reported the subsystem GREEN: a gate certifying that the lie is healthy (`e7c692453`).
- **A ratchet that cannot COMPILE cannot bite.** Three gates went silent this way; a non-compiling test
  target is SILENT, not red. It hid a live verify-TCB regression behind 249 un-compiled tests.
- **The root cause**: `.github/workflows/ci.yml` HAS the right gate (`cargo check --workspace
  --all-targets`) — but this clone has NO GitHub remote (only `devnetbox` ssh), so **it never runs here.**
  Guards that never execute are indistinguishable from no guards, except they look protective.

**The questions that matter** (not "how many tests"):
1. What ASSUMPTION does this validate, and would it flag RED if broken?
2. What CONFIGURATION space is never exercised (feature flags, backends, depths, params)?
3. What SCENARIO is never exercised (failure, concurrency, multi-agent, adversarial, recovery)?
4. What COMPOSITION is never exercised (subsystem seams, real e2e flows)?
5. Where do we have VERIFICATION (Lean) but no VALIDATION that the artifact matches it?
6. What is VACUOUS — happy-path-only, tautological, assertion-free, `#[ignore]`d, or unreachable?

---
