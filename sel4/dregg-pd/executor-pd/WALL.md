# The executor-PD wall — PASSED, and step 4 DONE: the verified executor runs INSIDE seL4

*The firmament's one true blocker (docs/FIRMAMENT.md §6, §7) — the ELF Lean
runtime — is BUILT, the VERIFIED executor runs one real turn through
`dregg_exec_full_forest_auth` on aarch64-linux-musl, AND (step 4) that turn now
runs INSIDE a real seL4 protection domain booted under qemu-system-aarch64,
emitting the identical accepted receipt over serial (`../executor-rootserver/`,
`out/sel4-boot-evidence.log`). Probed against the live toolchain (leanrt v4.30.0,
Lean `d024af099`, the in-tree `metatheory/` closure), run under aarch64 Linux/musl
AND on seL4, on 2026-06-13.*

## The four-step excision plan — where each stands now

| Step | What | Status |
|------|------|--------|
| (1) | ELF-recompile the Lean closure under leanc | **✅ GREEN** |
| (2) | ELF leanrt + the Lean library bottom-half (Init/Std/Lean/mathlib/deps) | **✅ GREEN — built** |
| (3) | GMP for ELF | **✅ GREEN — real GMP 6.3.0 cross-built** |
| (4) | host on seL4 (`sel4-musl` + `root-task-with-std`) | **✅ DONE** — the verified turn runs INSIDE a seL4 PD (`../executor-rootserver/`) |

**The turn runs.** `scripts/link-probe.sh` links the verified closure + the ELF
runtime into a static `aarch64-linux-musl` executable (`out/dregg-executor.elf`,
0 undefined symbols) and drives one real turn. On the `wideDemoInput` wire the
verified `dregg_exec_full_forest_auth` (= `execFullForestG` + admission) produces
**`status:2, ok:1` (bodyCommitted)** — nonce 7→8, a 30-unit transfer (cell-0 bal
100→70, cell-1 5→35), balance 100→90, a nullifier + commitment registered. The
boot/run evidence is `out/dregg-executor-run.log`. The same binary is the host-
musl validation of what the seL4 executor-PD will run (sel4-musl emulates the
musl syscall surface) — so the turn is banked BEFORE the PD link.

## How the wall fell (the build pipeline, all in `scripts/`)

The destination is an seL4 PD embedding the VERIFIED executor. Step (1) had
already ELF-recompiled the closure; the wall was that **no ELF Lean runtime
existed** to link it against (the toolchain ships leanrt/leancpp Mach-O-only with
no C++ sources). The fix was to rebuild the runtime + library bottom-half from
the upstream `lean4@d024af099` sources for a **hosted aarch64-linux-musl** target
(NOT bare freestanding — the Lean runtime is hosted C++ needing libstdc++ + malloc
+ GMP, all supplied by the `aarch64-unknown-linux-musl` GCC cross-toolchain that
`sel4-musl` emulates in-PD):

1. **ELF leanrt** (`build-leanrt-elf.sh`) — the 24 runtime objects (incl. `io.cpp`,
   the IO-monad core), a 5-symbol **mimalloc shim** over musl malloc, and a small
   **libuv stub** (the excision: drop `libuv.cpp` + the 8 `uv/*.cpp`, keep the IO
   monad; the pure executor turn does no socket/file/timer). `init_module.cpp` is
   welded to skip only `initialize_libuv()`.
2. **ELF Lean library** (`build-leanlib-elf.sh`) — re-emits the C facets for
   `Init` (589), `Std` (442), and `Lean` (1105) via the toolchain `lean -c` from
   the cloned sources, then ELF-compiles them (the step-1 recipe). The dependency
   libs (`Batteries`, `Aesop`, `Qq`, `Plausible`, `ProofWidgets`, `ImportGraph`,
   `LeanSearchClient`) and `mathlib` (8098) compile from their existing `.lake`
   facets via `compile-facets-elf.sh`.
3. **ELF Lean kernel C++** (`build-leancpp-elf.sh`) — the 17 `src/kernel/*.cpp` +
   `src/util/*.cpp` (Expr/Level smart constructors, instantiate, the typechecker).
   Some live module initializers build `Expr`/`Level` literals at init, so these
   `lean_expr_*`/`lean_level_*` are genuinely needed (the run probe surfaced this
   when a stub aborted on `lean_level_mk_data` — an honest result).
4. **Real GMP** (`build-gmp-elf.sh`) — GMP 6.3.0 cross-built static for
   aarch64-musl (the toolchain bundles GMP internally but exposes no `libgmp.a`).
   `-std=gnu17` works around GCC-15's C23 default rejecting GMP's configure probes.
5. **The link** (`link-probe.sh`) — joins the closure + the four bottom-halves
   under `--start-group`, GC-reduced from the entry, with the real crypto floor +
   small stub TUs:
   - **the REAL crypto floor** (`crypto-floor.c` + the `dregg-crypto-floor`
     staticlib, `crypto-floor/`) — the 8 `dregg_*` portals at the EXACT Lean C ABI
     (`lean_object*` in/out, read from `metatheory/.lake/.../PortalFloor.c`), with
     the HASHES wired to the SAME carried crypto the verifier-stark PD runs on seL4
     (Plonky3-conformant Poseidon2 over BabyBear + BLAKE3). A turn that hashes now
     computes a real on-device digest. REAL: Poseidon2 (§4, KAT'd == the circuit's
     `hash_2_to_1`), BLAKE3 (§5), the Poseidon2-derived nullifier (§6), the
     BLAKE3-keyed MAC (§8), AND **§2 STARK verification** — the staticlib now
     carries the verifier-stark `stark_core` (BabyBear+BLAKE3+FRI+Fiat-Shamir)
     verbatim and exposes `dreggcf_stark_verify_bytes(proof, pi)`: decode the
     structured proof, resolve the carried AIR, run `stark::verify` — ACCEPT a
     sound proof, REJECT a tampered proof / wrong PI (the anti-ghost + boundary
     teeth). **§2.1 — the LIVE proof-carrying-turn admission path is now wired**:
     `dreggcf_admit_proof_carrying_turn(wire)` decodes a turn's `PCT1` envelope (the
     proof bytes + public inputs a producer ships OUT OF BAND alongside the turn —
     `magic + turn_id + len-prefixed proof + len-prefixed PI`), pulls the *carried*
     proof + PI, routes them through `dreggcf_stark_verify_bytes`, and returns the
     ADMISSION verdict (1 = ADMIT iff the carried proof verifies, 0 = REFUSE,
     fail-closed). So a LIVE turn's proof bytes reach the real verifier — not just
     the in-line selftest (which mints + verifies in one breath). The anti-ghost
     teeth now bite ON THE ADMISSION PATH: a genuine turn ADMITS, a tampered-proof /
     wrong-PI / malformed-envelope turn REFUSES (`dreggcf_admit_selftest()` → `0x7`).
     (The Lean `dregg_stark_verify` *abstract Nat-pair* portal still fails closed —
     two opaque Nats carry no checkable proof; the real check is the byte channel
     the proof-carrying turn feeds.) **The three elliptic-curve primitives are NOW
     ALSO REAL** (welded from the SAME in-workspace crates the executor + cell use):
     **ed25519 (§1)** — `dreggcf_ed25519_verify` runs ed25519-dalek `verify_strict`
     (the exact check `turn/src/executor/authorize.rs` + the net-client turn gate
     run); **Pedersen (§3)** — `dreggcf_pedersen_commit` computes the Ristretto255
     `value·V + blinding·R` commitment byte-IDENTICAL to
     `cell::value_commitment::commit_bytes` (the commitment the executor's
     conservation check consumes and the circuit binds — the circuit does NOT
     algebraically re-derive a value commitment, it binds these 32 bytes as a
     public input, so matching them byte-for-byte is what "the same primitive the
     circuit verifies" means); **AEAD (§7)** — `dreggcf_chacha_{seal,open,authenticate}`
     runs ChaCha20-Poly1305, the committed-note ECIES box's primitive
     (`cell::note_encryption`). The C shim marshals the structured byte inputs out
     of the opaque Lean Nat/Int args (LE magnitudes) via `nat_to_le_bytes` /
     `le_bytes_to_nat` (pure `lean.h` Nat API — no GMP coupling). Each accepts iff
     valid, FAIL-CLOSED otherwise (a forged sig / wrong value / tampered ciphertext
     never spuriously passes). (Was `crypto-stub.c`: panic-if-reached with WRONG
     arity/types; then an ABI-correct fail-closed floor.) Run-verified via
     `crypto-floor-selftest.c` (calls each portal at the Lean ABI: the §1/§3/§7
     elliptic-curve teeth driven END-TO-END with Rust-minted test vectors, the
     STARK verify teeth, the LIVE admission teeth; the ELF links clean — 0 undefined
     symbols, the `dregg_{ed25519_verify,pedersen_commit,aead_open}` portals +
     `dreggcf_*` present as defined text in the selftest ELF) and
     `sel4/crypto-floor-hosttest/` (the byte-channel, the LIVE-turn admission, AND
     the §1/§3/§7 elliptic-curve teeth — incl. the Pedersen==commit_bytes and
     AEAD-opens-a-cell-sealed-note interop teeth — all run natively on the host,
     every bitmask `0xF`/`0x7`; on-device RUN of the selftest ELF awaits a user-mode
     `qemu-aarch64`, absent on macOS — the clean link is the on-device checkpoint).
   - `init-stubs.c` — the closure's import-boundary initializers. The **Lean
     elaborator** is cut at the SHAPE of the closure: `cross-compile-closure.sh`
     compiles exactly the import closure rooted at `Dregg2.Exec.FFI` (77 local
     modules), and EXCLUDES the one runtime-dead leaf `Dregg2.Tactics` (pure
     metaprogramming — its facet `LEAN_EXPORT`s zero `l_*` runtime functions, only
     `initialize_Dregg2_Dregg2_Tactics`, which chains into `initialize_Lean` + the
     mathlib Tactic inits). With `Tactics.c` absent from the archive, the only
     facet that ever called `initialize_Lean` is gone, so the elaborator init-chain
     is never pulled. `initialize_Dregg2_Dregg2_Tactics` (still called by the 22
     importing facets' inits) is then a genuine boundary no-op here, not a
     link-order shadow of a linked-but-dead member. `initialize_Lean` /
     `initialize_aesop_Aesop` no-ops stay (aesop is still reached via
     `Dregg2.Catalog`; the `Lean` no-op is defensive over the runtime archives).
   - `kernel-stub.c` (`kernel-stub-syms.txt`) — the libuv/dynlib/module-IO/
     elaborator-typechecker entries (`lean_uv_*`, `lean_kernel_check`, …) the dead
     tactic facets reference but the turn never reaches.
   - `dead-stub.c` (`dead-stub-syms.txt`) — a handful of metaprogramming/lemma
     `initialize_*`/`l_*` symbols pulled by dead init-chains (Lake/Qq/plausible/
     parallel-elab); no-op'd / abort-guarded (verified unreachable on the turn).
   - `aux-defs.c` — see the one fidelity gap below.

## The one re-emission fidelity gap (characterized + recovered exactly)

The released `lean -c`, reading the prebuilt v4.30.0 `.olean`s, is internally
inconsistent for **`l_String_instDecidableLtRaw___aux__1`**: `Init.Data.String.Basic`
*calls* it (Basic.c:1672, 5795) but `Init.Data.String.PosRaw` (its canonical owner,
where the toolchain's bootstrap `libInit.a` defines it) does **not** re-emit it — so
no re-emitted module supplies the body. It is reached at executor **init** (core
String infra). Recovered exactly (not hand-rolled): the SELF-CONTAINED wrapper that
IS emitted (`PosRaw.c: l_String_instDecidableLtRaw`) is verbatim `return
lean_nat_dec_lt(p1,p2)` (a `String.Pos.Raw` is a `Nat` byteIdx; its `<` is `Nat.decLt`),
and the `___aux__1` worker is the same instance's equation form — so the faithful
body is `lean_nat_dec_lt(p1,p2)` (`aux-defs.c`). Three sibling auxiliaries
(`l_instDecidableLtBitVec___aux__1___redArg`, two `Std.Time.Duration` ones) share the
gap but are unreachable on the turn (verified) and stay abort-guarded in dead-stub.c.

## Step (4): the seL4-PD host — DONE

The executor is now hosted as a **root-task-with-std**-style PD and **the verified
turn runs INSIDE a real seL4 protection domain**, booted under
`qemu-system-aarch64`: the seL4 kernel boots, drops to user space, the PD installs
its `sel4-musl` syscall handler, the Lean runtime initializes, and
`dregg_exec_full_forest_auth` produces the identical `status:2 ok:1` receipt over
serial. The full lane + the boot evidence + the precise wall-by-wall journey
(11 walls cleared, incl. building `muslForSeL4`, a root-task seL4 kernel, fixing
the loader's macOS cross-asm, the RAM/CNode sizing, and the syscall/`__sysinfo`/
`/dev/urandom` startup surface) live in **`../executor-rootserver/`** (see its
`WALL-roottask.md`). The reproducer is `../executor-rootserver/scripts/build-image.sh`.

## Reproduce

```sh
# 0) fetch lean4 sources at the toolchain commit:
git -C /tmp/lean4-rt init && git -C /tmp/lean4-rt remote add origin https://github.com/leanprover/lean4
git -C /tmp/lean4-rt fetch --depth 1 origin d024af099ca4bf2c86f649261ebf59565dc8c622
git -C /tmp/lean4-rt checkout FETCH_HEAD
# 1) the closure (banked) + the runtime bottom-halves:
./scripts/cross-compile-closure.sh                 # the verified closure -> ELF
./scripts/build-leanrt-elf.sh                       # ELF leanrt (+ mimalloc/libuv stubs)
./scripts/build-leancpp-elf.sh                      # ELF Lean kernel C++
./scripts/build-gmp-elf.sh                          # real GMP for aarch64-musl
for L in Init Std Lean; do ./scripts/build-leanlib-elf.sh $L; done
# mathlib + deps from existing .lake facets (compile-facets-elf.sh; see link-probe.sh inputs)
# 2) link + run one turn (host-musl validation, via an aarch64 Linux/musl runtime):
./scripts/link-probe.sh "$(cat out/demo-wire.txt)"  # -> out/dregg-executor.elf, status:2 ok:1
```
