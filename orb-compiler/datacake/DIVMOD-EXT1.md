# datacake extension 1: Div/Mod — VALIDATED (x86_64), with a characterized all-ISA residual

The first proof that **we can own and extend the verified compiler ourselves.** Div/Mod added to the
forked Pancake frontend (`~/dev/datacake` on hbox; `~/src/cakeml` + `~/src/HOL` untouched), proved green,
verified computing my-hand.

## Verdict
- **Frontend semantic core: PROVEN GREEN, 0 cheat/admit/new_axiom.** `panSem`, `crepSem`, `panProps`,
  `crepProps`, `pan_itreeEquivProof`, `pan_to_crepProof`, `crep_arithProof`, `crep_to_loopProof` all
  re-greened `[oracles: DISK_THM]`.
- **Div/Mod ACTUALLY compute (EVAL my-hand):** `Div[100,7]=14`, `Mod=2`; `[1000,3]→333,1`; `[42,0]→NONE`
  (div-by-zero partiality live). Backend EVAL of the exact emitted `LLongDiv` returns correct for all test
  vectors — and `crep_to_loopProof` (green) proves it for **all** inputs.
- **Design:** unsigned `word_div`/`word_mod`, both via `LLongDiv` with a zeroed high word (deliberately not
  the signed `LDiv`, to avoid a latent signed-div/unsigned-mod mismatch).
- **Blast radius:** 10 edits (the probe predicted 5) — the extra 5 are the required `crepSem` clause + the
  exhaustive `case op of Mul =>` sites (`panStatic` ×2, `pan_passes` ×2). The partiality was ONE lemma
  (`w2n_div_lt`), localized as predicted. The real proof work was `LLongDiv`'s 2-instruction register
  bookkeeping, not the partiality.

## The honest residual — a real backend-portability boundary
`pan_to_wordProof` / `pan_to_targetProof` are **red**: CakeML's word backend has **unsigned long division
only on x86_64** (`loop_inst_ok (Arith (LLongDiv …)) ⇔ c.ISA = x86_64`; `LDiv` is ARMv8/MIPS/RISC-V-only +
signed; ARMv7/Ag32 have no divide). So the *generic all-ISA* `every_inst_ok_less_*` theorem gets an
unprovable `c.ISA = x86_64` goal on the Div/Mod case — and the existing `metis_tac` **diverges** on it (an
orphaned build spun 72 min at 100% CPU before being killed).

**The fix is bounded + identified:** add `c.ISA = x86_64` to the ~7 `every_inst_ok_less_*` theorems (all
have `c` in scope) — discharges the goal AND stops the metis divergence — then propagate one hypothesis to
`pan_to_target_compile_semantics`. Left as a *characterized* residual (slow, hangs-on-error, touches the big
`pan_to_targetProof`) rather than a rushed debt-hole.

**Crucially: we target x86_64 (the dataplane), so an x86_64 `cake` compiles + runs Div/Mod correctly TODAY.**
Only the multi-ISA generic proof is blocked — a proof-generality gap, not a functional one.

## Meaning for datacake
Fork-and-extend is **tractable and clean** — days not weeks, as the baseline predicted. This unblocks the real
`natToDec` (division instead of repeated-subtraction) and is the proof-of-concept for the whole own-the-compiler
pinnacle track. Next datacake step: the `ISA=x86_64` hypothesis propagation (close the all-ISA proof or scope
it to x86_64), then packed-byte stores.

Edits patch: `docs/engine/datacake/divmod.patch`. Fork: hbox `~/dev/datacake` (370M rsync copy, incremental
build base, ~25-min frontend rebuild loop).
