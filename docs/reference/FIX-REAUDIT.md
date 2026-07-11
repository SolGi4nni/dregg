# FIX-REAUDIT — adversarial re-audit of the four wrap-class soundness fixes

Skeptic's re-audit of the four "just-landed" mod-p wrap-class fixes (commit `81889b0bb` and the
GAP #3 pair `dfc832daa`/`7e2bc7a18`). Mandate: assume each fix is flawed; find where it is
incomplete, algebraically wrong, vacuous, or leaves a residual/symmetric/edge-case wrap. Read-only
except fix #4 (the confirmed credit lead), which is applied here.

## Verdict summary

| # | Fix | Verdict |
|---|-----|---------|
| 1 | VAULT (`VaultSatDescriptor.lean` / `vault_weld.rs`) — CARRY_BITS 16→15, 15-bit schoolbook+borrow | **SUSPECT** — product/borrow core complete; residual: deposit-direction is an *unenforced* premise → large-withdrawal→deposit wrap |
| 2 | CAP-OPEN (`DeployedCapOpen.lean`) — per-16-bit-limb mask reconstruction | **COMPLETE** |
| 3 | CROSS-CELL (`CrossCellConservation.lean`) — dual 3×15-bit credit/debit accumulators | **COMPLETE** (bounded scope; two premises noted) |
| 4 | TRANSFER (`EffectVmEmitTransfer.lean` §11.7) — 15-bit borrow chain, debit-gated | **GAP CONFIRMED then FIXED** — credit overflow-wrap; carry chain added, green |

---

## Fix #4 — TRANSFER availability weld (CONFIRMED GAP → FIXED)

### The credit overflow-wrap is real
The borrow chain (`gBorrow0/1`, `gNoBorrow`) is `direction`-gated to the DEBIT (`dir=1`). On a CREDIT
row (`dir=0`) the only balance constraint pre-fix was `gBalLo` = `new ≡ old + amount [ZMOD p]` and
`gBalHi` passthrough. The operand-assembly + range gates bound `old`, `amount`, `after` each to
`[0, 2^30)` — but **nothing forced `old + amount < p`**. Witness `old = amount = 1006632961` (both
`< 2^30`): `old + amount = 2013265922 ≡ 1 [ZMOD p]`, and `after = 1 < 2^30` passes the after-range.
The destination is credited **1 instead of ~2·10⁹** — value destruction / downward conservation break.

### Cross-cell #3 does NOT catch it — transfer must self-enforce
`CrossCellConservation` accumulates each cell's **mod-p** `NET_DELTA`. The wrapped credit publishes
`new − old = 1 − 1006632961 ≡ 1006632961 [ZMOD p]`, i.e. a canonical residue `1006632961 < 2^30` that
the off-AIR fill records as an honest **credit of ~10⁹** — exactly balancing the sender's debit of
~10⁹. So `Σcredits = Σdebits` **passes**; the wrap is invisible in the field #3 works over. Only a
per-cell **exact-ℤ** `new = old + amount` check detects that the receiver's real balance (1) ≠
`old + amount`. Transfer self-enforcement is required.

### The fix applied (both twins, green)
Mirror of the debit borrow chain, `(1−dir)`-gated to the CREDIT:
- New witness cols `cCRY0`,`cCRY1` (`AVAIL_BASE+8/+9`); `AVAIL_WIDTH` 196→**198**.
- Gates (in `transferAvailGates`, 8→**13**): `gCry0Bool`,`gCry1Bool` (carry-bit booleanity),
  `gCarry0` = `(1−dir)·(bef0+am0 − cc0·2¹⁵ − aft0)`, `gCarry1` = `(1−dir)·(bef1+am1+cc0 − cc1·2¹⁵ − aft1)`,
  `gNoCarry` = `(1−dir)·cc1`. No new ranges (carry bits booleaned in-gate, like the borrow bits).
- Theorems added (all `#assert_axioms`-clean, no sorry/admit, no p-sized decide, derived-not-assumed):
  - `transferAvail_credit_no_overflow` — on `dir=0`, satisfying trace ⟹ `after = before + amount` over
    ℤ (the 15-bit carry chain lifts the addition exactly; `after < 2^30 < p`, no wrap). Sole hypothesis
    is the deployed canonicality `0 ≤ loc c < p` — same as the debit twin, no `hcanonMove`.
  - `transferAvail_credit_forgery_unsat` — the witness (`before=amount=1006632961`, `dir=0`) forces
    `after = 2013265922`, contradicting `after < p`. UNSAT.
- Liveness preserved: `goodAvailRow_gates_hold` (debit) unchanged; new `goodCreditRow_gates_hold` /
  `_ranges_hold` (honest credit `100+30=130`) + a kernel `#guard` that every weld gate body is 0 on
  the credit row. Both borrow and carry chains are direction-gated so neither bites the other side.
- Rust twin `transfer_avail_weld.rs`: `credit_gate`, the five credit gates, `fill_transfer_avail_aux`
  now returns 10 writes and fills/validates the carry chain (panics on `before+amount ≥ 2^30`, failing
  closed = UNSAT). Tests `honest_credit_*` + `over_credit_forgery_is_unfillable` added; counts updated
  (13 gates / 6 ranges / width 198).

Build: `lake build Dregg2.Circuit.Emit.EffectVmEmitTransfer` **green**; downstream
`CrossCellConservation` + `VaultSatDescriptor` green; `dregg-circuit` **lib** compiles (the crate's
*test* target has pre-existing unrelated breakage in `ivc.rs`).

**Honest completeness bar for #4:** both wrap directions now blocked — debit by the no-final-borrow
(`before ≥ amount`), credit by the no-final-carry (`before+amount < 2^30 < p`) — each derived from the
15-bit limb range checks + canonicality, quantified over the real deployed `transferVmDescriptorAvail`.
Remaining honest caveat (unchanged, pre-existing): the weld is STAGED behind the big-bang VK/registry
regen; the live registry still routes the bare `transferVmDescriptor`, so a pure light client does not
yet witness this in production.

---

## Fix #1 — VAULT (SUSPECT: unenforced deposit-direction admits a symmetric wrap)

**The targeted fix is complete.** CARRY_BITS 16→15 makes every schoolbook partial product `< 2^30` and
every carry (`ca,cb,cc,z3`) fit `< 2^15`, so each gate residual `|R| < 2^30 < p` and the mod-p→ℤ lift
(`modEqZeroBounded`, `liftProd*`) is sound; the 4-limb borrow comparison forces `P ≤ Q` (no dilution).
Liveness holds (honest schoolbook limbs all fit 15 bits). The three teeth
(`vault_{zero_mint,no_deposit,dilution}_unsat`) are non-vacuous (`#guard` witnesses bite).

**Residual wrap found (NEW).** The no-dilution guarantee (`vaultSatV3_forces`) is gated on the
*hypotheses* `hAssetDep`/`hShareDep` (`before ≤ after`), which the circuit does **not** self-enforce.
The delta gate pins `after − before ≡ D0 + 2¹⁵·D1 [ZMOD p]` with `D0,D1` 15-bit-ranged (RHS `∈ [0,2^30)`),
and `before` is pinned `< 2^30`. This admits **two** solution bands: the honest deposit
`after−before ∈ [0,2^30)`, AND a **large withdrawal** `after−before ∈ (−2^30, −(p−2^30)] ≈ (−1.07e9, −9.4e8]`
whose mod-p residue lands back in `[0,2^30)`. Concrete: `before_asset = 10^9`, `after_asset = 0`
→ true Δ = −10⁹, but `(−10⁹) mod p = 1013265921 < 2^30` has a valid limb decomposition, so the circuit
treats a **withdrawal of 10⁹ as a deposit of ~1.01e9** and the dilution comparison runs on the forged
positive Δ. `liftDelta`'s `0 ≤ v` obligation is exactly what silently excludes this band — supplied by
the assumed `hAssetDep`, not by a gate.

**Exploitability:** reachability-gated — depends on whether the rotated proof / selector routing can
present `vault_sel=1` on a row whose committed field assets net-*decrease*. Within this descriptor the
forged row is satisfiable and the teeth do not apply.

**Honest bar to close #1:** add an in-circuit `after − before` **no-borrow** gate (the same
availability-weld pattern as #4) — or a delta-sign gate — so the deposit direction is *derived*, not
assumed. Until then the fix closes the product overflow but leaves this symmetric delta-wrap open.

---

## Fix #2 — CAP-OPEN (COMPLETE)

The mask-recon-wrap (a `p`-shifted 32-bit boolean decomposition of the committed mask summing to
`M+kp` with different bits, flipping a `selectedBit`) is genuinely closed. `maskReconLoGate` /
`maskReconHiGate` reconstruct **each 16-bit limb from its own 16 bits**: each sum `< 2^16 < p`, so with
the limb cell canonical (`< p`) the residual `∈ (−2^16, p) ⊂ (−p, p)` and `≡0 [ZMOD p] ⟹ =0` — a
genuine `mask_lo,mask_hi < 2^16` range check with **no** `p`-shift (`mask_lo + p > 2^16` fails it).
Both limbs are covered symmetrically. The full 32-bit `maskReconGate` is **derived**
(`maskReconGate_of_limbs`), not assumed, and `Satisfied` carries the two limb gates; the main
theorems (`capOpen_confers_via_effGate`, line ~942/1149) consume the derived version. Forgery witness
`maskReconLoGate_rejects_wrap` proves the `p`-shifted decomposition UNSAT. Selected-bit membership is
genuine for both low-limb effects (transfer bit 1) and high-limb effects (`n` up to 31, e.g.
`EFFECT_ATTENUATE_CAPABILITY = 1<<23`). Liveness: a broad cap (`EFFECT_ALL = 0xFFFFFFFF`, `mask_hi =
0xFFFF`) decomposes fully and permits — the over-strict equality this replaced would have rejected it.
`#assert_axioms`-clean. No residual wrap found.

---

## Fix #3 — CROSS-CELL CONSERVATION (COMPLETE, bounded scope)

The single-felt `p`-sum forgery (`1006632961 + 1006632960 = p ≡ 0`) is closed by dual 3×15-bit
credit/debit accumulators with per-row carry propagation. Each limb+carry is range-checked `< 2^15`,
each transition residual is a sum of `< 2^15` terms so `|R| < 2^17 < p` and lifts to an exact-ℤ
recurrence (`credit_step`/`debit_step`, no wrap); `ccc_reconC/D_eq_credit/debitSum` prove the
accumulators reconstruct the TRUE integer prefix sums; the `.last` equality boundary pins final credit
limbs = debit limbs, so `Σcredits = Σdebits` over ℤ is **derived** (`ccc_conserves`).
`ccc_psum_forgery_unsat` bites. Sign/present gates correctly force pad rows and the wrong-sign limb to
0. `#assert_axioms`-clean.

**Fails-closed ceiling (not a wrap):** the accumulator is 45-bit (3×15), range-checked per limb, so a
turn whose true credit/debit sum reaches `2^45` (≈ 2¹⁵ rows × 2³⁰) has no valid witness — UNSAT, not a
silent wrap. Honestly above the old ~2³¹ range, so no liveness regression.

**Two premises (unchanged trust boundary, noted for honesty):** (a) the `cc/dc` split is bound to
`present·(sign·mag)` in-AIR, but the binding of `mag`/`sign` to each cell's real `NET_DELTA` is the
**off-AIR fill** from the per-cell proof PIs — a separate boundary, as documented. (b) As shown under
#4, #3 operates on **mod-p** deltas, so it cannot detect a per-cell field-wrap that leaves the mod-p
delta conservation-consistent; that soundness belongs to the per-cell descriptors (now closed both
directions in #4). Within its stated scope (turn-wide conservation of the accumulated contributions),
#3 is complete.
