# DEBT-A mod-p wrap-forgery audit — findings + repair playbook (found 2026-07-11; CLOSED + DEPLOYED 2026-07-13)

The DEBT-A migration retargeted `VmConstraint.holdsVm .gate` from `body.eval = 0` over ℤ to
`body.eval ≡ 0 [ZMOD 2013265921]` (BabyBear `p < 2³¹`). This broke a large cascade of circuit-apex
soundness modules (~of 196 `Dregg2/Circuit/*.lean`) and — because `p < 2³¹` with un-range-checked
limbs — exposed a **class of deployed wrap forgeries**. Two of them were real availability
mint-from-nothing forgeries in the deployed circuit.

**Status: the availability wrap-forgery class is CLOSED across the whole transfer-shaped cohort and
DEPLOYED in the live VK** (provenance-clean regen `887b95e76`, sweep-up `4dd7adee0`). This doc keeps
the classifying rule (the reusable playbook), the two concrete forgeries as the historical record of
what was found, and adds the RESOLUTION section describing the deployed closure.

## THE CLASSIFYING RULE (load-bearing, reusable)
A migrated keystone is a **WRAP FORGERY** iff BOTH:
1. an **un-range-checked** operand/limb whose reconstructed ℤ value can exceed `p`, AND
2. the invariant is an **ORDER** (`≤`) — order is NOT preserved mod `p` (an underflow wraps to `+p ∈ [0,2³⁰)`,
   passing the 30-bit range check).

Otherwise it is **REPAIRABLE** by threading canonicality:
- **equality / tick / write** (e.g. `nonce+1`, `fields[slot]=v`): recover the exact ℤ equality via the row's
  canonicality envelope (`canon_eq_of_modEq`), OR state `≡ [ZMOD p]`.
- **`≡ [ZMOD p]` balance congruence** (debit/credit): restate the conclusion as the congruence, re-prove.
- **bitwise-boolean subset** (attenuation/facet non-amp): `bit·(bit−1) ≡ 0 [ZMOD p]` + bit-canonicality
  (`0 ≤ bit < p`) pins each bit `{0,1}` exactly → faithful.

## THE MECHANICAL RED CAUSE
The migrated `*Vm_faithful` / gate sources gained a new `hcanon`/`hgc`/`hhc`/`CapOpenRowCanon` argument
(the canonicality the deployed range-check supplies). Downstream refinement calls missing it go red →
Lean error-recovery inserts `sorryAx` → the `#assert_axioms` gate fails. **Fix = thread the canonicality**
(from the row's range table if the column is range-checked; as a NAMED residual field on the `rotatedEncodes*`
structure — documented — if it isn't), then restate faithfully per the rule above.

## THE TWO FORGERIES THAT WERE FOUND (now closed — see RESOLUTION)
Both are **availability** (`amt ≤ bal`) — an ORDER over the un-range-checked amount limb, exactly the
wrap-forgery signature above. Recorded here with their concrete witnesses as the historical record.
1. **Transfer availability** (`RotatedKernelRefinement.lean`) — witness `pre.bal=0, amt=10⁹ → post.bal=1013265921 ∈ [0,2³⁰)`
   passes the 30-bit range check, yet `amt>bal`. Mint-from-nothing.
2. **Burn availability** (`RotatedKernelRefinementMintBurn.lean`) — witness `before=1, amt=1006632961`. WORSE than
   transfer: burn's ledger frame credits the well `(a,a)`, so the underflow **inflates well supply** =
   mint-from-nothing into the well.

## RESOLUTION — CLOSED across the transfer-shaped class + DEPLOYED
The forgery class is closed for the **whole transfer-shaped cohort — 10 members**: 5 narrow
(transfer, burn, fee, cap-open-EFF, cap-open-TB) and their 5 wide twins. For each member, availability
`amt ≤ bal` is now **circuit-FORCED** on a hardened `*Avail` descriptor rather than named as a residual.

How the closure works:
- **`graduableWide` + the 15-bit borrow weld.** Each hardened `*Avail` descriptor carries the availability
  witness limbs and a per-row borrow bit; the IR-2 assembly realizes 15-bit range teeth on the limbs.
  With every limb `< 2¹⁶ < p`, the subtraction cannot wrap in the field — a mod-`p` underflow is
  **structurally impossible**, so the ORDER `amt ≤ bal` holds over ℤ, not merely mod `p`. This converts
  the un-range-checked limb (condition 1 of the rule) into a range-checked one, which retires the class.
- **`guardAvail` DISCHARGED in Lean.** The eight modules
  `RotatedKernelRefinement{Avail, AvailWide, CapOpenAvail, CapOpenAvailWide, FeeAvail, FeeAvailWide,
  MintBurnAvail, MintBurnAvailWide}.lean` prove the availability obligation from the borrow weld — no
  named residual, no `sorryAx`. All are axiom-clean under `#assert_axioms`; every forgery witness is UNSAT
  against the hardened descriptors.
- **Empirically validated.** `circuit/tests/avail_weld_live_roundtrip.rs` (3/3): each hardened member
  proves and verifies live, and a forged NO-FINAL-BORROW bit on an honest trace is REFUSED at proof time.
- **DEPLOYED via a clean regen.** All three registries (`rotation-v3-staged-registry.tsv`,
  `rotation-wide-registry-staged.tsv`, `rotation-wide-umem-welded-registry-staged.tsv`) route every cohort
  member to its `*Avail` descriptor; the emission retargets landed in `circuit/src/effect_vm_descriptors.rs`.
  The FP constant is re-stamped → a new VK epoch with mint-from-nothing closed. The regen is
  provenance-clean (`source dirty = no`) — commit `887b95e76` (VK-REGEN) plus `4dd7adee0` (sweep-up of the
  shared-file emission retargets). Recorded as the `2026-07-13` row in `docs/VK-REGEN-LOG.md`.

## REMAINING (the DEBT-A campaign — multi-agent, cascading)
The availability forgery class is closed; the rest of the DEBT-A cascade is mechanical repair, not
forgeries. Red from the same migration is repaired module-by-module by the classifying rule above
(REPAIRABLE via canonicality threading). As each is repaired, **check for the availability-class
signature** (an order over an un-range-checked limb) — that is where any remaining real deployed bug
would hide; none has surfaced outside the transfer-shaped cohort. The whole-tree gauntlet greens when
the cascade completes.
