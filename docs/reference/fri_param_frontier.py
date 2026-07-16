#!/usr/bin/env python3
"""FRI / circuit parameter security-vs-cost model + efficient-frontier grid search.

READ-ONLY MODEL. Does not touch the deployed config. This is the map ember uses to
choose a leaner FRI config later; it changes nothing.

Ground truth (file:line, all in /Users/ember/dev/breadstuffs):

  Query ledgers (the checked-in budget gate). NEITHER is "the soundness":
    capacity (REFUTED)      = num_queries * log_blowup       + pow_bits
    johnson  (QUERY column) = num_queries * log_blowup // 2   + pow_bits   (integer floor)
    -- circuit/tests/fri_params_soundness_budget.rs:45-53  (CONJECTURED_FLOOR_BITS = 128, :42)

  The capacity column's conjecture is REFUTED: Crites-Stewart (eprint 2025/2046, "On
  Reed-Solomon Proximity Gaps Conjectures") disprove it by reduction; Kambire (arXiv
  2604.09724, "Proximity Gaps Conjecture Fails Near Capacity over Prime Fields") gives a
  prime-field counterexample. Carried as a knob-drift baseline only.

  The commit-phase term eps_C, which the Johnson column DROPS. BCIKS20 (eprint 2020/654),
  Lemma 8.2 / Theorem 8.3, printed pp. 40-41, verbatim:

    eps_FRI = eps_C + alpha^s ,   alpha = sqrt(rho)*(1 + 1/2m) ,   m >= 3
    eps_C   = (m+1/2)^7 * |D0|^2 / (2 * rho^{3/2} * |F|)
              + (2m+1)*(|D0|+1)/sqrt(rho) * (sum_i l^(i))/|F|

  num_queries*log_blowup//2 is -s*log2(alpha) as m -> infinity, i.e. the alpha^s half only.
  ethSTARK (eprint 2021/582) eq. (20) composes the terms:
    lambda >= min{-log2 eps_C, zeta - s*log2 alpha} - 1

  This script MIRRORS Dregg2.Circuit.FriLedger.friCommitLedger (metatheory/Dregg2/Circuit/
  FriLedger.lean), which is the authority; commit_bits() below reproduces its #eval outputs
  exactly (71 at |D0|=2^12 / 55 at 2^20 / 78 at m=3, deployed wrap).

  Challenge field cap:  degree-4 BabyBear extension ~ 2^124
    -- circuit/src/plonky3_prover.rs:63 (BinomialExtensionField<BabyBear,4>), :113 comment
    Both query ledgers are additionally capped by min(., 124) and the Poseidon2 commitment
    hash -- but eps_C binds FIRST: the ext-degree-4 eq.(20) ceiling is ~77.98, not ~124.

  Deployed IR-v2 knobs (log_blowup=6, log_final_poly=0, max_log_arity=3, q=19, pow=16):
    -- circuit/src/descriptor_ir2.rs:5382-5386  (IR2_FRI_* consts)
  Deployed v1 knobs (log_blowup=3, q=38, pow=16):
    -- circuit/src/plonky3_prover.rs:98-102  (PROD_FRI_* consts)

  Measured IR-v2 cost grid (release, --test-threads=1), the SAME real transfer proven at
  every (log_blowup, num_queries) size-parity point, 4-bit-nibble range table:
    -- circuit/tests/effect_vm_ir2_size_measure.rs:355-403  (ir2_fri_grid)
    -- docs (history) PROOF-ECONOMICS.md 2c  (the table reproduced below)
"""

import math

# ---------------------------------------------------------------------------
# 1. The QUERY ledgers (verbatim from fri_params_soundness_budget.rs:45-53)
# ---------------------------------------------------------------------------
# NAMING: these are COLUMNS, not soundness. `johnson_query_bits` is the m -> infinity
# idealisation and drops eps_C (section 1b below). The old name `proven_bits` asserted
# something this arithmetic does not establish.

FIELD_CAP_BITS = 124          # degree-4 BabyBear extension, plonky3_prover.rs:63/:113
FLOOR_BITS = 128              # CONJECTURED_FLOOR_BITS, fri_params_soundness_budget.rs:42
BABYBEAR_P = 2013265921       # 2^31 - 2^27 + 1; FriLedger.ledgerP
DEPLOYED_EXT_DEG = 4          # BinomialExtensionField<BabyBear, 4>
DEPLOYED_LOG_D0 = 12          # the measured grid's 2^6-row trace x blowup -- a FIXTURE, not
                              # a production height. eps_C moves ~2 bits per trace doubling.

def conjectured_bits(lb, q, pow):        # capacity / list-decoding-to-(1-rho) -- REFUTED
    return q * lb + pow

def johnson_query_bits(lb, q, pow):      # Johnson QUERY column, integer floor. Drops eps_C.
    return q * lb // 2 + pow

def effective_bits(raw):                 # min(query ledger, field cap) -- still not soundness
    return min(raw, FIELD_CAP_BITS)

# ---------------------------------------------------------------------------
# 1b. eps_C -- the commit-phase term, mirroring Lean's FriLedger.friCommitLedger
# ---------------------------------------------------------------------------
# Every rounding rounds eps_C UP (=> bits DOWN), never the reverse: a soundness ledger must
# not round in the flattering direction. The `2^8` common denominator keeps the numerator
# division-free, exactly as the Lean does.

def _ceil_div(a, b):
    return 0 if b == 0 else (a + b - 1) // b

def _nat_log2(n):                        # Lean's Nat.log2: greatest k with 2^k <= n, 0 for n<2
    return n.bit_length() - 1 if n >= 2 else 0

def eps_c_num_den(lb, mla, ext_deg, log_d0, bciks_m):
    """(numerator, denominator) with eps_C <= num/den. BCIKS20 Thm 8.3, m = bciks_m >= 3."""
    arity = 2 ** mla
    d0 = 2 ** log_d0
    sum_l = _ceil_div(log_d0 - lb, mla) * arity      # sum_i l^(i) = rounds * arity
    two_m_p1 = 2 * bciks_m + 1
    # rho = 2^-lb, so 1/(2*rho^{3/2}) = 2^(3lb/2 - 1) and 1/sqrt(rho) = 2^(lb/2);
    # (m+1/2)^7 = (2m+1)^7 / 2^7. Half-integer exponents round UP (odd lb only).
    a1 = two_m_p1 ** 7 * (d0 * d0) * 2 ** _ceil_div(3 * lb, 2)
    a2 = two_m_p1 * (d0 + 1) * sum_l * 2 ** _ceil_div(lb, 2)
    return a1 + 2 ** 8 * a2, 2 ** 8 * BABYBEAR_P ** ext_deg

def commit_bits(lb, mla=3, ext_deg=DEPLOYED_EXT_DEG, log_d0=DEPLOYED_LOG_D0, bciks_m=7):
    """-log2(eps_C), floored. Mirrors FriLedger.friCommitLedger's `commitBits` EXACTLY."""
    num, den = eps_c_num_den(lb, mla, ext_deg, log_d0, bciks_m)
    return _nat_log2((den - 1) // num)

def _neg_log2_eps_c(lb, mla, ext_deg, log_d0, bciks_m):   # unfloored, for eq.(20)
    num, den = eps_c_num_den(lb, mla, ext_deg, log_d0, bciks_m)
    return -math.log2(num / den)

def eq20_bits(lb, q, pow, ext_deg=DEPLOYED_EXT_DEG, log_d0=DEPLOYED_LOG_D0, mla=3):
    """ethSTARK eq.(20): lambda >= min{-log2 eps_C, zeta - s*log2 alpha} - 1, best over m>=3.

    The caller picks m; the ledger reports terms. This is the COMPOSITE of the two BCIKS20
    terms -- it is NOT the per-fold column, and the two are never multiplied together.
    """
    best = 0.0
    for m in range(3, 257):
        alpha = math.sqrt(2.0 ** -lb) * (1 + 1 / (2 * m))
        both = min(_neg_log2_eps_c(lb, mla, ext_deg, log_d0, m),
                   q * (-math.log2(alpha)) + pow)
        best = max(best, both)
    return best - 1

def eq20_ceiling(lb=6, ext_deg=DEPLOYED_EXT_DEG, log_d0=DEPLOYED_LOG_D0, mla=3):
    """The ceiling as q, pow -> infinity: eps_C contains NEITHER, so it caps everything."""
    return max(_neg_log2_eps_c(lb, mla, ext_deg, log_d0, m) for m in range(3, 257)) - 1

# ---------------------------------------------------------------------------
# 2. Cost model, ANCHORED to the measured ir2_fri_grid (effect_vm_ir2_size_measure.rs:370-402)
# ---------------------------------------------------------------------------
#
# Measured points (nibble range table), bytes / prove ms / verify ms / conj bits:
MEASURED = {
    #(lb, q): (bytes,  prove_ms, verify_ms)
    (3, 38): (198_758, 29, 6.9),   # 194.1 KiB
    (4, 29): (163_533, 20, 6.2),   # 159.7 KiB
    (5, 23): (139_366, 32, 4.9),   # 136.1 KiB
    (6, 19): (123_293, 58, 4.1),   # 120.4 KiB  == deployed ir2_config
    (7, 17): (116_736, 101, 4.0),  # 114.0 KiB
    (8, 15): (109_056, 183, 3.6),  # 106.5 KiB
}
# (KiB * 1024 reconstructed; the fitted model below reproduces all six to < 0.5 KiB.)

# --- Proof size ---
# The proof is: fixed OOD opened_values (~20.0 KiB) + tiny commitments (~81 B) + the FRI
# opening = q openings, each opening a row of every committed matrix PLUS its Merkle path.
# Merkle path length ~ log2(domain) = log2(trace_height) + log_blowup, so per-query bytes
# grow LINEARLY in log_blowup. Fitting the two extreme anchors (3,38) and (6,19):
#   per_query(lb) = 3971 + 239 * lb        bytes
#   size(lb,q)    = 20_561 + q * per_query(lb)
FIXED_BYTES = 20_561            # opened_values (~20.0 KiB, PROOF-ECONOMICS 2b) + commitments (81 B)
PQ_INTERCEPT = 3971
PQ_SLOPE = 239                 # bytes / query / blowup-step (the lengthening Merkle path)

def proof_bytes(lb, q):
    return FIXED_BYTES + q * (PQ_INTERCEPT + PQ_SLOPE * lb)

# --- Prover cost ---
# LDE dominates once blowup climbs: committed-column LDE is ~ 2^log_blowup * trace, so prove
# time roughly doubles per blowup step (measured 20->32->58->101->183 ms for lb 4..8). Queries
# only touch the opening phase (negligible prover cost). Reported as the measured anchor when
# available, else a 2^lb scaling off the (6,*) anchor.
def prove_ms(lb, q):
    if (lb, q) in MEASURED:
        return MEASURED[(lb, q)][1]
    # scale off lb=6 anchor (58 ms) by the LDE doubling; queries ~free on the prover
    return 58 * (2 ** (lb - 6))

# --- Verifier cost ---
# Falls with query count (fewer openings to check) + slightly with fewer FRI folding rounds.
# Measured 6.9->3.6 ms across q 38..15. Linear-in-q fit off the anchors.
def verify_ms(lb, q):
    if (lb, q) in MEASURED:
        return MEASURED[(lb, q)][2]
    # ~0.145 ms/query + ~1.6 ms floor (fit of the six anchors)
    return round(1.6 + 0.145 * q, 1)

def kib(b):
    return b / 1024.0

# Self-check: reproduce the measured grid.
def _selfcheck():
    print("== model vs measured (ir2_fri_grid) ==")
    print(f"{'(lb,q)':>8} {'model KiB':>10} {'meas KiB':>9} {'err KiB':>8}  cap  jQry")
    for (lb, q), (b, _, _) in MEASURED.items():
        m = proof_bytes(lb, q)
        print(f"{str((lb,q)):>8} {kib(m):>10.1f} {kib(b):>9.1f} {kib(m)-kib(b):>8.2f}"
              f"  {conjectured_bits(lb,q,16):>4} {johnson_query_bits(lb,q,16):>5}")

# ---------------------------------------------------------------------------
# 3. Grid search: min-cost config meeting a bit target on a chosen ledger
# ---------------------------------------------------------------------------
# lb range: lb >= 3 is the floor (degree-8 batch S-box quotient needs 8 chunks; points below
#   lb=3 are unprovable with the inline x^7 gadget -- effect_vm_ir2_size_measure.rs:351-353).
#   lb <= 8 in the measured grid; we extrapolate to lb=10 to show the (exploding-prover) tail.
LB_RANGE = range(3, 11)

def min_queries_for(target, ledger, lb, pow):
    """Fewest queries so `ledger(lb,q,pow) >= target`."""
    for q in range(1, 400):
        if ledger(lb, q, pow) >= target:
            return q
    return None

def frontier(target, ledger, pow=16, lb_range=LB_RANGE):
    rows = []
    for lb in lb_range:
        q = min_queries_for(target, ledger, lb, pow)
        if q is None:
            continue
        rows.append({
            "lb": lb, "q": q, "pow": pow,
            "conj": conjectured_bits(lb, q, pow),
            "jqry": johnson_query_bits(lb, q, pow),
            "bytes": proof_bytes(lb, q),
            "prove_ms": prove_ms(lb, q),
            "verify_ms": verify_ms(lb, q),
        })
    return rows

def print_frontier(title, rows, deployed=None):
    print(f"\n== {title} ==")
    hdr = f"{'lb':>3} {'q':>4} {'pow':>4} | {'proof KiB':>9} {'prove ms':>9} {'verify ms':>9} | {'cap':>4} {'jQry':>6}"
    print(hdr); print("-" * len(hdr))
    for r in rows:
        mark = ""
        if deployed and (r["lb"], r["q"], r["pow"]) == deployed:
            mark = "  <- deployed"
        print(f"{r['lb']:>3} {r['q']:>4} {r['pow']:>4} | {kib(r['bytes']):>9.1f} "
              f"{r['prove_ms']:>9.0f} {r['verify_ms']:>9.1f} | {r['conj']:>4} {r['jqry']:>6}{mark}")

if __name__ == "__main__":
    _selfcheck()

    print("\n### DEPLOYED ir2_config: lb=6 q=19 pow=16")
    print(f"  conjectured = 6*19+16 = {conjectured_bits(6,19,16)} bits "
          f"(effective min(.,124) = {effective_bits(conjectured_bits(6,19,16))})")
    print(f"  johnson qry = 6*19//2+16 = {johnson_query_bits(6,19,16)} bits  "
          f"<-- the QUERY COLUMN. Drops eps_C; not 'the proven soundness'.")
    print(f"  commit eps_C= {commit_bits(6)} bits at |D0|=2^12  <-- BINDS. No q/pow enters it.")
    print(f"  eq.(20)     = {eq20_bits(6,19,16):.2f} bits  <-- the composite of the two above")
    print(f"  proof size  = {kib(proof_bytes(6,19)):.1f} KiB (measured 120.4)")
    print("  (per-fold is a SEPARATE column -- 109 at the deployed arity 8, at 96.9% farness.")
    print("   Lean FriLedger/FriJohnsonRadiusGap own it. Never multiply the columns together.)")

    # --- Frontier 1: CONJECTURED ledger, 128-bit query-term target (the enforced floor) ---
    f_conj = frontier(FLOOR_BITS, conjectured_bits, pow=16)
    print_frontier("FRONTIER A -- conjectured ledger, target 128 (enforced floor), pow=16",
                   f_conj, deployed=(6, 19, 16))

    # --- Frontier 1b: against the ~124 FIELD CAP instead of the 128 query-term floor ---
    f_cap = frontier(FIELD_CAP_BITS, conjectured_bits, pow=16)
    print_frontier("FRONTIER A' -- conjectured, target 124 (the actual field cap), pow=16",
                   f_cap, deployed=(6, 19, 16))

    # --- Frontier 2: the Johnson QUERY column at 128. WITHDRAWN as a security frontier:
    #     these rows reach 128 on the query column ONLY. eps_C caps the extDeg-4 eq.(20)
    #     composite at ~77.98 regardless of q -- see the eps_C block below.
    f_jqry = frontier(FLOOR_BITS, johnson_query_bits, pow=16)
    print_frontier("FRONTIER B -- Johnson QUERY column at 128 (NOT a proven-128; see eps_C below)",
                   f_jqry)
    print("  ^ WITHDRAWN as a security claim. This is the query column reaching 128; the")
    print("    eq.(20) composite at extDeg 4 cannot exceed ~77.98 at ANY q. Real rows below.")

    # --- Lever: raise PoW to trim queries at the deployed blowup (lb=6) ---
    print("\n== LEVER: query-PoW trades grind for queries at lb=6 (conjectured target 128) ==")
    print(f"{'pow':>4} {'min q':>6} {'proof KiB':>10} {'conj':>5}  (grind ~2^pow hashes, one-time)")
    for pow in (16, 18, 20, 22, 24):
        q = min_queries_for(FLOOR_BITS, conjectured_bits, 6, pow)
        print(f"{pow:>4} {q:>6} {kib(proof_bytes(6,q)):>10.1f} {conjectured_bits(6,q,pow):>5}")

    # --- eps_C: the term the Johnson column drops, and the ceiling it imposes ---
    print("\n== eps_C -- the commit-phase column the Johnson query ledger DROPS ==")
    print("   (BCIKS20 Thm 8.3; mirrors Lean FriLedger.friCommitLedger)")
    print(f"{'config':>42} {'commitBits':>11}")
    for label, kw in [
        ("deployed wrap, |D0|=2^12, m=7", dict(log_d0=12, bciks_m=7)),
        ("same config, |D0|=2^20, m=7", dict(log_d0=20, bciks_m=7)),
        ("same config, |D0|=2^12, m=3 (eps_C-optimal)", dict(log_d0=12, bciks_m=3)),
    ]:
        print(f"{label:>42} {commit_bits(6, **kw):>11}")
    print("   eps_C depends on the TRACE HEIGHT (not an FRI knob): ~2 bits per doubling.")
    print("   eps_C contains NO num_queries and NO query_pow_bits -- so queries cannot pass it:")
    for q, pw in [(19, 16), (25, 16), (200, 27)]:
        print(f"     q={q:>3} pow={pw:>2} -> commitBits {commit_bits(6):>3} "
              f"(unchanged), johnson query column {johnson_query_bits(6,q,pw):>3}")

    print("\n== THE CEILING: ethSTARK eq.(20) composite, min{-log2 eps_C, zeta - s*log2 alpha} - 1 ==")
    print(f"  deployed (lb=6, q=19, pow=16, extDeg=4, |D0|=2^12): "
          f"{eq20_bits(6, 19, 16):.2f}  <-- NOT the Johnson column's {johnson_query_bits(6,19,16)}")
    print(f"  ceiling at extDeg=4 with q, pow UNBOUNDED:          {eq20_ceiling(6):.2f}")
    print("  => a proven 128 is UNREACHABLE at extDeg 4 at any q. The withdrawn 'FRONTIER B'")
    print("     rows (lb=7 q=32 / lb=8 q=28 at '128') were the Johnson QUERY column, not this.")
    print("  !! The ceiling assumes commit_proof_of_work_bits = 0 -- true of every shipped dregg")
    print("     config, but NOT absolute. plonky3 has a SECOND, commit-phase PoW knob (fri/src/")
    print("     config.rs:18, distinct from query_proof_of_work_bits at :20), ground per fold")
    print("     round before beta (prover.rs:224) and omitted from its own")
    print("     conjectured_soundness_bits (:42-44). It grinds the very terms eps_C bounds.")
    print("     UNPRICED here and unmodeled by this script. See FRI-BOTH-WIN-LEVERS.md 4.4.")

    # --- The one lever on the ceiling: the extension degree ---
    print("\n== LEVER: extension degree -- the ONLY knob on the ceiling (eps_C ~ 1/p^extDeg) ==")
    print(f"{'extDeg':>7} {'eq20 ceiling':>13} {'gain':>7}  plonky3 (pinned rev 82cfad73)")
    p3 = {4: "supported (DEPLOYED)", 5: "supported; EXT_TWO_ADICITY 27",
          6: "PANICS -- binomial_mul matches 4/5/8 only", 8: "supported; EXT_TWO_ADICITY 30"}
    prev = None
    for ed in (4, 5, 6, 8):
        c = eq20_ceiling(6, ext_deg=ed)
        gain = f"{c-prev:+.2f}" if prev is not None else "--"
        prev = c
        print(f"{ed:>7} {c:>13.2f} {gain:>7}  {p3[ed]}")
    print(f"  log2(p) = {math.log2(BABYBEAR_P):.2f} bits per degree, exactly (eps_C ~ 1/|F|).")
    print("  degree 5 does NOT reach 128 (~108.88 ceiling). degree 6 would, but plonky3 panics.")
    print("  degree 8 does, and beats 5 on two-adicity. Its arithmetic cost is UNMEASURED here.")

    print("\n== The field alone is not enough: BOTH columns must move ==")
    print(f"  deployed knobs (6,19,pow16) at extDeg 4 / 5 / 8:  "
          f"{eq20_bits(6,19,16,ext_deg=4):.2f} / {eq20_bits(6,19,16,ext_deg=5):.2f} / "
          f"{eq20_bits(6,19,16,ext_deg=8):.2f}")
    print("  -- the QUERY column binds once the field is bigger. Fewest queries clearing an")
    print("     eq.(20) composite of 128 at extDeg=8, pow=16, |D0|=2^12:")
    print(f"{'lb':>4} {'q':>5} {'proof KiB':>10} {'eq20':>8}")
    for lb in LB_RANGE:
        for q in range(1, 600):
            if eq20_bits(lb, q, 16, ext_deg=8) >= 128:
                print(f"{lb:>4} {q:>5} {kib(proof_bytes(lb,q)):>10.1f} "
                      f"{eq20_bits(lb,q,16,ext_deg=8):>8.2f}")
                break
    print("  ~2x the deployed 120.4 KiB. And every row is pinned to the 2^12 FIXTURE: a")
    print("  production-height trace moves them all. The distribution is unmeasured.")
    print("\n  BCHKS25 (ECCC TR25-169) improves the O(n^2) -> O(n) exception count that makes")
    print("  eps_C's |D0|^2 bind. It is a NAMED, UNINSTANTIATED lever: it restates no full FRI")
    print("  soundness theorem, and nobody has computed the ceiling it would give here. It")
    print("  backs NO number printed above -- these are BCIKS20's.")
