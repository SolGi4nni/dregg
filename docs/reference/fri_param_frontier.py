#!/usr/bin/env python3
"""FRI / circuit parameter security-vs-cost model + efficient-frontier grid search.

READ-ONLY MODEL. Does not touch the deployed config. This is the map ember uses to
choose a leaner FRI config later; it changes nothing.

Ground truth (file:line, all in /Users/ember/dev/breadstuffs):

  Soundness formulas (the checked-in budget gate):
    conjectured (capacity)  = num_queries * log_blowup       + pow_bits
    proven      (Johnson)   = num_queries * log_blowup // 2   + pow_bits   (integer floor)
    -- circuit/tests/fri_params_soundness_budget.rs:45-53  (CONJECTURED_FLOOR_BITS = 128, :42)
  Challenge field cap:  degree-4 BabyBear extension ~ 2^124
    -- circuit/src/plonky3_prover.rs:63 (BinomialExtensionField<BabyBear,4>), :113 comment
    Both ledgers are additionally capped by min(., 124) and the Poseidon2 commitment hash.

  Deployed IR-v2 knobs (log_blowup=6, log_final_poly=0, max_log_arity=3, q=19, pow=16):
    -- circuit/src/descriptor_ir2.rs:5382-5386  (IR2_FRI_* consts)
  Deployed v1 knobs (log_blowup=3, q=38, pow=16):
    -- circuit/src/plonky3_prover.rs:98-102  (PROD_FRI_* consts)

  Measured IR-v2 cost grid (release, --test-threads=1), the SAME real transfer proven at
  every (log_blowup, num_queries) size-parity point, 4-bit-nibble range table:
    -- circuit/tests/effect_vm_ir2_size_measure.rs:355-403  (ir2_fri_grid)
    -- docs (history) PROOF-ECONOMICS.md 2c  (the table reproduced below)
"""

# ---------------------------------------------------------------------------
# 1. Soundness ledgers (verbatim from fri_params_soundness_budget.rs:45-53)
# ---------------------------------------------------------------------------

FIELD_CAP_BITS = 124          # degree-4 BabyBear extension, plonky3_prover.rs:63/:113
FLOOR_BITS = 128              # CONJECTURED_FLOOR_BITS, fri_params_soundness_budget.rs:42

def conjectured_bits(lb, q, pow):        # capacity / list-decoding-to-(1-rho)
    return q * lb + pow

def proven_bits(lb, q, pow):             # Johnson / list-decoding-to-sqrt(rho), integer floor
    return q * lb // 2 + pow

def effective_bits(raw):                 # the honest headline is min(ledger, field cap)
    return min(raw, FIELD_CAP_BITS)

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
    print(f"{'(lb,q)':>8} {'model KiB':>10} {'meas KiB':>9} {'err KiB':>8}  conj proven")
    for (lb, q), (b, _, _) in MEASURED.items():
        m = proof_bytes(lb, q)
        print(f"{str((lb,q)):>8} {kib(m):>10.1f} {kib(b):>9.1f} {kib(m)-kib(b):>8.2f}"
              f"  {conjectured_bits(lb,q,16):>4} {proven_bits(lb,q,16):>5}")

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
            "proven": proven_bits(lb, q, pow),
            "bytes": proof_bytes(lb, q),
            "prove_ms": prove_ms(lb, q),
            "verify_ms": verify_ms(lb, q),
        })
    return rows

def print_frontier(title, rows, deployed=None):
    print(f"\n== {title} ==")
    hdr = f"{'lb':>3} {'q':>4} {'pow':>4} | {'proof KiB':>9} {'prove ms':>9} {'verify ms':>9} | {'conj':>4} {'proven':>6}"
    print(hdr); print("-" * len(hdr))
    for r in rows:
        mark = ""
        if deployed and (r["lb"], r["q"], r["pow"]) == deployed:
            mark = "  <- deployed"
        print(f"{r['lb']:>3} {r['q']:>4} {r['pow']:>4} | {kib(r['bytes']):>9.1f} "
              f"{r['prove_ms']:>9.0f} {r['verify_ms']:>9.1f} | {r['conj']:>4} {r['proven']:>6}{mark}")

if __name__ == "__main__":
    _selfcheck()

    print("\n### DEPLOYED ir2_config: lb=6 q=19 pow=16")
    print(f"  conjectured = 6*19+16 = {conjectured_bits(6,19,16)} bits "
          f"(effective min(.,124) = {effective_bits(conjectured_bits(6,19,16))})")
    print(f"  proven      = 6*19//2+16 = {proven_bits(6,19,16)} bits  "
          f"<-- WELL under the 128 target; the 128-claim rests on the CONJECTURED ledger")
    print(f"  proof size  = {kib(proof_bytes(6,19)):.1f} KiB (measured 120.4)")

    # --- Frontier 1: CONJECTURED ledger, 128-bit query-term target (the enforced floor) ---
    f_conj = frontier(FLOOR_BITS, conjectured_bits, pow=16)
    print_frontier("FRONTIER A -- conjectured ledger, target 128 (enforced floor), pow=16",
                   f_conj, deployed=(6, 19, 16))

    # --- Frontier 1b: against the ~124 FIELD CAP instead of the 128 query-term floor ---
    f_cap = frontier(FIELD_CAP_BITS, conjectured_bits, pow=16)
    print_frontier("FRONTIER A' -- conjectured, target 124 (the actual field cap), pow=16",
                   f_cap, deployed=(6, 19, 16))

    # --- Frontier 2: PROVEN (Johnson) ledger, 128-bit target ---
    f_prov = frontier(FLOOR_BITS, proven_bits, pow=16)
    print_frontier("FRONTIER B -- PROVEN (Johnson) ledger, target 128, pow=16", f_prov)

    # --- Lever: raise PoW to trim queries at the deployed blowup (lb=6) ---
    print("\n== LEVER: query-PoW trades grind for queries at lb=6 (conjectured target 128) ==")
    print(f"{'pow':>4} {'min q':>6} {'proof KiB':>10} {'conj':>5}  (grind ~2^pow hashes, one-time)")
    for pow in (16, 18, 20, 22, 24):
        q = min_queries_for(FLOOR_BITS, conjectured_bits, 6, pow)
        print(f"{pow:>4} {q:>6} {kib(proof_bytes(6,q)):>10.1f} {conjectured_bits(6,q,pow):>5}")

    # --- What a tighter PROVEN bound buys: if proven could reach the full lb rate ---
    print("\n== IF the proven ledger were raised toward capacity (lb instead of lb/2) ==")
    print("  Deployed (6,19) proven would jump 73 -> 130 with NO config change: the 128 claim")
    print("  becomes PROVEN, not conjectured. Holding proven-128 as the target, the leanest")
    print("  config collapses from FRONTIER B back onto FRONTIER A:")
    b_now = min(r["bytes"] for r in f_prov)
    a_now = min(r["bytes"] for r in f_conj if r["conj"] >= 128)
    print(f"    proven-128 today (Johnson):  {kib(b_now):.1f} KiB minimum")
    print(f"    proven-128 at capacity rate: {kib(a_now):.1f} KiB minimum  "
          f"(~{100*(1-a_now/b_now):.0f}% smaller, same PROVEN security)")
