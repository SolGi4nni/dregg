# Private-Market Dev-Plan — dark-pool + fhegg + MPC synthesis — 2026-07-25

Synthesis of the three scope docs (FHEGG-MARKET-SCOPE, MPC-STACK-SCOPE, + the dark-pool findings below). One
coherent story across all three.

## THE UNIFIED VERDICT
**PARTIAL, not scaffold — and unusually honest about where it stops.** Across dark-pool/fhegg/MPC the CRYPTO is
GENUINELY REAL (fhe.rs BFV + tfhe-rs threshold FHE with a Lean-pinned 80-bit smudge floor, real Chou-Orlandi OT,
real Yao garbling, real JF-DKG with complaints/QUAL/slashing, real Bulletproofs/Schnorr/Ristretto, real TLSNotary
2PC), and the Lean is non-vacuous + sorry-free (the market accounting core — conservation, mint-safety, fairness,
optimality — PROVEN over ℤ; the mint-wraparound hazard caught head-on by field_gate_refines_nat_eq +
mintWraparound_at_babyBear). **The gaps are STRUCTURAL and CONSISTENT, not fakery:** (a) single-process — no
distributed committee, no network transport; (b) plaintext custody / the shielded pool has NEVER held value;
(c) toy params (10-bit reserves, t≈2²⁰); (d) **UNROUTED Lean proofs** — the deployed Rust accepts a forged root
while the proven Lean fix sits *beside* it unrouted; (e) undischarged floors (FRI/STARK, DLog-Shor for binding).

**The dominant remaining work is WIRING proven Lean objects into the deployed path + building the distributed
committee perimeter + choosing params — NOT (mostly) new cryptography.** Plus a genuine-research tail
(house-blind proving, malicious triples, PQ integrity, the discharged floor) that must NEVER be claimed done.

## ⚡ THE STRATEGIC FORK (the headline — ember-gated)
Every DEX in the field is stuck on a trusted party (Penumbra/Shutter = a threshold COMMITTEE; CoW/dYdX = a
solver/proposer). Two of the three in-tree private-market paths carry the committee (Path 1 directly; Path 2's
output-boundary MPC needs it to decrypt). **ONLY Path 3 — Market/ShieldedClearing.lean "decrypts NOTHING" over
shielded commitments — structurally ELIMINATES the decryption committee**, at the cost of the undischarged
FRI/STARK floor.
→ **The fork:** build the honest distributed threshold committee (Paths 1/2, MPC-heavy, keeps a trusted-ish
committee) **OR** discharge the FRI floor and lean on Path 3 (ZK-heavy, committee-FREE — structurally beats every
competitor). MPC is the shared floor under 1&2; AVOIDABLE on Path 3.
**RECOMMENDATION:** lean Path 3 as the strategic bet — a committee-free private DEX is the differentiator, and the
session's FRI-correlated-agreement work ([[project-fri-correlated-agreement-formalization]]) is already engineered
to ONE elementary theorem (not open research), so discharging the FRI floor unlocks Path 3 AND validates the apex.
Keep Paths 1/2 (the distributed committee — real crypto, needs only the ops perimeter) as the pragmatic fallback.

## DARK-POOL specifics (the third map)
TWO "pools" + a front-end, NOT wired: (1) the shielded STARK pool (turn/src/executor/apply.rs::apply_shielded_transfer +
circuit-prove/shielded/* — hides value, has NEVER held value, unreachable from any surface); (2) the
dark-pool/dark-AMM market (dreggnet-market/ — moves REAL value but plaintext-custodied, single-process, no
servers); (3) the DrEX terminal (separate product). A production dark pool needs #1's value-hiding + #2's real
custody UNIFIED — today you get one property from each. There IS a real proven constant-product CFMM
(DarkAmmPrivateSwap.lean admitted_post_preserves_product) — but VERIFY-not-COMPUTE (the curve division priced in
plaintext), no slippage theorem, 10-bit toy scale. Closest-to-real slice: dark_pool_offering +
private_bfv_attested_clearing binding + quorum.rs t-of-n certificate = ONE integration campaign from a real
no-single-viewer value-holding dark pool at demo scale.

## RANKED CROSS-CUTTING NEEDS (shared blockers first)
1. [BLOCKS, EMBER-GATED (VK-affecting)] **Value on-ramp + shielded custody** — Effect::Shield/Deshield (none
   exist), the L0.5 ENCODING DECISION, corrected committed GATE-4 append so value ENTERS the accumulator. Unifies
   the two pools. (project-shielded-apex-campaign: L1/L4 blocked behind this.)
2. [BLOCKS, AUTONOMOUS-ish — ROUTING] **Pin merkle_root to the committed accumulator (#15 theft) on the DEPLOYED
   path.** merkle_root is a bare prover-supplied u32 (action.rs:1017) → #15 theft lands + AccumulatorSound FALSE.
   The Lean fix is PROVEN (ShieldedSpendDescriptor.root_is_pinned, emitted_accept_is_committed) — the work is
   EMITTING the descriptor + feeding pi[committed_root] + retiring the wire field. DELETES the Rust-authored
   spend_circuit.rs debt (house law #1) = the twin-deletion method for the shielded pool. (Gated only if it
   depends on the L0.5 encoding — confirm.)
3. [BLOCKS] **Distributed no-single-viewer threshold committee** — turn fhegg's single-process "simulated
   ceremony" into n independently-hosted custodians w/ authenticated transport (the crypto is FINISHED; it's
   ops + protocol wiring). THE shared blocker under Paths 1+2. + migrate the dark-AMM onto quorum.rs t-of-n.
4. [BLOCKS→HARDENING] **Same-opening binding** — the ring↔wide-join is a ~31-bit legacy_binding felt, NOT a
   cryptographic same-opening (falsifier ShieldedWideJoinPin.dark_value_decouples landed). Wire the PROVED-BUT-DEAD
   same-opening gadget (Market.EmitSameOpeningGadget, zero Rust consumers, highest security-per-effort). + malicious
   DKG (range proofs) + retire the trusted-dealer GF(256) turn-privacy scheme (used LIVE by intent/src/trustless.rs).
5. [HARDENING / RESEARCH] Malicious-secure MPC (authenticated garbling, real triples, malicious OT), network
   transport, PQ value-commitment cutover (#17, ember-gated), and DISCHARGE THE FRI FLOOR (the Path-3 unlock +
   the whole-apex validator). Never claim the floor done ("verifies on a box" ≠ verified).

## DRIVE SPLIT (autonomous vs ember-gated)
- AUTONOMOUS (I can drive, mostly ROUTING proven objects + non-VK crypto): the DrEX-clear regression (dispatched);
  the #15 merkle_root descriptor-routing IF not L0.5-gated (deletes Rust-AIR debt); wiring the dead same-opening
  gadget; the MPC malicious-security builds that don't touch VK. CAVEAT: most touch fhegg/dreggnet-market
  (edit-excluded) or circuit-prove/turn — coordinate; several are the shielded-apex campaign's active lane.
- EMBER-GATED: the strategic PATH FORK (1/2 vs 3); the L0.5 on-ramp ENCODING; the #17 PQ cutover; anything
  VK-affecting or federation-re-keying. These are architecture commitments, not lane work.

Anchors: dreggnet-market/src/{dark_pool_offering,private_bfv_attested_clearing}.rs, fhegg-fhe/src/{threshold/quorum,mpc}.rs,
turn/src/executor/apply.rs:1713, turn/src/action.rs:1017, metatheory/{Dregg2/Circuit/Shielded*,Market/*}.lean,
docs/{DESIGN-shielded-dark-value-campaign, deos/{FHEGG-MALICE-ROADMAP-2026-07-25,DREX-TIER-STATUS-2026-07-24}}.md.
