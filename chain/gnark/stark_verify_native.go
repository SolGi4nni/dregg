// NATIVE-HASH batch-STARK algebra layer — the layer ON TOP OF the FRI core
// (VerifyFriNative, fri_verify_native.go) that verifies the STARK side of the
// shrink proof: the quotient identity at the out-of-domain point zeta, with
// the constraints evaluated from the OPENED trace/preprocessed/permutation
// values, plus the global LogUp cumulative-sum balance.
//
// Ground truth (pinned Plonky3 rev 82cfad73, ~/.cargo/git/checkouts/
// plonky3-7d8a3b21a665a86f/82cfad7):
//
//   - batch-stark/src/verifier/mod.rs:507-621 (verify_batch, per-instance
//     constraint check): recompose quotient(zeta) from the opened chunks
//     (uni-stark/src/verifier.rs:59-96 recompose_quotient_from_chunks),
//     recompose the permutation columns from base-flattened openings
//     (mod.rs:543-556), then verify_constraints_with_lookups
//     (batch-stark/src/verifier/data.rs:53-105): evaluate the AIR + LogUp
//     constraints at zeta with the folder rule acc = acc*alpha + C
//     (lookup/src/folder.rs:174-181) and check
//     folded * Z_H(zeta)^-1 == quotient  (data.rs:100).
//   - commit/src/domain.rs:157-271 (TwoAdicMultiplicativeCoset):
//     natural domain shift = ONE (fri/src/two_adic_pcs.rs:285);
//     Z_{sH}(x) = (x/s)^|H| - 1 (domain.rs:251-253); selectors_at_point
//     (domain.rs:262-271); create_disjoint_domain shift = s*GENERATOR
//     (domain.rs:180-193); split_domains chunk j shift = s*w^j with
//     w = two_adic_generator(full log) (domain.rs:199-211).
//   - lookup/src/logup.rs:158-265 (LogUpGadget::eval_update): per global
//     lookup, THREE constraints in order —
//     is_first_row * s_local                                  (logup.rs:226)
//     is_transition * ((s_next - s_local)*denom - numer)      (logup.rs:245)
//     is_last_row  * ((cum   - s_local)*denom - numer)        (logup.rs:250)
//     with combined = Horner-in-beta over the element tuple
//     (logup.rs:88, fold acc = elt + acc*beta) and, for a single-tuple
//     lookup, denom = alpha_ch - combined, numer = multiplicity
//     (logup.rs:122-145 with n = 1). Filtered constraints multiply by the
//     selector (air/src/filtered.rs:78-85).
//   - batch-stark/src/transcript.rs:74-102: global lookups on the same bus
//     SHARE one (alpha_ch, beta_ch) challenge pair.
//   - batch-stark/src/verifier/mod.rs:623-643: the global cumulative sums of
//     each bus must sum to zero (logup.rs:314-324 verify_global_sum).
//
// HONEST SCOPE — what this file verifies of the REAL shrink proof, and what
// remains (the named residual before the full verify -> Groth16 wrap):
//
//	VERIFIED IN-CIRCUIT on real data (stark_algebra_real_fixture_test.go):
//	the quotient recomposition + quotient identity for ALL 6 instances
//	(Const, Public, Alu: 146 constraints, Poseidon2: 337, Recompose,
//	ExposeClaim: 100) with the FULL constraint evaluation (AIR + LogUp at
//	zeta) by the GENERIC symbolic interpreter (stark_constraint_interp.go)
//	over the constraint DAGs emitted from the AIRs themselves
//	(plonky3-recursion/circuit-prover/tests/emit_shrink_symbolic.rs — no
//	hand-encoding); the ExposeClaim instance additionally binds the shrink
//	proof's 25 PUBLIC claim lanes (pv == v_0, bus-bound) — the settlement
//	statement channel; plus the global WitnessChecks cumulative-sum balance
//	across all 53 lookups. The three simple instances are cross-checked
//	host-side against an independent hand-derived LogUp path (differential
//	only — the former in-circuit hand MODE, whose heavy instances were
//	witnessed and therefore vacuously satisfied, was REMOVED).
//
//	SEAM CLOSED (stark_open_input.go, verified on the real proof in
//	apex_shrink_open_input_test.go): the OPENED VALUES this layer consumes
//	are transcript-bound AND commitment-bound — the open_input layer
//	Merkle-opens the input batches against the trace/quotient/preprocessed/
//	permutation commitments, derives the FRI reduced openings from those
//	opened columns (the alpha-combination, verifier.rs:524 at the pinned
//	rev), and asserts them equal to the fold seeds VerifyFriNative walks.
//	The assembled circuit (SettlementCircuit) is therefore
//	commitments → (Merkle open + α-reduce) → FRI low-degree, with the same
//	opened-at-zeta values feeding the constraint/quotient identity here.
//
//	NAMED REMAINING (assembly, not soundness): bake the shape/constraint-DAG
//	as VK constants, size + compile the Groth16 wrap, and pin the
//	DreggSettlement.sol VK. Cryptographic assumption carried (not a seam):
//	FRI soundness itself — StarkSound half (i), the deep low-degree
//	extraction — also carried on the Lean side.
package friverifier

import (
	"errors"
	"math/big"

	"github.com/consensys/gnark/constraint/solver"
	"github.com/consensys/gnark/frontend"
)

// ============================================================================
// Pinned BabyBear two-adic ground truth
// ============================================================================

// bbTwoAdicGenerators[bits] is the generator of the order-2^bits subgroup —
// the EXACT table plonky3 uses (baby-bear/src/baby_bear.rs:46-51,
// TWO_ADIC_GENERATORS; monty-31/src/monty_31.rs:668 two_adic_generator
// indexes this table). The selectors and coset shifts below must match these
// values bit-for-bit or the quotient identity diverges from the prover.
var bbTwoAdicGenerators = [28]uint32{
	0x1, 0x78000000, 0x67055c21, 0x5ee99486, 0xbb4c4e4, 0x2d4cc4da,
	0x669d6090, 0x17b56c64, 0x67456167, 0x688442f9, 0x145e952d, 0x4fe61226,
	0x4c734715, 0x11c33e2a, 0x62c3d2b1, 0x77cad399, 0x54c131f4, 0x4cabd6a6,
	0x5cf5713f, 0x3e9430e8, 0xba067a3, 0x18adc27d, 0x21fd55bc, 0x4b859b3d,
	0x3bd57996, 0x4483d85a, 0x3a26eef8, 0x1a427a41,
}

// bbGenerator is the BabyBear multiplicative generator g = 31
// (baby-bear/src/baby_bear.rs:29 MONTY_GEN), the shift of every disjoint
// quotient domain (domain.rs:192: shift * Val::GENERATOR from shift ONE).
const bbGenerator = uint32(31)

func bbTwoAdicGeneratorRef(bits int) uint32 {
	if bits < 0 || bits >= len(bbTwoAdicGenerators) {
		panic("bbTwoAdicGeneratorRef: bits out of the BabyBear two-adicity range")
	}
	return bbTwoAdicGenerators[bits]
}

// ============================================================================
// Extension-field gadget extensions (BBExt helpers the algebra layer needs)
// ============================================================================

func init() {
	solver.RegisterHint(bbExtInvHint)
}

// bbExtInvHint computes the quartic-extension inverse host-side. UNTRUSTED:
// ExtInv constrains out * in == 1.
func bbExtInvHint(_ *big.Int, inputs, outputs []*big.Int) error {
	if len(inputs) != 4 || len(outputs) != 4 {
		return errors.New("bbExtInvHint: expected 4 inputs, 4 outputs")
	}
	var a bbExtRef
	for i := range a {
		if !inputs[i].IsUint64() || inputs[i].Uint64() >= BabyBearP {
			return errors.New("bbExtInvHint: input not a canonical BabyBear residue")
		}
		a[i] = uint32(inputs[i].Uint64())
	}
	inv, err := bbExtInvRef(a)
	if err != nil {
		return err
	}
	for i := range inv {
		outputs[i].SetUint64(uint64(inv[i]))
	}
	return nil
}

// ExtInv returns a^-1 in BabyBear[X]/(X^4-11) via a hinted witness pinned by
// the constraint a * a^-1 == 1. Fail-closed: a == 0 has no satisfying
// witness (0 * anything != 1).
func (bb *BBApi) ExtInv(a BBExt) BBExt {
	res, err := bb.api.Compiler().NewHint(bbExtInvHint, 4, a[0], a[1], a[2], a[3])
	if err != nil {
		panic(err)
	}
	inv := BBExt{res[0], res[1], res[2], res[3]}
	bb.ExtAssertIsCanonical(inv)
	bb.ExtAssertIsEqual(bb.ExtMul(a, inv), BBExt{1, 0, 0, 0})
	return inv
}

// ExtMulBaseConst returns c·a for a fixed canonical base-field constant c.
func (bb *BBApi) ExtMulBaseConst(c uint32, a BBExt) BBExt {
	var r BBExt
	for i := range r {
		r[i] = bb.MulConst(c, a[i])
	}
	return r
}

// ExtExpPow2 returns a^(2^k) by k squarings.
func (bb *BBApi) ExtExpPow2(a BBExt, k int) BBExt {
	r := a
	for i := 0; i < k; i++ {
		r = bb.ExtMul(r, r)
	}
	return r
}

// ExtFromBasisCoefficients recomposes an extension element from DIMENSION
// opened coefficients that are THEMSELVES extension elements — the verifier's
// from_ext_basis_coefficients (batch-stark verifier/mod.rs:543-556 for the
// permutation columns; uni-stark verifier.rs:92 for the quotient chunks):
//
//	s = c0 + c1·X + c2·X² + c3·X³   in BabyBear[X]/(X^4 - 11).
//
// Multiplication by the basis monomial X is coordinate rotation with the
// binomial wrap (X^4 = W = 11), so this is a pure linear combination:
//
//	s[0] = c0[0] + W·(c1[3] + c2[2] + c3[1])
//	s[1] = c0[1] +    c1[0] + W·(c2[3] + c3[2])
//	s[2] = c0[2] +    c1[1] +    c2[0] + W·c3[3]
//	s[3] = c0[3] +    c1[2] +    c2[1] +    c3[0]
//
// Bound: each term < 2^31 (canonical) or 11·2^31; the widest sum is
// < 34·2^31 < 2^37, so one ReduceBounded(·, 37) per coordinate.
func (bb *BBApi) ExtFromBasisCoefficients(c [4]BBExt) BBExt {
	api := bb.api
	w := func(v frontend.Variable) frontend.Variable { return api.Mul(BBExtW, v) }
	return BBExt{
		bb.ReduceBounded(api.Add(c[0][0], w(c[1][3]), w(c[2][2]), w(c[3][1])), 37),
		bb.ReduceBounded(api.Add(c[0][1], c[1][0], w(c[2][3]), w(c[3][2])), 37),
		bb.ReduceBounded(api.Add(c[0][2], c[1][1], c[2][0], w(c[3][3])), 37),
		bb.ReduceBounded(api.Add(c[0][3], c[1][2], c[2][1], c[3][0]), 37),
	}
}

// ============================================================================
// Instance shapes + the opened-values layout
// ============================================================================

// StarkInstanceShape is one batch-STARK instance's structural shape — the
// VK-side data that determines how the flat opened-values stream (the values
// pcs.verify observes, two_adic_pcs.rs:687-694) slices into per-instance
// trace/quotient/preprocessed/permutation openings at zeta.
type StarkInstanceShape struct {
	// log2 of the trace degree (is_zk = 0: ext == base degree bits).
	DegreeBits int
	// Main trace width (opened at zeta; also at zeta_next iff HasTraceNext).
	Width int
	// Preprocessed width (0 = no preprocessed matrix).
	PreWidth int
	// Number of quotient chunks (each opened as DIMENSION = 4 EF values).
	NumQuotientChunks int
	// Number of LogUp lookups = permutation aux columns. The flattened
	// permutation matrix has width 4*NumLookups (verifier mod.rs:524-541).
	NumLookups int
	// Number of GLOBAL lookups (== NumLookups in the shrink scope: every
	// lookup rides the WitnessChecks bus; no locals).
	NumGlobalLookups int
	// Number of table PUBLIC VALUES (base-field lanes). Zero for every shrink
	// table except expose_claim (the 25-lane settlement claim channel).
	NumPublicValues int
	// Whether trace_next / preprocessed_next are opened
	// (main_next_row_columns / preprocessed_next_row_columns nonempty).
	HasTraceNext bool
	HasPreNext   bool
}

// efSpan is a [off, off+len) window into the flat EF opened-values stream.
type efSpan struct{ off, len int }

// starkInstanceSpans locates one instance's openings inside the flat stream.
type starkInstanceSpans struct {
	traceLocal, traceNext efSpan
	quotientChunks        []efSpan // one span of len 4 per chunk
	preLocal, preNext     efSpan
	permLocal, permNext   efSpan
	cumSums               efSpan // into the separate cumulative-sums stream
}

// buildStarkOpenedSpans walks the PCS round structure in the EXACT order
// verify_batch builds coms_to_verify (batch-stark verifier/mod.rs:302-499)
// and the exporter mirrors (apex_shrink_gnark_export.rs Phase A) — trace
// round, quotient round, preprocessed round, permutation round; within each
// round instance order; within each matrix point order (zeta then zeta_next)
// — and returns per-instance spans plus the required total EF count.
// Fail-closed: the caller must check totalEF against the actual stream.
func buildStarkOpenedSpans(shapes []StarkInstanceShape) (spans []starkInstanceSpans, totalEF int) {
	spans = make([]starkInstanceSpans, len(shapes))
	off := 0
	take := func(n int) efSpan {
		s := efSpan{off, n}
		off += n
		return s
	}
	// Trace round.
	for i, sh := range shapes {
		spans[i].traceLocal = take(sh.Width)
		if sh.HasTraceNext {
			spans[i].traceNext = take(sh.Width)
		}
	}
	// Quotient round (chunks flattened across instances, mod.rs:388-406).
	for i, sh := range shapes {
		for c := 0; c < sh.NumQuotientChunks; c++ {
			spans[i].quotientChunks = append(spans[i].quotientChunks, take(4))
		}
	}
	// Preprocessed round (one matrix per instance with PreWidth > 0,
	// mod.rs:410-472; matrix_to_instance is instance-ascending here —
	// validated against the real proof by the identity checks).
	for i, sh := range shapes {
		if sh.PreWidth > 0 {
			spans[i].preLocal = take(sh.PreWidth)
			if sh.HasPreNext {
				spans[i].preNext = take(sh.PreWidth)
			}
		}
	}
	// Permutation round (instances with lookups, local then next,
	// mod.rs:474-499; flattened width = 4*NumLookups).
	for i, sh := range shapes {
		if sh.NumLookups > 0 {
			spans[i].permLocal = take(4 * sh.NumLookups)
			spans[i].permNext = take(4 * sh.NumLookups)
		}
	}
	totalEF = off
	// Cumulative sums are a separate stream (global_lookup_data flattened in
	// instance order, transcript.rs:114-116).
	cum := 0
	for i, sh := range shapes {
		spans[i].cumSums = efSpan{cum, sh.NumGlobalLookups}
		cum += sh.NumGlobalLookups
	}
	return spans, totalEF
}

func totalGlobalLookups(shapes []StarkInstanceShape) int {
	n := 0
	for _, sh := range shapes {
		n += sh.NumGlobalLookups
	}
	return n
}

// ============================================================================
// Quotient-domain constants (host-side, structural)
// ============================================================================

// quotientDomainConsts carries the per-instance base-field constants of the
// quotient chunk domains: chunk j is the coset (g·w^j)·H with |H| = 2^db,
// w = two_adic_generator(db + log2(nChunks)) (domain.rs:180-211).
type quotientDomainConsts struct {
	// kPow[j] = shift_j^(-2^db): Z_j(zeta) = zeta^(2^db)·kPow[j] - 1.
	kPow []uint32
	// zpsConst[i] = prod_{j != i} Z_j(shift_i)^(-1) — the Lagrange
	// normalization at the chunk's first point (verifier.rs:67-83).
	zpsConst []uint32
}

func shrinkQuotientDomainConsts(db, nChunks int) quotientDomainConsts {
	logChunks := 0
	for 1<<logChunks < nChunks {
		logChunks++
	}
	if 1<<logChunks != nChunks {
		panic("shrinkQuotientDomainConsts: nChunks must be a power of two")
	}
	w := bbTwoAdicGeneratorRef(db + logChunks)
	shifts := make([]uint32, nChunks)
	for j := range shifts {
		shifts[j] = bbMulRef(bbGenerator, bbPowRef(w, uint64(j)))
	}
	pow2db := uint64(1) << uint(db)
	c := quotientDomainConsts{
		kPow:     make([]uint32, nChunks),
		zpsConst: make([]uint32, nChunks),
	}
	for j := range shifts {
		c.kPow[j] = bbInvRef(bbPowRef(shifts[j], pow2db))
	}
	for i := range shifts {
		prod := uint32(1)
		for j := range shifts {
			if j == i {
				continue
			}
			// Z_j(shift_i) = (shift_i / shift_j)^(2^db) - 1.
			zj := bbSubRef(bbPowRef(bbMulRef(shifts[i], bbInvRef(shifts[j])), pow2db), 1)
			prod = bbMulRef(prod, bbInvRef(zj))
		}
		c.zpsConst[i] = prod
	}
	return c
}

// ============================================================================
// Selectors, quotient recomposition, LogUp folding (circuit)
// ============================================================================

// starkSelectorsNative are the Lagrange selectors at zeta over the trace
// domain (shift ONE, size 2^db) — domain.rs:262-271 with unshifted = zeta.
type starkSelectorsNative struct {
	zetaPow2Db   BBExt // zeta^(2^db), shared with the quotient-domain Z_j's
	zH           BBExt // zeta^(2^db) - 1
	isFirstRow   BBExt // zH / (zeta - 1)
	isLastRow    BBExt // zH / (zeta - g^-1)
	isTransition BBExt // zeta - g^-1
}

func computeStarkSelectorsNative(bb *BBApi, zeta BBExt, db int) starkSelectorsNative {
	one := BBExt{1, 0, 0, 0}
	gInv := bbInvRef(bbTwoAdicGeneratorRef(db))
	e := bb.ExtExpPow2(zeta, db)
	zh := bb.ExtSub(e, one)
	trans := bb.ExtSub(zeta, BBExt{gInv, 0, 0, 0})
	return starkSelectorsNative{
		zetaPow2Db:   e,
		zH:           zh,
		isFirstRow:   bb.ExtMul(zh, bb.ExtInv(bb.ExtSub(zeta, one))),
		isLastRow:    bb.ExtMul(zh, bb.ExtInv(trans)),
		isTransition: trans,
	}
}

// recomposeQuotientNative rebuilds quotient(zeta) from the opened chunks —
// recompose_quotient_from_chunks (uni-stark verifier.rs:59-96): each chunk's
// 4 opened EF values recompose on the basis, weighted by the Lagrange factor
// zps[i] = prod_{j != i} Z_j(zeta)/Z_j(first_i).
func recomposeQuotientNative(
	bb *BBApi, zetaPow2Db BBExt, chunks [][4]BBExt, dc quotientDomainConsts,
) BBExt {
	if len(chunks) != len(dc.kPow) {
		panic("recomposeQuotientNative: chunk count does not match domain constants")
	}
	one := BBExt{1, 0, 0, 0}
	zAt := make([]BBExt, len(chunks)) // Z_j(zeta) = E·kPow[j] - 1
	for j := range chunks {
		zAt[j] = bb.ExtSub(bb.ExtMulBaseConst(dc.kPow[j], zetaPow2Db), one)
	}
	quotient := BBExt{0, 0, 0, 0}
	for i := range chunks {
		zps := BBExt{dc.zpsConst[i], 0, 0, 0}
		for j := range chunks {
			if j != i {
				zps = bb.ExtMul(zps, zAt[j])
			}
		}
		quotient = bb.ExtAdd(quotient, bb.ExtMul(zps, bb.ExtFromBasisCoefficients(chunks[i])))
	}
	return quotient
}

// NOTE: the former in-circuit hand-derived LogUp evaluator
// (evalWitnessBusFoldedNative) was REMOVED together with the `sym == nil`
// verification mode — see the VerifyShrinkStarkAlgebra doc. Its host twin
// (evalWitnessBusFoldedRef, stark_verify_native_ref.go) survives as a pure
// DIFFERENTIAL cross-check against the symbolic interpreter.

// ============================================================================
// The shrink-shape orchestrator
// ============================================================================

// witnessBusSpec pins where a simple instance's lookup reads its multiplicity
// and witness index in the preprocessed row (column_layout.rs:23-27
// WitnessLookupPrepCols = [multiplicity, witness_idx] for Const/Public;
// recompose_columns.rs:9-13 RecomposePrepLaneCols = [output_idx, out_mult]).
type witnessBusSpec struct {
	multPreCol, idxPreCol int
}

// ShrinkNumInstances is the pinned instance count of the EXPOSED shrink proof
// (shrink_apex_to_outer_exposed): 3 primitives + Poseidon2-W16 + Recompose +
// ExposeClaim.
const ShrinkNumInstances = 6

// VkSpineLanes is the pinned VK-SPINE lane count: the turn-chain root exposes
// commit(L.cap8 || L.vk_spine8 || R.cap8 || R.vk_spine8) — the circuit
// identity of every leaf and aggregation node folded beneath it — as lanes
// 25..33 of its own claim, immediately after the 25-lane settlement segment
// (ivc_turn_chain.rs VK_SPINE_WIDTH / SEG_VK_SPINE_FIRST).
//
// It is the half of the claim the apex RecursionVk fingerprint does NOT
// cover: that fingerprint is deliberately content-independent and does not
// move when a child circuit is substituted, so the apex-VK pin alone never
// certified WHAT was folded. The SettlementCircuit pins these lanes too.
const VkSpineLanes = 8

// ApexClaimLanes is what a turn-chain root actually publishes:
// [settlement segment(25) || vk_spine(8)] (ivc_turn_chain.rs SEG_SPINE_WIDTH).
//
// NOT the same number as NumPublicInputs. The settlement STATEMENT is 25; the
// apex CLAIM is 33. Everything on this path read them as one number until
// 2026-08-08 and therefore read the SPINE where it meant to read the apex VK
// core.
const ApexClaimLanes = NumPublicInputs + VkSpineLanes

// ApexVkLanes is the pinned apex VK-core lane count: the apex's preprocessed
// commitment (its VK-identity core, one BabyBear Poseidon2-W16 Merkle root =
// 8 felts) rides as lanes 33..41 of the shrink proof's expose_claim channel —
// AFTER the apex's own ApexClaimLanes
// (shrink_apex_to_outer_exposed: in-circuit `pin_preprocessed_commit` +
// re-exposure). The SettlementCircuit pins these lanes to the DEPLOYED dregg
// apex's commitment as baked constants (the apex-VK pin, tooth 2).
const ApexVkLanes = 8

// ExposedShrinkClaimLanes is the full expose_claim width of the EXPOSED
// shrink proof: [segment(25) || vk_spine(8) || apex VK core(8)] = 41.
const ExposedShrinkClaimLanes = ApexClaimLanes + ApexVkLanes

// ShrinkVkShape is the pinned VK-side shape of the 6-instance EXPOSED shrink
// proof (batch_stark_prover.rs:276 NUM_PRIMITIVE_TABLES = 3: Const, Public,
// Alu (circuit/src/ops/op.rs:233-238); non-primitives registered Poseidon2,
// Recompose, ExposeClaim — apex_shrink.rs:222-232 + the exposed-claim hook of
// apex_shrink_gnark_export.rs shrink_apex_to_outer_exposed). Lookup counts
// from the AIR sources: Const/Public/Recompose 1 each; Alu 4 lanes·4 +
// 2·(k_max-1) = 18 at lanes=4, k_max=2 (alu_air.rs:294-299 total_width
// 4·16+12 = 76, preprocessed 4·13+7 = 59 pin those knobs); Poseidon2
// WIDTH_EXT + RATE_EXT + 1 = 7 (poseidon2-circuit-air/src/air.rs:1484-1532
// at WIDTH_EXT=4, RATE_EXT=2); ExposeClaim ONE WitnessChecks receive per
// lane = 41 (expose_claim_air.rs: the 25 settlement lanes ++ the 8 VK-spine
// lanes ++ the 8 apex VK-core lanes). Instances with an eval that reads
// next rows open trace_next / preprocessed_next (BaseAir defaults;
// Const/Public/Recompose/ExposeClaim override to none).
type ShrinkVkShape struct {
	NumLookups      [ShrinkNumInstances]int
	NumPublicValues [ShrinkNumInstances]int
	TraceNext       [ShrinkNumInstances]bool
	PreNext         [ShrinkNumInstances]bool
	// SimpleSpecs maps the fully-encoded instances (zero AIR constraints,
	// one WitnessChecks lookup) to their preprocessed column spec — used by
	// the host-side DIFFERENTIAL cross-check only (the circuit path is the
	// symbolic interpreter, always).
	SimpleSpecs map[int]witnessBusSpec
	// ClaimInstance is the expose_claim instance (the settlement claim
	// channel); ClaimLen its pinned public-value count = the 25 settlement
	// lanes ++ the 8 VK-spine lanes ++ the 8 apex VK-core lanes.
	ClaimInstance, ClaimLen int
}

// ShrinkVk is THE pinned shape for the current (exposed) shrink circuit.
var ShrinkVk = ShrinkVkShape{
	NumLookups:      [ShrinkNumInstances]int{1, 1, 18, 7, 1, ExposedShrinkClaimLanes},
	NumPublicValues: [ShrinkNumInstances]int{0, 0, 0, 0, 0, ExposedShrinkClaimLanes},
	TraceNext:       [ShrinkNumInstances]bool{false, false, true, true, false, false},
	PreNext:         [ShrinkNumInstances]bool{false, false, true, true, false, false},
	SimpleSpecs: map[int]witnessBusSpec{
		0: {multPreCol: 0, idxPreCol: 1}, // Const  (WitnessLookupPrepCols)
		1: {multPreCol: 0, idxPreCol: 1}, // Public (WitnessLookupPrepCols)
		4: {multPreCol: 1, idxPreCol: 0}, // Recompose (RecomposePrepLaneCols)
	},
	ClaimInstance: 5,
	// 25 settlement lanes + 8 VK-spine lanes + 8 apex VK-core lanes.
	ClaimLen: ExposedShrinkClaimLanes,
}

// ShrinkStarkChallenges are the transcript challenges the algebra layer
// consumes; the caller binds them to the live Fiat-Shamir replay.
type ShrinkStarkChallenges struct {
	PermAlpha BBExt // WitnessChecks bus alpha (transcript.rs:92-99)
	PermBeta  BBExt // WitnessChecks bus beta
	Alpha     BBExt // constraint-folding alpha (mod.rs:290)
	Zeta      BBExt // the OOD point (mod.rs:300)
}

// VerifyShrinkStarkAlgebra constrains the batch-STARK algebra layer of the
// shrink proof over the FLAT opened-values-at-zeta stream (the exact values
// pcs.verify observes into the transcript, in observation order), the flat
// cumulative-sums stream, and the per-instance table PUBLIC VALUES (the
// expose_claim settlement claim channel):
//
//  1. slices the streams per instance by the pinned shape;
//  2. per instance: recomposes quotient(zeta) from the opened chunks,
//     evaluates ALL its constraints IN-CIRCUIT by the generic symbolic
//     interpreter over the emitted AIR DAGs (stark_constraint_interp.go) —
//     with the instance's public values substituted into the DAG's `pub`
//     leaves (the ExposeClaimAir pv == v_0 binding rides here) — and asserts
//     the quotient identity  folded == quotient · Z_H(zeta);
//  3. asserts the global WitnessChecks cumulative-sum balance
//     (sum of all sums == 0, mod.rs:623-643).
//
// The symbolic interpreter is the ONLY constraint-evaluation mode. The former
// `sym == nil` "hand" mode was REMOVED: it evaluated only the three simple
// instances and took the heavy instances' (Alu, Poseidon2) folded values as
// WITNESSES, making the identity for those two hold by construction — a
// vacuous check an audit flagged as a trap ("5/5 instances" that a trace
// tamper passes). The hand-derived LogUp evaluation survives host-side as a
// DIFFERENTIAL cross-check only (evalWitnessBusFoldedRef).
//
// Precondition: openedEF, cumSums and pubVals coordinates are already
// canonicity-bound (they are when they flow through the challenger replay —
// ObserveBabyBear asserts canonicity).
func VerifyShrinkStarkAlgebra(
	bb *BBApi,
	shapes []StarkInstanceShape,
	openedEF []BBExt,
	cumSums []BBExt,
	pubVals [][]frontend.Variable,
	ch ShrinkStarkChallenges,
	sym *SymbolicConstraints,
) {
	if len(shapes) != ShrinkNumInstances {
		panic("VerifyShrinkStarkAlgebra: shrink scope is exactly 6 instances")
	}
	if sym == nil {
		panic("VerifyShrinkStarkAlgebra: the emitted symbolic constraints are REQUIRED " +
			"(no witnessed-folded fallback exists)")
	}
	if len(sym.Instances) != len(shapes) {
		panic("VerifyShrinkStarkAlgebra: symbolic constraint file instance count mismatch")
	}
	if len(pubVals) != len(shapes) {
		panic("VerifyShrinkStarkAlgebra: public-value stream instance count mismatch")
	}
	spans, totalEF := buildStarkOpenedSpans(shapes)
	if len(openedEF) != totalEF {
		panic("VerifyShrinkStarkAlgebra: opened-values stream length does not match the pinned shape")
	}
	if len(cumSums) != totalGlobalLookups(shapes) {
		panic("VerifyShrinkStarkAlgebra: cumulative-sums stream length mismatch")
	}

	slice := func(s efSpan) []BBExt { return openedEF[s.off : s.off+s.len] }

	for i, sh := range shapes {
		sp := spans[i]
		sel := computeStarkSelectorsNative(bb, ch.Zeta, sh.DegreeBits)

		// Quotient recomposition.
		chunks := make([][4]BBExt, len(sp.quotientChunks))
		for c, qs := range sp.quotientChunks {
			copy(chunks[c][:], slice(qs))
		}
		quotient := recomposeQuotientNative(bb, sel.zetaPow2Db, chunks,
			shrinkQuotientDomainConsts(sh.DegreeBits, sh.NumQuotientChunks))

		// Folded constraints at zeta — the symbolic interpreter over the
		// emitted DAG, public values substituted.
		inst := &sym.Instances[i]
		if inst.Width != sh.Width || inst.PreWidth != sh.PreWidth ||
			inst.NumLookups != sh.NumLookups || inst.NumPublicValues != sh.NumPublicValues {
			panic("VerifyShrinkStarkAlgebra: emitted constraint shape drifted from the proof shape")
		}
		if len(pubVals[i]) != sh.NumPublicValues {
			panic("VerifyShrinkStarkAlgebra: public-value lane count drifted from the pinned shape")
		}
		folded := evalSymbolicFoldedNative(bb, inst,
			shrinkSymInputsNative(bb, sh, sp, slice, cumSums, pubVals[i], ch, sel), ch.Alpha)

		// The quotient identity (data.rs:100, multiplied through by Z_H):
		// folded == quotient(zeta) · Z_H(zeta).
		bb.ExtAssertIsEqual(folded, bb.ExtMul(quotient, sel.zH))
	}

	// Global WitnessChecks balance: all cumulative sums add to zero.
	sum := BBExt{0, 0, 0, 0}
	for _, cs := range cumSums {
		sum = bb.ExtAdd(sum, cs)
	}
	bb.ExtAssertIsEqual(sum, BBExt{0, 0, 0, 0})
}

// shrinkSymInputsNative assembles one instance's symbolic-eval inputs from
// its spans: recomposed permutation columns (mod.rs:543-556), the repeated
// bus challenge pair (transcript.rs:86-101: all shrink lookups share the
// WitnessChecks (alpha, beta)), the instance's cumulative sums, and nil for
// unopened next rows (the verifier's zero substitution, mod.rs:563-581).
func shrinkSymInputsNative(
	bb *BBApi,
	sh StarkInstanceShape,
	sp starkInstanceSpans,
	slice func(efSpan) []BBExt,
	cumSums []BBExt,
	pubVals []frontend.Variable,
	ch ShrinkStarkChallenges,
	sel starkSelectorsNative,
) symEvalInputsNative {
	recompose := func(flat []BBExt) []BBExt {
		out := make([]BBExt, len(flat)/4)
		for c := range out {
			out[c] = bb.ExtFromBasisCoefficients([4]BBExt(flat[4*c : 4*c+4]))
		}
		return out
	}
	in := symEvalInputsNative{
		TraceLocal: slice(sp.traceLocal),
		PreLocal:   slice(sp.preLocal),
		PermLocal:  recompose(slice(sp.permLocal)),
		PermNext:   recompose(slice(sp.permNext)),
		PermValues: cumSums[sp.cumSums.off : sp.cumSums.off+sp.cumSums.len],
		Sel:        sel,
	}
	if sh.NumPublicValues > 0 {
		in.PublicValues = make([]BBExt, len(pubVals))
		for k, v := range pubVals {
			// Base-field public value lifted to the extension: [v, 0, 0, 0].
			in.PublicValues[k] = BBExt{v, 0, 0, 0}
		}
	}
	if sh.HasTraceNext {
		in.TraceNext = slice(sp.traceNext)
	}
	if sh.HasPreNext {
		in.PreNext = slice(sp.preNext)
	}
	in.Challenges = make([]BBExt, 2*sh.NumLookups)
	for l := 0; l < sh.NumLookups; l++ {
		in.Challenges[2*l] = ch.PermAlpha
		in.Challenges[2*l+1] = ch.PermBeta
	}
	return in
}
