// THE RECYCLE-CLEARING CIRCUIT — a Groth16-provable statement that a claimed
// clearing tuple (uniform price, bought, spent, per-ask fills) IS the correct
// order-invariant uniform-price marginal-fill clearing of a committed sealed
// book under a committed budget.
//
// This is the ARCHITECTURAL lever for `RecycleFlywheel.finalizeRecycle`
// (contracts/flywheel/RecycleFlywheel.sol): today the contract re-runs the
// clearing walk on-chain (measured ~10.7k gas per ask, cold), so the fairness
// tax grows O(n) with the book. With this circuit the operator clears
// OFF-CHAIN (native, microseconds) and the contract verifies ONE Groth16 proof
// (measured 466k gas for the settlement-shaped verifier in
// test/DreggSettlementRealProof.t.sol) — flat in n. Crossover ≈ 44 asks; at
// n=1000 the walk costs ~11.1M gas vs ~0.9M for the proof path. It ALSO
// closes the §4.3.1 NAMED WELD (the receipt today does not bind the clearing
// to an in-circuit price proof — this circuit IS that binding).
//
// ## The statement (public inputs)
//
//   ArrivalFoldHi/Lo — the keccak256 chain over the book in ARRIVAL order,
//       byte-layout-identical to the contract's fold
//       (`keccak256(abi.encodePacked(prev32, seller20, price32, qty32))`), so
//       the on-chain commitment accumulated at reveal time binds the SAME
//       object the circuit clears. No re-authored mirror: the preimage bytes
//       are the contract's.
//   Budget — the buy-side wei budget (the enforced committed split's buy leg).
//   ClearingPrice, Bought, Spent — the claimed uniform-price clearing tuple.
//   Fills[i] — the per-ask fills in SORTED order (prototype resolution; the
//       production shape folds these into a fillsRoot for O(1) publics and
//       per-seller Merkle settles — named below).
//
// ## Why it is SOUND (the three teeth)
//
//  1. BINDING: the circuit re-derives the arrival-order keccak fold from its
//     witness book and asserts equality with the public commitment — a proof
//     over any other book breaks keccak collision resistance.
//  2. PERMUTATION (no-drop/no-insert, the `_assertPermutation` twin): the
//     sorted witness book is bound to the arrival book by a grand-product
//     multiset argument at a Fiat–Shamir challenge derived (in-circuit, via
//     keccak) from BOTH folds — both multisets are committed before the
//     challenge exists, so cooking either after the fact is infeasible
//     (Schwartz–Zippel over ~2^128-sized challenges; the α-compression of
//     (seller, price, qty) triples collides only with negligible probability).
//  3. THE WALK: ascending order is asserted pairwise; the marginal-fill walk
//     is replicated constraint-for-constraint (integer division via a
//     witnessed quotient/remainder with `r < price`; fills capped by qty and
//     by `budget/price − bought`; zero-price asks take no fill — exactly
//     `_runAskClearing`), and the outputs are asserted equal to the public
//     claim. Ranges mirror the contract's DOCUMENTED packed bounds
//     (price < 2^128, qty < 2^96) — the .sol `ValueOutOfRange` bounds are the
//     circuit's range assumptions, made real on-chain.
//
// ## Honest scope (prototype resolution — named, not hidden)
//
//   - FIXED SIZE: one circuit instance per book size N (Groth16 needs a
//     per-circuit setup). Production options: a max-N circuit with in-circuit
//     length selection, a small ladder of sizes (16/64/256/1024), or routing
//     through the dregg STARK→shrink→BN254 wrap (no per-statement ceremony).
//   - Fills are public inputs (O(n) publics, ~6k gas each on-chain); the
//     production shape is a fillsRoot public + Merkle-proof settles.
//   - The dev Groth16 setup here is the same UNSAFE single-party ceremony as
//     the settlement fixture flow — a production key needs a real ceremony
//     (or the STARK wrap, which has none).
//   - The flywheel contract's proof-verifying entry point
//     (`finalizeRecycleWithProof`) is NOT yet built; the measured on-chain
//     verifier cost is taken from the real settlement verifier replay.
package friverifier

import (
	"math/big"

	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/std/hash/sha3"
	"github.com/consensys/gnark/std/math/bits"
	"github.com/consensys/gnark/std/math/cmp"
	"github.com/consensys/gnark/std/math/uints"
	"github.com/consensys/gnark/constraint/solver"
)

func init() {
	solver.RegisterHint(divRemHint)
}

// divRemHint witnesses (q, r) with a = q·b + r, r < b (b > 0). The circuit
// CONSTRAINS both equations — the hint is untrusted search, translation-
// validation style.
func divRemHint(_ *big.Int, inputs []*big.Int, outputs []*big.Int) error {
	outputs[0].DivMod(inputs[0], inputs[1], outputs[1])
	return nil
}

// RecycleClearingCircuit proves one uniform-price clearing. Slice lengths fix
// the book size N at compile time.
type RecycleClearingCircuit struct {
	// ── Public statement ──
	ArrivalFoldHi frontend.Variable `gnark:",public"` // keccak fold, top 16 bytes
	ArrivalFoldLo frontend.Variable `gnark:",public"` // keccak fold, low 16 bytes
	Budget        frontend.Variable `gnark:",public"`
	ClearingPrice frontend.Variable `gnark:",public"`
	Bought        frontend.Variable `gnark:",public"`
	Spent         frontend.Variable `gnark:",public"`
	Fills         []frontend.Variable `gnark:",public"` // per SORTED slot

	// ── Witness: the book in arrival (reveal) order… ──
	ASeller []frontend.Variable // < 2^160
	APrice  []frontend.Variable // < 2^128 (the .sol packed bound)
	AQty    []frontend.Variable // < 2^96  (the .sol packed bound)
	// ── …and in ascending-price (clearing) order. ──
	SSeller []frontend.Variable
	SPrice  []frontend.Variable
	SQty    []frontend.Variable
}

// bytesBE decomposes v into n big-endian bytes (range-constraining v < 2^(8n)).
func bytesBE(api frontend.API, bf *uints.BinaryField[uints.U64], v frontend.Variable, n int) []uints.U8 {
	bs := bits.ToBinary(api, v, bits.WithNbDigits(n*8))
	out := make([]uints.U8, n)
	for j := 0; j < n; j++ {
		b := frontend.Variable(0)
		for k := 0; k < 8; k++ {
			b = api.Add(b, api.Mul(bs[(n-1-j)*8+k], 1<<uint(k)))
		}
		out[j] = bf.ByteValueOf(b)
	}
	return out
}

// foldStep = keccak256(prev32 ‖ seller20 ‖ price32 ‖ qty32) — byte-identical
// to the contract's `keccak256(abi.encodePacked(bCommit, seller, price, qty))`.
func foldStep(api frontend.API, bf *uints.BinaryField[uints.U64], prev []uints.U8,
	seller, price, qty frontend.Variable) []uints.U8 {
	h, err := sha3.NewLegacyKeccak256(api)
	if err != nil {
		panic(err)
	}
	h.Write(prev)
	h.Write(bytesBE(api, bf, seller, 20))
	h.Write(bytesBE(api, bf, price, 32))
	h.Write(bytesBE(api, bf, qty, 32))
	return h.Sum()
}

// pack16 packs 16 bytes (big-endian) into one field element.
func pack16(api frontend.API, b []uints.U8) frontend.Variable {
	acc := frontend.Variable(0)
	for j := 0; j < 16; j++ {
		acc = api.Mul(acc, 256)
		acc = api.Add(acc, b[j].Val)
	}
	return acc
}

func (c *RecycleClearingCircuit) Define(api frontend.API) error {
	n := len(APanic(c))
	bf, err := uints.New[uints.U64](api)
	if err != nil {
		return err
	}

	zero32 := make([]uints.U8, 32)
	for i := range zero32 {
		zero32[i] = bf.ByteValueOf(0)
	}

	// (1) BINDING — the arrival-order fold equals the public commitment.
	// (bytesBE inside foldStep also range-constrains every seller/price/qty.)
	foldA := zero32
	for i := 0; i < n; i++ {
		foldA = foldStep(api, bf, foldA, c.ASeller[i], c.APrice[i], c.AQty[i])
	}
	api.AssertIsEqual(pack16(api, foldA[:16]), c.ArrivalFoldHi)
	api.AssertIsEqual(pack16(api, foldA[16:]), c.ArrivalFoldLo)

	// The sorted-order fold — the SAME layout the deployed contract emits as
	// `bookCommit` (walk order == ascending order). Committed before the
	// multiset challenge is derived.
	foldS := zero32
	for i := 0; i < n; i++ {
		foldS = foldStep(api, bf, foldS, c.SSeller[i], c.SPrice[i], c.SQty[i])
	}

	// (2) PERMUTATION — Fiat–Shamir: γ, α from keccak over BOTH folds.
	hc, err := sha3.NewLegacyKeccak256(api)
	if err != nil {
		return err
	}
	hc.Write(foldA)
	hc.Write(foldS)
	chal := hc.Sum()
	gamma := pack16(api, chal[:16])
	alpha := pack16(api, chal[16:])

	prodA := frontend.Variable(1)
	prodS := frontend.Variable(1)
	alpha2 := api.Mul(alpha, alpha)
	for i := 0; i < n; i++ {
		eA := api.Add(c.ASeller[i], api.Mul(alpha, c.APrice[i]), api.Mul(alpha2, c.AQty[i]))
		eS := api.Add(c.SSeller[i], api.Mul(alpha, c.SPrice[i]), api.Mul(alpha2, c.SQty[i]))
		prodA = api.Mul(prodA, api.Add(eA, gamma))
		prodS = api.Mul(prodS, api.Add(eS, gamma))
	}
	api.AssertIsEqual(prodA, prodS)

	// (3) THE WALK — `_runAskClearing`, constraint for constraint.
	// Values are bounded: price < 2^128, qty < 2^96, and Budget is
	// range-checked to < 2^160 (far above any wei amount; keeps comparators
	// sound). bought ≤ Σqty < 2^96·n.
	bits.ToBinary(api, c.Budget, bits.WithNbDigits(160))
	cmp160 := cmp.NewBoundedComparator(api, new(big.Int).Lsh(big.NewInt(1), 161), false)

	bought := frontend.Variable(0)
	clearingPrice := frontend.Variable(0)
	prevPrice := frontend.Variable(0)
	for i := 0; i < n; i++ {
		price := c.SPrice[i]
		qty := c.SQty[i]

		// NotSortedAscending: prevPrice ≤ price.
		cmp160.AssertIsLessEq(prevPrice, price)
		prevPrice = price

		// affordable = budget / price (integer), witnessed and CONSTRAINED;
		// price == 0 ⇒ the ask is skipped exactly as on-chain.
		isZero := api.IsZero(price)
		divisor := api.Add(price, isZero) // ≥ 1 always
		qr, err := api.Compiler().NewHint(divRemHint, 2, c.Budget, divisor)
		if err != nil {
			return err
		}
		q, r := qr[0], qr[1]
		api.AssertIsEqual(c.Budget, api.Add(api.Mul(q, divisor), r))
		bits.ToBinary(api, q, bits.WithNbDigits(160)) // q ≤ budget < 2^160
		cmp160.AssertIsLess(r, divisor)               // r < divisor

		// room = max(affordable − bought, 0); fill = min(qty, room); skip if
		// price == 0.
		hasRoom := cmp160.IsLess(bought, q) // bought < affordable
		room := api.Select(hasRoom, api.Sub(q, bought), 0)
		qtyLess := cmp160.IsLess(qty, room)
		fillIfRoom := api.Select(qtyLess, qty, room)
		fill := api.Mul(fillIfRoom, api.Sub(1, isZero))

		// The public per-ask fill IS the walk's fill.
		api.AssertIsEqual(c.Fills[i], fill)

		bought = api.Add(bought, fill)
		// clearingPrice = price of the LAST ask with fill > 0.
		filled := api.Sub(1, api.IsZero(fill))
		clearingPrice = api.Select(filled, price, clearingPrice)
	}

	api.AssertIsEqual(c.Bought, bought)
	api.AssertIsEqual(c.ClearingPrice, clearingPrice)
	api.AssertIsEqual(c.Spent, api.Mul(clearingPrice, bought))
	return nil
}

// APanic returns the arrival-seller slice after asserting the circuit's slice
// lengths agree (a mis-sized template is a programming error, caught at
// compile time).
func APanic(c *RecycleClearingCircuit) []frontend.Variable {
	n := len(c.ASeller)
	if len(c.APrice) != n || len(c.AQty) != n || len(c.SSeller) != n ||
		len(c.SPrice) != n || len(c.SQty) != n || len(c.Fills) != n {
		panic("RecycleClearingCircuit: inconsistent slice lengths")
	}
	return c.ASeller
}

// NewRecycleClearingCircuit allocates a size-n template.
func NewRecycleClearingCircuit(n int) *RecycleClearingCircuit {
	return &RecycleClearingCircuit{
		Fills:   make([]frontend.Variable, n),
		ASeller: make([]frontend.Variable, n),
		APrice:  make([]frontend.Variable, n),
		AQty:    make([]frontend.Variable, n),
		SSeller: make([]frontend.Variable, n),
		SPrice:  make([]frontend.Variable, n),
		SQty:    make([]frontend.Variable, n),
	}
}
