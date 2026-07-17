// End-to-end prototype for the RECYCLE-CLEARING circuit (clearing_snark.go):
// compile → (dev) setup → prove a real 4-ask book → verify → REJECT tampered
// public statements (price, a fill, the book commitment). The reference
// clearing mirrors `RecycleFlywheel._runAskClearing` line for line, and the
// book fold is byte-identical to the contract's `bookCommit` layout — the
// differential the .sol side can replay.
//
// The book mirrors test/RecycleFlywheelAB.t.sol's canonical honest recycle
// (1/2/3 gwei asks, 40 ETH budget → clears at 3 gwei, 10e9 tokens, 30 ETH)
// plus one zero-price ask (skipped by the walk, exactly as on-chain).
package friverifier

import (
	"math/big"
	"testing"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/backend/solidity"
	"github.com/consensys/gnark/frontend"
	"github.com/consensys/gnark/frontend/cs/r1cs"
	"golang.org/x/crypto/sha3"
)

type refAsk struct {
	seller *big.Int // 160-bit address as integer
	price  *big.Int // wei per whole token
	qty    *big.Int // whole tokens
}

// refFold replays the contract's fold:
// keccak256(abi.encodePacked(prev32, seller20, price32, qty32)).
func refFold(book []refAsk) [32]byte {
	var acc [32]byte
	for _, a := range book {
		h := sha3.NewLegacyKeccak256()
		h.Write(acc[:])
		h.Write(a.seller.FillBytes(make([]byte, 20)))
		h.Write(a.price.FillBytes(make([]byte, 32)))
		h.Write(a.qty.FillBytes(make([]byte, 32)))
		copy(acc[:], h.Sum(nil))
	}
	return acc
}

// refClearing mirrors RecycleFlywheel._runAskClearing over the SORTED book.
func refClearing(sorted []refAsk, budget *big.Int) (price, bought, spent *big.Int, fills []*big.Int) {
	price = big.NewInt(0)
	bought = big.NewInt(0)
	fills = make([]*big.Int, len(sorted))
	for i, a := range sorted {
		fills[i] = big.NewInt(0)
		if a.price.Sign() > 0 {
			affordable := new(big.Int).Div(budget, a.price)
			if affordable.Cmp(bought) > 0 {
				room := new(big.Int).Sub(affordable, bought)
				fill := new(big.Int).Set(a.qty)
				if fill.Cmp(room) > 0 {
					fill.Set(room)
				}
				if fill.Sign() > 0 {
					fills[i] = fill
					bought = new(big.Int).Add(bought, fill)
					price = a.price
				}
			}
		}
	}
	spent = new(big.Int).Mul(price, bought)
	return
}

func assignClearing(arrival, sorted []refAsk, budget *big.Int) *RecycleClearingCircuit {
	n := len(arrival)
	c := NewRecycleClearingCircuit(n)
	fold := refFold(arrival)
	c.ArrivalFoldHi = new(big.Int).SetBytes(fold[:16])
	c.ArrivalFoldLo = new(big.Int).SetBytes(fold[16:])
	c.Budget = budget
	price, bought, spent, fills := refClearing(sorted, budget)
	c.ClearingPrice = price
	c.Bought = bought
	c.Spent = spent
	for i := 0; i < n; i++ {
		c.Fills[i] = fills[i]
		c.ASeller[i] = arrival[i].seller
		c.APrice[i] = arrival[i].price
		c.AQty[i] = arrival[i].qty
		c.SSeller[i] = sorted[i].seller
		c.SPrice[i] = sorted[i].price
		c.SQty[i] = sorted[i].qty
	}
	return c
}

func TestRecycleClearingGroth16EndToEnd(t *testing.T) {
	g := big.NewInt(1_000_000_000) // 1 gwei
	eth := new(big.Int).Exp(big.NewInt(10), big.NewInt(18), nil)
	ask := func(sellerLow int64, priceG int64, qty int64) refAsk {
		return refAsk{
			seller: big.NewInt(0x1000 + sellerLow),
			price:  new(big.Int).Mul(big.NewInt(priceG), g),
			qty:    big.NewInt(qty),
		}
	}
	// The AB test's canonical book + a zero-price ask, in a scrambled arrival
	// order; sorted ascending for the walk.
	arrival := []refAsk{ask(3, 3, 4_000_000_000), ask(1, 1, 3_000_000_000), ask(4, 0, 5), ask(2, 2, 3_000_000_000)}
	sorted := []refAsk{arrival[2], arrival[1], arrival[3], arrival[0]}
	budget := new(big.Int).Mul(big.NewInt(40), eth)

	// The reference clearing must reproduce the measured .sol clearing.
	price, bought, spent, _ := refClearing(sorted, budget)
	if price.Cmp(new(big.Int).Mul(big.NewInt(3), g)) != 0 {
		t.Fatalf("reference uniform price = %s, want 3 gwei", price)
	}
	if bought.Cmp(big.NewInt(10_000_000_000)) != 0 {
		t.Fatalf("reference bought = %s, want 10e9", bought)
	}
	if spent.Cmp(new(big.Int).Mul(big.NewInt(30), eth)) != 0 {
		t.Fatalf("reference spent = %s, want 30 ETH", spent)
	}

	t0 := time.Now()
	ccs, err := frontend.Compile(ecc.BN254.ScalarField(), r1cs.NewBuilder, NewRecycleClearingCircuit(len(arrival)))
	if err != nil {
		t.Fatalf("compile: %v", err)
	}
	t.Logf("compile: %s; R1CS: %d constraints, %d public",
		time.Since(t0).Round(time.Millisecond), ccs.GetNbConstraints(), ccs.GetNbPublicVariables())

	t1 := time.Now()
	pk, vk, cacheHit, err := groth16LoadOrSetup(ccs, ecc.BN254, t.Logf)
	if err != nil {
		t.Fatalf("setup: %v", err)
	}
	if cacheHit {
		t.Logf("setup (CACHE HIT): %s", time.Since(t1).Round(time.Millisecond))
	} else {
		t.Logf("setup (UNSAFE dev): %s", time.Since(t1).Round(time.Millisecond))
	}

	t2 := time.Now()
	w, err := frontend.NewWitness(assignClearing(arrival, sorted, budget), ecc.BN254.ScalarField())
	if err != nil {
		t.Fatalf("witness: %v", err)
	}
	proof, err := groth16.Prove(ccs, pk, w,
		solidity.WithProverTargetSolidityVerifier(backend.GROTH16))
	if err != nil {
		t.Fatalf("prove: %v", err)
	}
	t.Logf("prove: %s", time.Since(t2).Round(time.Millisecond))

	pubw, err := w.Public()
	if err != nil {
		t.Fatal(err)
	}
	t3 := time.Now()
	if err := groth16.Verify(proof, vk, pubw,
		solidity.WithVerifierTargetSolidityVerifier(backend.GROTH16)); err != nil {
		t.Fatalf("verify REJECTED the honest clearing: %v", err)
	}
	t.Logf("verify: %s", time.Since(t3).Round(time.Millisecond))

	// ── The adversarial teeth: every tampered public statement must REJECT. ──
	reject := func(name string, mutate func(c *RecycleClearingCircuit)) {
		forged := assignClearing(arrival, sorted, budget)
		mutate(forged)
		fw, err := frontend.NewWitness(forged, ecc.BN254.ScalarField(), frontend.PublicOnly())
		if err != nil {
			t.Fatalf("%s: forged witness: %v", name, err)
		}
		if err := groth16.Verify(proof, vk, fw,
			solidity.WithVerifierTargetSolidityVerifier(backend.GROTH16)); err == nil {
			t.Fatalf("%s: ACCEPTED a clearing the proof does not attest", name)
		}
	}
	reject("misprice", func(c *RecycleClearingCircuit) {
		c.ClearingPrice = new(big.Int).Add(price, big.NewInt(1))
	})
	reject("skimmed spend", func(c *RecycleClearingCircuit) {
		c.Spent = new(big.Int).Sub(spent, big.NewInt(1))
	})
	reject("stolen fill", func(c *RecycleClearingCircuit) {
		c.Fills[1] = big.NewInt(1)
	})
	reject("swapped book", func(c *RecycleClearingCircuit) {
		c.ArrivalFoldLo = new(big.Int).Add(newFromVar(c.ArrivalFoldLo), big.NewInt(1))
	})
}

func newFromVar(v frontend.Variable) *big.Int {
	return new(big.Int).Set(v.(*big.Int))
}
