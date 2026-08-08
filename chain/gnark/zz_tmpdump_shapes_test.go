package friverifier

import (
	"fmt"
	"testing"
)

// TEMPORARY measurement harness — deleted after the shapes are read.
func TestTmpDumpBatchShapes(t *testing.T) {
	fx := loadShrinkRealFixture(t)
	logMax := fx.Fri.LogGlobalMaxHeight
	fmt.Printf("logGlobalMaxHeight=%d  index0=%d  rounds=%d\n", logMax, fx.Queries[0].ExpectedIndex, len(fx.InputRounds))
	for ri, r := range fx.InputRounds {
		round := OpenInputRoundShape{}
		for _, m := range r.Matrices {
			round.Matrices = append(round.Matrices,
				OpenInputMatrixShape{m.LogHeight, m.Width, m.NumPoints, m.NextPointBits})
		}
		groups := openInputHeightGroupsOf(round)
		maxLh := groups[0].logHeight
		var widths []int
		var heights []int
		total := 0
		for _, g := range groups {
			w := 0
			for _, mi := range g.mats {
				w += round.Matrices[mi].Width
			}
			widths = append(widths, w)
			heights = append(heights, g.logHeight)
			total += w
		}
		// injection mask: step s (0-based) injects when groups[next].logHeight == maxLh-s-1
		mask := make([]bool, maxLh)
		next := 1
		var injSteps []int
		for step := 0; step < maxLh; step++ {
			if next < len(groups) && groups[next].logHeight == maxLh-step-1 {
				mask[step] = true
				injSteps = append(injSteps, step)
				next++
			}
		}
		fmt.Printf("round %d: heights=%v widths=%v sumWidth=%d maxLh=%d injSteps=%v unconsumed=%v\n",
			ri, heights, widths, total, maxLh, injSteps, next != len(groups))
		fmt.Printf("  LEAN: batchData %v %d katMask(inj at %v)\n", widths, maxLh, injSteps)
	}
	fmt.Printf("commitMerkleDepths(apexShrinkShape-equivalent) — see EmitJson\n")
}
