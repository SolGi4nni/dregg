/-
# Fhegg — the fhEgg verified-RTL spine (root aggregator).

A dependency-free (core Lean, no mathlib) SEED for the FPGA dark-pool accelerator's
verified core: a Lean netlist DSL → Verilog emitter reusing dregg's verified-emit discipline,
a worked full-adder / ripple-adder example (`eval = spec` proven), and the FHE-fold golden
models (mint-safe accumulator, NTT butterfly) the productive-bulk RTL is co-simulated against.

See `docs/deos/FHEGG-RTL-VERIFIED-HARDWARE.md` (the survey + strategy) and
`fhegg-rtl/CONTRIBUTING.md` (the parallel on-ramp).
-/
import Fhegg.Rtl.Netlist
import Fhegg.Rtl.Examples.FullAdder
import Fhegg.Rtl.Examples.RippleAdder
import Fhegg.Rtl.Golden.Accumulator
import Fhegg.Rtl.Golden.Butterfly
