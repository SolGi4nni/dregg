// fhegg-rtl / hardware / spinalhdl / Butterfly.scala
//
// SKELETON (M0) — a SpinalHDL NTT butterfly, co-simulated against the Lean golden model
// `Fhegg.Rtl.Golden.butterfly` in `../../lean/Fhegg/Rtl/Golden/Butterfly.lean`:
//
//     butterfly (q a b w) = ( (a + w*b) mod q , (a - w*b) mod q )
//
// This is a COMMENTED SCAFFOLD with honest TODOs, not a finished core. It lays down the port
// shape (matching the golden `def` argument order so the co-sim mapping is trivial) and names
// the productive-bulk work. See ../../CONTRIBUTING.md §3 (milestone M0/M1) for the ladder.
//
// Build: this file is NOT yet wired to a real sbt project that resolves SpinalHDL — `build.sbt`
// here is a stub. A contributor adds the SpinalHDL dependency and runs `SpinalVerilog(...)`.

// TODO(contributor): uncomment once SpinalHDL is on the classpath (see build.sbt).
// import spinal.core._
// import spinal.lib._

// object ButterflyGen extends App {
//
//   /** An NTT butterfly over Z/qZ.
//     *
//     *  Ports mirror the Lean golden `butterfly (q a b w)` argument order:
//     *    inputs  a, b, w  : UInt(width bits)
//     *    outputs hi, lo   : UInt(width bits)   -- (a + w*b) mod q,  (a - w*b) mod q
//     *
//     *  The ADD/SUB combiner (`a ± t` where `t = w*b`) is the datapath VERIFIED in Lean
//     *  (Fhegg.Rtl.Examples.RippleAdder + Golden.Butterfly's `butterfly_add`/`butterfly_sub`).
//     *  The MODULAR MULTIPLY (`w*b`) and the MODULAR REDUCTION (mod q) are the productive-bulk
//     *  work co-simulated against the golden model — NOT claimed verified here.
//     */
//   case class Butterfly(width: Int, q: BigInt) extends Component {
//     val io = new Bundle {
//       val a  = in  UInt (width bits)
//       val b  = in  UInt (width bits)
//       val w  = in  UInt (width bits)
//       val hi = out UInt (width bits)
//       val lo = out UInt (width bits)
//     }
//
//     // TODO(M1): modular multiply w*b mod q. Use Barrett or Montgomery reduction.
//     //   val t = modMul(io.w, io.b, q)          // productive bulk
//     // TODO(M0): the add/sub combiner — the Lean-VERIFIED core datapath shape.
//     //   io.hi := modAdd(io.a, t, q)            // (a + w*b) mod q
//     //   io.lo := modSub(io.a, t, q)            // (a - w*b) mod q
//     //
//     // Placeholder wiring so the shape is visible (NOT correct — no reduction):
//     // io.hi := (io.a + io.w * io.b).resized
//     // io.lo := (io.a - io.w * io.b).resized
//   }
//
//   // Elaborate to Verilog for the co-sim harness (../cosim/):
//   // SpinalVerilog(Butterfly(width = 32, q = BigInt("2013265921")))  // BabyBear prime
// }

// -----------------------------------------------------------------------------------------------
// The co-sim contract (see ../cosim/README.md):
//   1. Lean dumps golden vectors: rows of (a, b, w, hi_expected, lo_expected) for random inputs.
//   2. This module is simulated (Verilator or SpinalSim) on the same (a, b, w).
//   3. The harness asserts (hi, lo) == (hi_expected, lo_expected) — first mismatch fails.
// The residual seam — "the simulator faithfully executes this RTL" — is NAMED, exactly as the
// dregg AIR path names its `HashCR` floor. No formal Verilog semantics is claimed.
