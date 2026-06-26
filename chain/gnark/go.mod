// dregg native ETH wrap — the gnark circuit that verifies a dregg whole-history
// FRI proof directly (no RISC-V zkVM), emitting a Groth16/BN254 proof for
// IDreggSettlement.settle. See docs/deos/ETH-NATIVE-WRAP.md.
//
// This is the SKELETON / interface spec for the native wrap circuit. The Define
// body is a structured TODO laying out the three teeth of
// verify_turn_chain_recursive_from_parts (circuit-prove/src/ivc_turn_chain.rs:2845).
module github.com/emberian/dregg/chain/gnark

go 1.22

require github.com/consensys/gnark v0.11.0
</content>
