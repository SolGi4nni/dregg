# Constant-address witness MSM qualification — 2026-07-22

This note records the isolated WGPU qualification stone for the security-critical
inner-product `L`/`R` boundary: an MSM with secret scalars and arbitrary public
canonical Ristretto points.  It is not wired into the Bulletproof prover and is
not production authority.

## Threat model and fixed schedule

The protected values are the canonical scalar bytes and every point derived
from them before the final MSM result.  Public values are the points, term
count, fixed 256-bit scalar width, power-of-two reduction shape, dispatch
geometry, and the final MSM point.

For every term the shader executes exactly 256 doublings and 256 additions.
The secret bit chooses between the public point and the identity through
limb-wise WGSL `select`; it does not choose a buffer address, loop bound,
dispatch count, branch, or early exit.  The compact field implementation is
also branchless with respect to secret-derived coordinates: borrow, conditional
subtraction, and point selection use arithmetic selection.  The only shader
`if` statements and returns are invocation-id bounds against a public count.

Scaled points remain on device.  A fixed power-of-two binary tree performs one
complete Edwards addition per pair and alternates two resident buffers until
one point remains.  The host uploads public points once, secret scalars once,
and the public dispatch-control table once.  It reads back only the final point.
Dalek independently computes the constant-time MSM and accepts the GPU result
only through checked extended-coordinate import against those exact compressed
bytes.

The Rust unit gate audits the WGSL source and fails if:

- an `if` or `return` appears beyond the two named public gid bounds;
- a non-fixed loop bound, `loop`, `while`, or `discard` appears;
- the single scalar read is no longer addressed by public term id plus fixed
  bit index; or
- the secret bit no longer flows through point selection.

This source audit is a regression pin, not a proof about generated GPU ISA.

## Scrubbing contract

On every normal completion, parity refusal, and asynchronous map failure after
allocation, the implementation submits clears for the scalar buffer, both
witness-derived point buffers, and the readback buffer, then waits for device
completion.  Host scalar words and the typed scalar copy are overwritten.  The
caller owns and must scrub the borrowed input scalar byte slice.

The WGPU clear is a logical device-buffer overwrite.  It does not attest
physical VRAM remanence, driver copies, swap, crash dumps, or behavior after a
process abort/device loss.

## Qualification gate

The stone is intentionally bounded to 256 power-of-two terms.  The hard hbox
gate covers zero, one, and dense canonical scalar patterns; identity and
ordinary public points; N=1,2,64; exact dalek parity; malformed scalar and point
refusal; length and reduction-shape refusal; final-point-only readback; and the
four-buffer scrub contract.

```sh
scripts/hbuild gpu-e2e env DREGG_REQUIRE_WGPU=1 \
  cargo nextest run --release \
  --manifest-path vendor/bulletproofs-r1cs-wgpu/Cargo.toml \
  --features yoloproofs,wgpu-msm \
  --test wgpu_secret_msm_constant_address --run-ignored all --no-capture
```

Hardware timing and final status are recorded only after that command passes.

## Residual before production use

- Review compiled SPIR-V/driver ISA to determine whether WGSL `select` remains
  branchless and whether integer operations have operand-dependent timing.
- Measure timing distributions across adversarial scalar Hamming weights, not
  just functional parity.
- Decide whether shared-GPU cache, scheduler, power, and co-tenant observation
  are within the deployment threat model; dedicated GPU execution may be
  required.
- Extend the fixed reduction and dispatch geometry to the real 2^21 scale and
  demonstrate an end-to-end prover win.
- Integrate transcript-round `L`/`R` readback and public `u` upload without
  exposing intermediate generator or witness vectors.
- Preserve byte-identical proof output and ordinary verifier acceptance in the
  full authenticated-custody tooth.
- Treat this Ristretto/Bulletproof path as classical cryptography; it is not a
  post-quantum proof system.

Until those gates close, the kernel is a security-relevant qualification
artifact only and must remain unwired from `inner_product_proof.rs`.
