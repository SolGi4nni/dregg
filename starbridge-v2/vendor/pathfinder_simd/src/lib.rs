// pathfinder/simd/src/lib.rs
//
// Copyright © 2019 The Pathfinder Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![cfg_attr(pf_rustc_nightly, allow(internal_features))]
#![cfg_attr(pf_rustc_nightly, feature(link_llvm_intrinsics, core_intrinsics))]
#![cfg_attr(pf_rustc_nightly, feature(simd_ffi))]
#![cfg_attr(pf_rustc_nightly, feature(repr_simd))]

//! A minimal SIMD abstraction, usable outside of Pathfinder.

#[cfg(all(not(feature = "pf-no-simd"), pf_rustc_nightly, target_arch = "aarch64"))]
pub use crate::arm as default;
#[cfg(any(
    feature = "pf-no-simd",
    not(any(
        target_arch = "x86",
        target_arch = "x86_64",
        all(pf_rustc_nightly, target_arch = "aarch64")
    ))
))]
pub use crate::scalar as default;
#[cfg(all(
    not(feature = "pf-no-simd"),
    any(target_arch = "x86", target_arch = "x86_64")
))]
pub use crate::x86 as default;

// PATCHED (starbridge-v2 vendor): added `not(feature = "pf-no-simd")` so the
// `pf-no-simd` feature actually disables the aarch64 SIMD module. Upstream
// 0.5.6 omits it here (line 18's `default` re-export IS gated, but this
// `pub mod arm` is not), so `pf-no-simd` cannot turn off the SIMD path that
// uses nightly intrinsics removed in current toolchains. With this gate +
// `pf-no-simd` enabled, the crate builds the scalar fallback on nightly.
#[cfg(all(not(feature = "pf-no-simd"), pf_rustc_nightly, target_arch = "aarch64"))]
pub mod arm;
mod extras;
pub mod scalar;
#[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
pub mod x86;

#[cfg(test)]
mod test;
