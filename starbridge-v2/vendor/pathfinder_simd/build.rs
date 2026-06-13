// pathfinder/simd/build.rs
//
// Copyright © 2019 The Pathfinder Project Developers.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

extern crate rustc_version;

use rustc_version::Channel;

fn main() {
    // Assert we haven't travelled back in time
    assert!(rustc_version::version().unwrap().major >= 1);

    // PATCHED (starbridge-v2 vendor): the `pf_rustc_nightly` cfg is NOT set.
    //
    // Upstream sets it on any nightly channel, which selects an aarch64 SIMD
    // module (`src/arm/mod.rs`) that uses portable-SIMD intrinsics
    // (`simd_minimum_number_nsz` / `simd_maximum_number_nsz`) that churn across
    // nightlies and were absent in this repo's pinned nightly. The `pf-no-simd`
    // feature was supposed to disable that path but upstream's `pub mod arm`
    // gate omits the feature check, so the feature alone can't turn it off.
    //
    // The robust fix: never advertise nightly. With `pf_rustc_nightly` unset,
    // `src/lib.rs` selects the portable SCALAR `default` on aarch64 (and SSE on
    // x86), and the `arm` module is gated out entirely — no nightly intrinsics,
    // no feature-unification dependence. gpui's geometry needs correct results,
    // not the SIMD fast path, so the scalar fallback is a pure perf trade.
    //
    // `Channel` is still imported to keep the upstream shape; suppress unused.
    let _ = Channel::Nightly;
}
