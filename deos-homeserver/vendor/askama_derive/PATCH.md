# Vendored `askama_derive` 0.16.0 — one-line patch

This is an unmodified copy of `askama_derive` 0.16.0 from crates.io **except** for
a single behavioral change in `src/generator.rs`, applied via
`[patch.crates-io.askama_derive]` in `../../Cargo.toml`.

## Why

continuwuity's `conduwuit_web` crate defines a `template!` macro_rules wrapper
(`src/web/pages/mod.rs`) that expands to `#[derive(askama::Template)]`, and
invokes it from source files at varying directory depths under
`src/web/pages/**`. It also ships an `askama.toml` (`dirs = ["pages/templates"]`)
at the crate root.

askama 0.16's `Generator::caller_dir()` computes a template's *caller-relative*
path from `proc_macro::Span::call_site().local_file()` and emits, for build
change-tracking, an `include_bytes!(<relative path>)` for both the templates and
`askama.toml`. On this toolchain (rustc 1.96.1, macOS), for a `#[derive]` emitted
inside a `macro_rules!` body, `call_site().local_file()` reports the macro
*definition* site (`pages/mod.rs`), so askama computes a path like
`../askama.toml`; but rustc resolves the emitted `include_bytes!` literal against
the macro *invocation* site (e.g. `pages/account/register.rs`). The two disagree
by the invocation directory's depth, so the tracked path points at a nonexistent
file (e.g. `pages/account/../askama.toml` → `pages/askama.toml`), and
`conduwuit_web` fails to compile with ~50 `couldn't read ...: No such file`
errors.

This is not git-vs-path or a feature/lockfile difference (verified: identical
askama/proc-macro2/syn/quote/toml versions, `config` feature on in both) — it is
askama's caller-relative change-tracking being unsound for macro-wrapped derives
on this toolchain.

## The change

`caller_dir` starts as `CallerDir::Invalid` instead of `CallerDir::Unresolved`,
so `caller_dir()` always returns `None` and `rel_path()` returns the **absolute**
template / `askama.toml` path unchanged. Absolute paths are equally valid for
`include_bytes!` (and are change-tracked the same), so template resolution and
recompile-on-change are unaffected — only upstream's relative-path prettiness is
dropped. `caller_dir()` feeds *only* `rel_path()`, which feeds *only* the
change-tracking `include_bytes!`; it is never used for actual template lookup
(`find_template`), so nothing else is affected.

## Upstreaming

This is a candidate upstream fix for askama (fall back to absolute paths when the
caller dir cannot be trusted for macro-wrapped derives). Until then this vendored
patch keeps continuwuity embeddable as a normal git dependency.
