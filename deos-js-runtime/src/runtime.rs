//! The **native deos-js runtime** — a pure-Rust `boa` engine driving cell-attached JS.
//!
//! A fresh [`boa_engine::Context`] has NO host bindings (no fetch/fs/process/clock
//! beyond ECMAScript `Date`). The sandbox boundary IS the absence of ambient
//! functions; [`NativeRuntime`] installs only the cap-bounded host surface a cell's
//! attached JS is allowed to touch. The keystone is `t(turn, arg)` — fire an
//! affordance = commit ONE cap-gated verified turn (the same path a static `{turn,arg}`
//! button runs). See `docs/deos/JS-ON-CELLS.md`.
//!
//! Host state is shared with the native function via a thread-local (the proven
//! deos-js pattern): [`NativeRuntime::run`] installs the [`CellApplet`] into the
//! thread-local for the eval's duration, then takes it back out with its committed
//! receipt tape.

use std::cell::RefCell;

use boa_engine::{js_string, Context, JsNativeError, JsValue, NativeFunction, Source};

use crate::applet::{CellApplet, FireError};
use crate::world::CellWorld;

thread_local! {
    /// The applet the installed host functions drive, for the duration of one
    /// [`NativeRuntime::run`]. The native `t` borrows it, fires, and puts it back.
    static CURRENT_APPLET: RefCell<Option<CellApplet>> = const { RefCell::new(None) };
    /// The multi-cell world the installed host functions drive, for the duration of one
    /// [`NativeRuntime::run_world`]. The native `t`/`tCell`/`transfer`/`viewPatch`/`get`
    /// borrow it, act, and put it back.
    static CURRENT_WORLD: RefCell<Option<CellWorld>> = const { RefCell::new(None) };
    /// The last cap-tooth / executor refusal a host fn hit (surfaced to the caller even
    /// though the JS sees a thrown error).
    static LAST_FIRE_ERROR: RefCell<Option<FireError>> = const { RefCell::new(None) };
}

/// What a [`NativeRuntime::run`] produced.
pub struct RunOutcome {
    /// The applet handed back, carrying its committed receipt tape + live model.
    pub applet: CellApplet,
    /// The script's completion value coerced to `i32`, if it produced a number.
    pub result: Option<i32>,
    /// The last fire refusal a host fn hit during the run (the cap tooth or the
    /// executor), if any — even though the JS observed a thrown error.
    pub last_fire_error: Option<FireError>,
}

/// The cap-bounded host function `t(turn, arg)` — **fire an affordance**. This is the
/// ONLY authority the cell-JS has: every other host capability (fs/net/clock) is
/// absent. It bridges into [`CellApplet::fire`], so the cell-JS commits the SAME
/// cap-gated verified turn a static `{turn,arg}` button does.
///
/// `t(name)` fires with arg 0; `t(name, n)` fires with the integer arg. Returns the new
/// value of the affordance's slot (a witnessed read off the live ledger). An unknown
/// affordance, a cap-tooth refusal, or an executor rejection throws a JS error AND is
/// recorded in [`LAST_FIRE_ERROR`] for the host.
fn native_fire(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    let name = match args.first() {
        Some(v) => v.to_string(ctx)?.to_std_string_escaped(),
        None => {
            return Err(JsNativeError::typ()
                .with_message("t(turn, arg): missing affordance name")
                .into())
        }
    };
    let arg: i64 = match args.get(1) {
        Some(v) if !v.is_undefined() => v.to_i32(ctx)? as i64,
        _ => 0,
    };

    // Fire inside the thread-local borrow; on success read back the model scalar (the
    // witnessed value `t` returns). The PoC counter surface writes slot 0.
    let fired: Result<i64, FireError> = CURRENT_APPLET.with(|cell| {
        let mut slot = cell.borrow_mut();
        let applet = slot
            .as_mut()
            .expect("a CellApplet is installed for the duration of run()");
        applet
            .fire(&name, arg)
            .map(|_receipt| applet.get_u64(0) as i64)
    });

    match fired {
        Ok(value) => Ok(JsValue::from(value)),
        Err(e) => {
            LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = Some(e.clone()));
            Err(JsNativeError::typ()
                .with_message(format!("t({name:?}) refused: {e}"))
                .into())
        }
    }
}

/// The native (pure-Rust, no-servo) deos-js runtime. One engine that runs cell-attached
/// JS in the cockpit (gpui) AND the web shell — `boa` compiles to native and wasm with
/// no C toolchain.
pub struct NativeRuntime {
    context: Context,
}

impl Default for NativeRuntime {
    fn default() -> Self {
        Self::new()
    }
}

impl NativeRuntime {
    /// Boot a fresh runtime. The `Context` starts with NO host bindings — the sandbox.
    pub fn new() -> Self {
        NativeRuntime {
            context: Context::default(),
        }
    }

    /// **Run cell-attached JS** against `applet`. Installs the cap-bounded host surface
    /// (`t(turn, arg)`) onto a fresh global, evals `source`, then hands the applet back
    /// with its committed receipt tape. The script can do nothing but call the installed
    /// host functions + ECMAScript builtins — no fs/net/clock/ambient authority.
    pub fn run(&mut self, applet: CellApplet, source: &str) -> Result<RunOutcome, String> {
        // Install the cap-bounded host functions onto the global.
        self.context
            .register_global_callable(js_string!("t"), 2, NativeFunction::from_fn_ptr(native_fire))
            .map_err(|e| format!("register t(): {e}"))?;

        CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(applet));
        LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = None);

        let eval = self.context.eval(Source::from_bytes(source));

        let applet = CURRENT_APPLET
            .with(|c| c.borrow_mut().take())
            .ok_or_else(|| "the applet vanished during run".to_string())?;
        let last_fire_error = LAST_FIRE_ERROR.with(|s| s.borrow_mut().take());

        match eval {
            Ok(value) => {
                let result = value.as_number().map(|n| n as i32);
                Ok(RunOutcome {
                    applet,
                    result,
                    last_fire_error,
                })
            }
            Err(e) => Err(format!("JS error: {e}")),
        }
    }
}

// ─── The multi-cell world host surface — a JS *app* coordinating several cells ──────

/// Record a fire refusal for the host, then translate it into a thrown JS error (so the
/// script's own `try/catch` sees it too). The over-reach is recorded AND surfaced.
fn refuse(name: &str, e: FireError) -> JsNativeError {
    LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = Some(e.clone()));
    JsNativeError::typ().with_message(format!("{name} refused: {e}"))
}

/// Borrow the installed world for one host-fn call.
fn with_world<R>(f: impl FnOnce(&mut CellWorld) -> R) -> R {
    CURRENT_WORLD.with(|c| {
        let mut slot = c.borrow_mut();
        let world = slot
            .as_mut()
            .expect("a CellWorld is installed for the duration of run_world()");
        f(world)
    })
}

/// `t(turn, arg)` — fire an affordance on the **home** cell (one cap-gated verified turn).
fn world_t(_this: &JsValue, args: &[JsValue], ctx: &mut Context) -> boa_engine::JsResult<JsValue> {
    let name = arg_string(args.first(), ctx, "t(turn, arg): missing affordance name")?;
    let arg = arg_i64(args.get(1), ctx)?;
    match with_world(|w| w.fire_home(&name, arg)) {
        Ok(fired) => Ok(JsValue::from(fired.value)),
        Err(e) => Err(refuse(&format!("t({name:?})"), e).into()),
    }
}

/// `tCell(cell, turn, arg)` — **fire an affordance on ANOTHER cell** the JS holds a cap to
/// (the multi-cell-coordination keystone). A cell the JS holds no cap to is unreachable.
fn world_t_cell(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    let cell = arg_string(
        args.first(),
        ctx,
        "tCell(cell, turn, arg): missing cell handle",
    )?;
    let name = arg_string(
        args.get(1),
        ctx,
        "tCell(cell, turn, arg): missing affordance",
    )?;
    let arg = arg_i64(args.get(2), ctx)?;
    match with_world(|w| w.fire_on(&cell, &name, arg)) {
        Ok(fired) => Ok(JsValue::from(fired.value)),
        Err(e) => Err(refuse(&format!("tCell({cell:?}, {name:?})"), e).into()),
    }
}

/// `transfer(from, to, amount)` — **move value** between two cells the JS holds caps to,
/// conservation enforced by the executor. Returns `from`'s new balance.
fn world_transfer(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    let from = arg_string(
        args.first(),
        ctx,
        "transfer(from, to, amount): missing from",
    )?;
    let to = arg_string(args.get(1), ctx, "transfer(from, to, amount): missing to")?;
    let amount = arg_i64(args.get(2), ctx)?.max(0) as u64;
    match with_world(|w| w.transfer(&from, &to, amount)) {
        Ok(bal) => Ok(JsValue::from(bal)),
        Err(e) => Err(refuse(&format!("transfer({from:?}->{to:?})"), e).into()),
    }
}

/// `get(slot)` — witnessed read of a **home** slot; `get(cell, slot)` — witnessed read of a
/// named cell's slot. Confers no authority.
fn world_get(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    // get(cell, slot) when the first arg is a string handle; get(slot) otherwise.
    let read = match args.first() {
        Some(v) if v.is_string() => {
            let cell = v.to_string(ctx)?.to_std_string_escaped();
            let slot = arg_i64(args.get(1), ctx)? as usize;
            with_world(|w| w.get_slot(&cell, slot))
        }
        _ => {
            let slot = arg_i64(args.first(), ctx)? as usize;
            with_world(|w| w.get_home_slot(slot))
        }
    };
    match read {
        Ok(v) => Ok(JsValue::from(v as i64)),
        Err(e) => Err(refuse("get", e).into()),
    }
}

/// `viewPatch(node)` — a **receipted self-edit** of the home cell's committed view-tree.
/// `node` is a JSON string of a `{kind,props,children}` node; a non-JSON string becomes a
/// text node. Moves `heap_root` + leaves a receipt; returns the new view version.
fn world_view_patch(
    _this: &JsValue,
    args: &[JsValue],
    ctx: &mut Context,
) -> boa_engine::JsResult<JsValue> {
    let raw = arg_string(args.first(), ctx, "viewPatch(node): missing node")?;
    let node = serde_json::from_str::<serde_json::Value>(&raw).unwrap_or_else(
        |_| serde_json::json!({ "kind": "text", "props": { "text": raw }, "children": [] }),
    );
    match with_world(|w| w.view_patch(node)) {
        Ok(version) => Ok(JsValue::from(version as i64)),
        Err(e) => Err(refuse("viewPatch", e).into()),
    }
}

fn arg_string(
    v: Option<&JsValue>,
    ctx: &mut Context,
    missing: &str,
) -> boa_engine::JsResult<String> {
    match v {
        Some(v) => Ok(v.to_string(ctx)?.to_std_string_escaped()),
        None => Err(JsNativeError::typ()
            .with_message(missing.to_string())
            .into()),
    }
}

fn arg_i64(v: Option<&JsValue>, ctx: &mut Context) -> boa_engine::JsResult<i64> {
    match v {
        Some(v) if !v.is_undefined() => Ok(v.to_i32(ctx)? as i64),
        _ => Ok(0),
    }
}

/// What a [`NativeRuntime::run_world`] produced — the world handed back with its committed
/// receipt tape + live cells, the script's coerced result, and any fire refusal.
pub struct WorldOutcome {
    /// The world handed back, carrying its committed receipt tape + live cell state.
    pub world: CellWorld,
    /// The script's completion value coerced to `i32`, if it produced a number.
    pub result: Option<i32>,
    /// The last fire refusal a host fn hit during the run (a cap tooth, a missing
    /// capability, or the executor), if any — even though the JS observed a thrown error.
    pub last_fire_error: Option<FireError>,
}

impl NativeRuntime {
    /// **Run a native-JS *app*** against a multi-cell [`CellWorld`]. Installs the full
    /// cap-bounded host surface — `t`/`tCell`/`transfer`/`get`/`viewPatch` — onto a fresh
    /// global, evals `source`, then hands the world back with its committed receipt tape.
    /// The script can do nothing but call these host functions + ECMAScript builtins; it
    /// references cells only by the handles the cap table installed (no ambient cell ids),
    /// and every effect is a verified turn bounded by the cap held for that cell.
    pub fn run_world(&mut self, world: CellWorld, source: &str) -> Result<WorldOutcome, String> {
        let installs: &[(&str, usize, NativeFunction)] = &[
            ("t", 2, NativeFunction::from_fn_ptr(world_t)),
            ("tCell", 3, NativeFunction::from_fn_ptr(world_t_cell)),
            ("transfer", 3, NativeFunction::from_fn_ptr(world_transfer)),
            ("get", 2, NativeFunction::from_fn_ptr(world_get)),
            (
                "viewPatch",
                1,
                NativeFunction::from_fn_ptr(world_view_patch),
            ),
        ];
        for (name, arity, f) in installs {
            self.context
                .register_global_callable(js_string!(*name), *arity, f.clone())
                .map_err(|e| format!("register {name}(): {e}"))?;
        }

        CURRENT_WORLD.with(|c| *c.borrow_mut() = Some(world));
        LAST_FIRE_ERROR.with(|s| *s.borrow_mut() = None);

        let eval = self.context.eval(Source::from_bytes(source));

        let world = CURRENT_WORLD
            .with(|c| c.borrow_mut().take())
            .ok_or_else(|| "the world vanished during run".to_string())?;
        let last_fire_error = LAST_FIRE_ERROR.with(|s| s.borrow_mut().take());

        match eval {
            Ok(value) => Ok(WorldOutcome {
                world,
                result: value.as_number().map(|n| n as i32),
                last_fire_error,
            }),
            Err(e) => Err(format!("JS error: {e}")),
        }
    }
}
