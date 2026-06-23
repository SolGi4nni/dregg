//! The **JS engine binding** — real SpiderMonkey (`mozjs`) driving deos substance.
//!
//! [`JsRuntime`] wraps a genuine `JSContext`/`Runtime` (the same minimal embedding the
//! `mozjs` `eval`/`callback` examples prove). It installs native Rust functions onto a
//! fresh global; a JS prelude builds the ergonomic `deos.applet({...})` / `app.fire` /
//! `app.get` / `app.view` surface on top of them. The natives bridge into a
//! thread-local [`Applet`] (the embedded verified executor) so:
//!
//!   - `app.fire("inc", n)` → a REAL cap-gated verified turn (a `TurnReceipt`);
//!   - `app.get(slot)` → a witnessed read off the live ledger;
//!   - `app.view.set(k, v)` → a plain in-memory change (NO turn, NO receipt).
//!
//! SpiderMonkey rooting/GC is observed via the `rooted!` macro and `CallArgs`, exactly
//! as the upstream `callback.rs` test does. This is the genuine engine, not a stub.

use std::cell::RefCell;
use std::ffi::CStr;
use std::ptr;
use std::ptr::NonNull;
use std::str;

use mozjs::context::{JSContext as SmContext, RawJSContext};
use mozjs::jsapi::{CallArgs, OnNewGlobalHookOption, Value};
use mozjs::jsval::{Int32Value, StringValue, UndefinedValue};
use mozjs::realm::AutoRealm;
use mozjs::rooted;
use mozjs::rust::wrappers2::{
    EncodeStringToUTF8, JS_DefineFunction, JS_NewGlobalObject, JS_NewStringCopyN,
};
use mozjs::rust::{
    evaluate_script, CompileOptionsWrapper, JSEngine, RealmOptions, Runtime, SIMPLE_GLOBAL_CLASS,
};

use crate::applet::Applet;
use crate::reflect_binding;

thread_local! {
    /// The applet the native functions drive. ONE applet per runtime for the spike
    /// (the polynomial-functor interface of a single sovereign cell). A real multi-app
    /// surface would key by an integer handle returned from `deos.applet`.
    static CURRENT_APPLET: RefCell<Option<Applet>> = const { RefCell::new(None) };
    /// The last error message a native produced (surfaced to the test).
    static LAST_NATIVE_ERROR: RefCell<Option<String>> = const { RefCell::new(None) };
    /// A scratch string for the UTF-8-encode callback to deposit into.
    static SCRATCH: RefCell<String> = const { RefCell::new(String::new()) };
}

/// Install the applet the native functions drive.
pub fn set_current_applet(applet: Applet) {
    CURRENT_APPLET.with(|c| *c.borrow_mut() = Some(applet));
}

/// Take the applet back out (to inspect its ledger/receipts after a JS run).
pub fn take_current_applet() -> Option<Applet> {
    CURRENT_APPLET.with(|c| c.borrow_mut().take())
}

/// The last native-function error, if any.
pub fn last_native_error() -> Option<String> {
    LAST_NATIVE_ERROR.with(|e| e.borrow().clone())
}

fn record_error(msg: String) {
    LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = Some(msg));
}

/// The JS prelude — builds `deos.applet`/`app.fire`/`app.get`/`app.view` atop the
/// `__deos_*` natives. `app.view.set/get` route to the EPHEMERAL natives (in-memory;
/// never a turn). `deos.applet(spec)` turns each declared affordance name into a
/// method that fires the corresponding verified turn.
const PRELUDE: &str = r#"
    var deos = {
        applet: function(spec) {
            var handle = {
                fire: function(name, arg) { return __deos_fire(String(name), arg | 0); },
                get: function(slot) { return __deos_get(slot | 0); },
                view: {
                    set: function(k, v) { __deos_view_set(String(k), String(v)); },
                    get: function(k) { return __deos_view_get(String(k)); }
                }
            };
            var names = (spec && spec.affordances) || [];
            for (var i = 0; i < names.length; i++) {
                (function(n) {
                    handle[n] = function(arg) { return handle.fire(n, arg | 0); };
                })(names[i]);
            }
            return handle;
        },
        // ── THE REFLECTIVE CRAWL (slice 2) — JS objects crawl the live image ──────
        // Reflection is a cap-bounded, attested READ (confers no authority), distinct
        // from driving (a turn). Every accessor parses JSON from a `__deos_reflect_*`
        // native that projects the live ledger through `deos-reflect`.
        world: {
            // every cell id on the ledger (the unbounded crawl root)
            cells: function() { return JSON.parse(__deos_world_cells()); },
            cellCount: function() { return this.cells().length; },
            // the capability web (nodes + edges)
            ocap: function() { return JSON.parse(__deos_world_ocap()); }
        },
        // a reflective handle on ONE cell: its four substances + per-viewer frustum.
        cell: function(id) {
            var cid = String(id);
            return {
                id: cid,
                // the four substances (value/authority/state/evidence) as a field tree
                reflect: function() {
                    var j = __deos_cell(cid);
                    return j === "null" ? null : JSON.parse(j);
                },
                // a quick read of a named substance field's value
                field: function(key) {
                    var r = this.reflect();
                    if (!r) return null;
                    for (var i = 0; i < r.fields.length; i++)
                        if (r.fields[i].key === key) return r.fields[i].value;
                    return null;
                },
                // .as(viewer) → the cap-bounded view: which cells `viewer` may crawl,
                // and a reflect() that yields null for an unobservable target.
                as: function(viewer) {
                    var v = String(viewer);
                    return {
                        frustum: function() { return JSON.parse(__deos_frustum(v)); },
                        canObserve: function(target) {
                            var f = this.frustum();
                            return f.visible.indexOf(String(target)) >= 0;
                        },
                        reflect: function(target) {
                            var j = __deos_frustum_reflect(v, String(target));
                            return j === "null" ? null : JSON.parse(j);
                        }
                    };
                }
            };
        }
    };
"#;

/// A real SpiderMonkey runtime with the `deos` binding available.
pub struct JsRuntime {
    rt: Runtime,
    // The engine handle must stay alive for the runtime's lifetime.
    _engine: JSEngine,
}

impl JsRuntime {
    /// Boot a genuine SpiderMonkey runtime. The `deos` binding + prelude are installed
    /// per-[`Self::eval`] (on a fresh global) so a single test script sees them.
    pub fn new() -> Result<Self, String> {
        let engine = JSEngine::init().map_err(|e| format!("JSEngine::init: {e:?}"))?;
        let rt = Runtime::new(engine.handle());
        Ok(JsRuntime { rt, _engine: engine })
    }

    /// Evaluate a JS program against a fresh global that has the `deos` binding. The
    /// program drives the thread-local applet. Returns the script's result as an i32
    /// if it produced one (else `None`).
    pub fn eval(&mut self, source: &str) -> Result<Option<i32>, String> {
        LAST_NATIVE_ERROR.with(|e| *e.borrow_mut() = None);

        let cx = self.rt.cx();
        let realm_opts = RealmOptions::default();
        unsafe {
            rooted!(&in(cx) let global = JS_NewGlobalObject(
                cx,
                &SIMPLE_GLOBAL_CLASS,
                ptr::null_mut(),
                OnNewGlobalHookOption::FireOnNewGlobalHook,
                &*realm_opts,
            ));

            // ENTER THE REALM before defining the natives / running scripts — the
            // proven upstream pattern (callback.rs). Defining a function on, or
            // converting a string within, a global that is NOT the active realm
            // segfaults. `global_and_reborrow` yields the realm-bound global handle +
            // the realm context to use for everything below.
            let mut realm = AutoRealm::new_from_handle(cx, global.handle());
            let (g, realm_cx) = realm.global_and_reborrow();

            // Install the native bridge functions on the realm's global.
            for (name, f, nargs) in [
                // drive (slice 1)
                (c"__deos_fire", native_fire as RawNative, 2u32),
                (c"__deos_get", native_get as RawNative, 1),
                (c"__deos_view_set", native_view_set as RawNative, 2),
                (c"__deos_view_get", native_view_get as RawNative, 1),
                // crawl (slice 2) — the reflective natives (return JSON strings)
                (c"__deos_world_cells", native_world_cells as RawNative, 0),
                (c"__deos_world_ocap", native_world_ocap as RawNative, 0),
                (c"__deos_cell", native_cell as RawNative, 1),
                (c"__deos_frustum", native_frustum as RawNative, 1),
                (c"__deos_frustum_reflect", native_frustum_reflect as RawNative, 2),
            ] {
                let defined = JS_DefineFunction(realm_cx, g, name.as_ptr(), Some(f), nargs, 0);
                if defined.is_null() {
                    return Err(format!("JS_DefineFunction failed for {name:?}"));
                }
            }

            // (1) install the prelude on this global; (2) run the user's source.
            eval_on(realm_cx, g, PRELUDE)?;
            let r = eval_on(realm_cx, g, source)?;

            if let Some(err) = last_native_error() {
                return Err(format!("native error during eval: {err}"));
            }
            Ok(r)
        }
    }
}

type RawNative = unsafe extern "C" fn(*mut RawJSContext, u32, *mut Value) -> bool;

/// Evaluate `source` against `global`, returning an i32 result if produced. The
/// rooted `rval` receives the script's completion value. `cx` must be the active
/// realm's context.
fn eval_on(
    cx: &mut SmContext,
    global: mozjs::rust::HandleObject,
    source: &str,
) -> Result<Option<i32>, String> {
    rooted!(&in(cx) let mut rval = UndefinedValue());
    let options = CompileOptionsWrapper::new(cx, c"deos.js".to_owned(), 1);
    match evaluate_script(cx, global, source, rval.handle_mut(), options) {
        Ok(()) => {
            let v = rval.get();
            if v.is_int32() {
                Ok(Some(v.to_int32()))
            } else {
                Ok(None)
            }
        }
        Err(()) => Err("evaluate_script returned an error".to_string()),
    }
}

/// Pull a UTF-8 String out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_string(cx: &mut SmContext, raw: mozjs::jsapi::HandleValue) -> String {
    let handle = mozjs::rust::Handle::from_raw(raw);
    let js = mozjs::rust::ToString(cx.raw_cx(), handle);
    rooted!(&in(cx) let rooted_str = js);
    unsafe extern "C" fn cb(message: *const core::ffi::c_char) {
        let m = CStr::from_ptr(message);
        let s = str::from_utf8(m.to_bytes()).unwrap_or("").to_string();
        SCRATCH.with(|sc| *sc.borrow_mut() = s);
    }
    EncodeStringToUTF8(cx, rooted_str.handle().into(), cb);
    SCRATCH.with(|sc| sc.borrow().clone())
}

/// Pull an i32 out of a JS value argument (the raw handle from `CallArgs::get`).
unsafe fn arg_i32(raw: mozjs::jsapi::HandleValue) -> i32 {
    let v = mozjs::rust::Handle::from_raw(raw).get();
    if v.is_int32() {
        v.to_int32()
    } else if v.is_double() {
        v.to_double() as i32
    } else {
        0
    }
}

// ── The native bridge functions ───────────────────────────────────────────────────

/// `__deos_fire(name, arg)` — fire an affordance = ONE cap-gated verified turn.
/// Returns the model's value at slot 0 after the turn (for the counter shape), or -1
/// on refusal (the cap tooth) / executor rejection.
unsafe extern "C" fn native_fire(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 1 {
        record_error("__deos_fire requires (name, arg)".into());
        args.rval().set(Int32Value(-1));
        return true;
    }
    let name = arg_string(&mut cx, args.get(0));
    let arg = if args.argc_ >= 2 {
        arg_i32(args.get(1)) as i64
    } else {
        0
    };

    // A cap-gate REFUSAL is an EXPECTED, JS-observable outcome (returns -1 with NO
    // receipt) — NOT a fatal eval error. Only a genuine fault (no applet, or the
    // executor rejecting an AUTHORIZED turn) poisons the eval.
    let outcome = CURRENT_APPLET.with(|c| {
        let mut guard = c.borrow_mut();
        match guard.as_mut() {
            Some(applet) => match applet.fire(&name, arg) {
                Ok(_receipt) => FireOutcome::Committed(applet.get_u64(0) as i32),
                Err(crate::applet::FireError::Unauthorized { .. }) => FireOutcome::Refused,
                Err(crate::applet::FireError::UnknownAffordance(n)) => {
                    FireOutcome::Fatal(format!("unknown affordance '{n}'"))
                }
                Err(crate::applet::FireError::Executor(r)) => {
                    FireOutcome::Fatal(format!("executor rejected authorized turn: {r}"))
                }
            },
            None => FireOutcome::Fatal("no applet installed".into()),
        }
    });

    match outcome {
        FireOutcome::Committed(v) => args.rval().set(Int32Value(v)),
        FireOutcome::Refused => args.rval().set(Int32Value(-1)),
        FireOutcome::Fatal(e) => {
            record_error(e);
            args.rval().set(Int32Value(-1));
        }
    }
    true
}

/// The three faces of a fire from JS: committed (a verified turn), refused (the cap
/// gate said no — expected, JS sees -1), or fatal (a real fault that poisons eval).
enum FireOutcome {
    Committed(i32),
    Refused,
    Fatal(String),
}

/// `__deos_get(slot)` — a witnessed read off the live ledger.
unsafe extern "C" fn native_get(_context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let args = CallArgs::from_vp(vp, argc);
    let slot = if args.argc_ >= 1 {
        arg_i32(args.get(0)) as usize
    } else {
        0
    };
    let v = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_u64(slot) as i32)
            .unwrap_or(-1)
    });
    args.rval().set(Int32Value(v));
    true
}

/// `__deos_view_set(key, value)` — ephemeral view-state. NO turn, NO receipt.
unsafe extern "C" fn native_view_set(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    if args.argc_ < 2 {
        record_error("__deos_view_set requires (key, value)".into());
        args.rval().set(UndefinedValue());
        return true;
    }
    let key = arg_string(&mut cx, args.get(0));
    let val = arg_string(&mut cx, args.get(1));
    CURRENT_APPLET.with(|c| {
        if let Some(a) = c.borrow_mut().as_mut() {
            a.set_view(&key, &val);
        }
    });
    args.rval().set(UndefinedValue());
    true
}

/// `__deos_view_get(key)` — read ephemeral view-state. Returns 1 if present else 0.
unsafe extern "C" fn native_view_get(
    context: *mut RawJSContext,
    argc: u32,
    vp: *mut Value,
) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let key = if args.argc_ >= 1 {
        arg_string(&mut cx, args.get(0))
    } else {
        String::new()
    };
    let present = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| a.get_view(&key).is_some())
            .unwrap_or(false)
    });
    args.rval().set(Int32Value(if present { 1 } else { 0 }));
    true
}

// ── THE REFLECTIVE CRAWL natives (slice 2) — each returns a JSON STRING ────────────

/// Set the rval of a native call to a freshly-allocated JS string. Returns false (the
/// native should return false) only on allocation failure.
unsafe fn return_string(cx: &mut SmContext, args: &CallArgs, s: &str) -> bool {
    let js_str = JS_NewStringCopyN(cx, s.as_ptr() as *const core::ffi::c_char, s.len());
    if js_str.is_null() {
        record_error("JS_NewStringCopyN failed".into());
        args.rval().set(UndefinedValue());
        return false;
    }
    args.rval().set(StringValue(&*js_str));
    true
}

/// `__deos_world_cells()` → JSON array of every cell id on the applet's ledger.
unsafe extern "C" fn native_world_cells(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| reflect_binding::world_cells_json(a.ledger()))
            .unwrap_or_else(|| "[]".to_string())
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_world_ocap()` → JSON of the capability web (nodes + edges).
unsafe extern "C" fn native_world_ocap(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let json = CURRENT_APPLET.with(|c| {
        c.borrow()
            .as_ref()
            .map(|a| reflect_binding::world_ocap_json(a.ledger()))
            .unwrap_or_else(|| "{\"nodes\":[],\"edges\":[]}".to_string())
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_cell(id)` → JSON of the cell's four substances (or `"null"` if absent).
unsafe extern "C" fn native_cell(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let id_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match reflect_binding::parse_cell_id(&id_hex) {
            Some(id) => reflect_binding::cell_json(applet.ledger(), &id).unwrap_or_else(|| "null".to_string()),
            None => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum(viewer)` → JSON of the cap-bounded view (which cells viewer crawls).
unsafe extern "C" fn native_frustum(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        };
        match reflect_binding::parse_cell_id(&viewer_hex) {
            Some(viewer) => reflect_binding::frustum_json(applet.ledger(), &viewer),
            None => "{\"viewer\":\"\",\"visibleCount\":0,\"visible\":[]}".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}

/// `__deos_frustum_reflect(viewer, target)` → the cell JSON if `viewer` may observe
/// `target`, else `"null"` (the attested read: an unreachable cell is absent).
unsafe extern "C" fn native_frustum_reflect(context: *mut RawJSContext, argc: u32, vp: *mut Value) -> bool {
    let mut cx = SmContext::from_ptr(NonNull::new(context).unwrap());
    let args = CallArgs::from_vp(vp, argc);
    let viewer_hex = if args.argc_ >= 1 { arg_string(&mut cx, args.get(0)) } else { String::new() };
    let target_hex = if args.argc_ >= 2 { arg_string(&mut cx, args.get(1)) } else { String::new() };
    let json = CURRENT_APPLET.with(|c| {
        let guard = c.borrow();
        let applet = match guard.as_ref() {
            Some(a) => a,
            None => return "null".to_string(),
        };
        match (
            reflect_binding::parse_cell_id(&viewer_hex),
            reflect_binding::parse_cell_id(&target_hex),
        ) {
            (Some(viewer), Some(target)) => {
                reflect_binding::frustum_reflect_json(applet.ledger(), &viewer, &target)
            }
            _ => "null".to_string(),
        }
    });
    return_string(&mut cx, &args, &json)
}
