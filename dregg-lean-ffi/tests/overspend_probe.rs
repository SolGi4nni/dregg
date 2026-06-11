//! Probe: does the GATED Lean executor reject an overspend transfer under unchecked auth
//! when the state has EMPTY side-tables (the lean_shadow marshal shape)?
//! Run: cargo test -p dregg-lean-ffi --features lean-lib --test overspend_probe -- --nocapture
#![cfg(feature = "lean-lib")]

#[test]
fn overspend_probe() {
    let cases = [
        (
            "shadow-shape overspend (empty side-tables, vu=1000000)",
            r#"{"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":0}]]}],[1,{"rec":[["balance",{"int":5}],["nonce",{"int":0}]]}]],"caps":[],"bal":[[0,0,100],[1,0,5]],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"turn":{"agent":0,"nonce":0,"fee":0,"valid_until":1000000,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"unchecked":0},"caveats":[],"action":{"bal":[0,0,1,1000,0]},"children":[]}}}"#,
        ),
        (
            "shadow-shape overspend but vu=0",
            r#"{"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":0}]]}],[1,{"rec":[["balance",{"int":5}],["nonce",{"int":0}]]}]],"caps":[],"bal":[[0,0,100],[1,0,5]],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"turn":{"agent":0,"nonce":0,"fee":0,"valid_until":0,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"unchecked":0},"caveats":[],"action":{"bal":[0,0,1,1000,0]},"children":[]}}}"#,
        ),
        (
            "valid transfer 30 (sanity)",
            r#"{"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":0}]]}],[1,{"rec":[["balance",{"int":5}],["nonce",{"int":0}]]}]],"caps":[],"bal":[[0,0,100],[1,0,5]],"escrows":[],"nullifiers":[],"commitments":[],"queues":[],"swiss":[],"revoked":[]},"turn":{"agent":0,"nonce":0,"fee":0,"valid_until":1000000,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"unchecked":0},"caveats":[],"action":{"bal":[0,0,1,30,0]},"children":[]}}}"#,
        ),
    ];
    for (label, wire) in cases {
        match dregg_lean_ffi::shadow_exec_full_forest_auth(wire) {
            Ok(out) => {
                let ok = out.contains("\"ok\":1");
                // extract the "bal":[...] segment to see if the balance actually moved.
                let bal = out
                    .find("\"bal\":")
                    .map(|i| {
                        let rest = &out[i..];
                        let end = rest.find(']').map(|j| j + 1).unwrap_or(rest.len());
                        &rest[..end]
                    })
                    .unwrap_or("<no bal>");
                println!("[{label}] committed={ok}  {bal}");
            }
            Err(e) => println!("[{label}] ERR {e}"),
        }
    }
}
