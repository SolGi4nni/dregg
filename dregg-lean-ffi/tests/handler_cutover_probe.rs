//! Runtime ABI tooth for the credential-preserving handler cutover.
//!
//! The old diagnostic handler path erased node authorization before flattening.
//! The exported replacement must accept the genuine credential and reject the
//! otherwise-identical forged one with a prologue-only status.
#![cfg(feature = "lean-lib")]

const GENUINE_WIRE: &str = r#"{"host":{"now":0,"block_height":0,"frozen":[],"stored_head":0,"budget":1000000000},"state":{"cells":[[0,{"rec":[["balance",{"int":100}],["nonce",{"int":7}]]}],[1,{"rec":[["balance",{"int":5}]]}]],"caps":[[9,[{"node":0}]]],"bal":[[0,0,100],[1,0,5]],"escrows":[[1,0,1,7,0,0,0,{"none":0},{"none":0}]],"nullifiers":[111],"commitments":[222],"queues":[[1,0,4,[333,444]]],"swiss":[[5,0,1,[0,1],1,{"some":99}]],"revoked":[],"lifecycle":[],"deathCert":[],"delegate":[]},"turn":{"agent":0,"nonce":7,"fee":10,"valid_until":1000,"prev":"0000000000000000000000000000000000000000000000000000000000000000","root":{"auth":{"sig":["0000000000000000000000000000000000000000000000000000000000000007",7]},"caveats":[],"action":{"bal":[0,0,1,30,0]},"children":[]}}}"#;

#[test]
fn handler_export_preserves_the_credential_gate() {
    if !dregg_lean_ffi::demand_lean(
        dregg_lean_ffi::lean_available(),
        "verified Lean runtime for the handler-cutover ABI",
    ) {
        return;
    }

    let genuine = match dregg_lean_ffi::shadow_exec_handler_turn(GENUINE_WIRE) {
        Ok(output) => output,
        Err(error)
            if !dregg_lean_ffi::test_require_lean()
                && error.contains("not exported by the linked archive") =>
        {
            eprintln!("SKIP: non-strict developer archive predates the safe handler export");
            return;
        }
        Err(error) => panic!("safe handler export must be linked: {error}"),
    };
    assert!(
        genuine.contains("\"status\":2") && genuine.contains("\"ok\":1"),
        "the genuine handler turn must body-commit: {genuine}"
    );

    let forged = GENUINE_WIRE.replacen(
        "0000000000000000000000000000000000000000000000000000000000000007\",7]",
        "0000000000000000000000000000000000000000000000000000000000000007\",8]",
        1,
    );
    let refused = dregg_lean_ffi::shadow_exec_handler_turn(&forged)
        .expect("the forged wire must execute to a fail-closed verdict");
    assert!(
        refused.contains("\"status\":1") && refused.contains("\"ok\":0"),
        "a forged node credential must never body-commit through the handler export: {refused}"
    );
}
