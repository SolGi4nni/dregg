//! Mint a dregg capability token to present to `pg-dregg` RLS / the write path.
//!
//! Minting holds the issuer SECRET, so it is a CLI/operator action, not a SQL
//! one (`dregg_mint` is deliberately out of the M1 SQL surface — `docs/PG-DREGG.md`
//! §5). This is the documented "tokens are minted in Rust and handed to SQL as
//! text" path: mint here, then `SET dregg.token = '<the dga1_… string>'` in psql.
//!
//! Run it:
//!
//! ```text
//! # an operator token that admits `read` and `submit` on every resource:
//! cargo run --example mint -- --seed 7 --action read --action submit --prefix ""
//!
//! # a token confined to ALICE's cell (hex prefix a1), read-only:
//! cargo run --example mint -- --seed 7 --action read --prefix a1
//! ```
//!
//! `--seed N` selects the issuer root `RootKey::from_seed([N; 32])`; its public
//! key is printed so you can set `dregg.issuer_pubkey` to match (the database
//! trust root). The token's caveats are `action ∈ {--action…}` (as an AnyOf when
//! several are given) AND `resource` has the `--prefix`.

use dregg_auth::credential::{Caveat, Pred, RootKey};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut seed: u8 = 7;
    let mut actions: Vec<String> = Vec::new();
    let mut prefix = String::new();
    let mut not_after: Option<u64> = None;

    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--seed" => {
                seed = args.get(i + 1).and_then(|s| s.parse().ok()).unwrap_or(7);
                i += 2;
            }
            "--action" => {
                if let Some(a) = args.get(i + 1) {
                    actions.push(a.clone());
                }
                i += 2;
            }
            "--prefix" => {
                prefix = args.get(i + 1).cloned().unwrap_or_default();
                i += 2;
            }
            "--not-after" => {
                not_after = args.get(i + 1).and_then(|s| s.parse().ok());
                i += 2;
            }
            other => {
                eprintln!("unknown arg: {other}");
                i += 1;
            }
        }
    }
    if actions.is_empty() {
        actions.push("read".into());
    }

    let root = RootKey::from_seed([seed; 32]);

    // action caveat: AttrEq for one action, AnyOf(AttrEq…) for several.
    let action_pred = if actions.len() == 1 {
        Pred::AttrEq {
            key: "action".into(),
            value: actions[0].clone(),
        }
    } else {
        Pred::AnyOf(
            actions
                .iter()
                .map(|a| Pred::AttrEq {
                    key: "action".into(),
                    value: a.clone(),
                })
                .collect(),
        )
    };

    let mut caveats = vec![
        Caveat::FirstParty(action_pred),
        Caveat::FirstParty(Pred::AttrPrefix {
            key: "resource".into(),
            prefix: prefix.clone(),
        }),
    ];
    if let Some(at) = not_after {
        caveats.push(Caveat::FirstParty(Pred::NotAfter { at }));
    }

    let token = root.mint(caveats).encode();

    eprintln!(
        "issuer pubkey (set dregg.issuer_pubkey to this): {}",
        root.public().to_hex()
    );
    eprintln!(
        "caveats: action ∈ {actions:?}, resource prefix = {prefix:?}{}",
        not_after
            .map(|a| format!(", not_after = {a}"))
            .unwrap_or_default()
    );
    // The token on stdout alone, so `TOK=$(cargo run -q --example mint …)` works.
    println!("{token}");
}
