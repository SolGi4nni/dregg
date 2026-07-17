//! Throwaway helper: print the demo day's winning move sequence as JSON, so an
//! out-of-process HTTP driver can POST it to `/descent/submit` and exercise the
//! real anchor path. Reuses `dreggnet_web::demo_win()` (the same source the demo
//! seeding uses).
fn main() {
    let (moves, level, class) = dreggnet_web::demo_win();
    let out = serde_json::json!({
        "moves": moves,
        "level": level,
        "class": class,
    });
    println!("{}", serde_json::to_string(&out).unwrap());
}
