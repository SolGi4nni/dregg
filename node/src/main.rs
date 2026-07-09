//! `dregg-node`: the federation node daemon binary.
//!
//! This is a thin entry point over the `dregg_node` library (`src/lib.rs`). It
//! parses the CLI and hands off to [`dregg_node::run`]; all of the node's logic
//! — the HTTP API, consensus, the executor cluster, the MCP server, the operator
//! onboarding dance, etc. — lives in the library, where the module surface is
//! legitimately public.

use clap::Parser;
use dregg_node::Cli;

#[tokio::main]
async fn main() {
    dregg_node::run(Cli::parse()).await;
}
