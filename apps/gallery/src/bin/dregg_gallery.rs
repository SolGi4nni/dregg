//! Standalone dregg-gallery server binary.
//!
//! Uses the shared `AppServer` from `dregg-app-framework` for standard
//! middleware (health, CORS, admin auth) and environment-based configuration.

use clap::Parser;
use dregg_app_framework::server::AppConfig;
use dregg_gallery::server::start_server;

#[derive(Parser)]
#[command(name = "dregg-gallery", about = "Federated art gallery server")]
struct Cli {
    /// Listen address (host:port).
    #[arg(long, default_value = "0.0.0.0:3040")]
    listen: String,

    /// Path to frontend static files directory.
    #[arg(long, default_value = "frontend")]
    frontend: String,

    /// Node API URL for the backing dregg node.
    #[arg(long, env = "DREGG_NODE_URL", default_value = "http://node-0:8420")]
    node_url: String,

    /// Path to state persistence file (JSON). State is saved on mutations and
    /// restored on startup.
    #[arg(long, env = "DREGG_STATE_FILE", default_value = "gallery_state.json")]
    state_file: String,
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();

    let cli = Cli::parse();

    let config = AppConfig::from_env()
        .with_listen(&cli.listen)
        .with_state_file(&cli.state_file);

    let addr = start_server(config, Some(cli.frontend)).await;
    tracing::info!(%addr, node_url = %cli.node_url, "gallery server running");

    // Block forever (server runs in background task).
    std::future::pending::<()>().await;
}
