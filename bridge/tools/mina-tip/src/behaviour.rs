// Vendored from `~/dev/mina-rust/tools/bootstrap-sandbox/src/behaviour.rs`.
// The combined libp2p NetworkBehaviour: openmina's Janestreet-RPC-over-libp2p
// behaviour plus `identify` (Mina peers expect an identify exchange). Unchanged
// in substance — this is openmina's own wiring, linked, not reimplemented.

use libp2p_rpc_behaviour::Behaviour as RpcBehaviour;

use libp2p::{swarm::NetworkBehaviour, PeerId};

#[derive(NetworkBehaviour)]
#[behaviour(to_swarm = "Event")]
pub struct Behaviour {
    pub rpc: RpcBehaviour,
    pub identify: libp2p::identify::Behaviour,
}

pub enum Event {
    Rpc((PeerId, libp2p_rpc_behaviour::Event)),
    Identify,
}

impl From<(PeerId, libp2p_rpc_behaviour::Event)> for Event {
    fn from(value: (PeerId, libp2p_rpc_behaviour::Event)) -> Self {
        Self::Rpc(value)
    }
}

impl From<libp2p::identify::Event> for Event {
    fn from(_value: libp2p::identify::Event) -> Self {
        // ignore, it is irrelevant
        Self::Identify
    }
}
