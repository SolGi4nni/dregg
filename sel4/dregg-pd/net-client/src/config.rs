//
// net-client config — channel ids + shared-region sizes, mirroring the driver's
// half (../net/src/config.rs) and the net-full.system assembly.
//

pub mod channels {
    use sel4_microkit::Channel;

    /// The driver PD. In net-full.system / dregg.system this client's `id=0` end
    /// binds to the driver's `id=1` end (the driver's CLIENT channel).
    /// Notifications both ways crank the ring buffers; the protected (PPC)
    /// direction fetches the MAC via sel4-microkit-simple-ipc.
    pub const DRIVER: Channel = Channel::new(0);

    /// The executor PD (dregg.system only). This client's `id=1` end binds the
    /// executor's `id=1` end (NET_TO_EXECUTOR). After an arriving SignedTurn
    /// passes the Ed25519 gate AND its message is staged into turn_in, the client
    /// notifies the executor on this channel — "a signature-checked turn is staged
    /// in turn_in". In net-full.system (no executor PD) this channel is absent and
    /// the staging path is a no-op (the gate still replies over the wire).
    #[cfg_attr(not(feature = "executor-ingress"), allow(dead_code))]
    pub const EXECUTOR: Channel = Channel::new(1);
}

/// The shared DMA region the driver copies RX frames into / TX frames out of.
/// Must match the driver's VIRTIO_NET_CLIENT_DMA_SIZE.
pub const VIRTIO_NET_CLIENT_DMA_SIZE: usize = 0x200_000;

/// The turn_in handoff region (dregg.system `<memory_region turn_in size=0x100000>`)
/// the ingress edge stages a verified turn into for the executor. Mapped RW here
/// (the executor maps it R). The staged framing is: a 4-byte LE length prefix +
/// the verified turn message bytes — exactly what the executor's
/// `run_turn_from_turn_in` reads.
#[cfg_attr(not(feature = "executor-ingress"), allow(dead_code))]
pub const TURN_IN_SIZE: usize = 0x100_000;

/// The TCP port the echo + SignedTurn-admission listener binds. Reached from the
/// host via `-netdev user,hostfwd=tcp::5555-:5555`.
pub const ECHO_PORT: u16 = 5555;
