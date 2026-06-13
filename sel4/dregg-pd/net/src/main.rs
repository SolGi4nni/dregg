//
// Copyright 2023, Colias Group, LLC
//
// SPDX-License-Identifier: BSD-2-Clause
//

#![no_std]
#![no_main]

use core::ptr::NonNull;

use virtio_drivers::{
    device::net::*,
    transport::{
        DeviceType, Transport,
        mmio::{MmioTransport, VirtIOHeader},
    },
};

use sel4_microkit::{debug_println, memory_region_symbol, protection_domain, var};
use sel4_microkit_driver_adapters::net::driver::HandlerImpl;
use sel4_shared_memory::SharedMemoryRef;
use sel4_shared_ring_buffer::{RingBuffers, roles::Use};
use sel4_virtio_hal_impl::HalImpl;
use sel4_virtio_net::DeviceWrapper;

mod config;

use config::channels;

const NET_QUEUE_SIZE: usize = 16;
const NET_BUFFER_LEN: usize = 2048;

#[protection_domain(
    heap_size = 512 * 1024,
)]
fn init() -> HandlerImpl<DeviceWrapper<HalImpl, MmioTransport<'static>>> {
    HalImpl::init(
        config::VIRTIO_NET_DRIVER_DMA_SIZE,
        *var!(virtio_net_driver_dma_vaddr: usize = 0),
        *var!(virtio_net_driver_dma_paddr: usize = 0),
    );

    let mut dev = {
        let header = NonNull::new(
            (*var!(virtio_net_mmio_vaddr: usize = 0) + config::VIRTIO_NET_MMIO_OFFSET)
                as *mut VirtIOHeader,
        )
        .unwrap();
        let transport =
            unsafe { MmioTransport::new(header, config::VIRTIO_NET_MMIO_SIZE) }.unwrap();
        // The edge's first real probe (docs/FIRMAMENT.md §6, M3): we read the
        // virtio-mmio header at the slot QEMU placed `-device
        // virtio-net-device` into and confirm it is a NETWORK device — the
        // wall here used to be InvalidDeviceType(0) (an empty slot).
        debug_println!(
            "[net] virtio-mmio probe: version={:?} device_type={:?} vendor={:#x}",
            transport.version(),
            transport.device_type(),
            transport.vendor_id(),
        );
        assert_eq!(transport.device_type(), DeviceType::Network);
        let dev =
            VirtIONet::<HalImpl, MmioTransport, NET_QUEUE_SIZE>::new(transport, NET_BUFFER_LEN)
                .unwrap();
        debug_println!(
            "[net] virtio-net device UP — MAC {:02x?} — the firmament reached the wire",
            dev.mac_address()
        );
        dev
    };

    let client_region = unsafe {
        SharedMemoryRef::<'static, _>::new(
            memory_region_symbol!(virtio_net_client_dma_vaddr: *mut [u8], n = config::VIRTIO_NET_CLIENT_DMA_SIZE),
        )
    };

    let notify_client: fn() = || channels::CLIENT.notify();

    let rx_ring_buffers =
        RingBuffers::<'_, Use, fn()>::from_ptrs_using_default_initialization_strategy_for_role(
            unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_rx_free: *mut _)) },
            unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_rx_used: *mut _)) },
            notify_client,
        );

    let tx_ring_buffers =
        RingBuffers::<'_, Use, fn()>::from_ptrs_using_default_initialization_strategy_for_role(
            unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_tx_free: *mut _)) },
            unsafe { SharedMemoryRef::new(memory_region_symbol!(virtio_net_tx_used: *mut _)) },
            notify_client,
        );

    dev.ack_interrupt();
    channels::DEVICE.irq_ack().unwrap();

    HandlerImpl::new(
        DeviceWrapper::new(dev),
        client_region,
        rx_ring_buffers,
        tx_ring_buffers,
        channels::DEVICE,
        channels::CLIENT,
    )
}
