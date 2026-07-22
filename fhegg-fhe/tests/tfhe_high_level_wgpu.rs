//! Actual high-level tfhe-rs `FheUint32` weld for the deployed KS->PBS order.

use std::time::Instant;

use fhegg_fhe::tfhe_high_level_wgpu::prepare_fhe_uint32_ks_pbs_transform_wgpu_plan;
use fhegg_fhe::tfhe_wgpu::{TorusMacBackend, TorusWgpuAlgorithm};
use tfhe::integer::IntegerCiphertext;
use tfhe::prelude::*;
use tfhe::{set_server_key, ClientKey, CompressedServerKey, ConfigBuilder, FheUint32};

#[test]
fn deployed_fhe_uint32_block_lut_matches_tfhe_and_remains_high_level_usable() {
    if std::env::var_os("DREGG_REQUIRE_WGPU").is_none() {
        eprintln!("set DREGG_REQUIRE_WGPU=1 to run the deployed high-level GPU PBS gate");
        return;
    }

    let client = ClientKey::generate(ConfigBuilder::default());
    let compressed = CompressedServerKey::new(&client);
    let server = compressed.decompress();
    let shortint_server: &tfhe::shortint::ServerKey = server.as_ref().as_ref();
    let lookup = shortint_server.generate_lookup_table(|value| (value % 4 + 1) % 4);
    let prepare_started = Instant::now();
    let plan = prepare_fhe_uint32_ks_pbs_transform_wgpu_plan(&compressed).unwrap();
    let prepare_time = prepare_started.elapsed();

    let clear = 0x1234_5678u32;
    let block_index = 3usize;
    let input = FheUint32::encrypt(clear, &client);

    let (mut oracle_radix, oracle_id, oracle_tag, oracle_rerandomization) =
        input.clone().into_raw_parts();
    let oracle_block =
        shortint_server.apply_lookup_table(&oracle_radix.blocks()[block_index], &lookup);
    oracle_radix.blocks_mut()[block_index] = oracle_block;
    let oracle =
        FheUint32::from_raw_parts(oracle_radix, oracle_id, oracle_tag, oracle_rerandomization);

    let gpu_started = Instant::now();
    let (gpu, backend) = plan
        .apply_lookup_table_to_block(&input, block_index, &lookup)
        .unwrap();
    let gpu_time = gpu_started.elapsed();
    assert!(matches!(
        backend,
        TorusMacBackend::Wgpu {
            algorithm: TorusWgpuAlgorithm::ExactTransformResidentPbs,
            ..
        }
    ));
    let oracle_clear: u32 = oracle.decrypt(&client);
    let gpu_clear: u32 = gpu.decrypt(&client);
    assert_eq!(gpu_clear, oracle_clear);
    eprintln!(
        "high-level KS->transform-PBS: prepare={:.3}ms block-LUT={:.3}ms backend={backend:?}",
        prepare_time.as_secs_f64() * 1_000.0,
        gpu_time.as_secs_f64() * 1_000.0,
    );

    // The output is not a private shortint side object: it remains a normal
    // large-key high-level value accepted by the deployed server key.
    set_server_key(server);
    let one = FheUint32::encrypt(1u32, &client);
    let advanced = &gpu + &one;
    let advanced_clear: u32 = advanced.decrypt(&client);
    assert_eq!(advanced_clear, oracle_clear + 1);
}
