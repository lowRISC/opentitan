// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use hmac::{Hmac, Mac};
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use anyhow::{Result, bail};
use arrayvec::ArrayVec;
use zerocopy::IntoBytes;

use bindgen::sram_program::SRAM_MAGIC_SP_EXECUTION_DONE;
use cert_lib::{CaConfig, CaKey, EndorsedCert, parse_and_endorse_x509_cert, validate_cert_chain};
use ft_ext_lib::ft_ext;
use opentitanlib::app::{TransportWrapper, UartRx};
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::io::console::ConsoleError;
use opentitanlib::io::gpio::{PinMode, PullMode};
use opentitanlib::io::jtag::{JtagParams, JtagTap, RiscvGpr, RiscvReg};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;
use ot_certs::CertFormat;
use ot_certs::x509::parse_certificate;
use ot_hal::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use perso_tlv_lib::perso_tlv_get_field;
use perso_tlv_lib::{CertHeader, CertHeaderType, ObjHeader, ObjHeaderType, ObjType};
use ujson_lib::UjsonPayloads;
use ujson_lib::provisioning_data::{
    LcTokenHash, ManufCertgenInputs, ManufFtIndividualizeData, PersoBlob, SerdesSha256Hash,
};
use util_lib::hash_lc_token;

pub mod response;
use response::*;

pub fn test_unlock(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    test_unlock_token: &ArrayVec<u32, 4>,
) -> Result<()> {
    // Connect to LC TAP.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset(UartRx::Clear)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_LOCKED0`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestLocked0.redundant_encoding());

    // ROM execution is not yet enabled in OTP so we can safely reconnect to the LC TAP after
    // the transition without risking the chip resetting.
    trigger_lc_transition(
        transport,
        jtag,
        DifLcCtrlState::TestUnlocked1,
        Some(test_unlock_token.clone().into_inner().unwrap()),
        /*use_external_clk=*/
        false, // AST will be calibrated by now, so no need for ext_clk.
        /*reset_tap_straps=*/ Some(JtagTap::LcTap),
    )?;

    jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;

    // Check that LC state has transitioned to `TestUnlocked1`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked1.redundant_encoding());

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn run_sram_ft_individualize(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    sram_program: &SramProgramParams,
    ft_individualize_data_in: &ManufFtIndividualizeData,
    console_spi: &str,
    console_tx_indicator_pin: &str,
    timeout: Duration,
    ujson_payloads: &mut UjsonPayloads,
) -> Result<()> {
    // Setup the SPI console with the GPIO TX indicator pin.
    let spi = transport.spi(console_spi)?;
    let device_console_tx_ready_pin = &transport.gpio_pin(console_tx_indicator_pin)?;
    device_console_tx_ready_pin.set_mode(PinMode::Input)?;
    device_console_tx_ready_pin.set_pull_mode(PullMode::None)?;
    let spi_console = SpiConsoleDevice::new(&*spi, Some(device_console_tx_ready_pin))?;

    // Set CPU TAP straps, reset, and connect to the JTAG interface.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset(UartRx::Clear)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = sram_program.load_and_execute(&mut *jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Wait for SRAM program to complete execution.
    let _ = UartConsole::wait_for(
        &spi_console,
        r"Waiting for FT SRAM provisioning data ...",
        timeout,
    )?;

    // Inject provisioning data into the device.
    ujson_payloads.dut_in.insert(
        "FT_INDIVIDUALIZE_DATA_IN".to_string(),
        ft_individualize_data_in.send(&spi_console)?,
    );

    // Wait for provisioning operations to complete.
    jtag.wait_halt(timeout)?;
    jtag.halt()?;
    let sp = jtag.read_riscv_reg(&RiscvReg::Gpr(RiscvGpr::SP))?;
    log::info!("after timeout, sp = {:x}", sp);
    match sp {
        SRAM_MAGIC_SP_EXECUTION_DONE => {}
        _ => panic!("SRAM program load/execution failed: sp = {:?}.", sp),
    }

    // Switch TAP straps to LC TAP (without resetting) to aid debugging if there are OTP issues.
    // TAP straps are continuously sampled in TEST_UNLOCKED* LC states.
    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;

    Ok(())
}

pub fn test_exit(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    test_exit_token: &ArrayVec<u32, 4>,
    target_mission_mode_lc_state: DifLcCtrlState,
) -> Result<()> {
    // Connect to LC TAP.
    //
    // We purposely DO NOT reset the chip here, as the FT provisioning SRAM progam that was just
    // executed should have unlocked ROM execution and halted the CPU already. If we reset the
    // chip, the ROM will attempt to boot the flash image, which we do not want to do until we
    // transition to a mission mode state. We do not need to reset the chip to switch TAPs because
    // TAP straps are continuously sampled in TEST_UNLOCKED* LC state.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::LcTap)?;

    // Check that LC state is currently `TEST_UNLOCKED*`.
    let state =
        DifLcCtrlState::from_redundant_encoding(jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?)?;
    match state {
        DifLcCtrlState::TestUnlocked0
        | DifLcCtrlState::TestUnlocked1
        | DifLcCtrlState::TestUnlocked2
        | DifLcCtrlState::TestUnlocked3
        | DifLcCtrlState::TestUnlocked4
        | DifLcCtrlState::TestUnlocked5
        | DifLcCtrlState::TestUnlocked6
        | DifLcCtrlState::TestUnlocked7 => {
            log::info!("Starting test exit LC transition ...")
        }
        _ => panic!(
            "Cannot perform test exit LC transition from {:x?} LC state.",
            state
        ),
    }

    // ROM execution should now be enabled in OTP so we cannot safely reconnect to the LC TAP after
    // the transition without risking the chip resetting. Therefore, it is the responsibility of the
    // flash program that is subsequently bootstrapped / run to check the LC state is as expected.
    trigger_lc_transition(
        transport,
        jtag,
        target_mission_mode_lc_state,
        Some(test_exit_token.clone().into_inner().unwrap()),
        /*use_external_clk=*/
        false, // AST will be calibrated by now, so no need for ext_clk.
        /*reset_tap_straps=*/ None,
    )?;

    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

fn send_rma_unlock_token_hash(
    rma_unlock_token: &ArrayVec<u32, 4>,
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    ujson_payloads: &mut UjsonPayloads,
) -> Result<()> {
    let rma_token_hash = LcTokenHash {
        hash: hash_lc_token(rma_unlock_token.as_bytes())?,
    };

    // Wait for test to start running.
    let _ = UartConsole::wait_for(
        spi_console,
        r"Waiting For RMA Unlock Token Hash ...",
        timeout,
    )?;
    ujson_payloads.dut_in.insert(
        "FT_PERSO_RMA_TOKEN_HASH".to_string(),
        rma_token_hash.send_with_crc(spi_console)?,
    );
    Ok(())
}

// Extract LTV object header from the input buffer.
fn get_obj_header(data: &[u8]) -> Result<ObjHeader> {
    let header_len = std::mem::size_of::<ObjHeaderType>();
    // The header is 2 bytes in size.
    if data.len() < header_len {
        bail!(
            "Insufficient amount of data ({} bytes) for object header",
            data.len()
        );
    }

    let typesize = u16::from_be_bytes([data[0], data[1]]);
    let obj_size = perso_tlv_get_field!("obj", "size", typesize);
    let obj_type = ObjType::from_usize(perso_tlv_get_field!("obj", "type", typesize))?;

    if obj_size > data.len() {
        bail!(
            "Object {} length {} exceeds buffer size {}",
            obj_type as u8,
            obj_size,
            data.len()
        );
    }
    Ok(ObjHeader { obj_type, obj_size })
}

// Extract certificate payload header from the input buffer.
fn get_cert(data: &[u8]) -> Result<CertHeader<'_>> {
    let header_len = std::mem::size_of::<CertHeaderType>();

    if data.len() < header_len {
        bail!(
            "Insufficient amount of data ({} bytes) for cert header",
            data.len()
        );
    }

    let header = u16::from_be_bytes([data[0], data[1]]);
    let wrapped_size = perso_tlv_get_field!("crth", "size", header);
    if wrapped_size > data.len() {
        bail!(
            "Cert object size {} exceeds buffer size {}",
            wrapped_size,
            data.len()
        );
    }

    let name_len = perso_tlv_get_field!("crth", "name", header);
    let cert_name = std::str::from_utf8(&data[header_len..header_len + name_len])?;
    log::info!("processing cert {cert_name}");
    let header_size = header_len + name_len;
    let cert_body: Vec<u8> = data[header_size..wrapped_size].to_vec();

    Ok(CertHeader {
        wrapped_size,
        cert_name,
        cert_body,
    })
}

fn push_endorsed_cert(
    cert: &Vec<u8>,
    ref_cert: &CertHeader,
    output: &mut ArrayVec<u8, 4096>,
) -> Result<()> {
    // Need to wrap the new cert in CertHeader
    let total_size = std::mem::size_of::<ObjHeaderType>()
        + std::mem::size_of::<CertHeaderType>()
        + ref_cert.cert_name.len()
        + cert.len();

    let obj_header = perso_tlv_lib::make_obj_header(total_size, ObjType::EndorsedX509Cert)?;
    let cert_wrapper_header =
        perso_tlv_lib::make_cert_wrapper_header(cert.len(), ref_cert.cert_name)?;
    output.try_extend_from_slice(&obj_header.to_be_bytes())?;
    output.try_extend_from_slice(&cert_wrapper_header.to_be_bytes())?;
    output.try_extend_from_slice(ref_cert.cert_name.as_bytes())?;
    output.try_extend_from_slice(cert.as_slice())?;

    Ok(())
}

fn process_dev_seeds(seeds: &[u8]) -> Result<Vec<Vec<u8>>> {
    let expected_seed_num = 2usize;
    let seed_size = 64usize;
    let mut response = Vec::new();

    if seeds.len() != seed_size * expected_seed_num {
        bail!("Unexpected seeds perso object size {}", seeds.len())
    }

    for i in 0..expected_seed_num {
        let seed = &seeds[i * seed_size..(i + 1) * seed_size];
        response.push(seed.to_vec());
        log::info!("Seed #{}: {}", i, hex::encode(seed))
    }
    Ok(response)
}

#[allow(clippy::too_many_arguments)]
fn provision_certificates(
    wafer_auth_secret: &ArrayVec<u8, 32>,
    ca_cfgs: HashMap<String, CaConfig>,
    ca_keys: HashMap<String, CaKey>,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
    ujson_payloads: &mut UjsonPayloads,
    response: &mut PersonalizeResponse,
) -> Result<()> {
    // Send attestation TCB measurements for generating DICE certificates.
    let t0 = Instant::now();
    let _ = UartConsole::wait_for(spi_console, r"Waiting for certificate inputs ...", timeout)?;
    response.stats.log_elapsed_time("perso-wait-ready", t0);

    let t0 = Instant::now();
    ujson_payloads.dut_in.insert(
        "FT_PERSO_CERTGEN_INPUTS".to_string(),
        perso_certgen_inputs.send(spi_console)?,
    );
    response.stats.log_elapsed_time("perso-certgen-inputs", t0);

    // Wait until the device exports the TBS certificates.
    let t0 = Instant::now();
    let _ = UartConsole::wait_for(spi_console, r"Exporting TBS certificates ...", timeout)?;
    let perso_blob = PersoBlob::recv(spi_console, timeout, true)?;
    response.stats.log_elapsed_time("perso-tbs-export", t0);

    // Extract certificate byte vectors, endorse TBS certs, and ensure they parse with OpenSSL.
    // During the process:
    //   1. prepare a UJSON payload of endorsed certs to send back to the device,
    //   2. collect the TBS certs to HMAC them with the WAS,
    //   3. collect the certs that were endorsed to verify their endorsement signatures with OpenSSL, and
    //   4. hash all certs to check the integrity of what gets written back to the device.
    let mut cert_hasher = Sha256::new();
    let mut start: usize = 0;
    let mut dice_cert_chain: Vec<EndorsedCert> = Vec::new();
    let mut sku_specific_certs: Vec<EndorsedCert> = Vec::new();
    let mut num_host_endorsed_certs = 0;
    let mut endorsed_cert_concat = ArrayVec::<u8, 4096>::new();
    let mut device_was_hmac: Vec<u8> = Vec::new();
    let mut device_id: Vec<u8> = Vec::new();
    let mut host_was_hmac = Hmac::<Sha256>::new_from_slice(wafer_auth_secret.as_slice())?;

    // Extract CAs.
    let dice_ca_cert = &ca_cfgs["dice"].certificate;
    let dice_ca_key = &ca_keys["dice"];

    // DICE certificate names.
    let dice_cert_names = HashSet::from(["UDS", "CDI_0", "CDI_1"]);

    let t0 = Instant::now();
    for _ in 0..perso_blob.num_objs {
        log::info!("Processing next object");
        let header = get_obj_header(&perso_blob.body[start..])?;
        let obj_header_size = std::mem::size_of::<ObjHeaderType>();

        if header.obj_size > (perso_blob.body.len() - start) {
            bail!("Perso blob overflow!");
        }
        start += obj_header_size;
        match header.obj_type {
            ObjType::EndorsedX509Cert | ObjType::UnendorsedX509Cert | ObjType::EndorsedCwtCert => {}
            ObjType::WasTbsHmac => {
                let was_tbs_hmac_size = header.obj_size - obj_header_size;
                device_was_hmac
                    .extend_from_slice(&perso_blob.body[start..start + was_tbs_hmac_size]);
                start += was_tbs_hmac_size;
                continue;
            }
            ObjType::DeviceId => {
                let device_id_size = header.obj_size - obj_header_size;
                device_id.extend_from_slice(&perso_blob.body[start..start + device_id_size]);
                start += device_id_size;
                continue;
            }
            ObjType::DevSeed => {
                let dev_seed_size = header.obj_size - obj_header_size;
                let seeds = &perso_blob.body[start..start + dev_seed_size];
                cert_hasher.update(seeds);
                let r = process_dev_seeds(seeds)?;
                start += dev_seed_size;
                response.seeds.number += r.len();
                response.seeds.seed.extend(r);
                continue;
            }
        }

        // The next object is a cert, let's retrieve its properties (name, needs
        // endorsement, etc.)
        let cert = get_cert(&perso_blob.body[start..])?;
        start += cert.wrapped_size;

        // Extract the certificate bytes and endorse the cert if needed.
        let cert_bytes = if header.obj_type == ObjType::UnendorsedX509Cert {
            host_was_hmac.update(cert.cert_body.as_slice());
            // Endorse the cert and updates its size.
            let cert_bytes = if dice_cert_names.contains(cert.cert_name) {
                parse_and_endorse_x509_cert(cert.cert_body.clone(), dice_ca_key)?
            } else {
                let ext_ca_key = &ca_keys["ext"];
                parse_and_endorse_x509_cert(cert.cert_body.clone(), ext_ca_key)?
            };

            // Prepare a collection of (SKU-specific) certs whose endorsements should be verified.
            if !dice_cert_names.contains(cert.cert_name) {
                let ec = EndorsedCert {
                    format: CertFormat::X509,
                    name: cert.cert_name.to_string(),
                    bytes: cert_bytes.clone(),
                    ignore_critical: false,
                };
                response.certs.insert(ec.name.clone(), ec.clone());
                sku_specific_certs.push(ec);
            }

            // Prepare the UJSON data payloads that will be sent back to the device.
            push_endorsed_cert(&cert_bytes, &cert, &mut endorsed_cert_concat)?;
            num_host_endorsed_certs += 1;
            cert_bytes
        } else {
            cert.cert_body
        };

        // Collect all DICE certs to validate the chain.
        // TODO(lowRISC/opentitan:#24281): Add CWT verifier
        if dice_cert_names.contains(cert.cert_name)
            && header.obj_type == ObjType::UnendorsedX509Cert
        {
            let ec = EndorsedCert {
                format: CertFormat::X509,
                name: cert.cert_name.to_string(),
                bytes: cert_bytes.clone(),
                ignore_critical: true,
            };
            response.certs.insert(ec.name.clone(), ec.clone());
            dice_cert_chain.push(ec);
        }

        // Ensure all certs parse with OpenSSL (even those that where endorsed on device).
        log::info!("{} Cert: {}", cert.cert_name, hex::encode(&cert_bytes));
        // TODO(lowRISC/opentitan:#24281): Add CWT parser
        if header.obj_type != ObjType::DevSeed && header.obj_type != ObjType::EndorsedCwtCert {
            let _ = parse_certificate(&cert_bytes)?;
        }
        // Push the cert into the hasher so we can ensure the certs written to the device's flash
        // info pages match those verified on the host.
        cert_hasher.update(cert_bytes);
    }
    response.stats.log_elapsed_time("perso-process-blobs", t0);

    // Execute extension hook.
    let t0 = Instant::now();
    endorsed_cert_concat = ft_ext(endorsed_cert_concat)?;
    response.stats.log_elapsed_time("perso-ft-ext", t0);

    // Authenticate WAS HMAC.
    let host_was_hmac_bytes = host_was_hmac.finalize().into_bytes();
    assert_eq!(host_was_hmac_bytes[..], device_was_hmac[..]);

    // Complete hash of all certs that will be sent back to the device and written to flash. This
    // is used as integrity check on what will be written to flash.
    let host_computed_certs_hash = cert_hasher.finalize();

    // Send endorsed certificates back to the device.
    let manuf_perso_data_back = PersoBlob {
        num_objs: num_host_endorsed_certs,
        next_free: endorsed_cert_concat.len(),
        body: endorsed_cert_concat,
    };
    let t0 = Instant::now();
    let _ = UartConsole::wait_for(spi_console, r"Importing endorsed certificates ...", timeout)?;
    ujson_payloads.dut_in.insert(
        "FT_PERSO_DATA_IN".to_string(),
        manuf_perso_data_back.send(spi_console)?,
    );
    let _ = UartConsole::wait_for(spi_console, r"Finished importing certificates.", timeout)?;
    response.stats.log_elapsed_time("perso-import-certs", t0);

    // Check the integrity of the certificates written to the device's flash by comparing a
    // SHA256 over all certificates computed on the host and device sides.
    let device_computed_certs_hash = SerdesSha256Hash::recv(spi_console, timeout, false)?;
    if !device_computed_certs_hash
        .data
        .as_bytes()
        .iter()
        .rev()
        .zip(host_computed_certs_hash.iter())
        .all(|(a, b)| a == b)
    {
        bail!(
            "Host ({:x?}) vs Device ({:x?}) certs hash mismatch.",
            host_computed_certs_hash.as_bytes(),
            device_computed_certs_hash.data.as_bytes()
        )
    }

    // Validate the certificate endorsements with OpenSSL.
    // TODO(lowRISC/opentitan:#24281): Add CWT verifier
    let t0 = Instant::now();
    if !dice_cert_chain.is_empty() {
        log::info!(
            "Validating DICE certificate chain with OpenSSL (root CA: {:?}) ...",
            dice_ca_cert
        );
        validate_cert_chain(dice_ca_cert.to_str().unwrap(), &dice_cert_chain)?;
        log::info!("Success.");
    }
    response.stats.log_elapsed_time("perso-validate-dice", t0);

    let t0 = Instant::now();
    if !sku_specific_certs.is_empty() {
        let ext_ca_cert = &ca_cfgs["ext"].certificate;
        log::info!(
            "Validating SKU-specific certificates with OpenSSL (root CA: {:?}) ...",
            ext_ca_cert
        );
        for sku_specific_cert in sku_specific_certs.iter() {
            validate_cert_chain(
                ext_ca_cert.to_str().unwrap(),
                std::slice::from_ref(sku_specific_cert),
            )?;
        }
        log::info!("Success.");
    }
    response.stats.log_elapsed_time("perso-validate-sku", t0);
    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    wafer_auth_secret: &ArrayVec<u8, 32>,
    rma_unlock_token: &ArrayVec<u32, 4>,
    ca_cfgs: HashMap<String, CaConfig>,
    ca_keys: HashMap<String, CaKey>,
    perso_certgen_inputs: &ManufCertgenInputs,
    second_bootstrap: PathBuf,
    spi_console: &SpiConsoleDevice,
    ujson_payloads: &mut UjsonPayloads,
    timeout: Duration,
    response: &mut PersonalizeResponse,
) -> Result<()> {
    // Bootstrap only personalization binary into ROM_EXT slot A in flash.
    let t0 = Instant::now();
    init.bootstrap.init(transport)?;
    response.stats.log_elapsed_time("first-bootstrap", t0);

    // Bootstrap personalization + ROM_EXT + Owner FW binaries into flash, since
    // flash scrambling seeds were provisioned in the previous step.
    let t0 = Instant::now();
    let _ = UartConsole::wait_for(spi_console, r"Bootstrap requested.", timeout)?;
    response.stats.log_elapsed_time("first-bootstrap-done", t0);

    let t0 = Instant::now();
    init.bootstrap.load(transport, &second_bootstrap)?;
    response.stats.log_elapsed_time("second-bootstrap", t0);

    // Send RMA unlock token digest to device.
    let second_t0 = Instant::now();
    let t0 = second_t0;
    send_rma_unlock_token_hash(rma_unlock_token, timeout, spi_console, ujson_payloads)?;
    response.stats.log_elapsed_time("send-rma-unlock-token", t0);

    // Provision all device certificates.
    let t0 = Instant::now();
    provision_certificates(
        wafer_auth_secret,
        ca_cfgs,
        ca_keys,
        perso_certgen_inputs,
        timeout,
        spi_console,
        ujson_payloads,
        response,
    )?;
    response.stats.log_elapsed_time("perso-all-certs-done", t0);

    let _ = UartConsole::wait_for(spi_console, r"Personalization done.", timeout)?;
    response
        .stats
        .log_elapsed_time("second-bootstrap-done", second_t0);
    Ok(())
}

pub fn check_slot_b_boot_up(
    transport: &TransportWrapper,
    timeout: Duration,
    response: &mut PersonalizeResponse,
    owner_fw_success_string: Option<String>,
) -> Result<()> {
    transport.reset(UartRx::Clear)?;
    let uart_console = transport.uart("console")?;
    let result = UartConsole::wait_for(&*uart_console, r"ROM_EXT:(.*)\r", timeout)?;
    log::info!("ROM_EXT started.");
    response.stats.log_string(
        "rom_ext-version",
        result
            .get(1)
            .as_ref()
            .map(|s| s.as_str())
            .unwrap_or("unknown"),
    );

    let t0 = Instant::now();

    // Timeout for waiting for a potential error message indicating invalid UDS
    // certificate or for the Owner firmware successful startup.
    //
    // These values were tested on fpga cw340 and could be potentially fine-tuned.
    let slot_b_startup_timeout: Duration =
        Duration::from_millis(if owner_fw_success_string.is_none() {
            800
        } else {
            2000
        });

    response.stats.log_elapsed_time("rom_ext-done", t0);

    // CAUTION: This error message should match the one in
    //   //sw/device/silicon_creator/lib/cert/dice_chain.c.
    let rom_ext_failure_msg = r"UDS certificate not valid";

    let error_code_msg = r"BFV:.*\r\n";

    let anchor_text = if let Some(owner_anchor) = &owner_fw_success_string {
        format!(
            r"(?s)({}|{}|{})",
            rom_ext_failure_msg, error_code_msg, owner_anchor
        )
    } else {
        format!(r"(?s)({}|{})", rom_ext_failure_msg, error_code_msg)
    };

    let result =
        UartConsole::wait_for(&*uart_console, anchor_text.as_str(), slot_b_startup_timeout);

    match result {
        Ok(captures) => {
            if captures[0] == *rom_ext_failure_msg {
                bail!("Invalid UDS certificate detected!");
            }
            if captures[0].starts_with("BFV:") {
                bail!("Error detected!");
            }
        }
        Err(e) => {
            if owner_fw_success_string.is_none()
                && matches!(
                    e.downcast_ref::<ConsoleError>(),
                    Some(ConsoleError::TimedOut)
                )
            {
                // Error message not found after timeout. This is the expected behavior.
            } else {
                // An unexpected error occurred while waiting for the console output.
                bail!(e);
            }
        }
    }

    Ok(())
}
