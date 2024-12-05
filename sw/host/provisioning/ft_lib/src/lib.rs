// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::collections::HashSet;
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Result};
use arrayvec::ArrayVec;
use zerocopy::AsBytes;

use cert_lib::{parse_and_endorse_x509_cert, validate_cert_chain, CaConfig, CaKey, EndorsedCert};
use ft_ext_lib::ft_ext;
use opentitanlib::app::TransportWrapper;
use opentitanlib::console::spi::SpiConsoleDevice;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{ConsoleRecv, ConsoleSend};
use opentitanlib::uart::console::UartConsole;
use ot_certs::x509::parse_certificate;
use ot_certs::CertFormat;
use perso_tlv_lib::perso_tlv_get_field;
use perso_tlv_lib::{CertHeader, CertHeaderType, ObjHeader, ObjHeaderType, ObjType};
use ujson_lib::provisioning_data::{
    LcTokenHash, ManufCertgenInputs, ManufFtIndividualizeData, PersoBlob, SerdesSha256Hash,
};
use util_lib::hash_lc_token;

pub fn test_unlock(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
    test_unlock_token: &ArrayVec<u32, 4>,
) -> Result<()> {
    // Connect to LC TAP.
    transport.pin_strapping("PINMUX_TAP_LC")?.apply()?;
    transport.reset_target(reset_delay, true)?;
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
        reset_delay,
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

pub fn run_sram_ft_individualize(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
    sram_program: &SramProgramParams,
    ft_individualize_data_in: &ManufFtIndividualizeData,
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    // Set CPU TAP straps, reset, and connect to the JTAG interface.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(reset_delay, true)?;
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
        spi_console,
        r"Waiting for FT SRAM provisioning data ...",
        timeout,
    )?;

    // Inject provisioning data into the device.
    ft_individualize_data_in.send(spi_console)?;

    // Wait for provisioning operations to complete.
    let _ = UartConsole::wait_for(spi_console, r"FT SRAM provisioning done.", timeout)?;

    jtag.disconnect()?;
    transport.pin_strapping("PINMUX_TAP_RISCV")?.remove()?;

    Ok(())
}

pub fn test_exit(
    transport: &TransportWrapper,
    jtag_params: &JtagParams,
    reset_delay: Duration,
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

    // Check that LC state is currently `TEST_UNLOCKED1`.
    let state = jtag.read_lc_ctrl_reg(&LcCtrlReg::LcState)?;
    assert_eq!(state, DifLcCtrlState::TestUnlocked1.redundant_encoding());

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
        reset_delay,
        /*reset_tap_straps=*/ None,
    )?;

    transport.pin_strapping("PINMUX_TAP_LC")?.remove()?;

    Ok(())
}

fn send_rma_unlock_token_hash(
    rma_unlock_token: &ArrayVec<u32, 4>,
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
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
    rma_token_hash.send_with_crc(spi_console)?;
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
fn get_cert(data: &[u8]) -> Result<CertHeader> {
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

fn process_dev_seeds(seeds: &[u8]) -> Result<()> {
    let expected_seed_num = 2usize;
    let seed_size = 64usize;

    if seeds.len() != seed_size * expected_seed_num {
        bail!("Unexpected seeds perso object size {}", seeds.len())
    }

    for i in 0..expected_seed_num {
        let seed = &seeds[i * seed_size..(i + 1) * seed_size];

        log::info!("Seed #{}: {}", i, hex::encode(seed))
    }
    Ok(())
}

fn provision_certificates(
    ca_cfgs: HashMap<String, CaConfig>,
    ca_keys: HashMap<String, CaKey>,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
    spi_console: &SpiConsoleDevice,
) -> Result<()> {
    // Send attestation TCB measurements for generating DICE certificates.
    let _ = UartConsole::wait_for(spi_console, r"Waiting for certificate inputs ...", timeout)?;
    perso_certgen_inputs.send(spi_console)?;

    // Wait until the device exports the TBS certificates.
    let _ = UartConsole::wait_for(spi_console, r"Exporting TBS certificates ...", timeout)?;
    let perso_blob = PersoBlob::recv(spi_console, timeout, true)?;

    // Extract certificate byte vectors, endorse TBS certs, and ensure they parse with OpenSSL.
    // During the process, both:
    //   1. prepare a UJSON payload of endorsed certs to send back to the device,
    //   2. collect the certs that were endorsed to verify their endorsement signatures with OpenSSL, and
    //   3. hash all certs to check the integrity of what gets written back to the device.
    let mut cert_hasher = Sha256::new();
    let mut start: usize = 0;
    let mut dice_cert_chain: Vec<EndorsedCert> = Vec::new();
    let mut sku_specific_certs: Vec<EndorsedCert> = Vec::new();
    let mut num_host_endorsed_certs = 0;
    let mut endorsed_cert_concat = ArrayVec::<u8, 4096>::new();

    // Extract CAs.
    let dice_ca_cert = &ca_cfgs["dice"].certificate;
    let dice_ca_key = &ca_keys["dice"];
    let ext_ca_cert = &ca_cfgs["ext"].certificate;
    let ext_ca_key = &ca_keys["ext"];

    // DICE certificate names.
    let dice_cert_names = HashSet::from(["UDS", "CDI_0", "CDI_1"]);

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
            ObjType::DevSeed => {
                let dev_seed_size = header.obj_size - obj_header_size;
                let seeds = &perso_blob.body[start..start + dev_seed_size];
                cert_hasher.update(seeds);
                process_dev_seeds(seeds)?;
                start += dev_seed_size;
                continue;
            }
        }

        // The next object is a cert, let's retrieve its properties (name, needs
        // endorsement, etc.)
        let cert = get_cert(&perso_blob.body[start..])?;
        start += cert.wrapped_size;

        // Extract the certificate bytes and endorse the cert if needed.
        let cert_bytes = if header.obj_type == ObjType::UnendorsedX509Cert {
            // Endorse the cert and updates its size.
            let cert_bytes = if dice_cert_names.contains(cert.cert_name) {
                parse_and_endorse_x509_cert(cert.cert_body.clone(), dice_ca_key)?
            } else {
                parse_and_endorse_x509_cert(cert.cert_body.clone(), ext_ca_key)?
            };

            // Prepare a collection of (SKU-specific) certs whose endorsements should be verified.
            if !dice_cert_names.contains(cert.cert_name) {
                sku_specific_certs.push(EndorsedCert {
                    format: CertFormat::X509,
                    name: cert.cert_name.to_string(),
                    bytes: cert_bytes.clone(),
                    ignore_critical: false,
                });
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
            dice_cert_chain.push(EndorsedCert {
                format: CertFormat::X509,
                name: cert.cert_name.to_string(),
                bytes: cert_bytes.clone(),
                ignore_critical: true,
            });
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

    // Execute extension hook.
    endorsed_cert_concat = ft_ext(endorsed_cert_concat)?;

    // Complete hash of all certs that will be sent back to the device and written to flash. This
    // is used as integrity check on what will be written to flash.
    let host_computed_certs_hash = cert_hasher.finalize();

    // Send endorsed certificates back to the device.
    let manuf_perso_data_back = PersoBlob {
        num_objs: num_host_endorsed_certs,
        next_free: endorsed_cert_concat.len(),
        body: endorsed_cert_concat,
    };
    let _ = UartConsole::wait_for(spi_console, r"Importing endorsed certificates ...", timeout)?;
    manuf_perso_data_back.send(spi_console)?;
    let _ = UartConsole::wait_for(spi_console, r"Finished importing certificates.", timeout)?;

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
    log::info!("Validating DICE certificate chain with OpenSSL ...");
    validate_cert_chain(dice_ca_cert.to_str().unwrap(), &dice_cert_chain)?;
    log::info!("Success.");
    log::info!("Validating SKU-specific certificates with OpenSSL ...");
    if !sku_specific_certs.is_empty() {
        for sku_specific_cert in sku_specific_certs.iter() {
            validate_cert_chain(ext_ca_cert.to_str().unwrap(), &[sku_specific_cert.clone()])?;
        }
    }
    log::info!("Success.");

    Ok(())
}

#[allow(clippy::too_many_arguments)]
pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    rma_unlock_token: &ArrayVec<u32, 4>,
    ca_cfgs: HashMap<String, CaConfig>,
    ca_keys: HashMap<String, CaKey>,
    perso_certgen_inputs: &ManufCertgenInputs,
    second_bootstrap: PathBuf,
    spi_console: &SpiConsoleDevice,
    timeout: Duration,
) -> Result<()> {
    // Bootstrap only personalization binary into ROM_EXT slot A in flash.
    init.bootstrap.init(transport)?;

    // Bootstrap personalization + ROM_EXT + Owner FW binaries into flash, since
    // flash scrambling seeds were provisioned in the previous step.
    let _ = UartConsole::wait_for(spi_console, r"Bootstrap requested.", timeout)?;
    init.bootstrap.load(transport, &second_bootstrap)?;

    // Send RMA unlock token digest to device.
    send_rma_unlock_token_hash(rma_unlock_token, timeout, spi_console)?;

    // Provision all device certificates.
    provision_certificates(ca_cfgs, ca_keys, perso_certgen_inputs, timeout, spi_console)?;

    let _ = UartConsole::wait_for(spi_console, r"Personalization done.", timeout)?;

    Ok(())
}

pub fn check_rom_ext_boot_up(
    transport: &TransportWrapper,
    init: &InitializeTest,
    timeout: Duration,
) -> Result<()> {
    transport.reset_target(init.bootstrap.options.reset_delay, true)?;
    let uart_console = transport.uart("console")?;
    let _ = UartConsole::wait_for(&*uart_console, r"Starting ROM_EXT.*\r\n", timeout)?;

    // Timeout for waiting for a potential error message indicating invalid UDS certificate.
    // This value is tested on fpga cw340 and could be potentially fine-tuned.
    const UDS_CERT_INVALID_TIMEOUT: Duration = Duration::from_millis(200);

    let result = UartConsole::wait_for(
        &*uart_console,
        r".*UDS certificate not valid.",
        UDS_CERT_INVALID_TIMEOUT,
    );

    match result {
        Ok(_captures) => {
            // Error message found.
            bail!("Invalid UDS certificate detected!");
        }
        Err(e) => {
            if e.to_string().contains("Timed Out") {
                // Error message not found after timeout. This is the expected behavior.
            } else {
                // An unexpected error occurred while waiting for the console output.
                bail!(e);
            }
        }
    }

    Ok(())
}
