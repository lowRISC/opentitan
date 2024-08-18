// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sha2::{Digest, Sha256};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Result};
use arrayvec::ArrayVec;
use bindgen::perso_tlv_objects;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::SecretKey;
use p256::NistP256;
use zerocopy::AsBytes;

use cert_lib::{
    get_cert_size, parse_and_endorse_x509_cert, validate_certs_chain, CertEndorsementKey,
};
use ft_ext_lib::ft_ext;
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::perso_tlv;
use opentitanlib::perso_tlv::{CertHeader, CertHeaderType, ObjHeader, ObjHeaderType, ObjType};
use opentitanlib::perso_tlv_get_field;
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use ot_certs::x509::parse_certificate;
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
) -> Result<()> {
    // Set CPU TAP straps, reset, and connect to the JTAG interface.
    transport.pin_strapping("PINMUX_TAP_RISCV")?.apply()?;
    transport.reset_target(reset_delay, true)?;
    let mut jtag = jtag_params.create(transport)?.connect(JtagTap::RiscvTap)?;

    // Reset and halt the CPU to ensure we are in a known state, and clear out any ROM messages
    // printed over the console.
    jtag.reset(/*run=*/ false)?;
    let uart = transport.uart("console")?;
    uart.clear_rx_buffer()?;

    // Load and execute the SRAM program that contains the provisioning code.
    let result = sram_program.load_and_execute(&mut *jtag, ExecutionMode::Jump)?;
    match result {
        ExecutionResult::Executing => log::info!("SRAM program loaded and is executing."),
        _ => panic!("SRAM program load/execution failed: {:?}.", result),
    }

    // Get UART, set flow control, and wait for SRAM program to complete execution.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(
        &*uart,
        r"Waiting for FT SRAM provisioning data ...",
        timeout,
    )?;

    // Inject provisioning data into the device.
    ft_individualize_data_in.send(&*uart)?;

    // Wait for provisioning operations to complete.
    let _ = UartConsole::wait_for(&*uart, r"FT SRAM provisioning done.", timeout)?;

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

// This enum provides two different certificate signing key representations. In
// case the local fake certificate is used for certificate chain validation, the
// key is a path to the file containing the private key. In case a Cloud KMS
// certificate is used, the key is a string, the ID of the key in cloud storage.
pub enum KeyWrapper {
    LocalKey(PathBuf),
    CkmsKey(String),
}

fn send_rma_unlock_token_hash(
    transport: &TransportWrapper,
    rma_unlock_token_hash: &ArrayVec<u32, 4>,
    timeout: Duration,
) -> Result<()> {
    let uart = transport.uart("console")?;

    let rma_token_hash = LcTokenHash {
        hash: hash_lc_token(rma_unlock_token_hash.as_bytes())?,
    };

    // Get UART, set flow control, and wait for test to start running.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Waiting For RMA Unlock Token Hash ...", timeout)?;
    rma_token_hash.send_with_crc(&*uart)?;
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

    // Sanity check, total size and cert size must  match
    let cert_size = get_cert_size(&cert_body)?;
    if cert_size != cert_body.len() {
        bail!(
            "cert size {} does not match length {}",
            cert_size,
            cert_body.len()
        );
    }
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

    let obj_header = perso_tlv::make_obj_header(total_size, ObjType::EndorsedX509Cert)?;
    let cert_wrapper_header = perso_tlv::make_cert_wrapper_header(cert.len(), ref_cert.cert_name)?;
    output.try_extend_from_slice(&obj_header.to_be_bytes())?;
    output.try_extend_from_slice(&cert_wrapper_header.to_be_bytes())?;
    output.try_extend_from_slice(ref_cert.cert_name.as_bytes())?;
    output.try_extend_from_slice(cert.as_slice())?;

    Ok(())
}

fn provision_certificates(
    transport: &TransportWrapper,
    cert_endorsement_key_wrapper: KeyWrapper,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
    ca_certificate: PathBuf,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Send attestation TCB measurements for generating DICE certificates.
    let _ = UartConsole::wait_for(&*uart, r"Waiting for certificate inputs ...", timeout)?;
    perso_certgen_inputs.send(&*uart)?;

    // Wait until the device exports the TBS certificates.
    let _ = UartConsole::wait_for(&*uart, r"Exporting TBS certificates ...", timeout)?;
    let perso_blob = PersoBlob::recv(&*uart, timeout, true)?;

    // Select the CA endorsement key to use.
    let key = match cert_endorsement_key_wrapper {
        KeyWrapper::LocalKey(path) => {
            log::info!("Using local key for cert endorsement");
            CertEndorsementKey::LocalKey(SecretKey::<NistP256>::read_pkcs8_der_file(path)?)
        }
        KeyWrapper::CkmsKey(key_id) => {
            log::info!("Using Cloud KMS key for cert endorsement");
            CertEndorsementKey::CkmsKey(key_id)
        }
    };

    log::info!("start of the body {}", hex::encode(&perso_blob.body[0..10]));

    // Extract certificate byte vectors, endorse TBS certs, and ensure they parse with OpenSSL.
    // During the process, both:
    //   1. prepare a UJSON payload of endorsed certs to send back to the device,
    //   2. collect the certs that were endorsed to verify their endorsement signatures with OpenSSL, and
    //   3. hash all certs to check the integrity of what gets written back to the device.
    let mut cert_hasher = Sha256::new();
    let mut start: usize = 0;
    let mut host_endorsed_certs: Vec<Vec<u8>> = Vec::new();
    let mut num_host_endorsed_certs = 0;
    let mut endorsed_cert_concat = ArrayVec::<u8, 4096>::new();

    for _ in 0..perso_blob.num_objs {
        log::info!("Processing next object");
        let header = get_obj_header(&perso_blob.body[start..])?;
        match header.obj_type {
            ObjType::EndorsedX509Cert | ObjType::UnendorsedX509Cert => (),
            ObjType::DevSeed => {
                start += header.obj_size;
                continue;
            }
        }
        start += std::mem::size_of::<ObjHeaderType>();

        // The next object is a cert, let's retrieve its properties (name, needs
        // endorsement, etc.)
        let cert = get_cert(&perso_blob.body[start..])?;
        start += cert.wrapped_size;

        let cert_bytes = if header.obj_type == ObjType::UnendorsedX509Cert {
            // Endorse the cert and updates its size.
            let cert_bytes = parse_and_endorse_x509_cert(cert.cert_body.clone(), &key)?;

            // Prepare a collection of certs whose endorsements should be checked with OpenSSL.
            // TODO: verify the endorsement of the UDS certificate with OpenSSL. It is currently
            // failing signature verification due to the custom DiceTcbInfo extension being a
            // non-recognizable extension that is marked "critical".
            if cert.cert_name != "UDS" {
                host_endorsed_certs.push(cert_bytes.clone());
            }

            // Prepare the UJSON data payloads that will be sent back to the device.
            push_endorsed_cert(&cert_bytes, &cert, &mut endorsed_cert_concat)?;
            num_host_endorsed_certs += 1;
            cert_bytes
        } else {
            cert.cert_body
        };
        // Ensure all certs parse with OpenSSL (even those that where endorsed on device).
        log::info!("{} Cert: {}", cert.cert_name, hex::encode(&cert_bytes));
        let _ = parse_certificate(&cert_bytes)?;
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
    let _ = UartConsole::wait_for(&*uart, r"Importing endorsed certificates ...", timeout)?;
    manuf_perso_data_back.send(&*uart)?;
    let _ = UartConsole::wait_for(&*uart, r"Finished importing certificates.", timeout)?;

    // Check the integrity of the certificates written to the device's flash by comparing a
    // SHA256 over all certificates computed on the host and device sides.
    let device_computed_certs_hash = SerdesSha256Hash::recv(&*uart, timeout, false)?;
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
    if !host_endorsed_certs.is_empty() {
        validate_certs_chain(ca_certificate.to_str().unwrap(), &host_endorsed_certs)?;
    }

    Ok(())
}

pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    cert_endorsement_key_wrapper: KeyWrapper,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
    ca_certificate: PathBuf,
    rma_unlock_token_hash: &ArrayVec<u32, 4>,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Bootstrap personalization binary into flash.
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    // Bootstrap again since the flash scrambling seeds were provisioned in the previous step.
    let _ = UartConsole::wait_for(&*uart, r"Bootstrap requested.", timeout)?;
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    send_rma_unlock_token_hash(transport, rma_unlock_token_hash, timeout)?;
    provision_certificates(
        transport,
        cert_endorsement_key_wrapper,
        perso_certgen_inputs,
        timeout,
        ca_certificate,
    )?;

    let _ = UartConsole::wait_for(&*uart, r"Personalization done.", timeout)?;

    Ok(())
}
