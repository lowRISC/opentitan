// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use sha2::{Digest, Sha256};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{bail, Result};
use arrayvec::ArrayVec;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::{PublicKey, SecretKey};
use p256::NistP256;
use zerocopy::AsBytes;

use cert_lib::{parse_and_endorse_x509_cert, validate_certs_chain, CertEndorsementKey};
use opentitanlib::app::TransportWrapper;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use ot_certs::x509::parse_certificate;
use ujson_lib::provisioning_data::{
    EccP256PublicKey, ManufCertgenInputs, ManufCerts, ManufEndorsedCerts, ManufFtIndividualizeData,
    SerdesSha256Hash, WrappedRmaUnlockToken,
};

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

fn extract_rma_unlock_token(
    transport: &TransportWrapper,
    host_ecc_sk: PathBuf,
    timeout: Duration,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Load host (HSM) generated ECC keys.
    let host_sk = SecretKey::<NistP256>::read_pkcs8_der_file(host_ecc_sk)?;
    let host_pk = PublicKey::<NistP256>::from_secret_scalar(&host_sk.to_nonzero_scalar());

    // Format host ECC public key to inject it into the device.
    // Note: we trim off the first byte of SEC1 formatted public key as these are not part
    // of the key bytes, rather this byte just indicates if the key was compressed or not.
    let host_pk_sec1_bytes = host_pk.to_sec1_bytes();
    let num_coord_bytes: usize = (host_pk_sec1_bytes.len() - 1) / 2;
    let mut host_pk_x = host_pk_sec1_bytes.as_ref()[1..num_coord_bytes + 1]
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<ArrayVec<u32, 8>>();
    let mut host_pk_y = host_pk_sec1_bytes.as_ref()[num_coord_bytes + 1..]
        .chunks(4)
        .map(|bytes| u32::from_be_bytes(bytes.try_into().unwrap()))
        .collect::<ArrayVec<u32, 8>>();
    host_pk_x.reverse();
    host_pk_y.reverse();
    let rma_token_wrapping_pubkey = EccP256PublicKey {
        x: host_pk_x,
        y: host_pk_y,
    };

    // Get UART, set flow control, and wait for test to start running.
    uart.set_flow_control(true)?;
    let _ = UartConsole::wait_for(&*uart, r"Waiting for host public key ...", timeout)?;

    // Send RMA token wrapping ECC keys into the device over the console.
    rma_token_wrapping_pubkey.send(&*uart)?;

    // Wait until device exports the wrapped RMA unlock token.
    let _ = UartConsole::wait_for(&*uart, r"Exporting RMA token ...", timeout)?;
    let rma_token_out_data = WrappedRmaUnlockToken::recv(&*uart, timeout, false)?;
    log::info!("{:x?}", rma_token_out_data);

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
    let certs_ujson = ManufCerts::recv(&*uart, timeout, true)?;

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

    // Extract certificate byte vectors, endorse TBS certs, and ensure they parse with OpenSSL.
    // During the process, both:
    //   1. prepare a UJSON payload of endorsed certs to send back to the device,
    //   2. collect the certs that were endorsed to verify their endorsement signatures with OpenSSL, and
    //   3. hash all certs to check the integrity of what gets written back to the device.
    let cert_labels = ["UDS", "CDI_0", "CDI_1", "TPM_EK", "CEK", "CIK"];
    let mut cert_hasher = Sha256::new();
    let mut start: usize = 0;
    let mut offset: u32 = 0;
    let mut host_endorsed_certs: Vec<Vec<u8>> = Vec::new();
    let mut endorsed_cert_concat = ArrayVec::<u8, 4096>::new();
    let mut endorsed_cert_sizes = ArrayVec::<u32, 8>::new();
    let mut endorsed_cert_offsets = ArrayVec::<u32, 8>::new();
    for (i, label) in cert_labels.iter().enumerate() {
        let mut cert_size = certs_ujson.sizes[i] as usize;
        let mut cert_bytes = certs_ujson.certs[start..start + cert_size].to_vec();
        start += cert_size;
        // Not all certificates need to be endorsed, some certs are already fully endorsed.
        if certs_ujson.tbs[i] {
            // Endorse the cert and updates its size.
            cert_bytes = parse_and_endorse_x509_cert(cert_bytes.clone(), &key)?;
            cert_size = cert_bytes.len();
            // Prepare a collection of certs whose endorsements should be checked with OpenSSL.
            // TODO: verify the endorsement of the UDS certificate with OpenSSL. It is currently
            // failing signature verification due to the custom DiceTcbInfo extension being a
            // non-recognizable extension that is marked "critical".
            if i > 0 {
                host_endorsed_certs.push(cert_bytes.clone());
            }
            // Prepare the UJSON data payloads that will be sent back to the device.
            endorsed_cert_concat.try_extend_from_slice(cert_bytes.as_slice())?;
            endorsed_cert_sizes.push(cert_size as u32);
            endorsed_cert_offsets.push(offset);
            offset += cert_size as u32;
        }
        // Ensure all certs parse with OpenSSL (even those that where endorsed on device).
        log::info!("{} Cert: {}", label, hex::encode(cert_bytes.clone()));
        let _ = parse_certificate(cert_bytes.as_slice())?;
        // Push the cert into the hasher so we can ensure the certs written to the device's flash
        // info pages match those verified on the host.
        cert_hasher.update(cert_bytes);
    }
    let host_computed_certs_hash = cert_hasher.finalize();

    // Send endorsed certificates back to the device.
    let manuf_endorsed_certs = ManufEndorsedCerts {
        sizes: endorsed_cert_sizes,
        offsets: endorsed_cert_offsets,
        certs: endorsed_cert_concat,
    };
    let _ = UartConsole::wait_for(&*uart, r"Importing endorsed certificates ...", timeout)?;
    manuf_endorsed_certs.send(&*uart)?;
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
    validate_certs_chain(ca_certificate.to_str().unwrap(), &host_endorsed_certs)?;

    Ok(())
}

pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    host_ecc_sk: PathBuf,
    cert_endorsement_key_wrapper: KeyWrapper,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
    ca_certificate: PathBuf,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Bootstrap personalization binary into flash.
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    // Bootstrap again since the flash scrambling seeds were provisioned in the previous step.
    let _ = UartConsole::wait_for(&*uart, r"Bootstrap requested.", timeout)?;
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    extract_rma_unlock_token(transport, host_ecc_sk, timeout)?;
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
