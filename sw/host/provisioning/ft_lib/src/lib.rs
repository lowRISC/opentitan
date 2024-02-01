// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

use std::path::PathBuf;
use std::time::Duration;

use anyhow::Result;
use arrayvec::ArrayVec;
use elliptic_curve::pkcs8::DecodePrivateKey;
use elliptic_curve::{PublicKey, SecretKey};
use num_bigint_dig::BigUint;
use p256::ecdsa::SigningKey;
use p256::NistP256;

use opentitanlib::app::TransportWrapper;
use opentitanlib::crypto::sha256::sha256;
use opentitanlib::dif::lc_ctrl::{DifLcCtrlState, LcCtrlReg};
use opentitanlib::io::jtag::{JtagParams, JtagTap};
use opentitanlib::test_utils::init::InitializeTest;
use opentitanlib::test_utils::lc_transition::trigger_lc_transition;
use opentitanlib::test_utils::load_sram_program::{
    ExecutionMode, ExecutionResult, SramProgramParams,
};
use opentitanlib::test_utils::rpc::{UartRecv, UartSend};
use opentitanlib::uart::console::UartConsole;
use ot_certs::template::{EcdsaSignature, Signature, Value};
use ot_certs::x509::{generate_certificate_from_tbs, parse_certificate};
use ujson_lib::provisioning_data::{
    EccP256PublicKey, ManufCertgenInputs, ManufDiceCerts, ManufEndorsedCerts,
    ManufFtIndividualizeData, WrappedRmaUnlockToken,
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

pub fn run_ft_personalize(
    transport: &TransportWrapper,
    init: &InitializeTest,
    host_ecc_sk: PathBuf,
    cert_endorsement_ecc_sk: PathBuf,
    perso_certgen_inputs: &ManufCertgenInputs,
    timeout: Duration,
) -> Result<()> {
    let uart = transport.uart("console")?;

    // Bootstrap personalization binary into flash.
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

    // -------------------------------------------------------------------------
    // RMA Token and (OTP) Root Key Provisioning                               |
    // -------------------------------------------------------------------------

    // Bootstrap again since the flash scrambling seeds were provisioned in the previous step.
    let _ = UartConsole::wait_for(&*uart, r"Bootstrap requested.", timeout)?;
    uart.clear_rx_buffer()?;
    init.bootstrap.init(transport)?;

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

    // -------------------------------------------------------------------------
    // Certificate Provisioning                                                |
    // -------------------------------------------------------------------------

    // Send attestation TCB measurements for generating certificates.
    let _ = UartConsole::wait_for(&*uart, r"Waiting for DICE certificate inputs ...", timeout)?;
    perso_certgen_inputs.send(&*uart)?;

    // Wait until device exports the attestation certificates.
    let _ = UartConsole::wait_for(&*uart, r"Exporting DICE certificates ...", timeout)?;
    let certs = ManufDiceCerts::recv(&*uart, timeout, true)?;

    // Extract certificate byte vectors and trim unused bytes.
    let uds_tbs_cert_bytes: Vec<u8> = certs
        .uds_tbs_certificate
        .clone()
        .into_iter()
        .take(certs.uds_tbs_certificate_size)
        .collect();
    let cdi_0_cert_bytes: Vec<u8> = certs
        .cdi_0_certificate
        .clone()
        .into_iter()
        .take(certs.cdi_0_certificate_size)
        .collect();
    let cdi_1_cert_bytes: Vec<u8> = certs
        .cdi_1_certificate
        .clone()
        .into_iter()
        .take(certs.cdi_1_certificate_size)
        .collect();

    // Log certificates to console and check they are parsable with OpenSSL.
    let cert_endorsement_sk = SecretKey::<NistP256>::read_pkcs8_der_file(cert_endorsement_ecc_sk)?;
    let uds_cert_bytes = parse_and_endorse_uds_cert(uds_tbs_cert_bytes, &cert_endorsement_sk)?;
    log::info!("UDS Cert: {}", hex::encode(uds_cert_bytes.clone()));
    log::info!("CDI_0 Cert: {}", hex::encode(cdi_0_cert_bytes.clone()));
    log::info!("CDI_1 Cert: {}", hex::encode(cdi_1_cert_bytes.clone()));
    let _uds_cert = parse_certificate(&uds_cert_bytes)?;
    let _cdi_0_cert = parse_certificate(&cdi_0_cert_bytes)?;
    let _cdi_1_cert = parse_certificate(&cdi_1_cert_bytes)?;

    // Send endorsed certificates back to the device.
    let endorsed_certs = ManufEndorsedCerts {
        uds_certificate: uds_cert_bytes.clone().into_iter().collect(),
        uds_certificate_size: uds_cert_bytes.len(),
    };
    let _ = UartConsole::wait_for(&*uart, r"Importing DICE UDS certificate ...", timeout)?;
    endorsed_certs.send(&*uart)?;
    let _ = UartConsole::wait_for(&*uart, r"Imported DICE UDS certificate.", timeout)?;

    Ok(())
}

fn parse_and_endorse_uds_cert(tbs: Vec<u8>, ca_sk: &SecretKey<NistP256>) -> Result<Vec<u8>> {
    // Hash and sign the TBS.
    let tbs_digest = sha256(&tbs);
    let signing_key = SigningKey::from(ca_sk);
    let (tbs_signature, _) = signing_key.sign_prehash_recoverable(&tbs_digest.to_be_bytes())?;
    let (r, s) = tbs_signature.split_bytes();

    // Reformat the signature.
    let signature = Signature::EcdsaWithSha256 {
        value: Some(EcdsaSignature {
            r: Value::Literal(BigUint::from_bytes_be(&r)),
            s: Value::Literal(BigUint::from_bytes_be(&s)),
        }),
    };

    // Generate the (endorsed) UDS certificate.
    generate_certificate_from_tbs(tbs, &signature)
}
