// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"

OTTF_DEFINE_TEST_CONFIG(.enable_uart_flow_control = true);

static manuf_cert_perso_data_in_t in_data;

enum {
  kAttestMeasurementSizeInBits = 256,
  kAttestMeasurementSizeInBytes = kAttestMeasurementSizeInBits / 8,
  kAttestMeasurementSizeIn32BitWords =
      kAttestMeasurementSizeInBytes / sizeof(uint32_t),
};

/**
 * Crank the keymgr to produce the attestation keys and certificates.
 */
static status_t personalize(ujson_t *uj) {
  // Retrieve certificate provisioning data.
  LOG_INFO("Waiting for FT provisioning data ...");
  TRY(ujson_deserialize_manuf_cert_perso_data_in_t(uj, &in_data));

  // Advance keymgr to Initialized state.
  TRY(entropy_complex_init());
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateInit));

  // Load OTBN attestation keygen program.
  attestation_public_key_t curr_pubkey = {.x = {0}, .y = {0}};
  TRY(otbn_boot_app_load());

  // Advance keymgr and generate UDS attestation keys / cert.
  // TODO(#19455): set attestation binding to OTP *Cfg partition measurements.
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateCreatorRootKey));
  TRY(otbn_boot_attestation_keygen(kUdsAttestationKeySeed,
                                   kUdsKeymgrDiversifier, &curr_pubkey));
  // TODO(#19455): create certificate and self-sign it. While it will be
  // endorsed off-device, i.e., the signature will be replaced, the self-sign
  // will be used to gaurantee the integrity of the cert to the host.
  //
  // Note: the offline endorsement will take place in a secure environment,
  // hence we are not taking any measure to authenticate the device to the host.
  TRY(otbn_boot_attestation_key_save(kUdsAttestationKeySeed,
                                     kCdi0KeymgrDiversifier));

  // Set attestation binding to ROM_EXT / Ownership Manifest measurements.
  // We set the sealing binding value to all zeros as it is unused in the
  // current personalization flow. This may be changed in the future.
  keymgr_binding_value_t attestation_binding_value = {.data = {0}};
  keymgr_binding_value_t sealing_binding_value = {.data = {0}};
  uint32_t rom_ext_measurements[kAttestMeasurementSizeIn32BitWords * 2];
  hmac_digest_t combined_measurements;
  memcpy(rom_ext_measurements, in_data.rom_ext_measurement,
         kAttestMeasurementSizeInBytes);
  memcpy(&rom_ext_measurements[kAttestMeasurementSizeIn32BitWords],
         in_data.owner_manifest_measurement, kAttestMeasurementSizeInBytes);
  hmac_sha256(rom_ext_measurements, kAttestMeasurementSizeInBytes * 2,
              &combined_measurements);
  memcpy(attestation_binding_value.data, combined_measurements.digest,
         kAttestMeasurementSizeInBytes);
  keymgr_sw_binding_unlock_wait();
  keymgr_sw_binding_set(&sealing_binding_value, &attestation_binding_value);

  // Advance keymgr and generate CDI_0 attestation keys / cert.
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateOwnerIntermediateKey));
  TRY(otbn_boot_attestation_keygen(kCdi0AttestationKeySeed,
                                   kCdi0KeymgrDiversifier, &curr_pubkey));
  // TODO(#19455): create certificate with key, endorse it, and write it to
  // flash info.
  TRY(otbn_boot_attestation_key_save(kCdi0AttestationKeySeed,
                                     kCdi0KeymgrDiversifier));

  // Set attestation binding to OWNER measurement.
  // We keep the sealing binding value to all zeros as it is unused in the
  // current personalization flow. This may be changed in the future.
  memcpy(attestation_binding_value.data, in_data.owner_measurement,
         kAttestMeasurementSizeInBytes);
  keymgr_sw_binding_unlock_wait();
  keymgr_sw_binding_set(&sealing_binding_value, &attestation_binding_value);

  // Advance keymgr and generate CDI_1 attestation keys / cert.
  keymgr_advance_state();
  TRY(keymgr_state_check(kKeymgrStateOwnerKey));
  TRY(otbn_boot_attestation_keygen(kCdi1AttestationKeySeed,
                                   kCdi1KeymgrDiversifier, &curr_pubkey));
  // TODO(#19455): create certificate with key, endorse it, and write it to
  // flash info.
  TRY(otbn_boot_attestation_key_save(kCdi1AttestationKeySeed,
                                     kCdi1KeymgrDiversifier));

  LOG_INFO("Exporting attestation certificates ...");
  // TODO(#19455): export certificates.

  LOG_INFO("Wait for UDS attestation certificate endorsement ...");
  // TODO(#19455): update UDS certificate signature field and commit to flash.

  return OK_STATUS();
}

bool test_main(void) {
  ujson_t uj = ujson_ottf_console();

  CHECK_STATUS_OK(personalize(&uj));

  return true;
}
