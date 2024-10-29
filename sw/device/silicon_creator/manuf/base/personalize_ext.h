// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSONALIZE_EXT_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSONALIZE_EXT_H_

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/testing/json/provisioning_data.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"

enum {
  /**
   * Index of the first available page in the `cert_flash_layout` array that
   * personalization extensions may use.
   */
  kCertFlashLayoutExt0Idx = 2,
  /**
   * Index of the second available page in the `cert_flash_layout` array that
   * personalization extensions may use.
   */
  kCertFlashLayoutExt1Idx = 3,
};

/**
 * Parameters passed to personalization extension function invoked before data
 * is sent to the host for endorsement. Not all parameters are necessarily used
 * by all extension implementations.
 */
typedef struct personalize_extension_pre_endorse {
  /**
   *  Serialization interface, marshals/unmarshals structures' fields and
   *  communicates with the host.
   */
  ujson_t *uj;
  /**
   *  Pointer to information used for generating certificates.
   */
  manuf_certgen_inputs_t *certgen_inputs;
  /**
   *  Pointer to the TLV data blob sent to the host for endorsement.
   */
  perso_blob_t *perso_blob_to_host;
  /**
   * Pointer to the flash layout table, the extension could enable disabled
   * entries in the table and configure its INFO space use so that the caller
   * knows where to place endorsed objects received from the host.
   */
  cert_flash_info_layout_t *cert_flash_layout;
  /**
   * Pointer to the flash controller handle necessary for proper flash access.
   */
  dif_flash_ctrl_state_t *flash_ctrl_handle;
  /**
   * Pointer to the UDS public key. Personalization extensions may require
   * accessing it to generate different certificate chains that fit a specific
   * SKU's requirements.
   */
  ecdsa_p256_public_key_t *uds_pubkey;
  hmac_digest_t *uds_pubkey_id;
  /**
   * Pointer to the OTP measurements used to generate the UDS public key.
   * Personalization extensions may require accessing these to generate
   * different certificate chains that fit a specific SKU's requirements.
   */
  hmac_digest_t *otp_creator_sw_cfg_measurement;
  hmac_digest_t *otp_owner_sw_cfg_measurement;
  hmac_digest_t *otp_rot_creator_auth_codesign_measurement;
  hmac_digest_t *otp_rot_creator_auth_state_measurement;
} personalize_extension_pre_endorse_t;

/**
 * Parameters passed to personalization extension function invoked after the
 * host finished endorsement processing and sent endorsed data to the device.
 */
typedef struct personalize_extension_post_endorse {
  /**
   *  Serialization interface, marshals/unmarshals structures' fields and
   *  communicates with the host.
   */
  ujson_t *uj;
  /**
   *  Pointer to the TLV data blob received from the host.
   */
  perso_blob_t *perso_blob_from_host;
  /**
   * Pointer to the flash layout table used previously when saving pre
   * endorsement data..
   */
  cert_flash_info_layout_t *cert_flash_layout;
} personalize_extension_post_endorse_t;

/**
 * A custom extension to the personalization flow.
 *
 * This extension runs *BEFORE* TBS certificates are sent to the host to be
 * endorsed. Implementing this extension enables SKU owners to add more TBS
 * certificates to the list of certificates to be endorsed by the host.
 */
status_t personalize_extension_pre_cert_endorse(
    personalize_extension_pre_endorse_t *pre_params);

/**
 * A custom extension to the personalization flow.
 *
 * This extension runs *AFTER* (endorsed) certificates are sent back to the
 * device from the host. Implementing this extension enables SKU owners to
 * provision additional data into flash, in addition to the endorsed
 * certificates in the `perso_blob_from_host` struct.
 */
status_t personalize_extension_post_cert_endorse(
    personalize_extension_post_endorse_t *post_params);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_MANUF_BASE_PERSONALIZE_EXT_H_
