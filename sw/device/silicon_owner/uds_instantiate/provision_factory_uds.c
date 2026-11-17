// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/silicon_creator/lib/base/static_dice_cdi_0.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/cert/uds.h"  // Generated.
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('p', 'f', 'u')

OTTF_DEFINE_TEST_CONFIG();

static uint8_t uds_tbs_buf[kUdsMaxTbsSizeBytes];
static uint8_t uds_cert_buf[kUdsMaxCertSizeBytes];
static uint8_t
    factory_page_buf[FLASH_CTRL_PARAM_BYTES_PER_PAGE] OT_WORD_ALIGNED;

static status_t provision_factory_uds(void) {
  TRY(ottf_alerts_ignore_alert(kTopEarlgreyAlertIdFlashCtrlRecovErr));
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageFactoryCerts);

  TRY(otbn_boot_app_load());
  TRY(dice_chain_attestation_silicon());
  TRY(otbn_boot_attestation_key_save(kDiceKeyUds.keygen_seed_idx,
                                     kDiceKeyUds.type,
                                     *kDiceKeyUds.keymgr_diversifier));

  hmac_digest_t creator_sw_cfg_meas;
  hmac_digest_t owner_sw_cfg_meas;
  hmac_digest_t auth_codesign_meas;
  hmac_digest_t auth_state_meas;
  hmac_digest_t ica_key_id;
  memset(&creator_sw_cfg_meas, 0x11, sizeof(creator_sw_cfg_meas));
  memset(&owner_sw_cfg_meas, 0x22, sizeof(owner_sw_cfg_meas));
  memset(&auth_codesign_meas, 0x33, sizeof(auth_codesign_meas));
  memset(&auth_state_meas, 0x44, sizeof(auth_state_meas));
  memset(&ica_key_id, 0xa5, sizeof(ica_key_id));

  cert_key_id_pair_t key_ids = {
      .endorsement = &ica_key_id,
      .cert = &static_dice_cdi_0.uds_pubkey_id,
  };
  size_t tbs_size = sizeof(uds_tbs_buf);
  TRY(dice_uds_tbs_cert_build(&creator_sw_cfg_meas, &owner_sw_cfg_meas,
                              &auth_codesign_meas, &auth_state_meas, &key_ids,
                              &static_dice_cdi_0.uds_pubkey, uds_tbs_buf,
                              &tbs_size));

  hmac_digest_t tbs_digest;
  hmac_sha256(uds_tbs_buf, tbs_size, &tbs_digest);

  ecdsa_p256_public_key_t uds_pubkey_le = static_dice_cdi_0.uds_pubkey;
  util_reverse_bytes(uds_pubkey_le.x, sizeof(uds_pubkey_le.x));
  util_reverse_bytes(uds_pubkey_le.y, sizeof(uds_pubkey_le.y));

  ecdsa_p256_signature_t sig = {0};
  TRY(otbn_boot_attestation_endorse(&tbs_digest, &sig, &uds_pubkey_le));
  util_p256_signature_le_to_be_convert(sig.r, sig.s);

  uds_cert_values_t cert_params = {0};
  cert_params.signature_alg = kUdsSignatureAlgEcdsaP256;
  TEMPLATE_SET(cert_params, Uds, Tbs, uds_tbs_buf);
  cert_params.tbs_size = tbs_size;
  TEMPLATE_SET(cert_params, Uds, CertSignatureR, sig.r);
  TEMPLATE_SET(cert_params, Uds, CertSignatureS, sig.s);

  size_t cert_size = sizeof(uds_cert_buf);
  TRY(uds_build_cert(&cert_params, uds_cert_buf, &cert_size));

  memset(factory_page_buf, 0, sizeof(factory_page_buf));
  size_t obj_size = sizeof(factory_page_buf);
  TRY(perso_tlv_cert_obj_build("UDS", kPersoObjectTypeX509Cert, uds_cert_buf,
                               cert_size, kPersoBlobVersionV0, factory_page_buf,
                               &obj_size));

  TRY(flash_ctrl_info_erase(&kFlashCtrlInfoPageFactoryCerts,
                            kFlashCtrlEraseTypePage));
  TRY(flash_ctrl_info_write(&kFlashCtrlInfoPageFactoryCerts, /*offset=*/0,
                            util_size_to_words(sizeof(factory_page_buf)),
                            factory_page_buf));
  LOG_INFO("Provisioned test factory P-256 UDS cert (%u bytes).",
           (unsigned int)cert_size);
  return OK_STATUS();
}

bool test_main(void) {
  status_t sts = provision_factory_uds();
  if (status_err(sts)) {
    LOG_ERROR("provision_factory_uds failed: %r", sts);
  }
  return status_ok(sts);
}
