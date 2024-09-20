// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdint.h>

#include "sw/device/lib/base/memory.h"
#include "sw/device/silicon_creator/lib/cert/cbor.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"

#include "otp_ctrl_regs.h"  // Generated.

// Keys
const int64_t kCoseKeyKtyLabel = 1;
const int64_t kCoseKeyAlgLabel = 3;
const int64_t kCoseEc2CrvLabel = -1;
const int64_t kCoseEc2XLabel = -2;
const int64_t kCoseEc2YLabel = -3;

// Values
const int64_t kCoseKeyAlgEcdsa256 = -7;
const int64_t kCoseEc2CrvP256 = 1;
const int64_t kCoseKeyKtyEc2 = 2;

// UDS (Creator) attestation key diverisfier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_diversification_t kUdsKeymgrDiversifier = {
    .salt =
        {
            0xabffa6a9,
            0xc781f1ad,
            0x4c1107ad,
            0xf9210d85,
            0x0931f555,
            0x6c5aef5d,
            0xb9ba4df0,
            0x77b248d2,
        },
    .version = 0,
};
// CDI_0 (OwnerIntermediate) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi0KeymgrDiversifier = {
    .salt =
        {
            0x3e5913c7,
            0x41156f1d,
            0x998ddb9f,
            0xfa334191,
            0x8a85380e,
            0xba76ca1a,
            0xdb17c4a7,
            0xfb8852dc,
        },
    .version = 0,
};
// CDI_1 (Owner) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi1KeymgrDiversifier = {
    .salt =
        {
            0x2d12c2e3,
            0x6acc6876,
            0x4bfb07ee,
            0xc45fc414,
            0x5d4fa9de,
            0xf295b128,
            0x50f49882,
            0xbbdefa29,
        },
    .version = 0,
};

const sc_keymgr_ecc_key_t kDiceKeyUds = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldUdsKeySeedIdx,
    .keymgr_diversifier = &kUdsKeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateCreatorRootKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi0 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi0KeySeedIdx,
    .keymgr_diversifier = &kCdi0KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerIntermediateKey,
};
const sc_keymgr_ecc_key_t kDiceKeyCdi1 = {
    .type = kScKeymgrKeyTypeAttestation,
    .keygen_seed_idx = kFlashInfoFieldCdi1KeySeedIdx,
    .keymgr_diversifier = &kCdi1KeymgrDiversifier,
    .required_keymgr_state = kScKeymgrStateOwnerKey,
};

// PubKeyECDSA256 = {               ; COSE_Key [RFC9052 s7]
//     1 : 2,                       ; Key type : EC2
//     3 : AlgorithmES256,          ; Algorithm : ECDSA w/ SHA-256
//     -1 : 1,                      ; Curve: P256
//     -2 : bstr,                   ; X coordinate, big-endian
//     -3 : bstr                    ; Y coordinate, big-endian
// }
rom_error_t dice_uds_tbs_cert_build(cert_key_id_pair_t *key_ids,
                                    ecdsa_p256_public_key_t *uds_pubkey,
                                    uint8_t *tbs_cert, size_t *tbs_cert_size) {
  struct CborOut kCborOutHandle;

  struct CborOut *pCborOut = &kCborOutHandle;

  HARDENED_RETURN_IF_ERROR(
      cbor_write_out_init(pCborOut, tbs_cert, *tbs_cert_size));
  HARDENED_RETURN_IF_ERROR(cbor_map_init(pCborOut, 5));
  HARDENED_RETURN_IF_ERROR(
      cbor_write_pair_uint_uint(pCborOut, kCoseKeyKtyLabel, kCoseKeyKtyEc2));
  HARDENED_RETURN_IF_ERROR(cbor_write_pair_uint_int(pCborOut, kCoseKeyAlgLabel,
                                                    kCoseKeyAlgEcdsa256));
  HARDENED_RETURN_IF_ERROR(
      cbor_write_pair_int_uint(pCborOut, kCoseEc2CrvLabel, kCoseEc2CrvP256));
  HARDENED_RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, kCoseEc2XLabel,
                                                     (uint8_t *)uds_pubkey->x,
                                                     sizeof(uds_pubkey->x)));
  HARDENED_RETURN_IF_ERROR(cbor_write_pair_int_bytes(pCborOut, kCoseEc2YLabel,
                                                     (uint8_t *)uds_pubkey->y,
                                                     sizeof(uds_pubkey->y)));
  *tbs_cert_size = CborOutSize(pCborOut);

  return kErrorOk;
}

rom_error_t dice_cdi_0_cert_build(hmac_digest_t *rom_ext_measurement,
                                  uint32_t rom_ext_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_0_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  // TODO(lowRISC/opentitan:#24281): implement body
  return kErrorOk;
}

rom_error_t dice_cdi_1_cert_build(hmac_digest_t *owner_measurement,
                                  hmac_digest_t *owner_manifest_measurement,
                                  uint32_t owner_security_version,
                                  cert_key_id_pair_t *key_ids,
                                  ecdsa_p256_public_key_t *cdi_1_pubkey,
                                  uint8_t *cert, size_t *cert_size) {
  // TODO(lowRISC/opentitan:#24281): implement body
  return kErrorOk;
}
