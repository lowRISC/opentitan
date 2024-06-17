# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS = [
    "sival",
    "prodc",
]

_DEVICE_ID_AND_TEST_TOKENS = """
  --device-id="0x11111111_22222222_33333333_44444444_55555555_66666666_77777777_88888888"
  --test-unlock-token="0x11111111_11111111_11111111_11111111"
  --test-exit-token="0x11111111_11111111_11111111_11111111"
"""

CP_PROVISIONING_INPUTS = _DEVICE_ID_AND_TEST_TOKENS + """
  --manuf-state="0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000"
  --wafer-auth-secret="0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000"
"""

FT_PERSONALIZE_KEYS = [
    "//sw/device/silicon_creator/manuf/keys/fake:cert_endorsement_key.sk.der",
    "//sw/device/silicon_creator/manuf/keys/fake:fake_ca.pem",
    "//sw/device/silicon_creator/manuf/keys/fake:ckms_ca.pem",
    "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der",
]

# Note that uds-auth-key-id below is the actual hash of the public key of cert_endorsement_key.sk.der
FT_PROVISIONING_INPUTS = _DEVICE_ID_AND_TEST_TOKENS + """
  --target-mission-mode-lc-state="prod"
  --host-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)"
  --rom-ext-measurement="0x11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111"
  --owner-manifest-measurement="0x22222222_22222222_22222222_22222222_22222222_22222222_22222222_22222222"
  --owner-measurement="0x33333333_33333333_33333333_33333333_33333333_33333333_33333333_33333333"
  --rom-ext-security-version="0"
  --owner-security-version="0"
"""

LOCAL_CERT_ENDORSEMENT_PARAMS = """
  --ca-key-der-file="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:cert_endorsement_key.sk.der)"
  --ca-key-id="0xfe584ae7_53790cfd_8601a312_fb32d3c1_b822d112"
  --ca-certificate="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:fake_ca.pem)"
"""

CLOUD_KMS_CERT_ENDORSEMENT_PARAMS = """
  --ca-key-ckms-id="gcs-kms-earlgrey-ze-ca-p256-sha256-key"
  --ca-key-id="0x40aac5fb_2b1205f9_003f40ab_7f3df784_1d5b59f5"
  --ca-certificate="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:ckms_ca.pem)"
"""
