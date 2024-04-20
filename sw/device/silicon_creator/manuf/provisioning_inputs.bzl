# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

EARLGREY_A0_INDIVIDUALIZE_OTP_SW_CFGS = [
    "sival_bringup",
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
    "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der",
]

FT_PROVISIONING_INPUTS = _DEVICE_ID_AND_TEST_TOKENS + """
  --target-mission-mode-lc-state="prod"
  --host-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der)"
  --cert-endorsement-ecc-sk="$(rootpath //sw/device/silicon_creator/manuf/keys/fake:cert_endorsement_key.sk.der)"
  --rom-ext-measurement="0x11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111"
  --owner-manifest-measurement="0x22222222_22222222_22222222_22222222_22222222_22222222_22222222_22222222"
  --owner-measurement="0x33333333_33333333_33333333_33333333_33333333_33333333_33333333_33333333"
  --uds-auth-key-id="0x11223344_55667788_99112233_44556677_88991122"
  --rom-ext-security-version="0"
  --owner-security-version="0"
"""

# TODO(#22780): Integrate real keys for A1 flows.
FT_PERSONALIZE_SIGNING_KEYS = {"//sw/device/silicon_creator/rom/keys/fake/ecdsa:prod_key_0_ecdsa_p256": "prod_key_0"}
