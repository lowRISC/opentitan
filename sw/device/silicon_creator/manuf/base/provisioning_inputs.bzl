# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@provisioning_exts//:cfg.bzl",
    "EXT_EARLGREY_OTP_CFGS",
    "EXT_EARLGREY_SKUS",
)

# A list of OTP configurations that will be used to autogenerate FT
# individualization binaries that configure OTP with the constants defined in
# these bazel targets.
EARLGREY_OTP_CFGS = {
    "sival": "//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_consts",
    "prodc": "//hw/ip/otp_ctrl/data/earlgrey_skus/prodc:otp_consts",
} | EXT_EARLGREY_OTP_CFGS

# A dictionary of SKU configurations that will be used to generate FT
# personalization binaries that configure OTP and flash info pages as defined
# in these bazel targets.
EARLGREY_SKUS = {
    # OTP Config: SIVAL; DICE Certs: X.509; Additional Certs: None
    "sival": {
        "otp": "sival",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
        "transport_image": "//sw/device/silicon_creator/rom_ext/sival:rom_ext_fake_prod_signed_slot_b",
    },
    # OTP Config: SIVAL; DICE Certs: CWT; Additional Certs: None
    # TODO(#24281): uncomment when DICE CWT cert flows are fully supported
    # "sival_dice_cwt": {
    #     "otp": "sival",
    #     "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice_cwt"],
    #     "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
    #     "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
    #     "transport_image": "//sw/device/silicon_creator/rom_ext/sival:rom_ext_fake_prod_signed_slot_b",
    # },
    # OTP Config: SIVAL; DICE Certs: X.509; Additional Certs: TPM EK
    "sival_tpm": {
        "otp": "sival",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": [
            "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
            "//sw/device/silicon_creator/manuf/base:tpm_perso_fw_ext",
        ],
        "transport_image": "//sw/device/silicon_creator/rom_ext/sival:rom_ext_fake_prod_signed_slot_b",
    },
    # OTP Config: PRODC; DICE Certs: X.509; Additional Certs: None
    "prodc": {
        "otp": "prodc",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
        "transport_image": "//sw/device/silicon_creator/rom_ext/prodc:rom_ext_fake_prod_signed_slot_b",
    },
} | EXT_EARLGREY_SKUS

_DEVICE_ID_AND_TEST_TOKENS = """
  --device-id="0x11111111_22222222_33333333_44444444_55555555_66666666_77777777_88888888"
  --test-unlock-token="0x11111111_11111111_11111111_11111111"
  --test-exit-token="0x11111111_11111111_11111111_11111111"
"""

CP_PROVISIONING_INPUTS = _DEVICE_ID_AND_TEST_TOKENS + """
  --manuf-state="0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000"
  --wafer-auth-secret="0x00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000"
"""

FT_PERSONALIZE_ENDORSEMENT_KEYS = [
    "//sw/device/silicon_creator/manuf/keys/fake:cert_endorsement_key.sk.der",
    "//sw/device/silicon_creator/manuf/keys/fake:fake_ca.pem",
    "//sw/device/silicon_creator/manuf/keys/fake:ckms_ca.pem",
    "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_token_export_key.sk_hsm.der",
]

# Note that uds-auth-key-id below is the actual hash of the public key of cert_endorsement_key.sk.der
FT_PROVISIONING_INPUTS = _DEVICE_ID_AND_TEST_TOKENS + """
  --target-mission-mode-lc-state="prod"
  --rom-ext-measurement="0x11111111_11111111_11111111_11111111_11111111_11111111_11111111_11111111"
  --owner-manifest-measurement="0x22222222_22222222_22222222_22222222_22222222_22222222_22222222_22222222"
  --owner-measurement="0x33333333_33333333_33333333_33333333_33333333_33333333_33333333_33333333"
  --rom-ext-security-version="0"
  --owner-security-version="0"
  --rma-unlock-token-hash="0x01234567_89abcdef"
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
