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
    "sv00": "//hw/top_earlgrey/data/otp/sival_skus:otp_consts",
    "em00": "//hw/top_earlgrey/data/otp/emulation:otp_consts",
} | EXT_EARLGREY_OTP_CFGS

EXT_SIGNED_PERSO_BINS = []

# A dictionary of SKU configurations that will be used to generate FT
# personalization binaries that configure OTP and flash info pages as defined
# in these bazel targets.
EARLGREY_SKUS = {
    # OTP Config: Emulation; DICE Certs: X.509; Additional Certs: None
    "emulation": {
        "otp": "em00",
        "ca_data": "@//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
    },
    # OTP Config: Emulation; DICE Certs: CWT; Additional Certs: None
    "emulation_dice_cwt": {
        "otp": "em00",
        "ca_data": "@//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice_cwt"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_cwt_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@//sw/host/provisioning/orchestrator/configs/skus:emulation_dice_cwt.hjson",
    },
    # OTP Config: Emulation; DICE Certs: X.509; Additional Certs: TPM EK
    "emulation_tpm": {
        "otp": "em00",
        "ca_data": "@//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
        "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
        "device_ext_libs": [
            "//sw/device/silicon_creator/lib/cert:tpm_ek_template_library",
            "//sw/device/silicon_creator/manuf/base:tpm_perso_fw_ext",
        ],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@//sw/host/provisioning/orchestrator/configs/skus:emulation_tpm.hjson",
    },
    # This configuration is not really usable in master but left here as an example until
    # a more appropriate solution is found.
    # "sival": {
    #     "otp": "sv00",
    #     "ca_data": "@//sw/device/silicon_creator/manuf/keys/sival:ca_data",
    #     "dice_libs": ["//sw/device/silicon_creator/lib/cert:dice"],
    #     "host_ext_libs": ["@provisioning_exts//:default_ft_ext_lib"],
    #     "device_ext_libs": ["@provisioning_exts//:default_perso_fw_ext"],
    #     "ownership_libs": ["//sw/device/silicon_creator/rom_ext/sival:sival_owner"],
    #     "rom_ext": "//sw/device/silicon_creator/rom_ext/sival/binaries:rom_ext_dice_x509_prod",
    #     # TODO(cfrantz, ttrippel): This owner_fw isn't signed with the sival owner keys,
    #     # so we expect the ROM_EXT to BFV with `kErrorOwnershipKeyNotFound`,
    #     "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
    #     "ecdsa_key": {"//hw/top_earlgrey/data/otp/skus/sival/keys:keyset": "sv00-earlgrey-a1-root-ecdsa-prod-0"},
    #     "spx_key": {},
    #     "signature_prefix": None,
    #     "perso_bin": "//sw/device/silicon_creator/manuf/base/binaries:ft_personalize_sival",
    #     "orchestrator_cfg": "@//sw/host/provisioning/orchestrator/configs/skus:sival.hjson",
    #     "offline": True,
    # },
} | EXT_EARLGREY_SKUS

# TODO(lowRISC#27275): Refactor build/signing rules for perso binaries.
def disqualified_for_signing(name, data):
    if "staging" in name:
        return True
    if "em00" in data["otp"]:
        return True
    return False
