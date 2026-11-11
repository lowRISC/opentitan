# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@bazel_skylib//lib:paths.bzl", "paths")
load("@provisioning_exts//:cfg.bzl", "EXT_EARLGREY_OTP_CFGS", "EXT_EARLGREY_SKUS")
load("//sw/device/silicon_creator/lib/cert:dice.bzl", "DICE_FORMATS")

# A list of OTP configurations that will be used to autogenerate FT
# individualization binaries that configure OTP with the constants defined in
# these bazel targets.
EARLGREY_OTP_CFGS = {
    "sv00": "//hw/ip/otp_ctrl/data/earlgrey_skus/sival:otp_consts",
    "em00": "//hw/ip/otp_ctrl/data/earlgrey_skus/emulation:otp_consts",
} | EXT_EARLGREY_OTP_CFGS

# A dictionary of SKU configurations that will be used to generate FT
# personalization binaries that configure OTP and flash info pages as defined
# in these bazel targets.
EARLGREY_SKUS = {
    # OTP Config: Emulation; DICE Certs: X.509; Additional Certs: None
    "emulation": {
        "otp": "em00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_format": "x509",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
        "device_ext_libs": ["@lowrisc_opentitan//sw/device/silicon_creator/manuf/default:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_x509_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:emulation",
    },
    # OTP Config: Emulation; DICE Certs: CWT; Additional Certs: None
    "emulation_dice_cwt": {
        "otp": "em00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_format": "cwt",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
        "device_ext_libs": ["@lowrisc_opentitan//sw/device/silicon_creator/manuf/default:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_cwt_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:emulation_dice_cwt",
    },
    # OTP Config: Emulation; DICE Certs: ECDSA X.509 for perso, ML-DSA ROM_EXT for Bank B
    "emulation_dice_mldsa": {
        "otp": "em00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_format": "mldsa",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
        "device_ext_libs": ["@lowrisc_opentitan//sw/device/silicon_creator/manuf/default:default_dice_mldsa_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/lib/ownership:test_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext:rom_ext_dice_mldsa_slot_b",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_mldsa_virtual",
        "ecdsa_key": {},
        "spx_key": {},
        "signature_prefix": None,
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:emulation_dice_mldsa",
    },
    # OTP Config: Emulation; DICE Certs: X.509; Additional Certs: TPM EK
    "emulation_tpm": {
        "otp": "em00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_format": "x509",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
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
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:emulation_tpm",
    },
    "sival": {
        "otp": "sv00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/sival:ca_data",
        "dice_format": "x509",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
        "device_ext_libs": ["@lowrisc_opentitan//sw/device/silicon_creator/manuf/default:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/rom_ext/sival:sival_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext/sival/binaries:rom_ext_dice_x509_prod",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {"//hw/ip/otp_ctrl/data/earlgrey_skus/sival/keys:keyset": "sv00-earlgrey-a1-root-ecdsa-prod-0"},
        "spx_key": {},
        "signature_prefix": None,
        "perso_bin": "//sw/device/silicon_creator/manuf/base/binaries:ft_personalize_sival",
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:sival",
        "offline": True,
    },
    "sival_staging": {
        "otp": "sv00",
        "ca_data": "@lowrisc_opentitan//sw/device/silicon_creator/manuf/keys/fake:ca_data",
        "dice_format": "x509",
        "host_ext_libs": ["@lowrisc_opentitan//sw/host/provisioning/ft_ext_lib:default_ft_ext_lib"],
        "device_ext_libs": ["@lowrisc_opentitan//sw/device/silicon_creator/manuf/default:default_perso_fw_ext"],
        "ownership_libs": ["//sw/device/silicon_creator/rom_ext/sival:sival_owner"],
        "rom_ext": "//sw/device/silicon_creator/rom_ext/sival/binaries:rom_ext_dice_x509_prod",
        "owner_fw": "//sw/device/silicon_owner/bare_metal:bare_metal_slot_b",
        "ecdsa_key": {"//hw/ip/otp_ctrl/data/earlgrey_skus/sival/keys:keyset": "sv00-earlgrey-a1-root-ecdsa-prod-0"},
        "spx_key": {},
        "signature_prefix": None,
        "perso_bin": "//sw/device/silicon_creator/manuf/base/binaries:ft_personalize_sival",
        "orchestrator_cfg": "@lowrisc_opentitan//sw/host/provisioning/orchestrator/configs/skus:sival_staging",
    },
} | EXT_EARLGREY_SKUS

def uds_cert_libs_name(template):
    """Get the name of the `uds_cert_libs` instance for this template."""
    label = Label(template)
    return paths.join(label.package, paths.replace_extension(label.name, ""))

def sku_dice_libs(sku, config):
    """Get the DICE libraries for a SKU's perso firmware. These are selected by the `dice_format`,
    but can be overriden using `dice_libs`."""
    dice_format = config.get("dice_format")
    uds_template = config.get("uds_template")
    if dice_format and dice_format not in DICE_FORMATS:
        fail("SKU {} has dice_format: \"{}\" but it must be one of {}".format(sku, dice_format, DICE_FORMATS))

    # TODO: This is primarily for backwards compatibility. If it is determined there are no
    # downstream use cases and downstream users have migrated, consider removing `dice_libs`.
    # For now we warn about the deprecation until "acknowledged" by adding `dice_format`.
    if "dice_libs" in config:
        if dice_format == None:
            print("WARNING: SKU {} uses deprecated `dice_libs` without `dice_format`. Set `dice_format` instead.".format(sku))
        if uds_template:
            fail("SKU {} sets both `dice_libs` and `uds_template`. Only one should be used.".format(sku))
        return config["dice_libs"]

    if not dice_format:
        fail("SKU {} has no defined `dice_format`.".format(sku))

    if dice_format == "cwt":
        if uds_template:
            fail("SKU {} sets a `uds_template`, which is not used by the \"cwt\" DICE format.".format(sku))
        return [
            "//sw/device/silicon_creator/lib/cert:dice_cwt",
            "//sw/device/silicon_creator/lib/cert:dice_mldsa_empty",
        ]

    # For x509 and ML-DSA, SKUs may override the UDS template
    if uds_template:
        name = uds_cert_libs_name(uds_template)
        uds_x509 = Label(":{}_uds_cert_build".format(name))
        uds_mldsa = Label(":{}_mldsa_uds_cert_build".format(name))
    else:
        uds_x509 = "//sw/device/silicon_creator/lib/cert:dice_uds_cert_build"
        uds_mldsa = "//sw/device/silicon_creator/lib/cert:dice_mldsa_uds_cert_build"

    if dice_format == "x509":
        return [uds_x509, "//sw/device/silicon_creator/lib/cert:dice_mldsa_empty"]
    return [uds_x509, uds_mldsa]

# TODO(lowRISC#27275): Refactor build/signing rules for perso binaries.
def disqualified_for_signing(name, data):
    if "staging" in name:
        return True
    if "emulation" in name:
        return True
    if not data["ecdsa_key"] and not data["spx_key"]:
        return True
    if "em00" in data["otp"]:
        return True
    return False
