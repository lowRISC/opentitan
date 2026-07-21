# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "EARLGREY_SKUS",
)
load(
    "//rules:sku.bzl",
    "sku_cert",
    "sku_cfg",
)

package(default_visibility = ["//visibility:public"])

exports_files(glob(["**"]))

sku_cert(
    name = "sival_dice_ca",
    certificate = "//sw/device/silicon_creator/manuf/keys/sival:dice_ca.pem",
    key = "sv00-earlgrey-a1-ca-dice-0",
    key_id = "0x5398A4F090F2A95C3D52FC98DEB9F2F9AF042F6E",
    key_type = "Token",
)

sku_cfg(
    name = "sival",
    testonly = True,
    dice_ca = ":sival_dice_ca",
    ext_ca = ":sival_dice_ca",
    otp = "sv00",
    owner_fw_boot_str = "ownership: OWND",
    package = "npcr10",
    perso_bin_suffix = "ft_personalize_{sku}_{target}.signed.bin",
    perso_bins = ["//sw/device/silicon_creator/manuf/base/binaries:ft_personalize_sival"],
    product = "earlgrey_a2",
    si_creator = "nuvoton",
    sku_name = "sival",
    target_lc_state = "prod",
    token_encrypt_key = "//sw/device/silicon_creator/manuf/keys/sival:rma_unlock_enc_rsa3072.pub.der",
)

sku_cert(
    name = "emulation_dice_ca",
    certificate = "//sw/device/silicon_creator/manuf/keys/fake:dice_ca.pem",
    key_file = "//sw/device/silicon_creator/manuf/keys/fake:sk.pkcs8.der",
    key_id = "0xfe584ae7_53790cfd_8601a312_fb32d3c1_b822d112",
    key_type = "Raw",
)

sku_cert(
    name = "emulation_ext_ca",
    certificate = "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
    key_file = "//sw/device/silicon_creator/manuf/keys/fake:sk.pkcs8.der",
    key_id = "0xfe584ae7_53790cfd_8601a312_fb32d3c1_b822d112",
    key_type = "Raw",
)

sku_cfg(
    name = "emulation",
    testonly = True,
    dice_ca = ":emulation_dice_ca",
    ext_ca = ":emulation_ext_ca",
    otp = "em00",
    owner_fw_boot_str = "Bare metal PASS!",
    package = "npcr10",
    perso_bin_suffix = "ft_flash_scramble_{sku}_{target}.prod_key_0.prod_key_0.signed.bin",
    perso_bins = ["//sw/device/silicon_creator/manuf/base:ft_flash_scramble_emulation"],
    product = "earlgrey_a2",
    si_creator = "nuvoton",
    sku_name = "emulation",
    target_lc_state = "prod",
    token_encrypt_key = "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_enc_rsa3072.pub.der",
)

sku_cfg(
    name = "emulation_dice_cwt",
    testonly = True,
    dice_ca = ":emulation_dice_ca",
    ext_ca = ":emulation_ext_ca",
    otp = "em00",
    owner_fw_boot_str = "Bare metal PASS!",
    package = "npcr10",
    perso_bin_suffix = "ft_flash_scramble_{sku}_{target}.prod_key_0.prod_key_0.signed.bin",
    perso_bins = ["//sw/device/silicon_creator/manuf/base:ft_flash_scramble_emulation_dice_cwt"],
    product = "earlgrey_a2",
    si_creator = "nuvoton",
    sku_name = "emulation_dice_cwt",
    target_lc_state = "prod",
    token_encrypt_key = "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_enc_rsa3072.pub.der",
)

sku_cfg(
    name = "emulation_tpm",
    testonly = True,
    dice_ca = ":emulation_dice_ca",
    ext_ca = ":emulation_ext_ca",
    otp = "em00",
    owner_fw_boot_str = "Bare metal PASS!",
    package = "npcr10",
    perso_bin_suffix = "ft_flash_scramble_{sku}_{target}.prod_key_0.prod_key_0.signed.bin",
    perso_bins = ["//sw/device/silicon_creator/manuf/base:ft_flash_scramble_emulation_tpm"],
    product = "earlgrey_a2",
    si_creator = "nuvoton",
    sku_name = "emulation_tpm",
    target_lc_state = "prod",
    token_encrypt_key = "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_enc_rsa3072.pub.der",
)

filegroup(
    name = "all",
    testonly = True,
    srcs = depset([
        config["orchestrator_cfg"]
        for _, config in EARLGREY_SKUS.items()
    ]).to_list(),
)
