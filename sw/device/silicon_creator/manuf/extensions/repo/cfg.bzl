# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This enables downstream integrators to define external Earlgrey OTP
# configurations to be used during provisioning for downstream SKUs. See the
# upstream Earlgrey OTP configurations list defined in the `EARLGREY_OTP_CFGS`
# dict in `sw/device/silicon_creator/manuf/base/provisioning_inputs.bzl` for
# more details.
EXT_EARLGREY_OTP_CFGS = {
    # <OTP image name>: <//bazel/target/path:otp_image_consts>
}

# This enables downstream integrators to define external Earlgrey SKU
# configurations to be used during provisioning. See the upstream Earlgrey SKU
# configurations defined in the `EARLGREY_SKUS` dictionary in
# `sw/device/silicon_creator/manuf/base/provisioning_inputs.bzl` for more
# details.
EXT_EARLGREY_SKUS = {
    # <SKU name>: {
    #    # --- Required attributes ---
    #    "otp": <OTP image name in EARLGREY_OTP_CFGS>,
    #    "ca_data": <label of SKU's CA data (certs and keys)>
    #    "dice_format": <DICE certificate format: 'x509', 'cwt' or 'mldsa'>
    #    "host_ext_libs": [<host (FT) hook extension libraries to use>]
    #    "device_ext_libs": [<device (perso) hook extension libraries to use>]
    #    "rom_ext": <label of ROM_EXT to provision>
    #    "owner_fw": <label of owner firmware to provision>
    #    "ecdsa_key": {<keyset label>: <key name>} describing the ECDSA key for
    #                 signing, or `{}` for no key.
    #    "spx_key": {<keyset label>: <key name>} describing the SPX key for
    #               signing, or `{}` for no key.
    #    "signature_prefix": <package containing `_signatures` targets, or None>
    #    "orchestrator_cfg": <label of the `sku_cfg` to configure the orchestrator.>
    #
    #    # --- Optional attributes ---
    #    "dice_libs": [<Deprecated. Now an override for the DICE certgen libs
    #                  (for perso firmware) instead of `dice_format`'s defaults.>]
    #    "ownership_libs": [<ownership libraries used by perso firmware>]
    #    "perso_bin": <override label of a prebuilt signed perso binary to use.>
    #    "scrambling_bin": <override label of a prebuild scrambling binary to use.>
    #    "offline": <True if provisioning tests need offline signed binaries>
    # }
}

# This enables downstream integrators to define external Earlgrey execution
# environments. See the upstream Silicon Owner execution environments defined
# in the `EARLGREY_SILICON_OWNER_ROM_EXT_ENVS` dictionary in
# `rules/opentitan/defs.bzl` for more details.
EXT_EXEC_ENV_SILICON_ROM_EXT = {
    # "@provisioning_ex/bazel/target/exec_env:exec_env_name": None,
}
