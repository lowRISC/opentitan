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
    #    "otp": <OTP image name above in EXT_EARLGREY_OTP_CFGS>,
    #    "dice_libs": [<which DICE certgen libs to use: X.509 or CWT>]
    #    "host_ext_libs": [<which host hooks extension libraries to use>]
    #    "device_ext_libs": [<which device hooks extension libraries to use>]
    # }
}
