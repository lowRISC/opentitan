# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

# Configure opentitantool for execution in the CI's CW310 container.
#
# Example:
#   bazel test //sw/device/silicon_creator/lib/drivers:hmac_functest_fpga_cw310 --define cw310=lowrisc
config_setting(
    name = "lowrisc_fpga_cw310",
    define_values = {
        "cw310": "lowrisc",
    },
)

config_setting(
    name = "lowrisc_fpga_cw340",
    define_values = {
        "cw340": "lowrisc",
    },
)
