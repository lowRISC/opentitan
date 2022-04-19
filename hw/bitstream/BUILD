# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

# Use a bitstream from the GCP bucket (this is also the default condition).
# You can control the GCP bitstream selection via the BITSTREAM environment
# variable.  See //rules/bitstreams.bzl for more information.
#
# Example:
#   bazel test //sw/device/silicon_creator/lib/drivers:fpga_cw310_hmac_functest --define bitstream=gcp
config_setting(
    name = "bitstream_gcp",
    define_values = {
        "bitstream": "gcp",
    },
)

# Skip loading a bitstream in to the FPGA.  This is useful if you already
# have a bitstream loaded into the FPGA and you don't want the GCP cache
# manager to do anything unexpected.
#
# Example:
#   bazel test //sw/device/silicon_creator/lib/drivers:fpga_cw310_hmac_functest --define bitstream=skip
config_setting(
    name = "bitstream_skip",
    define_values = {
        "bitstream": "skip",
    },
)

# Use a bitstream built by Vivado.  You'll need to have Xilinx Vivado
# installed and have properly configured access to a license or license
# server.
#
# Example:
#   bazel test //sw/device/silicon_creator/lib/drivers:fpga_cw310_hmac_functest --define bitstream=vivado
config_setting(
    name = "bitstream_vivado",
    define_values = {
        "bitstream": "vivado",
    },
)

filegroup(
    name = "test_rom",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_test_rom"],
        "bitstream_gcp": ["@bitstreams//:bitstream_test_rom"],
        "//conditions:default": ["@bitstreams//:bitstream_test_rom"],
    }),
)

filegroup(
    name = "mask_rom",
    srcs = select({
        "bitstream_skip": ["skip.bit"],
        "bitstream_vivado": ["//hw/bitstream/vivado:fpga_cw310_mask_rom"],
        "bitstream_gcp": ["@bitstreams//:bitstream_mask_rom"],
        "//conditions:default": ["@bitstreams//:bitstream_mask_rom"],
    }),
)
