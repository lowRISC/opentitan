# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//sw/device/lib/arch:device.bzl", "opentitan_device")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "device",
    hdrs = ["device.h"],
    visibility = ["//visibility:public"],
)

cc_library(
    name = "fpga_nexysvideo_impl",
    srcs = ["device_fpga_nexysvideo.c"],
    deps = [":device"],
)

cc_library(
    name = "fpga_cw310_impl",
    srcs = ["device_fpga_cw310.c"],
    deps = [":device"],
)

opentitan_device(
    name = "fpga_cw310",
    data = ["//sw/host/opentitantool/config"],
    default_args = [
        "--exec=\"console -q -t0\"",
        "--exec=\"bootstrap {flash}\"",
        "console",
        "--exit-success=PASS.*\n",
        "--exit-failure=(FAIL|FAULT).*\n",
        "--timeout=3600s",
    ],
    device_impl = ":fpga_cw310_impl",
    required_args = [
        "--rcfile=",
        "--logging=info",
        "--interface=cw310",
        "--conf=sw/host/opentitantool/config/opentitan_cw310.json",
    ],
    runner = "//sw/host/opentitantool",
    visibility = ["//visibility:public"],
)

cc_library(
    name = "sim_dv_impl",
    srcs = ["device_sim_dv.c"],
    deps = [":device"],
)

opentitan_device(
    name = "sim_dv",
    data = [
        "//hw:all_files",
        "//util/dvsim",
    ],
    device_impl = ":sim_dv_impl",
    dvsim_config = "//hw/top_earlgrey/dv:chip_sim_cfg.hjson",
    is_dv = True,
    required_args = [
        "-i",
        "chip_sw_{name}",
    ],
    runner = "//util:dvsim_test_runner.sh",
    uses_vmem = True,
    visibility = ["//visibility:public"],
)

cc_library(
    name = "sim_verilator_impl",
    srcs = ["device_sim_verilator.c"],
    deps = [":device"],
)

opentitan_device(
    name = "sim_verilator",
    data = [
        "//hw:verilator",
        "//sw/host/opentitantool/config",
    ],
    default_args = [
        "console",
        "--exit-success=PASS.*\n",
        "--exit-failure=(FAIL|FAULT).*\n",
        "--timeout=3600s",
    ],
    device_impl = ":sim_verilator_impl",
    required_args = [
        "--rcfile=",
        "--logging=info",
        "--interface=verilator",
        "--conf=sw/host/opentitantool/config/opentitan_verilator.json",
        "--verilator-bin=hw/build.verilator/sim-verilator/Vchip_sim_tb",
        "--verilator-rom={rom}",
        "--verilator-flash={flash}",
        "--verilator-otp={otp}",
    ],
    runner = "//sw/host/opentitantool",
    uses_vmem = True,
    visibility = ["//visibility:public"],
)
