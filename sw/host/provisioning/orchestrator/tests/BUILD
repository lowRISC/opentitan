# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_test")
load("//sw/host/provisioning/orchestrator/tests:transition.bzl", "orchestrator_test_settings_transition")

package(default_visibility = ["//visibility:public"])

py_test(
    name = "db_test",
    srcs = ["db_test.py"],
    deps = [
        "//sw/host/provisioning/orchestrator/src:db",
    ],
)

py_test(
    name = "device_id_test",
    srcs = ["device_id_test.py"],
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:dice_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:ext_ca.pem",
        "//sw/device/silicon_creator/manuf/keys/fake:sk.pkcs8.der",
        "//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
    ],
    deps = [
        requirement("hjson"),
        "//sw/host/provisioning/orchestrator/src:device_id",
        "//sw/host/provisioning/orchestrator/src:sku_config",
        "//sw/host/provisioning/orchestrator/src:util",
    ],
)

# This transition has the same effect as supplying the following flags to bazel test:
#  --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys
#  --//hw/bitstream/universal:otp=//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked0_manuf_empty
orchestrator_test_settings_transition(
    name = "orchestrator_zip",
    testonly = True,
    target = "//sw/host/provisioning/orchestrator/src:orchestrator.zip",
)

sh_test(
    name = "e2e_test",
    srcs = ["e2e.sh"],
    data = [
        ":orchestrator_zip",
        "@rules_python//python:current_py_toolchain",
    ],
    env = {
        "PYTHON": "$(PYTHON3)",
    },
    tags = [
        "hyper310",
        "manuf",
    ],
    toolchains = ["@rules_python//python:current_py_toolchain"],
)
