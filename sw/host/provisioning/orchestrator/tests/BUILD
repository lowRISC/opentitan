# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")
load("@rules_python//python:defs.bzl", "py_test")
load(
    "//sw/device/silicon_creator/manuf/base:provisioning_inputs.bzl",
    "EARLGREY_SKUS",
)
load(
    "//sw/host/provisioning/orchestrator/tests:defs.bzl",
    "orchestrator_test",
)

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
        "//sw/device/silicon_creator/manuf/keys/fake:rma_unlock_enc_rsa3072.pub.der",
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

py_test(
    name = "util_test",
    srcs = ["util_test.py"],
    data = [
        "//sw/device/silicon_creator/manuf/keys/fake:dice_ca.pem",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
    ],
    deps = [
        "//sw/host/provisioning/orchestrator/src:util",
    ],
)

EMULATION_SKUS = {
    "emulation": {
        "orchestrator_cfg": "//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
    },
}

EXEC_ENVS = {
    "//hw/top_earlgrey:fpga_cw310_rom_with_fake_keys": "cw310",
    "//hw/top_earlgrey:fpga_cw340_rom_with_fake_keys": "cw340",
}

orchestrator_test(
    name = "e2e_option_flags_test",
    timeout = "moderate",
    src = "e2e_option_flags.sh",
    env = {
        "PACKAGE": "npcr12",
    },
    exec_env = EXEC_ENVS,
    orchestrator = "//sw/host/provisioning/orchestrator/src:orchestrator",
    skus = EMULATION_SKUS,
)

orchestrator_test(
    name = "e2e_ate_individ_test",
    src = "e2e_ate_individ.sh",
    exec_env = EXEC_ENVS,
    orchestrator = "//sw/host/provisioning/orchestrator/src:orchestrator",
    skus = EMULATION_SKUS,
)

orchestrator_test(
    name = "e2e_multistage_test",
    src = "e2e_multistage.sh",
    exec_env = EXEC_ENVS,
    orchestrator = "//sw/host/provisioning/orchestrator/src:orchestrator",
    skus = EARLGREY_SKUS,
)

orchestrator_test(
    name = "e2e_test",
    timeout = "moderate",
    src = "e2e.sh",
    exec_env = EXEC_ENVS,
    orchestrator = "//sw/host/provisioning/orchestrator/src:orchestrator",
    skus = EARLGREY_SKUS,
)

[
    test_suite(
        name = "e2e_{}".format(fpga),
        tags = ["manual"],
        tests = [
            ":e2e_test_{}_{}".format(
                sku,
                exec_env.split(":")[-1],
            )
            for sku, config in EARLGREY_SKUS.items()
            if not config.get("offline", False)
        ],
    )
    for exec_env, fpga in EXEC_ENVS.items()
]

[
    test_suite(
        name = "e2e_including_offline_{}".format(fpga),
        tags = ["manual"],
        tests = [
            ":e2e_test_{}_{}".format(
                sku,
                exec_env.split(":")[-1],
            )
            for sku in EARLGREY_SKUS.keys()
        ],
    )
    for exec_env, fpga in EXEC_ENVS.items()
]
