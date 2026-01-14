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
    "//sw/host/provisioning/orchestrator/tests:transition.bzl",
    "orchestrator_cw310_test_settings_transition",
    "orchestrator_cw340_test_settings_transition",
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

# These transitions have the same effect as supplying the following flags to bazel test:
#  --//hw/bitstream/universal:env=//hw/top_earlgrey:fpga_<fpga>_rom_with_fake_keys
#  --//hw/bitstream/universal:otp=//hw/top_earlgrey/data/otp/emulation:otp_img_test_unlocked0_manuf_empty
orchestrator_cw310_test_settings_transition(
    name = "orchestrator_cw310_zip",
    testonly = True,
    target = "//sw/host/provisioning/orchestrator/src:orchestrator.zip",
)

orchestrator_cw340_test_settings_transition(
    name = "orchestrator_cw340_zip",
    testonly = True,
    target = "//sw/host/provisioning/orchestrator/src:orchestrator.zip",
)

[
    sh_test(
        name = "e2e_option_flags_test_{}".format(fpga),
        timeout = "moderate",
        srcs = ["e2e_option_flags.sh"],
        data = [
            ":orchestrator_{}_zip".format(fpga),
            "@//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
            "@python3",
        ],
        env = {
            "PYTHON": "$(location @python3//:python3)",
            "PACKAGE": "npcr12",
            "FPGA": "{}".format(fpga),
        },
        tags = [
            "changes_otp",
            "exclusive",
            "fpga",
            "manuf",
        ] + [fpga],
    )
    for fpga in [
        "cw310",
        "cw340",
    ]
]

[
    sh_test(
        name = "e2e_ate_individ_test_{}".format(fpga),
        timeout = "moderate",
        srcs = ["e2e_ate_individ.sh"],
        data = [
            ":orchestrator_{}_zip".format(fpga),
            "@//sw/host/provisioning/orchestrator/configs/skus:emulation.hjson",
            "@python3",
        ],
        env = {
            "PYTHON": "$(location @python3//:python3)",
            "PACKAGE": "npcr12",
            "FPGA": "{}".format(fpga),
        },
        tags = [
            "changes_otp",
            "exclusive",
            "fpga",
            "manuf",
        ] + [fpga],
    )
    for fpga in [
        "cw310",
        "cw340",
    ]
]

[
    sh_test(
        name = "e2e_{}_{}_multistage_test".format(sku, fpga),
        srcs = ["e2e_multistage.sh"],
        data = [
            ":orchestrator_{}_zip".format(fpga),
            cfg["orchestrator_cfg"],
            "@python3",
        ],
        env = {
            "PYTHON": "$(location @python3//:python3)",
            "SKU_CONFIG_PATH": "$(location {})".format(cfg["orchestrator_cfg"]),
            "FPGA": "{}".format(fpga),
        },
        tags = [
            "changes_otp",
            "exclusive",
            "manuf",
        ] + [fpga] + ([
            "manual",
        ] if cfg.get("offline", False) else []),
    )
    for sku, cfg in EARLGREY_SKUS.items()
    for fpga in [
        "cw310",
        "cw340",
    ]
]

[
    sh_test(
        name = "e2e_{}_{}_test".format(sku, fpga),
        timeout = "moderate",
        srcs = ["e2e.sh"],
        data = [
            ":orchestrator_{}_zip".format(fpga),
            cfg["orchestrator_cfg"],
            "@python3",
        ],
        env = {
            "PYTHON": "$(location @python3//:python3)",
            "SKU_CONFIG_PATH": "$(location {})".format(cfg["orchestrator_cfg"]),
            "FPGA": "{}".format(fpga),
        },
        tags = [
            "changes_otp",
            "exclusive",
            "manuf",
        ] + [fpga] + ([
            "manual",
        ] if cfg.get("offline", False) else []),
    )
    for sku, cfg in EARLGREY_SKUS.items()
    for fpga in [
        "cw310",
        "cw340",
    ]
]

[
    test_suite(
        name = "e2e_{}".format(fpga),
        tags = ["manual"],
        tests = [
            ":e2e_{}_{}_test".format(sku, fpga)
            for sku, config in EARLGREY_SKUS.items()
            if not config.get("offline", False)
        ],
    )
    for fpga in [
        "cw310",
        "cw340",
    ]
]

[
    test_suite(
        name = "e2e_including_offline_{}".format(fpga),
        tags = ["manual"],
        tests = [
            ":e2e_{}_{}_test".format(sku, fpga)
            for sku in EARLGREY_SKUS.keys()
        ],
    )
    for fpga in [
        "cw310",
        "cw340",
    ]
]
