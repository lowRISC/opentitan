# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex", "hex_digits")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
)
load(
    "//sw/device/silicon_creator/rom_ext:defs.bzl",
    "ROM_EXT_VERSION",
)
load(
    "//rules:manifest.bzl",
    "integrator_specific_firmware_binding",
    "isfb_erase_allowed_policy",
    "manifest",
    "product_expr",
)

manifest(d = {
    "name": "manifest_allow_isfb_erase",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "device_id": [
        hex(CONST.DEFAULT_USAGE_CONSTRAINTS),
        hex(0x66666666),
        hex(0x55555555),
    ],
    "isfb_erase_allowed_policy": isfb_erase_allowed_policy(
        name = "isfb_erase_allowed",
        erase_allowed = True,
    ),
})

manifest(d = {
    "name": "manifest_bad_erase_contraint",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "isfb_erase_allowed_policy": isfb_erase_allowed_policy(
        name = "isfb_erase_allowed",
        erase_allowed = True,
    ),
})

opentitan_binary(
    name = "isfb_page_init",
    testonly = True,
    srcs = ["isfb_page_test.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_cw310_rom_ext",
        "//hw/top_earlgrey:fpga_cw340_rom_ext",
    ],
    manifest = ":manifest_allow_isfb_erase",
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "isfb_page_test",
    srcs = ["isfb_page_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        # Check that bank=0 page=5 is configured for RD/WR, but not ERase.
        exit_success = "info region bank=0 part=0 page=5 RD-WR-uu-uu-uu-uu LK",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_isfb",
        testopt_clear_after_test = "True",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

opentitan_test(
    name = "isfb_page_bad_erase_constraint_test",
    srcs = ["isfb_page_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    fpga = fpga_params(
        # Even though the isfb_erase extension is present and set to true,
        # the manifest doesn't node lock this image.  The erase condition
        # is not met and the ISFB page should not allow erase.
        # Check that bank=0 page=5 is configured for RD/WR, but not ERase.
        exit_success = "info region bank=0 part=0 page=5 RD-WR-uu-uu-uu-uu LK",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_isfb",
        testopt_clear_after_test = "True",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = ":manifest_bad_erase_contraint",
    deps = [
        "//hw/top_earlgrey/ip_autogen/flash_ctrl:flash_ctrl_c_regs",
        "//hw/top_earlgrey/sw/autogen:top_earlgrey",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:flash_ctrl",
        "//sw/device/lib/runtime:print",
        "//sw/device/lib/testing:flash_ctrl_testutils",
        "//sw/device/lib/testing/test_framework:ottf_main",
    ],
)

manifest(d = {
    "name": "manifest_isfb_product_expr",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "integrator_specific_firmware_binding": integrator_specific_firmware_binding(
        name = "isfb",
        product_exprs = [
            product_expr(
                name = "abc-product",
                mask = "0xffffffff",
                value = "0x44434241",
            ),
            product_expr(
                name = "wx-feature",
                mask = "0x0000FFFF",
                value = "0x00005857",
            ),
        ],
        strike_mask = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE",
    ),
})

manifest(d = {
    "name": "manifest_isfb_bad_product_expr",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "integrator_specific_firmware_binding": integrator_specific_firmware_binding(
        name = "isfb",
        product_exprs = [
            product_expr(
                name = "abc-product",
                mask = "0xffffffff",
                value = "0x44434241",
            ),
            product_expr(
                name = "uu-feature",
                mask = "0x0000FFFF",
                value = "0x00005555",
            ),
        ],
        strike_mask = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE",
    ),
})

manifest(d = {
    "name": "manifest_isfb_bad_strike_mask",
    "identifier": hex(CONST.OWNER),
    "visibility": ["//visibility:public"],
    "integrator_specific_firmware_binding": integrator_specific_firmware_binding(
        name = "isfb",
        product_exprs = [
            product_expr(
                name = "abc-product",
                mask = "0xFFFFFFFF",
                value = "0x44434241",
            ),
            product_expr(
                name = "wx-feature",
                mask = "0x0000FFFF",
                value = "0x00005857",
            ),
        ],
        strike_mask = "0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
    ),
})

_ISFB_CONTRAINT_TESTS = {
    "unconstrained": {
        "manifest": "//sw/device/silicon_owner:manifest",
        "success": DEFAULT_TEST_SUCCESS_MSG,
        "failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "product_expr": {
        "manifest": ":manifest_isfb_product_expr",
        "success": DEFAULT_TEST_SUCCESS_MSG,
        "failure": DEFAULT_TEST_FAILURE_MSG,
    },
    "bad_product_expr": {
        "manifest": ":manifest_isfb_bad_product_expr",
        "success": "BFV:{}".format(hex_digits(CONST.BFV.ISFB.PRODUCT_EXP)),
        "failure": DEFAULT_TEST_SUCCESS_MSG,
    },
    "bad_strike_mask": {
        "manifest": ":manifest_isfb_bad_strike_mask",
        "success": "BFV:{}".format(hex_digits(CONST.BFV.ISFB.STRIKE_MASK)),
        "failure": DEFAULT_TEST_SUCCESS_MSG,
    },
}

[
    opentitan_test(
        name = "isfb_{}_test".format(name),
        srcs = ["//sw/device/silicon_creator/rom_ext/e2e/verified_boot:boot_test"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        },
        fpga = fpga_params(
            timeout = "long",
            binaries = {
                ":isfb_page_init": "isfb_page_init",
            },
            exit_failure = param["failure"],
            exit_success = param["success"],
            rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_isfb",
            test_cmd = """
                --exec="image assemble --output=init.bin --mirror=false --size=524288 {rom_ext}@{rom_ext_slot_a} {isfb_page_init}@{owner_slot_a}"
                --exec="bootstrap --clear-uart=true init.bin"
                --exec="console --non-interactive --exit-success='PASS!' --timeout=10s"
                --exec="bootstrap --clear-uart=true {firmware}"
                --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}' --timeout=10s"
                no-op
            """,
            testopt_bootstrap = "False",
            testopt_clear_after_test = "True",
            testopt_clear_before_test = "True",
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        manifest = param["manifest"],
        deps = [
            "//sw/device/lib/base:status",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/drivers:flash_ctrl",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/ownership:datatypes",
        ],
    )
    for name, param in _ISFB_CONTRAINT_TESTS.items()
]
