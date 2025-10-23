# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:const.bzl", "CONST", "hex")
load(
    "//rules/opentitan:defs.bzl",
    "DEFAULT_TEST_FAILURE_MSG",
    "DEFAULT_TEST_SUCCESS_MSG",
    "EARLGREY_TEST_ENVS",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "qemu_params",
)
load("//rules:manifest.bzl", "manifest")

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "boot_svc_test_lib",
    srcs = ["boot_svc_test_lib.c"],
    hdrs = ["boot_svc_test_lib.h"],
    deps = [
        "//sw/device/lib/base:status",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

# Note: the boot_svc commands for ownership_{activate,unlock} are tested by
# the ownership transfer tests.  These two commands are unlike the rest of
# the ownership commands in that they require a nonce, the device
# identification number and a signature, and thus require far more test
# infrastructure than the common boot_svc commands.

opentitan_test(
    name = "boot_svc_empty_test",
    srcs = ["boot_svc_empty_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "FinalBootLog: 4:AAAA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    qemu = qemu_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "FinalBootLog: 4:AAAA\r\n",
    ),
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_empty",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_enter_rescue_test",
    srcs = ["boot_svc_enter_rescue_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        timeout = "moderate",
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "mode: RESQ\r\n",
        test_cmd = """
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            # Try the `REBO` mode and make sure it works.
            --exec="rescue no-op --reset-target=reboot"
            no-op
        """,
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    qemu = qemu_params(
        timeout = "moderate",
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV|PASS|FAIL",
        exit_success = "mode: RESQ\r\n",
        # TODO: add bootstrap when QEMU bootstraps instead of splicing firmware
        test_cmd = """
            --exec="transport init"
            --exec="console --non-interactive --exit-success='{exit_success}' --exit-failure='{exit_failure}'"
            # Try the `REBO` mode and make sure it works.
            --exec="rescue no-op --reset-target=reboot"
            no-op
        """,
    ),
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_enter_rescue",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_after_wakeup_disabled_test",
    srcs = ["boot_svc_wakeup_test.c"],
    defines = ["BOOT_SVC_AFTER_WAKEUP_ENABLED=0"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        # Not supported in QEMU whilst low power is not modelled
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a}",
        #exit_failure = "BFV|PASS|FAIL",
        #exit_success = "FinalBootLog: 2:AA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_empty",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_after_wakeup_enabled_test",
    srcs = ["boot_svc_wakeup_test.c"],
    defines = ["BOOT_SVC_AFTER_WAKEUP_ENABLED=1"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        # Not supported in QEMU whilst low power is not modelled
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a}",
        rom_ext = "//sw/device/silicon_creator/rom_ext:rom_ext_boot_svc_after_wakeup",
        testopt_clear_after_test = "True",
        testopt_clear_before_test = "True",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/dif:aon_timer",
        "//sw/device/lib/dif:pwrmgr",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing:pwrmgr_testutils",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_empty",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

NEXT_TEST_SEQUENCES = [
    "AAB",
    "ABA",
    "ABB",
]

[
    opentitan_test(
        name = "boot_svc_next_{}_test".format(test_sequence.lower()),
        srcs = ["boot_svc_next_test.c"],
        defines = ["TEST_SEQUENCE_{}=1".format(test_sequence)],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
            exit_failure = "BFV:.*|PASS|FAIL",
            exit_success = "FinalBootLog: 3:{}\r\n".format(test_sequence),
            testopt_clear_after_test = "True",  # Clear the primary slot settings
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        qemu = qemu_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
            exit_failure = "BFV:.*|PASS|FAIL",
            exit_success = "FinalBootLog: 3:{}\r\n".format(test_sequence),
        ),
        deps = [
            ":boot_svc_test_lib",
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for test_sequence in NEXT_TEST_SEQUENCES
]

opentitan_test(
    name = "boot_svc_primary_test",
    srcs = ["boot_svc_primary_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 5:ABBBA\r\n",
        testopt_clear_before_test = "True",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    qemu = qemu_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 5:ABBBA\r\n",
        # TODO: add bootstrap when QEMU bootstraps instead of splicing firmware
    ),
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_bad_next_test",
    srcs = ["boot_svc_bad_next_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:AAA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    qemu = qemu_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:AAA\r\n",
    ),
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

opentitan_test(
    name = "boot_svc_bad_primary_test",
    srcs = ["boot_svc_bad_primary_test.c"],
    exec_env = {
        "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
        "//hw/top_earlgrey:sim_qemu_rom_ext": None,
    },
    fpga = fpga_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:ABA\r\n",
    ),
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    qemu = qemu_params(
        assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{owner_slot_a} {firmware}@{owner_slot_b}",
        exit_failure = "BFV:.*|PASS|FAIL",
        exit_success = "FinalBootLog: 3:ABA\r\n",
    ),
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_next_boot_bl0_slot",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

manifest({
    "name": "manifest_version_4",
    "address_translation": hex(CONST.HARDENED_TRUE),
    "security_version": "4",
    "identifier": hex(CONST.OWNER),
})

manifest({
    "name": "manifest_version_5",
    "address_translation": hex(CONST.HARDENED_TRUE),
    "security_version": "5",
    "identifier": hex(CONST.OWNER),
})

opentitan_binary(
    name = "min_sec_ver_5",
    testonly = True,
    srcs = ["boot_svc_min_sec_ver_test.c"],
    exec_env = [
        "//hw/top_earlgrey:fpga_hyper310_rom_ext",
        "//hw/top_earlgrey:fpga_cw340_rom_ext",
        "//hw/top_earlgrey:sim_qemu_rom_ext",
    ],
    linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
    manifest = ":manifest_version_5",
    deps = [
        ":boot_svc_test_lib",
        "//sw/device/lib/base:status",
        "//sw/device/lib/runtime:log",
        "//sw/device/lib/testing/test_framework:check",
        "//sw/device/lib/testing/test_framework:ottf_main",
        "//sw/device/silicon_creator/lib:boot_log",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_min_bl0_sec_ver",
        "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
        "//sw/device/silicon_creator/lib/drivers:retention_sram",
        "//sw/device/silicon_creator/lib/drivers:rstmgr",
    ],
)

MIN_SEC_VER_SLOTS = [
    "ab",
    "ba",
]

[
    opentitan_test(
        name = "boot_svc_min_sec_ver_{}_test".format(slots[1]),
        srcs = ["boot_svc_min_sec_ver_test.c"],
        exec_env = {
            "//hw/top_earlgrey:fpga_hyper310_rom_ext": None,
            "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
            "//hw/top_earlgrey:sim_qemu_rom_ext": None,
        },
        fpga = fpga_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{v0_slot} {min_sec_ver_5:signed_bin}@{v5_slot}",
            binaries = {
                ":min_sec_ver_5": "min_sec_ver_5",
            },
            testopt_clear_after_test = "True",
            testopt_clear_before_test = "True",
            v0_slot = "{{owner_slot_{}}}".format(slots[0]),
            v5_slot = "{{owner_slot_{}}}".format(slots[1]),
        ),
        linker_script = "//sw/device/lib/testing/test_framework:ottf_ld_silicon_owner_slot_virtual",
        manifest = ":manifest_version_4",
        qemu = qemu_params(
            assemble = "{rom_ext}@{rom_ext_slot_a} {firmware}@{v0_slot} {min_sec_ver_5:signed_bin}@{v5_slot}",
            binaries = {
                ":min_sec_ver_5": "min_sec_ver_5",
            },
            v0_slot = "{{owner_slot_{}}}".format(slots[0]),
            v5_slot = "{{owner_slot_{}}}".format(slots[1]),
        ),
        deps = [
            ":boot_svc_test_lib",
            "//sw/device/lib/base:status",
            "//sw/device/lib/runtime:log",
            "//sw/device/lib/testing/test_framework:check",
            "//sw/device/lib/testing/test_framework:ottf_main",
            "//sw/device/silicon_creator/lib:boot_log",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_min_bl0_sec_ver",
            "//sw/device/silicon_creator/lib/boot_svc:boot_svc_msg",
            "//sw/device/silicon_creator/lib/drivers:retention_sram",
            "//sw/device/silicon_creator/lib/drivers:rstmgr",
        ],
    )
    for slots in MIN_SEC_VER_SLOTS
]
