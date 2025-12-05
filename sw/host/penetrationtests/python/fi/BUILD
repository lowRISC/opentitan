# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("@ot_python_deps//:requirements.bzl", "requirement")

package(default_visibility = ["//visibility:public"])

py_binary(
    name = "fi_ibex_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_ibex_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_ibex",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_ibex_commands",
        "//sw/host/penetrationtests/python/fi:fi_ibex_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_crypto_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_crypto_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_crypto",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_crypto_commands",
        "//sw/host/penetrationtests/python/fi:fi_crypto_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_otbn_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_otbn_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_otbn",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_otbn_commands",
        "//sw/host/penetrationtests/python/fi:fi_otbn_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_otp_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_otp_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_otp",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_otp_commands",
        "//sw/host/penetrationtests/python/fi:fi_otp_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_rom_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_rom_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_rom",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_rom_commands",
        "//sw/host/penetrationtests/python/fi:fi_rom_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_alert_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_alert_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_alert_commands",
        "//sw/host/penetrationtests/python/fi:fi_alert_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_rng_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_rng_python_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//sw/host/penetrationtests/python/fi/gold_responses:fi_rng",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_rng_commands",
        "//sw/host/penetrationtests/python/fi:fi_rng_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
    ],
)

py_binary(
    name = "fi_sym_cryptolib_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_sym_cryptolib_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_sym_cryptolib_commands",
        "//sw/host/penetrationtests/python/fi:fi_sym_cryptolib_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_rom_ext_python_gdb_test",
    testonly = True,
    srcs = ["gdb_testing/fi_rom_ext_python_gdb_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:openocd_bin",
        "//util/openocd/target:lowrisc-earlgrey.cfg",
        "@lowrisc_rv32imcb_toolchain//:bin/riscv32-unknown-elf-gdb",
    ],
    deps = [
        "//sw/host/penetrationtests/python/util:dis_parser",
        "//sw/host/penetrationtests/python/util:gdb_controller",
        "//sw/host/penetrationtests/python/util:targets",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_rom_ext_rollback_python_gdb_test",
    testonly = True,
    srcs = ["gdb_testing/fi_rom_ext_rollback_python_gdb_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:openocd_bin",
        "//util/openocd/target:lowrisc-earlgrey.cfg",
        "@lowrisc_rv32imcb_toolchain//:bin/riscv32-unknown-elf-gdb",
    ],
    deps = [
        "//sw/host/penetrationtests/python/util:dis_parser",
        "//sw/host/penetrationtests/python/util:gdb_controller",
        "//sw/host/penetrationtests/python/util:targets",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_sym_cryptolib_python_gdb_test",
    testonly = True,
    srcs = ["gdb_testing/fi_sym_cryptolib_python_gdb_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:openocd_bin",
        "//util/openocd/target:lowrisc-earlgrey.cfg",
        "@lowrisc_rv32imcb_toolchain//:bin/riscv32-unknown-elf-gdb",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_sym_cryptolib_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:dis_parser",
        "//sw/host/penetrationtests/python/util:gdb_controller",
        "//sw/host/penetrationtests/python/util:targets",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_asym_cryptolib_python_test",
    testonly = True,
    srcs = ["test_scripts/fi_asym_cryptolib_python_test.py"],
    data = [
        "//sw/host/opentitantool",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_asym_cryptolib_commands",
        "//sw/host/penetrationtests/python/fi:fi_asym_cryptolib_functions",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
        "//sw/host/penetrationtests/python/util:utils",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_binary(
    name = "fi_asym_cryptolib_python_gdb_test",
    testonly = True,
    srcs = ["gdb_testing/fi_asym_cryptolib_python_gdb_test.py"],
    data = [
        "//sw/host/opentitantool",
        "//third_party/openocd:jtag_cmsis_dap_adapter_cfg",
        "//third_party/openocd:openocd_bin",
        "//util/openocd/target:lowrisc-earlgrey.cfg",
        "@lowrisc_rv32imcb_toolchain//:bin/riscv32-unknown-elf-gdb",
    ],
    deps = [
        "//sw/host/penetrationtests/python/fi:fi_asym_cryptolib_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:dis_parser",
        "//sw/host/penetrationtests/python/util:gdb_controller",
        "//sw/host/penetrationtests/python/util:targets",
        "@rules_python//python/runfiles",
        requirement("pycryptodome"),
    ],
)

py_library(
    name = "fi_ibex_functions",
    srcs = ["host_scripts/fi_ibex_functions.py"],
    deps = [
        ":fi_ibex_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_crypto_functions",
    srcs = ["host_scripts/fi_crypto_functions.py"],
    deps = [
        ":fi_crypto_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_otbn_functions",
    srcs = ["host_scripts/fi_otbn_functions.py"],
    deps = [
        ":fi_otbn_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_otp_functions",
    srcs = ["host_scripts/fi_otp_functions.py"],
    deps = [
        ":fi_otp_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_rom_functions",
    srcs = ["host_scripts/fi_rom_functions.py"],
    deps = [
        ":fi_rom_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_alert_functions",
    srcs = ["host_scripts/fi_alert_functions.py"],
    deps = [
        ":fi_alert_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_rng_functions",
    srcs = ["host_scripts/fi_rng_functions.py"],
    deps = [
        ":fi_rng_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_sym_cryptolib_functions",
    srcs = ["host_scripts/fi_sym_cryptolib_functions.py"],
    deps = [
        ":fi_sym_cryptolib_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_asym_cryptolib_functions",
    srcs = ["host_scripts/fi_asym_cryptolib_functions.py"],
    deps = [
        ":fi_asym_cryptolib_commands",
        "//sw/host/penetrationtests/python/util:common_library",
        "//sw/host/penetrationtests/python/util:targets",
    ],
)

py_library(
    name = "fi_ibex_commands",
    srcs = ["communication/fi_ibex_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_crypto_commands",
    srcs = ["communication/fi_crypto_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_otbn_commands",
    srcs = ["communication/fi_otbn_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_otp_commands",
    srcs = ["communication/fi_otp_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_rng_commands",
    srcs = ["communication/fi_rng_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_rom_commands",
    srcs = ["communication/fi_rom_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_alert_commands",
    srcs = ["communication/fi_alert_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_sym_cryptolib_commands",
    srcs = ["communication/fi_sym_cryptolib_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)

py_library(
    name = "fi_asym_cryptolib_commands",
    srcs = ["communication/fi_asym_cryptolib_commands.py"],
    deps = ["//sw/host/penetrationtests/python/util:common_library"],
)
