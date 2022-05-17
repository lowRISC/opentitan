# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load("//rules:opentitan_test.bzl", "opentitan_functest", "verilator_params")

def coremark_test():
    opentitan_functest(
        name = "coremark",
        srcs = [
            "top_earlgrey/core_portme.c",
            "top_earlgrey/ee_printf.c",
            #            "core_list_join.c",
            #            "core_main.c",
            #            "core_matrix.c",
            #            "core_state.c",
            #            "core_util.c",
        ],
        copts = [
            "-Wno-implicit-fallthrough",
            "-Wno-strict-prototypes",
            "-DITERATIONS=1",
            "-DPERFORMANCE_RUN=1",
            "-DTOTAL_DATA_SIZE=2000",
            "-DMAIN_HAS_NOARGC=1",
        ],
        linkopts = ["-Wl,--no-relax"],
        verilator = verilator_params(
            timeout = "long",
        ),
        deps = [
            "//sw/device/lib/testing/test_framework:ottf_main",
            "@coremark//:coremark_lib",
        ],
    )
