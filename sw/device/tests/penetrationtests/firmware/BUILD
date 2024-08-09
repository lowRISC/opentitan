# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "//rules/opentitan:defs.bzl",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
)

package(default_visibility = ["//visibility:public"])

FIRMWARE_DEPS_FPGA = [
    "//sw/device/tests/penetrationtests/firmware/fi:ibex_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:otbn_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:rng_fi",
    "//sw/device/tests/penetrationtests/firmware/sca:aes_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:ibex_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:kmac_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:prng_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:sha3_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/penetrationtests/json:commands",
]

FIRMWARE_DEPS_FI = [
    "//sw/device/tests/penetrationtests/firmware/fi:ibex_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:otbn_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:rng_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/penetrationtests/json:commands",
]

FIRMWARE_DEPS_SCA = [
    "//sw/device/tests/penetrationtests/firmware/sca:aes_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:ibex_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:kmac_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:prng_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:sha3_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/penetrationtests/json:commands",
]

[
    opentitan_binary(
        name = "firmware_{}".format(exec_env),
        testonly = True,
        srcs = [":firmware.c"],
        exec_env = [
            "//hw/top_earlgrey:{}".format(exec_env),
        ],
        deps = FIRMWARE_DEPS_FPGA,
    )
    for exec_env in [
        "fpga_cw310_test_rom",
    ]
]

opentitan_test(
    name = "chip_pen_test_fi",
    srcs = [":firmware_fi.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon_owner = silicon_params(
        tags = [
            "broken",
            "manual",
        ],
    ),
    deps = FIRMWARE_DEPS_FI,
)

opentitan_test(
    name = "chip_pen_test_sca",
    srcs = [":firmware_sca.c"],
    exec_env = {
        "//hw/top_earlgrey:silicon_owner_sival_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:silicon_owner_prodc_rom_ext": "silicon_owner",
        "//hw/top_earlgrey:sim_dv": None,
    },
    silicon_owner = silicon_params(
        tags = [
            "broken",
            "manual",
        ],
    ),
    deps = FIRMWARE_DEPS_SCA,
)
