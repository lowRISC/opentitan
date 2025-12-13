# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(
    "@bazel_skylib//lib:dicts.bzl",
    "dicts",
)
load(
    "//rules/opentitan:defs.bzl",
    "EARLGREY_SILICON_OWNER_ROM_EXT_ENVS",
    "EARLGREY_TEST_ENVS",
    "fpga_params",
    "opentitan_binary",
    "opentitan_test",
    "silicon_params",
    "verilator_params",
)

package(default_visibility = ["//visibility:public"])

PENTEST_EXEC_ENVS = dicts.add(
    {
        "//hw/top_earlgrey:fpga_cw310_test_rom": None,
        "//hw/top_earlgrey:fpga_cw340_test_rom": None,
        "//hw/top_earlgrey:fpga_cw340_sival_rom_ext": None,
        "//hw/top_earlgrey:fpga_cw340_rom_ext": None,
    },
    EARLGREY_SILICON_OWNER_ROM_EXT_ENVS,
)

FIRMWARE_DEPS_FI = [
    "//sw/device/tests/penetrationtests/firmware/fi:alert_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:crypto_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:lc_ctrl_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:otp_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:rng_fi",
    "//sw/device/tests/penetrationtests/firmware/fi:rom_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
    "//sw/device/lib/base:csr",
    "//sw/device/lib/base:status",
    "//sw/device/lib/crypto/drivers:entropy",
    "//sw/device/lib/testing:entropy_src_testutils",
    "//sw/device/lib/testing/test_framework:check",
    "//sw/device/lib/testing/test_framework:ottf_main",
    "//sw/device/lib/testing/test_framework:ujson_ottf",
    "//sw/device/lib/ujson",

    # Include all JSON commands.
    "//sw/device/tests/penetrationtests/json:commands",
]

FIRMWARE_DEPS_FI_IBEX = [
    "//sw/device/tests/penetrationtests/firmware/fi:ibex_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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

FIRMWARE_DEPS_FI_OTBN = [
    "//sw/device/tests/penetrationtests/firmware/fi:otbn_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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
    "//sw/device/tests/penetrationtests/firmware/sca:edn_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:hmac_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:ibex_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:kmac_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:otbn_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:prng_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:sha3_sca",
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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

FIRMWARE_DEPS_CRYPTOLIB_FI_SYM = [
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/fi:cryptolib_fi_sym",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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

FIRMWARE_DEPS_CRYPTOLIB_FI_ASYM = [
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/fi:cryptolib_fi_asym",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
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

FIRMWARE_DEPS_CRYPTOLIB_SCA_SYM = [
    "//sw/device/tests/penetrationtests/firmware/sca:cryptolib_sca_sym",
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
    "//sw/device/tests/penetrationtests/firmware/sca:prng_sca",
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

FIRMWARE_DEPS_CRYPTOLIB_SCA_ASYM = [
    "//sw/device/tests/penetrationtests/firmware/sca:cryptolib_sca_asym",
    "//sw/device/tests/penetrationtests/firmware/sca:trigger_sca",
    "//sw/device/tests/penetrationtests/firmware/lib:extclk_sca_fi",
    "//sw/device/tests/penetrationtests/firmware/lib:pentest_lib",
    "//sw/device/tests/penetrationtests/firmware/sca:prng_sca",
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

# Note that the targets below are only to build the software, to run tests, see the BUILD from penetrationtests

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_fi",
    srcs = [":firmware_fi.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_FI,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_fi_ibex",
    srcs = [":firmware_fi_ibex.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_FI_IBEX,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_fi_otbn",
    srcs = [":firmware_fi_otbn.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_FI_OTBN,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_sca",
    srcs = [":firmware_sca.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_SCA,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_cryptolib_fi_sym",
    srcs = [":firmware_cryptolib_fi_sym.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_CRYPTOLIB_FI_SYM,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_cryptolib_fi_asym",
    srcs = [":firmware_cryptolib_fi_asym.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_CRYPTOLIB_FI_ASYM,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_cryptolib_sca_sym",
    srcs = [":firmware_cryptolib_sca_sym.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_CRYPTOLIB_SCA_SYM,
)

# Not an actual test, only for building purposes
opentitan_test(
    name = "pen_test_cryptolib_sca_asym",
    srcs = [":firmware_cryptolib_sca_asym.c"],
    exec_env = PENTEST_EXEC_ENVS,
    # Tags are manual since these are not actually tests, but these create binaries to run the pentest framework
    fpga = fpga_params(tags = [
        "manual",
        "skip_in_ci",
    ]),
    silicon = silicon_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    verilator = verilator_params(
        tags = [
            "manual",
            "skip_in_ci",
        ],
    ),
    deps = FIRMWARE_DEPS_CRYPTOLIB_SCA_ASYM,
)
