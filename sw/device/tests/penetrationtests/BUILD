# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(":pentest.bzl", "pentest_fi", "pentest_fi_otbn")

package(default_visibility = ["//visibility:public"])

IBEX_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_ibex",
]

IBEX_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-ibex-json=\"$(rootpath {})\"".format(target)
    for target in IBEX_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_ibex",
    slow_test = False,
    test_args = IBEX_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_ibex:harness",
    test_vectors = IBEX_FI_TESTVECTOR_TARGETS,
)

CRYPTO_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_crypto",
]

CRYPTO_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-crypto-json=\"$(rootpath {})\"".format(target)
    for target in CRYPTO_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_crypto",
    slow_test = True,
    test_args = CRYPTO_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_crypto:harness",
    test_vectors = CRYPTO_FI_TESTVECTOR_TARGETS,
)

LCCTRL_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_lc_ctrl",
]

LCCTRL_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-lc-ctrl-json=\"$(rootpath {})\"".format(target)
    for target in LCCTRL_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_lc_ctrl",
    slow_test = True,
    test_args = LCCTRL_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_lc_ctrl:harness",
    test_vectors = LCCTRL_FI_TESTVECTOR_TARGETS,
)

OTP_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_otp",
]

OTP_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-otp-json=\"$(rootpath {})\"".format(target)
    for target in OTP_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_otp",
    slow_test = True,
    test_args = OTP_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_otp:harness",
    test_vectors = OTP_FI_TESTVECTOR_TARGETS,
)

RNG_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_rng",
]

RNG_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-rng-json=\"$(rootpath {})\"".format(target)
    for target in RNG_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_rng",
    slow_test = True,
    test_args = RNG_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_rng:harness",
    test_vectors = RNG_FI_TESTVECTOR_TARGETS,
)

ROM_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_rom",
]

ROM_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-rom-json=\"$(rootpath {})\"".format(target)
    for target in ROM_FI_TESTVECTOR_TARGETS
])

pentest_fi(
    name = "fi_rom",
    slow_test = True,
    test_args = ROM_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_rom:harness",
    test_vectors = ROM_FI_TESTVECTOR_TARGETS,
)

OTBN_FI_TESTVECTOR_TARGETS = [
    "//sw/host/penetrationtests/testvectors/data:fi_otbn",
]

OTBN_FI_TESTVECTOR_ARGS = " ".join([
    "--fi-otbn-json=\"$(rootpath {})\"".format(target)
    for target in OTBN_FI_TESTVECTOR_TARGETS
])

pentest_fi_otbn(
    name = "fi_otbn",
    slow_test = True,
    test_args = OTBN_FI_TESTVECTOR_ARGS,
    test_harness = "//sw/host/tests/penetrationtests/fi_otbn:harness",
    test_vectors = OTBN_FI_TESTVECTOR_TARGETS,
)
