# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

load(":defs.bzl", "TESTS", "rv_compliance_test")

package(default_visibility = ["//visibility:public"])

[[rv_compliance_test(test, arch) for test in tests] for arch, tests in TESTS.items()]
