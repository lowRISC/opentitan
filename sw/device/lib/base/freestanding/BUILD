# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

cc_library(
    name = "freestanding",
    hdrs = [
        "assert.h",
        "float.h",
        "iso646.h",
        "limits.h",
        "stdalign.h",
        "stdarg.h",
        "stdbool.h",
        "stddef.h",
        "stdint.h",
        "stdnoreturn.h",
    ],
    deprecation =
        "Do not depend on this target; instead, include its headers via " +
        "system header includes like #include <stdint.h>",
)
