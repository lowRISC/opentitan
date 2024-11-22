# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

package(default_visibility = ["//visibility:public"])

filegroup(
    name = "ecdsa_signatures",
    srcs = glob(
        ["*.ecdsa_sig"],
        # TODO(#25361): Eliminate this exclude and source signatures from the
        # external @provisioning_exts repo.
        exclude = glob(["ft_personalize_gb_*"]),
    ),
)

filegroup(
    name = "spx_signatures",
    srcs = glob(["*.spx_sig"]),
)
