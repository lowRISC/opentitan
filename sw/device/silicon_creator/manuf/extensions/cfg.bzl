# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

HOST_FT_EXTS = select({
    "@provisioning_exts//:example_perso_ext_cfg": ["@provisioning_exts//:example_ft_ext_lib"],
    "//conditions:default": ["@provisioning_exts//:default_ft_ext_lib"],
})
