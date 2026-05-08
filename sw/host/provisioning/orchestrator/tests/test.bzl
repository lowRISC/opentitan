# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
load("//rules/opentitan:defs.bzl", "opentitan_alias_test")

def opentitan_sh_test(name, **kwargs):
    """
    This macros morally behaves like `sh_test` but in addition registers the
    test with the CI. In the details, two targets will be created, one using
    `sh_test` and the other using `opentitan_alias_test`. The following tags
    will be applied to the latter target if they are present:
    - exclusive
    """
    TAGS_TO_PRESERVE = ["exclusive", "manual"]
    sh_name = name + "_sh"
    native.sh_test(
        name = sh_name,
        **kwargs
    )
    opentitan_alias_test(
        name = name,
        actual = ":" + sh_name,
        tags = [tag for tag in TAGS_TO_PRESERVE if tag in kwargs.get("tags", [])],
    )
