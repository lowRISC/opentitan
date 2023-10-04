# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

def legacy_rom_targets(target, suffixes):
    """Create filegroups for legacy ROM rule target names.

    Creates the `<name>_rom` and `<name>_scr_vmem` targets required by the
    `opentitan_functest` macro.

    Args:
      target: The name of the new `opentitan_binary` ROM target.
      targets: The suffix names to use when creating filegroups.
    """
    for suffix in suffixes:
        native.filegroup(
            name = "{}_{}".format(target, suffix),
            srcs = [":{}".format(target)],
            output_group = select({
                "//sw/device:is_english_breakfast": "{}_rom32".format(suffix),
                "//conditions:default": "{}_rom".format(suffix),
            }),
        )
        native.alias(
            name = "{}_{}_scr_vmem".format(target, suffix),
            actual = ":{}_{}".format(target, suffix),
        )
