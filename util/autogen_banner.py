# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from textwrap import fill

# REUSE-IgnoreStart
LICENSE_BANNER = (
    "Copyright lowRISC contributors (OpenTitan project).\n"
    "Licensed under the Apache License, Version 2.0, see LICENSE for details.\n"
    "SPDX-License-Identifier: Apache-2.0")
# REUSE-IgnoreEnd

AUTOGEN_BANNER = (
    "THIS FILE HAS BEEN GENERATED, DO NOT EDIT MANUALLY. COMMAND:\n{command}")

MAX_LEN = 70


def get_autogen_banner(command: str, comment: str = "") -> str:
    """Returns a commented out auto-generated code warning banner.

    command is a fully formatted string representing what command was used
    to auto-generate the source.
    comment is the style of comment supported by the file type.
    """
    command = fill(command.strip(),
                   width=MAX_LEN,
                   break_long_words=False,
                   break_on_hyphens=False)
    text = AUTOGEN_BANNER.format(command=command)
    return apply_comment(text, comment)


def get_license_banner(comment: str = "") -> str:
    """Returns a commented out license banner.

    comment is the style of comment supported by the source file type.
    """
    return apply_comment(LICENSE_BANNER, comment)


def apply_comment(text: str, comment: str) -> str:
    """Applies comment to a text paragraph.

    The returned string terminates in a newline.
    """
    if comment:
        comment += " "
    return "\n".join([f"{comment}{line}" for line in text.split("\n")]) + "\n"
