#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
import hjson  # type: ignore [import]
import logging as log
import sys

from reggen import ip_block, register, multi_register, field, window


def extend_optional_fields(arg_vendor_file: str) -> None:
    """Extend the optional fields with vendor specific fields, in case it is defined."""

    vendor_specific = import_fields(arg_vendor_file)

    _extend_fields(vendor_specific, "ip_block", ip_block.OPTIONAL_FIELDS)
    _extend_fields(vendor_specific, "register", register.OPTIONAL_FIELDS)
    _extend_fields(vendor_specific, "register", multi_register.OPTIONAL_FIELDS)
    _extend_fields(vendor_specific, "field", field.OPTIONAL_FIELDS)
    _extend_fields(vendor_specific, "window", window.OPTIONAL_FIELDS)


def _extend_fields(source: dict[str, str], name: str, dest: dict[str, list[str]]) -> None:
    if name not in source:
        return
    data = source[name]

    if not isinstance(data, dict):
        log.error(
            f"The following vendor specific attributes have the wrong type: {name}"
        )
        sys.exit(1)

    # Find overlapping keys using set intersection
    if overlap := data.keys() & dest.keys():
        log.error(
            f"The following vendor specific attributes are already defined: {', '.join(overlap)}"
        )
        sys.exit(1)

    dest.update(data)


def import_fields(vendor_file: str) -> dict[str, str]:
    """Return vendor specific fields."""

    vendor_specific = {}
    arg_vendor_file = Path(vendor_file)
    if arg_vendor_file.is_file():
        vendor_specific = hjson.load(arg_vendor_file.open("r"))
    else:
        log.error("File {} does not exist".format(vendor_file))
        sys.exit(1)

    return vendor_specific
