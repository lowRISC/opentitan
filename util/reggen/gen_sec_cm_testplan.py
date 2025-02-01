# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate the initial testplan for the listed countermeasures."""

import logging as log
from pathlib import Path

import hjson  # type: ignore
from mako import exceptions  # type: ignore
from mako.lookup import TemplateLookup  # type: ignore
import importlib_resources

from reggen.ip_block import IpBlock


def gen_sec_cm_testplan(block: IpBlock, outdir: str) -> int:
    """Generate the security countermeasures testplan.

    A new testplan is created only if it does not exist yet. If it already
    exists, then it checks if the list of countermeasures match the list
    of countermeasures in the design specification Hjson. If not, it throws
    an error to prompt the user to keep the testplan up-to-date manually.
    """
    if not block.countermeasures:
        return 0

    outfile = Path(outdir) / f"{block.name.lower()}_sec_cm_testplan.hjson"
    if outfile.exists():
        names_from_testplan = []
        with open(outfile, "r", encoding='UTF-8') as f:
            data = hjson.load(f)
            try:
                names_from_testplan = [tp["name"] for tp in data["testpoints"]]
            except KeyError as e:
                raise KeyError(f"Malformed testplan {outfile}:\n{e}")

        # Check if the testpoint names match the list in the design spec.
        names_from_spec = [
            "sec_cm_{}".format(str(cm).lower().replace(".", "_"))
            for cm in block.countermeasures
        ]

        if sorted(names_from_spec) != sorted(names_from_testplan):
            log.error("The generated security countermeasures testplan "
                      f"{outfile} is stale. Please manually update it "
                      "with the newly added (or removed) countermeasures.\n"
                      f"Deltas:\nSpec: {names_from_spec}\n"
                      f"Testplan: {names_from_testplan}.")
            return 1

        return 0

    lookup = TemplateLookup(directories=[str(importlib_resources.files('reggen'))])
    sec_cm_testplan_tpl = lookup.get_template('sec_cm_testplan.hjson.tpl')
    with open(outfile, 'w', encoding='UTF-8') as f:
        try:
            f.write(
                sec_cm_testplan_tpl.render(block=block,
                                           block_name=block.name.lower()))
        except:  # noqa F722 for template Exception handling
            log.error(exceptions.text_error_template().render())
            return 1

    return 0
