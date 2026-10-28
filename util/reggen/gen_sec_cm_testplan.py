# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Generate the initial testplan for the listed countermeasures."""

import collections
import logging as log
from pathlib import Path

import hjson  # type: ignore
from mako import exceptions  # type: ignore
from mako.lookup import TemplateLookup  # type: ignore
import importlib.resources

from reggen.ip_block import IpBlock


def load_hjson_to_dict(path: Path) -> dict | None:
    """Try to load the hjson file at path into a dictionary

    If there is no file at path, returns None. If there is a file, but this
    doesn't parse correctly as hjson, raise a RuntimeError.
    """
    if path.exists():
        with open(path, "r", encoding="UTF-8") as f:
            try:
                return hjson.load(f)
            except Exception as e:
                msg = f"Failed to parse hjson from {path}: {e}"
                raise RuntimeError(msg) from e
    else:
        return None


def get_names_from_testplan(testplan: dict) -> list[str]:
    """Read a parsed testplan and return a list with its testpoint names."""

    testpoints = testplan.get("testpoints")
    if testpoints is None:
        raise ValueError("No testpoints key in testplan dictionary.")

    names = []
    for idx, tp in enumerate(testpoints):
        if not isinstance(tp, dict):
            msg = f"Item {idx} in testpoints list is not a dict."
            raise ValueError(msg)

        name = tp.get("name")
        if name is None:
            msg = f"Item {idx} in testpoints list has no name."
            raise ValueError(msg)

        if not isinstance(name, str):
            msg = f"Name of item {idx} in testpoints list is not a string."
            raise ValueError(msg)

        names.append(name)

    return names

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
    parsed_testplan = load_hjson_to_dict(outfile)

    if parsed_testplan is not None:
        try:
            names_from_testplan = get_names_from_testplan(parsed_testplan)
        except Exception as e:
            msg = f"Error reading testplan at {outfile}: {e}"
            raise RuntimeError(msg) from e

        tp_names_set = set(names_from_testplan)
        if len(tp_names_set) != len(names_from_testplan):
            # If there is a difference here then converting to a set has
            # removed a duplicate name.
            counts = collections.Counter(names_from_testplan)
            duplicates = {name for name, count in counts.items() if count > 1}
            msg = f"Duplicate names in testplan at {outfile}: {duplicates}."
            raise RuntimeError(msg)

        # Check if the testpoint names match the list in the design spec.
        names_from_spec = [
            "sec_cm_{}".format(str(cm).lower().replace(".", "_"))
            for cm in block.countermeasures
        ]
        spec_names_set = set(names_from_spec)

        if tp_names_set != spec_names_set:
            spec_not_tp = spec_names_set - tp_names_set
            tp_not_spec = tp_names_set - spec_names_set

            msg_lines = [f"The list of testpoints in {outfile} doesn't match the "
                         "names inferred from the spec."]
            if spec_not_tp:
                msg_lines.append("\nNames from spec with no testpoint:")
                for name in sorted(spec_not_tp):
                    msg_lines.append(f" - {name}")
            if tp_not_spec:
                msg_lines.append("\nTestpoints with no countermeasure:")
                for name in sorted(tp_not_spec):
                    msg_lines.append(f" - {name}")

            log.error("\n".join(msg_lines))
            return 1

        return 0

    lookup = TemplateLookup(
        directories=[str(importlib.resources.files('reggen'))])
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
