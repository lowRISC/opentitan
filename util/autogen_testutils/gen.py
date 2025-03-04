#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from pathlib import Path
from typing import Dict, List

from autogen_banner import get_autogen_banner
from make_new_dif.ip import Ip
from mako.template import Template

# This file is $REPO_TOP/util/autogen_testutils.py, so it takes two parent()
# calls to get back to the top.
REPO_TOP = Path(__file__).resolve().parent.parent.parent


def gen_testutils(outdir: Path,
                  completecfg: Dict[str, object],
                  ips_with_difs: List[Ip]) -> List[Path]:
    """Generate testutils libraries that are rendered from Mako templates.

    Args:
        ips_with_difs: List of IP objects that have existing DIF libraries.

    Returns:
        List of files created.
    """
    # Sort input so the templates get rendered in the same order every time.
    ips_with_difs.sort(key=lambda ip: ip.name_snake)

    # Define input/output directories.
    testutils_templates_dir = REPO_TOP / "util/autogen_testutils/templates"

    # Create output directories if needed.
    outdir.mkdir(exist_ok=True)

    testutilses = []

    # Render templates.
    for testutils_template_path in testutils_templates_dir.iterdir():
        if testutils_template_path.suffix == ".tpl":
            comment_syntax = "#" if testutils_template_path.stem.endswith(
                ".build") else "//"
            # Read in template, render it, and write it to the output file.
            testutils_template = Template(testutils_template_path.read_text())
            testutils = outdir / testutils_template_path.stem
            testutils.write_text(
                testutils_template.render(
                    ips_with_difs=ips_with_difs,
                    autogen_banner=get_autogen_banner(
                        "util/autogen_testutils.py",
                        comment=comment_syntax
                    ),
                    top = completecfg,
                )
            )
            testutilses += [testutils]

    return testutilses
