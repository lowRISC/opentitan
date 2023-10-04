#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import json
import sys
import io
import re
from pathlib import Path
from typing import Union, Tuple, List, Dict

import dashboard.gen_dashboard_entry as dashboard
from mdbook import utils as md_utils

# We are looking to match on the following example strings
# {{#dashboard comportable }}
DASHBOARD_PATTERN = re.compile(r'\{\{#dashboard\s+?(.+?)\s*\}\}')
IP_CFG_PATTERN = re.compile(r'.+/data/(?!.+(_testplan|example)).+\.hjson')
REPO_TOP = Path(__file__).resolve().parents[1]

# FIXME: It would be nice if this isn't hard coded.
DASHBOARDS: Dict[str, List[Union[Path, Tuple[Path, Path]]]] = {
    'comportable': [
        REPO_TOP / "hw/ip/aes/data/aes.hjson",
        REPO_TOP / "hw/ip/aon_timer/data/aon_timer.hjson",
        REPO_TOP / "hw/ip/entropy_src/data/entropy_src.hjson",
        REPO_TOP / "hw/ip/csrng/data/csrng.hjson",
        REPO_TOP / "hw/ip/adc_ctrl/data/adc_ctrl.hjson",
        REPO_TOP / "hw/ip/edn/data/edn.hjson",
        REPO_TOP / "hw/ip/flash_ctrl/data/flash_ctrl.hjson",
        REPO_TOP / "hw/ip/gpio/data/gpio.hjson",
        REPO_TOP / "hw/ip/hmac/data/hmac.hjson",
        REPO_TOP / "hw/ip/i2c/data/i2c.hjson",
        REPO_TOP / "hw/ip/keymgr/data/keymgr.hjson",
        REPO_TOP / "hw/ip/kmac/data/kmac.hjson",
        REPO_TOP / "hw/ip/lc_ctrl/data/lc_ctrl.hjson",
        REPO_TOP / "hw/ip/otbn/data/otbn.hjson",
        REPO_TOP / "hw/ip/otp_ctrl/data/otp_ctrl.hjson",
        REPO_TOP / "hw/ip/pattgen/data/pattgen.hjson",
        REPO_TOP / "hw/ip/pwm/data/pwm.hjson",
        REPO_TOP / "hw/ip/rom_ctrl/data/rom_ctrl.hjson",
        REPO_TOP / "hw/ip/rv_dm/data/rv_dm.hjson",
        REPO_TOP / "hw/ip/rv_core_ibex/data/rv_core_ibex.hjson",
        REPO_TOP / "hw/ip/rv_timer/data/rv_timer.hjson",
        REPO_TOP / "hw/ip/spi_host/data/spi_host.hjson",
        REPO_TOP / "hw/ip/spi_device/data/spi_device.hjson",
        REPO_TOP / "hw/ip/sram_ctrl/data/sram_ctrl.hjson",
        REPO_TOP / "hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson",
        REPO_TOP / "hw/ip/uart/data/uart.hjson",
        REPO_TOP / "hw/ip/usbdev/data/usbdev.hjson",
    ],
    'top_earlgrey': [
        (
            REPO_TOP / "hw/top_earlgrey/ip/pinmux/data/autogen/pinmux.hjson",
            REPO_TOP / "hw/ip/pinmux/",
        ),
        (
            REPO_TOP / "hw/top_earlgrey/ip/clkmgr/data/autogen/clkmgr.hjson",
            REPO_TOP / "hw/ip/clkmgr/",
        ),
        (
            REPO_TOP / "hw/top_earlgrey/ip_autogen/pwrmgr/data/pwrmgr.hjson",
            REPO_TOP / "hw/top_earlgrey/ip_autogen/pwrmgr/",
        ),
        (
            REPO_TOP / "hw/top_earlgrey/ip/rstmgr/data/autogen/rstmgr.hjson",
            REPO_TOP / "hw/ip/rstmgr/",
        ),
        REPO_TOP / "hw/top_earlgrey/ip_autogen/alert_handler/data/alert_handler.hjson",
        REPO_TOP / "hw/top_earlgrey/ip/sensor_ctrl/data/sensor_ctrl.hjson",
        REPO_TOP / "hw/top_earlgrey/ip_autogen/rv_plic/data/rv_plic.hjson",
    ],
}

DASHBOARD_TEMPLATE = """
<table class="hw-project-dashboard">
  <thead>
    <tr>
      <th>Design Spec</th>
      <th>DV Document</th>
      <th>
        <a href="/book/doc/project_governance/development_stages.html#versioning">
          Spec Version
        </a>
      </th>
      <th colspan="4">
        <a href="/book/doc/project_governance/development_stages.html#life-stages">
          Development Stage
        </a>
      </th>
      <th>Notes</th>
    </tr>
  </thead>
  <tbody>
{}
  </tbody>
</table>
"""


def main() -> None:
    md_utils.supports_html_only()

    # Generate the dashboards
    # gen_dashboards()

    # load both the context and the book from stdin
    context, book = json.load(sys.stdin)

    for chapter in md_utils.chapters(book["sections"]):
        # Add in the generated dashboard html
        chapter['content'] = DASHBOARD_PATTERN.sub(
            replace_with_dashboard,
            chapter['content'])

    # dump the book into stdout
    print(json.dumps(book))


def replace_with_dashboard(m: re.Match) -> str:
    name = m.group(1)

    try:
        cfg_files = DASHBOARDS[name]
    except KeyError:
        sys.exit("A dashboard with name {}, {{#dashboard {} }}, doesn't exist".format(name, name))

    buffer = io.StringIO()
    # Generate the rows for the hardware blocks in a sorted order.
    for cfg_file in sorted(
        cfg_files,
        # if tuple sort using the first element.
        key=lambda file: file[0] if isinstance(file, Tuple) else file
    ):
        dashboard.gen_dashboard_row_html(cfg_file, buffer)

    return DASHBOARD_TEMPLATE.format(buffer.getvalue())


if __name__ == "__main__":
    main()
