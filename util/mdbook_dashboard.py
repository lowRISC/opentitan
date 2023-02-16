#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import json
import sys
import io
import re
from pathlib import Path

import dashboard.gen_dashboard_entry as dashboard
from mdbook import utils as md_utils

# We are looking to match on the following example strings
# {{#dashboard comportable }}
DASHBOARD_PATTERN = re.compile(r'\{\{#dashboard\s+?(.+?)\s*\}\}')
IP_CFG_PATTERN = re.compile(r'.+/data/(?!.+(_testplan|example)).+\.hjson')
REPO_TOP = Path(__file__).resolve().parents[1]

# FIXME: It would be nice if this isn't hard coded.
DASHBOARDS = {
    'comportable': [
        "hw/ip/aes/data/aes.hjson",
        "hw/ip/aon_timer/data/aon_timer.hjson",
        "hw/ip/entropy_src/data/entropy_src.hjson",
        "hw/ip/csrng/data/csrng.hjson",
        "hw/ip/adc_ctrl/data/adc_ctrl.hjson",
        "hw/ip/edn/data/edn.hjson",
        "hw/ip/flash_ctrl/data/flash_ctrl.hjson",
        "hw/ip/gpio/data/gpio.hjson",
        "hw/ip/hmac/data/hmac.hjson",
        "hw/ip/i2c/data/i2c.hjson",
        "hw/ip/keymgr/data/keymgr.hjson",
        "hw/ip/kmac/data/kmac.hjson",
        "hw/ip/lc_ctrl/data/lc_ctrl.hjson",
        "hw/ip/otbn/data/otbn.hjson",
        "hw/ip/otp_ctrl/data/otp_ctrl.hjson",
        "hw/ip/pattgen/data/pattgen.hjson",
        "hw/ip/pwm/data/pwm.hjson",
        "hw/ip/rom_ctrl/data/rom_ctrl.hjson",
        "hw/ip/rv_dm/data/rv_dm.hjson",
        "hw/ip/rv_core_ibex/data/rv_core_ibex.hjson",
        "hw/ip/rv_timer/data/rv_timer.hjson",
        "hw/ip/spi_host/data/spi_host.hjson",
        "hw/ip/spi_device/data/spi_device.hjson",
        "hw/ip/sram_ctrl/data/sram_ctrl.hjson",
        "hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson",
        "hw/ip/uart/data/uart.hjson",
        "hw/ip/usbdev/data/usbdev.hjson",
    ],
    'top_earlgrey': [
        "hw/top_earlgrey/ip_autogen/alert_handler/data/alert_handler.hjson",
        "hw/top_earlgrey/ip/pinmux/data/autogen/pinmux.hjson",
        "hw/top_earlgrey/ip/clkmgr/data/autogen/clkmgr.hjson",
        "hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson",
        "hw/top_earlgrey/ip/rstmgr/data/autogen/rstmgr.hjson",
        "hw/top_earlgrey/ip/sensor_ctrl/data/sensor_ctrl.hjson",
        "hw/top_earlgrey/ip_autogen/rv_plic/data/rv_plic.hjson",
    ],
}

DASHBOARD_TEMPLATE = """
<table class="hw-project-dashboard">
  <thead>
    <tr>
      <th>Design Spec</th>
      <th>DV Document</th>
      <th><a href="/doc/project_governance/development_stages.html#versioning">Spec Version</a></th>
      <th colspan="4">
        <a href="/doc/project_governance/development_stages.html#life-stages">
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
    for cfg_file in sorted(cfg_files):
        dashboard.gen_dashboard_html(REPO_TOP / cfg_file, buffer)

    return DASHBOARD_TEMPLATE.format(buffer.getvalue())


if __name__ == "__main__":
    main()
