#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
import argparse
import hjson
from pathlib import Path
from typing import Optional, Tuple

# This scripts generates a markdown table with regression links and badges for an IP README file,
# based on the IP's data hjson file.

# IPs which were taped out as part of Earl Grey 1.0.0.
# Extracted from branch earlgrey_1.0.0
EG100_TAPED_OUT_IPS = [
    "adc_ctrl",
    "aes",
    "aon_timer",
    "csrng",
    "edn",
    "entropy_src",
    "gpio",
    "hmac",
    "i2c",
    "keymgr",
    "kmac",
    "lc_ctrl",
    "otbn",
    "otp_ctrl",
    "pattgen",
    "pinmux",
    "pwm",
    "rom_ctrl",
    "rv_core_ibex",
    "rv_dm",
    "rv_timer",
    "spi_device",
    "spi_host",
    "sram_ctrl",
    "sysrst_ctrl",
    "uart",
    "usbdev",
]

# IPs which were generated per top (ipgen) and taped out as part of Earl Grey 1.0.0.
# Extracted from branch earlgrey_1.0.0 (hw/top_earlgrey/ip_autogen)
EG100_TAPED_OUT_IPGEN_IPS = [
    "alert_handler",
    "clkmgr",
    "flash_ctrl",
    "pwrmgr",
    "rstmgr",
    "rv_plic",
]

# Top-specific IPs which were taped out as part of Earl Grey 1.0.0.
# Extracted from branch earlgrey_1.0.0 (hw/top_earlgrey/ip)
# The AST in hw/top_earlgrey/ip/ast is an open-source model; the taped-out AST is closed source.
EG100_TAPED_OUT_TOP_SPECIFIC_IPS = [
    "sensor_ctrl",
]

# For some IPs the regression results are hosted outside the standard opentitan dashboard.
# Keys are IP names; values override the report URL and badge base URL used in the table.
CUSTOM_IP_REGRESSION_URLS = {
    "rv_core_ibex": {
        "report_url": "https://ibex.reports.lowrisc.org/opentitan/latest/report.html",
        "badge_base": "https://dashboard.reports.lowrisc.org/badges/dv/ibex/opentitan",
    },
}

# For some IPs there are multiple regressions with different naming. Any IP not listed here has one
# regression named after its name.
REGRESSIONS_PER_IP = {
    "aes": ["masked", "unmasked"],
    "kmac": ["masked", "unmasked"],
    "sram_ctrl": ["main", "ret"],
    "entropy_src": ["rng_4bits"],
    "edn": ["edn0", "edn1"],
    "lc_ctrl": ["volatile_unlock_enabled", "volatile_unlock_disabled"],
    "rom_ctrl": ["32kb", "64kb"],
    "rv_dm": ["use_jtag_interface"],
    "spi_device": ["1r1w", "2p"],
}


def parse_data_file(hjson_path: str) -> Tuple[str, str, str, str]:
    with Path(hjson_path).open() as f:
        block_data = hjson.load(f)

    try:
        return (
            block_data['name'],
            block_data['version'],
            block_data['design_stage'],
            block_data['verification_stage'],
        )
    except KeyError:
        # Assumes the last value is the most recent
        revision = block_data['revisions'][-1]
        return (
            block_data['name'],
            revision['version'],
            revision['design_stage'],
            revision['verification_stage'],
        )


def generate_links_for_regs_and_badges(ipname: str, topname: str) -> Tuple[list[str], list[str]]:
    if ipname in CUSTOM_IP_REGRESSION_URLS:
        custom = CUSTOM_IP_REGRESSION_URLS[ipname]
        return (
            [f"[`{ipname}`]({custom['report_url']})"],
            [custom["badge_base"]],
        )

    regression_base_url = f"https://dashboard.reports.lowrisc.org/opentitan/{topname}"
    # TODO: We link all regressions to the main dashboard as there are currently links to the
    # separate regression results.
    latest_reg_all_url = (f"{regression_base_url}/dashboard.html")

    badge_base_link = f"https://dashboard.reports.lowrisc.org/opentitan/{topname}/badge"

    regression_names = ([f"{ipname}_{reg}" for reg in REGRESSIONS_PER_IP[ipname]]
                        if ipname in REGRESSIONS_PER_IP else [ipname])

    regression_links = [f"[`{name}`]({latest_reg_all_url})" for name in regression_names]
    badge_links = [f"{badge_base_link}/{name}" for name in regression_names]

    return regression_links, badge_links


def eg100_doc_url(ipname: str) -> Optional[str]:
    """Return the URL of the Earl Grey 1.0.0 documentation of an IP, if it was taped out."""
    if ipname in EG100_TAPED_OUT_IPS:
        ip_dir = "hw/ip"
    elif ipname in EG100_TAPED_OUT_IPGEN_IPS:
        ip_dir = "hw/top_earlgrey/ip_autogen"
    elif ipname in EG100_TAPED_OUT_TOP_SPECIFIC_IPS:
        ip_dir = "hw/top_earlgrey/ip"
    else:
        return None
    return f"https://opentitan.org/earlgrey_1.0.0/book/{ip_dir}/{ipname}/index.html"


def generate_regression_table(ip_hjson_path: str, topname: str) -> str:
    ipname, version, design_stage, verification_stage = parse_data_file(ip_hjson_path)

    regression_links, badge_links = generate_links_for_regs_and_badges(ipname, topname)

    block_lines = []

    dev_stage_url = "https://opentitan.org/book/doc/project_governance/development_stages.html"

    block_lines += [
        f"| Regression | Version | [Stages]({dev_stage_url}) | Results |",
        "|-|-|-|-|",
    ]

    for reg_link, badge_link in zip(regression_links, badge_links):
        block_lines += [
            f" {reg_link} | {version} | {design_stage}, {verification_stage} | "
            f"![]({badge_link}/test.svg) ![]({badge_link}/passing.svg) "
            f"![]({badge_link}/functional.svg) ![]({badge_link}/code.svg) |",
        ]

    egv100_doc_url = eg100_doc_url(ipname)
    if egv100_doc_url is not None and topname == "earlgrey":
        block_lines += [
            "",
            "This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation and "
            f"regression results can be found [here]({egv100_doc_url})."
        ]

    return "\n".join(block_lines)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Generate regression and status table for an IP README file."
    )

    parser.add_argument("--topname", type=str, default="earlgrey",
                        help="The topname to link the regression results to.")

    parser.add_argument("--hjson", type=str, default=None,
                        help="The IP hjson file for which to generate the regression info for.")

    args = parser.parse_args()

    print(generate_regression_table(args.hjson, args.topname))
