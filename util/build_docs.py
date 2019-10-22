#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Usage:
#   run './build_docs.py' to generate the documentation and keep it updated
#   open 'http://localhost:1313/' to check live update (this opens the top
#   level index page). you can also directly access a specific document by
#   accessing 'http://localhost:1313/path/to/doc',
#       e.g. http://localhost:1313/hw/ip/uart/doc

import argparse
import io
import logging
import os
import shutil
import subprocess
from pathlib import Path

import hjson

import dashboard.gen_dashboard_entry as gen_dashboard_entry
import reggen.gen_cfg_html as gen_cfg_html
import reggen.gen_html as gen_html
import reggen.validate as validate
import testplanner.testplan_utils as testplan_utils

USAGE = """
  build_docs [options]
"""

# Configurations
# TODO: Move to config.yaml
SRCTREE_TOP = Path(__file__).parent.joinpath('..').resolve()
config = {
    # Toplevel source directory
    "topdir":
    SRCTREE_TOP,

    # Pre-generate register and hwcfg fragments from these files.
    "hardware_definitions": [
        "hw/ip/aes/data/aes.hjson",
        "hw/ip/alert_handler/data/alert_handler.hjson",
        "hw/ip/flash_ctrl/data/flash_ctrl.hjson",
        "hw/ip/gpio/data/gpio.hjson",
        "hw/ip/hmac/data/hmac.hjson",
        "hw/ip/i2c/data/i2c.hjson",
        "hw/ip/padctrl/data/padctrl.hjson",
        "hw/ip/pinmux/data/pinmux.hjson",
        "hw/ip/rv_plic/data/rv_plic.hjson",
        "hw/ip/rv_timer/data/rv_timer.hjson",
        "hw/ip/spi_device/data/spi_device.hjson",
        "hw/ip/uart/data/uart.hjson",
        "hw/ip/usbdev/data/usbdev.hjson",
        "hw/ip/usbuart/data/usbuart.hjson",
    ],

    # Pre-generate dashboard fragments from these directories.
    "dashboard_definitions": [
        "hw/ip",
    ],

    # Pre-generate testplan fragments from these files.
    "testplan_definitions": [
        "hw/ip/gpio/data/gpio_testplan.hjson",
        "hw/ip/hmac/data/hmac_testplan.hjson",
        "hw/ip/i2c/data/i2c_testplan.hjson",
        "hw/ip/rv_timer/data/rv_timer_testplan.hjson",
        "hw/ip/uart/data/uart_testplan.hjson",
        "util/testplanner/examples/foo_testplan.hjson",
    ],

    # Output directory for documents
    "outdir":
    SRCTREE_TOP.joinpath('build', 'docs'),
    "outdir-generated":
    SRCTREE_TOP.joinpath('build', 'docs-generated'),
    "verbose":
    False,
}


def generate_dashboards():
    for dashboard in config["dashboard_definitions"]:
        hjson_paths = []
        hjson_paths.extend(
            sorted(SRCTREE_TOP.joinpath(dashboard).rglob('*.prj.hjson')))

        dashboard_path = config["outdir-generated"].joinpath(
            dashboard, 'dashboard')
        dashboard_html = open(dashboard_path, mode='w')
        for hjson_path in hjson_paths:
            gen_dashboard_entry.gen_dashboard_html(hjson_path, dashboard_html)
        dashboard_html.close()


def generate_hardware_blocks():
    for hardware in config["hardware_definitions"]:
        hardware_file = open(SRCTREE_TOP.joinpath(hardware))
        regs = hjson.load(hardware_file,
                          use_decimal=True,
                          object_pairs_hook=validate.checking_dict)
        if validate.validate(regs) == 0:
            logging.info("Parsed %s" % (hardware))
        else:
            logging.fatal("Failed to parse %s" % (hardware))

        base_path = config["outdir-generated"].joinpath(hardware)
        base_path.parent.mkdir(parents=True, exist_ok=True)

        regs_html = open(base_path.parent.joinpath(base_path.name +
                                                   '.registers'),
                         mode='w')
        gen_html.gen_html(regs, regs_html)
        regs_html.close()

        hwcfg_html = open(base_path.parent.joinpath(base_path.name + '.hwcfg'),
                          mode='w')
        gen_cfg_html.gen_cfg_html(regs, hwcfg_html)
        hwcfg_html.close()


def generate_testplans():
    for testplan in config["testplan_definitions"]:
        plan = testplan_utils.parse_testplan(SRCTREE_TOP.joinpath(testplan))

        plan_path = config["outdir-generated"].joinpath(testplan + '.testplan')
        plan_path.parent.mkdir(parents=True, exist_ok=True)

        testplan_html = open(plan_path, mode='w')
        testplan_utils.gen_html_testplan_table(plan, testplan_html)
        testplan_html.close()


def invoke_hugo(preview):
    site_docs = SRCTREE_TOP.joinpath('site', 'docs')
    config_file = str(site_docs.joinpath('config.toml'))
    layout_dir = str(site_docs.joinpath('layouts'))
    args = [
        "hugo",
        "--config",
        config_file,
        "--destination",
        str(config["outdir"]),
        "--contentDir",
        str(SRCTREE_TOP),
        "--layoutDir",
        layout_dir,
    ]
    if preview:
        args += ["server"]
    subprocess.run(args, check=True, cwd=SRCTREE_TOP)


def main():
    logging.basicConfig(level=logging.INFO,
                        format="%(asctime)s - %(message)s",
                        datefmt="%Y-%m-%d %H:%M")

    parser = argparse.ArgumentParser(
        prog="build_docs",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        usage=USAGE)
    parser.add_argument(
        '--preview',
        action='store_true',
        help="""starts a local server with live reload (updates triggered upon
             changes in the documentation files). this feature is intended
             to preview the documentation locally.""")
    parser.add_argument('--hugo', help="""TODO""")

    args = parser.parse_args()

    generate_hardware_blocks()
    generate_dashboards()
    generate_testplans()
    invoke_hugo(args.preview)


if __name__ == "__main__":
    main()
