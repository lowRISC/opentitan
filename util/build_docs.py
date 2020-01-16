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
import platform
import re
import shutil
import subprocess
from pathlib import Path

import hjson

import dashboard.gen_dashboard_entry as gen_dashboard_entry
import reggen.gen_cfg_html as gen_cfg_html
import reggen.gen_html as gen_html
import reggen.validate as validate
import reggen.gen_selfdoc as reggen_selfdoc
import testplanner.testplan_utils as testplan_utils
import tlgen

USAGE = """
  build_docs [options]
"""

# Version of hugo extended to be used to build the docs
HUGO_EXTENDED_VERSION = "0.59.0"

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
        "hw/ip/entropy_src/data/entropy_src.hjson",
        "hw/ip/flash_ctrl/data/flash_ctrl.hjson",
        "hw/ip/gpio/data/gpio.hjson",
        "hw/ip/hmac/data/hmac.hjson",
        "hw/ip/i2c/data/i2c.hjson",
        "hw/ip/nmi_gen/data/nmi_gen.hjson",
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
        "hw/ip/aes/data/aes_testplan.hjson",
        "hw/ip/alert_handler/data/alert_handler_testplan.hjson",
        "hw/ip/gpio/data/gpio_testplan.hjson",
        "hw/ip/hmac/data/hmac_testplan.hjson",
        "hw/ip/i2c/data/i2c_testplan.hjson",
        "hw/ip/rv_plic/data/rv_plic_fpv_testplan.hjson",
        "hw/ip/rv_timer/data/rv_timer_testplan.hjson",
        "hw/ip/spi_device/data/spi_device_testplan.hjson",
        "hw/ip/uart/data/uart_testplan.hjson",
        "hw/ip/usbdev/data/usbdev_testplan.hjson",
        "hw/ip/tlul/data/tlul_testplan.hjson",
        "hw/top_earlgrey/data/standalone_sw_testplan.hjson",
        "util/testplanner/examples/foo_testplan.hjson",
    ],

    # Pre-generated utility selfdoc
    "selfdoc_tools": ["tlgen", "reggen"],

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
        dashboard_html = open(str(dashboard_path), mode='w')
        for hjson_path in hjson_paths:
            gen_dashboard_entry.gen_dashboard_html(hjson_path, dashboard_html)
        dashboard_html.close()


def generate_hardware_blocks():
    for hardware in config["hardware_definitions"]:
        hardware_file = open(str(SRCTREE_TOP.joinpath(hardware)))
        regs = hjson.load(hardware_file,
                          use_decimal=True,
                          object_pairs_hook=validate.checking_dict)
        if validate.validate(regs) == 0:
            logging.info("Parsed %s" % (hardware))
        else:
            logging.fatal("Failed to parse %s" % (hardware))

        base_path = config["outdir-generated"].joinpath(hardware)
        base_path.parent.mkdir(parents=True, exist_ok=True)

        regs_html = open(str(base_path.parent.joinpath(base_path.name +
                                                   '.registers')),
                         mode='w')
        gen_html.gen_html(regs, regs_html)
        regs_html.close()

        hwcfg_html = open(str(base_path.parent.joinpath(base_path.name + '.hwcfg')),
                          mode='w')
        gen_cfg_html.gen_cfg_html(regs, hwcfg_html)
        hwcfg_html.close()


def generate_testplans():
    for testplan in config["testplan_definitions"]:
        plan = testplan_utils.parse_testplan(SRCTREE_TOP.joinpath(testplan))

        plan_path = config["outdir-generated"].joinpath(testplan + '.testplan')
        plan_path.parent.mkdir(parents=True, exist_ok=True)

        testplan_html = open(str(plan_path), mode='w')
        testplan_utils.gen_html_testplan_table(plan, testplan_html)
        testplan_html.close()


def generate_selfdocs():
    """Generate documents for the tools in `util/` if `--doc` option exists.

    Each tool creates selfdoc differently. Manually invoked.
    """
    for tool in config["selfdoc_tools"]:
        selfdoc_path = config["outdir-generated"].joinpath(tool + '.selfdoc')
        selfdoc_path.parent.mkdir(parents=True, exist_ok=True)
        with open(str(selfdoc_path), mode='w') as fout:
            if tool == "reggen":
                reggen_selfdoc.document(fout)
            elif tool == "tlgen":
                fout.write(tlgen.selfdoc(heading=3, cmd='tlgen.py --doc'))


def is_hugo_extended():
    args = ["hugo", "version"]
    process = subprocess.run(args,
                             universal_newlines=True,
                             stdout=subprocess.PIPE,
                             check=True,
                             cwd=str(SRCTREE_TOP))

    # Hugo version string example:
    # Hugo Static Site Generator v0.59.0-1DD0C69C/extended linux/amd64 BuildDate: 2019-10-21T09:45:38Z
    return bool(re.search("v\d+\.\d+\.\d+-.*/extended", process.stdout))


def install_hugo(install_dir):
    """Download and "install" hugo into |install_dir|

    install_dir is created if it doesn't exist yet.

    Limitations:
      Currently only 64 bit Linux is supported."""

    # TODO: Support more configurations
    if platform.system() != 'Linux' or platform.machine() != 'x86_64':
        logging.fatal(
            "Auto-install of hugo only supported for 64 bit Linux "
            "currently. Manually install hugo and re-run this script.")
        return False

    download_url = 'https://github.com/gohugoio/hugo/releases/download/v{version}/hugo_extended_{version}_Linux-64bit.tar.gz'.format(
        version=HUGO_EXTENDED_VERSION)

    install_dir.mkdir(exist_ok=True, parents=True)
    hugo_bin_path = install_dir / 'hugo'

    # TODO: Investigate the use of Python builtins for downloading. Extracting
    # the archive will probably will be a call to tar.
    cmd = 'curl -sL {download_url} | tar -xzO --overwrite hugo > {hugo_bin_file}'.format(
        hugo_bin_file=str(hugo_bin_path), download_url=download_url)
    logging.info("Calling %s to download hugo.", cmd)
    subprocess.run(cmd, shell=True, check=True, cwd=str(SRCTREE_TOP))
    hugo_bin_path.chmod(0o755)
    return True


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
    subprocess.run(args, check=True, cwd=str(SRCTREE_TOP))


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
    generate_selfdocs()

    hugo_localinstall_dir = SRCTREE_TOP / 'build' / 'docs-hugo'
    os.environ["PATH"] += os.pathsep + str(hugo_localinstall_dir)

    try:
        if not is_hugo_extended():
            logging.info(
                "Hugo extended (with SASS support) is required, but only non-extended version found. "
                "Installing local copy and re-trying.")
            install_hugo(hugo_localinstall_dir)

        invoke_hugo(args.preview)
    except FileNotFoundError:
        logging.info("Hugo not found. Installing local copy and re-trying.")
        install_hugo(hugo_localinstall_dir)
        invoke_hugo(args.preview)
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
