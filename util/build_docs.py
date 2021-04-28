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
import logging
import os
import platform
import re
import subprocess
import sys
import textwrap
from pathlib import Path

import check_tool_requirements
import dashboard.gen_dashboard_entry as gen_dashboard_entry
import difgen.gen_dif_listing as gen_dif_listing
import reggen.gen_cfg_html as gen_cfg_html
import reggen.gen_html as gen_html
import reggen.gen_selfdoc as reggen_selfdoc
import dvsim.testplanner.testplan_utils as testplan_utils
import tlgen
from reggen.ip_block import IpBlock

USAGE = """
  build_docs [options]
"""

# Version of hugo extended to be used to build the docs
try:
    TOOL_REQUIREMENTS = check_tool_requirements.read_tool_requirements()
    HUGO_EXTENDED_VERSION = TOOL_REQUIREMENTS['hugo_extended'].min_version
except Exception as e:
    print("Unable to get required hugo version: %s" % str(e), file=sys.stderr)
    sys.exit(1)

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
        "hw/ip/aon_timer/data/aon_timer.hjson",
        "hw/top_earlgrey/ip/alert_handler/data/autogen/alert_handler.hjson",
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
        "hw/ip/nmi_gen/data/nmi_gen.hjson",
        "hw/ip/otbn/data/otbn.hjson",
        "hw/ip/otp_ctrl/data/otp_ctrl.hjson",
        "hw/ip/pattgen/data/pattgen.hjson",
        "hw/ip/pwm/data/pwm.hjson",
        "hw/ip/rom_ctrl/data/rom_ctrl.hjson",
        "hw/top_earlgrey/ip/pinmux/data/autogen/pinmux.hjson",
        "hw/top_earlgrey/ip/clkmgr/data/autogen/clkmgr.hjson",
        "hw/top_earlgrey/ip/pwrmgr/data/autogen/pwrmgr.hjson",
        "hw/top_earlgrey/ip/rstmgr/data/autogen/rstmgr.hjson",
        "hw/top_earlgrey/ip/rv_plic/data/autogen/rv_plic.hjson",
        "hw/ip/rv_timer/data/rv_timer.hjson",
        "hw/ip/spi_host/data/spi_host.hjson",
        "hw/ip/spi_device/data/spi_device.hjson",
        "hw/ip/sram_ctrl/data/sram_ctrl.hjson",
        "hw/ip/sysrst_ctrl/data/sysrst_ctrl.hjson",
        "hw/ip/uart/data/uart.hjson",
        "hw/ip/usbdev/data/usbdev.hjson",
        "hw/ip/usbuart/data/usbuart.hjson",
    ],

    # Pre-generate dashboard fragments from these directories.
    "dashboard_definitions": {
        "comportable": [
            "hw/ip",
        ],
    },

    # Pre-generate testplan fragments from these files.
    "testplan_definitions": [
        "hw/ip/aes/data/aes_testplan.hjson",
        "hw/ip/alert_handler/data/alert_handler_testplan.hjson",
        "hw/ip/aon_timer/data/aon_timer_testplan.hjson",
        "hw/ip/clkmgr/data/clkmgr_testplan.hjson",
        "hw/ip/entropy_src/data/entropy_src_testplan.hjson",
        "hw/ip/csrng/data/csrng_testplan.hjson",
        "hw/ip/adc_ctrl/data/adc_ctrl_testplan.hjson",
        "hw/ip/edn/data/edn_testplan.hjson",
        "hw/ip/flash_ctrl/data/flash_ctrl_testplan.hjson",
        "hw/ip/gpio/data/gpio_testplan.hjson",
        "hw/ip/hmac/data/hmac_testplan.hjson",
        "hw/ip/i2c/data/i2c_testplan.hjson",
        "hw/ip/keymgr/data/keymgr_testplan.hjson",
        "hw/ip/lc_ctrl/data/lc_ctrl_testplan.hjson",
        "hw/ip/otbn/data/otbn_testplan.hjson",
        "hw/ip/otp_ctrl/data/otp_ctrl_testplan.hjson",
        "hw/ip/pattgen/data/pattgen_testplan.hjson",
        "hw/ip/pwm/data/pwm_testplan.hjson",
        "hw/ip/pinmux/data/pinmux_fpv_testplan.hjson",
        "hw/ip/rv_plic/data/rv_plic_fpv_testplan.hjson",
        "hw/ip/rv_timer/data/rv_timer_testplan.hjson",
        "hw/ip/spi_host/data/spi_host_testplan.hjson",
        "hw/ip/spi_device/data/spi_device_testplan.hjson",
        "hw/ip/sram_ctrl/data/sram_ctrl_base_testplan.hjson",
        "hw/ip/uart/data/uart_testplan.hjson",
        "hw/ip/usbdev/data/usbdev_testplan.hjson",
        "hw/ip/tlul/data/tlul_testplan.hjson",
        "hw/top_earlgrey/data/chip_testplan.hjson",
        "hw/top_earlgrey/data/standalone_sw_testplan.hjson",
        "util/dvsim/testplanner/examples/foo_testplan.hjson",
    ],

    # Pre-generated utility selfdoc
    "selfdoc_tools": ["tlgen", "reggen"],

    # DIF Docs
    "difs-directory": "sw/device/lib/dif",

    # Output directory for documents
    "outdir":
    SRCTREE_TOP.joinpath('build', 'docs'),
    "outdir-generated":
    SRCTREE_TOP.joinpath('build', 'docs-generated'),
    "verbose":
    False,
}


def generate_dashboards():
    for dashboard_name, dirs in config["dashboard_definitions"].items():
        hjson_paths = []
        for d in dirs:
            hjson_paths += SRCTREE_TOP.joinpath(d).rglob('*.prj.hjson')

        hjson_paths.sort(key=lambda f: f.name)

        dashboard_path = config["outdir-generated"].joinpath(
            dashboard_name, 'dashboard')
        dashboard_path.parent.mkdir(exist_ok=True, parents=True)
        dashboard_html = open(str(dashboard_path), mode='w')
        for hjson_path in hjson_paths:
            gen_dashboard_entry.gen_dashboard_html(hjson_path, dashboard_html)
        dashboard_html.close()


def generate_hardware_blocks():
    for hardware in config["hardware_definitions"]:
        regs = IpBlock.from_path(str(SRCTREE_TOP.joinpath(hardware)), [])

        hw_path = config["outdir-generated"].joinpath(hardware)
        dst_path = hw_path.parent
        dst_path.mkdir(parents=True, exist_ok=True)

        regs_path = dst_path.joinpath(hw_path.name + '.registers')
        with open(regs_path, 'w') as regs_file:
            gen_html.gen_html(regs, regs_file)

        hwcfg_path = dst_path.joinpath(hw_path.name + '.hwcfg')
        with open(hwcfg_path, 'w') as hwcfg_file:
            gen_cfg_html.gen_cfg_html(regs, hwcfg_file)


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


def generate_pkg_reqs():
    """Generate an apt/yum command line invocation from
    apt/yum-requirements.txt

    This will be saved in outdir-generated/apt_cmd.txt and
    outdir-generated/yum_cmd.txt, respectively.
    """

    for pkgmgr in ["apt", "yum"]:
        # Read the apt/yum-requirements.txt
        requirements = []
        requirements_file = open(str(SRCTREE_TOP.joinpath(pkgmgr + "-requirements.txt")))
        for package_line in requirements_file.readlines():
            # Ignore everything after `#` on each line, and strip whitespace
            package = package_line.split('#', 1)[0].strip()
            if package:
                # only add non-empty lines to packages
                requirements.append(package)

        cmd = "$ sudo " + pkgmgr + " install " + " ".join(requirements)
        cmd_lines = textwrap.wrap(cmd,
                                  width=78,
                                  replace_whitespace=True,
                                  subsequent_indent='    ')
        # Newlines need to be escaped
        cmd = " \\\n".join(cmd_lines)

        # And then to write the generated string directly to the file.
        cmd_path = config["outdir-generated"].joinpath(pkgmgr + '_cmd.txt')
        cmd_path.parent.mkdir(parents=True, exist_ok=True)
        with open(str(cmd_path), mode='w') as fout:
            fout.write(cmd)


def generate_tool_versions():
    """Generate an tool version number requirement from tool_requirements.py

    The version number per tool will be saved in outdir-generated/version_$TOOL_NAME.txt
    """

    # And then write a version file for every tool.
    for tool, req in TOOL_REQUIREMENTS.items():
        version_path = config["outdir-generated"].joinpath('version_' + tool + '.txt')
        version_path.parent.mkdir(parents=True, exist_ok=True)
        with open(str(version_path), mode='w') as fout:
            fout.write(req.min_version)


def generate_dif_docs():
    """Generate doxygen documentation and DIF listings from DIF source comments.

    This invokes Doxygen, and a few other things. Be careful of changing any
    paths here, some correspond to paths in other configuration files.
    """

    logging.info("Generating Software API Documentation (Doxygen)...")

    doxygen_out_path = config["outdir-generated"].joinpath("sw")

    # The next two paths correspond to relative paths specified in the Doxyfile
    doxygen_xml_path = doxygen_out_path.joinpath("api-xml")

    # We need to prepare this path because doxygen won't `mkdir -p`
    doxygen_sw_path = doxygen_out_path.joinpath("public-api/sw/apis")
    doxygen_sw_path.mkdir(parents=True, exist_ok=True)

    # This is where warnings will be generated
    doxygen_warnings_path = doxygen_out_path.joinpath("doxygen_warnings.log")
    if doxygen_warnings_path.exists():
        doxygen_warnings_path.unlink()

    doxygen_args = [
        "doxygen",
        str(SRCTREE_TOP.joinpath("util/doxygen/Doxyfile")),
    ]

    doxygen_results = subprocess.run(  # noqa: F841
        doxygen_args, check=True,
        cwd=str(SRCTREE_TOP), stdout=subprocess.PIPE,
        env=dict(
            os.environ,
            SRCTREE_TOP=str(SRCTREE_TOP),
            DOXYGEN_OUT=str(doxygen_out_path),
        ))

    logging.info("Generated Software API Documentation (Doxygen)")

    if doxygen_warnings_path.exists():
        logging.warning("Doxygen Generated Warnings "
                        "(saved in {})".format(str(doxygen_warnings_path)))

    combined_xml = gen_dif_listing.get_combined_xml(doxygen_xml_path)

    dif_paths = []
    dif_paths.extend(sorted(SRCTREE_TOP.joinpath(config["difs-directory"]).glob("dif_*.h")))

    dif_listings_root_path = config["outdir-generated"].joinpath("sw/difs_listings")
    difrefs_root_path = config["outdir-generated"].joinpath("sw/difref")

    for dif_header_path in dif_paths:
        dif_header = str(dif_header_path.relative_to(SRCTREE_TOP))

        dif_listings_filename = dif_listings_root_path.joinpath(dif_header + ".html")
        dif_listings_filename.parent.mkdir(parents=True, exist_ok=True)

        with open(str(dif_listings_filename), mode='w') as dif_listings_html:
            gen_dif_listing.gen_listing_html(combined_xml, dif_header,
                                             dif_listings_html)

        difref_functions = gen_dif_listing.get_difref_info(combined_xml, dif_header)
        for function in difref_functions:
            difref_filename = difrefs_root_path.joinpath(function["name"] + '.html')
            difref_filename.parent.mkdir(parents=True, exist_ok=True)

            with open(str(difref_filename), mode='w') as difref_html:
                gen_dif_listing.gen_difref_html(function, difref_html)

        logging.info("Generated DIF Listing for {}".format(dif_header))


def generate_otbn_isa():
    '''Generate the OTBN ISA documentation fragment

    The result is in Markdown format and is written to
    outdir-generated/otbn-isa.md

    '''
    otbn_dir = SRCTREE_TOP / 'hw/ip/otbn'
    script = otbn_dir / 'util/yaml_to_doc.py'
    yaml_file = otbn_dir / 'data/insns.yml'
    impl_file = otbn_dir / 'dv/otbnsim/sim/insn.py'

    out_dir = config['outdir-generated'].joinpath('otbn-isa')
    subprocess.run([str(script), str(yaml_file), str(impl_file), str(out_dir)],
                   check=True)


def hugo_match_version(hugo_bin_path, version):
    logging.info("Hugo binary path: %s", hugo_bin_path)
    args = [str(hugo_bin_path), "version"]
    process = subprocess.run(args,
                             universal_newlines=True,
                             stdout=subprocess.PIPE,
                             check=True,
                             cwd=str(SRCTREE_TOP))

    logging.info("Checking for correct Hugo version: %s", version)
    # Hugo version string example:
    # "Hugo Static Site Generator v0.59.0-1DD0C69C/extended linux/amd64 BuildDate: 2019-10-21T09:45:38Z"  # noqa: E501
    return bool(re.search("v" + version + ".*[/+]extended", process.stdout))


def install_hugo(install_dir):
    """Download and "install" hugo into |install_dir|

    install_dir is created if it doesn't exist yet.

    Limitations:
      Currently only 64-bit x86 Linux and macOS is supported."""

    # TODO: Support more configurations
    if platform.system() == 'Linux' and platform.machine() == 'x86_64':
        download_url = ('https://github.com/gohugoio/hugo/releases/download/v{version}'
                        '/hugo_extended_{version}_Linux-64bit.tar.gz').format(
                            version=HUGO_EXTENDED_VERSION)

    elif platform.system() == 'Darwin' and platform.machine() == 'x86_64':
        download_url = ('https://github.com/gohugoio/hugo/releases/download/v{version}'
                        '/hugo_extended_{version}_macOS-64bit.tar.gz').format(
                            version=HUGO_EXTENDED_VERSION)

    else:
        logging.fatal(
            "Auto-install of hugo only supported for 64-bit x86 Linux and "
            "macOS. Manually install hugo and re-run this script with --force-global.")
        return False

    install_dir.mkdir(exist_ok=True, parents=True)
    hugo_bin_path = install_dir / 'hugo'

    try:
        if hugo_match_version(hugo_bin_path, HUGO_EXTENDED_VERSION):
            return hugo_bin_path
    except PermissionError:
        # If there is an error checking the version just continue to download
        logging.info("Hugo version could not be verified. Continue to download.")
    except FileNotFoundError:
        pass

    # TODO: Investigate the use of Python builtins for downloading. Extracting
    # the archive will probably will be a call to tar.
    cmd = 'curl -sL {download_url} | tar -xzO hugo > {hugo_bin_file}'.format(
        hugo_bin_file=str(hugo_bin_path), download_url=download_url)
    logging.info("Calling %s to download hugo.", cmd)
    subprocess.run(cmd, shell=True, check=True, cwd=str(SRCTREE_TOP))
    hugo_bin_path.chmod(0o755)
    return hugo_bin_path


def invoke_hugo(preview, hugo_bin_path):
    site_docs = SRCTREE_TOP.joinpath('site', 'docs')
    config_file = str(site_docs.joinpath('config.toml'))
    layout_dir = str(site_docs.joinpath('layouts'))
    args = [
        str(hugo_bin_path),
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
        help="""Starts a local server with live reload (updates triggered upon
             changes in the documentation files). This feature is intended
             to preview the documentation locally.""")
    parser.add_argument(
        '--force-global',
        action='store_true',
        help="""Use a global installation of Hugo. This skips the version
            check and relies on Hugo to be available from the environment.""")
    parser.add_argument('--hugo', help="""TODO""")

    args = parser.parse_args()

    generate_hardware_blocks()
    generate_dashboards()
    generate_testplans()
    generate_selfdocs()
    generate_pkg_reqs()
    generate_tool_versions()
    generate_dif_docs()
    generate_otbn_isa()

    hugo_localinstall_dir = SRCTREE_TOP / 'build' / 'docs-hugo'
    os.environ["PATH"] += os.pathsep + str(hugo_localinstall_dir)

    hugo_bin_path = "hugo"
    if not args.force_global:
        try:
            hugo_bin_path = install_hugo(hugo_localinstall_dir)
        except KeyboardInterrupt:
            pass

    try:
        invoke_hugo(args.preview, hugo_bin_path)
    except subprocess.CalledProcessError:
        sys.exit("Error building site")
    except PermissionError:
        sys.exit("Error running Hugo")
    except KeyboardInterrupt:
        pass


if __name__ == "__main__":
    main()
