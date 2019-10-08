#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import sys
from io import StringIO
from pathlib import Path

import hjson
from mako.template import Template

import tlgen
from reggen import gen_rtl, gen_dv, validate
from topgen import get_hjsonobj_xbars, merge_top, search_ips, validate_top, validate_reset

# Filter from IP list but adding generated hjson
filter_list = ['rv_plic', 'alert_h']

# Common header for generated files
genhdr = '''// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
'''


def generate_rtl(top, tpl_filename):
    top_rtl_tpl = Template(filename=tpl_filename)

    out_rtl = top_rtl_tpl.render(top=top)
    return out_rtl


def generate_xbars(top, out_path):
    for obj in top["xbar"]:
        xbar = tlgen.validate(obj)

        if not tlgen.elaborate(xbar):
            log.error("Elaboration failed." + repr(xbar))

        # Add clocks/resets to the top configuration
        obj["clocks"] = xbar.clocks
        out_rtl, out_pkg, out_bind = tlgen.generate(xbar)

        rtl_path = out_path / 'rtl'
        rtl_path.mkdir(parents=True, exist_ok=True)
        dv_path = out_path / 'dv'
        dv_path.mkdir(parents=True, exist_ok=True)

        rtl_filename = "xbar_%s.sv" % (xbar.name)
        rtl_filepath = rtl_path / rtl_filename
        with rtl_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_rtl)

        pkg_filename = "tl_%s_pkg.sv" % (xbar.name)
        pkg_filepath = rtl_path / pkg_filename
        with pkg_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_pkg)

        bind_filename = "xbar_%s_bind.sv" % (xbar.name)
        bind_filepath = dv_path / bind_filename
        with bind_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_bind)


def generate_plic(top, out_path):
    # Count number of interrupts
    src = sum([x["width"] if "width" in x else 1 for x in top["interrupt"]])

    # Target and priority: Currently fixed
    target = int(top["num_cores"], 0) if "num_cores" in top else 1
    prio = 3

    # Define target path
    #   rtl: rv_plic.sv & rv_plic_reg_pkg.sv & rv_plic_reg_top.sv
    #   doc: rv_plic.hjson
    rtl_path = out_path / 'rtl'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'doc'
    doc_path.mkdir(parents=True, exist_ok=True)

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from rv_plic directory directly.
    # Next, if the ip top gen tool is placed in util/ we can import the library.
    tpl_path = out_path / '../ip/rv_plic/doc'
    hjson_tpl_path = tpl_path / 'rv_plic.tpl.hjson'
    rtl_tpl_path = tpl_path / 'rv_plic.tpl.sv'

    # Generate Register Package and RTLs
    out = StringIO()
    with hjson_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        out = hjson_tpl.render(src=src, target=target, prio=prio)
        log.info("RV_PLIC hjson: %s" % out)

    if out == "":
        log.error("Cannot generate interrupt controller config file")
        return

    hjson_gen_path = doc_path / "rv_plic.hjson"
    gencmd = (
        "// util/topgen.py -t hw/top_earlgrey/doc/top_earlgrey.hjson --plic-only "
        "-o hw/top_earlgrey/\n\n")
    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    # Generate register RTLs (currently using shell execute)
    # TODO: More secure way to gneerate RTL
    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=validate.checking_dict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))

    # Generate RV_PLIC Top Module
    with rtl_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        rtl_tpl = Template(fin.read())
        out = rtl_tpl.render(src=src, target=target, prio=prio)
        log.info("RV_PLIC RTL: %s" % out)

    if out == "":
        log.error("Cannot generate interrupt controller RTL")
        return

    rtl_gen_path = rtl_path / "rv_plic.sv"
    with rtl_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)


def generate_top_ral(top, ip_objs, out_path):
    # construct top ral block
    top_block = gen_rtl.Block()
    top_block.name = "chip"
    top_block.base_addr = 0
    top_block.width = int(top["datawidth"])

    # add blocks
    for ip_obj in ip_objs:
        top_block.blocks.append(gen_rtl.json_to_reg(ip_obj))

    # add memories
    if "memory" in top.keys():
        for item in list(top["memory"]):
            mem = gen_rtl.Window()
            mem.name = item["name"]
            mem.base_addr = int(item["base_addr"], 0)
            mem.limit_addr = int(item["base_addr"], 0) + int(item["size"], 0)
            # TODO: need to add mem access info for memories in topcfg
            mem.dvrights = "RW"
            mem.n_bits = top_block.width
            top_block.wins.append(mem)

    # get sub-block base addresses from top cfg
    for block in top_block.blocks:
        for module in top["module"]:
            if block.name == module["name"]:
                block.base_addr = module["base_addr"]
                break
    # generate the top ral model with template
    gen_dv.gen_ral(top_block, str(out_path))


def main():
    parser = argparse.ArgumentParser(prog="topgen")
    parser.add_argument('--topcfg',
                        '-t',
                        required=True,
                        help="`top_{name}.hjson` file.")
    parser.add_argument('--tpl', '-c', help="`top_{name}.tpl.sv` file.")
    parser.add_argument(
        '--outdir',
        '-o',
        help='''Target TOP directory.
             Module is created under rtl/. (default: dir(topcfg)/..)
             ''') # yapf: disable
    parser.add_argument('--verbose', '-v', action='store_true', help="Verbose")

    # Generator options: 'no' series. cannot combined with 'only' series
    parser.add_argument(
        '--no-top',
        action='store_true',
        help="If defined, topgen doesn't generate top_{name} RTLs.")
    parser.add_argument(
        '--no-xbar',
        action='store_true',
        help="If defined, topgen doesn't generate crossbar RTLs.")
    parser.add_argument(
        '--no-plic',
        action='store_true',
        help="If defined, topgen doesn't generate the interrup controller RTLs."
    )
    parser.add_argument(
        '--no-gen-hjson',
        action='store_true',
        help='''If defined, the tool assumes topcfg as a generated hjson.
             So it bypasses the validation step and doesn't read ip and
             xbar configurations
             ''')

    # Generator options: 'only' series. cannot combined with 'no' series
    parser.add_argument(
        '--top-only',
        action='store_true',
        help="If defined, the tool generates top RTL only") # yapf:disable
    parser.add_argument(
        '--xbar-only',
        action='store_true',
        help="If defined, the tool generates crossbar RTLs only")
    parser.add_argument(
        '--plic-only',
        action='store_true',
        help="If defined, the tool generates RV_PLIC RTL and hjson only")
    parser.add_argument(
        '--hjson-only',
        action='store_true',
        help="If defined, the tool generates complete hjson only")
    # Generator options: generate dv ral model
    parser.add_argument(
        '--top_ral',
        '-r',
        default=False,
        action='store_true',
        help="If set, the tool generates top level RAL model for DV")

    args = parser.parse_args()

    # check combinations
    if args.top_ral:
        args.hjson_only = True
        args.no_top = True

    if args.hjson_only:
        args.no_gen_hjson = False

    if (args.no_top or args.no_xbar or
            args.no_plic) and (args.top_only or args.xbar_only or
                               args.plic_only):
        log.error(
            "'no' series options cannot be used with 'only' series options")
        raise SystemExit(sys.exc_info()[1])

    if not args.hjson_only and not args.tpl:
        log.error(
            "Template file can be omitted only if '--hjson-only' is true")
        raise SystemExit(sys.exc_info()[1])

    if args.verbose:
        log.basicConfig(format="%(levelname)s: %(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(levelname)s: %(message)s")

    if not args.outdir:
        outdir = Path(args.topcfg).parent / ".."
        log.info("TOP directory not given. Use %s", (outdir))
    elif not Path(args.outdir).is_dir():
        log.error("'--outdir' should point to writable directory")
        raise SystemExit(sys.exc_info()[1])
    else:
        outdir = Path(args.outdir)

    out_path = Path(outdir)

    if not args.no_gen_hjson or args.hjson_only:
        # load top configuration
        try:
            with open(args.topcfg, 'r') as ftop:
                topcfg = hjson.load(ftop, use_decimal=True)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

        # Sweep the IP directory and gather the config files
        ip_dir = Path(__file__).parents[1] / 'hw/ip'
        ips = search_ips(ip_dir)

        # exclude rv_plic (to use top_earlgrey one) and
        ips = [x for x in ips if not x.parents[1].name in filter_list]

        # It may require two passes to check if the module is needed.
        # TODO: first run of topgen will fail due to the absent of rv_plic.
        # It needs to run up to amend_interrupt in merge_top function
        # then creates rv_plic.hjson then run xbar generation.
        hjson_dir = Path(args.topcfg).parent
        ips.append(hjson_dir / 'rv_plic.hjson')

        # load hjson and pass validate from reggen
        try:
            ip_objs = []
            for x in ips:
                # Skip if it is not in the module list
                if not x.stem in [ip["type"] for ip in topcfg["module"]]:
                    log.info(
                        "Skip module %s as it isn't in the top module list" %
                        x.stem)
                    continue

                obj = hjson.load(x.open('r'),
                                 use_decimal=True,
                                 object_pairs_hook=validate.checking_dict)
                if validate.validate(obj) != 0:
                    log.info("Parsing IP %s configuration failed. Skip" % x)
                    continue
                ip_objs.append(obj)

        except ValueError:
            raise SystemExit(sys.exc_info()[1])

        # Read the crossbars under the top directory
        xbar_objs = get_hjsonobj_xbars(hjson_dir)

        log.info("Detected crossbars: %s" %
                 (", ".join([x["name"] for x in xbar_objs])))

        # TODO: Add validate
        topcfg = validate_top(topcfg)

        # TODO: Add conversion logic from top to top.complete.hjson
        completecfg = merge_top(topcfg, ip_objs, xbar_objs)

        # validate resets
        validate_reset(completecfg)

        genhjson_path = hjson_dir / ("top_%s.gen.hjson" % completecfg["name"])
        gencmd = (
            "// util/topgen.py -t hw/top_earlgrey/doc/top_earlgrey.hjson --hjson-only "
            "-o hw/top_earlgrey/\n")

        if args.top_ral:
            generate_top_ral(completecfg, ip_objs, out_path)
        else:
            genhjson_path.write_text(genhdr + gencmd +
                                     hjson.dumps(completecfg, for_json=True))

    if args.hjson_only:
        log.info("hjson is generated. Exiting...")
        sys.exit()

    if args.no_gen_hjson:
        # load top.complete configuration
        try:
            with open(args.topcfg, 'r') as ftop:
                completecfg = hjson.load(ftop, use_decimal=True)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

    # Generate PLIC
    if not args.no_plic or args.plic_only:
        generate_plic(completecfg, out_path)

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    # TODO: Get name from hjson
    top_name = completecfg["name"]

    if not args.no_top or args.top_only:
        rtl_path = out_path / 'rtl'
        rtl_path.mkdir(parents=True, exist_ok=True)
        rtl_filepath = rtl_path / ("top_%s.sv" % (top_name))
        out_rtl = generate_rtl(completecfg, args.tpl)

        with rtl_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_rtl)


if __name__ == "__main__":
    main()
