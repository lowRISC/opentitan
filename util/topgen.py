#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import sys
import subprocess
from collections import OrderedDict
from io import StringIO
from pathlib import Path

import hjson
from mako import exceptions
from mako.template import Template

import tlgen
from reggen import gen_dv, gen_rtl, gen_fpv, validate
from topgen import get_hjsonobj_xbars, merge_top, search_ips, validate_top

# Filter from IP list but adding generated hjson
filter_list = ['rv_plic', 'pinmux', 'alert_handler']

# Common header for generated files
genhdr = '''// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
'''

SRCTREE_TOP = Path(__file__).parent.parent

def generate_top(top, tpl_filename, **kwargs):
    top_tpl = Template(filename=tpl_filename)

    try:
        return top_tpl.render(top=top, **kwargs)
    except:  # noqa: E722
        log.error(exceptions.text_error_template().render())
        return ""


def generate_xbars(top, out_path):
    topname = top["name"]
    gencmd = ("// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson "
              "-o hw/top_{topname}/\n\n".format(topname=topname))

    for obj in top["xbar"]:
        xbar_path = out_path / 'ip/xbar_{}/data/autogen'.format(obj["name"])
        xbar_path.mkdir(parents=True, exist_ok=True)
        xbar = tlgen.validate(obj)
        xbar.ip_path = 'hw/top_' + top["name"] + '/ip/{dut}'

        # Generate output of crossbar with complete fields
        xbar_hjson_path = xbar_path / "xbar_{}.gen.hjson".format(xbar.name)
        xbar_hjson_path.write_text(genhdr + gencmd +
                                   hjson.dumps(obj, for_json=True))

        if not tlgen.elaborate(xbar):
            log.error("Elaboration failed." + repr(xbar))

        try:
            out_rtl, out_pkg, out_core = tlgen.generate(xbar)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())

        rtl_path = out_path / 'ip/xbar_{}/rtl/autogen'.format(obj["name"])
        rtl_path.mkdir(parents=True, exist_ok=True)
        dv_path = out_path / 'ip/xbar_{}/dv/autogen'.format(obj["name"])
        dv_path.mkdir(parents=True, exist_ok=True)

        rtl_filename = "xbar_%s.sv" % (xbar.name)
        rtl_filepath = rtl_path / rtl_filename
        with rtl_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_rtl)

        pkg_filename = "tl_%s_pkg.sv" % (xbar.name)
        pkg_filepath = rtl_path / pkg_filename
        with pkg_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_pkg)

        core_filename = "xbar_%s.core" % (xbar.name)
        core_filepath = rtl_path / core_filename
        with core_filepath.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out_core)

        # generate testbench for xbar
        tlgen.generate_tb(xbar, dv_path)


def generate_alert_handler(top, out_path):
    # default values
    esc_cnt_dw = 32
    accu_cnt_dw = 16
    lfsr_seed = 2**31 - 1
    async_on = "'0"
    # leave this constant
    n_classes = 4

    topname = top["name"]

    # check if there are any params to be passed through reggen and placed into
    # the generated package
    ip_list_in_top = [x["name"].lower() for x in top["module"]]
    ah_idx = ip_list_in_top.index("alert_handler")
    if 'localparam' in top['module'][ah_idx]:
        if 'EscCntDw' in top['module'][ah_idx]['localparam']:
            esc_cnt_dw = int(top['module'][ah_idx]['localparam']['EscCntDw'])
        if 'AccuCntDw' in top['module'][ah_idx]['localparam']:
            accu_cnt_dw = int(top['module'][ah_idx]['localparam']['AccuCntDw'])
        if 'LfsrSeed' in top['module'][ah_idx]['localparam']:
            lfsr_seed = int(top['module'][ah_idx]['localparam']['LfsrSeed'], 0)

    if esc_cnt_dw < 1:
        log.error("EscCntDw must be larger than 0")
    if accu_cnt_dw < 1:
        log.error("AccuCntDw must be larger than 0")
    if (lfsr_seed & 0xFFFFFFFF) == 0 or lfsr_seed > 2**32:
        log.error("LFSR seed out of range or zero")

    # Count number of interrupts
    n_alerts = sum([x["width"] if "width" in x else 1 for x in top["alert"]])

    if n_alerts < 1:
        # set number of alerts to 1 such that the config is still valid
        # that input will be tied off
        n_alerts = 1
        log.warning("no alerts are defined in the system")
    else:
        async_on = ""
        for alert in top['alert']:
            async_on = str(alert['async']) + async_on
        async_on = ("%d'b" % n_alerts) + async_on

    log.info("alert handler parameterization:")
    log.info("NAlerts   = %d" % n_alerts)
    log.info("EscCntDw  = %d" % esc_cnt_dw)
    log.info("AccuCntDw = %d" % accu_cnt_dw)
    log.info("LfsrSeed  = %d" % lfsr_seed)
    log.info("AsyncOn   = %s" % async_on)

    # Define target path
    rtl_path = out_path / 'ip/alert_handler/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/alert_handler/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from alert_handler directory directly.
    tpl_path = out_path / '../ip/alert_handler/data'
    hjson_tpl_path = tpl_path / 'alert_handler.hjson.tpl'

    # Generate Register Package and RTLs
    out = StringIO()
    with hjson_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(n_alerts=n_alerts,
                                   esc_cnt_dw=esc_cnt_dw,
                                   accu_cnt_dw=accu_cnt_dw,
                                   lfsr_seed=lfsr_seed,
                                   async_on=async_on,
                                   n_classes=n_classes)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("alert_handler hjson: %s" % out)

    if out == "":
        log.error("Cannot generate alert_handler config file")
        return

    hjson_gen_path = doc_path / "alert_handler.hjson"
    gencmd = (
        "// util/topgen.py -t hw/top_{topname}/doc/top_{topname}.hjson --alert-handler-only "
        "-o hw/top_{topname}/\n\n".format(topname=topname))
    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    # Generate register RTLs (currently using shell execute)
    # TODO: More secure way to gneerate RTL
    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=validate.checking_dict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


def generate_plic(top, out_path):
    topname = top["name"]
    # Count number of interrupts
    # Interrupt source 0 is tied to 0 to conform RISC-V PLIC spec.
    # So, total number of interrupts are the number of entries in the list + 1
    src = sum([x["width"] if "width" in x else 1
               for x in top["interrupt"]]) + 1

    # Target and priority: Currently fixed
    target = int(top["num_cores"], 0) if "num_cores" in top else 1
    prio = 3

    # Define target path
    #   rtl: rv_plic.sv & rv_plic_reg_pkg.sv & rv_plic_reg_top.sv
    #   data: rv_plic.hjson
    rtl_path = out_path / 'ip/rv_plic/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    fpv_path = out_path / 'ip/rv_plic/fpv/autogen'
    fpv_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/rv_plic/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)
    hjson_path = out_path / 'ip/rv_plic/data/autogen'
    hjson_path.mkdir(parents=True, exist_ok=True)

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from rv_plic directory directly.
    # Next, if the ip top gen tool is placed in util/ we can import the library.
    tpl_path = out_path / '../ip/rv_plic/data'
    hjson_tpl_path = tpl_path / 'rv_plic.hjson.tpl'
    rtl_tpl_path = tpl_path / 'rv_plic.sv.tpl'
    fpv_tpl_names = [
        'rv_plic_bind_fpv.sv', 'rv_plic_fpv.sv', 'rv_plic_fpv.core'
    ]

    # Generate Register Package and RTLs
    out = StringIO()
    with hjson_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(src=src, target=target, prio=prio)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("RV_PLIC hjson: %s" % out)

    if out == "":
        log.error("Cannot generate interrupt controller config file")
        return

    hjson_gen_path = hjson_path / "rv_plic.hjson"
    gencmd = (
        "// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson --plic-only "
        "-o hw/top_{topname}/\n\n".format(topname=topname))
    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    # Generate register RTLs (currently using shell execute)
    # TODO: More secure way to gneerate RTL
    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=OrderedDict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))
    gen_fpv.gen_fpv(hjson_obj, str(fpv_path))

    # Generate RV_PLIC Top Module
    with rtl_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        rtl_tpl = Template(fin.read())
        try:
            out = rtl_tpl.render(src=src, target=target, prio=prio)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("RV_PLIC RTL: %s" % out)

    if out == "":
        log.error("Cannot generate interrupt controller RTL")
        return

    rtl_gen_path = rtl_path / "rv_plic.sv"
    with rtl_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    # Generate RV_PLIC FPV testbench
    for file_name in fpv_tpl_names:
        tpl_name = file_name + ".tpl"
        path = tpl_path / tpl_name
        with path.open(mode='r', encoding='UTF-8') as fin:
            fpv_tpl = Template(fin.read())
            try:
                out = fpv_tpl.render(src=src, target=target, prio=prio)
            except:  # noqa : E722
                log.error(exceptions.text_error_template().render())
            log.info("RV_PLIC FPV: %s" % out)
        if out == "":
            log.error("Cannot generate rv_plic FPV testbench")
            return

        fpv_gen_path = fpv_path / file_name
        with fpv_gen_path.open(mode='w', encoding='UTF-8') as fout:
            fout.write(out)


def generate_pinmux(top, out_path):
    topname = top["name"]
    # MIO Pads
    num_mio = top["pinmux"]["num_mio"]
    if num_mio <= 0:
        log.warning(
            "No PINMUX is generated. The top %s has no multiplexed IO ports." %
            top["name"])
        return

    # Total inputs/outputs
    num_inputs = sum(
        [x["width"] if "width" in x else 1 for x in top["pinmux"]["inputs"]])
    num_outputs = sum(
        [x["width"] if "width" in x else 1 for x in top["pinmux"]["outputs"]])
    num_inouts = sum(
        [x["width"] if "width" in x else 1 for x in top["pinmux"]["inouts"]])

    n_periph_in = num_inouts + num_inputs
    n_periph_out = num_inouts + num_outputs

    # Target path
    #   rtl: pinmux_reg_pkg.sv & pinmux_reg_top.sv
    #   data: pinmux.hjson
    rtl_path = out_path / 'ip/pinmux/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    data_path = out_path / 'ip/pinmux/data/autogen'
    data_path.mkdir(parents=True, exist_ok=True)

    # Template path
    tpl_path = out_path / '../ip/pinmux/data/pinmux.hjson.tpl'

    # Generate register package and RTLs
    gencmd = ("// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson "
              "-o hw/top_{topname}/\n\n".format(topname=topname))

    hjson_gen_path = data_path / "pinmux.hjson"

    out = StringIO()
    with tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(n_periph_in=n_periph_in,
                                   n_periph_out=n_periph_out,
                                   n_mio_pads=num_mio)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("PINMUX HJSON: %s" % out)

    if out == "":
        log.error("Cannot generate pinmux HJSON")
        return

    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=validate.checking_dict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


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
            if "swaccess" in item.keys():
                mem.dvrights = item["swaccess"]
            else:
                mem.dvrights = "RW"
            mem.n_bits = top_block.width
            top_block.wins.append(mem)

    # get sub-block base addresses from top cfg
    for block in top_block.blocks:
        for module in top["module"]:
            if block.name == module["name"]:
                block.base_addr = module["base_addr"]
                break

    top_block.blocks.sort(key=lambda block: block.base_addr)
    top_block.wins.sort(key=lambda win: win.base_addr)

    # generate the top ral model with template
    gen_dv.gen_ral(top_block, str(out_path))


def main():
    parser = argparse.ArgumentParser(prog="topgen")
    parser.add_argument('--topcfg',
                        '-t',
                        required=True,
                        help="`top_{name}.hjson` file.")
    parser.add_argument(
        '--tpl',
        '-c',
        help=
        "The directory having top_{name}_core.sv.tpl and top_{name}.tpl.sv.")
    parser.add_argument(
        '--outdir',
        '-o',
        help='''Target TOP directory.
             Module is created under rtl/. (default: dir(topcfg)/..)
             ''')  # yapf: disable
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
        help="If defined, the tool generates top RTL only")  # yapf:disable
    parser.add_argument(
        '--xbar-only',
        action='store_true',
        help="If defined, the tool generates crossbar RTLs only")
    parser.add_argument(
        '--plic-only',
        action='store_true',
        help="If defined, the tool generates RV_PLIC RTL and Hjson only")
    parser.add_argument(
        '--alert-handler-only',
        action='store_true',
        help="If defined, the tool generates alert handler hjson only")
    parser.add_argument(
        '--hjson-only',
        action='store_true',
        help="If defined, the tool generates complete Hjson only")
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
                               args.plic_only or args.alert_handler_only):
        log.error(
            "'no' series options cannot be used with 'only' series options")
        raise SystemExit(sys.exc_info()[1])

    if not (args.hjson_only or args.plic_only or args.alert_handler_only or
            args.tpl):
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
                topcfg = hjson.load(ftop,
                                    use_decimal=True,
                                    object_pairs_hook=OrderedDict)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

        topname = topcfg["name"]

        # Sweep the IP directory and gather the config files
        ip_dir = Path(__file__).parents[1] / 'hw/ip'
        ips = search_ips(ip_dir)

        # exclude rv_plic (to use top_${topname} one) and
        ips = [x for x in ips if not x.parents[1].name in filter_list]

        # It may require two passes to check if the module is needed.
        # TODO: first run of topgen will fail due to the absent of rv_plic.
        # It needs to run up to amend_interrupt in merge_top function
        # then creates rv_plic.hjson then run xbar generation.
        hjson_dir = Path(args.topcfg).parent
        rv_plic_hjson = hjson_dir.parent / 'ip/rv_plic/data/autogen/rv_plic.hjson'
        ips.append(rv_plic_hjson)

        pinmux_hjson = hjson_dir.parent / 'ip/pinmux/data/autogen/pinmux.hjson'
        ips.append(pinmux_hjson)

        alert_handler_hjson = hjson_dir.parent / 'ip/alert_handler/data/autogen/alert_handler.hjson'
        ips.append(alert_handler_hjson)

        # load Hjson and pass validate from reggen
        try:
            ip_objs = []
            for x in ips:
                # Skip if it is not in the module list
                if x.stem not in [ip["type"] for ip in topcfg["module"]]:
                    log.info(
                        "Skip module %s as it isn't in the top module list" %
                        x.stem)
                    continue

                obj = hjson.load(x.open('r'),
                                 use_decimal=True,
                                 object_pairs_hook=OrderedDict)
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

        topcfg, error = validate_top(topcfg, ip_objs, xbar_objs)
        if error != 0:
            raise SystemExit("Error occured while validating top.hjson")

        completecfg = merge_top(topcfg, ip_objs, xbar_objs)

        genhjson_path = hjson_dir / ("autogen/top_%s.gen.hjson" %
                                     completecfg["name"])
        gencmd = (
            "// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson --hjson-only "
            "-o hw/top_{topname}/\n".format(topname=topname))

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
                completecfg = hjson.load(ftop,
                                         use_decimal=True,
                                         object_pairs_hook=OrderedDict)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

    # Generate PLIC
    if not args.no_plic and \
       not args.alert_handler_only and \
       not args.xbar_only:
        generate_plic(completecfg, out_path)
        if args.plic_only:
            sys.exit()

    # Generate Alert Handler
    if not args.xbar_only:
        generate_alert_handler(completecfg, out_path)
        if args.alert_handler_only:
            sys.exit()

    generate_pinmux(completecfg, out_path)

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    top_name = completecfg["name"]

    if not args.no_top or args.top_only:
        tpl_path = Path(args.tpl)

        def render_template(out_name_tpl, out_dir, **other_info):
            top_tplpath = tpl_path / ((out_name_tpl + '.tpl') % (top_name))
            template_contents = generate_top(completecfg, str(top_tplpath), **other_info)

            rendered_dir = out_path / out_dir
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / (out_name_tpl % (top_name))

            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)

            return rendered_path

        # SystemVerilog Top:
        # 'top_earlgrey.sv.tpl' -> 'rtl/autogen/top_earlgrey.sv'
        render_template('top_%s.sv', 'rtl/autogen')

        # C Header + C File
        # The C file needs some information from when the header is generated,
        # so we keep this in a dictionary here.
        c_gen_info = {}

        # 'top_earlgrey.h.tpl' -> 'sw/autogen/top_earlgrey.h'
        cheader_path = render_template('top_%s.h', 'sw/autogen', c_gen_info=c_gen_info)

        # Save the relative header path into `c_gen_info`
        rel_header_path = cheader_path.relative_to(SRCTREE_TOP)
        c_gen_info["header_path"] = str(rel_header_path)

        # 'top_earlgrey.c.tpl' -> 'sw/autogen/top_earlgrey.c'
        cimpl_path = render_template('top_%s.c', 'sw/autogen', c_gen_info=c_gen_info)

        # Format C header and implementation after creation
        subprocess.run(["clang-format", "-i", str(cheader_path), str(cimpl_path)],
                        check=True,
                        cwd=str(SRCTREE_TOP))
        # Fix the C header guard, which will have the wrong name
        subprocess.run(["util/fix_include_guard.py", str(cheader_path)],
                        universal_newlines=True,
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        check=True,
                        cwd=str(SRCTREE_TOP))


if __name__ == "__main__":
    main()
