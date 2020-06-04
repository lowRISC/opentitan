#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import subprocess
import sys
from collections import OrderedDict
from io import StringIO
from pathlib import Path

import hjson
from mako import exceptions
from mako.template import Template

import tlgen
from reggen import gen_dv, gen_fpv, gen_rtl, validate
from topgen import (amend_clocks, get_hjsonobj_xbars, merge_top, search_ips,
                    validate_top)

# Common header for generated files
genhdr = '''// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
'''

SRCTREE_TOP = Path(__file__).parent.parent.resolve()


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
            out_rtl, out_pkg, out_core = tlgen.generate(
                xbar, "top_" + top["name"])
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
        tlgen.generate_tb(xbar, dv_path, "top_" + top["name"])


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


def generate_pinmux_and_padctrl(top, out_path):
    topname = top["name"]
    # MIO Pads
    n_mio_pads = top["pinmux"]["num_mio"]
    if n_mio_pads <= 0:
        # TODO: add support for no MIO case
        log.error("Topgen does currently not support generation of a top " +
                  "without a pinmux.")
        return

    if "padctrl" not in top:
        # TODO: add support for no MIO case
        log.error("Topgen does currently not support generation of a top " +
                  "without a padctrl instance.")
        return

    # Get number of wakeup detectors
    if "num_wkup_detect" in top["pinmux"]:
        num_wkup_detect = top["pinmux"]["num_wkup_detect"]
    else:
        num_wkup_detect = 1

    if num_wkup_detect <= 0:
        # TODO: add support for no wakeup counter case
        log.error("Topgen does currently not support generation of a top " +
                  "without DIOs.")
        return

    if "wkup_cnt_width" in top["pinmux"]:
        wkup_cnt_width = top["pinmux"]["wkup_cnt_width"]
    else:
        wkup_cnt_width = 8

    if wkup_cnt_width <= 1:
        log.error("Wakeup counter width must be greater equal 2.")
        return

    # Total inputs/outputs
    # Validation ensures that the width field is present.
    num_mio_inputs = sum([x["width"] for x in top["pinmux"]["inputs"]])
    num_mio_outputs = sum([x["width"] for x in top["pinmux"]["outputs"]])
    num_mio_inouts = sum([x["width"] for x in top["pinmux"]["inouts"]])

    num_dio_inputs = sum([
        x["width"] if x["type"] == "input" else 0 for x in top["pinmux"]["dio"]
    ])
    num_dio_outputs = sum([
        x["width"] if x["type"] == "output" else 0
        for x in top["pinmux"]["dio"]
    ])
    num_dio_inouts = sum([
        x["width"] if x["type"] == "inout" else 0 for x in top["pinmux"]["dio"]
    ])

    n_mio_periph_in = num_mio_inouts + num_mio_inputs
    n_mio_periph_out = num_mio_inouts + num_mio_outputs
    n_dio_periph_in = num_dio_inouts + num_dio_inputs
    n_dio_periph_out = num_dio_inouts + num_dio_outputs
    n_dio_pads = num_dio_inouts + num_dio_inputs + num_dio_outputs

    if n_dio_pads <= 0:
        # TODO: add support for no DIO case
        log.error("Topgen does currently not support generation of a top " +
                  "without DIOs.")
        return

    log.info("Generating pinmux with following info from hjson:")
    log.info("num_mio_inputs:  %d" % num_mio_inputs)
    log.info("num_mio_outputs: %d" % num_mio_outputs)
    log.info("num_mio_inouts:  %d" % num_mio_inouts)
    log.info("num_dio_inputs:  %d" % num_dio_inputs)
    log.info("num_dio_outputs: %d" % num_dio_outputs)
    log.info("num_dio_inouts:  %d" % num_dio_inouts)
    log.info("num_wkup_detect: %d" % num_wkup_detect)
    log.info("wkup_cnt_width:  %d" % wkup_cnt_width)
    log.info("This translates to:")
    log.info("n_mio_periph_in:  %d" % n_mio_periph_in)
    log.info("n_mio_periph_out: %d" % n_mio_periph_out)
    log.info("n_dio_periph_in:  %d" % n_dio_periph_in)
    log.info("n_dio_periph_out: %d" % n_dio_periph_out)
    log.info("n_dio_pads:       %d" % n_dio_pads)

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
            # TODO: pass in information about always-on peripherals
            # TODO: pass in information on which DIOs can be selected
            # as wakeup signals
            # TODO: pass in signal names such that we can introduce
            # named enums for select signals
            out = hjson_tpl.render(
                n_mio_periph_in=n_mio_periph_in,
                n_mio_periph_out=n_mio_periph_out,
                n_mio_pads=n_mio_pads,
                # each DIO has in, out and oe wires
                # some of these have to be tied off in the
                # top, depending on the type.
                n_dio_periph_in=n_dio_pads,
                n_dio_periph_out=n_dio_pads,
                n_dio_pads=n_dio_pads,
                n_wkup_detect=num_wkup_detect,
                wkup_cnt_width=wkup_cnt_width)
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

    # Target path
    #   rtl: padctrl_reg_pkg.sv & padctrl_reg_top.sv
    #   data: padctrl.hjson
    rtl_path = out_path / 'ip/padctrl/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    data_path = out_path / 'ip/padctrl/data/autogen'
    data_path.mkdir(parents=True, exist_ok=True)

    # Template path
    tpl_path = out_path / '../ip/padctrl/data/padctrl.hjson.tpl'

    # Generate register package and RTLs
    gencmd = ("// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson "
              "-o hw/top_{topname}/\n\n".format(topname=topname))

    hjson_gen_path = data_path / "padctrl.hjson"

    out = StringIO()
    with tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(n_mio_pads=n_mio_pads,
                                   n_dio_pads=n_dio_pads,
                                   attr_dw=8)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("PADCTRL HJSON: %s" % out)

    if out == "":
        log.error("Cannot generate padctrl HJSON")
        return

    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=validate.checking_dict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


def generate_clkmgr(top, cfg_path, out_path):

    # Target paths
    rtl_path = out_path / 'ip/clkmgr/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    data_path = out_path / 'ip/clkmgr/data/autogen'
    data_path.mkdir(parents=True, exist_ok=True)

    # Template paths
    hjson_tpl = cfg_path / '../ip/clkmgr/data/clkmgr.hjson.tpl'
    rtl_tpl = cfg_path / '../ip/clkmgr/data/clkmgr.sv.tpl'
    pkg_tpl = cfg_path / '../ip/clkmgr/data/clkmgr_pkg.sv.tpl'

    hjson_out = data_path / 'clkmgr.hjson'
    rtl_out = rtl_path / 'clkmgr.sv'
    pkg_out = rtl_path / 'clkmgr_pkg.sv'

    tpls = [hjson_tpl, rtl_tpl, pkg_tpl]
    outputs = [hjson_out, rtl_out, pkg_out]
    names = ['clkmgr.hjson', 'clkmgr.sv', 'clkmgr_pkg.sv']

    # clock classification
    grps = top['clocks']['groups']

    src_aon_attr = OrderedDict()
    ft_clks = OrderedDict()
    rg_clks = OrderedDict()
    sw_clks = OrderedDict()
    hint_clks = OrderedDict()

    # construct a dictionary of the aon attribute for easier lookup
    # ie, src_name_A: True, src_name_B: False
    for src in top['clocks']['srcs']:
        if src['aon'] == 'yes':
            src_aon_attr[src['name']] = True
        else:
            src_aon_attr[src['name']] = False

    rg_srcs = [src for (src, attr) in src_aon_attr.items() if not attr]

    # clocks fed through clkmgr but are not disturbed in any way
    # This maintains the clocking structure consistency
    ft_clks = {
        clk: src
        for grp in grps for (clk, src) in grp['clocks'].items()
        if src_aon_attr[src]
    }

    # root-gate clocks
    rg_clks = {
        clk: src
        for grp in grps for (clk, src) in grp['clocks'].items()
        if grp['name'] != 'powerup' and grp['sw_cg'] == 'no' and
        not src_aon_attr[src]
    }

    # direct sw control clocks
    sw_clks = {
        clk: src
        for grp in grps for (clk, src) in grp['clocks'].items()
        if grp['sw_cg'] == 'yes' and not src_aon_attr[src]
    }

    # sw hint clocks
    hint_clks = {
        clk: src
        for grp in grps for (clk, src) in grp['clocks'].items()
        if grp['sw_cg'] == 'hint' and not src_aon_attr[src]
    }

    out = StringIO()
    for idx, tpl in enumerate(tpls):
        with tpl.open(mode='r', encoding='UTF-8') as fin:
            tpl = Template(fin.read())
            try:
                out = tpl.render(cfg=top,
                                 rg_srcs=rg_srcs,
                                 ft_clks=ft_clks,
                                 rg_clks=rg_clks,
                                 sw_clks=sw_clks,
                                 hint_clks=hint_clks)
            except:  # noqa: E722
                log.error(exceptions.text_error_template().render())

        if out == "":
            log.error("Cannot generate {}".format(names[idx]))
            return

        with outputs[idx].open(mode='w', encoding='UTF-8') as fout:
            fout.write(genhdr + out)

    # Generate reg files
    with open(str(hjson_out), 'r') as out:
        hjson_obj = hjson.load(out,
                               use_decimal=True,
                               object_pairs_hook=OrderedDict)
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
    cfg_path = Path(args.topcfg).parents[1]

    if not args.no_gen_hjson or args.hjson_only:
        # load top configuration
        try:
            with open(args.topcfg, 'r') as ftop:
                topcfg = hjson.load(ftop,
                                    use_decimal=True,
                                    object_pairs_hook=OrderedDict)
        except ValueError:
            raise SystemExit(sys.exc_info()[1])

        # Create filtered list
        filter_list = [
            module['type'] for module in topcfg['module']
            if 'generated' in module and module['generated'] == 'true'
        ]
        log.info("Filtered list is {}".format(filter_list))

        topname = topcfg["name"]

        # Sweep the IP directory and gather the config files
        ip_dir = Path(__file__).parents[1] / 'hw/ip'
        ips = search_ips(ip_dir)

        # exclude filtered IPs (to use top_${topname} one) and
        ips = [x for x in ips if not x.parents[1].name in filter_list]

        # Hack alert
        # Generate clkmgr.hjson here so that it can be included below
        # Unlike other generated hjsons, clkmgr thankfully does not require
        # ip.hjson information.  All the information is embedded within
        # the top hjson file
        amend_clocks(topcfg)
        generate_clkmgr(topcfg, cfg_path, out_path)

        # It may require two passes to check if the module is needed.
        # TODO: first run of topgen will fail due to the absent of rv_plic.
        # It needs to run up to amend_interrupt in merge_top function
        # then creates rv_plic.hjson then run xbar generation.
        hjson_dir = Path(args.topcfg).parent

        for ip in filter_list:
            log.info("Appending {}".format(ip))
            ip_hjson = hjson_dir.parent / "ip/{}/data/autogen/{}.hjson".format(
                ip, ip)
            ips.append(ip_hjson)

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

    # Generate Pinmux
    generate_pinmux_and_padctrl(completecfg, out_path)

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    top_name = completecfg["name"]

    if not args.no_top or args.top_only:
        tpl_path = Path(args.tpl)

        def render_template(out_name_tpl, out_dir, **other_info):
            top_tplpath = tpl_path / ((out_name_tpl + '.tpl') % (top_name))
            template_contents = generate_top(completecfg, str(top_tplpath),
                                             **other_info)

            rendered_dir = out_path / out_dir
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / (out_name_tpl % (top_name))

            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)

            return rendered_path

        # SystemVerilog Top:
        # 'top_earlgrey.sv.tpl' -> 'rtl/autogen/top_earlgrey.sv'
        render_template('top_%s.sv', 'rtl/autogen')

        # 'top_earlgrey_pkg.sv.tpl' -> 'rtl/autogen/top_earlgrey_pkg.sv'
        render_template('top_%s_pkg.sv', 'rtl/autogen')

        # C Header + C File + Clang-format file
        # The C file needs some information from when the header is generated,
        # so we keep this in a dictionary here.
        c_gen_info = {}

        # 'clang-format' -> 'sw/autogen/.clang-format'
        cformat_tplpath = tpl_path / 'clang-format'
        cformat_dir = out_path / 'sw/autogen'
        cformat_dir.mkdir(parents=True, exist_ok=True)
        cformat_path = cformat_dir / '.clang-format'
        cformat_path.write_text(cformat_tplpath.read_text())

        # 'top_earlgrey.h.tpl' -> 'sw/autogen/top_earlgrey.h'
        cheader_path = render_template('top_%s.h',
                                       'sw/autogen',
                                       c_gen_info=c_gen_info).resolve()

        # Save the relative header path into `c_gen_info`
        rel_header_path = cheader_path.relative_to(SRCTREE_TOP)
        c_gen_info["header_path"] = str(rel_header_path)

        # 'top_earlgrey.c.tpl' -> 'sw/autogen/top_earlgrey.c'
        render_template('top_%s.c', 'sw/autogen', c_gen_info=c_gen_info)

        # 'top_earlgrey_memory.ld.tpl' -> 'sw/autogen/top_earlgrey_memory.ld'
        render_template('top_%s_memory.ld', 'sw/autogen')

        # Fix the C header guard, which will have the wrong name
        subprocess.run(["util/fix_include_guard.py",
                        str(cheader_path)],
                       universal_newlines=True,
                       stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL,
                       check=True,
                       cwd=str(SRCTREE_TOP))

        # generate chip level xbar TB
        tb_files = ["xbar_env_pkg__params.sv", "tb__xbar_connect.sv"]
        for fname in tb_files:
            tpl_fname = "%s.tpl" % (fname)
            xbar_chip_data_path = tpl_path / tpl_fname
            template_contents = generate_top(completecfg,
                                             str(xbar_chip_data_path))

            rendered_dir = tpl_path / '../dv/autogen'
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / fname

            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)


if __name__ == "__main__":
    main()
