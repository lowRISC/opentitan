#!/usr/bin/env python3
# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import random
import subprocess
import sys
from collections import OrderedDict
from copy import deepcopy
from io import StringIO
from pathlib import Path

import hjson
from mako import exceptions
from mako.template import Template

import tlgen
from reggen import gen_dv, gen_rtl, validate
from topgen import amend_clocks, get_hjsonobj_xbars
from topgen import intermodule as im
from topgen import merge_top, search_ips, validate_top
from topgen.c import TopGenC

# Common header for generated files
warnhdr = '''//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
'''
genhdr = '''// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
''' + warnhdr

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
            results = tlgen.generate(xbar, "top_" + top["name"])
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())

        ip_path = out_path / 'ip/xbar_{}'.format(obj["name"])

        for filename, filecontent in results:
            filepath = ip_path / filename
            filepath.parent.mkdir(parents=True, exist_ok=True)
            with filepath.open(mode='w', encoding='UTF-8') as fout:
                fout.write(filecontent)

        dv_path = out_path / 'ip/xbar_{}/dv/autogen'.format(obj["name"])
        dv_path.mkdir(parents=True, exist_ok=True)

        # generate testbench for xbar
        tlgen.generate_tb(xbar, dv_path, "top_" + top["name"])

        # Read back the comportable IP and amend to Xbar
        xbar_ipfile = ip_path / ("data/autogen/xbar_%s.hjson" % obj["name"])
        with xbar_ipfile.open() as fxbar:
            xbar_ipobj = hjson.load(fxbar,
                                    use_decimal=True,
                                    object_pairs_hook=OrderedDict)

            # Deepcopy of the inter_signal_list.
            # As of writing the code, it is not expected to write-back the
            # read xbar objects into files. Still, as `inter_signal_list` is
            # modified in the `elab_intermodule()` stage, it is better to keep
            # the original content.
            obj["inter_signal_list"] = deepcopy(
                xbar_ipobj["inter_signal_list"])


def generate_alert_handler(top, out_path):
    # default values
    esc_cnt_dw = 32
    accu_cnt_dw = 16
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

    if esc_cnt_dw < 1:
        log.error("EscCntDw must be larger than 0")
    if accu_cnt_dw < 1:
        log.error("AccuCntDw must be larger than 0")

    # Count number of alerts
    n_alerts = sum([x["width"] if "width" in x else 1 for x in top["alert"]])

    if n_alerts < 1:
        # set number of alerts to 1 such that the config is still valid
        # that input will be tied off
        n_alerts = 1
        log.warning("no alerts are defined in the system")
    else:
        async_on = ""
        for alert in top['alert']:
            for k in range(alert['width']):
                async_on = str(alert['async']) + async_on
        async_on = ("%d'b" % n_alerts) + async_on

    log.info("alert handler parameterization:")
    log.info("NAlerts   = %d" % n_alerts)
    log.info("EscCntDw  = %d" % esc_cnt_dw)
    log.info("AccuCntDw = %d" % accu_cnt_dw)
    log.info("AsyncOn   = %s" % async_on)

    # Define target path
    rtl_path = out_path / 'ip/alert_handler/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/alert_handler/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)
    dv_path = out_path / 'ip/alert_handler/dv'
    dv_path.mkdir(parents=True, exist_ok=True)

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from alert_handler directory directly.
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/alert_handler/data'
    hjson_tpl_path = tpl_path / 'alert_handler.hjson.tpl'
    dv_tpl_path = tpl_path / 'alert_handler_env_pkg__params.sv.tpl'

    # Generate Register Package and RTLs
    out = StringIO()
    with hjson_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(n_alerts=n_alerts,
                                   esc_cnt_dw=esc_cnt_dw,
                                   accu_cnt_dw=accu_cnt_dw,
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
        "// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson --alert-handler-only "
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

    # generate testbench for alert_handler
    with dv_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        dv_tpl = Template(fin.read())
        try:
            out = dv_tpl.render(n_alerts=n_alerts, async_on=async_on)
        except:  # noqa : E722
            log.error(exceptions.text_error_template().render())
        log.info("ALERT_HANDLER DV: %s" % out)
        if out == "":
            log.error("Cannot generate dv alert_handler parameter file")
            return

        dv_gen_path = dv_path / 'alert_handler_env_pkg__params.sv'
        with dv_gen_path.open(mode='w', encoding='UTF-8') as fout:
            fout.write(genhdr + gencmd + out)


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
    doc_path = out_path / 'ip/rv_plic/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)
    hjson_path = out_path / 'ip/rv_plic/data/autogen'
    hjson_path.mkdir(parents=True, exist_ok=True)

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from rv_plic directory directly.
    # Next, if the ip top gen tool is placed in util/ we can import the library.
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/rv_plic/data'
    hjson_tpl_path = tpl_path / 'rv_plic.hjson.tpl'
    rtl_tpl_path = tpl_path / 'rv_plic.sv.tpl'

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
    # TODO: More secure way to generate RTL
    hjson_obj = hjson.loads(out,
                            use_decimal=True,
                            object_pairs_hook=OrderedDict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))

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
    tpl_path = Path(
        __file__).resolve().parent / '../hw/ip/pinmux/data/pinmux.hjson.tpl'

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
    tpl_path = Path(
        __file__).resolve().parent / '../hw/ip/padctrl/data/padctrl.hjson.tpl'

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
                                   attr_dw=10)
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

    ft_clks = OrderedDict()
    rg_clks = OrderedDict()
    sw_clks = OrderedDict()
    src_aon_attr = OrderedDict()
    hint_clks = OrderedDict()

    # construct a dictionary of the aon attribute for easier lookup
    # ie, src_name_A: True, src_name_B: False
    for src in top['clocks']['srcs'] + top['clocks']['derived_srcs']:
        if src['aon'] == 'yes':
            src_aon_attr[src['name']] = True
        else:
            src_aon_attr[src['name']] = False

    rg_srcs = [src for (src, attr) in src_aon_attr.items() if not attr]

    # clocks fed through clkmgr but are not disturbed in any way
    # This maintains the clocking structure consistency
    # This includes two groups of clocks
    # Clocks fed from the always-on source
    # Clocks fed to the powerup group
    ft_clks = OrderedDict([(clk, src) for grp in grps
                           for (clk, src) in grp['clocks'].items()
                           if src_aon_attr[src] or grp['name'] == 'powerup'])

    # root-gate clocks
    rg_clks = OrderedDict([(clk, src) for grp in grps
                           for (clk, src) in grp['clocks'].items()
                           if grp['name'] != 'powerup' and
                           grp['sw_cg'] == 'no' and not src_aon_attr[src]])

    # direct sw control clocks
    sw_clks = OrderedDict([(clk, src) for grp in grps
                           for (clk, src) in grp['clocks'].items()
                           if grp['sw_cg'] == 'yes' and not src_aon_attr[src]])

    # sw hint clocks
    hints = OrderedDict([(clk, src) for grp in grps
                         for (clk, src) in grp['clocks'].items()
                         if grp['sw_cg'] == 'hint' and not src_aon_attr[src]])

    # hint clocks dict
    for clk, src in hints.items():
        # the clock is constructed as clk_{src_name}_{module_name}.
        # so to get the module name we split from the right and pick the last entry
        hint_clks[clk] = OrderedDict()
        hint_clks[clk]['name'] = (clk.rsplit('_', 1)[-1])
        hint_clks[clk]['src'] = src

    for idx, tpl in enumerate(tpls):
        out = ""
        with tpl.open(mode='r', encoding='UTF-8') as fin:
            tpl = Template(fin.read())
            try:
                out = tpl.render(cfg=top,
                                 div_srcs=top['clocks']['derived_srcs'],
                                 rg_srcs=rg_srcs,
                                 ft_clks=ft_clks,
                                 rg_clks=rg_clks,
                                 sw_clks=sw_clks,
                                 export_clks=top['exported_clks'],
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


# generate pwrmgr
def generate_pwrmgr(top, out_path):
    log.info("Generating pwrmgr")

    # Count number of wakeups
    n_wkups = len(top["wakeups"])
    log.info("Found {} wakeup signals".format(n_wkups))

    # Count number of reset requests
    n_rstreqs = len(top["reset_requests"])
    log.info("Found {} reset request signals".format(n_rstreqs))

    if n_wkups < 1:
        n_wkups = 1
        log.warning(
            "The design has no wakeup sources. Low power not supported")

    # Define target path
    rtl_path = out_path / 'ip/pwrmgr/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/pwrmgr/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)

    # So, read template files from ip directory.
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/pwrmgr/data'
    hjson_tpl_path = tpl_path / 'pwrmgr.hjson.tpl'

    # Render and write out hjson
    out = StringIO()
    with hjson_tpl_path.open(mode='r', encoding='UTF-8') as fin:
        hjson_tpl = Template(fin.read())
        try:
            out = hjson_tpl.render(NumWkups=n_wkups, NumRstReqs=n_rstreqs)

        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("pwrmgr hjson: %s" % out)

    if out == "":
        log.error("Cannot generate pwrmgr config file")
        return

    hjson_path = doc_path / "pwrmgr.hjson"
    with hjson_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + out)

    # Generate reg files
    with open(str(hjson_path), 'r') as out:
        hjson_obj = hjson.load(out,
                               use_decimal=True,
                               object_pairs_hook=OrderedDict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


# generate rstmgr
def generate_rstmgr(topcfg, out_path):
    log.info("Generating rstmgr")

    # Define target path
    rtl_path = out_path / 'ip/rstmgr/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/rstmgr/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/rstmgr/data'

    # Read template files from ip directory.
    tpls = []
    outputs = []
    names = ['rstmgr.hjson', 'rstmgr.sv', 'rstmgr_pkg.sv']

    for x in names:
        tpls.append(tpl_path / Path(x + ".tpl"))
        if "hjson" in x:
            outputs.append(doc_path / Path(x))
        else:
            outputs.append(rtl_path / Path(x))

    # Parameters needed for generation
    clks = []
    output_rsts = OrderedDict()
    sw_rsts = OrderedDict()
    leaf_rsts = OrderedDict()

    # unique clocks
    for rst in topcfg["resets"]["nodes"]:
        if rst['type'] != "ext" and rst['clk'] not in clks:
            clks.append(rst['clk'])

    # resets sent to reset struct
    output_rsts = [
        rst for rst in topcfg["resets"]["nodes"] if rst['type'] == "top"
    ]

    # sw controlled resets
    sw_rsts = [
        rst for rst in topcfg["resets"]["nodes"]
        if 'sw' in rst and rst['sw'] == 1
    ]

    # leaf resets
    leaf_rsts = [rst for rst in topcfg["resets"]["nodes"] if rst['gen']]

    log.info("output resets {}".format(output_rsts))
    log.info("software resets {}".format(sw_rsts))
    log.info("leaf resets {}".format(leaf_rsts))

    # Number of reset requests
    n_rstreqs = len(topcfg["reset_requests"])

    # Generate templated files
    for idx, t in enumerate(tpls):
        out = StringIO()
        with t.open(mode='r', encoding='UTF-8') as fin:
            tpl = Template(fin.read())
            try:
                out = tpl.render(clks=clks,
                                 power_domains=topcfg['power']['domains'],
                                 num_rstreqs=n_rstreqs,
                                 sw_rsts=sw_rsts,
                                 output_rsts=output_rsts,
                                 leaf_rsts=leaf_rsts,
                                 export_rsts=topcfg['exported_rsts'])

            except:  # noqa: E722
                log.error(exceptions.text_error_template().render())

        if out == "":
            log.error("Cannot generate {}".format(names[idx]))
            return

        with outputs[idx].open(mode='w', encoding='UTF-8') as fout:
            fout.write(genhdr + out)

    # Generate reg files
    hjson_path = outputs[0]
    with open(str(hjson_path), 'r') as out:
        hjson_obj = hjson.load(out,
                               use_decimal=True,
                               object_pairs_hook=OrderedDict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


# generate flash
def generate_flash(topcfg, out_path):
    log.info("Generating flash")

    # Define target path
    rtl_path = out_path / 'ip/flash_ctrl/rtl/autogen'
    rtl_path.mkdir(parents=True, exist_ok=True)
    doc_path = out_path / 'ip/flash_ctrl/data/autogen'
    doc_path.mkdir(parents=True, exist_ok=True)
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/flash_ctrl/data'

    # Read template files from ip directory.
    tpls = []
    outputs = []
    names = ['flash_ctrl.hjson', 'flash_ctrl.sv', 'flash_ctrl_pkg.sv']

    for x in names:
        tpls.append(tpl_path / Path(x + ".tpl"))
        if "hjson" in x:
            outputs.append(doc_path / Path(x))
        else:
            outputs.append(rtl_path / Path(x))

    # Parameters needed for generation
    flash_mems = [mem for mem in topcfg['memory'] if mem['type'] == 'eflash']
    if len(flash_mems) > 1:
        log.error("This design does not currently support multiple flashes")
        return

    cfg = flash_mems[0]

    # Generate templated files
    for idx, t in enumerate(tpls):
        out = StringIO()
        with t.open(mode='r', encoding='UTF-8') as fin:
            tpl = Template(fin.read())
            try:
                out = tpl.render(cfg=cfg)

            except:  # noqa: E722
                log.error(exceptions.text_error_template().render())

        if out == "":
            log.error("Cannot generate {}".format(names[idx]))
            return

        with outputs[idx].open(mode='w', encoding='UTF-8') as fout:
            fout.write(genhdr + out)

    # Generate reg files
    hjson_path = outputs[0]
    with open(str(hjson_path), 'r') as out:
        hjson_obj = hjson.load(out,
                               use_decimal=True,
                               object_pairs_hook=OrderedDict)
    validate.validate(hjson_obj)
    gen_rtl.gen_rtl(hjson_obj, str(rtl_path))


def generate_top_only(top_only_list, out_path, topname):
    log.info("Generating top only modules")

    for ip in top_only_list:
        hjson_path = Path(__file__).resolve(
        ).parent / "../hw/top_{}/ip/{}/data/{}.hjson".format(topname, ip, ip)
        genrtl_dir = out_path / "ip/{}/rtl".format(ip)
        genrtl_dir.mkdir(parents=True, exist_ok=True)
        log.info("Generating top modules {}, hjson: {}, output: {}".format(
            ip, hjson_path, genrtl_dir))

        # Generate reg files
        with open(str(hjson_path), 'r') as out:
            hjson_obj = hjson.load(out,
                                   use_decimal=True,
                                   object_pairs_hook=OrderedDict)
            validate.validate(hjson_obj)
            gen_rtl.gen_rtl(hjson_obj, str(genrtl_dir))


def generate_top_ral(top, ip_objs, dv_base_prefix, out_path):
    # construct top ral block
    top_block = gen_rtl.Block()
    top_block.name = "chip"
    top_block.base_addr = 0
    top_block.width = int(top["datawidth"])

    # add all the IPs into blocks
    for ip_obj in ip_objs:
        top_block.blocks.append(gen_rtl.json_to_reg(ip_obj))

    # add memories
    if "memory" in top.keys():
        for item in list(top["memory"]):
            mem = gen_rtl.Window()
            mem.name = item["name"]
            mem.base_addr = int(item["base_addr"], 0)
            mem.limit_addr = int(item["base_addr"], 0) + int(item["size"], 0)
            mem.byte_write = ('byte_write' in item and
                              item["byte_write"].lower() == "true")
            if "swaccess" in item.keys():
                mem.dvrights = item["swaccess"]
            else:
                mem.dvrights = "RW"
            mem.n_bits = top_block.width
            top_block.wins.append(mem)

    # get sub-block base addresses, instance names from top cfg
    for block in top_block.blocks:
        for module in top["module"]:
            if block.name == module["type"]:
                block.base_addr[module["name"]] = int(module["base_addr"], 0)

    # sort by the base_addr of 1st instance of the block
    top_block.blocks.sort(key=lambda block: next(iter(block.base_addr))[1])
    top_block.wins.sort(key=lambda win: win.base_addr)

    # generate the top ral model with template
    gen_dv.gen_ral(top_block, dv_base_prefix, str(out_path))


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
    # Generator options: generate dv ral model
    parser.add_argument(
        '--top_ral',
        '-r',
        default=False,
        action='store_true',
        help="If set, the tool generates top level RAL model for DV")
    parser.add_argument('--dv-base-prefix',
                        default='dv_base',
                        help='Prefix for the DV register classes from which '
                        'the register models are derived.')
    # Generator options for compile time random netlist constants
    parser.add_argument(
        '--rnd_cnst_seed',
        type=int,
        metavar='<seed>',
        help='Custom seed for RNG to compute netlist constants.')

    args = parser.parse_args()

    # check combinations
    if args.top_ral:
        args.no_top = True

    if (args.no_top or args.no_xbar or
            args.no_plic) and (args.top_only or args.xbar_only or
                               args.plic_only or args.alert_handler_only):
        log.error(
            "'no' series options cannot be used with 'only' series options")
        raise SystemExit(sys.exc_info()[1])

    if not (args.top_ral or args.plic_only or args.alert_handler_only or
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

    try:
        with open(args.topcfg, 'r') as ftop:
            topcfg = hjson.load(ftop,
                                use_decimal=True,
                                object_pairs_hook=OrderedDict)
    except ValueError:
        raise SystemExit(sys.exc_info()[1])

    # Create generated list
    # These modules are generated through topgen
    generated_list = [
        module['type'] for module in topcfg['module']
        if 'generated' in module and module['generated'] == 'true'
    ]
    log.info("Filtered list is {}".format(generated_list))

    # These modules are NOT generated but belong to a specific top
    # and therefore not part of "hw/ip"
    top_only_list = [
        module['type'] for module in topcfg['module']
        if 'top_only' in module and module['top_only'] == 'true'
    ]
    log.info("Filtered list is {}".format(top_only_list))

    topname = topcfg["name"]

    # Sweep the IP directory and gather the config files
    ip_dir = Path(__file__).parents[1] / 'hw/ip'
    ips = search_ips(ip_dir)

    # exclude filtered IPs (to use top_${topname} one) and
    exclude_list = generated_list + top_only_list
    ips = [x for x in ips if not x.parents[1].name in exclude_list]

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

    for ip in generated_list:
        log.info("Appending {}".format(ip))
        if ip == 'clkmgr':
            ip_hjson = Path(out_path) / "ip/{}/data/autogen/{}.hjson".format(
                ip, ip)
        else:
            ip_hjson = hjson_dir.parent / "ip/{}/data/autogen/{}.hjson".format(
                ip, ip)
        ips.append(ip_hjson)

    for ip in top_only_list:
        log.info("Appending {}".format(ip))
        ip_hjson = hjson_dir.parent / "ip/{}/data/{}.hjson".format(ip, ip)
        ips.append(ip_hjson)

    # load Hjson and pass validate from reggen
    try:
        ip_objs = []
        for x in ips:
            # Skip if it is not in the module list
            if x.stem not in [ip["type"] for ip in topcfg["module"]]:
                log.info("Skip module %s as it isn't in the top module list" %
                         x.stem)
                continue

            # The auto-generated hjson might not yet exist. It will be created
            # later, see generate_{ip_name}() calls below. For the initial
            # validation, use the template in hw/ip/{ip_name}/data .
            if x.stem in generated_list and not x.is_file():
                hjson_file = ip_dir / "{}/data/{}.hjson".format(x.stem, x.stem)
                log.info(
                    "Auto-generated hjson %s does not yet exist. " % str(x) +
                    "Falling back to template %s for initial validation." %
                    str(hjson_file))
            else:
                hjson_file = x

            obj = hjson.load(hjson_file.open('r'),
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

    # If specified, override the seed for random netlist constant computation.
    if args.rnd_cnst_seed:
        log.warning('Commandline override of rnd_cnst_seed with {}.'.format(
            args.rnd_cnst_seed))
        topcfg['rnd_cnst_seed'] = args.rnd_cnst_seed
    # Otherwise, we either take it from the top_{topname}.hjson if present, or
    # randomly generate a new seed if not.
    else:
        random.seed()
        new_seed = random.getrandbits(64)
        if topcfg.setdefault('rnd_cnst_seed', new_seed) == new_seed:
            log.warning(
                'No rnd_cnst_seed specified, setting to {}.'.format(new_seed))

    topcfg, error = validate_top(topcfg, ip_objs, xbar_objs)
    if error != 0:
        raise SystemExit("Error occured while validating top.hjson")

    completecfg = merge_top(topcfg, ip_objs, xbar_objs)

    if args.top_ral:
        generate_top_ral(completecfg, ip_objs, args.dv_base_prefix, out_path)
        sys.exit()

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

    # Generate Pwrmgr
    generate_pwrmgr(completecfg, out_path)

    # Generate rstmgr
    generate_rstmgr(completecfg, out_path)

    # Generate flash
    generate_flash(completecfg, out_path)

    # Generate top only modules
    # These modules are not templated, but are not in hw/ip
    generate_top_only(top_only_list, out_path, topname)

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    # All IPs are generated. Connect phase now
    # Find {memory, module} <-> {xbar} connections first.
    im.autoconnect(completecfg)

    # Generic Inter-module connection
    im.elab_intermodule(completecfg)

    top_name = completecfg["name"]

    # Generate top.gen.hjson right before rendering
    genhjson_dir = Path(out_path) / "data/autogen"
    genhjson_dir.mkdir(parents=True, exist_ok=True)
    genhjson_path = genhjson_dir / ("top_%s.gen.hjson" % completecfg["name"])

    # Header for HJSON
    gencmd = '''//
// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson \\
//                -o hw/top_{topname}/ \\
//                --hjson-only \\
//                --rnd_cnst_seed {seed}
'''.format(topname=topname, seed=completecfg['rnd_cnst_seed'])

    genhjson_path.write_text(genhdr + gencmd +
                             hjson.dumps(completecfg, for_json=True))

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

            return rendered_path.resolve()

        # Header for SV files
        gencmd = warnhdr + '''//
// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson \\
//                --tpl hw/top_{topname}/data/ \\
//                -o hw/top_{topname}/ \\
//                --rnd_cnst_seed {seed}
'''.format(topname=topname, seed=topcfg['rnd_cnst_seed'])

        # SystemVerilog Top:
        render_template('top_%s.sv', 'rtl/autogen', gencmd=gencmd)
        # 'top_{topname}.sv.tpl' -> 'rtl/autogen/top_{topname}.sv'

        # The C / SV file needs some complex information, so we initialize this
        # object to store it.
        c_helper = TopGenC(completecfg)

        # 'top_{topname}_pkg.sv.tpl' -> 'rtl/autogen/top_{topname}_pkg.sv'
        render_template('top_%s_pkg.sv',
                        'rtl/autogen',
                        helper=c_helper,
                        gencmd=gencmd)

        # compile-time random netlist constants
        render_template('top_%s_rnd_cnst_pkg.sv', 'rtl/autogen', gencmd=gencmd)

        # C Header + C File + Clang-format file

        # Since SW does not use FuseSoC and instead expects those files always
        # to be in hw/top_{topname}/sw/autogen, we currently create these files
        # twice:
        # - Once under out_path/sw/autogen
        # - Once under hw/top_{topname}/sw/autogen
        for path in [Path(out_path).resolve(),
                     (SRCTREE_TOP / 'hw/top_{}/'.format(topname)).resolve()]:

            # 'clang-format' -> 'sw/autogen/.clang-format'
            cformat_tplpath = tpl_path / 'clang-format'
            cformat_dir = path / 'sw/autogen'
            cformat_dir.mkdir(parents=True, exist_ok=True)
            cformat_path = cformat_dir / '.clang-format'
            cformat_path.write_text(cformat_tplpath.read_text())

            # 'top_{topname}.h.tpl' -> 'sw/autogen/top_{topname}.h'
            cheader_path = render_template('top_%s.h',
                                           cformat_dir,
                                           helper=c_helper)

            # Save the relative header path into `c_gen_info`
            rel_header_path = cheader_path.relative_to(path.parents[1])
            c_helper.header_path = str(rel_header_path)

            # 'top_{topname}.c.tpl' -> 'sw/autogen/top_{topname}.c'
            render_template('top_%s.c', cformat_dir, helper=c_helper)

            # 'top_{topname}_memory.ld.tpl' -> 'sw/autogen/top_{topname}_memory.ld'
            render_template('top_%s_memory.ld', cformat_dir)

            # 'top_{topname}_memory.h.tpl' -> 'sw/autogen/top_{topname}_memory.h'
            memory_cheader_path = render_template('top_%s_memory.h', cformat_dir)

            try:
                cheader_path.relative_to(SRCTREE_TOP)
            except ValueError:
                log.error("cheader_path %s is not within SRCTREE_TOP %s",
                          cheader_path, SRCTREE_TOP)
                log.error("Thus skipping util/fix_include_guard.py")
                continue

            # Fix the C header guards, which will have the wrong name
            subprocess.run(["util/fix_include_guard.py",
                            str(cheader_path),
                            str(memory_cheader_path)],
                           universal_newlines=True,
                           stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL,
                           check=True,
                           cwd=str(SRCTREE_TOP))  # yapf: disable

        # generate chip level xbar and alert_handler TB
        tb_files = [
            "xbar_env_pkg__params.sv", "tb__xbar_connect.sv",
            "tb__alert_handler_connect.sv"
        ]
        for fname in tb_files:
            tpl_fname = "%s.tpl" % (fname)
            xbar_chip_data_path = tpl_path / tpl_fname
            template_contents = generate_top(completecfg,
                                             str(xbar_chip_data_path))

            rendered_dir = Path(out_path) / 'dv/autogen'
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / fname

            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)

        # generate chip level alert_handler pkg
        tpl_fname = 'alert_handler_env_pkg__params.sv.tpl'
        alert_handler_chip_data_path = tpl_path / tpl_fname
        template_contents = generate_top(completecfg,
                                         str(alert_handler_chip_data_path))

        rendered_dir = Path(out_path) / 'dv/env/autogen'
        rendered_dir.mkdir(parents=True, exist_ok=True)
        rendered_path = rendered_dir / 'alert_handler_env_pkg__params.sv'

        with rendered_path.open(mode='w', encoding='UTF-8') as fout:
            fout.write(template_contents)


if __name__ == "__main__":
    main()
