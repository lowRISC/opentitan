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
from typing import Dict, Optional, Tuple

import hjson
from mako import exceptions
from mako.template import Template

import tlgen
from reggen import access, gen_rtl, window
from reggen.inter_signal import InterSignal
from reggen.ip_block import IpBlock
from reggen.lib import check_list
from topgen import amend_clocks, get_hjsonobj_xbars
from topgen import intermodule as im
from topgen import lib as lib
from topgen import merge_top, search_ips, validate_top
from topgen.c import TopGenC
from topgen.gen_dv import gen_dv
from topgen.top import Top

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

TOPGEN_TEMPLATE_PATH = Path(__file__).parent / 'topgen/templates'


def generate_top(top, name_to_block, tpl_filename, **kwargs):
    top_tpl = Template(filename=tpl_filename)

    try:
        return top_tpl.render(top=top, name_to_block=name_to_block, **kwargs)
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

            r_inter_signal_list = check_list(xbar_ipobj.get('inter_signal_list', []),
                                             'inter_signal_list field')
            obj['inter_signal_list'] = [
                InterSignal.from_raw('entry {} of the inter_signal_list field'
                                     .format(idx + 1),
                                     entry)
                for idx, entry in enumerate(r_inter_signal_list)
            ]


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

    # Generating IP top module script is not generalized yet.
    # So, topgen reads template files from alert_handler directory directly.
    tpl_path = Path(__file__).resolve().parent / '../hw/ip/alert_handler/data'
    hjson_tpl_path = tpl_path / 'alert_handler.hjson.tpl'

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
    gen_rtl.gen_rtl(IpBlock.from_text(out, [], str(hjson_gen_path)),
                    str(rtl_path))


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
    gen_rtl.gen_rtl(IpBlock.from_text(out, [], str(hjson_gen_path)),
                    str(rtl_path))

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


def generate_pinmux(top, out_path):

    topname = top['name']
    pinmux = top['pinmux']

    # Generation without pinmux and pinout configuration is not supported.
    assert 'pinmux' in top
    assert 'pinout' in top

    # Get number of wakeup detectors
    if 'num_wkup_detect' in pinmux:
        num_wkup_detect = pinmux['num_wkup_detect']
    else:
        num_wkup_detect = 1

    if num_wkup_detect <= 0:
        # TODO: add support for no wakeup counter case
        log.error('Topgen does currently not support generation of a top ' +
                  'without DIOs.')
        return

    if 'wkup_cnt_width' in pinmux:
        wkup_cnt_width = pinmux['wkup_cnt_width']
    else:
        wkup_cnt_width = 8

    if wkup_cnt_width <= 1:
        log.error('Wakeup counter width must be greater equal 2.')
        return

    # MIO Pads
    n_mio_pads = pinmux['io_counts']['muxed']['pads']

    # Total inputs/outputs
    # Reuse the counts from the merge phase
    n_mio_periph_in = (pinmux['io_counts']['muxed']['inouts'] +
                       pinmux['io_counts']['muxed']['inputs'])
    n_mio_periph_out = (pinmux['io_counts']['muxed']['inouts'] +
                        pinmux['io_counts']['muxed']['outputs'])
    n_dio_periph_in = (pinmux['io_counts']['dedicated']['inouts'] +
                       pinmux['io_counts']['dedicated']['inputs'])
    n_dio_periph_out = (pinmux['io_counts']['dedicated']['inouts'] +
                        pinmux['io_counts']['dedicated']['outputs'])
    n_dio_pads = (pinmux['io_counts']['dedicated']['inouts'] +
                  pinmux['io_counts']['dedicated']['inputs'] +
                  pinmux['io_counts']['dedicated']['outputs'])

    # TODO: derive this value
    attr_dw = 13

    # Generation with zero MIO/DIO pads is currently not supported.
    assert (n_mio_pads > 0)
    assert (n_dio_pads > 0)

    log.info('Generating pinmux with following info from hjson:')
    log.info('attr_dw:         %d' % attr_dw)
    log.info('num_wkup_detect: %d' % num_wkup_detect)
    log.info('wkup_cnt_width:  %d' % wkup_cnt_width)
    log.info('n_mio_periph_in:  %d' % n_mio_periph_in)
    log.info('n_mio_periph_out: %d' % n_mio_periph_out)
    log.info('n_dio_periph_in:  %d' % n_dio_periph_in)
    log.info('n_dio_periph_out: %d' % n_dio_periph_out)
    log.info('n_dio_pads:       %d' % n_dio_pads)

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
                attr_dw=attr_dw,
                n_wkup_detect=num_wkup_detect,
                wkup_cnt_width=wkup_cnt_width
            )
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())
        log.info("PINMUX HJSON: %s" % out)

    if out == "":
        log.error("Cannot generate pinmux HJSON")
        return

    with hjson_gen_path.open(mode='w', encoding='UTF-8') as fout:
        fout.write(genhdr + gencmd + out)

    gen_rtl.gen_rtl(IpBlock.from_text(out, [], str(hjson_gen_path)),
                    str(rtl_path))


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

    # A dictionary of the aon attribute for easier lookup. src_aon_attr[C] is
    # True if clock C is always-on and False otherwise.
    src_aon_attr = {src['name']: (src['aon'] == 'yes')
                    for src in (top['clocks']['srcs'] +
                                top['clocks']['derived_srcs'])}

    # Classify the various clock signals. Here, we build the following
    # dictionaries, each mapping the derived clock name to its source.
    #
    # ft_clks:  Clocks fed through clkmgr but are not disturbed in any way.
    #           This maintains the clocking structure consistency.
    #           This includes two groups of clocks:
    #             - Clocks fed from the always-on source
    #             - Clocks fed to the powerup group
    #
    # rg_clks: Non-feedthrough clocks that have no software control. These
    #          clocks are root-gated and the root-gated clock is then exposed
    #          directly in clocks_o.
    #
    # sw_clks: Non-feedthrough clocks that have direct software control. These
    #          are root-gated, but (unlike rg_clks) then go through a second
    #          clock gate which is controlled by software.
    #
    # hints: Non-feedthrough clocks that have "hint" software control (with a
    #        feedback mechanism to allow blocks to avoid being suspended when
    #        they are not idle).
    ft_clks = {}
    rg_clks = {}
    sw_clks = {}
    hints = {}

    # We also build rg_srcs_set, which is the set of non-always-on clock sources
    # that are exposed without division. This doesn't include clock sources
    # that are only used to derive divided clocks (we might gate the divided
    # clocks, but don't bother gating the upstream source).
    rg_srcs_set = set()

    for grp in top['clocks']['groups']:
        if grp['name'] == 'powerup':
            # All clocks in the "powerup" group are considered feed-throughs.
            ft_clks.update(grp['clocks'])
            continue

        for clk, src in grp['clocks'].items():
            if src_aon_attr[src]:
                # Any always-on clock is a feedthrough
                ft_clks[clk] = src
                continue

            rg_srcs_set.add(src)

            if grp['sw_cg'] == 'no':
                # A non-feedthrough clock with no software control
                rg_clks[clk] = src
                continue

            if grp['sw_cg'] == 'yes':
                # A non-feedthrough clock with direct software control
                sw_clks[clk] = src
                continue

            # The only other valid value for the sw_cg field is "hint", which
            # means a non-feedthrough clock with "hint" software control.
            assert grp['sw_cg'] == 'hint'
            hints[clk] = src
            continue

    # hint clocks dict.
    #
    # The clock is constructed as clk_{src_name}_{module_name}. So to get the
    # module name we split from the right and pick the last entry
    hint_clks = {clk: {'name': clk.rsplit('_', 1)[-1], 'src': src}
                 for clk, src in hints.items()}

    # Define a canonical ordering for rg_srcs
    rg_srcs = sorted(rg_srcs_set)

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
    gen_rtl.gen_rtl(IpBlock.from_path(str(hjson_out), []), str(rtl_path))


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
            out = hjson_tpl.render(NumWkups=n_wkups,
                                   Wkups=top["wakeups"],
                                   NumRstReqs=n_rstreqs)

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
    gen_rtl.gen_rtl(IpBlock.from_path(str(hjson_path), []), str(rtl_path))


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
    gen_rtl.gen_rtl(IpBlock.from_path(str(hjson_path), []), str(rtl_path))


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
    gen_rtl.gen_rtl(IpBlock.from_path(str(hjson_path), []), str(rtl_path))


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
        gen_rtl.gen_rtl(IpBlock.from_path(str(hjson_path), []), str(genrtl_dir))


def generate_top_ral(top: Dict[str, object],
                     name_to_block: Dict[str, IpBlock],
                     dv_base_prefix: str,
                     out_path: str):
    # construct top ral block

    regwidth = int(top['datawidth'])
    assert regwidth % 8 == 0
    addrsep = regwidth // 8

    # Generate a map from instance name to the block that it instantiates,
    # together with a map of interface addresses.
    inst_to_block = {}  # type: Dict[str, str]
    if_addrs = {}  # type: Dict[Tuple[str, Optional[str]], int],
    attrs = {}  # type: Dict[str, str]

    for module in top['module']:
        inst_name = module['name']
        block_name = module['type']
        block = name_to_block[block_name]
        if "attr" in module:
            if module["attr"] not in ['templated', 'reggen_top', 'reggen_only']:
                raise ValueError('Unsupported value for attr field of {}: {!r}'
                                 .format(inst_name, module["attr"]))
            attrs[inst_name] = module["attr"]

        inst_to_block[inst_name] = block_name
        for if_name in block.reg_blocks.keys():
            if_addr = int(module["base_addrs"][if_name], 0)
            if_addrs[(inst_name, if_name)] = if_addr

    # Collect up the memories to add
    mems = []
    for item in list(top.get("memory", [])):
        byte_write = ('byte_write' in item and
                      item["byte_write"].lower() == "true")
        data_intg_passthru = ('data_intg_passthru' in item and
                              item["data_intg_passthru"].lower() == "true")
        size_in_bytes = int(item['size'], 0)
        num_regs = size_in_bytes // addrsep
        swaccess = access.SWAccess('top-level memory',
                                   item.get('swaccess', 'rw'))

        mems.append(window.Window(name=item['name'],
                                  desc='(generated from top-level)',
                                  unusual=False,
                                  byte_write=byte_write,
                                  data_intg_passthru=data_intg_passthru,
                                  validbits=regwidth,
                                  items=num_regs,
                                  size_in_bytes=size_in_bytes,
                                  offset=int(item["base_addr"], 0),
                                  swaccess=swaccess))

    chip = Top(regwidth, name_to_block, inst_to_block, if_addrs, mems, attrs)

    # generate the top ral model with template
    return gen_dv(chip, dv_base_prefix, str(out_path))


def _process_top(topcfg, args, cfg_path, out_path, pass_idx):
    # Create generated list
    # These modules are generated through topgen
    generated_list = [
        module['type'] for module in topcfg['module']
        if lib.is_templated(module)
    ]
    log.info("Filtered list is {}".format(generated_list))

    # These modules are NOT generated but belong to a specific top
    # and therefore not part of "hw/ip"
    top_only_list = [
        module['type'] for module in topcfg['module']
        if lib.is_top_reggen(module)
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
        # For modules that are generated prior to gathering, we need to take it from
        # the output path.  For modules not generated before, it may exist in a
        # pre-defined area already.
        log.info("Appending {}".format(ip))
        if ip == 'clkmgr' or (pass_idx > 0):
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

            ip_objs.append(IpBlock.from_path(str(hjson_file), []))

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

    name_to_block = {}  # type: Dict[str, IpBlock]
    for block in ip_objs:
        lblock = block.name.lower()
        assert lblock not in name_to_block
        name_to_block[lblock] = block

    completecfg = merge_top(topcfg, name_to_block, xbar_objs)

    # Generate flash controller and flash memory
    generate_flash(topcfg, out_path)

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
    generate_pinmux(completecfg, out_path)

    # Generate Pwrmgr
    generate_pwrmgr(completecfg, out_path)

    # Generate rstmgr
    generate_rstmgr(completecfg, out_path)

    # Generate top only modules
    # These modules are not templated, but are not in hw/ip
    generate_top_only(top_only_list, out_path, topname)

    if pass_idx > 0 and args.top_ral:
        exit_code = generate_top_ral(completecfg, name_to_block,
                                     args.dv_base_prefix, out_path)
        sys.exit(exit_code)

    return completecfg, name_to_block


def main():
    parser = argparse.ArgumentParser(prog="topgen")
    parser.add_argument('--topcfg',
                        '-t',
                        required=True,
                        help="`top_{name}.hjson` file.")
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

    # TODO, long term, the levels of dependency should be automatically determined instead
    # of hardcoded.  The following are a few examples:
    # Example 1: pinmux depends on amending all modules before calculating the correct number of
    #            pins.
    #            This would be 1 level of dependency and require 2 passes.
    # Example 2: pinmux depends on amending all modules, and pwrmgr depends on pinmux generation to
    #            know correct number of wakeups.  This would be 2 levels of dependency and require 3
    #            passes.
    #
    # How does mulit-pass work?
    # In example 1, the first pass gathers all modules and merges them.  However, the merge process
    # uses a stale pinmux.  The correct pinmux is then generated using the merged configuration. The
    # second pass now merges all the correct modules (including the generated pinmux) and creates
    # the final merged config.
    #
    # In example 2, the first pass gathers all modules and merges them.  However, the merge process
    # uses a stale pinmux and pwrmgr. The correct pinmux is then generated using the merged
    # configuration.  However, since pwrmgr is dependent on this new pinmux, it is still generated
    # incorrectly.  The second pass merge now has an updated pinmux but stale pwrmgr.  The correct
    # pwrmgr can now be generated.  The final pass then merges all the correct modules and creates
    # the final configuration.
    #
    # This fix is related to #2083
    process_dependencies = 1
    for pass_idx in range(process_dependencies + 1):
        log.debug("Generation pass {}".format(pass_idx))
        if pass_idx < process_dependencies:
            cfg_copy = deepcopy(topcfg)
            _process_top(cfg_copy, args, cfg_path, out_path, pass_idx)
        else:
            completecfg, name_to_block = _process_top(topcfg, args, cfg_path, out_path, pass_idx)

    topname = topcfg["name"]

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    # All IPs are generated. Connect phase now
    # Find {memory, module} <-> {xbar} connections first.
    im.autoconnect(completecfg, name_to_block)

    # Generic Inter-module connection
    im.elab_intermodule(completecfg)

    # Generate top.gen.hjson right before rendering
    genhjson_dir = out_path / "data/autogen"
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
        def render_template(template_path: str, rendered_path: Path, **other_info):
            template_contents = generate_top(completecfg, name_to_block,
                                             str(template_path), **other_info)

            rendered_path.parent.mkdir(exist_ok=True, parents=True)
            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)

        # Header for SV files
        gencmd = warnhdr + '''//
// util/topgen.py -t hw/top_{topname}/data/top_{topname}.hjson \\
//                -o hw/top_{topname}/ \\
//                --rnd_cnst_seed {seed}
'''.format(topname=topname, seed=topcfg['rnd_cnst_seed'])

        # SystemVerilog Top:
        # 'toplevel.sv.tpl' -> 'rtl/autogen/top_{topname}.sv'
        render_template(TOPGEN_TEMPLATE_PATH / "toplevel.sv.tpl",
                        out_path / f"rtl/autogen/top_{topname}.sv",
                        gencmd=gencmd)

        # Multiple chip-levels (ASIC, FPGA, Verilator, etc)
        for target in topcfg['targets']:
            render_template(TOPGEN_TEMPLATE_PATH / "chiplevel.sv.tpl",
                            out_path / f"rtl/autogen/chip_{topname}_{target['name']}.sv",
                            gencmd=gencmd,
                            target=target)

        # The C / SV file needs some complex information, so we initialize this
        # object to store it.
        c_helper = TopGenC(completecfg, name_to_block)

        # 'toplevel_pkg.sv.tpl' -> 'rtl/autogen/top_{topname}_pkg.sv'
        render_template(TOPGEN_TEMPLATE_PATH / "toplevel_pkg.sv.tpl",
                        out_path / f"rtl/autogen/top_{topname}_pkg.sv",
                        helper=c_helper,
                        gencmd=gencmd)

        # compile-time random netlist constants
        render_template(TOPGEN_TEMPLATE_PATH / "toplevel_rnd_cnst_pkg.sv.tpl",
                        out_path / f"rtl/autogen/top_{topname}_rnd_cnst_pkg.sv",
                        gencmd=gencmd)

        # C Header + C File + Clang-format file

        # Since SW does not use FuseSoC and instead expects those files always
        # to be in hw/top_{topname}/sw/autogen, we currently create these files
        # twice:
        # - Once under out_path/sw/autogen
        # - Once under hw/top_{topname}/sw/autogen
        for path in [out_path.resolve(),
                     (SRCTREE_TOP / 'hw/top_{}/'.format(topname)).resolve()]:

            # 'clang-format' -> 'sw/autogen/.clang-format'
            cformat_tplpath = TOPGEN_TEMPLATE_PATH / 'clang-format'
            cformat_dir = path / 'sw/autogen'
            cformat_dir.mkdir(parents=True, exist_ok=True)
            cformat_path = cformat_dir / '.clang-format'
            cformat_path.write_text(cformat_tplpath.read_text())

            # 'top_{topname}.h.tpl' -> 'sw/autogen/top_{topname}.h'
            cheader_path = cformat_dir / f"top_{topname}.h"
            render_template(TOPGEN_TEMPLATE_PATH / "toplevel.h.tpl",
                            cheader_path,
                            helper=c_helper)

            # Save the relative header path into `c_gen_info`
            rel_header_path = cheader_path.relative_to(path.parents[1])
            c_helper.header_path = str(rel_header_path)

            # 'toplevel.c.tpl' -> 'sw/autogen/top_{topname}.c'
            render_template(TOPGEN_TEMPLATE_PATH / "toplevel.c.tpl",
                            cformat_dir / f"top_{topname}.c",
                            helper=c_helper)

            # 'toplevel_memory.ld.tpl' -> 'sw/autogen/top_{topname}_memory.ld'
            render_template(TOPGEN_TEMPLATE_PATH / "toplevel_memory.ld.tpl",
                            cformat_dir / f"top_{topname}_memory.ld")

            # 'toplevel_memory.h.tpl' -> 'sw/autogen/top_{topname}_memory.h'
            memory_cheader_path = cformat_dir / f"top_{topname}_memory.h"
            render_template(TOPGEN_TEMPLATE_PATH / "toplevel_memory.h.tpl",
                            memory_cheader_path,
                            helper=c_helper)

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
            xbar_chip_data_path = TOPGEN_TEMPLATE_PATH / tpl_fname
            template_contents = generate_top(completecfg, name_to_block,
                                             str(xbar_chip_data_path))

            rendered_dir = out_path / 'dv/autogen'
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / fname

            with rendered_path.open(mode='w', encoding='UTF-8') as fout:
                fout.write(template_contents)

        # generate parameters for chip-level environment package
        tpl_fname = 'chip_env_pkg__params.sv.tpl'
        alert_handler_chip_data_path = TOPGEN_TEMPLATE_PATH / tpl_fname
        template_contents = generate_top(completecfg, name_to_block,
                                         str(alert_handler_chip_data_path))

        rendered_dir = out_path / 'dv/env/autogen'
        rendered_dir.mkdir(parents=True, exist_ok=True)
        rendered_path = rendered_dir / 'chip_env_pkg__params.sv'

        with rendered_path.open(mode='w', encoding='UTF-8') as fout:
            fout.write(template_contents)


if __name__ == "__main__":
    main()
