#!/usr/bin/env python3
# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
r"""Top Module Generator
"""
import argparse
import logging as log
import shutil
import sys
import tempfile
from collections import OrderedDict, defaultdict
from copy import deepcopy
from pathlib import Path
from typing import Callable, Dict, List, NamedTuple, Optional, Tuple

import hjson
import tlgen
import version_file
from basegen.typing import ConfigT, ParamsT
from design.lib.OtpMemMap import OtpMemMap
from ipgen import (IpBlockRenderer, IpConfig, IpDescriptionOnlyRenderer,
                   IpTemplate, TemplateRenderError)
from ipgen.clkmgr_gen import get_clkmgr_params
from mako import exceptions
from mako.lookup import TemplateLookup
from mako.template import Template
from raclgen.lib import DEFAULT_RACL_CONFIG
from reggen import access, gen_rtl, gen_sec_cm_testplan, window
from reggen.countermeasure import CounterMeasure
from reggen.ip_block import IpBlock
from topgen import get_hjsonobj_xbars
from topgen import intermodule as im
from topgen import lib as lib
from topgen import merge_top, secure_prng, validate_top
from topgen.c_test import TopGenCTest
from topgen.clocks import Clocks
from topgen.gen_dv import gen_dv
from topgen.gen_top_docs import gen_top_docs
from topgen.lib import find_module, find_modules, load_cfg
from topgen.merge import (
    amend_alert, amend_interrupt, amend_pinmux_io, amend_racl,
    amend_reset_request, amend_resets, amend_wkup, commit_alert_modules,
    commit_interrupt_modules, commit_outgoing_alert_modules,
    commit_outgoing_interrupt_modules, connect_clocks,
    create_alert_lpgs, elaborate_instance, extract_clocks)
from topgen.resets import Resets
from topgen.rust import TopGenRust
from topgen.top import Top
from topgen.typing import IpBlocksT

# Common header for generated files
warnhdr = """//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED WITH THE FOLLOWING COMMAND:
"""
genhdr = """// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
""" + warnhdr

GENCMD = ("// util/topgen.py -t hw/{top_name}/data/{top_name}.hjson\n"
          "// -o hw/{top_name}")

SRCTREE_TOP = Path(__file__).parents[1].resolve()

TOPGEN_TEMPLATE_PATH = SRCTREE_TOP / "util" / "topgen" / "templates"
IP_RAW_PATH = SRCTREE_TOP / "hw" / "ip"
IP_TEMPLATES_PATH = SRCTREE_TOP / "hw" / "ip_templates"


class UniquifiedModules(object):
    """This holds the uniquified name for all uniquified modules."""

    def __init__(self):
        self.modules: Dict[str, str] = {}

    def add_module(self, name: str, uniquified_name: str):
        if name == uniquified_name:
            return
        if (name in self.modules and uniquified_name != self.modules[name]):
            raise SystemExit(f"Multiple renames for module {name}")
        self.modules[name] = uniquified_name

    def get_uniq_name(self, name: str) -> Optional[str]:
        return self.modules.get(name)


uniquified_modules = UniquifiedModules()


class IpAttrs(NamedTuple):
    """Hold IP block, and path to hjson."""
    ip_block: IpBlock
    hjson_path: Path
    top_only: bool
    instances: List[object]


def _ipgen_render_prelude(template_name: str, topname: str,
                          params: ParamsT) -> (str, IpTemplate, IpConfig):
    module_name = (params.get("module_instance_name", template_name)
                   if params else template_name)
    top_name = f"top_{topname}"
    instance_name = f"{top_name}_{module_name}"
    ip_template = IpTemplate.from_template_path(IP_TEMPLATES_PATH /
                                                template_name)
    params.update({
        "topname": topname,
        "uniquified_modules": uniquified_modules.modules
    })

    try:
        ip_config = IpConfig(ip_template.params, instance_name, params)
    except ValueError as e:
        log.error(f"Unable to render IP template {template_name!r}: {str(e)}")
        sys.exit(1)
    return (module_name, ip_template, ip_config)


def ipgen_hjson_render(template_name: str, topname: str,
                       params: ParamsT) -> IpBlock:
    """ Render an IP hjson template for a specific toplevel using ipgen.

    Renders the hjson template as a string and returns an IpBlock
    constructed from it.

    Aborts the program execution in case of an error.
    """
    (_module_name, ip_template,
     ip_config) = _ipgen_render_prelude(template_name, topname, params)

    try:
        ip_desc = IpDescriptionOnlyRenderer(ip_template, ip_config).render()
    except TemplateRenderError as e:
        log.error(e.verbose_str())
        sys.exit(1)
    return IpBlock.from_text(
        ip_desc, [], f"ipgen description from {ip_template.template_path}")


def ipgen_render(template_name: str, topname: str, params: ParamsT,
                 out_path: Path) -> None:
    """ Render an IP template for a specific toplevel using ipgen.

    The generated IP block is placed in the "ip_autogen" directory of the
    toplevel.

    Aborts the program execution in case of an error.
    """
    (module_name, ip_template,
     ip_config) = _ipgen_render_prelude(template_name, topname, params)

    try:
        renderer = IpBlockRenderer(ip_template, ip_config)
        renderer.render(out_path / "ip_autogen" / module_name,
                        overwrite_output_dir=True)
    except TemplateRenderError as e:
        log.error(e.verbose_str())
        sys.exit(1)


def generate_top(top: ConfigT, name_to_block: IpBlocksT, tpl_filename: str,
                 **kwargs: Dict[str, object]) -> None:
    top_tpl = Template(filename=tpl_filename,
                       lookup=TemplateLookup([TOPGEN_TEMPLATE_PATH, "/"]))

    try:
        return top_tpl.render(top=top, name_to_block=name_to_block, **kwargs)
    except:  # noqa: E722
        log.error(exceptions.text_error_template().render())
        return ""


def configure_xbars(top: ConfigT) -> None:
    """Complete all xbar configs in the top config.

    Run validate and elaborate, and create the inter_signal_lists.
    """

    def create_inter_signal(name: str, act: str) -> Dict[str, str]:
        name_suffix = name.replace(".", "__")
        inter_signal: OrderedDict() = {
            "name": f"tl_{name_suffix}",
            "struct": "tl",
            "package": "tlul_pkg",
            "type": "req_rsp",
            "act": act,
        }
        return inter_signal

    def create_inter_signal_list(xar):
        isl = []
        for i, node in enumerate(xbar.hosts, 1):
            inter_signal = create_inter_signal(node.name, "rsp")
            isl.append(inter_signal)
        for i, node in enumerate(xbar.devices, 1):
            inter_signal = create_inter_signal(node.name, "req")
            isl.append(inter_signal)
        return isl

    for obj in top["xbar"]:
        objname = obj["name"]
        xbar = tlgen.validate(obj)
        if not tlgen.elaborate(xbar):
            log.error(f"Elaboration of xbar {objname} failed:\n" +
                      repr(vars(xbar)))
            raise SystemExit(sys.exc_info()[1])
        inter_signal_list = create_inter_signal_list(xbar)
        obj["inter_signal_list"] = inter_signal_list


def generate_xbars(top: ConfigT, out_path: Path) -> None:
    """Re-run validate and elaborate to generate the Xbar objects."""
    top_name = "top_" + top["name"]
    gencmd = (f"// util/topgen.py -t hw/{top_name}/data/{top_name}.hjson "
              f"-o hw/{top_name}/\n\n")

    for obj in top["xbar"]:
        objname = obj["name"]
        log.info(f"generating xbar {objname}")
        xbar_path = out_path / "ip" / f"xbar_{objname}" / "data" / "autogen"
        xbar_path.mkdir(parents=True, exist_ok=True)
        xbar = tlgen.validate(obj)
        xbar.ip_path = "/".join(["hw", top_name, "ip", "{dut}"])

        # Generate output of crossbar with complete fields
        xbar_hjson_path = xbar_path / f"xbar_{xbar.name}.gen.hjson"
        xbar_hjson_path.write_text(genhdr + gencmd +
                                   hjson.dumps(obj, for_json=True) + '\n')

        if not tlgen.elaborate(xbar):
            log.error("Elaboration failed." + repr(xbar))

        try:
            results = tlgen.generate(xbar, top_name)
        except:  # noqa: E722
            log.error(exceptions.text_error_template().render())

        ip_path = out_path / "ip" / f"xbar_{objname}"

        for filename, filecontent in results:
            filepath = ip_path / filename
            filepath.parent.mkdir(parents=True, exist_ok=True)
            with filepath.open(mode="w", encoding="UTF-8") as fout:
                fout.write(filecontent)

        dv_path = out_path / "ip" / f"xbar_{objname}" / "dv" / "autogen"
        dv_path.mkdir(parents=True, exist_ok=True)

        # generate testbench for xbar
        tlgen.generate_tb(xbar, dv_path, top_name)


def generate_ipgen(top: ConfigT, module: ConfigT, params: ParamsT,
                   out_path: Path) -> None:
    topname = top["name"]
    template_name = module["template_type"]
    module_name = module["type"]
    module_instance_name = params.get("module_instance_name")
    if module_instance_name and module_instance_name != module_name:
        raise ValueError(
            f"Unexpected module_instance_name: expected {module_name}, got "
            f"{module_instance_name}")
    uniq_name = uniquified_modules.get_uniq_name(template_name)
    if uniq_name and uniq_name != module_instance_name:
        raise ValueError(
            f"Unexpected uniquified name: expected {module_instance_name}, "
            f"got {uniq_name}")
    ipgen_render(module["template_type"], topname, params, out_path)


def _get_alert_handler_params(top: ConfigT) -> ParamsT:
    """Returns parameters for alert_hander ipgen from top config."""
    # default values
    esc_cnt_dw = 32
    accu_cnt_dw = 16
    # leave this constant
    n_classes = 4

    # Count number of alerts and LPGs, accepting lack of alert_lpgs in top.
    # They are added after the merge pass, so the ip_block won't have them.
    n_alerts = sum(
        [int(x["width"]) if "width" in x else 1 for x in top["alert"]])
    n_lpgs_int = len(top.get("alert_lpgs", []))
    n_lpgs = n_lpgs_int
    n_lpgs_incoming_offset = n_lpgs
    # Add incoming alerts and their LPGs
    for alerts in top['incoming_alert'].values():
        n_alerts += len(alerts)
        # Number of LPGs is maximum index + 1
        n_lpgs += max(alert['lpg_idx'] for alert in alerts) + 1

    if n_alerts < 1:
        # set number of alerts to 1 such that the config is still valid
        # that input will be tied off
        n_alerts = 1
        log.warning("no alerts are defined: is alert_handler needed?")

    async_on = []
    async_on_format = "1'b{:01b}"
    lpg_map = []
    if n_lpgs:
        # format to print lpg indices in decimal format
        n_lpg_width = n_lpgs.bit_length()
        lpg_idx_format = f"{n_lpg_width}'d{{:d}}"

    for alert in top["alert"]:
        for _ in range(alert["width"]):
            async_on.append(async_on_format.format(int(alert["async"])))
            if n_lpgs_int:
                lpg_map.append(lpg_idx_format.format(int(alert["lpg_idx"])))

    if "incoming_alert" in top:
        lpg_prev_offset = n_lpgs_incoming_offset
        for alerts in top['incoming_alert'].values():
            for alert in alerts:
                for _ in range(alert["width"]):
                    async_on.append(async_on_format.format(int(
                        alert["async"])))
                    lpg_map.append(
                        lpg_idx_format.format(lpg_prev_offset +
                                              int(alert["lpg_idx"])))
            lpg_prev_offset += max(alert['lpg_idx'] for alert in alerts) + 1
    module = lib.find_module(top["module"], "alert_handler")
    uniquified_modules.add_module(module["template_type"], module["type"])

    n_esc_sev = module["param_decl"]["EscNumSeverities"]
    ping_cnt_dw = module["param_decl"]["EscPingCountWidth"]

    return {
        "module_instance_name": module["type"],
        "n_alerts": n_alerts,
        "esc_cnt_dw": esc_cnt_dw,
        "accu_cnt_dw": accu_cnt_dw,
        "async_on": async_on,
        "n_classes": n_classes,
        "n_esc_sev": n_esc_sev,
        "ping_cnt_dw": ping_cnt_dw,
        "n_lpg": n_lpgs,
        "lpg_map": lpg_map,
    }


def generate_alert_handler(top: ConfigT, module: ConfigT,
                           out_path: Path) -> None:
    log.info("Generating alert_handler with ipgen")
    params = _get_alert_handler_params(top)
    generate_ipgen(top, module, params, out_path)


def generate_outgoing_alerts(top: ConfigT, out_path: Path) -> None:
    log.info("Generating outgoing alert definitions")

    def render_template(template_path: Path, rendered_path: Path,
                        **other_info):
        template_contents = generate_top(top, None, str(template_path),
                                         **other_info)

        rendered_path.parent.mkdir(exist_ok=True, parents=True)
        with rendered_path.open(mode="w", encoding="UTF-8") as fout:
            fout.write(template_contents)

    for alert_group, alerts in top['outgoing_alert'].items():
        # Outgoing alert definition
        # 'outgoing_alerts.hjson.tpl' -> 'data/autogen/{top_name}.sv'
        render_template(TOPGEN_TEMPLATE_PATH / 'outgoing_alerts.hjson.tpl',
                        out_path / 'data' / 'autogen' /
                        f'outgoing_alerts_{alert_group}.hjson',
                        alert_group=alert_group,
                        alerts=alerts)


def generate_outgoing_interrupts(top: ConfigT, out_path: Path) -> None:
    log.info("Generating outgoing interrupt definitions")

    def render_template(template_path: Path, rendered_path: Path,
                        **other_info):
        template_contents = generate_top(top, None, str(template_path),
                                         **other_info)

        rendered_path.parent.mkdir(exist_ok=True, parents=True)
        with rendered_path.open(mode="w", encoding="UTF-8") as fout:
            fout.write(template_contents)

    for interrupt_group, interrupts in top["outgoing_interrupt"].items():
        # Outgoing interrupt definition
        # "outgoing_interrupts.hjson.tpl" -> "data/autogen/{top_name}.sv"
        render_template(TOPGEN_TEMPLATE_PATH / "outgoing_interrupts.hjson.tpl",
                        out_path / "data" / "autogen" /
                        f"outgoing_interrupts_{interrupt_group}.hjson",
                        interrupt_group=interrupt_group,
                        interrupts=interrupts)


def _get_rv_plic_params(top: ConfigT) -> ParamsT:
    """Gets parameters for plic ipgen from top config."""
    # Get the PLIC instance
    module = lib.find_module(top["module"], "rv_plic")

    # Count number of interrupts
    # Interrupt source 0 is tied to 0 to conform RISC-V PLIC spec.
    # So, total number of interrupts are the number of entries in the list + 1
    num_srcs = sum(
        [int(x["width"]) if "width" in x else 1 for x in top["interrupt"]]) + 1
    num_cores = int(top["num_cores"], 0) if "num_cores" in top else 1
    uniquified_modules.add_module(module["template_type"], module["type"])
    return {
        "module_instance_name": module["type"],
        "src": num_srcs,
        "target": num_cores,
        "prio": 3,
    }


def generate_plic(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating rv_plic with ipgen")
    params = _get_rv_plic_params(top)
    generate_ipgen(top, module, params, out_path)


def generate_regfile_from_path(hjson_path: Path,
                               generated_rtl_path: Path) -> None:
    """Generate RTL register file from path and check countermeasure labels"""
    obj = IpBlock.from_path(str(hjson_path), [])

    # If this block has countermeasures, we grep for RTL annotations in
    # all .sv implementation files and check whether they match up
    # with what is defined inside the Hjson.
    sv_files = generated_rtl_path.glob("*.sv")
    rtl_names = CounterMeasure.search_rtl_files(sv_files)
    obj.check_cm_annotations(rtl_names, str(hjson_path))
    gen_rtl.gen_rtl(obj, str(generated_rtl_path))
    if gen_sec_cm_testplan.gen_sec_cm_testplan(obj, hjson_path.parent):
        sys.exit(1)


def _get_pinmux_params(top: ConfigT) -> ParamsT:
    """Gets parameters for pinmux ipgen from top config."""
    # Generation without pinmux and pinout configuration is not supported.
    assert "pinmux" in top
    assert "pinout" in top

    pinmux = top["pinmux"]

    # Get number of wakeup detectors
    if "num_wkup_detect" in pinmux:
        num_wkup_detect = pinmux["num_wkup_detect"]
    else:
        num_wkup_detect = 1

    if num_wkup_detect <= 0:
        # TODO: add support for no wakeup counter case
        log.error("Topgen does currently not support generation of a top " +
                  "without DIOs.")
        return

    if "wkup_cnt_width" in pinmux:
        wkup_cnt_width = pinmux["wkup_cnt_width"]
    else:
        wkup_cnt_width = 8

    if wkup_cnt_width <= 1:
        log.error("Wakeup counter width must be greater equal 2.")
        return

    # MIO Pads
    n_mio_pads = pinmux["io_counts"]["muxed"]["pads"]

    # Total inputs/outputs
    # Reuse the counts from the merge phase
    n_mio_periph_in = (pinmux["io_counts"]["muxed"]["inouts"] +
                       pinmux["io_counts"]["muxed"]["inputs"])
    n_mio_periph_out = (pinmux["io_counts"]["muxed"]["inouts"] +
                        pinmux["io_counts"]["muxed"]["outputs"])
    n_dio_periph_in = (pinmux["io_counts"]["dedicated"]["inouts"] +
                       pinmux["io_counts"]["dedicated"]["inputs"])
    n_dio_periph_out = (pinmux["io_counts"]["dedicated"]["inouts"] +
                        pinmux["io_counts"]["dedicated"]["outputs"])
    n_dio_pads = (pinmux["io_counts"]["dedicated"]["inouts"] +
                  pinmux["io_counts"]["dedicated"]["inputs"] +
                  pinmux["io_counts"]["dedicated"]["outputs"])

    # Generation with zero MIO/DIO pads is currently not supported.
    assert (n_mio_pads > 0)
    assert (n_dio_pads > 0)

    log.info("Generating pinmux with following info from hjson:")
    log.info("num_wkup_detect: %d" % num_wkup_detect)
    log.info("wkup_cnt_width:  %d" % wkup_cnt_width)
    log.info("n_mio_periph_in:  %d" % n_mio_periph_in)
    log.info("n_mio_periph_out: %d" % n_mio_periph_out)
    log.info("n_dio_periph_in:  %d" % n_dio_periph_in)
    log.info("n_dio_periph_out: %d" % n_dio_periph_out)
    log.info("n_dio_pads:       %d" % n_dio_pads)

    return {
        "n_wkup_detect": num_wkup_detect,
        "wkup_cnt_width": wkup_cnt_width,
        "n_mio_pads": n_mio_pads,
        "n_mio_periph_in": n_mio_periph_in,
        "n_mio_periph_out": n_mio_periph_out,
        "n_dio_pads": n_dio_pads,
        "n_dio_periph_in": n_dio_periph_in,
        "n_dio_periph_out": n_dio_periph_out,
        "enable_usb_wakeup": pinmux['enable_usb_wakeup'],
        "enable_strap_sampling": pinmux['enable_strap_sampling'],
    }


def generate_pinmux(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating pinmux with ipgen")
    params = _get_pinmux_params(top)
    generate_ipgen(top, module, params, out_path)


# generate clkmgr with ipgen
def generate_clkmgr(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating clkmgr with ipgen")
    params = get_clkmgr_params(top)
    log.info("clkmgr params:")
    for k, v in params.items():
        log.info(f"{k}: {v}")
    generate_ipgen(top, module, params, out_path)


def _get_pwrmgr_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for pwrmgr ipgen."""
    # Count number of wakeups
    n_wkups = len(top["wakeups"])
    log.info("Found {} wakeup signals".format(n_wkups))

    if n_wkups < 1:
        n_wkups = 1
        log.warning(
            "The design has no wakeup sources. Low power not supported.")

    # Count number of reset requests
    n_rstreqs = len(top["reset_requests"]["peripheral"])
    log.info("Found {} reset request signals".format(n_rstreqs))

    if n_rstreqs < 1:
        n_rstreqs = 1
        log.warning("The design has no reset request sources. "
                    "Reset requests are not supported.")

    n_rom_ctrl = lib.num_rom_ctrl(top['module'])
    assert n_rom_ctrl > 0

    # Add another artificial ROM_CTRL input to allow IBEX halting that input
    if top['power'].get('halt_ibex_via_rom_ctrl', False):
        n_rom_ctrl += 1

    clocks = top["clocks"]
    assert isinstance(clocks, Clocks)
    src_clks = [obj.name for obj in clocks.srcs.values() if not obj.aon]

    return {
        "NumWkups": n_wkups,
        "Wkups": top["wakeups"],
        "NumRstReqs": n_rstreqs,
        "rst_reqs": top["reset_requests"],
        "wait_for_external_reset": top['power']['wait_for_external_reset'],
        "NumRomInputs": n_rom_ctrl,
        "has_aon_clk": any(obj.aon for obj in clocks.srcs.values()),
        "src_clks": src_clks,
    }


def generate_pwrmgr(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating pwrmgr with ipgen")
    params = _get_pwrmgr_params(top)
    generate_ipgen(top, module, params, out_path)


def get_rst_ni(top: ConfigT) -> object:
    rstmgr = find_module(top["module"], "rstmgr", True)
    return rstmgr["reset_connections"]


def _get_rstmgr_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for rstmgr ipgen."""
    # Parameters needed for generation
    reset_obj = top["resets"]

    # The original resets dict is transformed to the reset class
    assert isinstance(reset_obj, Resets)

    # unique clocks
    clks = reset_obj.get_clocks()
    clocks = top["clocks"]
    assert isinstance(clocks, Clocks)
    src_freqs = {sv.name: sv.freq for sv in clocks.srcs.values()}
    src_freqs.update({dv.name: dv.freq for dv in clocks.derived_srcs.values()})
    # Create a dictionary indexed by clks containing their frequency.
    clk_freqs = {clk: src_freqs[clk] for clk in clks}

    # resets sent to reset struct
    output_rsts = reset_obj.get_top_resets()

    # sw controlled resets: dict indexed by device containing the clock
    sw_rsts = OrderedDict([(r.name, r.clock.name)
                           for r in reset_obj.get_sw_resets()])
    # rst_ni
    rst_ni = get_rst_ni(top)

    # leaf resets
    leaf_rsts = reset_obj.get_generated_resets()

    # Number of reset requests
    n_rstreqs = len(top["reset_requests"]["peripheral"])

    # Will connect to alert_handler
    with_alert_handler = lib.find_module(top['module'],
                                         'alert_handler') is not None

    return {
        "clk_freqs": clk_freqs,
        "reqs": top["reset_requests"],
        "power_domains": top["power"]["domains"],
        "num_rstreqs": n_rstreqs,
        "sw_rsts": sw_rsts,
        "output_rsts": output_rsts,
        "leaf_rsts": leaf_rsts,
        "rst_ni": rst_ni['rst_ni']['name'],
        "export_rsts": top["exported_rsts"],
        "with_alert_handler": with_alert_handler,
    }


# generate rstmgr with ipgen
def generate_rstmgr(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating rstmgr with ipgen")
    params = _get_rstmgr_params(top)
    generate_ipgen(top, module, params, out_path)


def _get_flash_ctrl_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for flash_ctrl ipgen."""

    # Parameters needed for generation
    flash_mems = find_modules(top["module"], "flash_ctrl", True)
    if len(flash_mems) > 1:
        log.error("This design does not currently support multiple flashes")
        return
    elif len(flash_mems) == 0:
        raise ValueError(
            "In _get_flash_ctrl_params for design with no flash_ctrl")

    params = vars(flash_mems[0]["memory"]["mem"]["config"])
    # Additional parameters not provided in the top config.
    params.update({
        "metadata_width": 12,
        "info_types": 3,
        "infos_per_bank": [10, 1, 2],
    })

    params.pop('base_addrs', None)
    return params


# generate flash_ctrl with ipgen
def generate_flash(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info("Generating flash_ctrl with ipgen")
    params = _get_flash_ctrl_params(top)
    generate_ipgen(top, module, params, out_path)


def _get_otp_ctrl_params(top: ConfigT,
                         out_path: Path,
                         seed: int = None) -> ParamsT:

    def has_flash_keys(parts, path) -> bool:
        """Determines if the SECRET1 partition has flash key seeds.

        This assumes the flash keys are in the secret1 partition, and are
        named "flash*key_seed" (case doesn't matter). If in some future
        otp mmap the location of these keys changes we can revisit this
        detection.
        """
        for p in parts:
            if p["name"].lower() == "secret1":
                secret1_partition = p
                break
        else:
            raise ValueError(f"SECRET1 partition not found in {path}")
        flash_keys = [i for i in secret1_partition["items"]
                      if i["name"].lower().startswith("flash")
                      and i["name"].lower().endswith("key_seed")]
        return len(flash_keys) > 0

    """Returns the parameters extracted from the otp_mmap.hjson file."""
    otp_mmap_path = out_path / "data" / "otp" / "otp_ctrl_mmap.hjson"
    otp_mmap = OtpMemMap.from_mmap_path(otp_mmap_path, seed).config
    enable_flash_keys = has_flash_keys(otp_mmap["partitions"], otp_mmap_path)
    return {
        "otp_mmap": otp_mmap,
        "enable_flash_key": enable_flash_keys,
    }


def generate_otp_ctrl(top: ConfigT,
                      module: ConfigT,
                      cfg_path: Path,
                      out_path: Path,
                      seed: int = None) -> None:
    log.info("Generating otp_ctrl with ipgen")
    params = _get_otp_ctrl_params(top, cfg_path, seed)
    generate_ipgen(top, module, params, out_path)


def _get_ac_range_check_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for ac_range_check ipgen."""
    # Determine RACL params from the top-level config, otherwise use ipgen's
    # default values
    racl_params = {}
    if "racl_config" in top:
        racl_params = {
            "nr_role_bits": top["racl"]["nr_role_bits"],
            "nr_ctn_uid_bits": top["racl"]["nr_ctn_uid_bits"]
        }

    # Get the AC Range Check instance
    module = lib.find_module(top['module'], 'ac_range_check')
    uniquified_modules.add_module(module["template_type"], module["type"])
    params = {
        "num_ranges": module["ipgen_param"]["num_ranges"],
        "module_instance_name": module["type"]
    }
    params.update(racl_params)
    return params


# generate ac_range_check with ipgen
def generate_ac_range_check(top: ConfigT, module: ConfigT,
                            out_path: Path) -> None:
    log.info('Generating ac_range_check with ipgen')
    params = _get_ac_range_check_params(top)
    generate_ipgen(top, module, params, out_path)


def _get_racl_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for racl_ctrl ipgen."""
    module = lib.find_module(top["module"], "racl_ctrl")
    racl_group = module.get("racl_group", "Null")
    if len(top["racl"]["policies"]) == 1:
        # If there is only one set of policies, take the first one
        policies = list(top["racl"]["policies"].values())[0]
    else:
        # More than one policy, we need to find the matching set of policies
        policies = top["racl"]["policies"][racl_group]

    num_subscribing_ips = defaultdict(int)
    for m in top["module"]:
        racl_mappings = m.get("racl_mappings", {})

        for group in set(
            mapping['racl_group'] for mapping in racl_mappings.values()
        ):
            num_subscribing_ips[group] += 1

    uniquified_modules.add_module(module["template_type"], module["type"])

    return {
        "module_instance_name": module["type"],
        "nr_role_bits": top["racl"]["nr_role_bits"],
        "nr_ctn_uid_bits": top["racl"]["nr_ctn_uid_bits"],
        "nr_policies": top["racl"]["nr_policies"],
        'nr_subscribing_ips': num_subscribing_ips[racl_group],
        "policies": policies
    }


# Generate RACL collateral
def generate_racl(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    # Not all tops use RACL
    if "racl_config" not in top:
        raise ValueError(
            "There is a racl_ctrl module but no 'racl_config' in top config")
    log.info("Generating RACL Control IP with ipgen")
    params = _get_racl_params(top)
    generate_ipgen(top, module, params, out_path)


def _get_gpio_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for GPIO ipgen."""
    module = lib.find_module(top["module"], "gpio")
    uniquified_modules.add_module(module["template_type"], module["type"])

    params = {
        # TODO(#26553): Remove the following code once topgen automatically
        # incorporates template parameters.
        "num_inp_period_counters":
        module.get("ipgen_param", {}).get("num_inp_period_counters", 0),
        "module_instance_name":
        module["type"]
    }
    return params


def generate_gpio(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info('Generating GPIO with ipgen')
    params = _get_gpio_params(top)
    generate_ipgen(top, module, params, out_path)


def _get_rv_core_ibex_params(topcfg: Dict[str, object]) -> Dict[str, object]:
    """Extracts parameters for rv_core_ibex ipgen."""
    module = lib.find_module(topcfg["module"], "rv_core_ibex")
    uniquified_modules.add_module(module["template_type"], module["type"])

    return {
        "racl_support": module.get("ipgen_param", {}).get("racl_support", False),
        "num_regions": module['ipgen_param']['NumRegions'],
        'module_instance_name': module['type']
    }


def generate_rv_core_ibex(topcfg: Dict[str, object], module: Dict[str, object],
                          out_path: Path) -> None:
    log.info("Generating RV Core Ibex with ipgen")
    params = _get_rv_core_ibex_params(topcfg)
    generate_ipgen(topcfg, module, params, out_path)


def _get_pwm_params(top: ConfigT) -> ParamsT:
    """Extracts parameters for PWM ipgen."""

    pwm = lib.find_module(top["module"], "pwm")
    params = {"module_instance_name": pwm["type"]}
    return params


def generate_pwm(top: ConfigT, module: ConfigT, out_path: Path) -> None:
    log.info('Generating PWM with ipgen')
    params = _get_pwm_params(top)
    generate_ipgen(top, module, params, out_path)


def generate_top_only(top_only_dict: List[str], out_path: Path, top_name: str,
                      alt_hjson_path: str) -> None:
    """Generate the regfile for top_only IPs."""
    log.info("Generating top only modules")

    for ip in top_only_dict:
        ip_out_path = out_path / "ip" / ip
        hjson_path = ip_out_path / "data" / f"{ip}.hjson"
        genrtl_dir = ip_out_path / "rtl"
        genrtl_dir.mkdir(parents=True, exist_ok=True)
        log.info(f"Generating registers for top module {ip}, hjson: "
                 f"{hjson_path}, output: {genrtl_dir}")
        generate_regfile_from_path(hjson_path, genrtl_dir)


def generate_top_ral(topname: str, top: ConfigT, name_to_block: IpBlocksT,
                     dv_base_names: List[str], out_path: str) -> None:
    # construct top ral block
    regwidth = int(top["datawidth"])
    assert regwidth % 8 == 0
    addrsep = regwidth // 8

    # Generate a map from instance name to the block that it instantiates,
    # together with a map of interface addresses.
    inst_to_block: Dict[str, str] = {}
    if_addrs: Dict[Tuple[str, Optional[str]], int] = {}
    attrs: Dict[str, str] = {}

    for module in top["module"]:
        inst_name = module["name"]
        block_name = module["type"]
        block = name_to_block[block_name]
        if "attr" in module:
            attrs[inst_name] = module["attr"]

        inst_to_block[inst_name] = block_name
        for if_name in block.reg_blocks.keys():
            if_addr = {
                asid: int(addr, 0)
                for (asid, addr) in module["base_addrs"][if_name].items()
            }
            if_addrs[(inst_name, if_name)] = if_addr

    # Collect up the memories to add
    mems = []
    for item in list(top.get("memory", [])):
        mems.append(create_mem(item, addrsep, regwidth))

    # Top-level may override the mem setting. Store the new type to
    # name_to_block. If no other instance uses the original type, delete it
    original_types = set()
    for module in top["module"]:
        if "memory" in module.keys() and len(module["memory"]) > 0:
            newtype = "{}_{}".format(module["type"], module["name"])
            assert newtype not in name_to_block

            block = deepcopy(name_to_block[module["type"]])
            name_to_block[newtype] = block
            inst_to_block[module["name"]] = newtype

            original_types.add(module["type"])

            for mem_name, item in module["memory"].items():
                assert block.reg_blocks[mem_name]
                assert len(block.reg_blocks[mem_name].windows) <= 1
                item["name"] = mem_name

                win = create_mem(item, addrsep, regwidth)
                if len(block.reg_blocks[mem_name].windows) > 0:
                    blk_win = block.reg_blocks[mem_name].windows[0]

                    # Top can only add new info for mem, shouldn't overwrite
                    # existing configuration
                    assert win.items == blk_win.items
                    assert win.byte_write == blk_win.byte_write
                    assert win.data_intg_passthru == blk_win.data_intg_passthru

                    block.reg_blocks[mem_name].windows[0] = win
                else:
                    block.reg_blocks[mem_name].windows.append(win)

    for t in original_types:
        if t not in inst_to_block.values():
            del name_to_block[t]

    addr_spaces = {addr_space["name"] for addr_space in top["addr_spaces"]}
    chip = Top(topname, regwidth, addr_spaces, name_to_block, inst_to_block,
               if_addrs, mems, attrs)

    # generate the top ral model with template
    return gen_dv(chip, dv_base_names, str(out_path))


def create_mem(item, addrsep, regwidth) -> window.Window:
    byte_write = ("byte_write" in item and
                  item["byte_write"].lower() == "true")
    data_intg_passthru = ("data_intg_passthru" in item and
                          item["data_intg_passthru"].lower() == "true")
    size_in_bytes = int(item["size"], 0)
    num_regs = size_in_bytes // addrsep
    swaccess = access.SWAccess("top-level memory", item.get("swaccess", "rw"))

    return window.Window(name=item["name"],
                         desc="(generated from top-level)",
                         unusual=False,
                         byte_write=byte_write,
                         data_intg_passthru=data_intg_passthru,
                         validbits=regwidth,
                         items=num_regs,
                         size_in_bytes=size_in_bytes,
                         offset=int(item.get("base_addr", "0"), 0),
                         swaccess=swaccess)


def generate_rust(topname, completecfg, name_to_block, out_path, version_stamp,
                  src_tree_top, topgen_template_path) -> None:
    # Template render helper
    def render_template(template_path: str, rendered_path: Path, **other_info):
        template_contents = generate_top(completecfg, name_to_block,
                                         str(template_path), **other_info)

        rendered_path.parent.mkdir(exist_ok=True, parents=True)
        with rendered_path.open(mode="w", encoding="UTF-8") as fout:
            fout.write(template_contents)

    # Create Rust output directory
    rsformat_dir = out_path / "sw/autogen/chip/"
    rsformat_dir.mkdir(parents=True, exist_ok=True)

    # Generating Rust device description for external sw usage
    render_template(topgen_template_path / 'toplevel_mod.rs.tpl',
                    rsformat_dir / 'mod.rs')

    for addr_space in completecfg['addr_spaces']:
        addr_space_suffix = lib.get_addr_space_suffix(addr_space)

        # The Rust file needs some complex information, so we initialize this
        # object to store it.
        rs_helper = TopGenRust(completecfg, name_to_block, version_stamp)

        # Generate Rust device-side files
        rsformat_dir = out_path / "sw/autogen/chip/"
        render_template(topgen_template_path / 'toplevel.rs.tpl',
                        rsformat_dir / f"top_{topname}{addr_space_suffix}.rs",
                        addr_space=addr_space['name'],
                        helper=rs_helper)

        # Generate Rust host-side files
        rsformat_dir = src_tree_top / 'sw/host/opentitanlib/src/chip/autogen'
        rsformat_dir.mkdir(parents=True, exist_ok=True)
        render_template(topgen_template_path / 'host_toplevel.rs.tpl',
                        rsformat_dir / f"{topname}{addr_space_suffix}.rs",
                        addr_space=addr_space['name'],
                        helper=rs_helper)


def _amend_block_reset_connections(module: ConfigT,
                                   default_power_domain: str) -> None:
    for port, reset in module["reset_connections"].items():
        if isinstance(reset, str):
            if "domain" not in module:
                domain = default_power_domain
            else:
                if len(module["domain"]) > 1:
                    raise ValueError(
                        f"{module['name']} reset connection {reset} "
                        "has no assigned domain")
                domain = module["domain"][0]
            module["reset_connections"][port] = {
                'name': reset,
                'domain': domain,
            }


def amend_reset_connections(topcfg: ConfigT) -> None:
    """Complete the reset connections information for each module.

    Add an explicit domain entry for each reset connection.
    The reset_connections are dictionaries keyed by a port name and
    with a value that can be just a string or a dictionary with a name
    and a domain. When the value is just a string determine the domain
    as the module's domain, or the default domain from the topcfg.
    """
    default_power_domain = topcfg["power"]["default"]
    for module in topcfg["module"]:
        _amend_block_reset_connections(module, default_power_domain)
    for xbar in topcfg["xbar"]:
        _amend_block_reset_connections(xbar, default_power_domain)


def create_generic_ip_blocks(topcfg: ConfigT, alias_cfgs: Dict[str, ConfigT],
                             cfg_path: Path,
                             out_path: Path) -> Dict[str, IpAttrs]:
    """Create IpAttrs for each generic ip type.

    Most importantly, IpAttrs holds the IpBlock.

    Raise an exception if any module's "attr" flag is invalid.
    """

    def handle_instance(top_only: bool) -> None:
        if top_only:
            hjson_path = cfg_path / "ip" / ip_type / "data" / f"{ip_type}.hjson"
        else:
            hjson_path = IP_RAW_PATH / ip_type / "data" / f"{ip_type}.hjson"
        if ip_type in ip_attrs:
            ip_attrs[ip_type].instances.append(instance)
        else:
            ip_block = IpBlock.from_path(str(hjson_path), [])
            if ip_type in alias_cfgs:
                ip_block = ip_block.alias_from_raw(
                    False, alias_cfgs[ip_type], f"alias file for {ip_type}")
            ip_attrs[ip_type] = IpAttrs(ip_block=ip_block,
                                        hjson_path=hjson_path,
                                        top_only=top_only,
                                        instances=[instance])

    ip_attrs = {}
    invalid_attr_instances = []
    for instance in topcfg["module"]:
        ip_type = instance["type"]
        if "attr" not in instance:
            handle_instance(top_only=False)
        elif lib.is_top_reggen(instance):
            handle_instance(top_only=True)
        elif lib.is_ipgen(instance):
            continue
        else:
            invalid_attr_instances.append(instance)
    if invalid_attr_instances:
        log.error("The following instances have invalid attributes, "
                  "listed as (instance, attr):"
                  ", ".join("({}, {})".format(inst, inst["attr"])
                            for inst in invalid_attr_instances))
        raise SystemExit(sys.exc_info()[1])
    return ip_attrs


def create_ipgen_ip_block(topname: str, template_name: str, module_name: str,
                          params: ParamsT,
                          alias_cfgs: Dict[str, ConfigT]) -> IpBlock:
    ip_block = ipgen_hjson_render(template_name, topname, params)
    if module_name in alias_cfgs:
        ip_block = ip_block.alias_from_raw(False, alias_cfgs[module_name],
                                           f"alias file for {module_name}")
    return ip_block


def create_ipgen_blocks(topcfg: ConfigT, alias_cfgs: Dict[str, ConfigT],
                        cfg_path: Path, out_path: Path,
                        name_to_block: IpBlocksT) -> Dict[str, IpAttrs]:
    """Create IpAttrs for each ipgen ip type.

    Most importantly, IpAttrs holds the IpBlock. The order in which
    ipgens are processed is important since they have interdependencies.
    All generic Ip blocks should already be created, so the dependencies
    that matter are only amongst ipgens.

    Prior to the generation of each ip we run some of the merge_top
    functions that provide information to such ip, based on all ips
    that have already been generated. This means the merge_top functions
    need to filter out ip blocks that don't yet have an ip block.

    A non-exhaustive list of edges between blocks follows, with a -> b
    meaning a must precede b:
    - racl_ctrl -> all_others
    - flash_ctrl -> pinmux
    - otp_ctrl -> pinmux
    - pinmux -> pwrmgr
    - pwrmgr -> rstmgr
    - all_others -> alert_handler
    - all_others -> rv_plic

    This implies a circular dependency between alert_handler and rv_plic,
    but it is worked out in the last merge_top pass, since at that point
    the total number of alerts and interrupts is set correctly.
    """

    def insert_ip_attrs(module: ConfigT, params: ParamsT):
        template_name = module["template_type"]
        module_name = module["type"]
        log.info(f"Ipgen for {module_name} from template {template_name}")
        hjson_path = (out_path / "ip_autogen" / module_name / "data" /
                      f"{module_name}.hjson")
        ip_block = create_ipgen_ip_block(topname, template_name, module_name,
                                         params, alias_cfgs)
        name_to_block[module_name] = ip_block
        ip_attrs[module_name] = IpAttrs(
            hjson_path=hjson_path,
            ip_block=ip_block,
            top_only=False,
            instances=ipgen_instances[template_name])

    topname = topcfg["name"]
    ip_attrs = {}
    ipgen_instances = defaultdict(list)
    multi_instance_ipgens = []
    for inst in topcfg["module"]:
        if lib.is_ipgen(inst):
            if inst["template_type"] in ipgen_instances:
                multi_instance_ipgens.append(inst)
            else:
                ipgen_instances[inst["template_type"]].append(inst)
    if multi_instance_ipgens:
        raise SystemExit("There are ipgen modules with multiple instances: "
                         f"{multi_instance_ipgens}")

    if "gpio" in ipgen_instances:
        instance = ipgen_instances["gpio"][0]
        insert_ip_attrs(instance, _get_gpio_params(topcfg))
    if "pwm" in ipgen_instances:
        instance = ipgen_instances["pwm"][0]
        insert_ip_attrs(instance, _get_pwm_params(topcfg))
    if "racl_config" in topcfg:
        amend_racl(topcfg, name_to_block, allow_missing_blocks=True)
        assert "racl_ctrl" in ipgen_instances
        instance = ipgen_instances["racl_ctrl"][0]
        insert_ip_attrs(instance, _get_racl_params(topcfg))
    if "clkmgr" in ipgen_instances:
        instance = ipgen_instances["clkmgr"][0]
        insert_ip_attrs(instance, get_clkmgr_params(topcfg))
    if "flash_ctrl" in ipgen_instances:
        instance = ipgen_instances["flash_ctrl"][0]
        insert_ip_attrs(instance, _get_flash_ctrl_params(topcfg))
    if "otp_ctrl" in ipgen_instances:
        instance = ipgen_instances["otp_ctrl"][0]
        insert_ip_attrs(instance, _get_otp_ctrl_params(topcfg, cfg_path))
    if "ac_range_check" in ipgen_instances:
        instance = ipgen_instances["ac_range_check"][0]
        insert_ip_attrs(instance, _get_ac_range_check_params(topcfg))

    if "rv_core_ibex" in ipgen_instances:
        instance = ipgen_instances["rv_core_ibex"][0]
        insert_ip_attrs(instance, _get_rv_core_ibex_params(topcfg))

    # Pinmux depends on flash_ctrl and otp_ctrl
    if "pinmux" in ipgen_instances:
        amend_pinmux_io(topcfg, name_to_block)
        instance = ipgen_instances["pinmux"][0]
        insert_ip_attrs(instance, _get_pinmux_params(topcfg))

    # Pwrmgr depends on pinmux
    # Add pwrmgr after necessary amends
    amend_wkup(topcfg, name_to_block, allow_missing_blocks=True)
    amend_reset_request(topcfg, name_to_block, allow_missing_blocks=True)
    if "pwrmgr" in ipgen_instances:
        insert_ip_attrs(ipgen_instances["pwrmgr"][0],
                        _get_pwrmgr_params(topcfg))
    # Add rstmgr after necessary amends
    amend_resets(topcfg, name_to_block, allow_missing_blocks=True)
    if "rstmgr" in ipgen_instances:
        insert_ip_attrs(ipgen_instances["rstmgr"][0],
                        _get_rstmgr_params(topcfg))
    # Add alert_handler
    amend_alert(topcfg, name_to_block, allow_missing_blocks=True)
    if "alert_handler" in ipgen_instances:
        insert_ip_attrs(ipgen_instances["alert_handler"][0],
                        _get_alert_handler_params(topcfg))
    # Add rv_plic
    amend_interrupt(topcfg, name_to_block, allow_missing_blocks=True)
    if "rv_plic" in ipgen_instances:
        insert_ip_attrs(ipgen_instances["rv_plic"][0],
                        _get_rv_plic_params(topcfg))
    return ip_attrs


def _process_top(
        topcfg: ConfigT, args: argparse.Namespace, cfg_path: Path,
        out_path: Path,
        alias_cfgs: Dict[str,
                         ConfigT]) -> (ConfigT, IpBlocksT, Dict[str, Path]):
    """Generate the full top config file.

    This creates ip_blocks for all ips used by this top config and uses
    them to further populate the top config. It can raise exceptions for
    errors found in the process.
    """
    # Prepare the topcfg.
    extract_clocks(topcfg)
    ip_attrs = create_generic_ip_blocks(topcfg, alias_cfgs, cfg_path, out_path)
    name_to_block = {name: attrs.ip_block for name, attrs in ip_attrs.items()}
    ipgen_attrs = create_ipgen_blocks(topcfg, alias_cfgs, cfg_path, out_path,
                                      name_to_block)
    ip_attrs.update(ipgen_attrs)

    # Connect idle signals to clkmgr. This could be done right after clkmgr
    # generation if all transactional units are generic or are generated
    # prior to clkmgr.
    for attrs in ip_attrs.values():
        for inst in attrs.instances:
            inst_name = inst["name"]
            log.info(f"elaborating {inst_name}")
            elaborate_instance(inst, attrs.ip_block)
    connect_clocks(topcfg, name_to_block)

    # Read the crossbars under the top directory
    hjson_dir = Path(args.topcfg).parent
    xbar_objs = get_hjsonobj_xbars(hjson_dir)

    log.info("Detected crossbars: " + ", ".join(k for k in xbar_objs.keys()))

    topcfg, error = validate_top(topcfg, name_to_block, xbar_objs)
    if error != 0:
        raise SystemExit("Error occured while validating top.hjson")

    completecfg = merge_top(topcfg, name_to_block, xbar_objs)
    name_to_hjson: Dict[str,
                        Path] = {k: v.hjson_path
                                 for k, v in ip_attrs.items()}
    # rv_plic is generated after alert_handler so the alert_handler ip_block
    # needs to be updated because rv_plic alerts were not visible when the
    # alert_handler ip_block was created.
    alert_handlers = find_modules(topcfg["module"], "alert_handler", True)
    for alert_handler in alert_handlers:
        template_name = alert_handler["template_type"]
        module_name = alert_handler["type"]
        params = _get_alert_handler_params(topcfg)
        name_to_block[module_name] = create_ipgen_ip_block(
            topcfg["name"], template_name, module_name, params, alias_cfgs)
    return completecfg, name_to_block, name_to_hjson


def complete_topcfg(topcfg: ConfigT, name_to_block: IpBlocksT) -> None:
    commit_alert_modules(topcfg, name_to_block)
    commit_interrupt_modules(topcfg, name_to_block)
    commit_outgoing_alert_modules(topcfg, name_to_block)
    commit_outgoing_interrupt_modules(topcfg, name_to_block)


def generate_full_ipgens(args: argparse.Namespace, topcfg: ConfigT,
                         name_to_block: Dict[str, ConfigT],
                         alias_cfgs: Dict[str, ConfigT], cfg_path: Path,
                         out_path: Path) -> None:

    # TODO, there are no interdependencies between ips so do them in any
    # order, which means could just iterate over all in the topcfg.

    def generate_modules(template_type: str,
                         generate_module: Callable[[Dict, Dict, Path], None],
                         single_instance: bool) -> None:
        modules = ipgens_by_template_type[template_type]
        if len(modules) > 1 and single_instance:
            raise SystemExit(
                f"Cannot have more than one {template_type} per top")
        for module in modules:
            generate_module(topcfg, module, out_path)

    ipgens_by_template_type = defaultdict(list)
    for m in topcfg["module"]:
        if m.get("attr") == "ipgen":
            ipgens_by_template_type[m["template_type"]].append(m)

    generate_modules("clkmgr", generate_clkmgr, single_instance=True)
    generate_modules("flash_ctrl", generate_flash, single_instance=False)
    if not args.no_plic and \
       not args.alert_handler_only and \
       not args.xbar_only:
        generate_modules("rv_plic", generate_plic, single_instance=True)
    if args.plic_only:
        sys.exit()

    # Generate Alert Handler if there is an instance
    if not args.xbar_only:
        generate_modules("alert_handler",
                         generate_alert_handler,
                         single_instance=True)
    if args.alert_handler_only:
        sys.exit()

    # Generate outgoing alerts
    generate_outgoing_alerts(topcfg, out_path)

    # Generate outgoing interrupts
    generate_outgoing_interrupts(topcfg, out_path)

    # Generate otp_ctrl if there is an instance. It needs an extra argument
    # than the other ipgens, so it cannot call generate_modules.
    modules = ipgens_by_template_type["otp_ctrl"]
    if len(modules) > 1:
        raise SystemExit("Cannot have more than one otp_ctrl per top")
    for module in modules:
        generate_otp_ctrl(topcfg, module, cfg_path, out_path)

    # Generate Pinmux
    generate_modules("pinmux", generate_pinmux, single_instance=True)

    # Generate Pwrmgr if there is an instance
    generate_modules("pwrmgr", generate_pwrmgr, single_instance=True)

    # Generate rstmgr if there is an instance
    generate_modules("rstmgr", generate_rstmgr, single_instance=True)

    # Generate gpio if there is an instance
    generate_modules("gpio", generate_gpio, single_instance=True)

    # Generate rv_core_ibex if there is an instance
    generate_modules("rv_core_ibex",
                     generate_rv_core_ibex,
                     single_instance=True)
    # Generate pwm if there is an instance
    generate_modules("pwm", generate_pwm, single_instance=True)

    # Generate ac_range_check
    generate_modules("ac_range_check",
                     generate_ac_range_check,
                     single_instance=True)

    # Generate RACL collateral
    if "racl_config" in topcfg:
        generate_modules("racl_ctrl", generate_racl, single_instance=True)


def _check_countermeasures(completecfg: ConfigT, name_to_block: IpBlocksT,
                           name_to_hjson: Dict[str, Path]) -> bool:
    success = True
    for name, hjson_path in name_to_hjson.items():
        log.debug("name %s, hjson %s", name, hjson_path)
        sv_files = (hjson_path.parents[1] / 'rtl').glob('*.sv')
        rtl_names = CounterMeasure.search_rtl_files(sv_files)
        log.debug("Checking countermeasures for %s.", name)
        success &= name_to_block[name].check_cm_annotations(
            rtl_names, hjson_path.name)
        success &= name_to_block[name].check_regwens()
    if success:
        log.info("All Hjson declared countermeasures are implemented in RTL.")
    else:
        log.error("Countermeasure checks failed.")
    return success


def dump_completecfg(cfg: ConfigT, out_path: Path) -> None:
    topname = cfg["name"]
    top_name = f"top_{topname}"
    cfg_dir = out_path / "data/autogen"
    cfg_dir.mkdir(parents=True, exist_ok=True)
    genhjson_path = cfg_dir / f"{top_name}.gen.hjson"

    # Header for HJSON
    gencmd = """//
// util/topgen.py -t hw/{top_name}/data/{top_name}.hjson \\
//                -o hw/{top_name}/ \\
//                --rnd_cnst_seed {seed}
""".format(top_name=top_name, seed=cfg["rnd_cnst_seed"])

    genhjson_path.write_text(genhdr + gencmd +
                             hjson.dumps(cfg, for_json=True, default=vars) +
                             '\n')


def main():
    parser = argparse.ArgumentParser(prog="topgen")
    parser.add_argument("--topcfg",
                        "-t",
                        required=True,
                        help="`top_{name}.hjson` file.")
    parser.add_argument(
        "--outdir",
        "-o",
        help="""Target TOP directory.
             Module is created under rtl/. (default: dir(topcfg)/..)
             """)  # yapf: disable
    parser.add_argument("--hjson-path",
                        help="""
          If defined, topgen uses supplied path to search for ip hjson.
          This applies only to ip's with the `reggen_only` attribute.
          If an hjson is located both in the conventional path and the alternate
          path, the alternate path has priority.
        """)
    parser.add_argument("--verbose", "-v", action="store_true", help="Verbose")
    parser.add_argument(
        '--version-stamp',
        type=Path,
        default=None,
        help=
        'If version stamping, the location of workspace version stamp file.')

    # Generator options: 'no' series. Cannot combine with 'only' series.
    parser.add_argument(
        "--no-top",
        action="store_true",
        help="If defined, topgen doesn't generate top_{name} RTLs.")
    parser.add_argument(
        "--no-xbar",
        action="store_true",
        help="If defined, topgen doesn't generate crossbar RTLs.")
    parser.add_argument(
        "--no-plic",
        action="store_true",
        help="If defined, topgen doesn't generate the interrup controller RTLs."
    )
    parser.add_argument("--no-rust",
                        action="store_true",
                        help="If defined, topgen doesn't generate Rust code.")

    # Generator options: 'only' series. cannot combined with 'no' series
    parser.add_argument(
        "--top-only",
        action="store_true",
        help="If defined, the tool generates top RTL only")  # yapf:disable
    parser.add_argument("--check-cm",
                        action="store_true",
                        help='''
        Check countermeasures.

        Check countermeasures of all modules in the top config. All
        countermeasures declared in the module's hjson file should
        be implemented in the RTL, and the RTL should only
        contain countermeasures declared there.
        ''')
    parser.add_argument(
        "--xbar-only",
        action="store_true",
        help="If defined, the tool generates crossbar RTLs only")
    parser.add_argument(
        "--plic-only",
        action="store_true",
        help="If defined, the tool generates RV_PLIC RTL and Hjson only")
    parser.add_argument(
        "--alert-handler-only",
        action="store_true",
        help="If defined, the tool generates alert handler hjson only")
    parser.add_argument(
        "--rust-only",
        action="store_true",
        help="If defined, the tool generates top Rust code only")
    # Generator options: generate dv ral model
    parser.add_argument(
        "--top_ral",
        "-r",
        default=False,
        action="store_true",
        help="If set, the tool generates top level RAL model for DV")
    parser.add_argument("--alias-files",
                        nargs="+",
                        type=Path,
                        default=None,
                        help="""
          If defined, topgen uses supplied alias hjson file(s) to override the
          generic register definitions when building the RAL model. This
          argument is only relevant in conjunction with the `--top_ral` switch.
        """)
    parser.add_argument(
        "--dv-base-names",
        nargs="+",
        help="Names or prefix for the DV register classes from which "
        "the register models are derived.")
    # Generator options for compile time random netlist constants
    parser.add_argument(
        "--rnd_cnst_seed",
        type=int,
        metavar="<seed>",
        help="Custom seed for RNG to compute netlist constants.")
    # Miscellaneous: only return the list of blocks and exit.
    parser.add_argument("--get_blocks",
                        default=False,
                        action="store_true",
                        help="Only return the list of blocks and exit.")

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

    if args.no_rust and args.rust_only:
        log.error(
            "'no' series options cannot be used with 'only' series options")
        raise SystemExit(sys.exc_info()[1])

    # Don't print warnings when querying the list of blocks.
    log_level = (log.ERROR if args.get_blocks or args.check_cm else
                 log.DEBUG if args.verbose else None)

    log.basicConfig(format="%(filename)s:%(lineno)d: %(levelname)s: %(message)s",
                    level=log_level)

    if not args.outdir:
        outdir = Path(args.topcfg).parents[1]
        log.info("TOP directory not given. Using %s", (outdir))
    elif not Path(args.outdir).is_dir():
        log.error("'--outdir' should point to writable directory")
        raise SystemExit(sys.exc_info()[1])
    else:
        outdir = Path(args.outdir)

    if args.hjson_path is not None:
        log.info(f"Alternate hjson path is {args.hjson_path}")

    out_path = Path(outdir)
    cfg_path = Path(args.topcfg).parents[1]

    topcfg = load_cfg(args.topcfg)

    # Add domain information to each module's reset_connections
    amend_reset_connections(topcfg)

    # Read external alert mappings for all available alert handlers and inject
    # them to the alert handler's module definition.
    # TODO: make this part of amend_alert and amend_interrupt
    if 'incoming_alert' not in topcfg:
        topcfg['incoming_alert'] = {}
    if 'incoming_interrupt' not in topcfg:
        topcfg['incoming_interrupt'] = OrderedDict()

    for m in topcfg['module']:
        if m.get('template_type') == 'alert_handler':
            for alert_mappings_path in m.get('incoming_alert', []):
                mapping = load_cfg(
                    Path(args.topcfg).parent / alert_mappings_path)
                for alert_group, alerts in mapping.items():
                    topcfg['incoming_alert'][alert_group] = alerts
        elif m.get('template_type') == 'rv_plic':
            for irq_mappings_path in m.get('incoming_interrupt', []):
                irq_mapping = load_cfg(
                    Path(args.topcfg).parent / irq_mappings_path)
                for irq_group, irqs in irq_mapping.items():
                    topcfg['incoming_interrupt'][irq_group] = irqs

    # Extract version stamp from file
    version_stamp = version_file.VersionInformation(args.version_stamp)

    # Determine the seed for RNG for compile-time netlist constants.
    # If specified, override the seed for random netlist constant computation.
    if args.rnd_cnst_seed:
        log.warning("Commandline override of rnd_cnst_seed with {}.".format(
            args.rnd_cnst_seed))
        topcfg["rnd_cnst_seed"] = args.rnd_cnst_seed
    # Otherwise we make sure a seed exists in the HJSON config file.
    elif "rnd_cnst_seed" not in topcfg:
        log.error('Seed "rnd_cnst_seed" not found in configuration HJSON.')
        exit(1)

    # The generation of ipgen modules needs to be carefully orchestrated to
    # avoid performing multiple passes when creating the complete top
    # configuration. Please refer to the description in util/topgen/README.md.
    #
    # This performs mutiple passes until the complete top configuration
    # doesn't change.
    #
    # This fix is related to #2083
    maximum_passes = 3

    # topgen generates IP blocks and associated Hjson configuration in multiple
    # steps. In each step, the ipgen peripheral's IP Hjson configuration is
    # regenerated from the updated top configuration, which can induce further
    # changes to the toplevel configuration.
    #
    # To generate the chip-level RAL we need to run the full generation step,
    # but ultimately only care about the toplevel configuration (a single Hjson
    # file). Since we don't have a better way at the moment, we dump all output
    # into a temporary directory, and delete it after the fact, retaining only
    # the toplevel configuration.
    if args.top_ral:
        out_path_gen = Path(tempfile.mkdtemp())
    else:
        out_path_gen = out_path

    alias_cfgs: Dict[str, ConfigT] = {}
    if args.alias_files:
        for alias in args.alias_files:
            alias_cfg = load_cfg(alias)
            if 'alias_target' not in alias_cfg:
                raise ValueError('Missing alias_target key '
                                 'in alias file {}.'.format(alias))
            alias_target = alias_cfg['alias_target'].lower()
            if alias_target in alias_cfgs:
                raise ValueError(f"Multiple alias targets for {alias_target}")
            alias_cfgs[alias_target] = alias_cfg

    topname = topcfg["name"]
    cfg_copy = deepcopy(topcfg)
    cfg_last_dump = None
    for pass_idx in range(maximum_passes):
        log.info("Generation pass {}".format(pass_idx + 1))
        # Use the same seed for each pass to have stable random constants.
        secure_prng.reseed(topcfg["rnd_cnst_seed"])
        # Insert the config file path of the HJSON to allow parsing files
        # relative the config directory
        cfg_copy["cfg_path"] = Path(args.topcfg).parent
        completecfg, name_to_block, name_to_hjson = _process_top(
            cfg_copy, args, cfg_path, out_path_gen, alias_cfgs)
        # Delete config path before dumping, not needed
        del completecfg["cfg_path"]
        cfg_dump = hjson.dumps(completecfg, for_json=True, default=vars)
        if pass_idx > 0 and cfg_dump == cfg_last_dump:
            log.info("process_top converged after {} passes".format(pass_idx +
                                                                    1))
            break
        else:
            cfg_last_dump = cfg_dump
        cfg_copy = completecfg
    else:
        log.error("Too many process_top passes without convergence")
        raise SystemExit(sys.exc_info()[1])

    complete_topcfg(completecfg, name_to_block)
    create_alert_lpgs(completecfg, name_to_block)

    configure_xbars(completecfg)

    # All IPs are generated. Connect phase now
    # Find {memory, module} <-> {xbar} connections first.
    im.autoconnect(completecfg, name_to_block)

    # Generic Inter-module connection
    im.elab_intermodule(completecfg)

    # Dump the complete top config
    dump_completecfg(completecfg, out_path)

    topname = topcfg["name"]
    top_name = f"top_{topname}"

    # Create the chip-level RAL only
    if args.top_ral:
        # See above: we only need `completecfg` and `name_to_block`, not all
        # the other files (e.g. RTL files) generated through topgen.
        shutil.rmtree(out_path_gen, ignore_errors=True)

        exit_code = generate_top_ral(topname, completecfg, name_to_block,
                                     args.dv_base_names, out_path)
        sys.exit(exit_code)

    # Generate top only modules
    # These modules are not ipgen, but are not in hw/ip
    top_only_ips = {
        m["type"]
        for m in completecfg["module"] if lib.is_top_reggen(m)
    }
    generate_top_only(top_only_ips, out_path, top_name, args.hjson_path)
    generate_full_ipgens(args, completecfg, name_to_block, alias_cfgs,
                         cfg_path, out_path)

    if args.get_blocks:
        print("\n".join(name_to_block.keys()))
        sys.exit(0)

    # Generate xbars
    if not args.no_xbar or args.xbar_only:
        generate_xbars(completecfg, out_path)

    # Generate Rust toplevel definitions
    if not args.no_rust:
        generate_rust(topname, completecfg, name_to_block, out_path.resolve(),
                      version_stamp, SRCTREE_TOP, TOPGEN_TEMPLATE_PATH)
        if args.rust_only:
            sys.exit(0)

    # Check countermeasures for all blocks.
    if args.check_cm:
        # Change verbosity to log.INFO to see an okay confirmation message:
        # the log level is set to log.ERROR upon start to avoid the chatter
        # of the regular topgen elaboration.
        log_level = log.DEBUG if args.verbose else log.INFO
        log.basicConfig(format="%(levelname)s: %(message)s",
                        level=log_level,
                        force=True)

        okay = _check_countermeasures(completecfg, name_to_block,
                                      name_to_hjson)
        sys.exit(0 if okay else 1)

    if not args.no_top or args.top_only:

        def render_template(template_path: str, rendered_path: Path,
                            **other_info):
            template_contents = generate_top(completecfg, name_to_block,
                                             str(template_path), **other_info)

            rendered_path.parent.mkdir(exist_ok=True, parents=True)
            with rendered_path.open(mode="w", encoding="UTF-8") as fout:
                fout.write(template_contents)

        # Header for SV files
        gencmd_sv = warnhdr + """//
// util/topgen.py -t hw/{top_name}/data/{top_name}.hjson \\
//                -o hw/{top_name}/ \\
//                --rnd_cnst_seed \\
//                {seed}
""".format(top_name=top_name, seed=completecfg["rnd_cnst_seed"])

        # Top and chiplevel templates are top-specific
        top_template_path = SRCTREE_TOP / "hw" / top_name / "templates"

        # SystemVerilog Top:
        # "toplevel.sv.tpl" -> "rtl/autogen/{top_name}.sv"
        render_template(top_template_path / "toplevel.sv.tpl",
                        out_path / "rtl" / "autogen" / f"{top_name}.sv",
                        gencmd=gencmd_sv)

        # Multiple chip-levels (ASIC, FPGA, Verilator, etc)
        for target in completecfg["targets"]:
            target_name = target["name"]
            render_template(top_template_path / "chiplevel.sv.tpl",
                            out_path /
                            f"rtl/autogen/chip_{topname}_{target_name}.sv",
                            gencmd=gencmd_sv,
                            target=target)

        # compile-time random netlist constants
        render_template(TOPGEN_TEMPLATE_PATH / "toplevel_rnd_cnst_pkg.sv.tpl",
                        out_path / f"rtl/autogen/{top_name}_rnd_cnst_pkg.sv",
                        gencmd=gencmd_sv)

        racl_config = completecfg.get('racl', DEFAULT_RACL_CONFIG)
        render_template(TOPGEN_TEMPLATE_PATH / 'top_racl_pkg.sv.tpl',
                        out_path / 'rtl' / 'autogen' / 'top_racl_pkg.sv',
                        gencmd=gencmd_sv,
                        topcfg=completecfg,
                        racl_config=racl_config)
        render_template(TOPGEN_TEMPLATE_PATH / 'toplevel_racl_pkg.sv.tpl',
                        out_path / 'rtl' / 'autogen' /
                        f'top_{topname}_racl_pkg.sv',
                        gencmd=gencmd_sv,
                        topcfg=completecfg,
                        racl_config=racl_config)

        # The C / SV file needs some complex information, so we initialize this
        # object to store it.
        c_helper = TopGenCTest(completecfg, name_to_block)

        # Since SW does not use FuseSoC and instead expects those files always
        # to be in hw/top_{topname}/sw/autogen, we currently create these files
        # twice:
        # - Once under out_path/sw/autogen
        # - Once under hw/top_{topname}/sw/autogen
        root_paths = [out_path.resolve(), SRCTREE_TOP]
        out_paths = [
            out_path.resolve(), (SRCTREE_TOP / "hw" / top_name).resolve()
        ]

        # C Header + C File + Clang-format file
        gencmd_c = warnhdr + GENCMD.format(top_name=top_name)
        gencmd_bzl = gencmd_c.replace("//", "#")

        for addr_space in topcfg['addr_spaces']:
            addr_space_suffix = lib.get_addr_space_suffix(addr_space)

            # "toplevel_pkg.sv.tpl" -> "rtl/autogen/{top_name}{addr_space_suffix}_pkg.sv"
            render_template(TOPGEN_TEMPLATE_PATH / "toplevel_pkg.sv.tpl",
                            out_path / "rtl" / "autogen" /
                            f"{top_name}{addr_space_suffix}_pkg.sv",
                            helper=c_helper,
                            addr_space=addr_space,
                            gencmd=gencmd_sv)

            for idx, path in enumerate(out_paths):

                # "clang-format" -> "sw/autogen/.clang-format"
                cformat_tplpath = TOPGEN_TEMPLATE_PATH / "clang-format"
                cformat_dir = path / "sw" / "autogen"
                cformat_dir.mkdir(parents=True, exist_ok=True)
                cformat_path = cformat_dir / ".clang-format"
                cformat_path.write_text(cformat_tplpath.read_text())

                # Save the header macro prefix into `c_helper`
                rel_header_dir = cformat_dir.relative_to(root_paths[idx])
                c_helper.header_macro_prefix = (
                    "OPENTITAN_" +
                    str(rel_header_dir).replace("/", "_").upper())

                # "toplevel.h.tpl" -> "sw/autogen/{top_name}.h"
                cheader_path = cformat_dir / f"{top_name}{addr_space_suffix}.h"
                render_template(TOPGEN_TEMPLATE_PATH / "toplevel.h.tpl",
                                cheader_path,
                                addr_space=addr_space['name'],
                                helper=c_helper,
                                gencmd=gencmd_c)

                # Save the relative header path into `c_helper`
                rel_header_path = cheader_path.relative_to(root_paths[idx])
                c_helper.header_path = str(rel_header_path)

                # "toplevel.c.tpl" -> "sw/autogen/{top_name}{addr_space_suffix}.c"
                render_template(TOPGEN_TEMPLATE_PATH / "toplevel.c.tpl",
                                cformat_dir /
                                f"{top_name}{addr_space_suffix}.c",
                                helper=c_helper,
                                addr_space=addr_space['name'],
                                gencmd=gencmd_c)

                # "toplevel_memory.h.tpl" -> "sw/autogen/{top_name}{addr_space_suffix}_memory.h"
                memory_cheader_path = cformat_dir / f"{top_name}{addr_space_suffix}_memory.h"
                render_template(TOPGEN_TEMPLATE_PATH / "toplevel_memory.h.tpl",
                                memory_cheader_path,
                                addr_space=addr_space['name'],
                                helper=c_helper,
                                gencmd=gencmd_c)

                # "toplevel_BUILD.h.tpl" -> "sw/autogen/BUILD"
                memory_cheader_path = cformat_dir / "BUILD"
                render_template(TOPGEN_TEMPLATE_PATH / "toplevel_BUILD.tpl",
                                memory_cheader_path,
                                helper=c_helper,
                                gencmd=gencmd_bzl)

                # "data_BUILD.h.tpl" -> "data/autogen/BUILD"
                render_template(TOPGEN_TEMPLATE_PATH / "data_BUILD.tpl",
                                path / "data" / "autogen" / "BUILD",
                                gencmd=gencmd_bzl)
                # "data_defs.bzl.tpl" -> "data/autogen/defs.bzl"
                render_template(TOPGEN_TEMPLATE_PATH / "data_defs.bzl.tpl",
                                path / "data" / "autogen" / "defs.bzl",
                                gencmd=gencmd_bzl)

        for idx, path in enumerate(out_paths):
            cformat_dir = path / "sw" / "autogen"
            c_helper.header_macro_prefix = (
                "OPENTITAN_" + str(rel_header_dir).replace("/", "_").upper())

            # "toplevel_memory.ld.tpl" ->
            #   "sw/autogen/{top_name}{addr_space_suffix}_memory.ld"
            render_template(
                TOPGEN_TEMPLATE_PATH / "toplevel_memory.ld.tpl",
                cformat_dir / f"{top_name}_memory.ld",
                addr_space='hart',  # TODO: Don't hard-code
                helper=c_helper,
                gencmd=gencmd_c)

            # Auto-generate tests in "sw/device/tests/autogen" area.
            outfile = cformat_dir / "tests" / "BUILD"
            render_template(
                TOPGEN_TEMPLATE_PATH / "BUILD.tpl",
                outfile,
                helper=c_helper,
                addr_space='hart',  # TODO: Don't hard-code
                gencmd=gencmd_bzl)

            outfile = cformat_dir / "tests" / "plic_all_irqs_test.c"
            render_template(
                TOPGEN_TEMPLATE_PATH / "plic_all_irqs_test.c.tpl",
                outfile,
                helper=c_helper,
                addr_space='hart',  # TODO: Don't hard-code
                gencmd=gencmd_c)

            # Render alert tests only if there is really an alert handler
            if lib.find_module(completecfg['module'], 'alert_handler'):
                outfile = cformat_dir / "tests" / "alert_test.c"
                render_template(
                    TOPGEN_TEMPLATE_PATH / "alert_test.c.tpl",
                    outfile,
                    helper=c_helper,
                    addr_space='hart',  # TODO: Don't hard-code
                    gencmd=gencmd_c)

        # generate chip level xbar and alert_handler TB
        tb_files = [
            "xbar_env_pkg__params.sv", "tb__xbar_connect.sv",
            "tb__alert_handler_connect.sv", "xbar_tgl_excl.cfg",
            "rstmgr_tgl_excl.cfg"
        ]
        for fname in tb_files:
            tpl_fname = "%s.tpl" % (fname)
            xbar_chip_data_path = TOPGEN_TEMPLATE_PATH / tpl_fname
            template_contents = generate_top(completecfg,
                                             name_to_block,
                                             str(xbar_chip_data_path),
                                             gencmd=gencmd_sv)

            rendered_dir = out_path / "dv/autogen"
            rendered_dir.mkdir(parents=True, exist_ok=True)
            rendered_path = rendered_dir / fname

            with rendered_path.open(mode="w", encoding="UTF-8") as fout:
                fout.write(template_contents)

        # generate parameters for chip-level environment package
        tpl_fname = "chip_env_pkg__params.sv.tpl"
        alert_handler_chip_data_path = TOPGEN_TEMPLATE_PATH / tpl_fname
        template_contents = generate_top(completecfg, name_to_block,
                                         str(alert_handler_chip_data_path))

        rendered_dir = out_path / "dv/env/autogen"
        rendered_dir.mkdir(parents=True, exist_ok=True)
        rendered_path = rendered_dir / "chip_env_pkg__params.sv"

        with rendered_path.open(mode="w", encoding="UTF-8") as fout:
            fout.write(template_contents)

        # generate documentation for toplevel
        gen_top_docs(completecfg, c_helper, out_path)


if __name__ == "__main__":
    main()
