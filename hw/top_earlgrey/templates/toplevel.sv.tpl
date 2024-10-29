// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import re
import topgen.lib as lib
from topgen.clocks import Clocks
from topgen.resets import Resets

num_mio_inputs = top['pinmux']['io_counts']['muxed']['inouts'] + \
                 top['pinmux']['io_counts']['muxed']['inputs']
num_mio_outputs = top['pinmux']['io_counts']['muxed']['inouts'] + \
                  top['pinmux']['io_counts']['muxed']['outputs']
num_mio_pads = top['pinmux']['io_counts']['muxed']['pads']

num_dio_inputs = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                 top['pinmux']['io_counts']['dedicated']['inputs']
num_dio_outputs = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                  top['pinmux']['io_counts']['dedicated']['outputs']
num_dio_total = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                top['pinmux']['io_counts']['dedicated']['inputs'] + \
                top['pinmux']['io_counts']['dedicated']['outputs']

num_im = sum([x["width"] if "width" in x else 1 for x in top["inter_signal"]["external"]])

max_sigwidth = max([x["width"] if "width" in x else 1 for x in top["pinmux"]["ios"]])
max_sigwidth = len("{}".format(max_sigwidth))

cpu_clk = top['clocks'].hier_paths['top'] + "clk_proc_main"

unused_resets = lib.get_unused_resets(top)
unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(top["inter_signal"]["definitions"])

has_toplevel_rom = False
for m in top['memory']:
  if m['type'] == 'rom':
    has_toplevel_rom = True

last_modidx_with_params = lib.idx_of_last_module_with_params(top)

%>\
module top_${top["name"]} #(
  // Manually defined parameters
% if not lib.num_rom_ctrl(top["module"]):
  parameter BootRomInitFile = "",
% endif

  // Auto-inferred parameters
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
  // parameters for ${m['name']}
  % for p_exp in [p for p in m["param_list"] if p.get("expose") == "true" ]:
<%
    p_type = p_exp.get('type')
    p_type_word = p_type + ' ' if p_type else ''

    p_lhs = f'{p_type_word}{p_exp["name_top"]}'

    if 'unpacked_dimensions' in p_exp:
      p_lhs += p_exp['unpacked_dimensions']

    p_rhs = p_exp['default']

    params_follow = not loop.last or loop.parent.index < last_modidx_with_params
    comma_char = ',' if params_follow else ''
%>\
    % if 12 + len(p_lhs) + 3 + len(p_rhs) + 1 < 100:
  parameter ${p_lhs} = ${p_rhs}${comma_char}
    % else:
  parameter ${p_lhs} =
      ${p_rhs}${comma_char}
    % endif
  % endfor
% endfor
) (
% if num_mio_pads != 0:
  // Multiplexed I/O
  input        ${lib.bitarray(num_mio_pads, max_sigwidth)} mio_in_i,
  output logic ${lib.bitarray(num_mio_pads, max_sigwidth)} mio_out_o,
  output logic ${lib.bitarray(num_mio_pads, max_sigwidth)} mio_oe_o,
% endif
% if num_dio_total != 0:
  // Dedicated I/O
  input        ${lib.bitarray(num_dio_total, max_sigwidth)} dio_in_i,
  output logic ${lib.bitarray(num_dio_total, max_sigwidth)} dio_out_o,
  output logic ${lib.bitarray(num_dio_total, max_sigwidth)} dio_oe_o,
% endif

% if "pinmux" in top:
  // pad attributes to padring
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr_o,
  output prim_pad_wrapper_pkg::pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr_o,
% endif

% if num_im != 0:

  // Inter-module Signal External type
  % for sig in top["inter_signal"]["external"]:
  ${lib.get_direction(sig)} ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]},
  % endfor

% endif

  // All externally supplied clocks
  % for clk in top['clocks'].typed_clocks().ast_clks:
  input ${clk},
  % endfor

  // All clocks forwarded to ast
  output clkmgr_pkg::clkmgr_out_t clks_ast_o,
  output rstmgr_pkg::rstmgr_out_t rsts_ast_o,

  input                      scan_rst_ni, // reset used for test mode
  input                      scan_en_i,
  input prim_mubi_pkg::mubi4_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  import tlul_pkg::*;
  import top_pkg::*;
  import tl_main_pkg::*;
  import top_${top["name"]}_pkg::*;
  // Compile-time random constants
  import top_${top["name"]}_rnd_cnst_pkg::*;

  // Signals
  logic [${num_mio_inputs - 1}:0] mio_p2d;
  logic [${num_mio_outputs - 1}:0] mio_d2p;
  logic [${num_mio_outputs - 1}:0] mio_en_d2p;
  logic [${num_dio_total - 1}:0] dio_p2d;
  logic [${num_dio_total - 1}:0] dio_d2p;
  logic [${num_dio_total - 1}:0] dio_en_d2p;
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
<%
  block = name_to_block[m['type']]
  inouts, inputs, outputs = block.xputs
%>\
  // ${m["name"]}
  % for p_in in inputs + inouts:
  logic ${lib.bitarray(p_in.bits.width(), max_sigwidth)} cio_${m["name"]}_${p_in.name}_p2d;
  % endfor
  % for p_out in outputs + inouts:
  logic ${lib.bitarray(p_out.bits.width(), max_sigwidth)} cio_${m["name"]}_${p_out.name}_d2p;
  logic ${lib.bitarray(p_out.bits.width(), max_sigwidth)} cio_${m["name"]}_${p_out.name}_en_d2p;
  % endfor
% endfor


<%
  # Interrupt source 0 is tied to 0 to conform RISC-V PLIC spec.
  # So, total number of interrupts are the number of entries in the list + 1
  interrupt_num = sum([x["width"] if "width" in x else 1 for x in top["interrupt"]]) + 1
%>\
  logic [${interrupt_num-1}:0]  intr_vector;
  // Interrupt source list
% for m in top["module"]:
<%
  block = name_to_block[m['type']]
%>\
    % if not lib.is_inst(m):
<% continue %>
    % endif
    % for intr in block.interrupts:
        % if intr.bits.width() != 1:
  logic [${intr.bits.width()-1}:0] intr_${m["name"]}_${intr.name};
        % else:
  logic intr_${m["name"]}_${intr.name};
        % endif
    % endfor
% endfor

  // Alert list
  prim_alert_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_alert_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;

% if not top["alert"]:
  for (genvar k = 0; k < alert_pkg::NAlerts; k++) begin : gen_alert_tie_off
    // tie off if no alerts present in the system
    assign alert_tx[k].alert_p = 1'b0;
    assign alert_tx[k].alert_n = 1'b1;
  end
% endif

## Inter-module Definitions
% if len(top["inter_signal"]["definitions"]) >= 1:
  // define inter-module signals
% endif
% for sig in top["inter_signal"]["definitions"]:
  ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]};
% endfor

## Mixed connection to port
## Index greater than 0 means a port is assigned to an inter-module array
## whereas an index of 0 means a port is directly driven by a module
  // define mixed connection to port
% for port in top['inter_signal']['external']:
  % if port['conn_type'] and port['index'] > 0:
    % if port['direction'] == 'in':
  assign ${port['netname']}[${port['index']}] = ${port['signame']};
    % else:
  assign ${port['signame']} = ${port['netname']}[${port['index']}];
    % endif
  % elif port['conn_type']:
    % if port['direction'] == 'in':
  assign ${port['netname']} = ${port['signame']};
    % else:
  assign ${port['signame']} = ${port['netname']};
    % endif
  % endif
% endfor

## Partial inter-module definition tie-off
  // define partial inter-module tie-off
% for sig in unused_im_defs:
  % for idx in range(sig['end_idx'], sig['width']):
  ${lib.im_defname(sig)} unused_${sig["signame"]}${idx};
  % endfor
% endfor

  // assign partial inter-module tie-off
% for sig in unused_im_defs:
  % for idx in range(sig['end_idx'], sig['width']):
  assign unused_${sig["signame"]}${idx} = ${sig["signame"]}[${idx}];
  % endfor
% endfor
% for sig in undriven_im_defs:
  % for idx in range(sig['end_idx'], sig['width']):
  assign ${sig["signame"]}[${idx}] = ${sig["default"]};
  % endfor
% endfor

## Inter-module signal collection

% for m in top["module"]:
  % if m["type"] == "otp_ctrl":
  // OTP HW_CFG* Broadcast signals.
  // TODO(#6713): The actual struct breakout and mapping currently needs to
  // be performed by hand.
  assign csrng_otp_en_csrng_sw_app_read =
      otp_ctrl_otp_broadcast.hw_cfg1_data.en_csrng_sw_app_read;
  assign sram_ctrl_main_otp_en_sram_ifetch =
      otp_ctrl_otp_broadcast.hw_cfg1_data.en_sram_ifetch;
  assign rv_dm_otp_dis_rv_dm_late_debug =
      otp_ctrl_otp_broadcast.hw_cfg1_data.dis_rv_dm_late_debug;
  assign lc_ctrl_otp_device_id =
      otp_ctrl_otp_broadcast.hw_cfg0_data.device_id;
  assign lc_ctrl_otp_manuf_state =
      otp_ctrl_otp_broadcast.hw_cfg0_data.manuf_state;
  assign keymgr_otp_device_id =
      otp_ctrl_otp_broadcast.hw_cfg0_data.device_id;

  logic unused_otp_broadcast_bits;
  assign unused_otp_broadcast_bits = ^{
    otp_ctrl_otp_broadcast.valid,
    otp_ctrl_otp_broadcast.hw_cfg0_data.hw_cfg0_digest,
    otp_ctrl_otp_broadcast.hw_cfg1_data.hw_cfg1_digest,
    otp_ctrl_otp_broadcast.hw_cfg1_data.unallocated
  };
  % endif
% endfor

  // See #7978 This below is a hack.
  // This is because ast is a comportable-like module that sits outside
  // of top_${top["name"]}'s boundary.
  assign clks_ast_o = ${top['clocks'].hier_paths['top'][:-1]};
  assign rsts_ast_o = ${top['resets'].hier_paths['top'][:-1]};

  // ibex specific assignments
  // TODO: This should be further automated in the future.
  assign rv_core_ibex_irq_timer = intr_rv_timer_timer_expired_hart0_timer0;
  assign rv_core_ibex_hart_id = '0;

  ## Not all top levels have a rom controller.
  ## For those that do not, reference the ROM directly.
<% num_rom_ctrl = lib.num_rom_ctrl(top["module"]) %>\
% if num_rom_ctrl == 1:
  assign rv_core_ibex_boot_addr = ADDR_SPACE_ROM_CTRL__ROM;
% elif num_rom_ctrl > 1:
  assign rv_core_ibex_boot_addr = ADDR_SPACE_ROM_CTRL0__ROM;
% else:
  ## Not all top levels have
  assign rv_core_ibex_boot_addr = ADDR_SPACE_ROM;
% endif

  ## Not all top levels have a lifecycle controller.
  ## For those that do not, always enable ibex.
% if not lib.is_lc_ctrl(top["module"]):
  assign rv_core_ibex_lc_cpu_en = lc_ctrl_pkg::On;
% endif

  // Struct breakout module tool-inserted DFT TAP signals
  pinmux_jtag_breakout u_dft_tap_breakout (
    .req_i    (pinmux_aon_dft_jtag_req),
    .rsp_o    (pinmux_aon_dft_jtag_rsp),
    .tck_o    (),
    .trst_no  (),
    .tms_o    (),
    .tdi_o    (),
    .tdo_i    (1'b0),
    .tdo_oe_i (1'b0)
  );

  // Wire up alert handler LPGs
  prim_mubi_pkg::mubi4_t [alert_pkg::NLpg-1:0] lpg_cg_en;
  prim_mubi_pkg::mubi4_t [alert_pkg::NLpg-1:0] lpg_rst_en;

<%
# get all known typed clocks and add them to a dict
# this is used to generate the tie-off assignments further below
clocks = top['clocks']
assert isinstance(clocks, Clocks)
typed_clocks = clocks.typed_clocks()
known_clocks = {}
for clk in typed_clocks.all_clocks():
  known_clocks.update({top['clocks'].hier_paths['lpg'] + clk.split('clk_')[-1]: 1})

# get all known resets and add them to a dict
# this is used to generate the tie-off assignments further below
resets = top['resets']
assert isinstance(resets, Resets)
output_rsts = resets.get_top_resets()
known_resets = {}
for rst in output_rsts:
  for dom in top['power']['domains']:
    if rst.shadowed:
      path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), True, dom)
      known_resets.update({
        path: 1
      })
    path = lib.get_reset_lpg_path(top, resets.get_reset_by_name(rst.name)._asdict(), False, dom)
    known_resets.update({
      path: 1
    })
%>\

% for k, lpg in enumerate(top['alert_lpgs']):
  // ${lpg['name']}
<%
  cg_en = top['clocks'].hier_paths['lpg'] + lpg['clock_connection'].split('.clk_')[-1]
  rst_en = lib.get_reset_lpg_path(top, lpg['reset_connection'])
  known_clocks[cg_en] = 0
  known_resets[rst_en] = 0
%>\
  assign lpg_cg_en[${k}] = ${cg_en};
  assign lpg_rst_en[${k}] = ${rst_en};
% endfor

// tie-off unused connections
//VCS coverage off
// pragma coverage off
<% k = 0 %>\
% for clk, unused in known_clocks.items():
  % if unused:
    prim_mubi_pkg::mubi4_t unused_cg_en_${k};
    assign unused_cg_en_${k} = ${clk};<% k += 1 %>
  % endif
% endfor
<% k = 0 %>\
% for rst, unused in known_resets.items():
  % if unused:
    prim_mubi_pkg::mubi4_t unused_rst_en_${k};
    assign unused_rst_en_${k} = ${rst};<% k += 1 %>
  % endif
% endfor
//VCS coverage on
// pragma coverage on

  // Peripheral Instantiation

<% alert_idx = 0 %>
% for m in top["module"]:
<%
if not lib.is_inst(m):
     continue

block = name_to_block[m['type']]
inouts, inputs, outputs = block.xputs

port_list = inputs + outputs + inouts
max_sigwidth = max(len(x.name) for x in port_list) if port_list else 0
max_intrwidth = (max(len(x.name) for x in block.interrupts)
                 if block.interrupts else 0)
%>\
  % if m["param_list"] or block.alerts:
  ${m["type"]} #(
  % if block.alerts:
<%
w = len(block.alerts)
slice = str(alert_idx+w-1) + ":" + str(alert_idx)
%>\
    .AlertAsyncOn(alert_handler_reg_pkg::AsyncOn[${slice}])${"," if m["param_list"] else ""}
  % endif
    % for i in m["param_list"]:
    .${i["name"]}(${i["name_top" if i.get("expose") == "true" or i.get("randtype", "none") != "none" else "default"]})${"," if not loop.last else ""}
    % endfor
  ) u_${m["name"]} (
  % else:
  ${m["type"]} u_${m["name"]} (
  % endif
    % for p_in in inputs + inouts:
      % if loop.first:

      // Input
      % endif
      .${lib.ljust("cio_"+p_in.name+"_i",max_sigwidth+9)} (cio_${m["name"]}_${p_in.name}_p2d),
    % endfor
    % for p_out in outputs + inouts:
      % if loop.first:

      // Output
      % endif
      .${lib.ljust("cio_"+p_out.name+"_o",   max_sigwidth+9)} (cio_${m["name"]}_${p_out.name}_d2p),
      .${lib.ljust("cio_"+p_out.name+"_en_o",max_sigwidth+9)} (cio_${m["name"]}_${p_out.name}_en_d2p),
    % endfor
    % for intr in block.interrupts:
      % if loop.first:

      // Interrupt
      % endif
      .${lib.ljust("intr_"+intr.name+"_o",max_intrwidth+7)} (intr_${m["name"]}_${intr.name}),
    % endfor
    % if block.alerts:
      % for alert in block.alerts:
      // [${alert_idx}]: ${alert.name}<% alert_idx += 1 %>
      % endfor
      .alert_tx_o  ( alert_tx[${slice}] ),
      .alert_rx_i  ( alert_rx[${slice}] ),
    % endif
    ## TODO: Inter-module Connection
    % if m.get('inter_signal_list'):

      // Inter-module signals
      % for sig in m['inter_signal_list']:
        ## TODO: handle below condition in lib.py
        % if sig['type'] == "req_rsp":
      .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
      .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")}),
        % elif sig['type'] == "io":
      .${lib.im_portname(sig,"io")}(${lib.im_netname(sig, "io")}),
        % elif sig['type'] == "uni":
          ## TODO: Broadcast type
          ## TODO: default for logic type
      .${lib.im_portname(sig)}(${lib.im_netname(sig)}),
        % endif
      % endfor
    % endif
    % if m["type"] == "rv_plic":
      .intr_src_i (intr_vector),
    % endif
    % if m["type"] == "pinmux":

      .periph_to_mio_i      (mio_d2p    ),
      .periph_to_mio_oe_i   (mio_en_d2p ),
      .mio_to_periph_o      (mio_p2d    ),

      .mio_attr_o,
      .mio_out_o,
      .mio_oe_o,
      .mio_in_i,

      .periph_to_dio_i      (dio_d2p    ),
      .periph_to_dio_oe_i   (dio_en_d2p ),
      .dio_to_periph_o      (dio_p2d    ),

      .dio_attr_o,
      .dio_out_o,
      .dio_oe_o,
      .dio_in_i,

    % endif
    % if m["type"] == "alert_handler":
      // alert signals
      .alert_rx_o  ( alert_rx ),
      .alert_tx_i  ( alert_tx ),
      // synchronized clock gated / reset asserted
      // indications for each alert
      .lpg_cg_en_i  ( lpg_cg_en  ),
      .lpg_rst_en_i ( lpg_rst_en ),
    % endif
    % if block.scan:
      .scanmode_i,
    % endif
    % if block.scan_reset:
      .scan_rst_ni,
    % endif
    % if block.scan_en:
      .scan_en_i,
    % endif

      // Clock and reset connections
    % for k, v in m["clock_connections"].items():
      .${k} (${v}),
    % endfor
    % for port, reset in m["reset_connections"].items():
      % if lib.is_shadowed_port(block, port):
      .${lib.shadow_name(port)} (${lib.get_reset_path(top, reset, True)}),
      % endif:
      .${port} (${lib.get_reset_path(top, reset)})${"," if not loop.last else ""}
    % endfor
  );
% endfor
  // interrupt assignments
<% base = interrupt_num %>\
  assign intr_vector = {
  % for intr in top["interrupt"][::-1]:
<% base -= intr["width"] %>\
      intr_${intr["name"]}, // IDs [${base} +: ${intr['width']}]
  % endfor
      1'b 0 // ID [0 +: 1] is a special case and tied to zero.
  };

  // TL-UL Crossbar
% for xbar in top["xbar"]:
<%
  name_len = max([len(x["name"]) for x in xbar["nodes"]]);
%>\
  xbar_${xbar["name"]} u_xbar_${xbar["name"]} (
  % for k, v in xbar["clock_connections"].items():
    .${k} (${v}),
  % endfor
  % for port, reset in xbar["reset_connections"].items():
    .${port} (${lib.get_reset_path(top, reset)}),
  % endfor

  ## Inter-module signal
  % for sig in xbar["inter_signal_list"]:
<% assert sig['type'] == "req_rsp" %>\
    // port: ${sig['name']}
    .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
    .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")}),

  % endfor

    .scanmode_i
  );
% endfor

% if "pinmux" in top:
  // Pinmux connections
  // All muxed inputs
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "input"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_in') %>\
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = mio_p2d[${literal}];
    % endif
  % endfor

  // All muxed outputs
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "output"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_out') %>\
  assign mio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All muxed output enables
  % for sig in top["pinmux"]["ios"]:
    % if sig["connection"] == "muxed" and sig["type"] in ["inout", "output"]:
<% literal = lib.get_io_enum_literal(sig, 'mio_out') %>\
  assign mio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All dedicated inputs
<% idx = 0 %>\
  logic [${num_dio_total-1}:0] unused_dio_p2d;
  assign unused_dio_p2d = dio_p2d;
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = dio_p2d[${literal}];
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign cio_${sig["name"]}_p2d${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""} = dio_p2d[${literal}];
    % endif
  % endfor

    // All dedicated outputs
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign dio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign dio_d2p[${literal}] = 1'b0;
    % elif sig["connection"] != "muxed" and sig["type"] in ["output"]:
  assign dio_d2p[${literal}] = cio_${sig["name"]}_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

  // All dedicated output enables
  % for sig in top["pinmux"]["ios"]:
<% literal = lib.get_io_enum_literal(sig, 'dio') %>\
    % if sig["connection"] != "muxed" and sig["type"] in ["inout"]:
  assign dio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % elif sig["connection"] != "muxed" and sig["type"] in ["input"]:
  assign dio_en_d2p[${literal}] = 1'b0;
    % elif sig["connection"] != "muxed" and sig["type"] in ["output"]:
  assign dio_en_d2p[${literal}] = cio_${sig["name"]}_en_d2p${"[" + str(sig["idx"]) +"]" if sig["idx"] !=-1  else ""};
    % endif
  % endfor

% endif

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)

endmodule
