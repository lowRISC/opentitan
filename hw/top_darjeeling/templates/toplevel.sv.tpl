// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import topgen.lib as lib

domain = "Main"

feature_info = {}
cio_info = {}
%>\
<%include file="/toplevel_snippets/info_dicts.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info" />\
`include "prim_assert.sv"

module top_${top["name"]} #(
<%include file="/toplevel_snippets/header_parameters.tpl" args="top=top, domain=domain" />\
) (
<%include file="/toplevel_snippets/port_intermodule_signals.tpl" args="top=top, domain=domain" />\
<%include file="/toplevel_snippets/port_special_signals.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\
);

  import top_${top["name"]}_pkg::*;
  // Compile-time random constants
  import top_${top["name"]}_rnd_cnst_pkg::*;
  import top_${top["name"]}_racl_pkg::*;

<%include file="/toplevel_snippets/localparams.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/cio_signals.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\

<%include file="/toplevel_snippets/interrupt_signals.tpl" args="top=top, name_to_block=name_to_block, domain=domain" />\

<%include file="/toplevel_snippets/alert_handler_signals.tpl" args="top=top, feature_info=feature_info, domain=domain" />\

<%include file="/toplevel_snippets/intermodule_signals.tpl" args="top=top, domain=domain" />\

% for m in top["module"]:
  % if m.get("template_type") == "otp_ctrl":
  // OTP HW_CFG Broadcast signals.
  // TODO(#6713): The actual struct breakout and mapping currently needs to
  // be performed by hand.
  assign csrng_otp_en_csrng_sw_app_read =
      otp_ctrl_otp_broadcast.hw_cfg1_data.en_csrng_sw_app_read;
  assign sram_ctrl_main_otp_en_sram_ifetch =
      otp_ctrl_otp_broadcast.hw_cfg1_data.en_sram_ifetch;
  assign lc_ctrl_otp_device_id =
      otp_ctrl_otp_broadcast.hw_cfg0_data.device_id;
  assign soc_dbg_ctrl_soc_dbg_state =
      otp_ctrl_otp_broadcast.hw_cfg1_data.soc_dbg_state;
  assign lc_ctrl_otp_manuf_state =
      otp_ctrl_otp_broadcast.hw_cfg0_data.manuf_state;
  % for mod in top["module"]:
    % if mod["type"] in ["keymgr", "keymgr_dpe"]:
  assign ${mod["name"]}_otp_device_id =
      otp_ctrl_otp_broadcast.hw_cfg0_data.device_id;
    % endif
  % endfor

  logic unused_otp_broadcast_bits;
  assign unused_otp_broadcast_bits = ^{
    otp_ctrl_otp_broadcast.valid,
    otp_ctrl_otp_broadcast.hw_cfg0_data.hw_cfg0_digest,
    otp_ctrl_otp_broadcast.hw_cfg1_data.hw_cfg1_digest,
    otp_ctrl_otp_broadcast.hw_cfg1_data.unallocated
  };
  % endif
% endfor

  // Ibex-specific assignments
  // TODO: This should be further automated in the future.
  assign rv_core_ibex_irq_timer = intr_rv_timer_timer_expired_hart0_timer0;
  assign rv_core_ibex_hart_id = '0;

  // Unconditionally disable the late debug feature and enable early debug
  assign rv_dm_otp_dis_rv_dm_late_debug = prim_mubi_pkg::MuBi8True;

% if 'rv_core_ibex_boot_addr' in (sig['signame'] for sig in top['inter_signal']['definitions']):
  ## Not all top levels have a rom controller.
  ## For those that do not, reference the ROM directly.
<% num_rom_ctrl = lib.num_rom_ctrl(top["module"]) %>\
  % if num_rom_ctrl == 1:
  assign rv_core_ibex_boot_addr = tl_main_pkg::ADDR_SPACE_ROM_CTRL__ROM;
  % elif num_rom_ctrl > 1:
  assign rv_core_ibex_boot_addr = tl_main_pkg::ADDR_SPACE_ROM_CTRL0__ROM;
  % else:
  assign rv_core_ibex_boot_addr = tl_main_pkg::ADDR_SPACE_ROM;
  % endif
% endif

<%include file="/toplevel_snippets/clk_reset_lpg_assigns.tpl" args="top=top, feature_info=feature_info, domain=domain" />\

<%include file="/toplevel_snippets/module_instantiations.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/interrupt_assigns.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/xbar_instantiations.tpl" args="top=top, domain=domain" />\

<%include file="/toplevel_snippets/cio_assigns.tpl" args="top=top, feature_info=feature_info, cio_info=cio_info, domain=domain" />\

% if lib.find_module(top["module"], "clkmgr").get("domain") == domain:
  // Make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_main_i, 0)
% endif\

endmodule
