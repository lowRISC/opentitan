// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import re
import topgen.lib as lib

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

%>\
module top_${top["name"]} #(
  // Manually defined parameters
% if not lib.is_rom_ctrl(top["module"]):
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
    p_rhs = p_exp['default']
%>\
    % if 12 + len(p_lhs) + 3 + len(p_rhs) + 1 < 100:
  parameter ${p_lhs} = ${p_rhs}${"" if loop.parent.last & loop.last else ","}
    % else:
  parameter ${p_lhs} =
      ${p_rhs}${"" if loop.parent.last & loop.last else ","}
    % endif
  % endfor
% endfor
) (
  // Reset, clocks defined as part of intermodule
  input               rst_ni,

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
  ${"input " if sig["direction"] == "in" else "output"} ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]},
  % endfor

  // Flash specific voltages
  inout [1:0] flash_test_mode_a_io,
  inout flash_test_voltage_h_io,

  // OTP specific voltages
  inout otp_ext_voltage_h_io,

% endif
  input                      scan_rst_ni, // reset used for test mode
  input                      scan_en_i,
  input lc_ctrl_pkg::lc_tx_t scanmode_i   // lc_ctrl_pkg::On for Scan
);

  // JTAG IDCODE for development versions of this code.
  // Manufacturers of OpenTitan chips must replace this code with one of their
  // own IDs.
  // Field structure as defined in the IEEE 1149.1 (JTAG) specification,
  // section 12.1.1.
  localparam logic [31:0] JTAG_IDCODE = {
    4'h0,     // Version
    16'h4F54, // Part Number: "OT"
    11'h426,  // Manufacturer Identity: Google
    1'b1      // (fixed)
  };

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
  // OTP HW_CFG Broadcast signals.
  // TODO(#6713): The actual struct breakout and mapping currently needs to
  // be performed by hand.
  assign csrng_otp_en_csrng_sw_app_read = otp_ctrl_otp_hw_cfg.data.en_csrng_sw_app_read;
  assign entropy_src_otp_en_entropy_src_fw_read = otp_ctrl_otp_hw_cfg.data.en_entropy_src_fw_read;
  assign entropy_src_otp_en_entropy_src_fw_over = otp_ctrl_otp_hw_cfg.data.en_entropy_src_fw_over;
  assign sram_ctrl_main_otp_en_sram_ifetch = otp_ctrl_otp_hw_cfg.data.en_sram_ifetch;
  assign sram_ctrl_ret_aon_otp_en_sram_ifetch = otp_ctrl_otp_hw_cfg.data.en_sram_ifetch;
  assign lc_ctrl_otp_device_id = otp_ctrl_otp_hw_cfg.data.device_id;
  assign lc_ctrl_otp_manuf_state = otp_ctrl_otp_hw_cfg.data.manuf_state;
  assign keymgr_otp_device_id = otp_ctrl_otp_hw_cfg.data.device_id;

  logic unused_otp_hw_cfg_bits;
  assign unused_otp_hw_cfg_bits = ^{
    otp_ctrl_otp_hw_cfg.valid,
    otp_ctrl_otp_hw_cfg.data.hw_cfg_digest,
    otp_ctrl_otp_hw_cfg.data.unallocated
  };
  % endif
% endfor

  // Unused reset signals
% for k, v in unused_resets.items():
  logic unused_d${v.lower()}_rst_${k};
% endfor
% for k, v in unused_resets.items():
  assign unused_d${v.lower()}_rst_${k} = ${lib.get_reset_path(k, v, top)};
% endfor

  // ibex specific assignments
  // TODO: This should be further automated in the future.
  assign rv_core_ibex_irq_timer = intr_rv_timer_timer_expired_0_0;
  assign rv_core_ibex_hart_id = '0;

  ## Not all top levels have a rom controller.
  ## For those that do not, reference the ROM directly.
% if lib.is_rom_ctrl(top["module"]):
  assign rv_core_ibex_boot_addr = ADDR_SPACE_ROM_CTRL__ROM;
% else:
  assign rv_core_ibex_boot_addr = ADDR_SPACE_ROM;
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

## Memory Instantiation
% for m in top["memory"]:
<%
  resets = m['reset_connections']
  clocks = m['clock_connections']
%>\
  % if m["type"] == "ram_1p_scr":
<%
     data_width = int(top["datawidth"])
     full_data_width = data_width + int(m["integ_width"])
     dw_byte = data_width // 8
     addr_width = ((int(m["size"], 0) // dw_byte) -1).bit_length()
     sram_depth = (int(m["size"], 0) // dw_byte)
     max_char = len(str(max(data_width, addr_width)))
%>\
  // sram device
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_req;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_gnt;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_we;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_intg_err;
  logic ${lib.bitarray(addr_width, max_char)} ${m["name"]}_addr;
  logic ${lib.bitarray(full_data_width, max_char)} ${m["name"]}_wdata;
  logic ${lib.bitarray(full_data_width, max_char)} ${m["name"]}_wmask;
  logic ${lib.bitarray(full_data_width, max_char)} ${m["name"]}_rdata;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_rvalid;
  logic ${lib.bitarray(2,          max_char)} ${m["name"]}_rerror;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(2),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor
    .tl_i        (${m["name"]}_tl_req),
    .tl_o        (${m["name"]}_tl_rsp),
    .en_ifetch_i (${m["inter_signal_list"][3]["top_signame"]}),
    .req_o       (${m["name"]}_req),
    .req_type_o  (),
    .gnt_i       (${m["name"]}_gnt),
    .we_o        (${m["name"]}_we),
    .addr_o      (${m["name"]}_addr),
    .wdata_o     (${m["name"]}_wdata),
    .wmask_o     (${m["name"]}_wmask),
    .intg_error_o(${m["name"]}_intg_err),
    .rdata_i     (${m["name"]}_rdata),
    .rvalid_i    (${m["name"]}_rvalid),
    .rerror_i    (${m["name"]}_rerror)
  );

<%
mem_name = m["name"].split("_")
mem_name = lib.Name(mem_name[1:])
%>\
  prim_ram_1p_scr #(
    .Width(${full_data_width}),
    .Depth(${sram_depth}),
    .EnableParity(0),
    .LfsrWidth(${data_width}),
    .StatePerm(RndCnstSramCtrl${mem_name.as_camel_case()}SramLfsrPerm),
    .DataBitsPerMask(1), // TODO: Temporary change to ensure byte updates can still be done
    .DiffWidth(8)
  ) u_ram1p_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor

    .key_valid_i (${m["inter_signal_list"][1]["top_signame"]}_req.valid),
    .key_i       (${m["inter_signal_list"][1]["top_signame"]}_req.key),
    .nonce_i     (${m["inter_signal_list"][1]["top_signame"]}_req.nonce),
    .init_req_i  (${m["inter_signal_list"][2]["top_signame"]}_req.req),
    .init_seed_i (${m["inter_signal_list"][2]["top_signame"]}_req.seed),
    .init_ack_o  (${m["inter_signal_list"][2]["top_signame"]}_rsp.ack),

    .req_i       (${m["name"]}_req),
    .intg_error_i(${m["name"]}_intg_err),
    .gnt_o       (${m["name"]}_gnt),
    .write_i     (${m["name"]}_we),
    .addr_i      (${m["name"]}_addr),
    .wdata_i     (${m["name"]}_wdata),
    .wmask_i     (${m["name"]}_wmask),
    .rdata_o     (${m["name"]}_rdata),
    .rvalid_o    (${m["name"]}_rvalid),
    .rerror_o    (${m["name"]}_rerror),
    .raddr_o     (${m["inter_signal_list"][1]["top_signame"]}_rsp.raddr),
    .intg_error_o(${m["inter_signal_list"][4]["top_signame"]}),
    .cfg_i       (ram_1p_cfg_i)
  );

  assign ${m["inter_signal_list"][1]["top_signame"]}_rsp.rerror = ${m["name"]}_rerror;

  % elif m["type"] == "rom":
<%
     data_width = int(top["datawidth"])
     full_data_width = data_width + int(m['integ_width'])
     dw_byte = data_width // 8
     addr_width = ((int(m["size"], 0) // dw_byte) -1).bit_length()
     rom_depth = (int(m["size"], 0) // dw_byte)
     max_char = len(str(max(data_width, addr_width)))
%>\
  // ROM device
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_req;
  logic ${lib.bitarray(addr_width, max_char)} ${m["name"]}_addr;
  logic ${lib.bitarray(full_data_width, max_char)} ${m["name"]}_rdata;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_rvalid;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(2),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor

    .tl_i        (${m["name"]}_tl_req),
    .tl_o        (${m["name"]}_tl_rsp),
    .en_ifetch_i (tlul_pkg::InstrEn),
    .req_o       (${m["name"]}_req),
    .req_type_o  (),
    .gnt_i       (1'b1), // Always grant as only one requester exists
    .we_o        (),
    .addr_o      (${m["name"]}_addr),
    .wdata_o     (),
    .wmask_o     (),
    .intg_error_o(), // Connect to ROM checker and ROM scramble later
    .rdata_i     (${m["name"]}_rdata[${data_width-1}:0]),
    .rvalid_i    (${m["name"]}_rvalid),
    .rerror_i    (2'b00)
  );

  prim_rom_adv #(
    .Width(${full_data_width}),
    .Depth(${rom_depth}),
    .MemInitFile(BootRomInitFile)
  ) u_rom_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor
    .req_i    (${m["name"]}_req),
    .addr_i   (${m["name"]}_addr),
    .rdata_o  (${m["name"]}_rdata),
    .rvalid_o (${m["name"]}_rvalid),
    .cfg_i    (rom_cfg_i)
  );

  % elif m["type"] == "eflash":

  // host to flash communication
  logic flash_host_req;
  tlul_pkg::tl_type_e flash_host_req_type;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic flash_host_rderr;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::BusAddrW-1:0] flash_host_addr;
  logic flash_host_intg_err;

  tlul_adapter_sram #(
    .SramAw(flash_ctrl_pkg::BusAddrW),
    .SramDw(flash_ctrl_pkg::BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor

    .tl_i        (${m["name"]}_tl_req),
    .tl_o        (${m["name"]}_tl_rsp),
    .en_ifetch_i (tlul_pkg::InstrEn), // tie this to secure boot somehow
    .req_o       (flash_host_req),
    .req_type_o  (flash_host_req_type),
    .gnt_i       (flash_host_req_rdy),
    .we_o        (),
    .addr_o      (flash_host_addr),
    .wdata_o     (),
    .wmask_o     (),
    .intg_error_o(flash_host_intg_err),
    .rdata_i     (flash_host_rdata),
    .rvalid_i    (flash_host_req_done),
    .rerror_i    ({flash_host_rderr,1'b0})
  );

  flash_phy u_flash_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for port, reset in resets.items():
    .${port}   (${lib.get_reset_path(reset, m['domain'], top)}),
    % endfor
    .host_req_i        (flash_host_req),
    .host_intg_err_i   (flash_host_intg_err),
    .host_req_type_i   (flash_host_req_type),
    .host_addr_i       (flash_host_addr),
    .host_req_rdy_o    (flash_host_req_rdy),
    .host_req_done_o   (flash_host_req_done),
    .host_rderr_o      (flash_host_rderr),
    .host_rdata_o      (flash_host_rdata),
    .flash_ctrl_i      (${m["inter_signal_list"][0]["top_signame"]}_req),
    .flash_ctrl_o      (${m["inter_signal_list"][0]["top_signame"]}_rsp),
    .lc_nvm_debug_en_i (${m["inter_signal_list"][2]["top_signame"]}),
    .flash_bist_enable_i,
    .flash_power_down_h_i,
    .flash_power_ready_h_i,
    .flash_test_mode_a_io,
    .flash_test_voltage_h_io,
    .flash_alert_o,
    .scanmode_i,
    .scan_en_i,
    .scan_rst_ni
  );

  % else:
    // flash memory is embedded within controller
  % endif
% endfor
## Peripheral Instantiation

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
    % endif
    % if m["type"] == "otp_ctrl":
      .otp_ext_voltage_h_io,
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
      .${port} (${lib.get_reset_path(reset, m['domain'], top)})${"," if not loop.last else ""}
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
    .${port} (${lib.get_reset_path(reset, xbar["domain"], top)}),
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
