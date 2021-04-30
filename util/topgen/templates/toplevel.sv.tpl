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

clks_attr = top['clocks']
cpu_clk = top['clocks']['hier_paths']['top'] + "clk_proc_main"
cpu_rst = top["reset_paths"]["sys"]
dm_rst = top["reset_paths"]["lc"]
esc_clk = top['clocks']['hier_paths']['top'] + "clk_io_div4_timers"
esc_rst = top["reset_paths"]["sys_io_div4"]

unused_resets = lib.get_unused_resets(top)
unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(top["inter_signal"]["definitions"])

has_toplevel_rom = False
for m in top['memory']:
  if m['type'] == 'rom':
    has_toplevel_rom = True

%>\
module top_${top["name"]} #(
  // Auto-inferred parameters
% for m in top["module"]:
  % if not lib.is_inst(m):
<% continue %>
  % endif
  % for p_exp in filter(lambda p: p.get("expose") == "true", m["param_list"]):
  parameter ${p_exp["type"]} ${p_exp["name_top"]} = ${p_exp["default"]},
  % endfor
% endfor

  // Manually defined parameters
% if has_toplevel_rom:
  parameter     BootRomInitFile = "",
% endif
  parameter ibex_pkg::regfile_e IbexRegFile = ibex_pkg::RegFileFF,
  parameter bit IbexICache = 1,
  parameter bit IbexPipeLine = 0,
  parameter bit SecureIbex = 1
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


<% add_spaces = " " * len(str((interrupt_num-1).bit_length()-1)) %>
  logic [0:0]${add_spaces}irq_plic;
  logic [0:0]${add_spaces}msip;
  logic [${(interrupt_num-1).bit_length()-1}:0] irq_id[1];
  logic [${(interrupt_num-1).bit_length()-1}:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

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

  // Unused reset signals
% for k, v in unused_resets.items():
  logic unused_d${v.lower()}_rst_${k};
% endfor
% for k, v in unused_resets.items():
  assign unused_d${v.lower()}_rst_${k} = ${lib.get_reset_path(k, v, top['resets'])};
% endfor

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // debug request from rv_dm to core
  logic debug_req;

  // processor core
  rv_core_ibex #(
    .PMPEnable                (1),
    .PMPGranularity           (0), // 2^(PMPGranularity+2) == 4 byte granularity
    .PMPNumRegions            (16),
    .MHPMCounterNum           (10),
    .MHPMCounterWidth         (32),
    .RV32E                    (0),
    .RV32M                    (ibex_pkg::RV32MSingleCycle),
    .RV32B                    (ibex_pkg::RV32BNone),
    .RegFile                  (IbexRegFile),
    .BranchTargetALU          (1),
    .WritebackStage           (1),
    .ICache                   (IbexICache),
    .ICacheECC                (1),
    .BranchPredictor          (0),
    .DbgTriggerEn             (1),
    .SecureIbex               (SecureIbex),
    .DmHaltAddr               (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress[31:0]),
    .DmExceptionAddr          (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress[31:0]),
    .PipeLine                 (IbexPipeLine)
  ) u_rv_core_ibex (
    // clock and reset
    .clk_i                (${cpu_clk}),
    .rst_ni               (${cpu_rst}[rstmgr_pkg::Domain0Sel]),
    .clk_esc_i            (${esc_clk}),
    .rst_esc_ni           (${esc_rst}[rstmgr_pkg::Domain0Sel]),
    .ram_cfg_i            (ast_ram_1p_cfg),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM_CTRL__ROM),
    // TL-UL buses
    .tl_i_o               (main_tl_corei_req),
    .tl_i_i               (main_tl_corei_rsp),
    .tl_d_o               (main_tl_cored_req),
    .tl_d_i               (main_tl_cored_rsp),
    // interrupts
    .irq_software_i       (msip),
    .irq_timer_i          (intr_rv_timer_timer_expired_0_0),
    .irq_external_i       (irq_plic),
    // escalation input from alert handler (NMI)
    .esc_tx_i             (alert_handler_esc_tx[0]),
    .esc_rx_o             (alert_handler_esc_rx[0]),
    // debug interface
    .debug_req_i          (debug_req),
    // crash dump interface
    .crash_dump_o         (rv_core_ibex_crash_dump),
    // CPU control signals
    .lc_cpu_en_i          (lc_ctrl_lc_cpu_en),
    .pwrmgr_cpu_en_i      (pwrmgr_aon_fetch_en),
    .core_sleep_o         (pwrmgr_aon_pwr_cpu.core_sleeping),

    // dft bypass
    .scan_rst_ni,
    .scanmode_i
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (${cpu_clk}),
    .rst_ni        (${dm_rst}[rstmgr_pkg::Domain0Sel]),
    .hw_debug_en_i (lc_ctrl_lc_hw_debug_en),
    .scanmode_i,
    .scan_rst_ni,
    .ndmreset_o    (ndmreset_req),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (main_tl_debug_mem_req),
    .tl_d_o        (main_tl_debug_mem_rsp),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (main_tl_dm_sba_req),
    .tl_h_i        (main_tl_dm_sba_rsp),

    //JTAG
    .jtag_req_i    (pinmux_aon_rv_jtag_req),
    .jtag_rsp_o    (pinmux_aon_rv_jtag_rsp)
  );

  assign rstmgr_aon_cpu.ndmreset_req = ndmreset_req;
  assign rstmgr_aon_cpu.rst_cpu_n = ${top["reset_paths"]["sys"]}[rstmgr_pkg::Domain0Sel];

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
    % for key, value in resets.items():
    .${key}   (${value}),
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
    % for key, value in resets.items():
    .${key}   (${value}),
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
    .EnableDataIntgGen(1) // TODO: Needs to be updated for intgerity passthrough
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key, value in resets.items():
    .${key}   (${value}),
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
    % for key, value in resets.items():
    .${key}   (${value}),
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
    % for key, value in resets.items():
    .${key}   (${value}),
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
    % for key, value in resets.items():
    .${key}   (${value}),
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
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),
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
    % for k, v in m["reset_connections"].items():
      .${k} (${v})${"," if not loop.last else ""}
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
  % for k, v in xbar["reset_connections"].items():
    .${k} (${v}),
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
