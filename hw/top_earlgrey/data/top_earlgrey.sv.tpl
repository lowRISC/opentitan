// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import re
import topgen.lib as lib

num_mio_inputs = sum([x["width"] for x in top["pinmux"]["inputs"]])
num_mio_outputs = sum([x["width"] for x in top["pinmux"]["outputs"]])
num_mio_inouts = sum([x["width"] for x in top["pinmux"]["inouts"]])
num_mio = top["pinmux"]["num_mio"]

num_dio_inputs = sum([x["width"] if x["type"] == "input" else 0 for x in top["pinmux"]["dio"]])
num_dio_outputs = sum([x["width"] if x["type"] == "output" else 0 for x in top["pinmux"]["dio"]])
num_dio_inouts = sum([x["width"] if x["type"] == "inout" else 0 for x in top["pinmux"]["dio"]])
num_dio = sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])

num_im = sum([x["width"] if "width" in x else 1 for x in top["inter_signal"]["external"]])

max_miolength = max([len(x["name"]) for x in top["pinmux"]["inputs"] + top["pinmux"]["outputs"] + top["pinmux"]["inouts"]])
max_diolength = max([len(x["name"]) for x in top["pinmux"]["dio"]])

max_sigwidth = max([x["width"] if "width" in x else 1 for x in top["pinmux"]["inputs"] + top["pinmux"]["outputs"] +  top["pinmux"]["inouts"]])
max_sigwidth = len("{}".format(max_sigwidth))

clks_attr = top['clocks']
cpu_clk = top['clocks']['hier_paths']['top'] + "clk_proc_main"
cpu_rst = top["reset_paths"]["sys"]
dm_rst = top["reset_paths"]["lc"]
%>\
module top_${top["name"]} #(
  parameter bit IbexPipeLine = 0,
  parameter     BootRomInitFile = ""
) (
  // Clock and Reset
  input               clk_i,
  input               rst_ni,

  // Fixed io clock
  input               clk_io_i,

  // USB clock
  input               clk_usb_i,

  // aon clock
  input               clk_aon_i,

  // JTAG interface
  input               jtag_tck_i,
  input               jtag_tms_i,
  input               jtag_trst_ni,
  input               jtag_tdi_i,
  output              jtag_tdo_o,

% if num_mio != 0:
  // Multiplexed I/O
  input        ${lib.bitarray(num_mio, max_sigwidth)} mio_in_i,
  output logic ${lib.bitarray(num_mio, max_sigwidth)} mio_out_o,
  output logic ${lib.bitarray(num_mio, max_sigwidth)} mio_oe_o,
% endif
% if num_dio != 0:
  // Dedicated I/O
  input        ${lib.bitarray(num_dio, max_sigwidth)} dio_in_i,
  output logic ${lib.bitarray(num_dio, max_sigwidth)} dio_out_o,
  output logic ${lib.bitarray(num_dio, max_sigwidth)} dio_oe_o,
% endif

% if "padctrl" in top:
  // pad attributes to padring
  output logic[padctrl_reg_pkg::NMioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   mio_attr_o,
  output logic[padctrl_reg_pkg::NDioPads-1:0]
              [padctrl_reg_pkg::AttrDw-1:0]   dio_attr_o,
% endif

% if num_im != 0:

  // Inter-module Signal External type
  % for sig in top["inter_signal"]["external"]:
  ${"input " if sig["direction"] == "in" else "output"} ${lib.im_defname(sig)} ${lib.bitarray(sig["width"],1)} ${sig["signame"]},
  % endfor
% endif

  input               scanmode_i  // 1 for Scan
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

  tl_h2d_t  tl_corei_h_h2d;
  tl_d2h_t  tl_corei_h_d2h;

  tl_h2d_t  tl_cored_h_h2d;
  tl_d2h_t  tl_cored_h_d2h;

  tl_h2d_t  tl_dm_sba_h_h2d;
  tl_d2h_t  tl_dm_sba_h_d2h;

  tl_h2d_t  tl_debug_mem_d_h2d;
  tl_d2h_t  tl_debug_mem_d_d2h;

## TL-UL device port declaration
% for m in top["module"]:
%     if not m["bus_device"] in ["none", ""]:
  tl_h2d_t  tl_${m["name"]}_d_h2d;
  tl_d2h_t  tl_${m["name"]}_d_d2h;
%     endif
%     if not m["bus_host"] in ["none", ""]:
  tl_h2d_t  tl_${m["name"]}_h_h2d;
  tl_d2h_t  tl_${m["name"]}_h_d2h;
%     endif
% endfor

% for m in top["memory"]:
  tl_h2d_t tl_${m["name"]}_d_h2d;
  tl_d2h_t tl_${m["name"]}_d_d2h;
% endfor

## Xbar connection
% for xbar in top["xbar"]:
<%
  xbar_devices = [x for x in xbar["nodes"] if x["type"] == "device" and x["xbar"]]
%>\
  % for node in xbar_devices:
  tl_h2d_t tl_${xbar["name"]}_${node["name"]}_h2d;
  tl_d2h_t tl_${xbar["name"]}_${node["name"]}_d2h;
  % endfor
% endfor

  // Signals
  logic [${num_mio_inputs + num_mio_inouts - 1}:0] mio_p2d;
  logic [${num_mio_outputs + num_mio_inouts - 1}:0] mio_d2p;
  logic [${num_mio_outputs + num_mio_inouts - 1}:0] mio_d2p_en;
  logic [${num_dio - 1}:0] dio_p2d;
  logic [${num_dio - 1}:0] dio_d2p;
  logic [${num_dio - 1}:0] dio_d2p_en;
% for m in top["module"]:
  // ${m["name"]}
  % for p_in in m["available_input_list"] + m["available_inout_list"]:
    ## assume it passed validate and have available input list always
    % if "width" in p_in:
  logic ${lib.bitarray(int(p_in["width"]), max_sigwidth)} cio_${m["name"]}_${p_in["name"]}_p2d;
    % else:
  logic ${lib.bitarray(1, max_sigwidth)} cio_${m["name"]}_${p_in["name"]}_p2d;
    % endif
  % endfor
  % for p_out in m["available_output_list"] + m["available_inout_list"]:
    ## assume it passed validate and have available output list always
    % if "width" in p_out:
  logic ${lib.bitarray(int(p_out["width"]), max_sigwidth)} cio_${m["name"]}_${p_out["name"]}_d2p;
  logic ${lib.bitarray(int(p_out["width"]), max_sigwidth)} cio_${m["name"]}_${p_out["name"]}_en_d2p;
    % else:
  logic ${lib.bitarray(1, max_sigwidth)} cio_${m["name"]}_${p_out["name"]}_d2p;
  logic ${lib.bitarray(1, max_sigwidth)} cio_${m["name"]}_${p_out["name"]}_en_d2p;
    % endif
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
    % for intr in m["interrupt_list"] if "interrupt_list" in m else []:
        % if "width" in intr and int(intr["width"]) != 1:
  logic [${int(intr["width"])-1}:0] intr_${m["name"]}_${intr["name"]};
        % else:
  logic intr_${m["name"]}_${intr["name"]};
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
  // Escalation outputs
  prim_esc_pkg::esc_tx_t [alert_pkg::N_ESC_SEV-1:0]  esc_tx;
  prim_esc_pkg::esc_rx_t [alert_pkg::N_ESC_SEV-1:0]  esc_rx;

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

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // debug request from rv_dm to core
  logic debug_req;

  // processor core
  rv_core_ibex #(
    .PMPEnable                (1),
    .PMPGranularity           (0), // 2^(PMPGranularity+2) == 4 byte granularity
    .PMPNumRegions            (16),
    .MHPMCounterNum           (8),
    .MHPMCounterWidth         (40),
    .RV32E                    (0),
    .RV32M                    (1),
    .BranchTargetALU          (1),
    .WritebackStage           (1),
    .MultiplierImplementation ("single-cycle"),
    .ICache                   (0),
    .ICacheECC                (0),
    .DbgTriggerEn             (1),
    .SecureIbex               (0),
    .DmHaltAddr               (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr          (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine                 (IbexPipeLine)
  ) u_rv_core_ibex (
    // clock and reset
    .clk_i                (${cpu_clk}),
    .rst_ni               (${cpu_rst}),
    .test_en_i            (1'b0),
    // static pinning
    .hart_id_i            (32'b0),
    .boot_addr_i          (ADDR_SPACE_ROM),
    // TL-UL buses
    .tl_i_o               (tl_corei_h_h2d),
    .tl_i_i               (tl_corei_h_d2h),
    .tl_d_o               (tl_cored_h_h2d),
    .tl_d_i               (tl_cored_h_d2h),
    // interrupts
    .irq_software_i       (msip),
    .irq_timer_i          (intr_rv_timer_timer_expired_0_0),
    .irq_external_i       (irq_plic),
    .irq_fast_i           (15'b0),// PLIC handles all peripheral interrupts
    .irq_nm_i             (1'b0),// TODO - add and connect alert responder
    // debug interface
    .debug_req_i          (debug_req),
    // CPU control signals
    .fetch_enable_i       (1'b1),
    .core_sleep_o         (pwrmgr_pwr_cpu.core_sleeping)
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (${cpu_clk}),
    .rst_ni        (${dm_rst}),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_req),
    .dmactive_o    (),
    .debug_req_o   (debug_req),
    .unavailable_i (1'b0),

    // bus device with debug memory (for execution-based debug)
    .tl_d_i        (tl_debug_mem_d_h2d),
    .tl_d_o        (tl_debug_mem_d_d2h),

    // bus host (for system bus accesses, SBA)
    .tl_h_o        (tl_dm_sba_h_h2d),
    .tl_h_i        (tl_dm_sba_h_d2h),

    //JTAG
    .tck_i            (jtag_tck_i),
    .tms_i            (jtag_tms_i),
    .trst_ni          (jtag_trst_ni),
    .td_i             (jtag_tdi_i),
    .td_o             (jtag_tdo_o),
    .tdo_oe_o         (       )
  );

  assign rstmgr_cpu.ndmreset_req = ndmreset_req;
  assign rstmgr_cpu.rst_cpu_n = ${top["reset_paths"]["sys"]};

## Memory Instantiation
% for m in top["memory"]:
<%
  resets = m['reset_connections']
  clocks = m['clock_connections']
%>\
  % if m["type"] == "ram_1p":
<%
     data_width = int(top["datawidth"])
     dw_byte = data_width // 8
     addr_width = ((int(m["size"], 0) // dw_byte) -1).bit_length()
     sram_depth = (int(m["size"], 0) // dw_byte)
     max_char = len(str(max(data_width, addr_width)))
%>\
  // sram device
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_req;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_we;
  logic ${lib.bitarray(addr_width, max_char)} ${m["name"]}_addr;
  logic ${lib.bitarray(data_width, max_char)} ${m["name"]}_wdata;
  logic ${lib.bitarray(data_width, max_char)} ${m["name"]}_wmask;
  logic ${lib.bitarray(data_width, max_char)} ${m["name"]}_rdata;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_rvalid;
  logic ${lib.bitarray(2,          max_char)} ${m["name"]}_rerror;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(2)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor
    .tl_i     (tl_${m["name"]}_d_h2d),
    .tl_o     (tl_${m["name"]}_d_d2h),

    .req_o    (${m["name"]}_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (${m["name"]}_we),
    .addr_o   (${m["name"]}_addr),
    .wdata_o  (${m["name"]}_wdata),
    .wmask_o  (${m["name"]}_wmask),
    .rdata_i  (${m["name"]}_rdata),
    .rvalid_i (${m["name"]}_rvalid),
    .rerror_i (${m["name"]}_rerror)
  );

  prim_ram_1p_adv #(
    .Width(${data_width}),
    .Depth(${sram_depth}),
    .DataBitsPerMask(8),
    .CfgW(8),
    // TODO: enable parity once supported by the simulation infrastructure
    .EnableParity(0)
  ) u_ram1p_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor

    .req_i    (${m["name"]}_req),
    .write_i  (${m["name"]}_we),
    .addr_i   (${m["name"]}_addr),
    .wdata_i  (${m["name"]}_wdata),
    .wmask_i  (${m["name"]}_wmask),
    .rdata_o  (${m["name"]}_rdata),
    .rvalid_o (${m["name"]}_rvalid),
    .rerror_o (${m["name"]}_rerror),
    .cfg_i    ('0)
  );
  % elif m["type"] == "rom":
<%
     data_width = int(top["datawidth"])
     dw_byte = data_width // 8
     addr_width = ((int(m["size"], 0) // dw_byte) -1).bit_length()
     rom_depth = (int(m["size"], 0) // dw_byte)
     max_char = len(str(max(data_width, addr_width)))
%>\
  // ROM device
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_req;
  logic ${lib.bitarray(addr_width, max_char)} ${m["name"]}_addr;
  logic ${lib.bitarray(data_width, max_char)} ${m["name"]}_rdata;
  logic ${lib.bitarray(1,          max_char)} ${m["name"]}_rvalid;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(2),
    .ErrOnWrite(1)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor

    .tl_i     (tl_${m["name"]}_d_h2d),
    .tl_o     (tl_${m["name"]}_d_d2h),

    .req_o    (${m["name"]}_req),
    .gnt_i    (1'b1), // Always grant as only one requester exists
    .we_o     (),
    .addr_o   (${m["name"]}_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (${m["name"]}_rdata),
    .rvalid_i (${m["name"]}_rvalid),
    .rerror_i (2'b00)
  );

  prim_rom_adv #(
    .Width(${data_width}),
    .Depth(${rom_depth}),
    .MemInitFile(BootRomInitFile)
  ) u_rom_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor
    .req_i    (${m["name"]}_req),
    .addr_i   (${m["name"]}_addr),
    .rdata_o  (${m["name"]}_rdata),
    .rvalid_o (${m["name"]}_rvalid),
    .cfg_i    ('0) // tied off for now
  );

  % elif m["type"] == "eflash":

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [flash_ctrl_pkg::BusWidth-1:0] flash_host_rdata;
  logic [flash_ctrl_pkg::AddrW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(flash_ctrl_pkg::AddrW),
    .SramDw(flash_ctrl_pkg::BusWidth),
    .Outstanding(2),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) u_tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor

    .tl_i       (tl_${m["name"]}_d_h2d),
    .tl_o       (tl_${m["name"]}_d_d2h),

    .req_o    (flash_host_req),
    .gnt_i    (flash_host_req_rdy),
    .we_o     (),
    .addr_o   (flash_host_addr),
    .wdata_o  (),
    .wmask_o  (),
    .rdata_i  (flash_host_rdata),
    .rvalid_i (flash_host_req_done),
    .rerror_i (2'b00)
  );

  flash_phy u_flash_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}),
    % endfor
    % for key in resets:
    .${key}   (${top["reset_paths"][resets[key]]}),
    % endfor
    .host_req_i      (flash_host_req),
    .host_addr_i     (flash_host_addr),
    .host_req_rdy_o  (flash_host_req_rdy),
    .host_req_done_o (flash_host_req_done),
    .host_rdata_o    (flash_host_rdata),
    .flash_ctrl_i    (${m["inter_signal_list"][0]["top_signame"]}_req),
    .flash_ctrl_o    (${m["inter_signal_list"][0]["top_signame"]}_rsp)
  );

  % else:
    // flash memory is embedded within controller
  % endif
% endfor
## Peripheral Instantiation

<% alert_idx = 0 %>
% for m in top["module"]:
<%
port_list = m["available_input_list"] + m["available_output_list"] + m["available_inout_list"]
if len(port_list) == 0:
    max_sigwidth = 0
else:
    max_sigwidth = max([len(x["name"]) for x
      in m["available_input_list"] + m["available_inout_list"] + m["available_output_list"]])

if len(m["interrupt_list"]) == 0:
    max_intrwidth = 0
else:
    max_intrwidth = max([len(x["name"]) for x
        in m["interrupt_list"]])
%>\
  % if "parameter" in m:
  ${m["type"]} #(
    % for k, v in m["parameter"].items():
        % if loop.last:
    .${k}(${v | lib.parameterize})
        % else:
    .${k}(${v | lib.parameterize}),
        % endif
    % endfor
  ) u_${m["name"]} (
  % else:
  ${m["type"]} u_${m["name"]} (
  % endif
    % if not "bus_host" in m or m["bus_host"] in ["none", ""]:
      .tl_i (tl_${m["name"]}_d_h2d),
      .tl_o (tl_${m["name"]}_d_d2h),
    % else:
      .tl_d_i (tl_${m["name"]}_d_h2d),
      .tl_d_o (tl_${m["name"]}_d_d2h),
      .tl_h_o (tl_${m["name"]}_h_h2d),
      .tl_h_i (tl_${m["name"]}_h_d2h),
    % endif
    % for p_in in m["available_input_list"] + m["available_inout_list"]:
      % if loop.first:

      // Input
      % endif
      .${lib.ljust("cio_"+p_in["name"]+"_i",max_sigwidth+9)} (cio_${m["name"]}_${p_in["name"]}_p2d),
    % endfor
    % for p_out in m["available_output_list"] + m["available_inout_list"]:
      % if loop.first:

      // Output
      % endif
      .${lib.ljust("cio_"+p_out["name"]+"_o",   max_sigwidth+9)} (cio_${m["name"]}_${p_out["name"]}_d2p),
      .${lib.ljust("cio_"+p_out["name"]+"_en_o",max_sigwidth+9)} (cio_${m["name"]}_${p_out["name"]}_en_d2p),
    % endfor
    % for intr in m["interrupt_list"] if "interrupt_list" in m else []:
      % if loop.first:

      // Interrupt
      % endif
      .${lib.ljust("intr_"+intr["name"]+"_o",max_intrwidth+7)} (intr_${m["name"]}_${intr["name"]}),
    % endfor
    % if m["alert_list"]:
<%
w = sum([x["width"] if "width" in x else 1 for x in m["alert_list"]])
slice = str(alert_idx+w-1) + ":" + str(alert_idx)
%>
      % for alert in m["alert_list"] if "alert_list" in m else []:
      // [${alert_idx}]: ${alert["name"]}<% alert_idx += 1 %>
      % endfor
      .alert_tx_o  ( alert_tx[${slice}] ),
      .alert_rx_i  ( alert_rx[${slice}] ),
    % endif
    ## TODO: Inter-module Connection
    % if "inter_signal_list" in m:

      // Inter-module signals
      % for sig in m["inter_signal_list"]:
        ## TODO: handle below condition in lib.py
        % if sig["type"] == "req_rsp":
      .${lib.im_portname(sig,"req")}(${lib.im_netname(sig, "req")}),
      .${lib.im_portname(sig,"rsp")}(${lib.im_netname(sig, "rsp")}),
        % elif sig["type"] == "uni":
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
      .periph_to_mio_oe_i   (mio_d2p_en ),
      .mio_to_periph_o      (mio_p2d    ),

      .mio_out_o,
      .mio_oe_o,
      .mio_in_i,

      .periph_to_dio_i      (dio_d2p    ),
      .periph_to_dio_oe_i   (dio_d2p_en ),
      .dio_to_periph_o      (dio_p2d    ),

      .dio_out_o,
      .dio_oe_o,
      .dio_in_i,
    % endif
    % if m["type"] == "padctrl":

      .mio_attr_o,
      .dio_attr_o,
    % endif
    % if m["type"] == "alert_handler":
      // TODO: wire this to hardware debug circuit
      .crashdump_o (          ),
      // TODO: wire this to TRNG
      .entropy_i   ( 1'b0     ),
      // alert signals
      .alert_rx_o  ( alert_rx ),
      .alert_tx_i  ( alert_tx ),
      // escalation outputs
      .esc_rx_i    ( esc_rx   ),
      .esc_tx_o    ( esc_tx   ),
    % endif
    % if m["type"] == "nmi_gen":
      // escalation signal inputs
      .esc_rx_o    ( esc_rx   ),
      .esc_tx_i    ( esc_tx   ),
    % endif
    % if m["scan"] == "true":
      .scanmode_i   (scanmode_i),
    % endif

    % for k, v in m["clock_connections"].items():
      .${k} (${v}),
    % endfor
    % for k, v in m["reset_connections"].items():
      .${k} (${top["reset_paths"][v]})${"," if not loop.last else ""}
    % endfor
  );

% endfor
  // interrupt assignments
  assign intr_vector = {
  % for intr in top["interrupt"][::-1]:
      intr_${intr["name"]},
  % endfor
      1'b 0 // For ID 0.
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
    .${k} (${top["reset_paths"][v]}),
  % endfor
  % for node in xbar["nodes"]:
    % if node["xbar"]:
      % if node["type"] == "device":
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${xbar["name"]}_${node["name"]}_h2d),
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${xbar["name"]}_${node["name"]}_d2h),
      % elif node["type"] == "host":
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${node["name"]}_${xbar["name"]}_h2d),
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${node["name"]}_${xbar["name"]}_d2h),
      % endif
    % else:
      % if node["type"] == "device":
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${node["name"]}_d_h2d),
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${node["name"]}_d_d2h),
      % elif node["type"] == "host":
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${node["name"]}_h_h2d),
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${node["name"]}_h_d2h),
      % endif
    % endif
  % endfor

    .scanmode_i
  );
% endfor

% if "pinmux" in top:
  // Pinmux connections
  % if num_mio_outputs + num_mio_inouts != 0:
  assign mio_d2p = {
    % for sig in top["pinmux"]["inouts"] + top["pinmux"]["outputs"]:
    cio_${sig["name"]}_d2p${"" if loop.last else ","}
    % endfor
  };
  assign mio_d2p_en = {
  % for sig in top["pinmux"]["inouts"] + top["pinmux"]["outputs"]:
    cio_${sig["name"]}_en_d2p${"" if loop.last else ","}
  % endfor
  };
  % endif
  % if num_mio_inputs + num_mio_inouts != 0:
  assign {
    % for sig in top["pinmux"]["inouts"] + top["pinmux"]["inputs"]:
    cio_${sig["name"]}_p2d${"" if loop.last else ","}
    % endfor
  } = mio_p2d;
  % endif
% endif

% if num_dio != 0:
  // Dedicated IO connections
  // Input-only DIOs have no d2p signals
  assign dio_d2p = {
  % for sig in top["pinmux"]["dio"]:
    % if sig["type"] in ["output", "inout"]:
    cio_${sig["name"]}_d2p${"" if loop.last else ","} // DIO${num_dio - 1 - loop.index}
    % else:
    ${sig["width"]}'b0${"" if loop.last else ","} // DIO${num_dio - 1 - loop.index}: cio_${sig["name"]}
    % endif
  % endfor
  };

  assign dio_d2p_en = {
  % for sig in top["pinmux"]["dio"]:
    % if sig["type"] in ["output", "inout"]:
    cio_${sig["name"]}_en_d2p${"" if loop.last else ","} // DIO${num_dio - 1 - loop.index}
    % else:
    ${sig["width"]}'b0${"" if loop.last else ","} // DIO${num_dio - 1 - loop.index}: cio_${sig["name"]}
    % endif
  % endfor
  };

  // Output-only DIOs have no p2d signal
  % for sig in top["pinmux"]["dio"]:
    % if sig["type"] in ["input", "inout"]:
  assign cio_${sig["name"]}_p2d${" " * (max_diolength - len(sig["name"]))} = dio_p2d[${num_dio - 1 - loop.index}]; // DIO${num_dio - 1 - loop.index}
    % else:
  // DIO${num_dio - 1 - loop.index}: cio_${sig["name"]}
    % endif
  % endfor
% endif

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
