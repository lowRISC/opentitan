// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import re
import topgen.lib as lib

num_mio_input = sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["inputs"]])
num_mio_output = sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["outputs"]])
num_mio_inout = sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["inouts"]])

num_dio = sum([x["width"] if "width" in x else 1 for x in top["pinmux"]["dio"]])

max_miolength = max([len(x["name"]) for x in top["pinmux"]["inputs"] + top["pinmux"]["outputs"] + top["pinmux"]["inouts"]])
max_diolength = max([len(x["name"]) for x in top["pinmux"]["dio"]])

max_sigwidth = max([x["width"] if "width" in x else 1 for x in top["pinmux"]["inputs"] + top["pinmux"]["outputs"] +  top["pinmux"]["inouts"]])
max_sigwidth = len("{}".format(max_sigwidth))

%>\
module top_${top["name"]} #(
  parameter bit IbexPipeLine = 0
) (
  // Clock and Reset
  input               clk_i,
  input               rst_ni,

  // JTAG interface
  input               jtag_tck_i,
  input               jtag_tms_i,
  input               jtag_trst_ni,
  input               jtag_td_i,
  output              jtag_td_o,

% if top["pinmux"]["num_mio"] != 0:
  // Multiplexed I/O
  input        ${lib.bitarray(top["pinmux"]["num_mio"], max_sigwidth)} mio_in_i,
  output logic ${lib.bitarray(top["pinmux"]["num_mio"], max_sigwidth)} mio_out_o,
  output logic ${lib.bitarray(top["pinmux"]["num_mio"], max_sigwidth)} mio_oe_o,
% endif
% if num_dio != 0:

  // Dedicated I/O
  % for sig in top["pinmux"]["dio"]:
    % if sig["type"] in ["input", "inout"]:
  input        ${lib.bitarray(sig["width"], max_sigwidth)} dio_${sig["name"]}_i,
    % endif
    % if sig["type"] in ["output", "inout"]:
  output logic ${lib.bitarray(sig["width"], max_sigwidth)} dio_${sig["name"]}_o,
  output logic ${lib.bitarray(sig["width"], max_sigwidth)} dio_${sig["name"]}_en_o,
    % endif
  % endfor
% endif

  input               scanmode_i  // 1 for Scan
);

  // JTAG IDCODE for development versions of this code.
  // Manufacturers of OpenTitan chips must replace this code with one of their
  // own IDs.
  // Field structure as defined in the IEEE 1149.1 (JTAG) specification,
  // section 12.1.1.
  localparam JTAG_IDCODE = {
    4'h0,     // Version
    16'h4F54, // Part Number: "OT"
    11'h426,  // Manufacturer Identity: Google
    1'b1      // (fixed)
  };

  import tlul_pkg::*;
  import top_pkg::*;
  import tl_main_pkg::*;
  import flash_ctrl_pkg::*;

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
  tl_h2d_t tl_${xbar["name"]}_h_h2d;
  tl_d2h_t tl_${xbar["name"]}_h_d2h;
  tl_h2d_t tl_${node["name"]}_d_h2d;
  tl_d2h_t tl_${node["name"]}_d_d2h;

  assign tl_${xbar["name"]}_h_h2d = tl_${node["name"]}_d_h2d;
  assign tl_${node["name"]}_d_d2h = tl_${xbar["name"]}_h_d2h;
  % endfor
% endfor

  //reset wires declaration
% for reset in top['resets']:
  logic ${reset['name']}_rst_n;
% endfor

  //clock wires declaration
% for clock in top['clocks']:
  logic ${clock['name']}_clk;
% endfor

  // Signals
  logic [${num_mio_input + num_mio_inout -1}:0] m2p;
  logic [${num_mio_output + num_mio_inout -1}:0] p2m;
  logic [${num_mio_output + num_mio_inout -1}:0] p2m_en;
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
  interrupt_num = sum([x["width"] if "width" in x else 1 for x in top["interrupt"]])
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


  <% add_spaces = " " * len(str((interrupt_num).bit_length()-1)) %>
  logic [0:0]${add_spaces}irq_plic;
  logic [0:0]${add_spaces}msip;
  logic [${(interrupt_num).bit_length()-1}:0] irq_id[1];
  logic [${(interrupt_num).bit_length()-1}:0] unused_irq_id[1];

  // this avoids lint errors
  assign unused_irq_id = irq_id;

  // Alert list
  prim_pkg::alert_tx_t [alert_pkg::NAlerts-1:0]  alert_tx;
  prim_pkg::alert_rx_t [alert_pkg::NAlerts-1:0]  alert_rx;
  // Escalation outputs
  prim_pkg::esc_tx_t [alert_pkg::N_ESC_SEV-1:0]  esc_tx;
  prim_pkg::esc_rx_t [alert_pkg::N_ESC_SEV-1:0]  esc_rx;

% if not top["alert"]:
  for (genvar k = 0; k < alert_pkg::NAlerts; k++) begin : gen_alert_tie_off
    // tie off if no alerts present in the system
    assign alert_tx[k].alert_p = 1'b0;
    assign alert_tx[k].alert_n = 1'b1;
  end
% endif

  // clock assignments
% for clock in top['clocks']:
  assign ${clock['name']}_clk = clk_i;
% endfor

  // Non-debug module reset == reset for everything except for the debug module
  logic ndmreset_req;

  // root resets
  // TODO: lc_rst_n is not the true root reset.  It will be differentiated once the
  //       the reset controller logic is present
  assign lc_rst_n = rst_ni;
  assign sys_rst_n = (scanmode_i) ? lc_rst_n : ~ndmreset_req & lc_rst_n;

  //non-root reset assignments
% for reset in top['resets']:
  % if reset['type'] in ['leaf']:
  assign ${reset['name']}_rst_n = ${reset['root']}_rst_n;
  % endif
% endfor

  // debug request from rv_dm to core
  logic debug_req;

  // processor core
  rv_core_ibex #(
    .PMPEnable           (0),
    .PMPGranularity      (0),
    .PMPNumRegions       (4),
    .MHPMCounterNum      (8),
    .MHPMCounterWidth    (40),
    .RV32E               (0),
    .RV32M               (1),
    .DmHaltAddr          (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr     (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine            (IbexPipeLine)
  ) core (
    // clock and reset
    .clk_i                (main_clk),
    .rst_ni               (sys_rst_n),
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
    .core_sleep_o         ()
  );

  // Debug Module (RISC-V Debug Spec 0.13)
  //

  rv_dm #(
    .NrHarts     (1),
    .IdcodeValue (JTAG_IDCODE)
  ) u_dm_top (
    .clk_i         (main_clk),
    .rst_ni        (lc_rst_n),
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
    .td_i             (jtag_td_i),
    .td_o             (jtag_td_o),
    .tdo_oe_o         (       )
  );

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

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(1)
  ) tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
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
    .rerror_i (2'b00)
  );

  ## TODO: Instantiate ram_1p model using RAMGEN (currently not available)
  prim_ram_1p #(
    .Width(${data_width}),
    .Depth(${sram_depth}),
    .DataBitsPerMask(${int(data_width/4)})
  ) u_ram1p_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
    % endfor

    .req_i    (${m["name"]}_req),
    .write_i  (${m["name"]}_we),
    .addr_i   (${m["name"]}_addr),
    .wdata_i  (${m["name"]}_wdata),
    .wmask_i  (${m["name"]}_wmask),
    .rvalid_o (${m["name"]}_rvalid),
    .rdata_o  (${m["name"]}_rdata)
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
    .Outstanding(1),
    .ErrOnWrite(1)
  ) tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
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

  ## TODO: Replace emulated ROM to real ROM in ASIC SoC
  prim_rom #(
    .Width(${data_width}),
    .Depth(${rom_depth})
  ) u_rom_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
    % endfor
    .cs_i     (${m["name"]}_req),
    .addr_i   (${m["name"]}_addr),
    .dout_o   (${m["name"]}_rdata),
    .dvalid_o (${m["name"]}_rvalid)
  );

  % elif m["type"] == "eflash":

  // flash controller to eflash communication
  flash_c2m_t flash_c2m;
  flash_m2c_t flash_m2c;

  // host to flash communication
  logic flash_host_req;
  logic flash_host_req_rdy;
  logic flash_host_req_done;
  logic [FLASH_DW-1:0] flash_host_rdata;
  logic [FLASH_AW-1:0] flash_host_addr;

  tlul_adapter_sram #(
    .SramAw(FLASH_AW),
    .SramDw(FLASH_DW),
    .Outstanding(1),
    .ByteAccess(0),
    .ErrOnWrite(1)
  ) tl_adapter_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
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

  flash_phy #(
    .NumBanks(FLASH_BANKS),
    .PagesPerBank(FLASH_PAGES_PER_BANK),
    .WordsPerPage(FLASH_WORDS_PER_PAGE),
    .DataWidth(${data_width})
  ) u_flash_${m["name"]} (
    % for key in clocks:
    .${key}   (${clocks[key]}_clk),
    % endfor
    % for key in resets:
    .${key}   (${resets[key]}_rst_n),
    % endfor
    .host_req_i      (flash_host_req),
    .host_addr_i     (flash_host_addr),
    .host_req_rdy_o  (flash_host_req_rdy),
    .host_req_done_o (flash_host_req_done),
    .host_rdata_o    (flash_host_rdata),
    .flash_ctrl_i    (flash_c2m),
    .flash_ctrl_o    (flash_m2c)
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
  ) ${m["name"]} (
  % else:
  ${m["type"]} ${m["name"]} (
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
      // [${alert_idx}]: ${alert["name"]} <% alert_idx += 1 %>
      % endfor
      .alert_tx_o  ( alert_tx[${slice}] ),
      .alert_rx_i  ( alert_rx[${slice}] ),
    % endif
    ## TODO: Inter-module Connection
    % if m["type"] == "flash_ctrl":

      .flash_o(flash_c2m),
      .flash_i(flash_m2c),
    % endif
    % if m["type"] == "rv_plic":

      .intr_src_i (intr_vector),
      .irq_o      (irq_plic),
      .irq_id_o   (irq_id),
      .msip_o     (msip),
    % endif
    % if m["type"] == "pinmux":

      .periph_to_mio_i      (p2m    ),
      .periph_to_mio_oe_i   (p2m_en ),
      .mio_to_periph_o      (m2p    ),

      .mio_out_o            (mio_out_o),
      .mio_oe_o             (mio_oe_o ),
      .mio_in_i             (mio_in_i ),
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
      .${k} (${v}_clk),
    % endfor
    % for k, v in m["reset_connections"].items():
      .${k} (${v}_rst_n)${"," if not loop.last else ""}
    % endfor
  );

% endfor
  // interrupt assignments
  assign intr_vector = {
  % for intr in top["interrupt"][::-1]:
      intr_${intr["name"]}${"," if not loop.last else ""}
  % endfor
  };

  // TL-UL Crossbar
% for xbar in top["xbar"]:
<%
  name_len = max([len(x["name"]) for x in xbar["nodes"]]);
%>\
  xbar_${xbar["name"]} u_xbar_${xbar["name"]} (
  % for k, v in xbar["clock_connections"].items():
    .${k} (${v}_clk),
  % endfor
  % for k, v in xbar["reset_connections"].items():
    .${k} (${v}_rst_n),
  % endfor
  % for node in xbar["nodes"]:
    % if node["type"] == "device":
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${node["name"]}_d_h2d),
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${node["name"]}_d_d2h),
    % elif node["type"] == "host":
    .tl_${(node["name"]+"_i").ljust(name_len+2)} (tl_${node["name"]}_h_h2d),
    .tl_${(node["name"]+"_o").ljust(name_len+2)} (tl_${node["name"]}_h_d2h),
    % endif
  % endfor

    .scanmode_i
  );
% endfor

% if "pinmux" in top:
  // Pinmux connections
  % if num_mio_output + num_mio_inout != 0:
  assign p2m = {
    % for sig in top["pinmux"]["inouts"] + top["pinmux"]["outputs"]:
    cio_${sig["name"]}_d2p${"" if loop.last else ","}
    % endfor
  };
  assign p2m_en = {
  % for sig in top["pinmux"]["inouts"] + top["pinmux"]["outputs"]:
    cio_${sig["name"]}_en_d2p${"" if loop.last else ","}
  % endfor
  };
  % endif
  % if num_mio_input + num_mio_inout != 0:
  assign {
    % for sig in top["pinmux"]["inouts"] + top["pinmux"]["inputs"]:
    cio_${sig["name"]}_p2d${"" if loop.last else ","}
    % endfor
  } = m2p;
  % endif
% endif

% if num_dio != 0:
  % for sig in top["pinmux"]["dio"]:
  % if sig["type"] in ["input", "inout"]:
  assign ${lib.ljust("cio_" + sig["name"] + "_p2d", max_diolength+9)} = dio_${sig["name"]}_i;
  % endif
  % if sig["type"] in ["output", "inout"]:
  assign ${lib.ljust("dio_" + sig["name"] + "_o",   max_diolength+9)} = cio_${sig["name"]}_d2p;
  assign ${lib.ljust("dio_" + sig["name"] + "_en_o",max_diolength+9)} = cio_${sig["name"]}_en_d2p;
  % endif
  % endfor
% endif

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
