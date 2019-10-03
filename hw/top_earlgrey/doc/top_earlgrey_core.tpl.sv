// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import re
%>\
module top_${top["name"]}_core #(
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

% for m in top["module"]:
  // ${m["name"]}
%     for p_in in m["available_input_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available input list always
%         if "width" in p_in and int(p_in["width"]) != 1:
  input  [${int(p_in["width"])-1}:0] cio_${m["name"]}_${p_in["name"]}_p2d_i,
%         else:
  input  cio_${m["name"]}_${p_in["name"]}_p2d_i,
%         endif
%     endfor
%     for p_out in m["available_output_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available output list always
%         if "width" in p_out and int(p_out["width"]) != 1:
  output [${int(p_out["width"])-1}:0] cio_${m["name"]}_${p_out["name"]}_d2p_o,
  output [${int(p_out["width"])-1}:0] cio_${m["name"]}_${p_out["name"]}_en_d2p_o,
%         else:
  output cio_${m["name"]}_${p_out["name"]}_d2p_o,
  output cio_${m["name"]}_${p_out["name"]}_en_d2p_o,
%         endif
%     endfor
% endfor

  input               scanmode_i  // 1 for Scan
);

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


  logic [0:0]   irq_plic;
  logic [${(interrupt_num).bit_length()-1}:0] irq_id[1];
  logic [0:0]   msip;

  // Non-debug module reset == reset for everything except for the debug module
  // and the logic required to access it.
  logic ndmreset_n;
  logic ndmreset_from_dm;
  assign ndmreset_n = (scanmode_i) ? rst_ni : ~ndmreset_from_dm & rst_ni;

  logic debug_req;

  // processor core
  rv_core_ibex #(
    .MHPMCounterNum      (8),
    .MHPMCounterWidth    (40),
    .RV32E               (0),
    .RV32M               (1),
    .DmHaltAddr          (ADDR_SPACE_DEBUG_MEM + dm::HaltAddress),
    .DmExceptionAddr     (ADDR_SPACE_DEBUG_MEM + dm::ExceptionAddress),
    .PipeLine            (IbexPipeLine)
  ) core (
    // clock and reset
    .clk_i                (clk_i),
    .rst_ni               (ndmreset_n),
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
    .NrHarts     (  1),
    .IdcodeValue (32'h00000001) // Temporary value
                                // xxxx             version
                                // xxxxxxxxxxxxxxxx part number
                                // xxxxxxxxxxx      manufacturer id
                                // 1                required by standard
  ) u_dm_top (
    .clk_i         (clk_i),
    .rst_ni        (rst_ni),
    .testmode_i    (1'b0),
    .ndmreset_o    (ndmreset_from_dm),
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
  % if m["type"] == "ram_1p":
<%
     data_width = int(top["datawidth"])
     dw_byte = data_width // 8
     addr_width = ((int(m["size"], 0) // dw_byte) -1).bit_length()
     sram_depth = (int(m["size"], 0) // dw_byte)
%>\
  // sram device
  logic        ${m["name"]}_req;
  logic        ${m["name"]}_we;
  logic [${addr_width-1}:0] ${m["name"]}_addr;
  logic [${data_width-1}:0] ${m["name"]}_wdata;
  logic [${data_width-1}:0] ${m["name"]}_wmask;
  logic [${data_width-1}:0] ${m["name"]}_rdata;
  logic        ${m["name"]}_rvalid;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(1)
  ) tl_adapter_${m["name"]} (
    .clk_i,
    .rst_ni   (ndmreset_n),

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
    .clk_i,
    .rst_ni   (ndmreset_n),

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
%>\
  // ROM device
  logic        ${m["name"]}_req;
  logic [${addr_width-1}:0] ${m["name"]}_addr;
  logic [${data_width-1}:0] ${m["name"]}_rdata;
  logic        ${m["name"]}_rvalid;

  tlul_adapter_sram #(
    .SramAw(${addr_width}),
    .SramDw(${data_width}),
    .Outstanding(1),
    .ErrOnWrite(1)
  ) tl_adapter_${m["name"]} (
    .clk_i,
    .rst_ni   (ndmreset_n),

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
    .clk_i,
    .rst_ni   (ndmreset_n),
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
    .clk_i,
    .rst_ni     (ndmreset_n),

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
    .clk_i,
    .rst_ni,
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
% for m in top["module"]:
  % if "parameter" in m:
  ${m["type"]} #(
    % for k, v in m["parameter"].items():
        % if loop.last:
    .${k}(${parameterize(v)})
        % else:
    .${k}(${parameterize(v)}),
        % endif
    % endfor
  ) ${m["name"]} (
  % else:
  ${m["type"]} ${m["name"]} (
  % endif
    % if not "bus_host" in m or m["bus_host"] in ["none", ""]:
          ## Assume TL-UL
      .tl_i (tl_${m["name"]}_d_h2d),
      .tl_o (tl_${m["name"]}_d_d2h),
    % else:
      .tl_d_i (tl_${m["name"]}_d_h2d),
      .tl_d_o (tl_${m["name"]}_d_d2h),
      .tl_h_o (tl_${m["name"]}_h_h2d),
      .tl_h_i (tl_${m["name"]}_h_d2h),
    % endif
    ## CIO
    ## TODO: Find a way to handle `scanmode`. It is not cio_ but top-level signal
    % for p_in in m["available_input_list"] + m["available_inout_list"]:
        ## assume it passed validate and have available input list always
      .cio_${p_in["name"]}_i (cio_${m["name"]}_${p_in["name"]}_p2d_i),
    % endfor
    % for p_in in m["available_output_list"] + m["available_inout_list"]:
        ## assume it passed validate and have available output list always
      .cio_${p_in["name"]}_o    (cio_${m["name"]}_${p_in["name"]}_d2p_o),
      .cio_${p_in["name"]}_en_o (cio_${m["name"]}_${p_in["name"]}_en_d2p_o),
    % endfor
    % for intr in m["interrupt_list"] if "interrupt_list" in m else []:
      .intr_${intr["name"]}_o (intr_${m["name"]}_${intr["name"]}),
    % endfor
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
    % if m["scan"] == "true":
      .scanmode_i   (scanmode_i),
    % endif
      .clk_i(${"clk_i" if m["clock"] == "main" else "clk_"+ m["clock"] + "_i"}),
      .rst_ni(${"ndmreset_n" if m["clock"] == "main" else "rst_" + m["clock"] + "_ni"})
  );

% endfor
  // interrupt assignments
  assign intr_vector = {
  % for intr in top["interrupt"][::-1]:
    % if loop.last:
      intr_${intr["name"]}
    % else:
      intr_${intr["name"]},
    % endif
  % endfor
  };

  // TL-UL Crossbar
  logic clk_main;
  logic ndmreset_sync_main_n;   // ndmreset synchronized to clk_main

  assign clk_main = clk_i;
  assign ndmreset_sync_main_n = ndmreset_n;

% for xbar in top["xbar"]:
<%
  name_len = max([len(x["name"]) for x in xbar["nodes"]]);
%>\
  xbar_${xbar["name"]} u_xbar_${xbar["name"]} (
  % for clock in xbar["clocks"]:
    ## TODO: How we can handle the reset?
    .clk_${clock}_i  (clk_${clock}),
    .rst_${clock}_ni (ndmreset_sync_${clock}_n),
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
% endfor
  );

  // make sure scanmode_i is never X (including during reset)
  `ASSERT_KNOWN(scanmodeKnown, scanmode_i, clk_i, 0)

endmodule
<%def name="parameterize(v)">\
    ## value type
    ## if it is integer, or bit'{h|d|b} digit, just put without quote
    ## else return with quote
    % if re.match('(\d+\'[hdb]\s*[0-9a-f_A-F]+|[0-9]+)',v) == None:
"${v}"\
    % else:
${v}\
    % endif
</%def>\
