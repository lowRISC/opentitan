// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// VCS does not support overriding enum and string parameters via command line. Instead, a `define
// is used that can be set from the command line. If no value has been specified, this gives a
// default. Other simulators don't take the detour via `define and can override the corresponding
// parameters directly.
`ifndef RV32M
  `define RV32M ibex_pkg::RV32MFast
`endif

`ifndef RV32B
  `define RV32B ibex_pkg::RV32BNone
`endif

`ifndef RegFile
  `define RegFile ibex_pkg::RegFileFF
`endif

/**
 * Ibex simple system
 *
 * This is a basic system consisting of an ibex, a 1 MB sram for instruction/data
 * and a small memory mapped control module for outputting ASCII text and
 * controlling/halting the simulation from the software running on the ibex.
 *
 * It is designed to be used with verilator but should work with other
 * simulators, a small amount of work may be required to support the
 * simulator_ctrl module.
 */

module ibex_simple_system (
  input IO_CLK,
  input IO_RST_N
);

  parameter bit                 SecureIbex               = 1'b0;
  parameter bit                 PMPEnable                = 1'b0;
  parameter int unsigned        PMPGranularity           = 0;
  parameter int unsigned        PMPNumRegions            = 4;
  parameter bit                 RV32E                    = 1'b0;
  parameter ibex_pkg::rv32m_e   RV32M                    = `RV32M;
  parameter ibex_pkg::rv32b_e   RV32B                    = `RV32B;
  parameter ibex_pkg::regfile_e RegFile                  = `RegFile;
  parameter bit                 BranchTargetALU          = 1'b0;
  parameter bit                 WritebackStage           = 1'b0;
  parameter bit                 ICache                   = 1'b0;
  parameter bit                 ICacheECC                = 1'b0;
  parameter bit                 BranchPredictor          = 1'b0;
  parameter                     SRAMInitFile             = "";

  logic clk_sys = 1'b0, rst_sys_n;

  typedef enum logic {
    CoreD
  } bus_host_e;

  typedef enum logic[1:0] {
    Ram,
    SimCtrl,
    Timer
  } bus_device_e;

  localparam int NrDevices = 3;
  localparam int NrHosts = 1;

  // interrupts
  logic timer_irq;

  // host and device signals
  logic           host_req    [NrHosts];
  logic           host_gnt    [NrHosts];
  logic [31:0]    host_addr   [NrHosts];
  logic           host_we     [NrHosts];
  logic [ 3:0]    host_be     [NrHosts];
  logic [31:0]    host_wdata  [NrHosts];
  logic           host_rvalid [NrHosts];
  logic [31:0]    host_rdata  [NrHosts];
  logic           host_err    [NrHosts];

  // devices (slaves)
  logic           device_req    [NrDevices];
  logic [31:0]    device_addr   [NrDevices];
  logic           device_we     [NrDevices];
  logic [ 3:0]    device_be     [NrDevices];
  logic [31:0]    device_wdata  [NrDevices];
  logic           device_rvalid [NrDevices];
  logic [31:0]    device_rdata  [NrDevices];
  logic           device_err    [NrDevices];

  // Device address mapping
  logic [31:0] cfg_device_addr_base [NrDevices];
  logic [31:0] cfg_device_addr_mask [NrDevices];
  assign cfg_device_addr_base[Ram] = 32'h100000;
  assign cfg_device_addr_mask[Ram] = ~32'hFFFFF; // 1 MB
  assign cfg_device_addr_base[SimCtrl] = 32'h20000;
  assign cfg_device_addr_mask[SimCtrl] = ~32'h3FF; // 1 kB
  assign cfg_device_addr_base[Timer] = 32'h30000;
  assign cfg_device_addr_mask[Timer] = ~32'h3FF; // 1 kB

  // Instruction fetch signals
  logic instr_req;
  logic instr_gnt;
  logic instr_rvalid;
  logic [31:0] instr_addr;
  logic [31:0] instr_rdata;
  logic instr_err;

  assign instr_gnt = instr_req;
  assign instr_err = '0;

  `ifdef VERILATOR
    assign clk_sys = IO_CLK;
    assign rst_sys_n = IO_RST_N;
  `else
    initial begin
      rst_sys_n = 1'b0;
      #8
      rst_sys_n = 1'b1;
    end
    always begin
      #1 clk_sys = 1'b0;
      #1 clk_sys = 1'b1;
    end
  `endif

  // Tie-off unused error signals
  assign device_err[Ram] = 1'b0;
  assign device_err[SimCtrl] = 1'b0;

  bus #(
    .NrDevices    ( NrDevices ),
    .NrHosts      ( NrHosts   ),
    .DataWidth    ( 32        ),
    .AddressWidth ( 32        )
  ) u_bus (
    .clk_i               (clk_sys),
    .rst_ni              (rst_sys_n),

    .host_req_i          (host_req     ),
    .host_gnt_o          (host_gnt     ),
    .host_addr_i         (host_addr    ),
    .host_we_i           (host_we      ),
    .host_be_i           (host_be      ),
    .host_wdata_i        (host_wdata   ),
    .host_rvalid_o       (host_rvalid  ),
    .host_rdata_o        (host_rdata   ),
    .host_err_o          (host_err     ),

    .device_req_o        (device_req   ),
    .device_addr_o       (device_addr  ),
    .device_we_o         (device_we    ),
    .device_be_o         (device_be    ),
    .device_wdata_o      (device_wdata ),
    .device_rvalid_i     (device_rvalid),
    .device_rdata_i      (device_rdata ),
    .device_err_i        (device_err   ),

    .cfg_device_addr_base,
    .cfg_device_addr_mask
  );

  ibex_core_tracing #(
      .SecureIbex      ( SecureIbex      ),
      .PMPEnable       ( PMPEnable       ),
      .PMPGranularity  ( PMPGranularity  ),
      .PMPNumRegions   ( PMPNumRegions   ),
      .MHPMCounterNum  ( 29              ),
      .RV32E           ( RV32E           ),
      .RV32M           ( RV32M           ),
      .RV32B           ( RV32B           ),
      .RegFile         ( RegFile         ),
      .BranchTargetALU ( BranchTargetALU ),
      .ICache          ( ICache          ),
      .ICacheECC       ( ICacheECC       ),
      .WritebackStage  ( WritebackStage  ),
      .BranchPredictor ( BranchPredictor ),
      .DmHaltAddr      ( 32'h00100000    ),
      .DmExceptionAddr ( 32'h00100000    )
    ) u_core (
      .clk_i                 (clk_sys),
      .rst_ni                (rst_sys_n),

      .test_en_i             ('b0),

      .hart_id_i             (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i           (32'h00100000),

      .instr_req_o           (instr_req),
      .instr_gnt_i           (instr_gnt),
      .instr_rvalid_i        (instr_rvalid),
      .instr_addr_o          (instr_addr),
      .instr_rdata_i         (instr_rdata),
      .instr_err_i           (instr_err),

      .data_req_o            (host_req[CoreD]),
      .data_gnt_i            (host_gnt[CoreD]),
      .data_rvalid_i         (host_rvalid[CoreD]),
      .data_we_o             (host_we[CoreD]),
      .data_be_o             (host_be[CoreD]),
      .data_addr_o           (host_addr[CoreD]),
      .data_wdata_o          (host_wdata[CoreD]),
      .data_rdata_i          (host_rdata[CoreD]),
      .data_err_i            (host_err[CoreD]),

      .irq_software_i        (1'b0),
      .irq_timer_i           (timer_irq),
      .irq_external_i        (1'b0),
      .irq_fast_i            (15'b0),
      .irq_nm_i              (1'b0),

      .debug_req_i           ('b0),

      .fetch_enable_i        ('b1),
      .alert_minor_o         (),
      .alert_major_o         (),
      .core_sleep_o          ()
    );

  // SRAM block for instruction and data storage
  ram_2p #(
      .Depth(1024*1024/4),
      .MemInitFile(SRAMInitFile)
    ) u_ram (
      .clk_i       (clk_sys),
      .rst_ni      (rst_sys_n),

      .a_req_i     (device_req[Ram]),
      .a_we_i      (device_we[Ram]),
      .a_be_i      (device_be[Ram]),
      .a_addr_i    (device_addr[Ram]),
      .a_wdata_i   (device_wdata[Ram]),
      .a_rvalid_o  (device_rvalid[Ram]),
      .a_rdata_o   (device_rdata[Ram]),

      .b_req_i     (instr_req),
      .b_we_i      (1'b0),
      .b_be_i      (4'b0),
      .b_addr_i    (instr_addr),
      .b_wdata_i   (32'b0),
      .b_rvalid_o  (instr_rvalid),
      .b_rdata_o   (instr_rdata)
    );

  simulator_ctrl #(
    .LogName("ibex_simple_system.log")
    ) u_simulator_ctrl (
      .clk_i     (clk_sys),
      .rst_ni    (rst_sys_n),

      .req_i     (device_req[SimCtrl]),
      .we_i      (device_we[SimCtrl]),
      .be_i      (device_be[SimCtrl]),
      .addr_i    (device_addr[SimCtrl]),
      .wdata_i   (device_wdata[SimCtrl]),
      .rvalid_o  (device_rvalid[SimCtrl]),
      .rdata_o   (device_rdata[SimCtrl])
    );

  timer #(
    .DataWidth    (32),
    .AddressWidth (32)
    ) u_timer (
      .clk_i          (clk_sys),
      .rst_ni         (rst_sys_n),

      .timer_req_i    (device_req[Timer]),
      .timer_we_i     (device_we[Timer]),
      .timer_be_i     (device_be[Timer]),
      .timer_addr_i   (device_addr[Timer]),
      .timer_wdata_i  (device_wdata[Timer]),
      .timer_rvalid_o (device_rvalid[Timer]),
      .timer_rdata_o  (device_rdata[Timer]),
      .timer_err_o    (device_err[Timer]),
      .timer_intr_o   (timer_irq)
    );

  export "DPI-C" function mhpmcounter_get;

  function automatic longint mhpmcounter_get(int index);
    return u_core.u_ibex_core.cs_registers_i.mhpmcounter[index];
  endfunction

endmodule
