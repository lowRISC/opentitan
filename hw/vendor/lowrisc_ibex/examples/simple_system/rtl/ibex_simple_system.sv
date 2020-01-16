// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

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

  parameter bit RV32E = 0;
  parameter bit RV32M = 1;

  logic clk_sys = 1'b0, rst_sys_n;

  typedef enum {
    CoreD,
    CoreI
  } bus_host_e;

  typedef enum {
    Ram,
    SimCtrl,
    Timer
  } bus_device_e;

  localparam NrDevices = 3;
  localparam NrHosts = 2;

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


  `ifdef VERILATOR
    assign clk_sys = IO_CLK;
    assign rst_sys_n = IO_RST_N;
  `else
    initial begin
      rst_sys_n = 1'b0;
      device_err = '{default:1'b0};
      #8
      rst_sys_n = 1'b1;
    end
    always begin
      #1 clk_sys = 1'b0;
      #1 clk_sys = 1'b1;
    end
  `endif

  bus #(
    .NrDevices   (NrDevices),
    .NrHosts     (NrHosts  ),
    .DataWidth   (32       ),
    .AddressWidth(32       )
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

  assign host_we[CoreI]    = 1'b0;
  assign host_be[CoreI]    = 4'b1111;
  assign host_wdata[CoreI] = 32'b0;

  ibex_core_tracing #(
      .MHPMCounterNum(29),
      .DmHaltAddr(32'h00100000),
      .DmExceptionAddr(32'h00100000),
      .RV32E(RV32E),
      .RV32M(RV32M)
    ) u_core (
      .clk_i                 (clk_sys),
      .rst_ni                (rst_sys_n),

      .test_en_i             ('b0),

      .hart_id_i             (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i           (32'h00100000),

      .instr_req_o           (host_req[CoreI]),
      .instr_gnt_i           (host_gnt[CoreI]),
      .instr_rvalid_i        (host_rvalid[CoreI]),
      .instr_addr_o          (host_addr[CoreI]),
      .instr_rdata_i         (host_rdata[CoreI]),
      .instr_err_i           (host_err[CoreI]),

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
      .core_sleep_o          ()
    );

  // SRAM block for instruction and data storage
  ram_1p #(
      .Depth(1024*1024/4)
    ) u_ram (
      .clk_i     (clk_sys),
      .rst_ni    (rst_sys_n),
      .req_i     (device_req[Ram]),
      .we_i      (device_we[Ram]),
      .be_i      (device_be[Ram]),
      .addr_i    (device_addr[Ram]),
      .wdata_i   (device_wdata[Ram]),
      .rvalid_o  (device_rvalid[Ram]),
      .rdata_o   (device_rdata[Ram])
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

  // Expose the performance counter array so it's easy to access in
  // a verilator siumulation
  logic [63:0] mhpmcounter_vals [32] /*verilator public_flat*/;

  for(genvar i = 0;i < 32; i = i + 1) begin
      assign mhpmcounter_vals[i] = u_core.u_ibex_core.cs_registers_i.mhpmcounter[i];
  end
endmodule

