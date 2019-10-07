// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Ibex simulation to run the RISC-V compliance test on
 *
 * This is a toplevel wrapper for Ibex with helpers to run the RISC-V compliance
 * test. It is designed for Verilator, but should equally work for other
 * simulators (if the top-level clk and rst ports are replaced with a generated
 * clock).
 */
module ibex_riscv_compliance (
  input IO_CLK,
  input IO_RST_N
);

  parameter bit RV32E = 0;
  parameter bit RV32M = 1;

  logic clk_sys, rst_sys_n;

  assign clk_sys = IO_CLK;
  assign rst_sys_n = IO_RST_N;

  // Bus hosts, ordered in decreasing priority
  typedef enum {
    TestUtilHost,
    CoreD,
    CoreI
  } bus_host_e;

  typedef enum {
    Ram,
    TestUtilDevice
  } bus_device_e;

  localparam NrDevices = 2;
  localparam NrHosts = 3;

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
  assign cfg_device_addr_base[Ram] = 32'h0;
  assign cfg_device_addr_mask[Ram] = ~32'hFFFF; // 64 kB
  assign cfg_device_addr_base[TestUtilDevice] = 32'h20000;
  assign cfg_device_addr_mask[TestUtilDevice] = ~32'h3FF; // 1 kB


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

  ibex_core_tracing #(
      .DmHaltAddr(32'h00000000),
      .DmExceptionAddr(32'h00000000),
      .RV32E(RV32E),
      .RV32M(RV32M)
    ) u_core (
      .clk_i                 (clk_sys),
      .rst_ni                (rst_sys_n),

      .test_en_i             ('b0),

      .hart_id_i             (32'b0),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i           (32'h00000000),

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
      .irq_timer_i           (1'b0),
      .irq_external_i        (1'b0),
      .irq_fast_i            (15'b0),
      .irq_nm_i              (1'b0),

      .debug_req_i           ('b0),

      .fetch_enable_i        ('b1),
      .core_sleep_o          ()
    );

  // SRAM block for instruction and data storage
  ram_1p #(
      .Depth(64*1024/4)
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

  // RISC-V test utility, used by the RISC-V compliance test to interact with
  // the simulator.
  riscv_testutil
    u_riscv_testutil(
      .clk_i     (clk_sys),
      .rst_ni    (rst_sys_n),

      // Device port
      .dev_req_i     (device_req[TestUtilDevice]),
      .dev_we_i      (device_we[TestUtilDevice]),
      .dev_addr_i    (device_addr[TestUtilDevice]),
      .dev_wdata_i   (device_wdata[TestUtilDevice]),
      .dev_rvalid_o  (device_rvalid[TestUtilDevice]),
      .dev_rdata_o   (device_rdata[TestUtilDevice]),
      .dev_be_i      (device_be[TestUtilDevice]),
      .dev_err_o     (device_err[TestUtilDevice]),

      // Host port
      .host_req_o    (host_req[TestUtilHost]),
      .host_gnt_i    (host_gnt[TestUtilHost]),
      .host_rvalid_i (host_rvalid[TestUtilHost]),
      .host_addr_o   (host_addr[TestUtilHost]),
      .host_rdata_i  (host_rdata[TestUtilHost])
    );

endmodule
