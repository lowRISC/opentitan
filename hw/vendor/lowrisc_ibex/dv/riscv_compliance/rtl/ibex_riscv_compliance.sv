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

  parameter bit          PMPEnable        = 1'b0;
  parameter int unsigned PMPGranularity   = 0;
  parameter int unsigned PMPNumRegions    = 4;
  parameter int unsigned MHPMCounterNum   = 0;
  parameter int unsigned MHPMCounterWidth = 40;
  parameter bit RV32E                     = 1'b0;
  parameter ibex_pkg::rv32m_e RV32M       = ibex_pkg::RV32MFast;
  parameter ibex_pkg::rv32b_e RV32B       = ibex_pkg::RV32BNone;
  parameter ibex_pkg::rv32zc_e RV32ZC     = ibex_pkg::RV32Zca;
  parameter ibex_pkg::regfile_e RegFile   = ibex_pkg::RegFileFF;
  parameter bit BranchTargetALU           = 1'b0;
  parameter bit WritebackStage            = 1'b0;
  parameter bit ICache                    = 1'b0;
  parameter bit ICacheECC                 = 1'b0;
  parameter bit ICacheTweakInfection      = 1'b0;
  parameter bit BranchPredictor           = 1'b0;
  parameter bit SecureIbex                = 1'b0;
  parameter int unsigned LockstepOffset   = 1;
  parameter bit ICacheScramble            = 1'b0;
  parameter bit DbgTriggerEn              = 1'b0;

  logic clk_sys, rst_sys_n;

  assign clk_sys = IO_CLK;
  assign rst_sys_n = IO_RST_N;

  // Bus hosts, ordered in decreasing priority
  typedef enum logic[1:0] {
    TestUtilHost,
    CoreD,
    CoreI
  } bus_host_e;

  typedef enum logic {
    Ram,
    TestUtilDevice
  } bus_device_e;

  localparam int unsigned NrDevices = 2;
  localparam int unsigned NrHosts = 3;
  // 64 kB RAM. Must be a power of 2. Check bus configuration below when changing.
  localparam int unsigned RamSizeWords = 64*1024/4;

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

  logic [6:0]     ibex_data_rdata_intg;
  logic [6:0]     ibex_instr_rdata_intg;

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
  assign cfg_device_addr_mask[Ram] = ~32'(RamSizeWords * 4 - 1);
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

  if (SecureIbex) begin : g_mem_rdata_ecc
    logic [31:0] unused_data_rdata;
    logic [31:0] unused_instr_rdata;

    prim_secded_inv_39_32_enc u_data_rdata_intg_gen (
      .data_i (host_rdata[CoreD]),
      .data_o ({ibex_data_rdata_intg, unused_data_rdata})
    );

    prim_secded_inv_39_32_enc u_instr_rdata_intg_gen (
      .data_i (host_rdata[CoreI]),
      .data_o ({ibex_instr_rdata_intg, unused_instr_rdata})
    );
  end else begin : g_no_mem_rdata_ecc
    assign ibex_data_rdata_intg = '0;
    assign ibex_instr_rdata_intg = '0;
  end

  ibex_top_tracing #(
      .PMPEnable            (PMPEnable           ),
      .PMPGranularity       (PMPGranularity      ),
      .PMPNumRegions        (PMPNumRegions       ),
      .MHPMCounterNum       (MHPMCounterNum      ),
      .MHPMCounterWidth     (MHPMCounterWidth    ),
      .RV32E                (RV32E               ),
      .RV32M                (RV32M               ),
      .RV32B                (RV32B               ),
      .RV32ZC               (RV32ZC              ),
      .RegFile              (RegFile             ),
      .BranchTargetALU      (BranchTargetALU     ),
      .WritebackStage       (WritebackStage      ),
      .ICache               (ICache              ),
      .ICacheECC            (ICacheECC           ),
      .ICacheTweakInfection (ICacheTweakInfection),
      .BranchPredictor      (BranchPredictor     ),
      .DbgTriggerEn         (DbgTriggerEn        ),
      .SecureIbex           (SecureIbex          ),
      .LockstepOffset       (LockstepOffset      ),
      .ICacheScramble       (ICacheScramble      ),
      .DmBaseAddr           (32'h00000000        ),
      .DmAddrMask           (32'h00000003        ),
      .DmHaltAddr           (32'h00000000        ),
      .DmExceptionAddr      (32'h00000000        )
    ) u_top (
      .clk_i                     (clk_sys              ),
      .rst_ni                    (rst_sys_n            ),

      .test_en_i                 ('b0                  ),
      .scan_rst_ni               (1'b1                 ),
      .ram_cfg_icache_tag_i      ('b0                  ),
      .ram_cfg_rsp_icache_tag_o  (                     ),
      .ram_cfg_icache_data_i     ('b0                  ),
      .ram_cfg_rsp_icache_data_o (                     ),

      .hart_id_i                 (32'b0                ),
      // First instruction executed is at 0x0 + 0x80
      .boot_addr_i               (32'h00000000         ),

      .instr_req_o               (host_req[CoreI]      ),
      .instr_gnt_i               (host_gnt[CoreI]      ),
      .instr_rvalid_i            (host_rvalid[CoreI]   ),
      .instr_addr_o              (host_addr[CoreI]     ),
      .instr_rdata_i             (host_rdata[CoreI]    ),
      .instr_rdata_intg_i        (ibex_instr_rdata_intg),
      .instr_err_i               (host_err[CoreI]      ),

      .data_req_o                (host_req[CoreD]      ),
      .data_gnt_i                (host_gnt[CoreD]      ),
      .data_rvalid_i             (host_rvalid[CoreD]   ),
      .data_we_o                 (host_we[CoreD]       ),
      .data_be_o                 (host_be[CoreD]       ),
      .data_addr_o               (host_addr[CoreD]     ),
      .data_wdata_o              (host_wdata[CoreD]    ),
      .data_wdata_intg_o         (                     ),
      .data_rdata_i              (host_rdata[CoreD]    ),
      .data_rdata_intg_i         (ibex_data_rdata_intg ),
      .data_err_i                (host_err[CoreD]      ),

      .irq_software_i            (1'b0                 ),
      .irq_timer_i               (1'b0                 ),
      .irq_external_i            (1'b0                 ),
      .irq_fast_i                (15'b0                ),
      .irq_nm_i                  (1'b0                 ),

      .scramble_key_valid_i      ('0                   ),
      .scramble_key_i            ('0                   ),
      .scramble_nonce_i          ('0                   ),
      .scramble_req_o            (                     ),

      .debug_req_i               ('b0                  ),
      .crash_dump_o              (                     ),
      .double_fault_seen_o       (                     ),

      .fetch_enable_i            (ibex_pkg::IbexMuBiOn ),
      .alert_minor_o             (                     ),
      .alert_major_internal_o    (                     ),
      .alert_major_bus_o         (                     ),
      .core_sleep_o              (                     ),

      .lockstep_cmp_en_o         (                     ),

      .data_req_shadow_o         (                     ),
      .data_we_shadow_o          (                     ),
      .data_be_shadow_o          (                     ),
      .data_addr_shadow_o        (                     ),
      .data_wdata_shadow_o       (                     ),
      .data_wdata_intg_shadow_o  (                     ),

      .instr_req_shadow_o        (                     ),
      .instr_addr_shadow_o       (                     )
    );

  // SRAM block for instruction and data storage
  ram_1p #(
      .Depth(RamSizeWords)
    ) u_ram (
      .clk_i    (clk_sys           ),
      .rst_ni   (rst_sys_n         ),
      .req_i    (device_req[Ram]   ),
      .we_i     (device_we[Ram]    ),
      .be_i     (device_be[Ram]    ),
      .addr_i   (device_addr[Ram]  ),
      .wdata_i  (device_wdata[Ram] ),
      .rvalid_o (device_rvalid[Ram]),
      .rdata_o  (device_rdata[Ram] )
    );

  // RISC-V test utility, used by the RISC-V compliance test to interact with
  // the simulator.
  riscv_testutil
    u_riscv_testutil(
      .clk_i         (clk_sys                      ),
      .rst_ni        (rst_sys_n                    ),

      // Device port
      .dev_req_i     (device_req[TestUtilDevice]   ),
      .dev_we_i      (device_we[TestUtilDevice]    ),
      .dev_addr_i    (device_addr[TestUtilDevice]  ),
      .dev_wdata_i   (device_wdata[TestUtilDevice] ),
      .dev_rvalid_o  (device_rvalid[TestUtilDevice]),
      .dev_rdata_o   (device_rdata[TestUtilDevice] ),
      .dev_be_i      (device_be[TestUtilDevice]    ),
      .dev_err_o     (device_err[TestUtilDevice]   ),

      // Host port
      .host_req_o    (host_req[TestUtilHost]       ),
      .host_gnt_i    (host_gnt[TestUtilHost]       ),
      .host_rvalid_i (host_rvalid[TestUtilHost]    ),
      .host_addr_o   (host_addr[TestUtilHost]      ),
      .host_rdata_i  (host_rdata[TestUtilHost]     )
    );

endmodule
