// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package jtag_riscv_agent_pkg;
  // dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import dv_lib_pkg::*;
  import jtag_agent_pkg::*;

  // macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // parameters

  // JTAG TAP for DMI according to debug spec 0.13
  parameter uint DMI_OPW = 2;
  parameter uint DMI_DATAW = 32;
`ifdef USE_DMI_INTERFACE
  parameter uint DMI_ADDRW = 16;
`else
  parameter uint DMI_ADDRW = 7;
`endif
  parameter uint DMI_IRW = 5;
  parameter uint DMI_DRW = DMI_OPW + DMI_DATAW + DMI_ADDRW;
  parameter uint DTMCS_DRW = 32;
  // Bits to shift byte address to word address
  parameter uint DMI_WORD_SHIFT = $clog2(DMI_DATAW / 8);

  uint default_jtag_timeout = 10_000_000;
  string msg_id = "jtag_riscv_agent_pkg";

  // local types
  typedef enum logic [DMI_IRW-1:0] {
    JtagBypass0   = 'h0,
    JtagIdcode    = 'h1,
    JtagDtmCsr    = 'h10,
    JtagDmiAccess = 'h11,
    JtagBypass1   = 'h1f
  } jtag_ir_e;

  typedef enum logic [DMI_OPW-1:0] {
    DmiNoErr      = 'h0,
    DmiReserved   = 'h1,
    DmiFail       = 'h2,
    DmiInProgress = 'h3
  } jtag_op_status_e;

  typedef enum logic [DMI_OPW-1:0] {
    DmiStatus = 'h0,
    DmiRead   = 'h1,
    DmiWrite  = 'h2
  } jtag_op_e;

  typedef enum bit [4:0] {
    DmiReset     = 16,
    DmiHardReset = 17
  } jtag_dtmcs_e;

  typedef enum bit [7:0] {
    DmControl  = 8'h10,
    Sbcs       = 8'h38,
    SbAddress0 = 8'h39,
    SbData0    = 8'h3C
  } jtag_dm_csr_e;

  typedef enum bit [4:0] {
    SbAccess32   = 'd2,
    SbAccess     = 'd17,
    SbReadOnAddr = 'd20,
    SbBusy       = 'd21
  } sbcs_field_e;

  // forward declare classes to allow typedefs below
  typedef class jtag_riscv_item;
  typedef class jtag_riscv_agent_cfg;

  // package sources
  `include "jtag_riscv_item.sv"
  `include "jtag_riscv_agent_cfg.sv"
  `include "jtag_riscv_agent_cov.sv"
  `include "jtag_riscv_reg_adapter.sv"
  `include "jtag_riscv_monitor.sv"
  `include "jtag_riscv_driver.sv"
  `include "jtag_riscv_sequencer.sv"
  `include "jtag_riscv_agent.sv"
  `include "jtag_riscv_seq_list.sv"

  task automatic jtag_read_csr(bit [bus_params_pkg::BUS_AW-1:0] csr_addr,
                               jtag_riscv_sequencer seqr,
                               output bit [bus_params_pkg::BUS_DW-1:0] csr_val);
    jtag_riscv_csr_seq jtag_csr_seq = jtag_riscv_csr_seq::type_id::create("jtag_csr_seq");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jtag_csr_seq, addr == csr_addr; do_write == 0;,, msg_id)
    jtag_csr_seq.start(seqr);
    csr_val = jtag_csr_seq.data;
  endtask

  task automatic jtag_write_csr(bit [bus_params_pkg::BUS_AW-1:0] csr_addr,
                                jtag_riscv_sequencer             seqr,
                                bit [bus_params_pkg::BUS_DW-1:0] csr_val);
    jtag_riscv_csr_seq jtag_csr_seq = jtag_riscv_csr_seq::type_id::create("jtag_csr_seq");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(jtag_csr_seq, addr == csr_addr; do_write == 1; data == csr_val;,
                                   , msg_id)
    jtag_csr_seq.start(seqr);
  endtask

  // spin on a jtag csr read until expected value is matched
  task automatic jtag_csr_spinwait(bit [bus_params_pkg::BUS_AW-1:0] csr_addr,
    jtag_riscv_sequencer seqr,
    bit [bus_params_pkg::BUS_DW-1:0] exp_data,
    uint timeout_ns = 1000);

    `uvm_info(msg_id, $sformatf("timeout is %d ns", timeout_ns), UVM_MEDIUM)

    fork
      begin : isolation_fork
        bit [bus_params_pkg::BUS_DW-1:0] prev_read_data = 0;
        bit [bus_params_pkg::BUS_DW-1:0] read_data = ~exp_data;

        fork
          while (read_data != exp_data) begin
            jtag_read_csr(csr_addr,
            seqr,
            read_data);

            if (prev_read_data != read_data) begin
              `uvm_info(msg_id, $sformatf("addr: 0x%0h, data: 0x%0h",
                                             csr_addr, read_data), UVM_LOW)
              prev_read_data = read_data;
            end
          end
          begin
            `DV_WAIT_TIMEOUT(timeout_ns, msg_id, $sformatf("timeout (addr=0x%0h) == 0x%0h",
                csr_addr, exp_data))
          end
        join_any
        disable fork;
      end : isolation_fork
    join
  endtask


endpackage: jtag_riscv_agent_pkg
