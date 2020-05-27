// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_rx_tx_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_rx_tx_vseq)

  `uvm_object_new

  virtual task host_init();
    bit             fmtrst,  rxrst;
    bit [1:0]       fmtilvl, rxilvl;
    bit [TL_DW-1:0] reg_val;

    super.host_init();
    // diable override
    ral.ovrd.txovrden.set(1'b0);
    csr_update(ral.ovrd);
    // reset and set level of rx and fmt fifos
    rxrst   = 1'b1;
    fmtrst  = 1'b1;
    rxilvl  = 2'd3;
    fmtilvl = 2'd3;
    reg_val = {24'd0, fmtilvl, rxilvl, fmtrst, rxrst};
    csr_wr(.csr(ral.fifo_ctrl), .value(reg_val));
  endtask : host_init

  virtual task host_send_trans(int num_trans);
    bit   last_tran;

    // setup config
    force_use_incorrect_config = 1'b0;
    fmt_item = new("fmt_item");
    `DV_CHECK_RANDOMIZE_FATAL(this)
    get_timing_values();
    program_timing_regs();

    for (uint cur_tran = 1; cur_tran <= num_trans; cur_tran++) begin
      last_tran = (cur_tran == num_trans) ? 1'b1 : 1'b0;
      // not program address for chained reads
      host_program_target_address();
      `uvm_info(`gfn, $sformatf("start sending %s transaction %0d/%0d",
          (rw_bit) ? "READ" : "WRITE", cur_tran, num_trans), UVM_DEBUG)
      if (rw_bit) host_read_trans(last_tran);
      else        host_write_trans(last_tran);
      `uvm_info(`gfn, $sformatf("finish sending %s transaction, %0s at the end,  %0d/%0d, ",
          (rw_bit) ? "read" : "write",
          (fmt_item.stop) ? "stop" : "rstart", cur_tran, num_trans), UVM_DEBUG)
    end
  endtask : host_send_trans

  virtual task host_program_target_address();
    // programm fmt flags for address
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_item)
    fmt_item.start = 1'b1;
    fmt_item.stop  = 1'b0;
    fmt_item.read  = 1'b0;
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(addr)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rw_bit)
    fmt_item.fbyte = (rw_bit) ? {addr, BusOpRead} : {addr, BusOpWrite};
    program_format_flag(fmt_item, "host_program_target_address");
  endtask : host_program_target_address

  virtual task host_read_trans(bit last_tran);
    uint real_rd_bytes;
    uint total_rd_bytes = 0;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_rd_bytes)
    fork
      begin
        `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_item)
        fmt_item.fbyte = num_rd_bytes;
        fmt_item.start = 1'b0;
        fmt_item.read  = 1'b1;
        fmt_item.rcont = 1'b0; // TODO: no chained read support
        // for the last write byte of last tran., stop flag must be set to issue stop bit (stimulus end)
        // otherwise, stop can be randomly set/unset to issue stop/rstart bit respectively
        fmt_item.stop  = (last_tran) ? 1'b1 : $urandom_range(0, 1);
        real_rd_bytes = (num_rd_bytes) ? num_rd_bytes : 256;
        total_rd_bytes += real_rd_bytes;
        program_format_flag(fmt_item, "program number of bytes to read");
      end
      begin
        if (!cfg.do_rd_overflow) begin
          while (total_rd_bytes > 0) begin
            csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0));
            csr_rd(.ptr(ral.rdata), .value(rd_data));
            total_rd_bytes--;
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
            cfg.m_i2c_agent_cfg.vif.wait_for_dly(rx_fifo_access_dly);
          end
        end
      end
    join
  endtask : host_read_trans

  virtual task host_write_trans(bit last_tran);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_wr_bytes)
    for (int i = 1; i <= num_wr_bytes; i++) begin
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmt_item)
      fmt_item.start = 1'b0;
      fmt_item.read  = 1'b0;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      fmt_item.fbyte = wr_data;
      // last write byte of last  tran., stop flag must be set to issue stop bit
      // last write byte of other tran., stop is randomly set/unset to issue stop/rstart bit
      fmt_item.stop  = (i != num_wr_bytes) ? 1'b0 : ((last_tran) ? 1'b1 : fmt_item.stop);
      program_format_flag(fmt_item, "host_write_trans");
    end
  endtask : host_write_trans

  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_status, clear_intr;
    bit             clear_rx_intr, clear_tx_intr;

    csr_rd(.ptr(ral.intr_state), .value(intr_status));
    `uvm_info(`gfn, $sformatf("intr_state 0x%08h", intr_status), UVM_HIGH)
    // TODO: interrupts must be properly handled before EoT
  endtask : process_interrupts

  virtual task post_start();
    bit [TL_DW-1:0] intr_status;

    do_dut_shutdown = 0;
    super.post_start();
  endtask : post_start

endclass : i2c_rx_tx_vseq
