// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_rx_tx_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_rx_tx_vseq)

  `uvm_object_new

  uint total_rd_bytes = 0;

  virtual task host_init();
    super.host_init();

    // diable override
    ral.ovrd.txovrden.set(1'b0);
    csr_update(ral.ovrd);
    // reset and set level of rx and fmt fifos
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fmtilvl)
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rxilvl)
    ral.fifo_ctrl.rxrst.set(1'b1);
    ral.fifo_ctrl.fmtrst.set(1'b1);
    ral.fifo_ctrl.rxilvl.set(rxilvl);
    ral.fifo_ctrl.fmtilvl.set(fmtilvl);
    csr_update(ral.fifo_ctrl);
  endtask : host_init

  virtual task host_send_trans(int num_trans);
    bit last_tran;

    // setup config
    force_use_incorrect_config = 1'b0;
    fmt_item = new("fmt_item");
    for (uint cur_tran = 1; cur_tran <= num_trans; cur_tran++) begin
      // re-programming timing registers for the first transaction
      // or when the previous transaction is completed
      if (fmt_item.stop || cur_tran == 1) begin
        `DV_CHECK_RANDOMIZE_FATAL(this)
        get_timing_values();
        program_timing_regs();
      end

      // program address for
      if ((cur_tran == 1'b1) ||                       // first read
          (!fmt_item.read)   ||                       // write trans.
          (fmt_item.read && !fmt_item.rcont)) begin   // non-chained reads
        host_program_target_address();
      end

      last_tran = (cur_tran == num_trans) ? 1'b1 : 1'b0;
      `uvm_info(`gfn, $sformatf("start sending %s transaction %0d/%0d",
          (rw_bit) ? "READ" : "WRITE", cur_tran, num_trans), UVM_DEBUG)
      if (rw_bit) host_read_trans(last_tran);
      else        host_write_trans(last_tran);

      `uvm_info(`gfn, $sformatf("finish sending %s transaction, %0s at the end,  %0d/%0d, ",
          (rw_bit) ? "read" : "write",
          (fmt_item.stop) ? "stop" : "rstart", cur_tran, num_trans), UVM_DEBUG)
      // check a completed transaction is programmed to the host/dut (stop bit must be issued)
      // and check if the host/dut is in idle before allow re-programming the timing registers
      if (fmt_item.stop) begin
        check_host_idle();
      end
    end
  endtask : host_send_trans

  virtual task host_program_target_address();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
      start == 1'b1;
      stop  == 1'b0;
      read  == 1'b0;
      rcont == 1'b0;
    )
    if (cfg.target_addr_mode == Addr7BitMode) begin
      fmt_item.fbyte = (rw_bit) ? {addr[6:0], BusOpRead} : {addr[6:0], BusOpWrite};
    end else begin // Addr10BitMode
      fmt_item.fbyte = (rw_bit) ? {addr[9:0], BusOpRead} : {addr[9:0], BusOpWrite};
    end
    program_format_flag(fmt_item, "host_program_target_address");
  endtask : host_program_target_address

  virtual task host_read_trans(bit last_tran);
    uint real_rd_bytes;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_rd_bytes)
    fork
      begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
          fbyte == num_rd_bytes;
          start == 1'b0;
          read  == 1'b1;
          // for the last write byte of last tran., stop flag must be set to issue stop bit (stimulus end)
          // otherwise, stop can be randomly set/unset to issue stop/rstart bit respectively
          // rcont is derived from stop and read to issue chained/non-chained reads
          stop  == (last_tran) ? 1'b1 : stop;
        )
        `DV_CHECK_EQ(fmt_item.stop | fmt_item.rcont, 1)

        real_rd_bytes = (num_rd_bytes) ? num_rd_bytes : 256;
        total_rd_bytes += real_rd_bytes;
        if (fmt_item.rcont) begin
          `uvm_info(`gfn, "\nTransaction READ with chaining", UVM_DEBUG)
        end else begin
          `uvm_info(`gfn, $sformatf("\nTransaction READ  %0s with ",
              (fmt_item.stop) ? "STOP end, START after" : "RSTART after"), UVM_DEBUG)
        end
        program_format_flag(fmt_item, "program number of bytes to read");
      end
      begin
        if (!cfg.do_rd_overflow) begin
          // if not a chained read, read out data sent over rx_fifo
          while (!fmt_item.rcont && total_rd_bytes > 0) begin
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
      `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
        start == 1'b0;
        read  == 1'b0;
      )
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(wr_data)
      fmt_item.fbyte = wr_data;
      // last write byte of last  tran., stop flag must be set to issue stop bit
      // last write byte of other tran., stop is randomly set/unset to issue stop/rstart bit
      fmt_item.stop = (i != num_wr_bytes) ? 1'b0 : ((last_tran) ? 1'b1 : fmt_item.stop);
      if (i == num_wr_bytes) begin
        `uvm_info(`gfn, $sformatf("\nTransaction WRITE %0s with",
            (fmt_item.stop) ? "STOP end, START after" : "RSTART after"), UVM_DEBUG)
      end
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
