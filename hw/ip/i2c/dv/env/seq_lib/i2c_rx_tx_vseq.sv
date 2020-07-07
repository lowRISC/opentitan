// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_rx_tx_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_rx_tx_vseq)

  `uvm_object_new

  uint total_rd_bytes = 0;

  virtual task host_send_trans(int num_trans, string trans_type = "");
    bit last_tran;

    fmt_item = new("fmt_item");
    for (uint cur_tran = 1; cur_tran <= num_trans; cur_tran++) begin
      // re-programming timing registers for the first transaction
      // or when the previous transaction is completed
      if (fmt_item.stop || cur_tran == 1) begin
        under_program_regs = 1'b1;
        `DV_CHECK_RANDOMIZE_FATAL(this)
        // if trans_type is not empty (default), then rw_bit is overrided
        // otherwise, rw_bit is randomized
        rw_bit = (trans_type  == "WriteOnly") ? 1'b0 :
                 ((trans_type == "ReadOnly")  ? 1'b1 : rw_bit);
        get_timing_values();
        program_registers();
        under_program_regs = 1'b0;
      end

      // program address for folowing transaction types
      if ((cur_tran == 1'b1) ||                       // first read transaction
          (!fmt_item.read)   ||                       // write transactions
          (fmt_item.read && !fmt_item.rcont)) begin   // non-chained read transactions
        host_program_target_address();
      end

      last_tran = (cur_tran == num_trans);
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
    bit rxfull = 1'b0;

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
          `uvm_info(`gfn, "\nTransaction READ is chained with next READ transaction", UVM_DEBUG)
        end else begin
          `uvm_info(`gfn, $sformatf("\nTransaction READ ended %0s", (fmt_item.stop) ?
              "with STOP, next transaction should begin with START" :
              "without STOP, next transaction should begin with RSTART"), UVM_DEBUG)
        end
        program_format_flag(fmt_item, "program number of bytes to read");
      end
      begin
        do begin
          csr_rd(.ptr(ral.status.rxfull), .value(rxfull));
          // if delay_read_rx_until_full is unset, rx_fifo is quickly filled up to full
          // so watermark/overflow interrupt could be deterministically triggered
          // if delay_read_rx_until_full is set or rx_fifo is full, start reading data
          if (delay_read_rx_until_full || rxfull) begin
            // if not a chained read, read out data sent over rx_fifo
            while (!fmt_item.rcont && total_rd_bytes > 0) begin
              csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0));
              `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
              cfg.clk_rst_vif.wait_clks(rx_fifo_access_dly);
              csr_rd(.ptr(ral.rdata), .value(rd_data));
              total_rd_bytes--;
            end
          end
        end while (!delay_read_rx_until_full && !rxfull);
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
        `uvm_info(`gfn, $sformatf("\nTransaction WRITE ended %0s", (fmt_item.stop) ?
            "with STOP, next transaction should begin with START" :
            "without STOP, next transaction should begin with RSTART"), UVM_DEBUG)
      end
      program_format_flag(fmt_item, "host_write_trans");
    end
  endtask : host_write_trans

  // read interrupts and randomly clear interrupts if set
  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_state, intr_clear;

    // read interrupt
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // clear interrupt if it is set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intr_clear,
                                       foreach (intr_clear[i]) {
                                           intr_state[i] -> intr_clear[i] == 1;
                                       })

    if (bit'(get_field_val(ral.intr_state.fmt_watermark, intr_clear))) begin
      `uvm_info(`gfn, "\nClearing fmt_watermark", UVM_DEBUG)
    end
    if (bit'(get_field_val(ral.intr_state.rx_watermark, intr_clear))) begin
      `uvm_info(`gfn, "\nClearing rx_watermark", UVM_DEBUG)
    end

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(access_intr_dly)
    cfg.clk_rst_vif.wait_clks(access_intr_dly);
    csr_wr(.csr(ral.intr_state), .value(intr_clear));
  endtask : process_interrupts

  // TODO: This task could be extended along with V2 test development
  virtual task clear_interrupt(i2c_intr_e intr, bit verify_clear = 1'b1);
    csr_wr(.csr(ral.intr_state), .value(1 << intr));
    if (verify_clear) begin
      case (intr)
        FmtWatermark: csr_spinwait(.ptr(ral.intr_state.fmt_watermark), .exp_data(1'b0));
        RxWatermark:  csr_spinwait(.ptr(ral.intr_state.rx_watermark), .exp_data(1'b0));
        default: `uvm_fatal(`gfn, "Invalid intr input")
      endcase
    end
  endtask : clear_interrupt

  virtual task post_start();
    do_dut_shutdown = 0;
    // TODO: tempraly disable the execution of clear_all_interrupt task due to
    // incorrecly assertions of sda_interference and scl_interference (to be fixed with other PR)
    //super.post_start();
  endtask : post_start

endclass : i2c_rx_tx_vseq
