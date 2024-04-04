// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class i2c_rx_tx_vseq extends i2c_base_vseq;
  `uvm_object_utils(i2c_rx_tx_vseq)
  `uvm_object_new

  local bit complete_program_fmt_fifo;
  local uint total_rd_bytes;

  virtual task body();
    bit do_interrupt = 1'b1;
    initialization();
    `uvm_info(`gfn, "\n--> start of sequence", UVM_DEBUG)
    fork
      begin
        while (!cfg.under_reset && do_interrupt) process_interrupts();
      end
      begin
        host_send_trans(.max_trans(num_trans));
        do_interrupt = 1'b0; // gracefully stop process_interrupts
      end
    join
    `uvm_info(`gfn, "\n--> end of sequence", UVM_DEBUG)
  endtask : body

  virtual task host_send_trans(int max_trans = num_trans, tran_type_e trans_type = ReadWrite,
                               bit read = 1'b1, bit stopbyte = 1'b0);
    bit last_tran, chained_read;

    fmt_item = new("fmt_item");
    total_rd_bytes = 0;
    `uvm_info(`gfn, "\n  host_send_trans task running ...", UVM_DEBUG)
    fork
      begin
        complete_program_fmt_fifo = 1'b0;
        for (uint cur_tran = 1; cur_tran <= max_trans; cur_tran++) begin
          // randomize knobs for error interrupts
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(prob_sda_unstable)
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(prob_sda_interference)
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(prob_scl_interference)

          // re-programming timing registers for the first transaction
          // or when the previous transaction is completed
          if (fmt_item.stop || cur_tran == 1) begin
            `DV_CHECK_RANDOMIZE_FATAL(this)
            // if trans_type is provided, then rw_bit is overridden
            // otherwise, rw_bit is randomized
            rw_bit = (trans_type  == WriteOnly) ? 1'b0 :
                     ((trans_type == ReadOnly)  ? 1'b1 : rw_bit);
            get_timing_values();
            program_registers();
          end

          // if trans_type is provided, then rw_bit is overridden
          // otherwise, rw_bit is randomized
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rw_bit)
          rw_bit = (trans_type  == WriteOnly) ? 1'b0 :
                   ((trans_type == ReadOnly)  ? 1'b1 : rw_bit);
          // program address for folowing transaction types
          chained_read = fmt_item.read && fmt_item.rcont;
          if ((cur_tran == 1'b1) ||  // first read transaction
              (!fmt_item.read)   ||  // write transactions
              (!chained_read)) begin // non-chained read transactions
            program_address_to_target();
          end

          last_tran = (cur_tran == max_trans);
          `uvm_info(`gfn, $sformatf("\n  start sending %s transaction %0d/%0d",
              (rw_bit) ? "READ" : "WRITE", cur_tran, max_trans), UVM_MEDIUM)
          if (chained_read) begin
            // keep programming chained read transaction
            program_control_read_to_target(last_tran);
          end else begin
            if (rw_bit) program_control_read_to_target(last_tran);
            else        program_write_data_to_target(last_tran,stopbyte);
          end

          `uvm_info(`gfn, $sformatf("\n  finish sending %s transaction, %0s at the end, %0d/%0d, ",
              (rw_bit) ? "read" : "write",
              (fmt_item.stop) ? "stop" : "rstart", cur_tran, max_trans), UVM_MEDIUM)

          // check a completed transaction is programmed to the host/dut (stop bit must be issued)
          // and check if the host/dut is in idle before allow re-programming the timing registers
          if (fmt_item.stop) begin
            wait_for_reprogram_registers();
          end
        end // for (uint cur_tran = 1; cur_tran <= max_trans; cur_tran++)
        complete_program_fmt_fifo = 1'b1;
      end
      if (read) begin
        read_data_from_target();
        `uvm_info(`gfn, "\n  read_data_from_target task ended", UVM_DEBUG)
      end
    join
    wait_host_for_idle();
    `uvm_info(`gfn, "\n  host_send_trans task ended", UVM_DEBUG)
  endtask : host_send_trans

  virtual task program_address_to_target();
    `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
      start == 1'b1;
      stop  == 1'b0;
      read  == 1'b0;
      rcont == 1'b0;
    )
    if (cfg.target_addr_mode == Addr7BitMode) begin
      fmt_item.fbyte = {addr[6:0], rw_bit};
    end else begin // Addr10BitMode
      fmt_item.fbyte = {addr[9:0], rw_bit};
    end
    `uvm_info(`gfn, $sformatf("\nprogram, %s address %x",
        fmt_item.fbyte[0] ? "read" : "write", fmt_item.fbyte[7:1]), UVM_DEBUG)
    program_format_flag(fmt_item, "  program_address_to_target", 1);
  endtask : program_address_to_target

  virtual task program_control_read_to_target(bit last_tran);
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_rd_bytes)
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
    `uvm_info(`gfn, $sformatf("\n  read transaction length is %0d byte",
        num_rd_bytes ? num_rd_bytes : 256), UVM_DEBUG)

    // accumulate number of read byte
    total_rd_bytes += (num_rd_bytes) ? num_rd_bytes : 256;
    // decrement total_rd_bytes since one data is must be dropped in fifo_overflow test
    if (cfg.seq_cfg.en_rx_overflow) total_rd_bytes--;
    `uvm_info(`gfn, $sformatf("\n  program_control_read_to_target, read %0d byte",
        total_rd_bytes), UVM_DEBUG)

    if (fmt_item.rcont) begin
      `uvm_info(`gfn, "\n  transaction READ is chained with next READ transaction", UVM_DEBUG)
    end else begin
      `uvm_info(`gfn, $sformatf("\n  transaction READ ended %0s", (fmt_item.stop) ?
          "with STOP, next transaction should begin with START" :
          "without STOP, next transaction should begin with RSTART"), UVM_DEBUG)
    end
    program_format_flag(fmt_item, "  program number of bytes to read", 0);
  endtask : program_control_read_to_target

  virtual task read_data_from_target();
    bit rx_smoke, rx_full, rx_overflow, rx_threshold, rx_empty, start_read;

    // if not a chained read, read out data sent over rx_fifo
    rx_overflow  = 1'b0;
    rx_threshold = 1'b0;
    while (!cfg.under_reset && (!complete_program_fmt_fifo || total_rd_bytes > 0)) begin
      rx_smoke    = !cfg.seq_cfg.en_rx_threshold & !cfg.seq_cfg.en_rx_overflow;
      rx_overflow |= (cfg.seq_cfg.en_rx_overflow  & cfg.intr_vif.pins[RxOverflow]);
      if (cfg.seq_cfg.en_rx_threshold) begin
        csr_rd(.ptr(ral.status.rxfull), .value(rx_full));
        rx_threshold |= (cfg.seq_cfg.en_rx_threshold & rx_full);
      end
      start_read = rx_smoke     | // read rx_fifo if there is valid data
                   rx_threshold | // read rx_fifo after full (ensure intr rx_threshold asserted)
                   rx_overflow;   // read rx_fifo after overflow (ensure intr_rx_overflow asserted)
      if (start_read) begin
        csr_rd(.ptr(ral.status.rxempty), .value(rx_empty));
        if (!rx_empty) begin
          csr_rd(.ptr(ral.rdata), .value(rd_data));
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
          cfg.clk_rst_vif.wait_clks(rx_fifo_access_dly);
          `uvm_info(`gfn, $sformatf("\n  read byte %0d  %x", total_rd_bytes, rd_data), UVM_DEBUG)
          total_rd_bytes--;
        end
      end
      // avoid non-bloking time
      if (!cfg.seq_cfg.en_rx_threshold && !start_read) begin
        cfg.clk_rst_vif.wait_clks(1);
      end
    end
  endtask : read_data_from_target

  virtual task program_write_data_to_target(bit last_tran, bit stopbyte);
    bit [7:0] wr_data[$];
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(num_wr_bytes)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wr_data, wr_data.size == num_wr_bytes;)
    if (num_wr_bytes == 256) begin
      `uvm_info(`gfn, "\n  write transaction length is 256 byte", UVM_DEBUG)
    end
    print_host_wr_data(wr_data);

    for (int i = 1; i <= num_wr_bytes; i++) begin
      // randomize until at least one of format bits is non-zero to ensure
      // data format will be pushed into fmt_fifo (if not empty)
      do begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(fmt_item,
          start == 1'b0;
          read  == 1'b0;
        )
        if (stopbyte && (i == num_wr_bytes)) begin
        fmt_item.fbyte = 8'hee;
        end else begin
        fmt_item.fbyte = wr_data[i - 1];
        end
      end while (!fmt_item.nakok && !fmt_item.rcont && !fmt_item.fbyte);

      // last write byte of last  tran., stop flag must be set to issue stop bit
      // last write byte of other tran., stop is randomly set/unset to issue stop/rstart bit
      fmt_item.stop = (i != num_wr_bytes) ? 1'b0 : ((last_tran) ? 1'b1 : fmt_item.stop);
      if (i == num_wr_bytes) begin
        `uvm_info(`gfn, $sformatf("\n  transaction WRITE ended %0s", (fmt_item.stop) ?
            "with STOP, next transaction should begin with START" :
            "without STOP, next transaction should begin with RSTART"), UVM_MEDIUM)
      end
      program_format_flag(fmt_item, "program_write_data_to_target", 1);
    end
  endtask : program_write_data_to_target

endclass : i2c_rx_tx_vseq
