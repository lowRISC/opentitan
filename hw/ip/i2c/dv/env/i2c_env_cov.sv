// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Covergroup for I2C interrupts with interrupt enable and interrupt test
covergroup i2c_interrupts_cg with function sample(
  bit [14:0] intr_state,
  bit [14:0] intr_enable,
  bit [14:0] intr_test
  );
  option.per_instance = 1;

  // host            mode interrupt: raised when the FMT FIFO depth is less than the low threshold.
  cp_fmt_threshold    : coverpoint intr_state[ 0] iff (intr_enable[ 0]);
  // host            mode interrupt: raised if the RX FIFO is greater than the high threshold.
  cp_rx_threshold     : coverpoint intr_state[ 1] iff (intr_enable[ 1]);
  //          target mode interrupt: raised if the ACQ FIFO depth is greater than the high threshold.
  cp_acq_threshold    : coverpoint intr_state[ 2] iff (intr_enable[ 2]);
  // host            mode interrupt: raised if the RX FIFO has overflowed.
  cp_rx_overflow      : coverpoint intr_state[ 3] iff (intr_enable[ 3]);
  // host            mode interrupt: raised if there is no ACK in response to an address or data
  //                                 write.
  cp_nak              : coverpoint intr_state[ 4] iff (intr_enable[ 4]);
  // host            mode interrupt: raised if the SCL line drops early (not supported without
  //                                 clock synchronization).
  cp_scl_interference : coverpoint intr_state[ 5] iff (intr_enable[ 5]);
  // host            mode interrupt: raised if the SDA line goes low when host is trying to assert
  //                                 high.
  cp_sda_interference : coverpoint intr_state[ 6] iff (intr_enable[ 6]);
  // host            mode interrupt: raised if target stretches the clock beyond the allowed
  //                                 timeout period.
  cp_stretch_timeout  : coverpoint intr_state[ 7] iff (intr_enable[ 7]);
  // host            mode interrupt: raised if the target does not assert a constant value of SDA
  //                                 during transmission.
  cp_sda_unstable     : coverpoint intr_state[ 8] iff (intr_enable[ 8]);
  // host and target mode interrupt: in host mode, raised if the host issues a repated START or
  //                                 terminates the transaction by issuing STOP.
  cp_cmd_complete     : coverpoint intr_state[ 9] iff (intr_enable[ 9]);
  //          target mode interrupt: raised if the target is stretching clocks for a read command.
  //                                 This is a level status interrupt.
  cp_tx_stretch       : coverpoint intr_state[10] iff (intr_enable[10]);
  //          target mode interrupt: raised if TX FIFO depth is less than the low threshold.
  cp_tx_threshold     : coverpoint intr_state[11] iff (intr_enable[11]);
  //          target mode interrupt: raised if ACQ FIFO becomes full. This is a level status
  //                                 interrupt.
  cp_acq_full         : coverpoint intr_state[12] iff (intr_enable[12]);
  //          target mode interrupt: raised if STOP is received without a preceding NACK during an
  //                                 external host read.
  cp_unexp_stop       : coverpoint intr_state[13] iff (intr_enable[13]);
  //          target mode interrupt: raised if the host stops sending the clock during an ongoing
  //                                 transaction.
  cp_host_timeout     : coverpoint intr_state[14] iff (intr_enable[14]);

  cp_fmt_threshold_test    : coverpoint intr_state[ 0] iff (intr_test[ 0]){ ignore_bins dis = {0}; }
  cp_rx_threshold_test     : coverpoint intr_state[ 1] iff (intr_test[ 1]){ ignore_bins dis = {0}; }
  cp_acq_threshold_test    : coverpoint intr_state[ 2] iff (intr_test[ 2]){ ignore_bins dis = {0}; }
  cp_rx_overflow_test      : coverpoint intr_state[ 3] iff (intr_test[ 3]){ ignore_bins dis = {0}; }
  cp_nak_test              : coverpoint intr_state[ 4] iff (intr_test[ 4]){ ignore_bins dis = {0}; }
  cp_scl_interference_test : coverpoint intr_state[ 5] iff (intr_test[ 5]){ ignore_bins dis = {0}; }
  cp_sda_interference_test : coverpoint intr_state[ 6] iff (intr_test[ 6]){ ignore_bins dis = {0}; }
  cp_stretch_timeout_test  : coverpoint intr_state[ 7] iff (intr_test[ 7]){ ignore_bins dis = {0}; }
  cp_sda_unstable_test     : coverpoint intr_state[ 8] iff (intr_test[ 8]){ ignore_bins dis = {0}; }
  cp_cmd_complete_test     : coverpoint intr_state[ 9] iff (intr_test[ 9]){ ignore_bins dis = {0}; }
  cp_tx_stretch_test       : coverpoint intr_state[10] iff (intr_test[10]){ ignore_bins dis = {0}; }
  cp_tx_threshold_test     : coverpoint intr_state[11] iff (intr_test[11]){ ignore_bins dis = {0}; }
  cp_acq_full_test         : coverpoint intr_state[12] iff (intr_test[12]){ ignore_bins dis = {0}; }
  cp_unexp_stop_test       : coverpoint intr_state[13] iff (intr_test[13]){ ignore_bins dis = {0}; }
  cp_host_timeout_test     : coverpoint intr_state[14] iff (intr_test[14]){ ignore_bins dis = {0}; }
endgroup

covergroup i2c_fifo_reset_cg with function sample(
  bit fmtrst,
  bit rxrst,
  bit acqrst,
  bit txrst,
  bit fmt_threshold,
  bit rx_threshold,
  bit acq_threshold,
  bit rx_overflow,
  bit acq_overflow,
  bit tx_threshold
);
  cp_fmtrst : coverpoint fmtrst;
  cp_rxrst : coverpoint rxrst;
  cp_acqrst : coverpoint acqrst;
  cp_txrst : coverpoint txrst;
  cp_fmt_threshold : coverpoint fmt_threshold;
  cp_rx_threshold : coverpoint rx_threshold;
  cp_acq_threshold : coverpoint acq_threshold;
  cp_rx_overflow : coverpoint rx_overflow;
  cp_acq_overflow : coverpoint acq_overflow;
  cp_tx_threshold : coverpoint tx_threshold;
  cp_fmt_threshold_cross : cross cp_fmt_threshold, cp_fmtrst;
  cp_rx_threshold_cross : cross cp_rx_threshold, cp_rxrst;
  cp_acq_threshold_cross : cross cp_acq_threshold, cp_fmtrst;
  cp_rx_overflow_cross : cross cp_rx_overflow, cp_rxrst;
  cp_acq_overflow_cross : cross cp_acq_overflow, cp_acqrst;
  cp_tx_threshold_cross : cross cp_tx_threshold, cp_txrst;
endgroup

covergroup i2c_fifo_level_cg (uint fifo_depth)
  with function sample(int fifolvl, bit irq, bit rst);
  option.per_instance = 1;

  cp_rst: coverpoint rst;
  cp_irq: coverpoint irq;
  cp_fifolvl: coverpoint fifolvl {
    bins lvl[] = {1, 4, 8, 16};
    bins others = {[0:fifo_depth]} with (!(item inside {1, 4, 8, 16}));
  }
  cp_fifo_threshold_cross : cross cp_fifolvl, cp_irq {
    ignore_bins reserved_values = binsof(cp_fifolvl.others);
  }
endgroup : i2c_fifo_level_cg

covergroup i2c_operating_mode_cg
  with function sample(bit ip_mode, bit tb_mode, int scl_frequency);
  option.per_instance = 1;

  cp_ip_mode : coverpoint ip_mode{
    bins host = {1'b1};
    bins target = {1'b0};
  }
  cp_tb_mode : coverpoint tb_mode{
    bins host = {1'b1};
    bins target = {1'b0};
  }
  cp_mode_cross : cross ip_mode, tb_mode {
    ignore_bins both_host   = binsof(ip_mode) intersect {1} && binsof(tb_mode) intersect {1};
    ignore_bins both_target = binsof(ip_mode) intersect {0} && binsof(tb_mode) intersect {0};
    bins dut_host_tb_target = binsof(ip_mode) intersect {1} && binsof(tb_mode) intersect {0};
    bins dut_target_tb_host = binsof(ip_mode) intersect {0} && binsof(tb_mode) intersect {1};
  }
  cp_scl_frequency : coverpoint scl_frequency{
    bins standard_mode[2]  = { 100, [  0: 99]};
    bins fast_mode[2]      = { 400, [101:399]};
    bins fast_plus_mode[2] = {1000, [401:999]};
  }
  cp_ip_mode_x_frequency: cross cp_ip_mode, cp_scl_frequency;
endgroup


covergroup i2c_status_cg
  with function sample(
    bit fmtfull,
    bit rxfull,
    bit fmtempty,
    bit hostidle,
    bit targetidle,
    bit rxempty,
    bit txfull,
    bit acqfull,
    bit txempty,
    bit acqempty
  );
  option.per_instance = 1;

  cp_fmtfull    : coverpoint fmtfull;
  cp_rxfull     : coverpoint rxfull;
  cp_fmtempty   : coverpoint fmtempty;
  cp_hostidle   : coverpoint hostidle;
  cp_targetidle : coverpoint targetidle;
  cp_rxempty    : coverpoint rxempty;
  cp_txfull     : coverpoint txfull;
  cp_acqfull    : coverpoint acqfull;
  cp_txempty    : coverpoint txempty;
  cp_acqempty   : coverpoint acqempty;
endgroup : i2c_status_cg

covergroup i2c_scl_sda_override_cg
  with function sample(bit txovrden, bit sclval, bit sdaval);
  option.per_instance = 1;

  cp_txorvden : coverpoint txovrden;
  cp_sclval   : coverpoint sclval;
  cp_sdaval   : coverpoint sdaval;
  cp_txorvden_x_sclval : cross cp_txorvden, cp_sclval;
  cp_txorvden_x_sdaval : cross cp_txorvden, cp_sdaval;
endgroup : i2c_scl_sda_override_cg

// The 'format FIFO' controls the HWIP state-machine in HOST-mode, where the
// transaction to be enacted is specified by a series of 1-byte+5-bit
// packets in the FIFO. Each entry in the 'format FIFO' may part of a larger
// transaction, chained together by using the RCONT bit.
covergroup i2c_fmt_fifo_cg
with function sample(bit[7:0] fbyte, bit start, bit stop, bit read, bit rcont, bit nakok,
                     bit ack_int_recv);
  option.per_instance = 1;

  cp_fbyte : coverpoint fbyte {
    bins all_zero = {8'h00};
    bins sml      = {[  8'd1: 8'd100]};
    bins med      = {[8'd101: 8'd200]};
    bins high     = {[8'd201: 8'd254]};
    bins all_ones = {8'hFF};
  }
  cp_start : coverpoint start;
  cp_stop  : coverpoint stop;
  cp_read  : coverpoint read;
  cp_rcont : coverpoint rcont;
  cp_nakok : coverpoint nakok;
  cp_ack : coverpoint ack_int_recv {
    bins ack = {1'b1};
    bins nack = {1'b0};
  }
  cp_fbyte_X_start_X_stop_X_read_X_rcont_X_nakok_X_ack :
    cross cp_fbyte, start, stop, read, rcont, nakok, cp_ack
  {
    bins data_byte = binsof(start) intersect {0} &&
                     binsof(stop) intersect {0} &&
                     binsof(read) intersect {0} &&
                     binsof(rcont) intersect {0} &&
                     binsof(nakok) intersect {0};
    bins write_address_byte = binsof(start) intersect {1} &&
                              binsof(read) intersect {0};
    bins read_address_byte = binsof(start) intersect {1} &&
                             binsof(read) intersect {1};
    bins read_with_ack = binsof(read) intersect {1} &&
                         binsof(rcont) intersect {1};
    bins read_with_nack = binsof(read) intersect {1} &&
                          binsof(rcont) intersect {0};
    bins stop_byte = binsof(stop) intersect {1};
    bins stop_after_start = binsof(stop) intersect {1} &&
                            binsof(start) intersect {1};
    bins write_address_byte_nak = binsof(start) intersect {1} &&
                                  binsof(cp_ack) intersect {0};
    bins data_byte_nack = binsof(cp_ack) intersect {0};
    bins stop_byte_nack = binsof(stop) intersect {1} &&
                          binsof(cp_ack) intersect {0};
    bins nakok_byte_nack = binsof(nakok) intersect {1} &&
                           binsof(cp_ack) intersect {0};
    bins nakok_addr_byte_nack = binsof(start) intersect {1} &&
                                binsof(nakok) intersect {1} &&
                                binsof(cp_ack) intersect {0};
  }

endgroup : i2c_fmt_fifo_cg

// (TARGET/DEVICE mode) ACQDATA : I2C target acquired data
// This register is populated with data + formatting information about the
// previously-received byte from the host.
// rw_ack_nack(abyte[0]) -> indicates R/W bit for adress bytes
//                       -> indicates ACK/NACK bit for RSTART or STOP
covergroup i2c_acq_fifo_cg
  with function sample(bit[6:0] abyte, bit rw_ack_nack, bit[1:0] signal);
  option.per_instance = 1;

  cp_abyte : coverpoint {abyte, rw_ack_nack} {
    bins all_zero = {8'h00};
    bins sml      = {[8'd1: 8'd100]};
    bins med      = {[8'd101: 8'd200]};
    bins high     = {[8'd201: 8'd254]};
    bins all_ones = {8'hFF};
  }
  cp_action : coverpoint signal {
                         // 'signal'/'format_flags' encoding
    bins none = {2'b00};   // No START or STOP: 00
    bins stop = {2'b10};   //             STOP: 10
    bins start = {2'b01};  //            START: 01
    bins rstart = {2'b11}; //   repeated START: 11
  }
  cp_request_type: coverpoint rw_ack_nack iff (signal == 2'b01){
    bins read = {1'b1};
    bins write = {1'b0};
  }
  cp_abyte_X_cp_action : cross cp_abyte, cp_action {
    bins write_address_byte = binsof(cp_action.start);
    bins read_address_byte = binsof(cp_action.start);
    bins data_byte = binsof(cp_action.none);
  }
  // Cover different combinations of Read request terminations in target mode
  // `abyte[0]` format flag encodings for termination of read request
  //  0 -> ACK
  //  1 -> NACK
  cp_target_read_ack_nack: coverpoint {signal, rw_ack_nack} {
                                    // Read request start   // request termination
    bins read_req_ack_before_stop    = ({2'b01, 1'b1} => {2'b10, 1'b0});
    bins read_req_nack_before_rstart = ({2'b01, 1'b1} => {2'b11, 1'b0});
    // This scenario is not possible to achieve since in target mode, DUT will recieve NACK/ACK
    // from external host.
    // With ACK, SDA will be driven low, but RStart requires SDA transition from high to low
    ignore_bins read_req_ack_before_rstart = ({2'b01, 1'b1} => {2'b11, 1'b0});
    // Similar to above bin, Stop requires SDA low to high transition,
    // but during NACK SDA is driven high
    ignore_bins read_req_nack_before_stop = ({2'b01, 1'b1} => {2'b10, 1'b0});
  }
endgroup : i2c_acq_fifo_cg
// Cover different back to back transactions issued by or received by DUT
// in host and target modes
covergroup i2c_b2b_txn_cg with function sample(bit[7:0] past_addr, bit[7:0] addr, bit en);
     option.per_instance = 1;
     B2B_txn_cp : coverpoint {past_addr[0], addr[0], (past_addr[7:1] != addr[7:1])} iff (en) {
       bins b2b_write_same_addr = {3'b000};
       bins b2b_write_different_addr = {3'b001};
       bins read_after_write_same_addr = {3'b010};
       bins read_after_write_different_addr = {3'b011};
       bins write_after_read_same_addr = {3'b100};
       bins write_after_read_different_addr = {3'b101};
       bins b2b_read_same_addr = {3'b110};
       bins b2b_read_different_addr = {3'b111};
     }
endgroup

// Cover timing parameters of I2C transactions
covergroup i2c_timing_param_cg(string name="i2c_timing_param_cg") with
  function sample(bit[15:0] param);
  option.per_instance = 1;
  option.name = name;
  cp_timing_param : coverpoint param {
    bins zero = {0};
    bins low = {[1: 100]};
    bins med = {[101: 1000]};
    bins high = {[1001: 65535]};
  }
endgroup : i2c_timing_param_cg

// Cover SCL stretch functionality in Host and Target modes
covergroup i2c_scl_stretch_cg(bit[15:0] FIFO_SIZE) with function sample(
  bit host_mode,
  bit intr_stretch_timeout,
  bit host_timeout_ctrl_en,
  bit intr_tx_stretch,
  bit intr_acq_full,
  uint acq_fifo_size,
  uint tx_fifo_size
);
  /////////////////////////////////////////
  // CLOCK STRETCHING : DUT -> HOST_MODE //
  /////////////////////////////////////////

  // Stretch detected if cio_scl_en_o is not asserted but still cio_scl_i low which indicates
  // target device is stretching the clock, if the number of cycles SCL is stretched exceeds
  // a timeout value intr_stretch_timeout is raised
  cp_host_mode_stretch : coverpoint intr_stretch_timeout iff (
      host_mode && host_timeout_ctrl_en){
    bins stretch = {1};
    ignore_bins unused = {0};
  }

  ///////////////////////////////////////////
  // CLOCK STRETCHING : DUT -> TARGET_MODE //
  ///////////////////////////////////////////

  // Target mode SCL stretch due to three scenarios
  // 1. ACQ full, can be an Address or Write data byte, both indicated by intr_acq_full
  // 2. During Read transaction, if TX FIFO is empty and ACQ FIFO has read transaction, indicated
  //    by intr_tx_stretch
  // 3. For a Read transaction, if ACQ FIFO has more than one entry, indicated by intr_tx_stretch
  cp_acq_fifo_size : coverpoint acq_fifo_size {
    bins empty = {0};
    bins not_empty = {[1:FIFO_SIZE-1]};
  }
  cp_tx_fifo_size : coverpoint tx_fifo_size {
    bins empty = {0};
    bins not_empty = {[1:FIFO_SIZE-1]};
  }
  cp_target_scl_stretch_addr_write: coverpoint acq_fifo_size iff (intr_acq_full && !host_mode) {
    bins addr_write_byte_stretch = {FIFO_SIZE-1};
  }
  cp_target_scl_stretch_read : cross cp_acq_fifo_size, cp_tx_fifo_size
    iff (intr_tx_stretch && !host_mode) {
    bins read_byte_stretch = binsof(cp_acq_fifo_size.not_empty) && binsof(cp_tx_fifo_size.empty);
    bins scl_stretch_read_request = binsof(cp_acq_fifo_size.not_empty);
  }
endgroup : i2c_scl_stretch_cg

class i2c_env_cov extends cip_base_env_cov #(.CFG_T(i2c_env_cfg));
  `uvm_component_utils(i2c_env_cov)

  i2c_interrupts_cg interrupts_cg;
  i2c_fifo_reset_cg fifo_reset_cg;
  i2c_fifo_level_cg fmt_fifo_level_cg;
  i2c_fifo_level_cg rx_fifo_level_cg;
  i2c_operating_mode_cg openting_mode_cg;
  i2c_status_cg status_cg;
  i2c_scl_sda_override_cg scl_sda_override_cg;
  i2c_fmt_fifo_cg fmt_fifo_cg;
  i2c_acq_fifo_cg acq_fifo_cg;
  i2c_b2b_txn_cg    b2b_txn_host_cg;
  i2c_b2b_txn_cg    b2b_txn_target_cg;

  i2c_timing_param_cg     tlow_cg;
  i2c_timing_param_cg     thigh_cg;
  i2c_timing_param_cg     t_r_cg;
  i2c_timing_param_cg     t_f_cg;
  i2c_timing_param_cg     thd_sta_cg;
  i2c_timing_param_cg     tsu_sta_cg;
  i2c_timing_param_cg     tsu_dat_cg;
  i2c_timing_param_cg     thd_dat_cg;
  i2c_timing_param_cg     t_buf_cg;
  i2c_timing_param_cg     tsu_sto_cg;
  i2c_scl_stretch_cg      scl_stretch_cg;
  bit got_first_addr;
  bit [7:0] past_addr;

  function new(string name, uvm_component parent);
    super.new(name, parent);
    fmt_fifo_level_cg = new(I2C_FMT_FIFO_DEPTH);
    rx_fifo_level_cg  = new(I2C_RX_FIFO_DEPTH);
    interrupts_cg = new();
    fifo_reset_cg = new();
    openting_mode_cg = new();
    status_cg = new();
    scl_sda_override_cg = new();
    fmt_fifo_cg = new();
    acq_fifo_cg = new();
    b2b_txn_host_cg = new();
    b2b_txn_target_cg = new();
    tlow_cg = new("tlow_cg");
    thigh_cg = new("thigh_cg");
    t_r_cg = new("t_r_cg");
    t_f_cg = new("t_f_cg");
    thd_sta_cg = new("thd_sta_cg");
    tsu_sta_cg = new("tsu_sta_cg");
    tsu_dat_cg = new("tsu_dat_cg");
    thd_dat_cg = new("thd_dat_cg");
    t_buf_cg = new("t_buf_cg");
    tsu_sto_cg = new("tsu_sto_cg");
    scl_stretch_cg = new(I2C_ACQ_FIFO_DEPTH);
    got_first_addr = 0;
  endfunction : new

  function void sample_i2c_b2b_cg(bit[7:0] addr, bit host_mode);
    if(got_first_addr) begin
      b2b_txn_host_cg.sample(past_addr, addr, host_mode);
      b2b_txn_target_cg.sample(past_addr, addr, !host_mode);
      past_addr = addr;
    end else begin
      got_first_addr = 1;
      past_addr = addr;
    end
  endfunction

endclass : i2c_env_cov
