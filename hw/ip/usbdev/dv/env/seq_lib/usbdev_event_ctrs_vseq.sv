// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence for basic testing of usbdev event counters

class usbdev_event_ctrs_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_event_ctrs_vseq)

  `uvm_object_new

  constraint num_trans_c { num_trans inside {[256:1024]}; }

  // TODO: Collect this from somewhere?
  localparam int unsigned NBuf = 64;

  // Collect the number of Endpoints supported by the USB device.
  localparam int unsigned NEndpoints = usbdev_reg_pkg::NEndpoints;

  // Actions to perform; forming a bit field.
  typedef enum {
    Act_SupplyAVSetup = 0,
    Act_SupplyAVOut,
    Act_SendSETUP,
    Act_SendOUT,
    Act_SendIN,
    Act_ReadRXa,
    Act_ReadRXb,
    // Count of actions, must be last.
    Act_Count
  } action_e;

  // Possible responses to an IN transaction.
  typedef enum {
    InRsp_Ack = 0,
    InRsp_Nak,
    InRsp_Ignore
  } in_rsp_e;

  // Randomized bit masks, indicating for each event counter the set of endpoints
  // for which that event shall be counted.
  rand bit [NEndpoints-1:0] ep_ign_avsetup;
  rand bit [NEndpoints-1:0] ep_drop_avout;
  rand bit [NEndpoints-1:0] ep_drop_rx;
  rand bit [NEndpoints-1:0] ep_datatog_out;
  rand bit [NEndpoints-1:0] ep_timeout_in;
  rand bit [NEndpoints-1:0] ep_nak_in;
  rand bit [NEndpoints-1:0] ep_nodata_in0;
  rand bit [NEndpoints-1:0] ep_nodata_in1;

  // Actual counts read from the USB device
  uint act_cnt_ign_avsetup;
  uint act_cnt_drop_avout;
  uint act_cnt_drop_rx;
  uint act_cnt_datatog_out;
  uint act_cnt_timeout_in;
  uint act_cnt_nak_in;
  uint act_cnt_nodata_in0;
  uint act_cnt_nodata_in1;
  uint act_cnt_crc5_out;
  uint act_cnt_crc16_out;
  uint act_cnt_bitstuff;
  uint act_cnt_pid_invalid;

  // Simple utility functions to set the appropriate bits within an event counter register
  function bit [31:0] ctr_reset(bit rst);
    return {rst, 31'b0};
  endfunction
  function bit [31:0] ctr_endp(bit [NEndpoints-1:0] endp);
    return {{(16-NEndpoints){1'b0}}, endp, 16'b0};
  endfunction
  function bit [31:0] ctr_enable(bit en);
    return {1'b0, en, 30'b0};
  endfunction

  // Simple utility function that updates an event counter, saturating where appropriate
  function bit [15:0] ctr_event(bit [15:0] count, bit ev);
    return count + (ev & ~&count);
  endfunction

  // Read and report the actual counter values from the USB device.
  task read_and_report_counters();
    // Collect the actual counts for subsequent checking against expectations.
    csr_rd(.ptr(ral.count_ign_avsetup.count), .value(act_cnt_ign_avsetup));
    csr_rd(.ptr(ral.count_drop_avout.count),  .value(act_cnt_drop_avout));
    csr_rd(.ptr(ral.count_drop_rx.count),     .value(act_cnt_drop_rx));
    csr_rd(.ptr(ral.count_datatog_out.count), .value(act_cnt_datatog_out));
    csr_rd(.ptr(ral.count_timeout_in.count),  .value(act_cnt_timeout_in));
    csr_rd(.ptr(ral.count_nak_in.count),      .value(act_cnt_nak_in));
    csr_rd(.ptr(ral.count_nodata_in0.count),  .value(act_cnt_nodata_in0));
    csr_rd(.ptr(ral.count_nodata_in1.count),  .value(act_cnt_nodata_in1));
    csr_rd(.ptr(ral.count_crc5_out.count),    .value(act_cnt_crc5_out));
    csr_rd(.ptr(ral.count_crc16_out.count),   .value(act_cnt_crc16_out));
    csr_rd(.ptr(ral.count_bitstuff.count),    .value(act_cnt_bitstuff));
    csr_rd(.ptr(ral.count_pid_invalid.count), .value(act_cnt_pid_invalid));

    // Report the observed counts
    `uvm_info(`gfn, $sformatf("count_ign_avsetup %d", act_cnt_ign_avsetup), UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_drop_avout  %d", act_cnt_drop_avout),  UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_drop_rx     %d", act_cnt_drop_rx),     UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_datatog_out %d", act_cnt_datatog_out), UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_timeout_in  %d", act_cnt_timeout_in),  UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_nak_in      %d", act_cnt_nak_in),      UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_nodata_in0  %d", act_cnt_nodata_in0),  UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_nodata_in1  %d", act_cnt_nodata_in1),  UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_crc5_out    %d", act_cnt_crc5_out),    UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_crc16_out   %d", act_cnt_crc16_out),   UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_bitstuff    %d", act_cnt_bitstuff),    UVM_LOW)  // UVM_HIGH
    `uvm_info(`gfn, $sformatf("count_pid_invalid %d", act_cnt_pid_invalid), UVM_LOW)  // UVM_HIGH
  endtask

  task body();
    // Our expectations of the event counters
    // TODO: perhaps at some point the scoreboard can be pressed into service; it can certainly
    //       model the CSR-side activity, but how it handles the actual event count is unclear.
    bit [15:0] exp_cnt_ign_avsetup = 16'b0;
    bit [15:0] exp_cnt_drop_avout  = 16'b0;
    bit [15:0] exp_cnt_drop_rx     = 16'b0;
    bit [15:0] exp_cnt_datatog_out = 16'b0;
    bit [15:0] exp_cnt_timeout_in  = 16'b0;
    bit [15:0] exp_cnt_nak_in      = 16'b0;
    bit [15:0] exp_cnt_nodata_in0  = 16'b0;
    bit [15:0] exp_cnt_nodata_in1  = 16'b0;
    // TODO: we cannot presently inject errors to cause these 4 to become non-zero.
    bit [15:0] exp_cnt_crc5_out    = 16'b0;
    bit [15:0] exp_cnt_crc16_out   = 16'b0;
    bit [15:0] exp_cnt_bitstuff    = 16'b0;
    bit [15:0] exp_cnt_pid_invalid = 16'b0;
    // Expectation of the USB device IN-side Data Toggles.
    bit [NEndpoints-1:0] exp_in_toggles  = 16'b0;
    // Expectation of the USB device OUT-side Data Toggles.
    bit [NEndpoints-1:0] exp_out_toggles = 16'b0;
    bit [31:0] all_endpoints = {NEndpoints{1'b1}};
    bit [31:0] iso_endpoints = 32'h184;

    // Configure all endpoints to respond to all of SETUP, OUT and IN packets.
    // TODO: usb20_driver presently cannot send SETUP packets to endpoints that will not respond.
    csr_wr(.ptr(ral.ep_in_enable[0]),   .value(all_endpoints));
    csr_wr(.ptr(ral.ep_out_enable[0]),  .value(all_endpoints));
    csr_wr(.ptr(ral.rxenable_setup[0]), .value(all_endpoints));
    csr_wr(.ptr(ral.rxenable_out[0]),   .value(all_endpoints));
    // Include a couple of Isochronous ports because we do need to ensure that the 'timeout_in'
    // counter does not count Isochronous IN transactions, whether successful or unsuccessful.
    csr_wr(.ptr(ral.in_iso[0]),         .value(iso_endpoints));
    csr_wr(.ptr(ral.out_iso[0]),        .value(iso_endpoints));

    for (uint txn = 0; txn < num_trans; txn++) begin
      // Set of actions to perform
      bit [Act_Count-1:0] actions;
      // FIFO status information
      bit [31:0] usbstat;
      bit avsetup_empty;
      bit avsetup_full;
      bit avout_empty;
      bit avout_full;
      uint rx_level;
      uint bufnum;
      bit [11:0] rst;
      bit [3:0] en;

      // Reset a random subset of the counters
      `DV_CHECK_STD_RANDOMIZE_FATAL(rst);
      // Enable a subset of the non-endpoint counters
      `DV_CHECK_STD_RANDOMIZE_FATAL(en);

      // Note: although we're not changing the set of enabled endpoints at this point, it's
      //       important that we can write a new endpoint subset without modifying the counter
      //       value or impacting the behavior of the event counter.

      // Configure event counters for OUT side packet rejections
      csr_wr(.ptr(ral.count_ign_avsetup), .value(ctr_endp(ep_ign_avsetup) | ctr_reset(rst[0])));
      csr_wr(.ptr(ral.count_drop_avout),  .value(ctr_endp(ep_drop_avout)  | ctr_reset(rst[1])));
      csr_wr(.ptr(ral.count_drop_rx),     .value(ctr_endp(ep_drop_rx)     | ctr_reset(rst[2])));
      csr_wr(.ptr(ral.count_datatog_out), .value(ctr_endp(ep_datatog_out) | ctr_reset(rst[3])));
      // Configure event counters for IN side packet rejections
      csr_wr(.ptr(ral.count_timeout_in),  .value(ctr_endp(ep_timeout_in)  | ctr_reset(rst[4])));
      csr_wr(.ptr(ral.count_nak_in),      .value(ctr_endp(ep_nak_in)      | ctr_reset(rst[5])));
      csr_wr(.ptr(ral.count_nodata_in0),  .value(ctr_endp(ep_nodata_in0)  | ctr_reset(rst[6])));
      csr_wr(.ptr(ral.count_nodata_in1),  .value(ctr_endp(ep_nodata_in1)  | ctr_reset(rst[7])));
      csr_wr(.ptr(ral.count_crc5_out),    .value(ctr_enable(en[0])        | ctr_reset(rst[8])));
      csr_wr(.ptr(ral.count_crc16_out),   .value(ctr_enable(en[1])        | ctr_reset(rst[9])));
      csr_wr(.ptr(ral.count_bitstuff),    .value(ctr_enable(en[2])        | ctr_reset(rst[10])));
      csr_wr(.ptr(ral.count_pid_invalid), .value(ctr_enable(en[3])        | ctr_reset(rst[11])));

      // Update counter expectations
      if (rst[0])  exp_cnt_ign_avsetup = 0;
      if (rst[1])  exp_cnt_drop_avout  = 0;
      if (rst[2])  exp_cnt_drop_rx     = 0;
      if (rst[3])  exp_cnt_datatog_out = 0;
      if (rst[4])  exp_cnt_timeout_in  = 0;
      if (rst[5])  exp_cnt_nak_in      = 0;
      if (rst[6])  exp_cnt_nodata_in0  = 0;
      if (rst[7])  exp_cnt_nodata_in1  = 0;
      if (rst[8])  exp_cnt_crc5_out    = 0;
      if (rst[9])  exp_cnt_crc16_out   = 0;
      if (rst[10]) exp_cnt_bitstuff    = 0;
      if (rst[11]) exp_cnt_pid_invalid = 0;

      // Ascertain the present state of the FIFOs.
      csr_rd(.ptr(ral.usbstat), .value(usbstat));
      avsetup_full  =  get_field_val(ral.usbstat.av_out_full,    usbstat);
      avsetup_empty = (get_field_val(ral.usbstat.av_setup_depth, usbstat) <= 0);
      avout_full    =  get_field_val(ral.usbstat.av_setup_full,  usbstat);
      avout_empty   = (get_field_val(ral.usbstat.av_out_depth,   usbstat) <= 0);
      rx_level      =  get_field_val(ral.usbstat.rx_depth,       usbstat);

      `uvm_info(`gfn, $sformatf("AVSETUP depth %d full %d empty %d",
                                get_field_val(ral.usbstat.av_setup_depth, usbstat), avsetup_full,
                                avsetup_empty), UVM_LOW)  // UVM_HIGH
      `uvm_info(`gfn, $sformatf("AVOUT depth %d full %d empty %d",
                                get_field_val(ral.usbstat.av_out_depth, usbstat), avout_full,
                                avout_empty), UVM_LOW)  // UVM_HIGH
      `uvm_info(`gfn, $sformatf("RXFIFO depth %d", rx_level), UVM_LOW)   // UVM_HIGH

      // Decide whether to supply buffer(s);
      // Note: the buffer numbers do not actually matter, we're not concerned with the data itself.
      `DV_CHECK_STD_RANDOMIZE_FATAL(actions)
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(bufnum, bufnum inside {[0:NBuf-1]};)
      if (actions[Act_SupplyAVSetup] & !avsetup_full) begin
        csr_wr(.ptr(ral.avsetupbuffer), .value(bufnum));
        avsetup_empty = 0;
      end
      if (actions[Act_SupplyAVOut] & !avout_full) begin
        csr_wr(.ptr(ral.avoutbuffer), .value(bufnum));
        avout_empty = 0;
      end

      // Attempt to send a SETUP packet to a randomly-chosen endpoint.
      if (actions[Act_SendSETUP]) begin
        bit exp_accepted = !avsetup_empty && (rx_level < RxFIFODepth);

        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endp, endp inside {[0:NEndpoints-1]};)
        call_token_seq(PidTypeSetupToken);
        call_data_seq(PidTypeData0, .randomize_length(1'b0), .num_of_bytes(8));

        exp_cnt_ign_avsetup = ctr_event(exp_cnt_ign_avsetup, ep_ign_avsetup[endp] && avsetup_empty);
        exp_cnt_drop_rx = ctr_event(exp_cnt_drop_rx, ep_drop_rx[endp] && (rx_level >= RxFIFODepth));
        if (exp_accepted) begin
          // Update our understanding of the RX FIFO level.
          rx_level = rx_level - 1;
          // It should be expecting DATA1 next.
          exp_out_toggles[endp] = 1'b1;
        end
      end
      if (actions[Act_SendOUT]) begin
        bit exp_accepted = !avout_empty && (rx_level < RxFIFODepth - 1);

        // Attempt to send an OUT packet to a randomly-chosen endpoint.
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endp, endp inside {[0:NEndpoints-1]};)
        call_token_seq(PidTypeOutToken);
        call_data_seq(exp_out_toggles[endp] ? PidTypeData1 : PidTypeData0,
                      .randomize_length(1'b1), .num_of_bytes(0));
        get_response(m_response_item);
        $cast(m_usb20_item, m_response_item);
        get_out_response_from_device(m_usb20_item, exp_accepted ? PidTypeAck : PidTypeNak);

        exp_cnt_drop_avout = ctr_event(exp_cnt_drop_avout, ep_drop_avout[endp] && avout_empty);
        // Note: Final entry of the RX FIFO is reserved only for use by SETUP packets.
        exp_cnt_drop_rx = ctr_event(exp_cnt_drop_rx,
                                    ep_drop_rx[endp] && (rx_level >= RxFIFODepth - 1));
        if (exp_accepted) begin
          // Update our understanding of the RX FIFO level.
          rx_level = rx_level - 1;
          // OUT Data Toggle inverts.
          exp_out_toggles[endp] ^=  1;
        end
      end
      if (actions[Act_SendIN]) begin
        // Response to IN transactions
        in_rsp_e in_response;

        // Request an IN packet from a randomly-chosen endpoint.
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(endp, endp inside {[0:NEndpoints-1]};)
        call_token_seq(PidTypeInToken);
        // Get response from DUT.
        get_response(m_response_item);
        $cast(m_usb20_item, m_response_item);
        // TODO: We shall always get NAK presently.
        if (1) begin
          get_data_pid_from_device(m_usb20_item, PidTypeNak);
        end else begin
          get_data_pid_from_device(m_usb20_item,
                                   exp_in_toggles[endp] ? PidTypeData1 : PidTypeData0);
        end
        // Decide how we wish to respond to the IN transaction.
        `DV_CHECK_STD_RANDOMIZE_FATAL(in_response);
        case (in_response)
          InRsp_Ack: begin
            call_handshake_sequence(PktTypeHandshake, PidTypeAck);
            // IN Data toggle inverts, on the assumption that the device sees the ACK successfully.
            exp_in_toggles[endp] ^= 1;
          end
          // IN Data toggle does not advance at the device if it does not see an ACK response.
          InRsp_Nak: call_handshake_sequence(PktTypeHandshake, PidTypeNak);
          default: begin
            cfg.clk_rst_vif.wait_clks(20);
            `uvm_info(`gfn, "No handshake response", UVM_HIGH) // Do nothing
          end
        endcase

        // TODO: presently we do NOT supply any IN packets via 'configin' so enabled 'nodata_in'
        //       counter(s) will increment for every attempted IN transactions.
        exp_cnt_nodata_in0 = ctr_event(exp_cnt_nodata_in0, ep_nodata_in0[endp] && 1);
        exp_cnt_nodata_in1 = ctr_event(exp_cnt_nodata_in1, ep_nodata_in1[endp] && 1);
      end

      // Decide whether to pluck a packet from the RX FIFO; we may pluck 0-2 to match the average
      // rate of supplying packets
      if (actions[Act_ReadRXa] && rx_level > 0) begin
        bit [31:0] rx_fifo_entry;
        csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_entry));
        rx_level = rx_level - 1;
      end
      if (actions[Act_ReadRXb] && rx_level > 0) begin
        bit [31:0] rx_fifo_entry;
        csr_rd(.ptr(ral.rxfifo), .value(rx_fifo_entry));
        rx_level = rx_level - 1;
      end

      // TODO: presently we have no mechanism for the deliberate injection of CRC5/16 errors,
      //       or Bit Stuffing errors.
      //       Invalid PIDs we probably can generate?

      read_and_report_counters();

      // Check that we have the expected counts at this point
      `DV_CHECK_EQ(act_cnt_ign_avsetup, exp_cnt_ign_avsetup)
      `DV_CHECK_EQ(act_cnt_drop_avout,  exp_cnt_drop_avout)
      `DV_CHECK_EQ(act_cnt_drop_rx,     exp_cnt_drop_rx)
      `DV_CHECK_EQ(act_cnt_datatog_out, exp_cnt_datatog_out)
      `DV_CHECK_EQ(act_cnt_timeout_in,  exp_cnt_timeout_in)
      `DV_CHECK_EQ(act_cnt_nak_in,      exp_cnt_nak_in)
      `DV_CHECK_EQ(act_cnt_nodata_in0,  exp_cnt_nodata_in0)
      `DV_CHECK_EQ(act_cnt_nodata_in1,  exp_cnt_nodata_in1)
      `DV_CHECK_EQ(act_cnt_crc5_out,    exp_cnt_crc5_out)
      `DV_CHECK_EQ(act_cnt_crc16_out,   exp_cnt_crc16_out)
      `DV_CHECK_EQ(act_cnt_bitstuff,    exp_cnt_bitstuff)
      `DV_CHECK_EQ(act_cnt_pid_invalid, exp_cnt_pid_invalid)
    end
  endtask

endclass
