// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Streaming test vseq
class usbdev_streaming_test_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_streaming_test_vseq)

  `uvm_object_new

  task body();
    bit av_out_empty;
    pid_type_e     DataToggle;
    uvm_reg_data_t read_rxfifo;
    endp = 4'd1;

    super.dut_init("HARD");
    clear_all_interrupts();  // clear interrupts
   // Configure out transaction
    configure_out_trans();
    // Enable av_empty interrupt
    ral.intr_enable.av_out_empty.set(1'b1);
    csr_update(ral.intr_enable);
    for (int i = 0; i < 6; i++) begin
      case(i)
        0: DataToggle = PidTypeData0;
        1: DataToggle = PidTypeData1;
        2: DataToggle = PidTypeData0;
        3: DataToggle = PidTypeData1;
        4: DataToggle = PidTypeData0;
        5: DataToggle = PidTypeData1;
        default: DataToggle = PidTypeData0;
      endcase
      // Out token packet followed by a data packet
      call_token_seq(PidTypeOutToken);
      cfg.clk_rst_vif.wait_clks(20);
      call_data_seq(PktTypeData, DataToggle, rand_or_not, num_of_bytes);
      cfg.clk_rst_vif.wait_clks(20);
      get_response(m_response_item);
      $cast(m_usb20_item, m_response_item);
      get_out_response_from_device(m_usb20_item, PidTypeAck);
      // Verifies that the av empty signal
      check_trans_accuracy();
      // Make sure buffer is availabe for next trans
      ral.avoutbuffer.buffer.set(out_buffer_id);
      csr_update(ral.avoutbuffer);
    end
  endtask

  task check_trans_accuracy();
    uvm_reg_data_t read_rxfifo;
    bit av_out_empty;

    // Read rxfifo reg
    csr_rd(.ptr(ral.rxfifo), .value(read_rxfifo));
    // Read av empty interrupt state
    csr_rd(.ptr(ral.intr_state.av_out_empty), .value(av_out_empty));
    // DV_CHECK on av empty interrupt
    `DV_CHECK_EQ(av_out_empty, 1);
  endtask
endclass
