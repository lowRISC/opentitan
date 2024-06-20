// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence for testing the 'link_out_err' interrupt.
class usbdev_link_out_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_link_out_err_vseq)

  `uvm_object_new

  // We iterate through each of the possible causes in turn.
  typedef enum {
    // First test the behavior when there is no buffer in the 'Available OUT Buffer FIFO.'
    LinkOutNoAvail,
    // Supply a buffer at this point, so that the other causes are accessible.
    LinkOutBadToggle,
    LinkOutTokenCRC16,
    LinkOutNoSpace
  } link_out_cause_e;

  virtual task body();
    bit [31:0] intr_bit = 1 << IntrLinkOutErr;
    bit [31:0] ep_mask = 1 << ep_default;
    link_out_cause_e next_cause, cause;
    uvm_reg_data_t out_toggles;

    buf_init();

    // Enable the 'link_out_err' interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(intr_bit));

    // Enable an endpoint for testing, and ensure that there is no buffer available initially.
    csr_wr(.ptr(ral.ep_out_enable[0]), .value(ep_mask));
    csr_wr(.ptr(ral.rxenable_out[0]), .value(ep_mask));

    // This interrupt is heavily overloaded and there are many events that may cause it to be
    // asserted; it is only informative/diagnostic for software, indicating only that an issue
    // occurred with OUT traffic, rather than anything more specific.
    //
    // Iterate through the potential causes...
    next_cause = cause.first();
    do begin
      uvm_reg_data_t intr_state;
      cause = next_cause;
      next_cause = next_cause.next();

      // Ensure that the interrupt is not set.
      csr_rd(.ptr(ral.intr_state), .value(intr_state));
      `DV_CHECK_EQ(intr_state[IntrLinkOutErr], 0, "Interrupt unexpectedly asserted already")
      `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkOutErr], 0, "Interrupt line unexpected asserted")

      case (cause)
        LinkOutNoAvail: begin
          uvm_reg_data_t usbstat;
          // Check that the Av OUT FIFO is empty.
          csr_rd(.ptr(ral.usbstat), .value(usbstat));
          `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_depth, usbstat), 0, "Av FIFO not empty")
          send_prnd_out_packet(ep_default, correct_toggle(ep_default, out_toggles));
          // DUT should be unable to accept the packet right now, so we're expecting a NAK.
          check_response_matches(PidTypeNak);
          // Now supply a buffer for subsequent tests.
          supply_out_buffer();
        end

        LinkOutBadToggle: begin
          // Send an OUT data packet with incorrect Data Toggle; to be sure that we get it 'wrong'
          // we'll read the current toggle.
          csr_wr(.ptr(ral.out_data_toggle), .value(out_toggles));
          send_prnd_out_packet(ep_default, bad_toggle(ep_default, out_toggles));
          // With an invalid Data Toggle the DUT shall still ACK to try to get us to advance to the
          // next packet/toggle bit, on the premise that its previous ACK was corrupted/lost.
          check_response_matches(PidTypeAck);
        end

        LinkOutTokenCRC16: begin
          inject_bad_data_crc16 = 1'b1;
          send_prnd_out_packet(ep_default, correct_toggle(ep_default, out_toggles));
          inject_bad_data_crc16 = 1'b0;
          // Packets with invalid CRC16 shall simply be ignored; host shall try again.
          check_no_response();
        end

        // The final cause is LinkOutNoSpace.
        LinkOutNoSpace: begin
          // Expected RX FIFO level; fail as soon as possible if packets are not being stored.
          int unsigned exp_rx_depth = 0;
          // At this point we just keep sending packets until the RX FIFO can take no more.
          uvm_reg_data_t usbstat;
          bit exp_ack;
          do begin
            supply_out_buffer();
            // Check the level of the RX FIFO and form an expectation of the DUT response;
            // remember that the last entry of the RX FIFO cannot be populated with an OUT DATA
            // packet, so the DUT should NAK.
            csr_rd(.ptr(ral.usbstat), .value(usbstat));
            `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_depth, usbstat), exp_rx_depth)
            exp_ack = (get_field_val(ral.usbstat.rx_depth, usbstat) < RxFIFODepth - 1);
            send_prnd_out_packet(ep_default, correct_toggle(ep_default, out_toggles));
            check_response_matches(exp_ack ? PidTypeAck : PidTypeNak);
            // Flip the Data Toggle bit otherwise a subsequent OUT DATA packet shall not be stored.
            out_toggles[ep_default] ^= 1'b1;
            exp_rx_depth++;
          end while (exp_ack);
        end

        default: `uvm_fatal(`gfn, "Unrecognised/unsupported cause")
      endcase

      // Interrupt bit should be asserted almost immediately; do not clear it at this point because
      // we want to check the interrupt line from the DUT too, and not just the status register bit.
      wait_for_interrupt(intr_bit, .timeout_clks(20), .clear(0), .enforce(1));
      // Interrupt line may take a little longer.
      loopback_delay();
      `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkOutErr], 1, "Interrupt line not asserted as expected")
      // Clear the interrupt
      csr_wr(.ptr(ral.intr_state), .value(intr_bit));
      // Interrupt line may take a little longer.
      loopback_delay();
      `DV_CHECK_EQ(cfg.intr_vif.pins[IntrLinkOutErr], 0, "Interrupt line still asserted")
    end while (cause != cause.last());

    // Disable and clear the interrupt.
    csr_wr(.ptr(ral.intr_enable), .value(0));
    csr_wr(.ptr(ral.intr_state), .value(intr_bit));
    // Empty the RX FIFO.
    flush_rx_fifo();
  endtask
endclass : usbdev_link_out_err_vseq
