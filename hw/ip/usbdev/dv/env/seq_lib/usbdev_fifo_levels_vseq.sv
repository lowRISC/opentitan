// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Exercise the receipt of SETUP and OUT DATA packets with the Available OUT/SETUP Buffer FIFO
// and Rx FIFO at randomized levels, including Isochronous endpoints for branch/cond coverage in the
// OUT side Packet Engine.
class usbdev_fifo_levels_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_fifo_levels_vseq)

  `uvm_object_new

  // Widths of buffer numbers, in bits.
  localparam uint BufW = $clog2(NumBuffers + 1);

  // Widths of FIFO levels/depths in bits.
  localparam uint AvOutDepthW   = $clog2(AvOutFIFODepth + 1);
  localparam uint AvSetupDepthW = $clog2(AvSetupFIFODepth + 1);
  localparam uint RxDepthW      = $clog2(RxFIFODepth + 1);

  // Initial FIFO levels are randomized.
  rand bit [AvOutDepthW  -1:0] avout_level;
  rand bit [AvSetupDepthW-1:0] avsetup_level;
  rand bit [RxDepthW     -1:0] rx_level;

  // FIFO levels must be more restricted to hit the various permutations of empty, full and nearly
  // empty/full. It is presumed that the intermediate levels are less likely to be problematic.
  constraint avsetup_restrict_c {
    avsetup_level inside {0, 1, AvSetupFIFODepth};
  }
  constraint avout_restrict_c {
    avout_level inside {0, 1, AvOutFIFODepth};
  }
  constraint rx_restrict_c {
    rx_level inside {0, RxFIFODepth-1, RxFIFODepth};
  }

  // FIFO selection.
  typedef enum {
    AvOutFifo,
    AvSetupFifo,
    RxFifo
  } fifo_type_e;

  // Populate a FIFO with the given number of buffers.
  //
  // Note: the buffer numbers chosen don't actually matter for this test because the buffers
  // themselves shall never be used.
  task populate_fifo(fifo_type_e fifo, uint nbuf);
    for (uint b = 0; b < nbuf; b++) begin
      bit [BufW-1:0] buffer;
      // Choose a random buffer number
      buffer = $urandom_range(0, NumBuffers - 1);
      case (fifo)
        AvOutFifo:   csr_wr(.ptr(ral.avoutbuffer.buffer), .value(buffer));
        AvSetupFifo: csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(buffer));
        // Writing into the Rx FIFO requires packet transmission from the host.
        default: begin
          int unsigned level;
          // Ensure that there is a buffer available.
          csr_rd(.ptr(ral.usbstat.av_setup_depth), .value(level));
          if (!level) csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(buffer));
          send_prnd_setup_packet(ep_default);
          check_response_matches(PidTypeAck);
          // Be sure to restore the level of the AvSetup FIFO.
          if (level) csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(buffer));
        end
      endcase
    end
  endtask

  // Choose the type of transaction to perform.
  rand bit use_setup;  // SETUP rather than OUT?
  rand bit use_iso;    // If OUT, shall we use Isochronous?

  // The four possible responses from the DUT.
  typedef enum {
    // No response within timeout period, eg. SETUP packet has been dropped.
    ResponseNone,
    // No response to Isochronous Data packets at all (this distinction arises from the present
    // structure of usb20_driver).
    ResponseNoneIso,
    ResponseAck,
    ResponseNak
  } response_e;

  // Initialize the FIFOs to the chosen levels.
  task init_fifo_levels();
    // Report the chosen FIFO levels.
    `uvm_info(`gfn, $sformatf("avsetup_level %0d avout_level %0d rx_level %0d", avsetup_level,
                              avout_level, rx_level), UVM_LOW)

    // Pre-fill the Rx FIFO to the chosen level. To do this we we must use SETUP packets because
    // only they can fill the Rx FIFO completely; the final slot is reserved for SETUP packets to
    // improve responsiveness to Control Transfers from the USB host controller.
    configure_out_all();
    configure_setup_all();
    populate_fifo(RxFifo, rx_level);

    // Supply buffer to the AvOut/Setup Buffer FIFOs.
    populate_fifo(AvOutFifo, avout_level);
    populate_fifo(AvSetupFifo, avsetup_level);
  endtask

  virtual task body();
    // Normally packets receive an ACK in response.
    response_e exp_response = ResponseAck;
    // Initial expectations are 'no change'; refined below.
    int unsigned exp_avsetup_level = avsetup_level;
    int unsigned exp_avout_level = avout_level;
    int unsigned exp_rx_level = rx_level;
    // `usbstat` register holds the actual FIFO levels.
    uvm_reg_data_t usbstat;
    // DATAx to be sent if OUT transaction is chosen.
    pid_type_e pid = PidTypeData0;

    init_fifo_levels();

    // If we've sent one or more SETUP packets to the endpoint already to populate the Rx FIFO
    // then we shall need to send DATA1 next.
    if (rx_level) pid = PidTypeData1;

    // Report the chosen transaction properties.
    `uvm_info(`gfn, $sformatf("use_setup %0d use_iso %0d ep %0d", use_setup, use_iso, ep_default),
              UVM_LOW)

    // Predict the DUT response to us attempting to send the chosen packet.
    if (use_setup) begin
      // SETUP packets never receive a NAK; they are silently dropped.
      if (!avsetup_level || rx_level >= RxFIFODepth) exp_response = ResponseNone;
      else exp_avsetup_level--;
    end else begin
      // NAK means that the an OUT packet cannot be accepted; DUT busy.
      if (!avout_level || rx_level >= RxFIFODepth - 1) exp_response = ResponseNak;
      else exp_avout_level--;
      if (use_iso) begin
        // The Control/Setup bit within the endpoint configuration takes precedence over the
        // Isochronous configuration bit, so we must remove Setup support from this endpoint.
        int unsigned all_ep = {NEndpoints{1'b1}};
        csr_wr(.ptr(ral.rxenable_setup[0]), .value(all_ep & ~(1 << ep_default)));
        // Now enable Isochronous support for this OUT endpoint.
        csr_wr(.ptr(ral.out_iso[0]), .value(1 << ep_default));
      end
    end
    if (exp_response == ResponseAck) begin
      exp_rx_level++;
    end
    // Isochronous transfers, whether successful, do not elicit a response.
    if (use_iso & !use_setup) exp_response = ResponseNoneIso;

    if (use_setup) send_prnd_setup_packet(ep_default);
    else begin
      send_prnd_out_packet(ep_default, pid, .randomize_length(1), .num_of_bytes(0),
                           .isochronous_transfer(use_iso));
    end

    // We mostly rely upon the scoreboard/BFM to check that the DUT behaves as expected, and only
    // check the response over the USB at this point.
    `uvm_info(`gfn, $sformatf("Expecting %p", exp_response), UVM_LOW)
    case (exp_response)
      ResponseNoneIso: begin
        `uvm_info(`gfn, "Iso packets yield no response; not waiting", UVM_LOW)
      end
      ResponseNone: check_no_response();  // Expects a response from the usb20_driver, but not DUT.
      ResponseAck:  check_response_matches(PidTypeAck);
      ResponseNak:  check_response_matches(PidTypeNak);
      default:      `uvm_fatal(`gfn, "Invalid/unsupported response type")
    endcase

    // May as well check the FIFO levels too.
    csr_rd(.ptr(ral.usbstat), .value(usbstat));
    `DV_CHECK_EQ(get_field_val(ral.usbstat.av_setup_depth, usbstat), exp_avsetup_level)
    `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_depth, usbstat), exp_avout_level)
    `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_depth, usbstat), exp_rx_level)
  endtask
endclass : usbdev_fifo_levels_vseq
