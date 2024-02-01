// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// FIFO RST sequence
//
// Since the FIFO RST functionality can only be employed safely whilst the USB device is not
// connected to the USB, the verification of this functionality can be achieved almost entirely
// from the CSR side.
//
// TODO: The one complication is that in order to place packets in the Rx FIFO we must connect to
// the device and sent it traffic over the USB.
class usbdev_fifo_rst_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_fifo_rst_vseq)

  `uvm_object_new

  // Number of transactions to perform
  //rand uint num_txns;
  constraint num_trans_c {num_trans inside {[64:256]};}

  // Widths of buffer numbers, in bits
  localparam uint BufW = $clog2(usbdev_env_pkg::NumBuffers + 1);

  // Widths of FIFO levels/depths in bits
  localparam uint AvOutDepthW   = $clog2(usbdev_env_pkg::AvOutFIFODepth + 1);
  localparam uint AvSetupDepthW = $clog2(usbdev_env_pkg::AvSetupFIFODepth + 1);
  localparam uint RxDepthW      = $clog2(usbdev_env_pkg::RxFIFODepth + 1);

  // Initial FIFO levels are randomized
  rand bit [AvOutDepthW  -1:0] avout_level;
  rand bit [AvSetupDepthW-1:0] avsetup_level;
  rand bit [RxDepthW     -1:0] rx_level;

  constraint avout_level_c {avout_level inside {[0:usbdev_env_pkg::AvOutFIFODepth]};}
  constraint avsetup_level_c {avsetup_level inside {[0:usbdev_env_pkg::AvSetupFIFODepth]};}
  constraint rx_level_c {rx_level inside {[0:usbdev_env_pkg::RxFIFODepth]};}

  // FIFO selection
  typedef enum {
    AvOutFifo,
    AvSetupFifo,
    RxFifo
  } fifo_type_e;

  // Populate a FIFOs with the given number of buffers.
  //
  // Note: the buffer numbers chosen don't actually matter for this test because the buffers
  // themselves shall never be used.
  task populate_fifo(fifo_type_e fifo, uint nbuf);
    for (uint b = 0; b < nbuf; b++) begin
      bit [BufW-1:0] buffer;
      // Choose a random buffer number
      buffer = $urandom_range(0, usbdev_env_pkg::NumBuffers - 1);
      case (fifo)
        AvOutFifo:   csr_wr(.ptr(ral.avoutbuffer.buffer), .value(buffer));
        AvSetupFifo: csr_wr(.ptr(ral.avsetupbuffer.buffer), .value(buffer));
        // Writing into the Rx FIFO require packet transmission from the host
        // TODO: here we need to connect the device, with some appropriate configuration of at least
        // one endpoint, and then transmit the appropriate number of packets to the OUT endpoint
        // in question.
        default:     `uvm_fatal(`gfn, "Rx FIFO writing not yet implemented")
      endcase
    end
  endtask

  task body();
    // Set each of the FIFOs to its initial state.
    populate_fifo(AvOutFifo, avout_level);
    populate_fifo(AvSetupFifo, avsetup_level);
    // populate_fifo(RxFifo, rx_level);
    for (int unsigned txn = 0; txn < num_trans; txn++) begin
      bit avout_full, avsetup_full, rx_empty;
      uvm_reg_data_t usbstat;

      if (cfg.under_reset) begin
        avsetup_level = 0;
        avout_level = 0;
        rx_level = 0;
      end else begin
        uint new_level;
        // Choose a FIFO to reset
        fifo_type_e fifo;
        // TODO: Rx FIFO not yet supported.
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(fifo, fifo != RxFifo;)
        // Hit the reset
        case (fifo)
          AvOutFifo: begin
            ral.fifo_ctrl.avout_rst.set(1'b1);
            csr_update(.csr(ral.fifo_ctrl));
            new_level = $urandom_range(0, usbdev_env_pkg::AvOutFIFODepth);
            avout_level = new_level;
          end
          AvSetupFifo: begin
            ral.fifo_ctrl.avsetup_rst.set(1'b1);
            csr_update(.csr(ral.fifo_ctrl));
            new_level = $urandom_range(0, usbdev_env_pkg::AvSetupFIFODepth);
            avsetup_level = new_level;
          end
          default: begin
            ral.fifo_ctrl.rx_rst.set(1'b1);
            csr_update(.csr(ral.fifo_ctrl));
            new_level = $urandom_range(0, usbdev_env_pkg::RxFIFODepth);
            rx_level = new_level;
          end
        endcase
        populate_fifo(fifo, new_level);
      end

      // Expected status indicators.
      avout_full   = (avout_level   >= usbdev_env_pkg::AvOutFIFODepth);
      avsetup_full = (avsetup_level >= usbdev_env_pkg::AvSetupFIFODepth);
      rx_empty     = 1'b1;

      // Read the new FIFO levels and status indicators.
      csr_rd(ral.usbstat, usbstat);
      // Check the FIFO levels are as expected
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_depth,   usbstat), avout_level);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_setup_depth, usbstat), avsetup_level);
      // TODO: Rx FIFO not yet supported.
      `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_depth,       usbstat), 0);
      // Check the other status indications as well for completeness.
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_full,    usbstat), avout_full);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_setup_full,  usbstat), avsetup_full);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_empty,       usbstat), rx_empty);
    end
  endtask

endclass : usbdev_fifo_rst_vseq
