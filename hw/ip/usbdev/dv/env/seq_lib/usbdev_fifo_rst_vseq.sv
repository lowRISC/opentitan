// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// FIFO RST sequence
//
// Since the FIFO RST functionality can only be employed safely whilst the USB device is not
// connected to the USB, the verification of this functionality can be achieved almost entirely
// from the CSR side.
class usbdev_fifo_rst_vseq extends usbdev_fifo_levels_vseq;
  `uvm_object_utils(usbdev_fifo_rst_vseq)

  `uvm_object_new

  // Number of transactions to perform
  constraint num_trans_c {num_trans inside {[64:256]};}

  // FIFO levels must be valid but not as constrained as in the parent sequence.
  constraint avout_level_c {avout_level inside {[0:AvOutFIFODepth]};}
  constraint avsetup_level_c {avsetup_level inside {[0:AvSetupFIFODepth]};}
  constraint rx_level_c {rx_level inside {[0:RxFIFODepth]};}

  task body();
    // FIFO levels must be valid but not as constrained as in the parent sequence.
    avsetup_restrict_c.constraint_mode(0);
    avout_restrict_c.constraint_mode(0);
    rx_restrict_c.constraint_mode(0);

    // Initialize the FIFOs to the chosen levels.
    init_fifo_levels();

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

        // Re-populate the FIFO of choice to its new level.
        populate_fifo(fifo, new_level);
      end

      // Expected status indicators.
      avout_full   = (avout_level   >= usbdev_env_pkg::AvOutFIFODepth);
      avsetup_full = (avsetup_level >= usbdev_env_pkg::AvSetupFIFODepth);
      rx_empty     = !rx_level;

      // Read the new FIFO levels and status indicators.
      csr_rd(ral.usbstat, usbstat);
      // Check the FIFO levels are as expected
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_depth,   usbstat), avout_level);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_setup_depth, usbstat), avsetup_level);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_depth,       usbstat), rx_level);
      // Check the other status indications as well for completeness.
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_out_full,    usbstat), avout_full);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.av_setup_full,  usbstat), avsetup_full);
      `DV_CHECK_EQ(get_field_val(ral.usbstat.rx_empty,       usbstat), rx_empty);
    end
  endtask

endclass : usbdev_fifo_rst_vseq
