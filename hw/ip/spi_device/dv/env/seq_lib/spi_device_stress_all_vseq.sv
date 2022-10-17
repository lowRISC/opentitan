// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Combine most of the spi_device sequences in one test to run sequentially, except csr sequences.
// mainly test these:
// - Modes switch among FW, flash, passthrough and tpm.
// - send some dummy transactions along with normal transactions
// - Randomly add reset between each sequence
class spi_device_stress_all_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_stress_all_vseq)
  `uvm_object_new

  constraint num_trans_c {
    num_trans inside {[3:5]};
  }
  rand bit en_dummy_host_xfer;

  task body();
    int num_flash_tpm_seq;
    string seq_names[$] = {"spi_device_txrx_vseq",
                           "spi_device_fifo_full_vseq",
                           "spi_device_fifo_underflow_overflow_vseq",
                           "spi_device_extreme_fifo_size_vseq",
                           "spi_device_dummy_item_extra_dly_vseq",
                           "spi_device_intr_vseq",
                           "spi_device_perf_vseq",
                           "spi_device_csb_read_vseq",
                           "spi_device_common_vseq" // for intr_test
                          };
    // above seq are all for FW mode, increase the chance of running flash/tpm seq by adding
    // the spi_device_flash_and_tpm_vseq mutiple times.
    num_flash_tpm_seq = seq_names.size() / 2;
    // this includes both flash_all and tpm_all, which cover most of these 2 modes.
    repeat (num_flash_tpm_seq) seq_names.push_back("spi_device_flash_and_tpm_vseq");

    for (int i = 1; i <= num_trans; i++) begin
      uvm_sequence   seq;
      spi_device_base_vseq spi_vseq;
      uint           seq_idx = $urandom_range(0, seq_names.size - 1);
      bit            done_xfer;

      seq = create_seq_by_name(seq_names[seq_idx]);
      `downcast(spi_vseq, seq)

      // if upper seq disables do_apply_reset for this seq, then can't issue reset
      // as upper seq may drive reset
      if (do_apply_reset) spi_vseq.do_apply_reset = $urandom_range(0, 1);
      else                spi_vseq.do_apply_reset = 0;

      spi_vseq.set_sequencer(p_sequencer);
      `DV_CHECK_RANDOMIZE_FATAL(spi_vseq)
      if (seq_names[seq_idx] == "spi_device_common_vseq") begin
        spi_device_common_vseq common_vseq;
        `downcast(common_vseq, spi_vseq);
        common_vseq.common_seq_type = "intr_test";
      end

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(en_dummy_host_xfer)
      fork
        begin : main_seq
          spi_vseq.start(p_sequencer);
          done_xfer = 1;
        end : main_seq
        begin : dummy_item_seq
          while (!done_xfer && en_dummy_host_xfer) begin
            cfg.clk_rst_vif.wait_clks($urandom_range(10, 1000));
            spi_host_xfer_dummy_item();
          end
        end : dummy_item_seq
      join
    end
  endtask : body
endclass : spi_device_stress_all_vseq
