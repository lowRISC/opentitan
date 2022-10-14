// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A full random test to verify TPM mode
// on the top of spi_device_tpm_read_hw_reg_vseq, override the constraint to enable following
// 1. Enable TPM write
// 2. Full randomization on TPM_CFG, except TPM_CFG.en is fixed to 1
// Add a SW thread to read TPM write data or prepare data for TPM to read
class spi_device_tpm_all_vseq extends spi_device_tpm_read_hw_reg_vseq;
  `uvm_object_utils(spi_device_tpm_all_vseq)
  `uvm_object_new

  // Override this to test more in the extended test
  constraint tpm_addition_for_read_hw_reg_c {
    tpm_write dist {
      0 :/ 2,
      1 :/ 1
    };
    // this removed the constraint on setting TPM_CFG
    direct_return_for_hw_reg == 0;
  }

  rand uint sw_to_poll_intr_cyc_dly;

  constraint sw_to_poll_intr_cyc_dly_c {
    sw_to_poll_intr_cyc_dly dist {
      [1:10]     :/ 5,
      [11:100]   :/ 2,
      [101:1000] :/ 1
    };
  }

  virtual task body();
    bit main_body_done;

    // both SW and HW may want to update this interrupt at the same time,
    // scb can't predict this interrupt properly.
    cfg.en_check_tpm_not_empty_intr = 0;
    fork
      begin
        super.body();
        main_body_done = 1;
      end
      begin : sw_process_tpm_fifo_thread
        bit tpm_intr;
        while (1) begin
          bit cmdaddr_notempty_val;
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(sw_to_poll_intr_cyc_dly)
          cfg.clk_rst_vif.wait_clks(sw_to_poll_intr_cyc_dly);

          csr_rd(.ptr(ral.intr_state.tpm_header_not_empty), .value(tpm_intr));
          if (tpm_intr) begin
            csr_rd_check(.ptr(ral.tpm_status.cmdaddr_notempty), .compare_value(1));
            do begin
              process_tpm_fifo();
              // it's intented to exit even if it's not empty.
              // Since it's a level interrupt, will get notified again.
              if ($urandom_range(0, 2) == 0) break;
              csr_rd(.ptr(ral.tpm_status.cmdaddr_notempty), .value(cmdaddr_notempty_val));
            end while (cmdaddr_notempty_val);
            clear_tpm_interrupt();
          end else if (main_body_done) begin
            break;
          end
        end
      end : sw_process_tpm_fifo_thread
    join
  endtask : body

  virtual task process_tpm_fifo();
    bit [TL_DW-1:0] cmd_addr_data;
    bit [7:0] cmd_val;
    bit write;
    uint size;
    bit [7:0] sw_byte_q[$]; // returned data is checked in scb

    csr_rd(.ptr(ral.tpm_cmd_addr), .value(cmd_addr_data));

    cmd_val = get_field_val(ral.tpm_cmd_addr.cmd, cmd_addr_data);
    decode_tpm_cmd(cmd_val, write, size);
    wait_and_process_tpm_fifo(write, size, sw_byte_q);
  endtask : process_tpm_fifo
endclass : spi_device_tpm_all_vseq
