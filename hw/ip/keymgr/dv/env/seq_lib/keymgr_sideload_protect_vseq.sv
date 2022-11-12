// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test KEYMGR.OUTPUT_KEYS.CTRL.REDUN
// 1. randomly advance to a functional state and start a sideload operation
// 2. flip either data_sw_en or data_valid,
// 3. read sw_share* for check
//  - if hw_key_sel is flipped but data_sw_en is not, it doesn't match either the
//    previously flopped value or the sideload value.
//  - if hw_key_sel is not flipped but data_en is, you should see the previous value.
class keymgr_sideload_protect_vseq extends keymgr_random_vseq;
  `uvm_object_utils(keymgr_sideload_protect_vseq)
  `uvm_object_new

  // don'd advance any of the 3 functonal states
  constraint num_adv_c {
    num_adv inside {[2:4]};
  }

  task body();
    bit force_hw_key_sel_or_data_en;
    bit [keymgr_pkg::Shares-1:0][DIGEST_SHARE_WORD_NUM-1:0][TL_DW-1:0] sw_share_output;
    keymgr_pkg::hw_key_req_t hw_key;
    super.body();

    // update key_version to a valid value
    update_key_version();
    // read sw_shares to clear the output (these are w0c CSRs)
    read_sw_shares(sw_share_output);

    repeat ($urandom_range(2, 5)) begin
      force_hw_key_sel_or_data_en = $urandom_range(0, 1);
      $assertoff(0, "tb.dut.u_ctrl.DataEn_A");
      $assertoff(0, "tb.dut.u_ctrl.DataEnDis_A");
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(key_dest, key_dest != keymgr_pkg::None;)
      fork
        keymgr_generate(.operation(keymgr_pkg::OpGenHwOut), .key_dest(key_dest), .wait_done(1));
        cfg.keymgr_vif.inject_sideload_fault(force_hw_key_sel_or_data_en);
      join

      case (key_dest)
        keymgr_pkg::Aes:  hw_key = cfg.keymgr_vif.aes_key.key;
        keymgr_pkg::Kmac: hw_key = cfg.keymgr_vif.kmac_key.key;
        keymgr_pkg::Otbn: begin
          // truncate otbn key from 386 to 256 bits
          foreach (hw_key.key[i]) hw_key.key[i] = cfg.keymgr_vif.otbn_key.key[i];
        end
        default: `uvm_fatal(`gfn, "invalid value")
      endcase

      // Let scb know sw output is random value
      if (force_hw_key_sel_or_data_en) cfg.scb.is_sw_share_corrupted = 1;

      read_sw_shares(sw_share_output);
      // force on data_sw_en, sw output remains 0
      // force hw_key_sel, random value is assigned to sw output
      if (force_hw_key_sel_or_data_en) begin
        `DV_CHECK_NE(sw_share_output, 0)
      end else begin
        `DV_CHECK_EQ(sw_share_output, 0)
      end
      `DV_CHECK_NE(sw_share_output, hw_key.key)

      $asserton(0, "tb.dut.u_ctrl.DataEn_A");
      $asserton(0, "tb.dut.u_ctrl.DataEnDis_A");
    end
  endtask : body

endclass : keymgr_sideload_protect_vseq
