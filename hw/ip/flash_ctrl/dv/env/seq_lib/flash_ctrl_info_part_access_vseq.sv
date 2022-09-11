// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The sequence accesses secret info regions after randomize lc_ctrl inputs.
// lc_ctrl_inputs:

//   .lc_creator_seed_sw_rw_en_i
//   .lc_owner_seed_sw_rw_en_i
//   .lc_seed_hw_rd_en_i
//   .lc_iso_part_sw_rd_en_i
//   .lc_iso_part_sw_wr_en_i

class flash_ctrl_info_part_access_vseq extends flash_ctrl_hw_sec_otp_vseq;
  `uvm_object_utils(flash_ctrl_info_part_access_vseq)
  `uvm_object_new

  typedef enum {
    AccessTest,
    ReadOnlyTest,
    WriteOnlyTest
  } test_type_e;

  virtual task body();
    int round = 0;
    flash_init = FlashMemInitRandomize;
    reset_flash();

    // INITIALIZE FLASH REGIONS
    init_sec_info_part();
    $assertoff(0, "prim_lc_sync");
    cfg.seq_cfg.check_mem_post_tran = 1;

    repeat (10) begin
      `uvm_info(`gfn, $sformatf("iter:%0d", round++), UVM_LOW)

      check_lc_ctrl(cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en, FlashCreatorPart);
      check_lc_ctrl(cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en, FlashOwnerPart);
      randcase
        1: check_lc_ctrl(cfg.flash_ctrl_vif.lc_seed_hw_rd_en, FlashCreatorPart, ReadOnlyTest);
        1: check_lc_ctrl(cfg.flash_ctrl_vif.lc_seed_hw_rd_en, FlashOwnerPart, ReadOnlyTest);
      endcase
      randcase
        1: check_lc_ctrl(cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en, FlashIsolPart, WriteOnlyTest);
        1: check_lc_ctrl(cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en, FlashIsolPart, ReadOnlyTest);
      endcase
    end
  endtask // body

  task check_lc_ctrl(lc_ctrl_pkg::lc_tx_t sig, flash_sec_part_e part,
                     test_type_e test = AccessTest);
    flash_op_e flash_op;
    bit is_valid;

    if (test == AccessTest) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_op,
                                         flash_op != FlashOpInvalid;)
    end else if (test  == ReadOnlyTest) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_op,
                                         flash_op == FlashOpRead;)
    end else begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flash_op,
                                         flash_op inside {FlashOpProgram, FlashOpErase};)
    end

    sig = get_rand_lc_tx_val(.t_weight(1), .f_weight(1), .other_weight(4));
    is_valid = is_lc_ctrl_valid(sig);

    `uvm_info(`gfn, $sformatf("Check sig:0x%x(is_valid:%0d) part:%s op:%s testype:%s",
                              sig, is_valid, part.name, flash_op.name, test.name), UVM_LOW)

    do_flash_op_info_part(part, flash_op, is_valid);
  endtask // check_lc_ctrl

  // Task to access secret info partition.
  // lc control should be set from the exernal task.
  task do_flash_op_info_part(flash_sec_part_e part, flash_op_e op, bit is_valid);
    data_q_t flash_op_data;
    flash_op_t flash_op;
    flash_op.op = op;
    flash_op.erase_type = FlashErasePage;

    case (part)
      FlashCreatorPart: begin
        flash_op.addr      = FlashCreatorPartStartAddr;  // Fixed Val
        flash_op.num_words = FullPageNumWords;  // Fixed Val
        flash_op.partition = FlashPartInfo;
      end
      FlashOwnerPart: begin
        flash_op.addr      = FlashOwnerPartStartAddr;  // Fixed Val
        flash_op.num_words = FullPageNumWords;  // Fixed Val
        flash_op.partition = FlashPartInfo;
      end
      FlashIsolPart: begin
        flash_op.addr      = FlashIsolPartStartAddr;  // Fixed Val
        flash_op.num_words = FullPageNumWords;  // Fixed Val
        flash_op.partition = FlashPartInfo;
      end
      default: `uvm_error(`gfn, $sformatf("%s partition is not supported in this task",
                                          part.name))
    endcase


    flash_op_data = '{};
    case (op)
      FlashOpErase: begin
        if (!is_valid) set_otf_exp_alert("recov_err");
        flash_ctrl_start_op(flash_op);
        wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
        cfg.flash_mem_bkdr_erase_check(.flash_op(flash_op), .check_match(is_valid));
      end
      FlashOpProgram: begin
        for (int i = 0; i < flash_op.num_words; i++) begin
          flash_op_data[i] = $urandom_range(0, 2 ** (TL_DW) - 1);
        end
        if (!is_valid) begin
          repeat(32) set_otf_exp_alert("recov_err");
        end
        // This task issues flash_ctrl.control write 32 times
        flash_ctrl_write_extra(flash_op, flash_op_data, is_valid);

      end
      FlashOpRead: begin
        if (!is_valid) set_otf_exp_alert("recov_err");
        flash_ctrl_start_op(flash_op);
        flash_ctrl_read(flash_op.num_words, flash_op_data, 1);
        wait_flash_op_done();
        cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data, is_valid);
      end
      default: `uvm_error(`gfn, $sformatf("%s op is not supported in this task",
                                          op.name))
    endcase
  endtask

  task init_sec_info_part();
    flash_bank_mp_info_page_cfg_t info_regions = '{default: MuBi4True};

    for (int i = 1; i < 4; i++) begin
      flash_ctrl_mp_info_page_cfg(0, 0, i, info_regions);
    end
  endtask // init_info_part

endclass // flash_ctrl_info_part_access_vseq
