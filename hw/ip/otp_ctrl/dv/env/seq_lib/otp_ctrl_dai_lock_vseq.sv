// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_dai_lock_vseq is developed to read/write lock DAI interface by partitions, and request
// read/write access to check if correct status and error code is triggered
class otp_ctrl_dai_lock_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_dai_lock_vseq)

  `uvm_object_new

  // enable access_err for each cycle
  constraint no_access_err_c {access_locked_parts == 1;}

  // access locked means no memory clear, constraint to ensure there are enough dai address
  constraint num_iterations_up_to_num_valid_addr_c {
    collect_used_addr -> num_trans * num_dai_op <= DAI_ADDR_SIZE;
  }

  constraint num_trans_c {
    num_trans  inside {[1:10]};
    num_dai_op inside {[1:50]};
  }

  constraint dai_wr_legal_addr_c {
    {dai_addr[TL_AW-1:2], 2'b0} dist {
      {CreatorSwCfgDigestOffset, OwnerSwCfgDigestOffset,HwCfgDigestOffset, Secret0DigestOffset,
       Secret1DigestOffset, Secret2DigestOffset} :/ 1,
      [CreatorSwCfgOffset : (LifeCycleOffset + LifeCycleSize)] :/ 9
    };
  }

  virtual task pre_start();
    super.pre_start();
    is_valid_dai_op = 0;
  endtask

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    if ($urandom_range(0, 1)) cfg.otp_ctrl_vif.drive_lc_creator_seed_sw_rw_en_i(lc_ctrl_pkg::Off);
  endtask;

endclass
