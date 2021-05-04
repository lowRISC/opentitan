// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_dai_errs_vseq is developed to randomly read/write to any address within OTP:
// - A writeblank error will be triggered if write to a non-empty address
// - An access error will be triggered if write to lc partition via DAI interface, or if DAI write
//   to digest addrs for non-sw partitions
`define PART_ADDR_RANGE(i) \
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - 1)]}

class otp_ctrl_dai_errs_vseq extends otp_ctrl_dai_lock_vseq;
  `uvm_object_utils(otp_ctrl_dai_errs_vseq)

  `uvm_object_new

  constraint num_trans_c {
    num_trans  inside {[1:5]};
    num_dai_op inside {[100:500]};
  }

  constraint partition_index_c {part_idx inside {[CreatorSwCfgIdx:LifeCycleIdx]};}

  constraint dai_wr_legal_addr_c {
    if (part_idx == CreatorSwCfgIdx) dai_addr inside `PART_ADDR_RANGE(CreatorSwCfgIdx);
    if (part_idx == OwnerSwCfgIdx)   dai_addr inside `PART_ADDR_RANGE(OwnerSwCfgIdx);
    if (part_idx == HwCfgIdx)        dai_addr inside `PART_ADDR_RANGE(HwCfgIdx);
    if (part_idx == Secret0Idx)      dai_addr inside `PART_ADDR_RANGE(Secret0Idx);
    if (part_idx == Secret1Idx)      dai_addr inside `PART_ADDR_RANGE(Secret1Idx);
    if (part_idx == Secret2Idx)      dai_addr inside `PART_ADDR_RANGE(Secret2Idx);
    if (part_idx == LifeCycleIdx)    dai_addr inside `PART_ADDR_RANGE(LifeCycleIdx);
    solve part_idx before dai_addr;
  }

  function void pre_randomize();
    this.dai_wr_blank_addr_c.constraint_mode(0);
    this.no_access_err_c.constraint_mode(0);
    this.num_iterations_up_to_num_valid_addr_c.constraint_mode(0);
    collect_used_addr = 0;
  endfunction

endclass

`undef PART_ADDR_RANGE
