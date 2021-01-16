// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// otp_ctrl_dai_errs_vseq is developed to randomly read/write to any address within OTP:
// - A writeblank error will be triggered if write to a non-empty address
// - An access error will be triggered if write to lc partition via DAI interface, or if DAI write
//   to digest addrs for non-sw partitions
class otp_ctrl_dai_errs_vseq extends otp_ctrl_smoke_vseq;
  `uvm_object_utils(otp_ctrl_dai_errs_vseq)

  `uvm_object_new

  constraint num_iterations_c {
    num_trans  inside {[1:5]};
    num_dai_op inside {[100:500]};
  }

  constraint dai_wr_legal_addr_c {
    {dai_addr[TL_AW-1:2], 2'b0} inside {[CreatorSwCfgOffset : (LifeCycleOffset + LifeCycleSize)]};
  }

  function void pre_randomize();
    this.partition_index_c.constraint_mode(0);
    this.dai_wr_blank_addr_c.constraint_mode(0);
    this.no_access_err_c.constraint_mode(0);
    collect_used_addr = 0;
  endfunction

endclass
