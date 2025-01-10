// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class otp_ctrl_wake_up_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_wake_up_vseq)

  `uvm_object_new

  virtual task otp_ctrl_init();
    super.otp_ctrl_init();
    csr_wr(ral.intr_enable, en_intr);
  endtask

  task body();
    bit [TL_DW-1:0] rand_addr = $urandom_range(CreatorSwCfgOffset,
                                               CreatorSwCfgOffset + CreatorSwCfgSize);
    // check status
    cfg.clk_rst_vif.wait_clks(1);

    // turn on all intr_enable
    csr_wr(ral.intr_enable, (1'b1 << NumOtpCtrlIntr) - 1);
    csr_rd_check(.ptr(ral.status.dai_idle), .compare_value(1));

    // write seq
    csr_wr(ral.direct_access_address, rand_addr);
    csr_wr(ral.direct_access_wdata[0], '1);
    csr_wr(ral.direct_access_cmd, 2);
    wait(cfg.intr_vif.pins[OtpOperationDone] == 1);
    csr_wr(ral.intr_state, 1'b1 << OtpOperationDone);

    // read seq
    csr_wr(ral.direct_access_address, rand_addr);
    csr_wr(ral.direct_access_cmd, 1);
    wait(cfg.intr_vif.pins[OtpOperationDone] == 1);
    csr_rd_check(.ptr(ral.direct_access_rdata[0]), .compare_value('1));
    csr_wr(ral.intr_state, 1'b1 << OtpOperationDone);

    // digest sw error seq
    csr_wr(ral.direct_access_address, CreatorSwCfgOffset + 2);
    csr_wr(ral.direct_access_cmd, 4);
    wait(cfg.intr_vif.pins[OtpOperationDone] == 1);
    wait(cfg.intr_vif.pins[OtpErr] == 1);
    csr_wr(ral.intr_state, (1'b1 << NumOtpCtrlIntr) - 1);

    // digest hw seq
    csr_wr(ral.direct_access_address, HwCfg0DigestOffset);
    csr_wr(ral.direct_access_cmd, 4);
    wait(cfg.intr_vif.pins[OtpOperationDone] == 1);
    csr_wr(ral.intr_state, 1'b1 << OtpOperationDone);

    // check all interrupts are cleared
    csr_rd_check(.ptr(ral.intr_state), .compare_value(0));
  endtask : body

endclass : otp_ctrl_wake_up_vseq
