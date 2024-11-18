// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gen_comment}
<%
from topgen.lib import Name
%>\
// smoke test vseq to walk through DAI states and request keys
`define PART_CONTENT_RANGE(i) ${"\\"}
    {[PartInfo[``i``].offset : (PartInfo[``i``].offset + PartInfo[``i``].size - DIGEST_SIZE - 1)]}

class otp_ctrl_smoke_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_smoke_vseq)

  `uvm_object_new

  rand bit                           do_req_keys, do_lc_trans;
  rand bit                           access_locked_parts;
  rand bit                           rand_wr, rand_rd, rd_sw_tlul_rd;
  rand bit [TL_DW-1:0]               dai_addr;
  rand bit [TL_DW-1:0]               wdata0, wdata1;
  rand int                           num_dai_op;
  rand otp_ctrl_part_pkg::part_idx_e part_idx;
  rand bit                           check_regwen_val, check_trigger_regwen_val;
  rand bit [TL_DW-1:0]               check_timeout_val;
  rand bit [1:0]                     check_trigger_val;
  rand otp_ecc_err_e                 ecc_otp_err, ecc_chk_err;

  constraint no_access_err_c {access_locked_parts == 0;}

  // LC partition does not allow DAI access (the LC partition is always the last one)
  constraint partition_index_c {part_idx inside {[0:LifeCycleIdx-1]};}

  constraint dai_wr_legal_addr_c {
% for part in otp_mmap.config["partitions"]:
<%
  part_name = Name.from_snake_case(part["name"])
  part_name_camel = part_name.as_camel_case()
%>\
    if (part_idx == ${part_name_camel}Idx)
        dai_addr inside `PART_CONTENT_RANGE(${part_name_camel}Idx);
% endfor
    solve part_idx before dai_addr;
  }

  constraint dai_wr_blank_addr_c {
    dai_addr % 4 == 0;
    if (PartInfo[part_idx].secret) dai_addr % 8 == 0;
  }

  constraint num_trans_c {
    if (cfg.smoke_test) {
      num_trans == 1;
      num_dai_op inside {[1:2]};
    } else {
      num_trans  inside {[1:2]};
      num_dai_op inside {[1:50]};
    }
  }

  constraint regwens_c {
    check_regwen_val         dist {0 :/ 1, 1 :/ 9};
    check_trigger_regwen_val dist {0 :/ 1, 1 :/ 9};
  }

  constraint check_timeout_val_c {
    check_timeout_val inside {0, [100_000:'1]};
  }

  constraint ecc_otp_err_c {ecc_otp_err == OtpNoEccErr;}

  constraint ecc_chk_err_c {ecc_chk_err == OtpNoEccErr;}

  constraint apply_reset_during_pwr_init_cycles_c {
    apply_reset_during_pwr_init_cycles dist {
        [1:5]       :/ 4,
        [6:2000]    :/ 4,
        [2001:4000] :/ 2};
  }

  virtual task dut_init(string reset_kind = "HARD");
    if (do_apply_reset) begin
      lc_prog_blocking = 1;
      super.dut_init(reset_kind);
      csr_wr(ral.intr_enable, en_intr);
    end
  endtask

  virtual task pre_start();
    super.pre_start();
    num_dai_op.rand_mode(0);
    check_lc_err();
  endtask

  virtual task check_lc_err();
    fork
      forever begin
        wait(cfg.otp_ctrl_vif.lc_prog_err == 1);
        lc_prog_blocking = 0;
        wait(lc_prog_blocking == 1);
      end
    join_none;
  endtask

  task body();
    for (int i = 1; i <= num_trans; i++) begin
      bit [TL_DW-1:0] tlul_val;
      if (cfg.stop_transaction_generators()) break;
      `uvm_info(`gfn, $sformatf("starting seq %0d/%0d", i, num_trans), UVM_LOW)

      // to avoid access locked OTP partions, issue reset and clear the OTP memory to all 0.
      if (access_locked_parts == 0) begin
        do_otp_ctrl_init = 1;
        if (i > 1 && do_dut_init) dut_init();
        // after otp-init done, check status
        cfg.clk_rst_vif.wait_clks(1);
        if (!cfg.otp_ctrl_vif.lc_esc_on) begin
          csr_rd_check(.ptr(ral.status.dai_idle), .compare_value(1));
        end
      end
      do_otp_ctrl_init = 0;

      `DV_CHECK_RANDOMIZE_FATAL(this)
      // set consistency and integrity checks
      csr_wr(ral.check_regwen, check_regwen_val);
      csr_wr(ral.check_trigger_regwen, check_trigger_regwen_val);
      csr_wr(ral.check_timeout, check_timeout_val);
      trigger_checks(.val(check_trigger_val), .wait_done(1), .ecc_err(ecc_chk_err));

      if (!$urandom_range(0, 9) && access_locked_parts) write_sw_rd_locks();

      // Backdoor write mubi to values that are not true or false.
      force_mubi_part_access();

      if (do_req_keys && !cfg.otp_ctrl_vif.alert_reqs) begin
        req_otbn_key();
        req_flash_addr_key();
        req_flash_data_key();
        req_all_sram_keys();
      end
      if (do_lc_trans && !cfg.otp_ctrl_vif.alert_reqs) begin
        req_lc_transition(do_lc_trans, lc_prog_blocking);
        if (cfg.otp_ctrl_vif.lc_prog_req == 0) begin
          for (int k = 0; k <= LciIdx; k++) begin
            csr_rd(.ptr(ral.err_code[k]), .value(tlul_val));
          end
        end
      end

      for (int i = 0; i < num_dai_op; i++) begin
        bit [TL_DW-1:0] rdata0, rdata1, backdoor_rd_val;
        if (cfg.stop_transaction_generators()) break;

        `DV_CHECK_RANDOMIZE_FATAL(this)
        // recalculate part_idx in case some test turn off constraint dai_wr_legal_addr_c
        part_idx = part_idx_e'(get_part_index(dai_addr));
        `uvm_info(`gfn, $sformatf("starting dai access seq %0d/%0d with addr %0h in partition %0d",
                  i, num_dai_op, dai_addr, part_idx), UVM_HIGH)

        // OTP write via DAI
        if (rand_wr && !digest_calculated[part_idx]) begin
          dai_wr(dai_addr, wdata0, wdata1);
          if (cfg.otp_ctrl_vif.lc_prog_req == 0) begin
            for (int k = 0; k <= LciIdx; k++) begin
              csr_rd(.ptr(ral.err_code[k]), .value(tlul_val));
            end
          end
        end

        // Inject ECC error.
        if (ecc_otp_err != OtpNoEccErr && dai_addr < LifeCycleOffset) begin
          `uvm_info(`gfn, $sformatf("Injecting ecc error %0d at 0x%x", ecc_otp_err, dai_addr),
                    UVM_HIGH)
          backdoor_rd_val = backdoor_inject_ecc_err(dai_addr, ecc_otp_err);
        end

        if (rand_rd) begin
          // OTP read via DAI, check data in scb
          dai_rd(dai_addr, rdata0, rdata1);
        end

        // if write sw partitions, check tlul window
        if (is_sw_part(dai_addr) && rd_sw_tlul_rd) begin
          uvm_reg_addr_t tlul_addr = cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr));
          // tlul error rsp is checked in scoreboard
          do_otp_rd = 1;
          tl_access(.addr(tlul_addr), .write(0), .data(tlul_val), .blocking(1), .check_rsp(0));
        end

        // Backdoor restore injected ECC error, but should not affect fatal alerts.
        if (ecc_otp_err != OtpNoEccErr && dai_addr < LifeCycleOffset) begin
          `uvm_info(`gfn, $sformatf("Injecting ecc error %0d at 0x%x", ecc_otp_err, dai_addr),
                    UVM_HIGH)
          cfg.mem_bkdr_util_h.write32({dai_addr[TL_DW-3:2], 2'b00}, backdoor_rd_val);
          // Wait for two lock cycles to make sure the local escalation error propagates to other
          // patitions and err_code reg.
          cfg.clk_rst_vif.wait_clks(2);
        end

        // Random lock sw partitions
        if (!$urandom_range(0, 9) && access_locked_parts) write_sw_rd_locks();
        if (!$urandom_range(0, 9) && access_locked_parts) write_sw_digests();
        if ($urandom_range(0, 1)) csr_rd(.ptr(ral.direct_access_regwen), .value(tlul_val));
        if ($urandom_range(0, 1)) csr_rd(.ptr(ral.status), .value(tlul_val));
        if (cfg.otp_ctrl_vif.lc_prog_req == 0) begin
          for (int k = 0; k <= LciIdx; k++) begin
            csr_rd(.ptr(ral.err_code[k]), .value(tlul_val));
          end
        end
      end

      // Read/write test access memory
      otp_test_access();

      // lock digests
      `uvm_info(`gfn, "Trigger HW digest calculation", UVM_HIGH)
      cal_hw_digests();
      if ($urandom_range(0, 1)) csr_rd(.ptr(ral.status), .value(tlul_val));

      if (cfg.otp_ctrl_vif.lc_prog_req == 0) begin
        for (int k = 0; k <= LciIdx; k++) begin
          csr_rd(.ptr(ral.err_code[k]), .value(tlul_val));
        end
      end

      if ($urandom_range(0, 1)) rd_digests();
      if (do_dut_init) dut_init();

      // read and check digest in scb
      rd_digests();

      // send request to the interfaces again after partitions are locked
      if (do_lc_trans && !cfg.otp_ctrl_vif.alert_reqs) begin
        req_lc_transition(do_lc_trans, lc_prog_blocking);
        if (cfg.otp_ctrl_vif.lc_prog_req == 0) begin
          for (int k = 0; k <= LciIdx; k++) begin
            csr_rd(.ptr(ral.err_code[k]), .value(tlul_val));
          end
        end
      end

      if (do_req_keys && !cfg.otp_ctrl_vif.alert_reqs && !cfg.smoke_test) begin
        req_otbn_key();
        req_flash_addr_key();
        req_flash_data_key();
        req_all_sram_keys();
      end

    end

  endtask : body

endclass : otp_ctrl_smoke_vseq

`undef PART_CONTENT_RANGE
