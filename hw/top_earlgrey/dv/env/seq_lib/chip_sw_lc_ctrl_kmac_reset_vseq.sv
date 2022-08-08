// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence issues two kmac reset (sys domain reset) during and after LC requesting a kmac
// data. Then we check lc state transition status to ensure the kmac reset does not affect the
// result of lc state transition.
class chip_sw_lc_ctrl_kmac_reset_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_lc_ctrl_kmac_reset_vseq)

  `uvm_object_new

  rand bit [7:0] lc_exit_token[TokenWidthByte];
  rand bit [7:0] lc_unlock_token[TokenWidthByte];

  localparam string LC_CTRL_KMAC_REQ =
      "tb.dut.top_earlgrey.u_lc_ctrl.kmac_data_o.valid";

  localparam string LC_CTRL_KMAC_DONE =
      "tb.dut.top_earlgrey.u_lc_ctrl.kmac_data_i.done";

  localparam string SYS_DOMAIN_RESET_REQ =
      "tb.dut.top_earlgrey.u_rv_dm.ndmreset_req_o";

  virtual function void backdoor_override_otp();
    // Override the LC partition to TestUnlocked1 state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStTestUnlocked1);

    // Override the test exit token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret0_partition(
        .unlock_token(dec_otp_token_from_lc_csrs(lc_unlock_token)),
        .exit_token(dec_otp_token_from_lc_csrs(lc_exit_token)));
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    backdoor_override_otp();
  endtask

  virtual task body();
    super.body();

    // Override the C test kLcExitToken with random data.
    sw_symbol_backdoor_overwrite("kLcExitToken", lc_exit_token);

    // Attempt the LC state transition twice:
    // The first time we expect to see a transition failure because the C side will load incorrect
    // exit token data.
    // The second time we expect to see the transition succsessful.
    for (int trans = 1; trans <= 2; trans++) begin
      bit kmac_req, kmac_done;
      bit [TL_DW-1:0] lc_status;
      `uvm_info(`gfn, $sformatf("Start transition %0d/2", trans), UVM_LOW)

      // Wait for SW to finish power on set up.
      `DV_WAIT(cfg.sw_logger_vif.printed_log == "LC transition requested.")

      // Wait until kmac request is sent by LC_CTRL.
      `DV_SPINWAIT(
        while (kmac_req == 0) begin
          `DV_CHECK(uvm_hdl_read(LC_CTRL_KMAC_REQ, kmac_req))
          cfg.clk_rst_vif.wait_clks(1);
        end
      )

      // Issue sys domain reset.
       force_sys_domain_reset(
          "Attempt to force sys_domain reset request during LC_CTRL KMAC data request.");

      // Wait for kmac data request complete.
      `DV_SPINWAIT(
        while (kmac_done == 0) begin
          `DV_CHECK(uvm_hdl_read(LC_CTRL_KMAC_DONE, kmac_done))
          cfg.clk_rst_vif.wait_clks(1);
        end
      )

      // Issue another sys domain reset.
      force_sys_domain_reset(
          "Attempt to force sys_domain reset request after LC_CTRL KMAC data request completed.");

      // For the first transition, expect a kmac token_error.
      if (trans == 1) begin
        `DV_SPINWAIT(
          while (lc_status[LcTokenError] == 0) begin
            csr_rd(.ptr(ral.lc_ctrl.status), .value(lc_status), .backdoor(1));
            `DV_CHECK_EQ(lc_status[LcTransitionSuccessful], 0, $sformatf(
                "LC status error, expect transition not successful but get status value %0h",
                lc_status))
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
          end
        )
        `uvm_info(`gfn, "LC transition has expected token error.", UVM_LOW)

      // For the second transition, expect the transition succeeds.
      end else begin
        `DV_SPINWAIT(
          while (lc_status[LcTransitionSuccessful] == 0) begin
            csr_rd(.ptr(ral.lc_ctrl.status), .value(lc_status), .backdoor(1));
            cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
          end
        )
        `uvm_info(`gfn, "LC transition is successful.", UVM_LOW)
      end

      apply_reset();
      `uvm_info(`gfn, "Apply reset and wait for chip init.", UVM_HIGH)
    end
  endtask

  virtual task force_sys_domain_reset(string msg);
    cfg.clk_rst_vif.wait_clks($urandom_range(0, 10));
    `uvm_info(`gfn, msg, UVM_LOW)
    `DV_CHECK(uvm_hdl_force(SYS_DOMAIN_RESET_REQ, 1))
    cfg.clk_rst_vif.wait_clks($urandom_range(2_000, 3_000));
    `DV_CHECK(uvm_hdl_release(SYS_DOMAIN_RESET_REQ))
    `uvm_info(`gfn, "sys_domain reset released", UVM_LOW)
  endtask
endclass
