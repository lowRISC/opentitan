// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class clkmgr_common_vseq extends clkmgr_base_vseq;
  `uvm_object_utils(clkmgr_common_vseq)

  constraint num_trans_c {num_trans inside {[1 : 2]};}
  `uvm_object_new

  virtual task pre_start();
    csr_excl_item csr_excl = ral.get_excl_item();
    super.pre_start();

    // Remove rw1c type from same_csr_outstanding
    if (common_seq_type == "same_csr_outstanding") begin
      csr_excl.add_excl("clkmgr_reg_block.recov_err_code", CsrExclWrite);
    end
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        csr_rd_check(.ptr(ral.fatal_err_code.idle_cnt), .compare_value(1));
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Unexpected sec_cm_type %0s", if_proxy.sec_cm_type.name))
      end
    endcase
  endtask

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (enable) begin
      $asserton(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $asserton(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
      return;
    end
    if (if_proxy.sec_cm_type == SecCmPrimCount) begin
      $assertoff(0, "tb.dut.FpvSecCmClkMainKmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainAesCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainHmacCountCheck_A");
      $assertoff(0, "tb.dut.FpvSecCmClkMainOtbnCountCheck_A");
    end
  endfunction

  task initialize_on_start();
    super.initialize_on_start();
    // update default idle to false for
    // csr test.
    cfg.clkmgr_vif.idle_i = {NUM_TRANS{MuBi4False}};
  endtask : initialize_on_start

  // override shadow_reg_errors task
  // to cover shadow regs under clock div2, div4
  task poke_and_check_storage_error(dv_base_reg shadowed_csr);
    uvm_reg_data_t  err_val, origin_val, rand_val;
    bkdr_reg_path_e kind;
    int             shadow_reg_width = shadowed_csr.get_msb_pos() + 1;
    string          alert_name = shadowed_csr.get_storage_err_alert_name();

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(
                                       kind, kind inside {BkdrRegPathRtl, BkdrRegPathRtlShadow};)
    csr_peek(.ptr(shadowed_csr), .value(origin_val), .kind(kind));
    err_val = get_shadow_reg_diff_val(shadowed_csr, origin_val);

    csr_poke(.ptr(shadowed_csr), .value(err_val), .kind(kind), .predict(1));
    predict_shadow_reg_status(.predict_storage_err(shadowed_csr.get_shadow_storage_err()));
    `uvm_info(`gfn, $sformatf("backdoor write %s through %s with value 0x%0h",
                              shadowed_csr.`gfn, kind.name, err_val), UVM_HIGH);

    // This non-blocking task checks if the alert is continuously firing until reset is issued.
    if (cfg.m_alert_agent_cfg.exists(alert_name)) begin
      // increase clock delay for shadow regs under clk div2, div4
      cfg.clk_rst_vif.wait_clks(10);
      check_fatal_alert_nonblocking(alert_name);
    end

    // Wait random clock cycles and ensure the fatal alert is continuously firing.
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));

    // Check if CSR write is blocked.
    `DV_CHECK_STD_RANDOMIZE_FATAL(rand_val);
    shadow_reg_wr(.csr(shadowed_csr), .wdata(rand_val), .en_shadow_wr(1));
    csr_rd_check(.ptr(shadowed_csr), .compare_vs_ral(1));

    // Backdoor write back to original value and ensure the fatal alert is continuously firing.
    csr_poke(.ptr(shadowed_csr), .value(origin_val), .kind(kind), .predict(1));

    read_check_shadow_reg_status("Poke_and_check_storage_error task");
    cfg.clk_rst_vif.wait_clks($urandom_range(10, 100));
  endtask


endclass
