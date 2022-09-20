// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_common_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_common_vseq)

  `uvm_object_new

  virtual function void configure_vseq();
    cfg.seq_cfg.max_num_trans = 2;
  endfunction

  virtual task pre_start();
    super.pre_start();
    // After reset, scoreboard need to wait until  wip process is done.
    // Since common reset test is not awared of it, remove check from sb and
    // have each test check read response.
    if (common_seq_type inside {"stress_all_with_rand_reset", "csr_mem_rw_with_rand_reset"}) begin
      cfg.scb_h.skip_read_check = 1'b1;
    end
    // Remove prim from following test until alert issue is resolved
    if (common_seq_type inside {"same_csr_outstanding"}) begin
      foreach (all_csrs[i]) begin
        csr_excl_item csr_excl = get_excl_item(all_csrs[i]);
        if (!uvm_re_match("*prim_reg_block*", all_csrs[i].get_full_name)) begin
          csr_excl.add_excl(all_csrs[i].get_full_name, CsrExclAll, CsrRwTest);
        end

      end
    end else begin
      csr_excl_item csr_excl = ral.get_excl_item();
      csr_excl.add_excl("flash_ctrl_core_reg_block.init", CsrExclAll, CsrAllTests);
    end
  endtask // pre_start

  virtual task body();
    if (common_seq_type == "") void'($value$plusargs("run_%0s", common_seq_type));
    // Each run of sec_cm takes about 10 min.
    // Limit num_trans of sec_cm to 5.
    if (common_seq_type == "sec_cm_fi") run_sec_cm_fi_vseq(5);
    else run_common_vseq_wrapper(num_trans);
  endtask : body

  task run_tl_intg_err_vseq_sub(string ral_name);
    if (!uvm_re_match("*prim_reg_block*", ral_name)) return;
    else super.run_tl_intg_err_vseq_sub(ral_name);
  endtask

  bit skip_check_tl_intg_error;
  virtual task sec_cm_inject_fault(sec_cm_base_if_proxy if_proxy);
    super.sec_cm_inject_fault(if_proxy);
    // disable error check for prim_reg for now
    if (!uvm_re_match("*u_prim_reg*", if_proxy.path)) skip_check_tl_intg_error = 1;
    else skip_check_tl_intg_error = 0;
  endtask
  virtual task check_tl_intg_error_response();
    if (!skip_check_tl_intg_error) begin
      super.check_tl_intg_error_response();
    end
  endtask // check_tl_intg_error_response

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    `uvm_info(`gfn, $sformatf("path: %s", if_proxy.path), UVM_MEDIUM)
    super.check_sec_cm_fi_resp(if_proxy);

    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (!uvm_re_match("*.u_host_rsp_fifo.*", if_proxy.path) |
            !uvm_re_match("*.u_to_rd_fifo.*", if_proxy.path) |
            !uvm_re_match("*.u_rd_storage.*", if_proxy.path)) begin
          csr_rd_check(.ptr(ral.std_fault_status.fifo_err), .compare_value(1));
        end
        if (!uvm_re_match("*.u_flash_hw_if.*", if_proxy.path)) begin
          csr_rd_check(.ptr(ral.std_fault_status.lcmgr_err), .compare_value(1));
        end
      end
      SecCmPrimSparseFsmFlop: begin
        if (!uvm_re_match("*.flash_cores*", if_proxy.path)) begin
          csr_rd_check(.ptr(ral.std_fault_status.phy_fsm_err), .compare_value(1));
        end
        if (!uvm_re_match("*.u_ctrl_arb.*", if_proxy.path)) begin
          csr_rd_check(.ptr(ral.std_fault_status.arb_fsm_err), .compare_value(1));
        end
        if (!uvm_re_match("*.u_flash_hw_if.*", if_proxy.path)) begin
          csr_rd_check(.ptr(ral.std_fault_status.lcmgr_err), .compare_value(1));
        end
      end
      SecCmPrimOnehot: begin
        // Do nothing.
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
      end
    endcase

    csr_rd_check(.ptr(ral.debug_state),
                 .compare_value(flash_ctrl_env_pkg::FlashLcDisabled));
    flash_access_after_disabled();
  endtask // check_sec_cm_fi_resp

   virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    case (if_proxy.sec_cm_type)
      SecCmPrimCount: begin
        if (enable) begin
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rd_storage");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rd_storage");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_host_rsp_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_host_rsp_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rsp_order_fifo");
          $asserton(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rsp_order_fifo");
          $asserton(0, "tb.dut.u_to_rd_fifo.u_rspfifo.DataKnown_A");
        end else begin
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rd_storage");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rd_storage");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_host_rsp_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_host_rsp_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[0].u_core.u_rd.u_rsp_order_fifo");
          $assertoff(0, "tb.dut.u_eflash.gen_flash_cores[1].u_core.u_rd.u_rsp_order_fifo");
          $assertoff(0, "tb.dut.u_to_rd_fifo.u_rspfifo.DataKnown_A");
        end
      end
      SecCmPrimSparseFsmFlop: begin
        if (enable) begin
          $asserton(0, "tb.dut.u_flash_hw_if.DisableChk_A");
        end else begin
          $assertoff(0, "tb.dut.u_flash_hw_if.DisableChk_A");
        end
      end
      SecCmPrimOnehot: begin
        // Do nothing.
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("unexpected sec_cm_type %s", if_proxy.sec_cm_type.name))
      end
    endcase
   endfunction
endclass
