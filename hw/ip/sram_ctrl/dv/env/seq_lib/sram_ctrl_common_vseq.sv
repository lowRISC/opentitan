// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class sram_ctrl_common_vseq extends sram_ctrl_base_vseq;
  `uvm_object_utils(sram_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  bit first_reset;

  bit readback_task_enabled;

  string path_sram_key = {`DUT_HIER_STR, ".key_q"};
  string path_sram_nonce = {`DUT_HIER_STR, ".nonce_q"};

  // adjust delay to issue reset for stress_all_with_rand_reset test,
  // as sram_ctrl tests usually don't run very long
  constraint rand_reset_delay_c {
    rand_reset_delay dist {
      [1 : 1000]             :/ 1,
      [1001 : 10_000]        :/ 4,
      [10_001 : 100_000]     :/ 1
    };
  }

  // Write rubbish to the storage backing memory for a prim_fifo_sync
  function void splat_fifo_storage(string fifo_path, int unsigned depth);
    for (int unsigned i = 0; i < depth; i++) begin
      string storage = $sformatf("%0s.gen_normal_fifo.storage[%0d]", fifo_path, i);
      bit [31:0] value;
      randcase
        1: value = '0;
        1: value = '1;
        1: value = $urandom;
      endcase
      `DV_CHECK_FATAL(uvm_hdl_deposit(storage, value))
    end
  endfunction

  virtual task pre_start();
    string common_seq_type;

    `DV_CHECK_FATAL(uvm_hdl_check_path(path_sram_key))
    `DV_CHECK_FATAL(uvm_hdl_check_path(path_sram_nonce))

    void'($value$plusargs("run_%0s", common_seq_type));

    // To avoid reading out unknown data from mem, do init for mem test after 1st reset
    // Also do init for integrity test to make sure mem has correct integrity
    if ((!uvm_re_match("*mem*", common_seq_type) ||
         !uvm_re_match("*passthru_mem_tl_intg_err", common_seq_type) ||
         !uvm_re_match("*sec_cm", common_seq_type)) &&
        !first_reset) begin
      do_sram_ctrl_init = 1;
      first_reset       = 1;
    end else begin
      do_sram_ctrl_init = 0;
    end

    if (!readback_task_enabled) begin
      // Enable the SRAM readback enable feature. The sram_readback_en task initializes
      // the test randomly with the SRAM readback feature enabled or disabled. During
      // the test, at random points in time, the feature is enabled or disabled.
      do_readback_en = 1;
      readback_task_enabled = 1;
    end else begin
      do_readback_en = 0;
    end

    super.pre_start();
  endtask

  task dut_init(string reset_kind = "HARD");
    // Zero the contents of the sram_ctrl sram request fifos if we're about to do fault injection on
    // their counters. This avoids a problem where we generate a spurious request when the FIFO was
    // actually empty and lots of signals in the design become X. This will let the fifos error
    // signal stuck at X. Zeroing the backing memory avoids that problem.
    splat_fifo_storage("tb.dut.u_tlul_adapter_sram.u_reqfifo", 2);
    splat_fifo_storage("tb.dut.u_tlul_adapter_sram.u_sramreqfifo", 2);

    super.dut_init(reset_kind);
  endtask

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem,
                                                          bit [bus_params_pkg::BUS_AW-1:0] addr);
    bit[bus_params_pkg::BUS_DW-1:0] rdata;
    bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] flip_bits;

    rdata = cfg.mem_bkdr_util_h.sram_encrypt_read32_integ(addr, cfg.scb.key, cfg.scb.nonce, 0);

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flip_bits,
        $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

    `uvm_info(`gfn, $sformatf("Backdoor change mem (addr 0x%0h) value 0x%0h by flipping bits %0h",
                              addr, rdata, flip_bits), UVM_LOW)

    cfg.mem_bkdr_util_h.sram_encrypt_write32_integ(addr, rdata, cfg.scb.key, cfg.scb.nonce, 0,
                                                   flip_bits);
  endfunction

  // Check internal key/nonce are reset to default
  // Check sram access returns d_error after a fault injection
  virtual task check_sram_access_blocked_after_fi();
    otp_ctrl_pkg::sram_key_t internal_key;
    otp_ctrl_pkg::sram_nonce_t internal_nonce;

    // all mem accesses are gated after FI
    cfg.tl_mem_access_gated = 1;
    `DV_CHECK(uvm_hdl_read(path_sram_key, internal_key))
    `DV_CHECK_EQ(internal_key, sram_ctrl_pkg::RndCnstSramKeyDefault)
    `DV_CHECK(uvm_hdl_read(path_sram_nonce, internal_nonce))
    `DV_CHECK_EQ(internal_nonce, sram_ctrl_pkg::RndCnstSramNonceDefault)

    do_rand_ops(.num_ops($urandom_range(5, 20)), .blocking(0), .exp_err_rsp(1));
    csr_utils_pkg::wait_no_outstanding_access();

  endtask : check_sram_access_blocked_after_fi

  // Return 1 if path is a pointer in the prim_count associated with the fifo at fifo_path
  function bit is_ptr_in_prim_counts_fifo(string path, string fifo_path);
    string cnt_path = {fifo_path, ".gen_normal_fifo.u_fifo_cnt"};
    string ptr_rel_paths[] = '{"gen_secure_ptrs.u_rptr", "gen_secure_ptrs.u_wptr"};

    foreach (ptr_rel_paths[i]) begin
      if (path == {cnt_path, ".", ptr_rel_paths[i]}) begin
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  // Return 1 if path is a pointer in a prim_count for a fifo in with the adapter at adapter_path.
  // If returning 1, this also writes to in_req_fifo output argument, setting the bit if this is a
  // request fifo.
  function bit is_ptr_in_adapters_fifo(string path, output bit in_req_fifo);
    string adapter_path = {"tb.dut.u_tlul_adapter_sram"};
    string fifo_paths[] = '{{adapter_path, ".u_reqfifo"},
                            {adapter_path, ".u_sramreqfifo"},
                            {adapter_path, ".u_rspfifo"}};

    foreach (fifo_paths[i]) begin
      if (is_ptr_in_prim_counts_fifo(path, fifo_paths[i])) begin
        in_req_fifo = (i == 0 || i == 1);
        return 1'b1;
      end
    end
    return 1'b0;
  endfunction

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    if (if_proxy.sec_cm_type == SecCmPrimCount) begin
      // If we are injecting an error into a prim_count inside a prim_fifo_sync, we need to disable
      // the DataKnown_A assertion inside the fifo. The problem is that we're telling the FIFO that
      // it contains some elements that it doesn't really contain, so the backing memory is probably
      // 'X, which fails an !$isunknown() check. The touching_fifo bit is computed to figure out
      // whether this is happening.

      bit touching_fifo = 1'b0, touching_req_fifo = 1'b0;

      if (is_ptr_in_adapters_fifo(if_proxy.path, touching_req_fifo)) begin
        if (!enable) begin
          `uvm_info(`gfn, "Doing FI on a prim_fifo_sync. Disabling related assertions", UVM_HIGH)
          $assertoff(0, "tb.dut.u_tlul_adapter_sram.u_reqfifo");
          $assertoff(0, "tb.dut.u_tlul_adapter_sram.u_sramreqfifo");
          $assertoff(0, "tb.dut.u_tlul_adapter_sram.u_rspfifo");
        end else begin
          $asserton(0, "tb.dut.u_tlul_adapter_sram.u_reqfifo");
          $asserton(0, "tb.dut.u_tlul_adapter_sram.u_sramreqfifo");
          $asserton(0, "tb.dut.u_tlul_adapter_sram.u_rspfifo");
        end

        // Disable assertions that we expect to fail if we corrupt a request FIFO. This causes us to
        // generate spurious TL transactions.
        if (touching_req_fifo) begin
          if (!enable) begin
            `uvm_info(`gfn, "Doing FI on a request fifo. Disabling related assertions", UVM_HIGH)
            $assertoff(0, "tb.dut");
            cfg.m_tl_agent_cfg.check_tl_errs = 1'b0;
          end else begin
            $asserton(0, "tb.dut");
            cfg.m_tl_agent_cfg.check_tl_errs = 1'b1;
          end
        end
      end
    end
  endfunction: sec_cm_fi_ctrl_svas

  // Check alert and the corresponding status bit is set.
  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    bit [TL_AW-1:0]  addr;
    bit [TL_DBW-1:0] mask;
    bit [TL_DW-1:0]  rdata;
    bit touching_req_fifo = 1'b0;

    super.check_sec_cm_fi_resp(if_proxy);

    if (is_ptr_in_adapters_fifo(if_proxy.path, touching_req_fifo)) begin
      // Do a backdoor access as the TL-UL bus can be frozen.
      csr_rd_check(.ptr(ral.status.bus_integ_error), .compare_value(1), .backdoor(1));
      // Only execute the function below when not messing around with the request FIFO.
      // If we inject a fault into a request FIFO, we generate spurious TL transactions.
      // Hence, we cannot expect that subsequent TL transactions still work.
      if (!touching_req_fifo) begin
        check_sram_access_blocked_after_fi();
      end
    end else begin
      csr_rd_check(.ptr(ral.status.init_error), .compare_value(1));
      check_sram_access_blocked_after_fi();
    end
  endtask : check_sec_cm_fi_resp

  virtual task check_tl_intg_error_response();
    super.check_tl_intg_error_response();

    check_sram_access_blocked_after_fi();
  endtask : check_tl_intg_error_response

endclass
