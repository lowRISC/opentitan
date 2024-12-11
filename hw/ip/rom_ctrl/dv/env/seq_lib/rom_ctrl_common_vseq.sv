// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_common_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

  // If this flag is set, we will wait a short time after coming out of reset to allow the DUT to
  // finish its start-up sequence and become available for TL accesses.
  bit pause_after_dut_init = 1'b0;

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

  virtual task body();
    run_common_vseq_wrapper(num_trans);
  endtask : body

  virtual function void inject_intg_fault_in_passthru_mem(dv_base_mem mem,
                                                          bit [bus_params_pkg::BUS_AW-1:0] addr);
    bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] rdata;
    bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] flip_bits;

    rdata = cfg.mem_bkdr_util_h.rom_encrypt_read32(addr, RND_CNST_SCR_KEY,
                                                   RND_CNST_SCR_NONCE, 1'b1);

    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flip_bits,
        $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

    `uvm_info(`gfn, $sformatf("Backdoor change mem (addr 0x%0h) value 0x%0h by flipping bits %0h",
                              addr, rdata, flip_bits), UVM_LOW)

    cfg.mem_bkdr_util_h.rom_encrypt_write32_integ(addr, rdata, RND_CNST_SCR_KEY, RND_CNST_SCR_NONCE,
                                                  1'b1, flip_bits);
  endfunction

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
    string adapter_path = {"tb.dut.u_tl_adapter_rom"};
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
          $assertoff(0, "tb.dut.u_tl_adapter_rom.u_reqfifo");
          $assertoff(0, "tb.dut.u_tl_adapter_rom.u_sramreqfifo");
          $assertoff(0, "tb.dut.u_tl_adapter_rom.u_rspfifo");
        end else begin
          $asserton(0, "tb.dut.u_tl_adapter_rom.u_reqfifo");
          $asserton(0, "tb.dut.u_tl_adapter_rom.u_sramreqfifo");
          $asserton(0, "tb.dut.u_tl_adapter_rom.u_rspfifo");
        end

        // Disable assertions that we expect to fail if we corrupt a request FIFO. This causes us to
        // generate spurious TL transactions.
        if (touching_req_fifo) begin
          if (!enable) begin
            `uvm_info(`gfn, "Doing FI on a request fifo. Disabling related assertions", UVM_HIGH)
            $assertoff(0, "tb.dut");
          end else begin
            $asserton(0, "tb.dut");
          end
        end
      end
    end

  endfunction: sec_cm_fi_ctrl_svas

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    uvm_reg_field fatal_cause;
    super.check_sec_cm_fi_resp(if_proxy);
    case (if_proxy.sec_cm_type)
      SecCmPrimCount : begin
        if (!uvm_re_match("*.u_tl_adapter_rom*", if_proxy.path))
          fatal_cause = ral.fatal_alert_cause.integrity_error;
        else
          fatal_cause = ral.fatal_alert_cause.checker_error;
        csr_utils_pkg::csr_rd_check(.ptr(fatal_cause), .compare_value(1));
      end
      default :
        `DV_CHECK_EQ(cfg.rom_ctrl_vif.checker_fsm_state, rom_ctrl_pkg::Invalid)
    endcase
  endtask : check_sec_cm_fi_resp

  // Wait while the dut's checker FSM is in the "ReadingLow" state. This waits the bulk of the time
  // after reset and will finish when the dut is almost ready to start handling TL transactions.
  virtual task wait_while_reading_low();
    while (cfg.rom_ctrl_vif.checker_fsm_state == rom_ctrl_pkg::ReadingLow) begin
      #1000ns;
    end
  endtask

  // A slightly tweaked version of the base dut_init which obeys pause_after_dut_init
  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);

    if (pause_after_dut_init) begin
      wait_while_reading_low();
    end

    // If do_apply_reset is true then super.dut_init just applied a reset and the rom_ctrl sram
    // request fifos will be empty. We might be about to do fault injection on those fifos' counters
    // which will generate spurious requests. But we don't want the request data to be X (because it
    // will cause the fifos' error signals to get stuck at X). Write some arbitrary rubbish to the
    // contents.
    if (do_apply_reset) begin
      splat_fifo_storage("tb.dut.u_tl_adapter_rom.u_reqfifo", 2);
      splat_fifo_storage("tb.dut.u_tl_adapter_rom.u_sramreqfifo", 2);
    end
  endtask

  // This task is defined in cip_base_vseq. It tries to run some TL accesses and injects integrity
  // errors in parallel. To make it work for rom_ctrl, we need to wait a bit for the DUT to be ready
  // for TL accesses.
  virtual task run_passthru_mem_tl_intg_err_vseq(int num_times = 1);
    wait_while_reading_low();
    pause_after_dut_init = 1'b1;

    // Waiting like this takes quite a while, so running with a large value of num_times will cause
    // the test to fail with a UVM phase timeout. Rather than overriding the test_timeout_ns
    // argument in dv_base_test.sv, we have a simple bodge to divide the count down to something
    // that takes a similar time to the other blocks.
    num_times = (num_times + 3) / 4;

    super.run_passthru_mem_tl_intg_err_vseq(num_times);
  endtask

endclass
