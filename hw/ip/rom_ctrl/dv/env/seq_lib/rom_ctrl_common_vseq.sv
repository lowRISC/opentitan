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

  virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
    super.check_sec_cm_fi_resp(if_proxy);
    `DV_CHECK_EQ(cfg.rom_ctrl_vif.checker_fsm_state, rom_ctrl_pkg::Invalid)
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
