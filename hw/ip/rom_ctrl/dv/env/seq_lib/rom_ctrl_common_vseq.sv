// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_common_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_common_vseq)

  `uvm_object_new

  // If this flag is set, we will wait a short time after coming out of reset to allow the DUT to
  // finish its start-up sequence and become available for TL accesses.
  bit pause_after_dut_init = 1'b0;

  extern constraint num_trans_c;
  extern virtual task body();
  extern virtual function void inject_intg_fault_in_passthru_mem(
                                   dv_base_mem mem,
                                   bit [bus_params_pkg::BUS_AW-1:0] addr);
  extern virtual task check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
  extern virtual task dut_init(string reset_kind = "HARD");
  extern virtual task run_passthru_mem_tl_intg_err_vseq(int num_times = 1);

endclass

constraint rom_ctrl_common_vseq::num_trans_c {
  num_trans inside {[1:2]};
}

task rom_ctrl_common_vseq::body();
  run_common_vseq_wrapper(num_trans);
endtask : body

function void rom_ctrl_common_vseq::inject_intg_fault_in_passthru_mem(
                                        dv_base_mem mem,
                                        bit [bus_params_pkg::BUS_AW-1:0] addr);
  bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] rdata;
  bit[tlul_pkg::DataIntgWidth+bus_params_pkg::BUS_DW-1:0] flip_bits;

  rdata = cfg.rom_ctrl_bkdr_util_h.rom_encrypt_read32(addr, 1'b1);

  `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(flip_bits,
      $countones(flip_bits) inside {[1:cip_base_pkg::MAX_TL_ECC_ERRORS]};)

  `uvm_info(`gfn, $sformatf("Backdoor change mem (addr 0x%0h) value 0x%0h by flipping bits %0h",
                            addr, rdata, flip_bits), UVM_LOW)

  cfg.rom_ctrl_bkdr_util_h.rom_encrypt_write32_integ(addr, rdata, 1'b1, flip_bits);
endfunction

task rom_ctrl_common_vseq::check_sec_cm_fi_resp(sec_cm_base_if_proxy if_proxy);
  super.check_sec_cm_fi_resp(if_proxy);
  case (if_proxy.sec_cm_type)
    SecCmPrimCount :
      csr_utils_pkg::csr_rd_check(.ptr(ral.fatal_alert_cause.checker_error), .compare_value(1));
    default :
      `DV_CHECK_EQ(cfg.fsm_vif.get_fsm_state(), rom_ctrl_pkg::Invalid)
  endcase
endtask : check_sec_cm_fi_resp

// A slightly tweaked version of the base dut_init which obeys pause_after_dut_init
task rom_ctrl_common_vseq::dut_init(string reset_kind = "HARD");
  super.dut_init(reset_kind);

  if (pause_after_dut_init) begin
    cfg.fsm_vif.wait_while_reading_low();
  end
endtask

// This task is defined in cip_base_vseq. It tries to run some TL accesses and injects integrity
// errors in parallel. To make it work for rom_ctrl, we need to wait a bit for the DUT to be ready
// for TL accesses.
task rom_ctrl_common_vseq::run_passthru_mem_tl_intg_err_vseq(int num_times = 1);
  cfg.fsm_vif.wait_while_reading_low();
  pause_after_dut_init = 1'b1;

  // Waiting like this takes quite a while, so running with a large value of num_times will cause
  // the test to fail with a UVM phase timeout. Rather than overriding the test_timeout_ns
  // argument in dv_base_test.sv, we have a simple bodge to divide the count down to something
  // that takes a similar time to the other blocks.
  num_times = (num_times + 3) / 4;

  super.run_passthru_mem_tl_intg_err_vseq(num_times);
endtask
