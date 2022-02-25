// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rom_ctrl_common_vseq extends rom_ctrl_base_vseq;
  `uvm_object_utils(rom_ctrl_common_vseq)

  constraint num_trans_c {
    num_trans inside {[1:2]};
  }
  `uvm_object_new

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

  virtual function void sec_cm_fi_ctrl_svas(sec_cm_base_if_proxy if_proxy, bit enable);
    $assertoff(0, "tb.dut.KeymgrValidChk_A");
    $assertoff(0, "tb.kmac_app_if.req_data_if.ValidHighUntilReady_A");
  endfunction: sec_cm_fi_ctrl_svas
endclass
