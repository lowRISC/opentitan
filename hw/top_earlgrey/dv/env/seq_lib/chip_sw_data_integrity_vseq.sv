// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_data_integrity_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_data_integrity_vseq)

  `uvm_object_new

  typedef enum bit [31:0] {
    FaultTargetMainSramData,
    FaultTargetRetSramData,
    FaultTargetMainSramInstr
  } fault_target_e;

  virtual task body();
    fault_target_e fault_target;
    bit [31:0] error_ram_address;
    bit [31:0] error_ram_base;
    bit [31:0] error_ram_size;
    bit [ 7:0] sw_error_ram_base[4];
    bit [ 7:0] sw_error_ram_address[4];
    bit [ 7:0] sw_fault_target[4];

    // This sequence will trigger a fatal sec_cm failure.
    super.body();

    // Randomly select either the main or the retention SRAM.
    `DV_CHECK_STD_RANDOMIZE_FATAL(fault_target)

    // Memory blocks are always aligned to powers of 2, hence we can
    // use the get_addr_mask() function of the RAL model to automatically infer the size.
    if (fault_target == FaultTargetMainSramData) begin
      `uvm_info(`gfn, "Injecting data error in main SRAM.", UVM_MEDIUM)
      error_ram_size = ral.sram_ctrl_main_ram.get_addr_mask() + 1;
      error_ram_base = ral.sram_ctrl_main_ram.default_map.get_base_addr();
    end else if (fault_target == FaultTargetRetSramData) begin
      `uvm_info(`gfn, "Injecting data error in retention SRAM.", UVM_MEDIUM)
      error_ram_size = ral.sram_ctrl_ret_aon_ram.get_addr_mask() + 1;
      error_ram_base = ral.sram_ctrl_ret_aon_ram.default_map.get_base_addr();
    end else begin
      `uvm_info(`gfn, "Injecting instruction error in main SRAM.", UVM_MEDIUM)
      // Get the address of the first instruction of the test program in SRAM.
      sw_symbol_backdoor_read("kSramFunctionTestAddress", sw_error_ram_base);
      error_ram_address = {<<byte{sw_error_ram_base}};
    end

    if (fault_target != FaultTargetMainSramInstr) begin
      // Choose a random address +-10 words around the midpoint of the SRAM so that
      // we do not accidentally clobber data on the stack / heap.
      error_ram_address = error_ram_base +
                          error_ram_size/2 +
                          (($urandom_range(0, 20) - 10) << $clog2(bus_params_pkg::BUS_DBW));
    end

    // Disable scoreboard tl error checks since we will trigger faults which cannot be predicted.
    cfg.en_scb_tl_err_chk = 0;

    // Let SW know the address that will trigger an error when read.
    sw_error_ram_address = {<<byte{error_ram_address}};
    `uvm_info(`gfn, $sformatf("address 0x%x as bytes %p", error_ram_address, sw_error_ram_address),
              UVM_MEDIUM)
    sw_symbol_backdoor_overwrite("kErrorRamAddress", sw_error_ram_address);

    // Communicate the fault target to SW.
    sw_fault_target = {<<byte{fault_target}};
    `uvm_info(`gfn, $sformatf("fault_target 0x%x as bytes %p", fault_target, sw_fault_target),
              UVM_MEDIUM)
    sw_symbol_backdoor_overwrite("kFaultTarget", sw_fault_target);

    // Wait until the test and associated data in SRAM have been loaded.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Entered test_main")

    // And corrupt the data.
    `uvm_info(`gfn, $sformatf(
              "Corrupting memory at address 0x%x, for alert %0d", error_ram_address,
              TopEarlgreyAlertIdRvCoreIbexFatalHwErr), UVM_MEDIUM)
    if (fault_target == FaultTargetRetSramData) begin
      // Double check again that the address range is correct.
      error_ram_size = ral.sram_ctrl_ret_aon_ram.get_addr_mask() + 1;
      error_ram_base = ral.sram_ctrl_ret_aon_ram.default_map.get_base_addr();
      `DV_CHECK(error_ram_address >= error_ram_base)
      `DV_CHECK(error_ram_address < error_ram_base + error_ram_size)
      ret_sram_inject_ecc_error(.addr(error_ram_address));
    end else begin
      // Double check again that the address range is correct.
      error_ram_size = ral.sram_ctrl_main_ram.get_addr_mask() + 1;
      error_ram_base = ral.sram_ctrl_main_ram.default_map.get_base_addr();
      `DV_CHECK(error_ram_address >= error_ram_base)
      `DV_CHECK(error_ram_address < error_ram_base + error_ram_size)
      main_sram_inject_ecc_error(.addr(error_ram_address));
    end
  endtask
endclass
