// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to handle signal level code for the miscellaneous signals without an attached
// UVM agent
interface soc_dbg_ctrl_misc_io_if();
  // Dep packages
  import uvm_pkg::*;
  import dv_utils_pkg::*;
  import soc_dbg_ctrl_env_pkg::*;
  import soc_dbg_ctrl_test_pkg::*;

  // Macro includes
  `include "uvm_macros.svh"
  `include "dv_macros.svh"

  // Imports from packages
  import soc_dbg_ctrl_pkg::soc_dbg_policy_t;
  import soc_dbg_ctrl_pkg::dbg_category_e;
  import lc_ctrl_state_pkg::soc_dbg_state_t;
  import lc_ctrl_state_pkg::SocDbgStBlank;
  import lc_ctrl_state_pkg::SocDbgStPreProd;
  import lc_ctrl_state_pkg::SocDbgStProd;
  import lc_ctrl_pkg::lc_tx_t;
  import lc_ctrl_pkg::On;
  import lc_ctrl_pkg::Off;
  import pwrmgr_pkg::pwr_boot_status_t;
  import rom_ctrl_pkg::pwrmgr_data_t;
  import prim_mubi_pkg::mubi4_test_true_strict;
  import prim_mubi_pkg::mubi4_bool_to_mubi;

  // Variables corresponding to some of the DUT signals
  soc_dbg_policy_t  soc_dbg_policy_bus;
  soc_dbg_state_t   soc_dbg_state;
  lc_tx_t           lc_dft_en;
  lc_tx_t           lc_hw_debug_en;
  lc_tx_t           lc_raw_test_rma;
  pwr_boot_status_t boot_status;
  logic             halt_cpu_boot;
  pwrmgr_data_t     continue_cpu_boot;

  // Methods to manage soc_dbg_policy_bus
  function automatic soc_dbg_policy_t get_soc_dbg_policy_bus();
    return soc_dbg_policy_bus;
  endfunction : get_soc_dbg_policy_bus

  function automatic logic is_soc_dbg_policy_valid();
    return mubi4_test_true_strict(soc_dbg_policy_bus.valid);
  endfunction : is_soc_dbg_policy_valid

  function automatic logic is_soc_dbg_policy_relocked();
    return mubi4_test_true_strict(soc_dbg_policy_bus.relocked);
  endfunction : is_soc_dbg_policy_relocked

  function automatic dbg_category_e get_soc_dbg_policy_category();
    return soc_dbg_policy_bus.category;
  endfunction : get_soc_dbg_policy_category

  // Methods to manage soc_dbg_state
  function automatic void set_soc_dbg_state_blank();
    soc_dbg_state = SocDbgStBlank;
  endfunction : set_soc_dbg_state_blank

  function automatic void set_soc_dbg_state_preprod();
    soc_dbg_state = SocDbgStPreProd;
  endfunction : set_soc_dbg_state_preprod

  function automatic void set_soc_dbg_state_prod();
    soc_dbg_state = SocDbgStProd;
  endfunction : set_soc_dbg_state_prod

  // Methods to manage lc_dft_en
  function automatic void set_lc_dft_en_on();
    lc_dft_en = On;
  endfunction : set_lc_dft_en_on

  function automatic void set_lc_dft_en_off();
    lc_dft_en = Off;
  endfunction : set_lc_dft_en_off

  // Methods to manage lc_hw_debug_en
  function automatic void set_lc_hw_debug_en_on();
    lc_hw_debug_en = On;
  endfunction : set_lc_hw_debug_en_on

  function automatic void set_lc_hw_debug_en_off();
    lc_hw_debug_en = Off;
  endfunction : set_lc_hw_debug_en_off

  // Methods to manage lc_raw_test_rma
  function automatic void set_lc_raw_test_rma_on();
    lc_raw_test_rma = On;
  endfunction : set_lc_raw_test_rma_on

  function automatic void set_lc_raw_test_rma_off();
    lc_raw_test_rma = Off;
  endfunction : set_lc_raw_test_rma_off

  // Methods to manage boot_status
  function automatic void init_boot_status();
    boot_status = '0;
  endfunction : init_boot_status

  function automatic void set_bs_cpu_fetch_en_on();
    boot_status.cpu_fetch_en = On;
  endfunction : set_bs_cpu_fetch_en_on

  function automatic void set_bs_cpu_fetch_en_off();
    boot_status.cpu_fetch_en = Off;
  endfunction : set_bs_cpu_fetch_en_off

  function automatic void set_bs_rom_ctrl_status_done(int index, logic done);
    if (index < 0 || index >= pwrmgr_reg_pkg::NumRomInputs) begin
      `uvm_fatal("SOC_DBG_CTRL_MISC_IO_IF", "Index out of range for boot_status.rom_ctrl_status");
    end
    boot_status.rom_ctrl_status[index].done = mubi4_bool_to_mubi(done);
  endfunction : set_bs_rom_ctrl_status_done

  function automatic void set_bs_rom_ctrl_status_good(int index, logic good);
    if (index < 0 || index >= pwrmgr_reg_pkg::NumRomInputs) begin
      `uvm_fatal("SOC_DBG_CTRL_MISC_IO_IF", "Index out of range for boot_status.rom_ctrl_status");
    end
    boot_status.rom_ctrl_status[index].good = mubi4_bool_to_mubi(good);
  endfunction : set_bs_rom_ctrl_status_good

  function automatic void set_bs_lc_done(logic done);
    boot_status.lc_done = done;
  endfunction : set_bs_lc_done

  function automatic void set_bs_otp_done(logic done);
    boot_status.otp_done = done;
  endfunction : set_bs_otp_done

  function automatic void set_bs_strap_sampled(logic sampled);
    boot_status.strap_sampled = sampled;
  endfunction : set_bs_strap_sampled

  function automatic void set_bs_light_reset_req(logic reset_req);
    boot_status.light_reset_req = reset_req;
  endfunction : set_bs_light_reset_req

  function automatic void set_bs_clk_main_status(logic main_status);
    boot_status.clk_status.main_status = main_status;
  endfunction : set_bs_clk_main_status

  function automatic void set_bs_clk_io_status(logic io_status);
    boot_status.clk_status.io_status = io_status;
  endfunction : set_bs_clk_io_status

  // Methods to manage halt_cpu_boot
  function automatic void enable_halt_cpu_boot();
    halt_cpu_boot = 1'b1;
  endfunction : enable_halt_cpu_boot

  function automatic void disable_halt_cpu_boot();
    halt_cpu_boot = 1'b0;
  endfunction : disable_halt_cpu_boot

  // Methods to manage continue_cpu_boot
  function automatic pwrmgr_data_t get_continue_cpu_boot();
    return continue_cpu_boot;
  endfunction : get_continue_cpu_boot

  function automatic logic is_continue_cpu_boot_done();
    return mubi4_test_true_strict(continue_cpu_boot.done);
  endfunction : is_continue_cpu_boot_done

  function automatic logic is_continue_cpu_boot_good();
    return mubi4_test_true_strict(continue_cpu_boot.good);
  endfunction : is_continue_cpu_boot_good

endinterface : soc_dbg_ctrl_misc_io_if
