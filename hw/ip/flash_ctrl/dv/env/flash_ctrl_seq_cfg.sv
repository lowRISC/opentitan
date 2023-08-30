// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This clas provides knobs to set the weights for various seq random variables.
class flash_ctrl_seq_cfg extends uvm_object;
  `uvm_object_utils(flash_ctrl_seq_cfg)

  // Randomization weights in percentages, and other related settings.

  // Maximun number of times the vseq is randomized and rerun.
  uint max_num_trans;

  // Memory protection configuration.
  uint num_en_mp_regions;

  // This enables memory protection regions to overlap.
  bit allow_mp_region_overlap;

  // Weights for enable bits for each of the flash banks information partitions memory protection
  //  configuration registers.
  uint mp_info_page_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];

  // When this knob is NOT FlashOpInvalid (default) the selected operation will be the only
  //  operation to run in the test (FlashOpRead, FlashOpProgram, FlashOpErase).
  flash_ctrl_pkg::flash_op_e flash_only_op;

  // Weights to enable read / program and erase for each mem region.
  uint mp_region_en_pc;
  uint mp_region_read_en_pc;
  uint mp_region_program_en_pc;
  uint mp_region_erase_en_pc;
  uint mp_region_scramble_en_pc;
  uint mp_region_ecc_en_pc;
  uint mp_region_he_en_pc;
  uint mp_region_max_pages;

  // Knob to control bank level erasability.
  uint bank_erase_en_pc;

  // Default region knobs.
  uint default_region_read_en_pc;
  uint default_region_program_en_pc;
  uint default_region_erase_en_pc;
  uint default_region_scramble_en_pc;
  uint default_region_ecc_en_pc;
  uint default_region_he_en_pc;

  // Weights to enable read / program and erase for each information partition page.
  // For each of the information partitions in each of the banks there is a single variable to
  //  control all of this partition pages.
  uint mp_info_page_read_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];
  uint mp_info_page_program_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];
  uint mp_info_page_erase_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];
  uint mp_info_page_scramble_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];
  uint mp_info_page_ecc_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];
  uint mp_info_page_he_en_pc[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes];

  // Control the number of flash ops.
  uint max_flash_ops_per_cfg;

  // Flash ctrl op randomization knobs.

  // Partition select. Make sure to keep sum equals to 100.
  uint op_on_data_partition_pc;   // Choose data partition.
  uint op_on_info_partition_pc;   // Choose info partition.
  uint op_on_info1_partition_pc;  // Choose info1 partition.
  uint op_on_info2_partition_pc;  // Choose info2 partition.

  bit avoid_ro_partitions; // Avoid partitions defined as read-only.

  bit op_readonly_on_info_partition;   // Make info  partition read-only.
  bit op_readonly_on_info1_partition;  // Make info1 partition read-only.
  bit op_readonly_on_info2_partition;  // Make info2 partition read-only.

  // Vendor flash model hook
  bit use_vendor_flash = 0;
  string vendor_flash_path = "";  // Use to indicate a vendor flash hierarchical path.
  bit exclude_info2 = 0;
  // Used for expected_alert["fatal_err"].max_delay
  // Vendor can use larger value
  int long_fatal_err_delay = 2000;

  uint op_erase_type_bank_pc;
  uint op_prog_type_repair_pc;
  uint op_max_words;
  bit op_allow_invalid;

  // Poll fifo status before writing to prog_fifo / reading from rd_fifo.
  uint poll_fifo_status_pc;

  // Chances to start flash with all 1s and not with random values (default is 30%).
  uint flash_init_set_pc;

  // Set by a higher level vseq that invokes this vseq.
  bit external_cfg;

  // If pre-transaction back-door memory preperation isn't needed, set do_tran_prep_mem to 0.
  bit do_tran_prep_mem;

  // When 0, the post-transaction back-door checks will be disabled.
  // Added to enable other post-transaction checks and actions.
  bit check_mem_post_tran;

  // Timeout for program transaction
  uint prog_timeout_ns;

  // Timeout for erase transaction
  uint erase_timeout_ns;

  // Expected time for the erase-suspend operation
  uint erase_suspend_expected_time_ns;

  // Timeout for read transaction
  uint read_timeout_ns;

  // Timeout for LC state transition
  uint state_wait_timeout_ns;

  // Enable/Disable the Secret Seeds and Keys during Initialisation
  bit en_init_keys_seeds;

  // States whether to wait for the flash_init to finish before starting the actual sequence.
  bit wait_init_done;

  // Enable/Disable the Random Flash Inititlisation After Reset
  bit disable_flash_init;

  // Path to flash wrapper hierarchy.
  string flash_path_str;

  // NOTE: Make sure to keep
  // cfg.flash_ctrl_vif.rst_to_pd_time_ns < reset_width_clks_lo * clk_period_ns.
  // This will make sure that the power-down assertion will happen before reset deassertion.

  // Low limit of reset assertion time in clock cycles (from assertion to deassertion).
  uint reset_width_clks_lo;

  // High limit of reset assertion time in clock cycles (from assertion to deassertion).
  uint reset_width_clks_hi;

  `uvm_object_new

  // Set partition select percentages. Make sure to keep sum equals to 100.
  virtual function void set_partition_pc(uint sel_data_part_pc = 100, uint sel_info_part_pc = 0,
                                         uint sel_info1_part_pc = 0,
                                         uint sel_info2_part_pc = 0);

    `DV_CHECK_EQ(sel_data_part_pc + sel_info_part_pc + sel_info1_part_pc + sel_info2_part_pc,
                 100, $sformatf(
                 {
                   "Error! sum of arguments must be 100. Be aware of arguments ",
                   "default values - 100 for data partition and 0 for all the ",
                   "others. Arguments current value: sel_data_part_pc=%0d , ",
                   "sel_info_part_pc=%0d , sel_info1_part_pc=%0d , ",
                   "sel_info2_part_pc=%0d"
                 },
                 sel_data_part_pc,
                 sel_info_part_pc,
                 sel_info1_part_pc,
                 sel_info2_part_pc
                 ))

    op_on_data_partition_pc       = sel_data_part_pc;
    op_on_info_partition_pc       = sel_info_part_pc;
    op_on_info1_partition_pc      = sel_info1_part_pc;
    op_on_info2_partition_pc = sel_info2_part_pc;

  endfunction : set_partition_pc

  virtual function void configure();
    max_num_trans                 = 20;

    num_en_mp_regions             = flash_ctrl_pkg::MpRegions;

    allow_mp_region_overlap       = 1'b0;

    mp_region_en_pc               = 50;
    mp_region_read_en_pc          = 50;
    mp_region_program_en_pc       = 50;
    mp_region_erase_en_pc         = 50;
    mp_region_scramble_en_pc      = 0;
    mp_region_ecc_en_pc           = 0;
    mp_region_he_en_pc            = 0;
    mp_region_max_pages           = 32;

    bank_erase_en_pc              = 50;

    default_region_read_en_pc     = 50;
    default_region_program_en_pc  = 50;
    default_region_erase_en_pc    = 50;
    default_region_scramble_en_pc = 0;
    default_region_ecc_en_pc      = 0;
    default_region_he_en_pc       = 0;

    foreach (mp_info_page_en_pc[i, j]) begin
      mp_info_page_en_pc[i][j] = 50;
      mp_info_page_read_en_pc[i][j] = 50;
      mp_info_page_program_en_pc[i][j] = 50;
      mp_info_page_erase_en_pc[i][j] = 50;
      mp_info_page_scramble_en_pc[i][j] = 0;
      mp_info_page_ecc_en_pc[i][j] = 0;
      mp_info_page_he_en_pc[i][j] = 0;
    end

    flash_only_op = FlashOpInvalid;

    max_flash_ops_per_cfg = 50;

    op_readonly_on_info_partition = 0;
    // info1 partition will be read-only by default
    op_readonly_on_info1_partition = 1;

    avoid_ro_partitions = 0;

    op_erase_type_bank_pc = 20;
    op_prog_type_repair_pc = 10;
    op_max_words = 512;
    op_allow_invalid = 1'b0;

    poll_fifo_status_pc = 30;

    flash_init_set_pc = 30;

    external_cfg = 1'b0;

    do_tran_prep_mem = 1'b1;

    check_mem_post_tran = 1'b1;

    prog_timeout_ns                     = 10_000_000;   // 10ms

    read_timeout_ns                     = 100_000;      // 100us

    erase_timeout_ns                    = 120_000_000;  // 120ms

    erase_suspend_expected_time_ns      = 50_000;       // 50us

    state_wait_timeout_ns               = 500_000;      // 500us

    en_init_keys_seeds = 1'b0;  // Off

    // By default, wait for flash to finish initializing process before sending transactions
    //  requests.
    wait_init_done = 1'b1;

    disable_flash_init = 1'b0;  // Off

    flash_path_str = "tb.dut.u_eflash.u_flash.gen_generic.u_impl_generic";

    // NOTE: Make sure to keep
    // cfg.flash_ctrl_vif.rst_to_pd_time_ns < reset_width_clks_lo * min clock period in ns.
    // This will make sure that the power-down assertion will happen before reset deassertion.

    reset_width_clks_lo = 50;

    reset_width_clks_hi = 100;

    set_partition_pc();

  endfunction : configure

endclass
