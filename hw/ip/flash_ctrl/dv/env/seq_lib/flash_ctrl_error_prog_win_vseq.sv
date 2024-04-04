// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_error_prog_win Test

// Pseudo Code
// Loop (x)
//   Initialize
//   Choose whether to violate a programming window, or not
//   Randomize a Flash Program Operation (Data Partition)
//   If a violation is selected, adjust Flash Op to give a window violation
//     else, leave it as it was correctly randomized
//   Do Flash Op
//   Model expected response
//   Check prediction above, Pass/Fail
// End

class flash_ctrl_error_prog_win_vseq extends flash_ctrl_fetch_code_vseq;
  `uvm_object_utils(flash_ctrl_error_prog_win_vseq)

  `uvm_object_new

  // Class Members
  rand bit        exp_alert;
  rand uint       extended_num_words;
  rand data_q_t   extended_data;

  // Iteration Limits
  rand uint x_max;
  constraint x_max_c { x_max inside {[64:256]}; }  // Loop - Num Iterations

  // Expect Alert Violation
  constraint exp_alert_c { exp_alert dist {MP_PASS:=3, MP_VIOLATION:=1}; }

  // Extended Num Words (for the Violation Case)
  constraint extended_num_words_c { extended_num_words
    inside {[cfg.seq_cfg.op_max_words+1:cfg.seq_cfg.op_max_words+32]}; }

  // Extended Data Words (for the Violation case)
  constraint extended_data_c {
    solve extended_num_words before extended_data;
    extended_data.size() == extended_num_words;
  }

  // Constraint for the Flash Operation
  constraint flash_op_c {

    flash_op.op == flash_ctrl_pkg::FlashOpProgram;  // Only Flash Program Used in this test
    flash_op.partition == FlashPartData;  // Ony Data Partitions Used in this test

    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];

    flash_op.prog_sel inside {FlashProgSelNormal, FlashProgSelRepair};
  }

  // Configure sequence knobs to tailor it to seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op (by default)
    cfg.seq_cfg.op_max_words = 16;

    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Enable High Endurance
    cfg.seq_cfg.mp_region_he_en_pc = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

  endfunction : configure_vseq

  // Body
  virtual task body();

    // Local Variables
    flash_op_t flash_op_prog_win;
    data_q_t   flash_op_data_prog_win;
    string     alert_str;

    `uvm_info(`gfn, "TEST : error_prog_win", UVM_LOW)

    // Loop
    for (int x = 0; x < x_max; x++) begin

      // Enable All Regions
      init_flash_regions();

      // Randomize Class (flash_op uses Flash Program, and a Data Partition)
      `DV_CHECK_RANDOMIZE_FATAL(this)

      `uvm_info(`gfn, $sformatf("extended_num_words : %0d", extended_num_words), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("extended_data      : %p ", extended_data), UVM_MEDIUM)

      // Display Alert Chosen
      alert_str = exp_alert ? "MP_VIOLATION" : "MP_PASS";
      `uvm_info(`gfn, $sformatf("Expect Alert : %s", alert_str), UVM_LOW)

      // Choose given Flash Op, or Extend Program Window
      flash_op_prog_win = flash_op;  // Copy Op
      if (exp_alert == MP_PASS)  // Normal Window - PASS
        flash_op_data_prog_win = flash_op_data;  // Copy Data
      else begin  // Extended Program Window - VIOLATION
        flash_op_prog_win.num_words = extended_num_words; // Extended Window
        flash_op_data_prog_win = extended_data;
        `uvm_info(`gfn, $sformatf("--> flash_op_data_prog_win : %p",
          flash_op_data_prog_win), UVM_MEDIUM)
      end

      // Initialise Flash Content
      cfg.flash_mem_bkdr_init(flash_op_prog_win.partition, FlashMemInitInvalidate);
      cfg.flash_mem_bkdr_write(.flash_op(flash_op_prog_win), .scheme(FlashMemInitSet));

      // Model Expected Response (Error Expected / Pass)
      if (exp_alert) set_otf_exp_alert("recov_err");

      // FLASH PROGRAM
      flash_ctrl_start_op(flash_op_prog_win);
      flash_ctrl_write(flash_op_data_prog_win, poll_fifo_status);
      wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.prog_timeout_ns));
      `uvm_info(`gfn, $sformatf("Program Data : %0p", flash_op_data_prog_win), UVM_MEDIUM)

      // Predict Alert Status (for RAL)
      ral.err_code.prog_win_err.predict(exp_alert);

      // Check Alert Status
      check_exp_alert_status(exp_alert, "prog_win_err", flash_op, flash_op_data);

    end

  endtask : body

  // Task to initialize the Flash Access (Enable All Regions)
  virtual task init_flash_regions();
    // Enable Bank Erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // Initialize MP Regions
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    // Initialize Default Regions
    flash_ctrl_default_region_cfg(
        .read_en(default_region_read_en), .program_en(default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en(default_region_ecc_en), .he_en(default_region_he_en));

    // Initialize Info MP Regions
    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_HIGH)
    end

  endtask : init_flash_regions

endclass : flash_ctrl_error_prog_win_vseq
