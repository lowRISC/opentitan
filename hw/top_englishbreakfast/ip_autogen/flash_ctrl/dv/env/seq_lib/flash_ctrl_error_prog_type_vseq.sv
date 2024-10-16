// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_error_prog_type Test

// Pseudo Code
// Outer Loop (x)
//   Initialize
//   Choose a random Program Type Scheme (Normal and/or Program Repair)
//   Select Scheme via CSR
//   Inner Loop (y)
//     Randomize a Flash Program Operation (Data Partition)
//     Predict whether access will accepted or denied (random prog_sel)
//     Do Flash Op
//     Check prediction above, Pass/Fail
//   End
//   Reset DUT
//  End

class flash_ctrl_error_prog_type_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_error_prog_type_vseq)

  `uvm_object_new

  // Class Members
  bit             poll_fifo_status = 1;
  rand flash_op_t flash_op;
  rand data_q_t   flash_op_data;
  rand uint       bank;
  rand bit [1:0]  prog_type_en;

  // Iteration Limits
  rand uint x_max;
  constraint x_max_c { x_max inside {[8:16]}; }   // Outer Loop - Num Schemes
  rand uint y_max;
  constraint y_max_c { y_max inside {[16:32]}; }  // Inner Loop - Num Transactions

  // Constraint for Bank.
  constraint bank_c {bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};}

  // Constraint for controller address to be in relevant range the for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
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

  // Flash ctrl operation data queue - used for programing in this test
  constraint flash_op_data_c {
    flash_op_data.size() == flash_op.num_words;
  }

  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {

    foreach (mp_regions[i]) {
      mp_regions[i].en == MuBi4False;
      mp_regions[i].read_en == MuBi4True;
      mp_regions[i].program_en == MuBi4True;
      mp_regions[i].erase_en == MuBi4True;
      mp_regions[i].scramble_en == MuBi4False;
      mp_regions[i].ecc_en == MuBi4False;
      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True  :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page inside {[0 : FlashNumPages - 1]};
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;

      // If overlap is not allowed, then each configured region is uniquified.
      // This creates an ascending order of mp_regions that are configured, so we shuffle it in
      // post_randomize.
      if (!cfg.seq_cfg.allow_mp_region_overlap) {
        foreach (mp_regions[j]) {
          if (i != j) {
            !(mp_regions[i].start_page inside {
              [mp_regions[j].start_page:mp_regions[j].start_page + mp_regions[j].num_pages]
            });
          }
        }
      }
    }
  }

  // Information partitions memory protection settings.
  rand flash_bank_mp_info_page_cfg_t
    mp_info_pages[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  constraint mp_info_pages_c {

    foreach (mp_info_pages[i, j]) {
      mp_info_pages[i][j].size() == flash_ctrl_pkg::InfoTypeSize[j];
      foreach (mp_info_pages[i][j][k]) {
        mp_info_pages[i][j][k].en == MuBi4True;
        mp_info_pages[i][j][k].read_en == MuBi4True;
        mp_info_pages[i][j][k].program_en == MuBi4True;
        mp_info_pages[i][j][k].erase_en == MuBi4True;
        mp_info_pages[i][j][k].scramble_en == MuBi4False;
        mp_info_pages[i][j][k].ecc_en == MuBi4False;
        mp_info_pages[i][j][k].he_en dist {
          MuBi4False :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          MuBi4True  :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  mubi4_t default_region_read_en;
  mubi4_t default_region_program_en;
  mubi4_t default_region_erase_en;
  mubi4_t default_region_scramble_en;
  rand mubi4_t default_region_he_en;
  rand mubi4_t default_region_ecc_en;

  // Bank Erasability.
  rand bit [flash_ctrl_pkg::NumBanks-1:0] bank_erase_en;

  constraint bank_erase_en_c {
    foreach (bank_erase_en[i]) {
      bank_erase_en[i] == 1;
    }
  }

  // High Endurance
  constraint default_region_he_en_c {
    default_region_he_en dist {
      MuBi4True  :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  constraint default_region_ecc_en_c {default_region_ecc_en == MuBi4False;}

  // Configure sequence knobs to tailor it to seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op (by default)
    cfg.seq_cfg.op_max_words = 16;

    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Enable High Endurance
    cfg.seq_cfg.mp_region_he_en_pc = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // MAX Delay for an Expected Alert
    cfg.alert_max_delay = cfg.seq_cfg.prog_timeout_ns;

  endfunction : configure_vseq

  // Body
  virtual task body();

    // Local Variables
    bit [1:0] prog_type_en;
    bit       exp_alert;

    `uvm_info(`gfn, "TEST : error_prog_type", UVM_LOW)

    // Outer Loop
    for (int x = 0; x < x_max; x++) begin

      // Enable All Regions
      init_flash_regions();

      // Choose a Flash Program Scheme (Normal and/or Program Repair)
      prog_type_en = $urandom_range(0, 3);

      csr_wr(.ptr(ral.prog_type_en), .value(prog_type_en));
      csr_rd_check(.ptr(ral.prog_type_en), .compare_vs_ral(1));
      display_prog_scheme(prog_type_en);

      // Inner Loop
      for (int y = 0; y < y_max; y++) begin
        `uvm_info(`gfn, $sformatf("Iteration : %0d:%0d", x, y), UVM_LOW)

        // Randomize the Members of the Class (Uses Flash Program, and a Data Partition)
        `DV_CHECK_RANDOMIZE_FATAL(this)

        // Model Expected Response (Violation Expected / Pass)
        exp_alert = predict_expected_err_rsp(prog_type_en, flash_op.prog_sel);

        // Initialise Flash Content
        cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));

        if (exp_alert) set_otf_exp_alert("recov_err");
        // FLASH PROGRAM
        flash_ctrl_start_op(flash_op);
        flash_ctrl_write(flash_op_data, poll_fifo_status);
        wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.prog_timeout_ns));
        `uvm_info(`gfn, $sformatf("Program Data : %0p", flash_op_data), UVM_LOW)

        // Predict Status (for RAL)
        ral.err_code.prog_type_err.predict(exp_alert);

        // Check Status
        check_exp_alert_status(exp_alert, "prog_type_err", flash_op, flash_op_data);
      end

      // RESET DUT
      `uvm_info(`gfn, ">>> RESET <<<", UVM_LOW)
      apply_reset();
    end
  endtask : body

  // Task to initialize the Flash Access (Enable All Regions)
  virtual task init_flash_regions();

    // Default Region Settings
    default_region_read_en     = MuBi4True;
    default_region_program_en  = MuBi4True;
    default_region_erase_en    = MuBi4True;
    default_region_scramble_en = MuBi4False;

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

  // Display The Chosen Program Scheme
  virtual function void display_prog_scheme(input bit [1:0] prog_type_en);
    string flash_program_scheme;
    unique case (prog_type_en)
      2'b00 : flash_program_scheme = "NO SCHEME";
      2'b01 : flash_program_scheme = "NORMAL";
      2'b10 : flash_program_scheme = "REPAIR";
      2'b11 : flash_program_scheme = "NORMAL and REPAIR";
      default : `uvm_fatal(`gfn, "Unrecognised Flash Program Scheme")
    endcase
    `uvm_info(`gfn, $sformatf("FLASH PROGRAM SCHEME : %s", flash_program_scheme), UVM_LOW)
  endfunction : display_prog_scheme

  // Predict the expected Pass/Error Response (Model)
  virtual function bit predict_expected_err_rsp(input bit [1:0] prog_type_en, input bit prog_sel);
    bit    rsp;
    string rsp_str;
    rsp = ~prog_type_en[prog_sel];
    rsp_str = rsp ? "MP_VIOLATION" : "MP_PASS";
    `uvm_info(`gfn, $sformatf("prog_type : %02b, prog_sel : %0b : Expect : %s", prog_type_en,
       prog_sel, rsp_str), UVM_LOW)
    return (rsp);
  endfunction : predict_expected_err_rsp

endclass : flash_ctrl_error_prog_type_vseq
