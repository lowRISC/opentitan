// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Perform accesses in order to provoke memory permission errors. Test the Software
// interface (Erase, Program, Read).

// flash_ctrl_error_mp Test

// Pseudo Code
// Initialize Random Flash MP Regions, Enable All Default Regions
// Loop (x)
//   Randomize a Flash Program Operation (any Partition)
//   Predict if the selected operation will cause an MP violation, or not
//   Set scoreboard to accept alert, if predicted
//   Perform selected Flash Operation
//   If no violation is expected, check data integrity (via backdoor)
//   Check Status Registers
// End

class flash_ctrl_error_mp_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_error_mp_vseq)

  `uvm_object_new

  // Class Members
  bit             poll_fifo_status = 1;
  uint            num_iter;
  rand flash_op_t flash_op;
  rand data_q_t   flash_op_data;
  rand uint       bank;
  uint            prog_err_cnt  = 0;
  uint            read_err_cnt  = 0;
  uint            erase_err_cnt = 0;

  // Copies of the MP Region Settings (Data and Info Partitions)
  flash_mp_region_cfg_t mp_data_regions[flash_ctrl_pkg::MpRegions];
  flash_bank_mp_info_page_cfg_t
    mp_info_regions[flash_ctrl_pkg::NumBanks][flash_ctrl_pkg::InfoTypes][$];

  // Constraint for Bank.
  constraint bank_c {bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};}

  // Constraint for controller address to be in the relevant range for
  // the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

  // Constraint for the Flash Operation
  constraint flash_op_c {

    // Bank Erase is only supported for Data & 1st Info Partitions
    flash_op.partition != FlashPartData && flash_op.partition != FlashPartInfo ->
     flash_op.erase_type == flash_ctrl_pkg::FlashErasePage;

    if (cfg.seq_cfg.op_readonly_on_info_partition) {
      flash_op.partition == FlashPartInfo -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 -> flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (cfg.seq_cfg.op_readonly_on_info2_partition) {
      if (flash_op.partition == FlashPartInfo2) {flash_op.op == flash_ctrl_pkg::FlashOpRead;}
    }

    flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram,
                        flash_ctrl_pkg::FlashOpErase};

    flash_op.erase_type dist {
      flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.num_words inside {[10 : FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]]};
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth];
  }

  // Flash ctrl operation data queue - used for programing or reading the flash.
  constraint flash_op_data_c {
    solve flash_op before flash_op_data;
    if (flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram}) {
      flash_op_data.size() == flash_op.num_words;
    } else {
      flash_op_data.size() == 0;
    }
  }

  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {

    foreach (mp_regions[i]) {

      mp_regions[i].en dist {
        MuBi4False := 1,
        MuBi4True  := 4
      };
      mp_regions[i].program_en dist {
        MuBi4False := 4,
        MuBi4True  := 1
      };
      mp_regions[i].erase_en dist {
        MuBi4False := 4,
        MuBi4True  := 1
      };
      mp_regions[i].read_en dist {
        MuBi4False := 4,
        MuBi4True  := 1
      };
      mp_regions[i].scramble_en == MuBi4False;
      mp_regions[i].ecc_en      == MuBi4False;
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
        mp_info_pages[i][j][k].scramble_en == MuBi4False;
        mp_info_pages[i][j][k].ecc_en      == MuBi4False;
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
  mubi4_t default_region_ecc_en;
  mubi4_t default_region_scramble_en;
  rand mubi4_t default_region_he_en;

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

  // Configure sequence knobs to tailor it to seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op (by default)
    cfg.seq_cfg.op_max_words = 16;

    // Configure High Endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // Configure MP Region Enable Prob
    cfg.seq_cfg.mp_region_en_pc = 70;

    // Scoreboard knob for blocking host reads
    cfg.block_host_rd = 1;

  endfunction : configure_vseq

  // Body
  virtual task body();

    // Local Variables
    data_q_t exp_data;
    bit      exp_alert;

    `uvm_info(`gfn, "TEST : error_mp", UVM_LOW)

    // Enable/Disable Flash Regions
    init_flash_regions();

    // Iteration Loop
    num_iter = 200;
    for (int iter = 0; iter < num_iter; iter++) begin
      `uvm_info(`gfn, $sformatf("Iteration : %0d : %0d", iter+1, num_iter), UVM_LOW)

      // Randomize the Members of the Class
      `DV_CHECK_RANDOMIZE_FATAL(this)

      // Model Expected Response
      exp_alert = predict_expected_mp_err_rsp(flash_op);

      // Control HW Access to Info Partitions if Selected
      control_hw_access(flash_op);

      // Initialise Flash Content
      cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
      if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      end else begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
      end

      // Model Expected Response (Error Expected / Pass)
      if (exp_alert) set_otf_exp_alert("recov_err");

      // Do FLASH Operation
      case (flash_op.op)

        // ERASE
        flash_ctrl_pkg::FlashOpErase : begin
          `uvm_info(`gfn, $sformatf("Flash : ERASE exp_alert:%0d", exp_alert), UVM_LOW)
          flash_ctrl_start_op(flash_op);
          wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.erase_timeout_ns));
          if (exp_alert == MP_PASS)
            cfg.flash_mem_bkdr_erase_check(flash_op);
          else
            erase_err_cnt++;
        end

        // PROGRAM
        flash_ctrl_pkg::FlashOpProgram : begin
          `uvm_info(`gfn, $sformatf("Flash : PROGRAM exp_alert:%0d", exp_alert), UVM_LOW)
          exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
          flash_ctrl_start_op(flash_op);
          flash_ctrl_write(flash_op_data, poll_fifo_status);
          wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.prog_timeout_ns));
          if (exp_alert == MP_PASS)
            cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
          else
            prog_err_cnt++;
        end

        // READ
        flash_ctrl_pkg::FlashOpRead : begin
          `uvm_info(`gfn, $sformatf("Flash : READ exp_alert:%0d", exp_alert), UVM_LOW)
          flash_op_data.delete();
          flash_ctrl_start_op(flash_op);
          flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
          wait_flash_op_done(.clear_op_status(0), .timeout_ns(cfg.seq_cfg.read_timeout_ns));
          if (exp_alert == MP_PASS)
            cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
          else
            read_err_cnt++;
        end

        default : `uvm_fatal(`gfn, "Unrecognized Flash Operation, FAIL")

      endcase

      // Predict Status (for RAL)
      ral.err_code.mp_err.predict(exp_alert);

      // Check Alert Status
      check_exp_alert_status(exp_alert, "mp_err", flash_op, flash_op_data);
    end

    // Final Statistics for Information
    display_test_stats();
  endtask : body

  // Task to initialize the Flash Access (Enable All Regions)
  virtual task init_flash_regions();

    // Default Region Settings
    default_region_read_en     = MuBi4True;
    default_region_program_en  = MuBi4True;
    default_region_erase_en    = MuBi4True;
    default_region_scramble_en = MuBi4False;
    default_region_ecc_en      = MuBi4False;

    // Configure Bank Erasability
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // Copy mp_regions settings, so we only apply one configuration per test.
    mp_data_regions = mp_regions;

    // Initialize MP Region Settings
    foreach (mp_data_regions[i]) begin
      flash_ctrl_mp_region_cfg(i, mp_data_regions[i]);
      `uvm_info(`gfn, $sformatf("MP DATA Region [%0d] : %p", i, mp_data_regions[i]), UVM_MEDIUM)
    end

    // Initialize Default Regions (other than set above)
    flash_ctrl_default_region_cfg(
      .read_en(default_region_read_en),   .program_en(default_region_program_en),
      .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
      .ecc_en(default_region_ecc_en),     .he_en(default_region_he_en));

    // Initialize Info MP Regions
    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO Region [%0d, %0d, %0d] : %p", i, j, k,
        mp_info_pages[i][j][k]), UVM_MEDIUM)
    end

    // Copy mp_info_pages settings, so we only apply one configuration per test.
    mp_info_regions = mp_info_pages;

  endtask : init_flash_regions

  // Predict the expected MP Error Response (Model)
  virtual function bit predict_expected_mp_err_rsp(input flash_op_t flash_op);

    // Local Variables
    bit rsp;

    /// Flash Operation
    `uvm_info(`gfn, $sformatf("Flash Operation : flash_op : %p", flash_op), UVM_MEDIUM)

    unique case (flash_op.partition)
      FlashPartData : rsp = do_data_part(flash_op);
      FlashPartInfo, FlashPartInfo1, FlashPartInfo2 : rsp = do_info_part(flash_op);
      default : `uvm_fatal(`gfn, "Unrecognised Flash Operation, FAIL")
    endcase

    // Display Expected Response
    if (rsp == MP_PASS)
      `uvm_info(`gfn, "Expect : MP_PASS", UVM_INFO)
    else
      `uvm_info(`gfn, "Expect : MP_VIOLATION", UVM_INFO)

    return (rsp);  // Return Status

  endfunction : predict_expected_mp_err_rsp

  virtual function void control_hw_access(flash_op_t flash_op);
    lc_tx_t  hw_access;
    hw_access = (flash_op.partition inside {FlashPartInfo, FlashPartInfo1, FlashPartInfo2}) ?
      lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
    cfg.flash_ctrl_vif.lc_creator_seed_sw_rw_en = hw_access;
    cfg.flash_ctrl_vif.lc_owner_seed_sw_rw_en   = hw_access;
    cfg.flash_ctrl_vif.lc_iso_part_sw_rd_en     = hw_access;
    cfg.flash_ctrl_vif.lc_iso_part_sw_wr_en     = hw_access;
  endfunction : control_hw_access

  // Model Flash Data Partition Behaviour
  virtual function do_data_part(flash_op_t flash_op);

    // Local Variables
    string op_msg;
    uint   region_start;
    uint   region_end;
    bit [MpRegions-1:0] rsp_vec = (MpRegions)'(MP_PASS);

    display_mp_region_info();

    // Assign op_msg to Op Type (used below)
    unique case (flash_op.op)
      flash_ctrl_pkg::FlashOpErase   : op_msg = "Erase";
      flash_ctrl_pkg::FlashOpProgram : op_msg = "Program";
      flash_ctrl_pkg::FlashOpRead    : op_msg = "Read";
      default : `uvm_fatal(`gfn, "Unrecognised Flash Operation, FAIL")
    endcase

    // Look for MP Area Violations
    foreach (mp_data_regions[i]) begin
      // Start and End Regions for the Flash Operation
      region_start =  mp_data_regions[i].start_page*(FullPageNumWords*4);
      region_end =
        (mp_data_regions[i].start_page+mp_data_regions[i].num_pages)*(FullPageNumWords*4);
      if (flash_op.addr inside {[region_start : region_end - 1]}) begin
        `uvm_info(`gfn, $sformatf("%s : MP Region : Address :  HIT : MPR%0d", op_msg, i),
          UVM_MEDIUM)
        if (mp_data_regions[i].en == MuBi4True) begin
          unique case (flash_op.op)
            flash_ctrl_pkg::FlashOpErase : begin
              // Bank Erase Defeats the MP Settings
              if (flash_op.erase_type == flash_ctrl_pkg::FlashEraseBank)
                rsp_vec[i] = MP_PASS;
              else
                rsp_vec[i] = (mp_data_regions[i].erase_en == MuBi4False);
            end
            flash_ctrl_pkg::FlashOpProgram : rsp_vec[i] =
              (mp_data_regions[i].program_en == MuBi4False);
            flash_ctrl_pkg::FlashOpRead : rsp_vec[i] =
              (mp_data_regions[i].read_en == MuBi4False);
            default : `uvm_fatal(`gfn, "Unrecognised Flash Operation, FAIL")
          endcase
        end else
          rsp_vec[i] = MP_PASS;
      end else begin
        `uvm_info(`gfn, $sformatf("%s : MP Region : Address : MISS : MPR%0d", op_msg, i),
          UVM_MEDIUM)
        rsp_vec[i] = MP_PASS;
      end
    end

    return (|(rsp_vec));

  endfunction : do_data_part

  // Model Flash Info Partition Behaviour
  virtual function do_info_part(flash_op_t flash_op);

    // Local Variables
    uint info_bank;
    uint info_page;
    uint info_part;
    bit  rsp;

    unique case (flash_op.partition)
      FlashPartInfo  : info_part = 0;
      FlashPartInfo1 : info_part = 1;
      FlashPartInfo2 : info_part = 2;
      default : `uvm_fatal(`gfn, "Unrecognised Info Partition, FAIL")
    endcase

    // Info Partition Bank and Page
    info_bank = flash_op.addr[19];
    info_page = flash_op.addr[18:11];
    `uvm_info(`gfn, $sformatf("Info Partition Selected : Info%0d", info_part), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("Bank : %0d, Page : %0d", flash_op.addr[19],
                              flash_op.addr[18:11]), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("MP INFO Regions [%0d, %0d, %0d] : %p", info_bank, info_part,
      info_page, mp_info_regions[info_bank][info_part][info_page]), UVM_MEDIUM)

    // Look for MP Area Violations
    if (mp_info_regions[info_bank][info_part][info_page].en == MuBi4True) begin
      unique case (flash_op.op)
        flash_ctrl_pkg::FlashOpErase : begin
          // Bank Erase Defeats the MP Settings, Only valid for Info Partition (not Info1 or info2)
          if ((info_part == 0) && (flash_op.erase_type == flash_ctrl_pkg::FlashEraseBank))
            rsp = MP_PASS;
          else
            rsp = (mp_info_regions[info_bank][info_part][info_page].erase_en == MuBi4False);
        end
        flash_ctrl_pkg::FlashOpProgram :
          rsp = (mp_info_regions[info_bank][info_part][info_page].program_en == MuBi4False);
        flash_ctrl_pkg::FlashOpRead :
          rsp = (mp_info_regions[info_bank][info_part][info_page].read_en == MuBi4False);
        default : `uvm_fatal(`gfn, "Unrecognised Flash Operation, FAIL")
      endcase
    end
    else
    begin
      // Bank Erase Defeats the MP Settings, Only valid for Info Partition (not Info1 or info2)
      if ((info_part == 0) && (flash_op.op == flash_ctrl_pkg::FlashOpErase) &&
          (flash_op.erase_type == flash_ctrl_pkg::FlashEraseBank))
        rsp = MP_PASS;
      else
        rsp = MP_VIOLATION;
    end

    return (rsp);

  endfunction : do_info_part

  virtual function void display_mp_region_info();
    string en_msg;
    `uvm_info(`gfn, "MP REGION INFORMATION (DATA PARTITIONS)", UVM_MEDIUM)
    foreach (mp_data_regions[i]) begin
      en_msg = (mp_data_regions[i].en == MuBi4True) ? "Enabled": "Disabled";
      `uvm_info(`gfn,
        $sformatf("MPR%0d : From : 0x%03x, To : 0x%03x : From : 0x%08x, To : 0x%08x, %s", i,
          mp_data_regions[i].start_page, mp_data_regions[i].start_page+mp_data_regions[i].num_pages,
            mp_data_regions[i].start_page*(FullPageNumWords*4),
              (mp_data_regions[i].start_page+mp_data_regions[i].num_pages)*(FullPageNumWords*4),
                en_msg), UVM_MEDIUM)
    end
  endfunction :  display_mp_region_info

  // Display Test Statistics, Error/Pass Counts
  virtual task display_test_stats();
    uint pass_cnt = num_iter - (prog_err_cnt + read_err_cnt + erase_err_cnt);
    `uvm_info(`gfn, "Test Statistics", UVM_LOW)
    `uvm_info(`gfn, $sformatf("Program Error : %0d", prog_err_cnt),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("Read Errors   : %0d", read_err_cnt),  UVM_LOW)
    `uvm_info(`gfn, $sformatf("Erase Errors  : %0d", erase_err_cnt), UVM_LOW)
    `uvm_info(`gfn, $sformatf("Passes        : %0d", pass_cnt),      UVM_LOW)
  endtask : display_test_stats

endclass : flash_ctrl_error_mp_vseq
