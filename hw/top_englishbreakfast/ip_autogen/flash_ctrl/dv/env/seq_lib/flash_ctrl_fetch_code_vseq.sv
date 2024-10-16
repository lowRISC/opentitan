// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_fetch_code Test

// Pseudo Code
// Initialise (All)
// Loop { 32 .. 64
//   Randomize (Read Cycle, Data Partition, Exec Key, Instruction Type)
//   Model and Verify Expected Functionality
//     Do Flash Read, expect code access Allowed/Denied
//     Uses Modeling in the Scorboard to expect TLUL Error when denied
//     Checks Data via Frontdoor/Backdoor and Equal to Zero as required
// }
//
// exec_key==CODE_EXEC_KEY, instr_type=MuBi4False - Allowed, Data Match, No TL Error - Data Access
// exec_key==CODE_EXEC_KEY, instr_type=MuBi4True  - Allowed, Data Match, No TL Error - Code Access
// exec_key!=CODE_EXEC_KEY, instr_type=MuBi4False - Allowed, Data Match, No TL Error - Data Access
// exec_key!=CODE_EXEC_KEY, instr_type=MuBi4True  - Denied,  Data 0,     TL Error    - Code Access
//   x (Don't care)       , instr_type=None       - Denied,              TL Error


class flash_ctrl_fetch_code_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_fetch_code_vseq)

  `uvm_object_new

  // Code Allowed/Denied Flags
  typedef enum bit [1:0] {
     CODE_FETCH_ALLOWED,
     CODE_FETCH_DENIED,
     CODE_FETCH_ERR
  } code_fetch_type_e;

  // Class Members
  bit  poll_fifo_status = 1;
  rand data_q_t flash_op_data;
  rand flash_op_t flash_op;
  rand uint bank;
  rand mubi4_t instr_type;
  rand bit [CODE_EXEC_KEY_W-1:0] exec_key;

  constraint exec_key_c {
    exec_key dist {
      [32'h00000000 : 32'hFFFFFFFF] :/ 2,  // All Keys except CODE_EXEC_KEY Deny Code Access
      CODE_EXEC_KEY                 :/ 1   // CODE_EXEC_KEY Correct 1 in 3, otherwise too Random
    };
  }

  constraint bank_c {bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};}

  // Constraint for controller address to be in relevant range for the selected partition.
  constraint addr_c {
    solve bank before flash_op;
    flash_op.addr inside {[BytesPerBank * bank : BytesPerBank * (bank + 1)]};
    if (flash_op.partition != FlashPartData) {
      flash_op.addr inside
       {[0:InfoTypeBytes[flash_op.partition>>1]-1],
        [BytesPerBank:BytesPerBank+InfoTypeBytes[flash_op.partition>>1]-1]};
    }
  }

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

    if (flash_op.partition == FlashPartInfo2) {flash_op.op == flash_ctrl_pkg::FlashOpRead;}

    flash_op.op inside {flash_ctrl_pkg::FlashOpRead, flash_ctrl_pkg::FlashOpProgram,
                        flash_ctrl_pkg::FlashOpErase};

    flash_op.erase_type dist {
     flash_ctrl_pkg::FlashErasePage :/ (100 - cfg.seq_cfg.op_erase_type_bank_pc),
      flash_ctrl_pkg::FlashEraseBank :/ cfg.seq_cfg.op_erase_type_bank_pc
    };

    flash_op.num_words >= 10;
    flash_op.num_words <= (FlashNumBusWords - flash_op.addr[TL_AW-1:TL_SZW]);
    flash_op.num_words <= cfg.seq_cfg.op_max_words;
    flash_op.num_words < (FlashPgmRes - flash_op.addr[TL_SZW+:FlashPgmResWidth]);
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

  // Bit vector representing which of the mp region cfg CSRs to enable.
  rand bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  // Memory Protection Regions
  constraint en_mp_regions_c {$countones(en_mp_regions) == cfg.seq_cfg.num_en_mp_regions;}

  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en == mubi4_bool_to_mubi(en_mp_regions[i]);
      mp_regions[i].read_en == MuBi4True;
      mp_regions[i].program_en == MuBi4True;
      mp_regions[i].erase_en == MuBi4True;
      mp_regions[i].scramble_en == MuBi4False;
      mp_regions[i].ecc_en == MuBi4False;
      mp_regions[i].he_en dist {
        MuBi4False :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        MuBi4True :/ cfg.seq_cfg.mp_region_he_en_pc
      };

      mp_regions[i].start_page inside {[0 : FlashNumPages - 1]};
      mp_regions[i].num_pages inside {[1 : FlashNumPages - mp_regions[i].start_page]};
      mp_regions[i].num_pages <= cfg.seq_cfg.mp_region_max_pages;

      // If overlap is not allowed, then each configured region is uniquified.
      if (!cfg.seq_cfg.allow_mp_region_overlap) {
        foreach (mp_regions[j]) {
          if (i != j) {
            !mp_regions[i].start_page inside {
              [mp_regions[j].start_page:mp_regions[j].start_page + mp_regions[j].num_pages]
            };
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
          MuBi4True :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  // Default region values
  mubi4_t default_region_read_en = MuBi4True;
  mubi4_t default_region_program_en = MuBi4True;
  mubi4_t default_region_erase_en = MuBi4True;
  mubi4_t default_region_scramble_en = MuBi4False;
  rand mubi4_t default_region_he_en;
  mubi4_t default_region_ecc_en = MuBi4False;

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
      MuBi4True :/ cfg.seq_cfg.default_region_he_en_pc,
      MuBi4False :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op.
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
    string msg;
    uint   num_trans;

    `uvm_info(`gfn, $sformatf("FETCH CODE TEST"), UVM_LOW)

    // Scoreboard knob for Blocking Read Data Checking
    // Checks performed in this test
    cfg.block_host_rd = 0;

    // Iterate
    num_trans = $urandom_range(32, 64);

    for (int i = 0; i < num_trans; i++) begin

      `uvm_info(`gfn, $sformatf("Iteration : %0d / %0d", i + 1, num_trans), UVM_LOW)

      // Enable All Regions
      init_flash_regions();

      // Randomize the Members of the Class (Use Flash Read, and a Data Partition)
      `DV_CHECK_RANDOMIZE_WITH_FATAL(this, flash_op.op == FlashOpRead;
                                           flash_op.partition == FlashPartData;)
      instr_type = get_rand_mubi4_val(.t_weight(2),
                                      .f_weight(2),
                                      .other_weight(1));

      `uvm_info(`gfn, $sformatf(
         "Flash Op : Bank: %0d, flash_op: %0p, flash_op_data: %0p, EXEC Key: 0x%0x, instr_type: %s",
           bank, flash_op, flash_op_data, exec_key, instr_type.name()), UVM_LOW)

      // Note: 'exec_key' and 'instr_type' are randomised with the rest of the class

      // Write Randomly Selected Code Execution Key
      csr_wr(.ptr(ral.exec), .value(exec_key));

      // EXEC Key Value
      msg = (exec_key == CODE_EXEC_KEY) ? "(KEY MATCH)" : "";
      `uvm_info(`gfn, $sformatf("Set: FLASH_CTRL.EXEC: Fetch Code Key : 0x%08x %s", exec_key, msg),
        UVM_LOW)

      // Instruction Type : MuBi4False - Data, MuBi4True - Code
      if (instr_type == MuBi4False) msg = "Data";
      else msg = "Code";
      `uvm_info(`gfn, $sformatf("Code Fetch Type : %s (%s)", instr_type.name(), msg), UVM_LOW)

      // Model Expected Functionality
      if (exec_key == CODE_EXEC_KEY &&
          instr_type inside {MuBi4True, MuBi4False}) begin
        check_code_access(CODE_FETCH_ALLOWED);
      end else begin
        unique case (instr_type)
          MuBi4False: check_code_access(CODE_FETCH_ALLOWED);
          MuBi4True: check_code_access(CODE_FETCH_DENIED);
          default: check_code_access(CODE_FETCH_ERR);
        endcase
      end

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

  // Task to Check Code Access
  virtual task check_code_access(code_fetch_type_e opt);
    bit comp, exp_err;
    // Local Variables
    addr_t read_addr;
    data_t rdata;
    data_t rdata_unused;

    // Note : opt 'CODE_FETCH_ALLOWED' - Access Allowed, 'CODE_FETCH_DENIED' - Access Denied
    exp_err = (opt != CODE_FETCH_ALLOWED);

    // Delete Data Queues
    flash_op_data.delete();
    cfg.flash_rd_data.delete();

    // Read Selected Data Block via SW Access (Frontdoor) and Store
    flash_ctrl_start_op(flash_op);
    flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
    wait_flash_op_done();

    // Read from Memory Interface (Direct Read)
    for (int i = 0; i < flash_op.num_words; i++) begin
      read_addr = flash_op.addr + 4 * i;
      // Note: rdata is omitted, as it cannot be directly compared with Backdoor reads
      do_direct_read(.addr(read_addr), .mask('1), .blocking(cfg.block_host_rd), .check_rdata(0),
                     .instr_type(instr_type), .rdata(rdata_unused), .exp_err_rsp(exp_err),
                     .completed(comp));
      cfg.clk_rst_vif.wait_clks($urandom_range(1, 10));
    end
    csr_utils_pkg::wait_no_outstanding_access();

    // Check SW Read Data vs Host Direct Read Data (stored in cfg.flash_rd_data)
    foreach (flash_op_data[i]) begin
      if (opt == CODE_FETCH_ALLOWED) begin  // Expect Data to Match
        rdata = cfg.flash_rd_data.pop_front();
        `DV_CHECK_EQ(rdata, flash_op_data[i])
      end else if (opt == CODE_FETCH_ERR) begin
        `DV_CHECK_NE(rdata, flash_op_data[i])
      end else  begin // Expect Data to Read Zero
        `DV_CHECK_EQ(rdata, '0)
      end

      `uvm_info(`gfn, $sformatf(
                "Flash SW Read Data: 0x%0h, Flash Direct Read Data: 0x%0h", flash_op_data[i], rdata
                ), UVM_LOW)
    end

  endtask : check_code_access

endclass : flash_ctrl_fetch_code_vseq
