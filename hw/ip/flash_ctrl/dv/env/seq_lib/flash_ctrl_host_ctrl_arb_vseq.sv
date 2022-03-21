// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// flash_ctrl_host_ctrl_arb Test

// Pseudo Code
// Initialise (All)
// Loop (2) {
//   Initialize Flash Regions (Enable All MP Regions)
//   Number of Flash Operations is set to 64
//   Select a Flash Operation when to Apply an RMA (random)
//   loop (64) {
//     Do SW Flash Operation (random)
//     Apply RMA Request during Flash Operation (at selected point)
//     SW Flash Operations should complete successfully before and during
//       initial RMA Request period, after that when RMA is active, Software
//       is denied access.  This remains valid until the DUT is Reset
//   }
//   Check that the RMA FSM Remains in its final state.
//   Reset DUT
//   Repeat
// }

class flash_ctrl_host_ctrl_arb_vseq extends flash_ctrl_base_vseq;
  `uvm_object_utils(flash_ctrl_host_ctrl_arb_vseq)

  `uvm_object_new

  // Class Members
  bit           poll_fifo_status = 0;
  rand data_q_t flash_op_data;

  rand flash_op_t flash_op;
  rand uint       bank;

  // Constraint for Bank.
  constraint bank_c {
    bank inside {[0 : flash_ctrl_pkg::NumBanks - 1]};
  }

  // Constraint for controller address to be in relevant range the for the selected partition.
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
      flash_op.partition == FlashPartInfo ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (cfg.seq_cfg.op_readonly_on_info1_partition) {
      flash_op.partition == FlashPartInfo1 ->
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
    }

    if (flash_op.partition == FlashPartRedundancy) {
        flash_op.op == flash_ctrl_pkg::FlashOpRead;
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

  // Bit vector representing which of the mp region cfg CSRs to enable.
  rand bit [flash_ctrl_pkg::MpRegions-1:0] en_mp_regions;

  // Memory Protection Regions
  constraint en_mp_regions_c {$countones(en_mp_regions) == cfg.seq_cfg.num_en_mp_regions;}

  rand flash_mp_region_cfg_t mp_regions[flash_ctrl_pkg::MpRegions];

  constraint mp_regions_c {
    solve en_mp_regions before mp_regions;

    foreach (mp_regions[i]) {
      mp_regions[i].en          == en_mp_regions[i];
      mp_regions[i].read_en     == 1;
      mp_regions[i].program_en  == 1;
      mp_regions[i].erase_en    == 1;
      mp_regions[i].scramble_en == 0;
      mp_regions[i].ecc_en      == 0;
      mp_regions[i].he_en dist {
        0 :/ (100 - cfg.seq_cfg.mp_region_he_en_pc),
        1 :/ cfg.seq_cfg.mp_region_he_en_pc
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
        mp_info_pages[i][j][k].en          == 1;
        mp_info_pages[i][j][k].read_en     == 1;
        mp_info_pages[i][j][k].program_en  == 1;
        mp_info_pages[i][j][k].erase_en    == 1;
        mp_info_pages[i][j][k].scramble_en == 0;
        mp_info_pages[i][j][k].ecc_en      == 0;
        mp_info_pages[i][j][k].he_en dist {
          0 :/ (100 - cfg.seq_cfg.mp_info_page_he_en_pc[i][j]),
          1 :/ cfg.seq_cfg.mp_info_page_he_en_pc[i][j]
        };
      }
    }
  }

  bit default_region_read_en;
  bit default_region_program_en;
  bit default_region_erase_en;
  bit default_region_scramble_en;
  rand bit default_region_he_en;
  rand bit default_region_ecc_en;

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
      1 :/ cfg.seq_cfg.default_region_he_en_pc,
      0 :/ (100 - cfg.seq_cfg.default_region_he_en_pc)
    };
  }

  constraint default_region_ecc_en_c {default_region_ecc_en == 0;}

  // Configure sequence knobs to tailor it to smoke seq.
  virtual function void configure_vseq();

    // Do no more than 16 words per op.
    cfg.seq_cfg.op_max_words = 16;

    // Enable NO memory protection regions
    cfg.seq_cfg.num_en_mp_regions = 0;

    // Enable High Endurance
    cfg.seq_cfg.mp_region_he_en_pc      = 50;
    cfg.seq_cfg.default_region_he_en_pc = 50;

    // Enable Read Only on Info Partitions
    cfg.seq_cfg.op_readonly_on_info_partition  = 1;
    cfg.seq_cfg.op_readonly_on_info1_partition = 1;

  endfunction : configure_vseq

  // Body
  virtual task body();

    // Local Variables
    bit    result;
    uint   apply_rma;
    uint   num_ops;
    event  ev_rma_req;
    string dut_prb;
    uint   rd_prb;
    logic [RmaSeedWidth-1:0] rma_seed;

    `uvm_info(`gfn, $sformatf("HOST CONTROL ARB TEST"), UVM_LOW)

    // Iterate (Fixed to 2) Per Run
    for (int i=0; i<2; i++)
    begin

      `uvm_info(`gfn, $sformatf("Iteration : %0d", i), UVM_LOW)

      // Enable All Regions
      init_flash_regions();

      `uvm_info(`gfn, "Start SW Flash Operations, then randomly apply an RMA Request", UVM_HIGH)

      // Define Number of Flash Operations, and when to apply the RMA Request in parallel
      num_ops   = 64;
      apply_rma = $urandom_range((num_ops/2)-16, (num_ops/2)+16);

      `uvm_info(`gfn, $sformatf("Apply RMA at Flash Operation : %0d", apply_rma+1), UVM_LOW)

      // Perform random Flash Operations, and send an RMA Request when required
      fork
        begin
          for (int op_cnt=0; op_cnt<num_ops; op_cnt++) begin
            if (op_cnt == apply_rma) -> ev_rma_req;
            do_sw_op(op_cnt, apply_rma, num_ops);
          end
        end
        begin
          @(ev_rma_req);
          cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
          `uvm_info(`gfn, "RMA REQUEST", UVM_LOW)
          rma_seed = $urandom;
          send_rma_req(rma_seed);
        end
      join

      // Check the End State Of the RMA FSM - Uses Internal DUT Probing
      dut_prb = PRB_RMA_FSM;

      repeat (16)
      begin
         #($urandom_range(1000, 5000)*1us);
         if (!uvm_hdl_read(dut_prb, rd_prb))
           `uvm_error(`gfn, $sformatf("Unable to Read from DUT Probe : %s, FAIL", dut_prb))

          if (rd_prb == RMA_FSM_STATE_ST_RMA_RSP)
            `uvm_info(`gfn, "RMA FSM Remains in Final State 'StRmaRsp' - PASS", UVM_LOW)
          else
            `uvm_error(`gfn, "RMA FSM NOT in Final State 'StRmaRsp' - FAIL")
      end

      // RESET DUT

      `uvm_info(`gfn, "RESET DUT", UVM_LOW)
      lc_ctrl_if_rst();  // Restore lc_ctrl_if to Reset Values
      apply_reset();

    end

  endtask : body

  // Task to do a Software Flash Operation, checking arbitration between SW and RMA
  virtual task do_sw_op(input uint op_cnt, input uint apply_rma, input uint num_ops);

    // Local Variables
    data_q_t exp_data;

    // Randomize The Members of the Class
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `uvm_info(`gfn, $sformatf(
      "Flash Operation : Bank: %0d, flash_op: %0p, flash_op_data: %0p",
        bank, flash_op, flash_op_data), UVM_LOW)

    // If the 'Info' Partition is Selected, Turn On the HW Access Signals
    // to allow SW access to Creator, Owner and Isolation Partitions
    en_sw_rw_part_info(flash_op, lc_ctrl_pkg::On);

    // Note: Once the RMA has started, these backdoor calls fail,
    //       so only apply them when SW has access
    if (op_cnt <= apply_rma) begin
      // Initialise Flash Content
      cfg.flash_mem_bkdr_init(flash_op.partition, FlashMemInitInvalidate);
      if (flash_op.op == flash_ctrl_pkg::FlashOpProgram) begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitSet));
      end else begin
        cfg.flash_mem_bkdr_write(.flash_op(flash_op), .scheme(FlashMemInitRandomize));
      end
    end

    `uvm_info(`gfn, $sformatf("Flash Operation : %0d / %0d", op_cnt+1, num_ops), UVM_LOW)

    // Start Controller Read, Program or Erase
    unique case (flash_op.op)

      FlashOpRead :
        begin
          flash_op_data.delete();
          flash_ctrl_start_op(flash_op);
          if (op_cnt <= apply_rma) begin  // Expect Success
            flash_ctrl_read(flash_op.num_words, flash_op_data, poll_fifo_status);
            wait_flash_op_done();
            `uvm_info(`gfn, $sformatf("Read Data : %0p", flash_op_data), UVM_LOW)
            cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
          end else begin  // Expect Fail
            expect_flash_op_fail();
          end
        end

      FlashOpProgram :
        begin
          exp_data = cfg.calculate_expected_data(flash_op, flash_op_data);
          flash_ctrl_start_op(flash_op);
          if (op_cnt <= apply_rma) begin  // Expect Success
            flash_ctrl_write(flash_op_data, poll_fifo_status);
            wait_flash_op_done(.timeout_ns(cfg.seq_cfg.prog_timeout_ns));
            `uvm_info(`gfn, $sformatf("Program Data : %0p", flash_op_data), UVM_LOW)
            cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
          end else begin  // Expect Fail
            expect_flash_op_fail();
          end
        end

      FlashOpErase :
      begin
        flash_ctrl_start_op(flash_op);
        if (op_cnt <= apply_rma) begin  // Expect Success
          wait_flash_op_done(.timeout_ns(cfg.seq_cfg.erase_timeout_ns));
          `uvm_info(`gfn, "Erase Data", UVM_LOW)
          cfg.flash_mem_bkdr_erase_check(flash_op, exp_data);
        end else begin  // Expect Fail
          expect_flash_op_fail();
        end
      end

      default : `uvm_fatal(`gfn, "Flash Operation Unrecognised, FAIL")

    endcase

    // If the 'Info' Partition is Selected, Turn Off the HW Access Signals
    // to disallow SW access to Creator, Owner and Isolation Partitions
    en_sw_rw_part_info (flash_op, lc_ctrl_pkg::Off);

    // Delay and resync to clk
    #($urandom_range(100, 500)*0.01ms);
    cfg.clk_rst_vif.wait_clks(1);

  endtask : do_sw_op

  // Task to initialize the Flash Access (Enable All Regions)
  virtual task init_flash_regions();

    // Default Region Settings
    default_region_read_en     = 1;
    default_region_program_en  = 1;
    default_region_erase_en    = 1;
    default_region_scramble_en = 0;

    // Enable Bank Erase
    flash_ctrl_bank_erase_cfg(.bank_erase_en(bank_erase_en));

    // Initialize MP Regions
    foreach (mp_regions[k]) begin
      flash_ctrl_mp_region_cfg(k, mp_regions[k]);
      `uvm_info(`gfn, $sformatf("MP regions values %p", mp_regions[k]), UVM_HIGH)
    end

    // Initialize Default Regions
    flash_ctrl_default_region_cfg(
        .read_en (default_region_read_en),  .program_en (default_region_program_en),
        .erase_en(default_region_erase_en), .scramble_en(default_region_scramble_en),
        .ecc_en  (default_region_ecc_en),   .he_en      (default_region_he_en));

    // Initialize Info MP Regions
    foreach (mp_info_pages[i, j, k]) begin
      flash_ctrl_mp_info_page_cfg(i, j, k, mp_info_pages[i][j][k]);
      `uvm_info(`gfn, $sformatf("MP INFO regions values %p", mp_info_pages[i][j][k]), UVM_HIGH)
    end

  endtask : init_flash_regions

  // Task to wait for a Flash Operation Fail, and display this status
  virtual task expect_flash_op_fail();

    // Local Variables
    bit result;

    wait_flash_op_done_expect_timeout(.timeout_ns(100000), .result(result));
    if (result == 1)  // Expect a Timeout
      `uvm_info(`gfn,  "Timeout Seen - RMA is Blocking SW Access, Expected, PASS", UVM_LOW)
    else
      `uvm_error(`gfn, "Timeout Not Seen - RMA is NOT Blocking SW Access, Unexpected, FAIL")

  endtask : expect_flash_op_fail

endclass : flash_ctrl_host_ctrl_arb_vseq
