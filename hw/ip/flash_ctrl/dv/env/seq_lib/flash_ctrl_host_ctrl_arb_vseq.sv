// Copyright lowRISC contributors (OpenTitan project).
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

class flash_ctrl_host_ctrl_arb_vseq extends flash_ctrl_fetch_code_vseq;
  `uvm_object_utils(flash_ctrl_host_ctrl_arb_vseq)

  `uvm_object_new

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

    // Iterate fixed Number of iterations as test time is VERY LONG.
    // Set to 1 always
    uint num_trans = 1;

    `uvm_info(`gfn, $sformatf("HOST CONTROL ARB TEST"), UVM_LOW)
    poll_fifo_status = 0;
    for (int i=0; i < num_trans; i++) begin

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
            // if on the last operation before rma, only check that half the words
            // are correct. This is because upon read completion, the hardware
            // immediately transitions into RMA and clears the read fifos.
            // Thus, even if the read completed correctly, the data likely cannot
            // be read out in time.
            // This is no longer valid after #14244.
            // Leave this comment for sometime until a new update become matured.
            if (op_cnt == apply_rma) begin
              flash_op.num_words = flash_op.num_words;
              cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
            end else begin
              cfg.flash_mem_bkdr_read_check(flash_op, flash_op_data);
            end
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
