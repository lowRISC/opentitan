// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This vseq stimulates mid-transfer START and STOP conditions to test DUT-Target responses to
// these non-protocol but valid bus events.
// (We refer to this stimulus as 'glitches' within this vseq).
//
// The main function of this vseq is to increase coverage of FSM state transitions
// back to the idle/acquire states upon the early Sr/P conditions short-circuiting the
// normal transfer/transaction process.
//
// Test Procedure:
// - Initialize DUT-Target mode
// - Begin stimulating an i2c transaction using the Agent-Controller.
// - Randomly introduce glitches specified by enum `glitch_e`
//   - For each glitch type, byte transmission will be interrupted causing the internal FSM to
//     go to Idle/AcquireStart state
// - Issue new transactions after glitch to check if DUT is processing transactions as expected

class i2c_target_hrst_vseq extends i2c_target_smoke_vseq;

  ///////////////
  // VARIABLES //
  ///////////////

  // This indicates the index of the transaction we will glitch
  rand uint glitch_txn_num;

  // Protocol glitch type
  rand glitch_e glitch;

  `uvm_object_utils_begin(i2c_target_hrst_vseq)
    `uvm_field_int(glitch_txn_num,           UVM_DEFAULT)
    `uvm_field_enum(glitch_e, glitch,        UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  /////////////////
  // CONSTRAINTS //
  /////////////////

  constraint num_trans_c {num_trans == 5;}

  // This sequence only tests "glitches" in DUT-Target WRITE Transfers.
  // - i2c_glitch_vseq is a directed-test which is responsible for stimulating "glitches" into
  //   primarily READ Transfers.
  constraint rw_bit_c {rw_bit == WriteOnly;}

  // Constrain the glitched transaction position to ensure a number of post-glitch normal
  // transactions can test recovery.
  constraint glitch_txn_num_c {
    glitch_txn_num inside {[0 : num_trans - 2]};
  }

  // Randomize type of glitch
  constraint glitch_c {
    glitch dist {
      AddressByteStart := 1,
      AddressByteStop := 1 ,
      WriteDataByteStart := 1 ,
      WriteDataByteStop := 1
    };
  }

  ///////////////////
  // CLASS METHODS //
  ///////////////////


  virtual task pre_start();
    super.pre_start();
    expected_intr[UnexpStop] = 1;
  endtask


  virtual task body();
    // Intialize DUT in target mode and agent in controller mode
    initialization();

    `uvm_info("cfg_summary",
              $sformatf("target_addr0:0x%x target_addr1:0x%x illegal_addr:0x%x num_trans:%0d",
                        target_addr0, target_addr1, illegal_addr, num_trans), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("vseq summary:\n%s", this.sprint()), UVM_MEDIUM)

    fork
      // Send all transaction stimulus
      // - This includes all the normal transactions, plus the one special one where we apply the
      //   glitch.
      for (uint i = 0; i < num_trans; i++) send_trans(i);
      // Handle all DUT-Controller interrupts, and gracefully stop handlers at end of test
      fork
        while (!cfg.stop_intr_handler) process_target_interrupts();
        stop_target_interrupt_handler();
      join
    join
  endtask : body


  task send_trans(uint i);
    // Agent-Controller sequence to generate stimulus
    i2c_target_base_seq m_i2c_host_seq;

    // Wait for previous stop-condition before proceeding with next transaction.
    if (i > 0) begin
      `DV_WAIT(cfg.m_i2c_agent_cfg.got_stop,, cfg.spinwait_timeout_ns, "target_hrst_vseq")
      cfg.m_i2c_agent_cfg.got_stop = 0;
    end

    `DV_WAIT(cfg.intr_vif.pins[CmdComplete] == 1'b0, "cmd_complete interrupt did not de-assert!")
    // Cleanup for next iteration.
    empty_acqfifo();

    // Check all acqfifo entries have been read before beginning the next transfer.
    `DV_WAIT(`ALL_READS_OCCURRED,,, "Failed check for ALL_READS_OCCURRED")
    `DV_WAIT(`ALL_ACQFIFO_READS_OCCURRED,,, "Failed check for ALL_ACQFIFO_READS_OCCURRED")

    `uvm_info(`gfn, $sformatf("Starting trans(%0d)/num_trans(%0d) (glitch_txn_num=%0d)",
                              i + 1, num_trans, glitch_txn_num + 1), UVM_MEDIUM)

    // Apply a new set of timing parameters for the next transaction.
    // However, don't update new timing params during and right after the glitched runt transaction
    if (!(i inside {glitch_txn_num, (glitch_txn_num + 1)})) begin
      get_timing_values();
      program_registers();
    end

    // Populate item queue that defines the upcoming transaction
    `uvm_create_obj(i2c_target_base_seq, m_i2c_host_seq)
    if (i == glitch_txn_num) begin
      // Disable address randomization for the glitch txn
      cfg.bad_addr_pct = 0;
      // Create the special glitches txn
      create_write_glitch(m_i2c_host_seq.req_q);
      `uvm_info(`gfn, "Generated glitched transaction stimulus now.", UVM_MEDIUM)
    end else begin
      // Create a normal transaction
      generate_agent_controller_stimulus(m_i2c_host_seq.req_q);
    end

    fork
      // Start the agent driving the stimulus sequence
      m_i2c_host_seq.start(p_sequencer.i2c_sequencer_h);
    join

    `uvm_info("seq", $sformatf("End of trans %0d/%0d", i + 1, num_trans), UVM_MEDIUM)

    sent_txn_cnt++;
  endtask: send_trans


  // Populate transaction queue to introduce Start/Stop conditions in Data or Address byte
  function void create_write_glitch(ref i2c_item driver_q[$]);
    `uvm_info(`gfn, $sformatf("Introducing %s glitch", glitch.name()), UVM_LOW)

    // First drive a START condition to begin the transactiona.
    begin
      i2c_item start_txn;
      `uvm_create_obj(i2c_item, start_txn)
      start_txn.drv_type = HostStart;
      driver_q.push_back(start_txn);
    end

    // Address byte
    begin
      i2c_item addr_txn;
      `uvm_create_obj(i2c_item, addr_txn)
      addr_txn.wdata[7:1] = get_target_addr(); // Get one of the two (valid) addresses
      addr_txn.wdata[0] = (rw_bit == ReadOnly) ? i2c_pkg::READ : i2c_pkg::WRITE; // direction bit
      addr_txn.drv_type = HostData;
      driver_q.push_back(addr_txn);
    end

    // If we're adding the glitch into the Addr+Dir byte, create the special driver item now.
    if (glitch inside {AddressByteStart, AddressByteStop}) begin

      i2c_item glitch_txn;
      `uvm_create_obj(i2c_item, glitch_txn)
      case (glitch)
        AddressByteStart: glitch_txn.drv_type = HostRStart; // START glitch
        AddressByteStop: glitch_txn.drv_type = HostStop; // STOP glitch
        default:;
      endcase
      driver_q.push_back(glitch_txn);

      // There should be no entry in the ACQFIFO for an Address byte glitch, since this is a
      // new transaction that never completes addressing the target.
      // Therefore, we don't need to add any further drive stimulus items.
      return;
    end

    // If we're not glitching the address byte, we must be glitching one of the data bytes.
    `DV_CHECK(glitch inside {WriteDataByteStart, WriteDataByteStop}, "Invalid glitch type!")

    // Add glitch in Data byte

    // First add the drive item for the first part of the data byte, which is normal.
    // This special data bytes driver terminates early, allowing us to then drive the glitch
    // condition afterwards.
    begin
      i2c_item data_txn;
      `uvm_create_obj(i2c_item, data_txn)
      data_txn.drv_type = HostDataNoWaitForACK;
      data_txn.wait_cycles = $urandom_range(2, 6); // This makes us only drive a partial byte
      case(glitch)
        WriteDataByteStart: data_txn.wdata = 8'hFF;
        WriteDataByteStop: data_txn.wdata = 8'h00;
        default: `uvm_fatal(`gfn, "Shouldn't get here!")
      endcase
      driver_q.push_back(data_txn);
    end

    // Now drive the glitch itself
    begin
      i2c_item glitch_txn;
      `uvm_create_obj(i2c_item, glitch_txn)
      case(glitch)
        WriteDataByteStart: glitch_txn.drv_type = HostRStart;
        WriteDataByteStop:  glitch_txn.drv_type = HostStop;
        default: `uvm_fatal(`gfn, "Shouldn't get here!")
      endcase
      driver_q.push_back(glitch_txn);
    end

  endfunction


endclass : i2c_target_hrst_vseq
