// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RAL /////////////////////////////////////////////////////////////////////////
//
// The tb's RAL model, similar to most other OpenTitan testbenches, does not use
// a conventional UVM prediction scheme.
// We do not use 'implicit prediction' (auto_predict is left at 0 by default),
// but we do not use a canonical form of 'explicit prediction' either.
// A reg_adapter is configured to make frontdoor accesses, but we do not
// instantiate a uvm_reg_predictor component, and instead predictions are made by
// calling the predict() routine explicitly in the scoreboard/model.
// The scb base-class subscribes to the relevant bus activity and provides
// a method "process_tl_access()" which hooks all bus accesses.
//
// The testbench architect is then responsible for calling predict() when they
// know the DUT's registers have changed value, or should have changed.
// Based on the bus accesses, if the accessed CSRs don't have unusual access
// behaviours, we can simply predict based on the data seen in the bus item.
// This takes the possible access-controls into account, such as RC/RS/WO/W1C/W0C etc.
// (Registers may be read or write sensitive)
//
// However, we still needs to model the internal effect of those accesses to try and
// form new predictions/expectations of the DUT's behaviour.
// This is where the reference_model comes in.
//
// REFMODEL /////////////////////////////////////////////////////////////////////
//
// This (I2C) reference model uses two class variables (exp_wr_item/exp_rd_item) to accumulate
// multiple fifo writes (FMTFIFO,TXFIFO) and reads (ACQFIFO,RXFIFO) into completed i2c_items
// that represent the entire expected transfer/transactions.
//
// As a DUT-Controller, for both writes and reads, we start forming expectations based on the
// first write to the FMTFIFO. This first write sets the transfer direction and address. The
// sequence item is created at this point, but it is not yet complete. We store these
// intermediate-items across multiple CSR accesses, as follows:
//
// - The 'wr' items are formed solely from FMTFIFO writes, starting from a START/RSTART to the
//   next RSTART/STOP. Additional data-only writes (after the start/address) to the FMTFIFO push
//   bytes into the sequence item. Each item therefore represents a single I2C write transfer.
//
// - The 'rd' items are slightly more complex.
//   FMTFIFO writes with readb=1 are used to specify how much data should be read from the bus
//   (into the RXFIFO), so we update the item on these writes. For each of these writes that
//   update the existing item, we clone the item and push it into the 'rd_pending_q[$]'. The
//   item is only discarded/cleared when a 'stop' is seen. For reads which use RCONT to chain
//   longer accesses, this means that multiple items are pushed into the pending queue for a
//   single read transfer.
//
//   These items pushed to 'rd_pending_q[$]' tell us how many data bytes we should expect to
//   read from the RXFIFO. The RXFIFO read handler pops an item from the rd_pending_q, and
//   pushes data into it until it has pushed the number of bytes specified in the item (set from
//   the value written into the fmtfifo.)
//   After the item has been populated with the amount of data it expects, and the 'stop' bit
//   was seen from the fmtfifo, it is pushed into the 'exp_rd_q[$]' for checking against the
//   item captured by the monitor. If RCONT was used to create multiple pending read items in
//   the queue, each time the byte count is reached we pop the next queued item, and add its
//   count to the previous item.
//
//
class i2c_reference_model extends uvm_component;
  `uvm_component_utils(i2c_reference_model)

  i2c_env_cfg cfg;
  i2c_reg_block ral;

  /////////////////////////////////

  // Inputs
  // - Note. that the tl_ul monitor inputs (i.e DUT CSR accesses) are input to the model via the
  //   process_tl_access() method.

  // Complete transfer items from the i2c_monitor
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_wr_obs_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_rd_obs_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_wr_obs_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_rd_obs_fifo;

  // The following ports capture monitor items that contain the state of an in-progress
  // i2c transfer. This is needed to make predictions at a more granual level, based on any
  // mid-transfer input stimulus.
  uvm_tlm_analysis_fifo #(i2c_item) controller_mode_in_progress_fifo;
  uvm_tlm_analysis_fifo #(i2c_item) target_mode_in_progress_fifo;

  // Outputs

  uvm_analysis_port #(i2c_item) controller_mode_wr_port;
  uvm_analysis_port #(i2c_item) controller_mode_rd_port;
  uvm_analysis_port #(i2c_item) target_mode_wr_port;
  uvm_analysis_port #(i2c_item) target_mode_rd_port;

  /////////////////////////////////
  //
  // Modelling Variables
  //

  // These queues are used to capture predictions of transfers based upon CSR writes to the DUT.
  // As we can potentially enque multiple transfers by writing to the FMTFIFO before
  // any transfer has even started, we need to keep a track of the expected ordering of transfers.
  // Once we have predicted the transfer to have actually been driven and any data read back, we
  // can drop the item from this queue.
  // Note. that this sort of prediction does not take into account if the predicted transfer
  // actually completed. In reality, we can halt mid-transfer and completely change the progress of
  // the transfer. Therefore, this is a pretty limited predictor.
  local i2c_item exp_controller_mode_txn_q[$];
  local i2c_item prev_item[$];

  // DUT-Controller Operation
  //
  // The following local seq_items are used to construct larger transactions.
  // We update the local items as different events occur, then push the item
  // into a queue for checking after the end of the transaction has been detected.
  // See the header comment for more details.
  //
  local i2c_item exp_wr_item;
  local i2c_item exp_rd_item, rd_pending_item;
  local i2c_item rd_pending_q[$]; // Helper-queue : holds partial read transactions
  local uint rdata_cnt = 0; // Count data-bytes read in a single transfer (DUT-Controller)

  // DUT-Target Operation
  //
  // In Target-mode, read data is created in the stimulus vseqs by the function
  // i2c_base_seq::generate_agent_controller_stimulus(), and by default we form our expectations
  // based on these items.
  // However, sometimes we want to determine what our expected read data is just by looking
  // at the inputs to the DUT (in particular, writes to TXDATA). Store all writes to txdata
  // into this queue.
  bit [7:0] txdata_wr[$];
  bit [10:0] acqdata_rd[$];

  bit [6:0] target_addr0;  // Target Address 0
  bit [6:0] target_addr1;  // Target Address 1

  `uvm_component_new

  ///////////////////
  // CLASS METHODS //
  ///////////////////
  //
  // {build,connect,run,report,check}_phase()
  //
  // process_tl_access()
  // update_on_read()
  //   rdata_read()
  // update_on_write
  //   fmtfifo_write()
  //
  //////////////////////////////////////

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral = cfg.ral;

    // seq_items used to model in-progress transactions
    exp_rd_item = new("exp_rd_item");
    exp_wr_item = new("exp_wr_item");
    rd_pending_item = new("rd_pending_item");

    // Input fifos
    controller_mode_wr_obs_fifo = new("controller_mode_wr_obs_fifo", this);
    controller_mode_rd_obs_fifo = new("controller_mode_rd_obs_fifo", this);
    target_mode_wr_obs_fifo = new("target_mode_wr_obs_fifo", this);
    target_mode_rd_obs_fifo = new("target_mode_rd_obs_fifo", this);
    controller_mode_in_progress_fifo = new("controller_mode_in_progress_fifo", this);
    target_mode_in_progress_fifo = new("target_mode_in_progress_fifo", this);
    // Output ports
    controller_mode_wr_port = new("controller_mode_wr_port", this);
    controller_mode_rd_port = new("controller_mode_rd_port", this);
    target_mode_wr_port = new("target_mode_wr_port", this);
    target_mode_rd_port = new("target_mode_rd_port", this);
  endfunction: build_phase

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      forever create_target_exp();
      forever create_controller_exp();
    join_none
  endtask: run_phase

  // Update our reference model, and hence our predictions/expectations, based on observed TileLink
  // accesses.
  //
  virtual task process_tl_access(tl_seq_item item,
                                 tl_channels_e channel,
                                 string ral_name,
                                 uvm_reg csr);

    // The 'do_read_check' bit enables a check analagous to using 'reg.mirror(.check(UVM_CHECK))',
    // or if reg.set_check_on_read(1) was set for the RAL model. These settings would cause the
    // UVM RAL routines to hook do_check() upon reading from the DUT, and setting this bit will
    // cause an equivalent check to be performed at the end of the read access handler below.
    //
    // For any registers where hw can modify the register's value, and our refmodel / scoreboard
    // are unable to predict this new value before the read takes place, the code below should
    // ensure this bit is cleared so that no check takes place.
    bit do_read_check = 1'b1;

    bit write = item.is_write();
    bit tl_get           = (!write && channel == AddrChannel);
    bit tl_putdata       =  (write && channel == AddrChannel); // write
    bit tl_accessackdata = (!write && channel == DataChannel); // read
    bit tl_accessack     =  (write && channel == DataChannel);

    if (tl_putdata) begin
      // Incoming access is a write to a valid csr, so update the RAL right away
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // Update the refmodel's state based on the observed write.
      update_on_write(item.a_data, csr);
    end

    if (tl_accessackdata) begin
      // Update the refmodel's state based on the observed read.
      update_on_read(item.d_data, csr);

      // Mark registers which we are currently unable to predict / unmodelled, so we don't
      // check the read data against the RAL's mirrored value.
      if (csr.get_name() inside
          {"rdata",
           "intr_state",
           "status",
           "host_fifo_status",
           "target_fifo_status",
           "acqdata",
           "ovrd",
           "host_fifo_config",
           "target_fifo_config",
           "target_nack_count",
           "controller_events",
           "target_events"}
          ) begin
        do_read_check = 1'b0;
      end

      if (do_read_check) begin
        `DV_CHECK_EQ(`gmv(csr), item.d_data,
          $sformatf("Read-Check of %0s failed: mirror = 0x%0x, DUT = 0x%0x",
          csr.get_full_name(), `gmv(csr), item.d_data))
      end else begin
        // If we disabled the read-check, now update the RAL to take our
        // observed value from the DUT. We're not modelling these registers,
        // so this is the only way they are updated.
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end
    end

  endtask : process_tl_access


  // Update our model and predictions based on the write event.
  //
  task update_on_write(bit [bus_params_pkg::BUS_DW-1:0] data, uvm_reg csr);
    case (csr.get_name())

      "target_id": begin
        // Update the model's addresses
        target_addr0 = get_field_val(ral.target_id.address0, data);
        target_addr1 = get_field_val(ral.target_id.address1, data);
        // If we write new addresses into the DUT, also update the agent's configuration
        // with the same value(s).
        // TODO(#23920) Remove knowledge of the DUT Addresses from the i2c_agent
        cfg.m_i2c_agent_cfg.target_addr0 = get_field_val(ral.target_id.address0, data);
        cfg.m_i2c_agent_cfg.target_addr1 = get_field_val(ral.target_id.address1, data);
      end

      "fdata": begin // aka. FMTFIFO
        // Only capture items if not in reset, and HOST/CONTROLLER mode is active.
        if (!cfg.under_reset && `gmv(ral.ctrl.enablehost)) begin
          // Capture exp/obs data for checking.
          fmtfifo_write(data);
        end
      end

      "fifo_ctrl": begin
        bit rxrst_val = get_field_val(ral.fifo_ctrl.rxrst, data);
        if (rxrst_val) begin
          rd_pending_q = {};
          rd_pending_item.clear_all();
          exp_rd_item.clear_all();
        end
      end

      "txdata": begin
        txdata_wr.push_back(data[7:0]);
      end

      default:;
    endcase
  endtask: update_on_write

  // Update our model and predictions based on the read event.
  //
  task update_on_read(bit [bus_params_pkg::BUS_DW-1:0] data, uvm_reg csr);
    case (csr.get_name())
      "rdata": begin
        // Capture exp/obs data for checking.
        rdata_read(data);
      end

      "acqdata": begin
        acqdata_rd.push_back(data[10:0]);
        cfg.obs_num_acqfifo_reads++; // Used for stimulus generation purposes #TODO Remove
      end

      default:;
    endcase
  endtask: update_on_read

  // Task to accumulate expected items based on writes to the FMTFIFO
  //
  task fmtfifo_write(bit [bus_params_pkg::BUS_DW-1:0] data);

    bit [7:0] fbyte = get_field_val(ral.fdata.fbyte, data);
    bit start = get_field_val(ral.fdata.start, data);
    bit stop  = get_field_val(ral.fdata.stop,  data);
    bit readb = get_field_val(ral.fdata.readb, data);
    bit rcont = get_field_val(ral.fdata.rcont, data);
    bit nakok = get_field_val(ral.fdata.nakok, data);

    // If the start bit is set, we're writing the first indicator of a new
    // transfer (maybe a START or RSTART), where the FBYTE contains address + rw-bit.
    if (start) begin

      if (exp_wr_item.start || exp_wr_item.rstart_front) begin
        // If there is an in-progress write transfer, and this fmtfifo write has start = 1,
        // the current transfer ends (with an RSTART beginning a new transfer.)
        exp_wr_item.rstart_back = 1'b1;
        push_complete_dut_controller_xfer(exp_wr_item);
        prev_item.push_back(exp_wr_item); // Keep track of the previously pushed item.
        `uvm_create_obj(i2c_item, exp_wr_item);
      end

      // Create a new seq_item for the transfer we are starting.
      // This item is currently populated with address + direction from the first byte
      // of the transfer. Upon further writes to the FMTFIFO, we will fill in the remaining
      // fields.
      case (fbyte[0])

        i2c_pkg::READ: begin
          `uvm_create_obj(i2c_item, exp_rd_item);
          exp_rd_item.bus_op = BusOpRead;
          exp_rd_item.dir    = i2c_pkg::READ;
          exp_rd_item.addr   = fbyte[7:1];
          if (prev_item[$] != null && prev_item[$].rstart_back) begin
            exp_rd_item.rstart_front = 1;
          end else begin
            exp_rd_item.start = 1;
          end
          exp_rd_item.stop = stop;
        end

        i2c_pkg::WRITE: begin
          `uvm_create_obj(i2c_item, exp_wr_item);
          exp_wr_item.bus_op = BusOpWrite;
          exp_wr_item.dir    = i2c_pkg::WRITE;
          exp_wr_item.addr   = fbyte[7:1];
          if (prev_item[$] != null && prev_item[$].rstart_back) begin
            exp_wr_item.rstart_front = 1;
          end else begin
            exp_wr_item.start = 1;
          end
          exp_wr_item.stop = stop;
        end
        default:;
      endcase

    // If the start-bit was not set as part of the fmtfifo write, we may be writing part of a
    // larger transfer. Check if there is an in-progress transfer, and amend it with any new
    // expectations.
    end else begin // fdata.start == 0

      if (exp_wr_item.start || exp_wr_item.rstart_front) begin
        // There is already an in-progress write transfer.

        // Capture the data byte
        exp_wr_item.data_q.push_back(fbyte);
        exp_wr_item.data_ack_q.push_back(i2c_pkg::ACK);
        exp_wr_item.num_data++;

        // If stop was set, that concludes the in-progress write
        // transfer. Push it to a queue for checking.
        exp_wr_item.stop = stop;
        if (stop) begin
          push_complete_dut_controller_xfer(exp_wr_item);
          prev_item.push_back(exp_wr_item); // Keep track of the previously pushed item.
          `uvm_create_obj(i2c_item, exp_wr_item);
        end
      end

      if (exp_rd_item.start || exp_rd_item.rstart_front) begin
        // There is an in-progress read transfer.

        // If the 'readb' bit was set, we know more about the upcoming read transfer.
        // Capture this information and push it to the pending queue, which can be
        // completed when reading 'rdata' tells us what data we actually got from the bus.
        if (readb) begin
          i2c_item tmp_rd_item;

          // First, get the number of bytes to read
          // If RCONT is set, we add this to the previous item's count, which
          // represents our expectation for chained-reads
          uint num_rd_bytes = (fbyte == 8'd0) ? 256 : fbyte;
          if (exp_rd_item.rcont && (rcont || stop)) begin
            exp_rd_item.num_data += num_rd_bytes;
          end else begin
            exp_rd_item.num_data  = num_rd_bytes;
          end
          exp_rd_item.stop        = stop;
          exp_rd_item.rcont       = rcont;
          exp_rd_item.read        = readb;
          exp_rd_item.nakok       = nakok;
          // exp_rd_item.rstart_back = (exp_rd_item.stop) ? 1'b0 : 1'b1;
          // Note. 'start' is ignored when used with 'readb'.

          // The rx_overflow vseq overflows the RXFIFO by 1 word of data, so
          // decrement here in anticipation of that.
          if (cfg.seq_cfg.en_rx_overflow) exp_rd_item.num_data--;

          // Push the expected transaction into the queue, to be handled again during
          // reads from 'rdata'.
          `downcast(tmp_rd_item, exp_rd_item.clone());
          rd_pending_q.push_back(tmp_rd_item);
          prev_item.push_back(tmp_rd_item); // Keep track of the previously pushed item.

          // If this read also set the 'stop' bit to end the transaction, clear the
          // temporary variable we use to accumulate chained reads.
          if (exp_rd_item.stop) `uvm_create_obj(i2c_item, exp_rd_item);

        end

      end
    end

  endtask: fmtfifo_write


  // Complete forming our expectations of DUT-Controller read items by capturing data read from the
  // RXFIFO and adding it into the items created when we started a read xfer in the fmtfifo.
  //
  task rdata_read(bit [bus_params_pkg::BUS_DW-1:0] data);
    if (`gmv(ral.ctrl.enablehost)) begin

      // First, check if we need to wait for new data from a FMTFIFO write.
      //
      // 1) If read data count is 0, it means the transaction has not yet started.
      //
      // 2) If read data count is non-zero and equals the expected number of bytes while the stop
      //    bit is not set, it means a chained read has been issued and we need to update the
      //    expected transaction with the amount of data in the next item.
      //
      // 3) After the stop bit was set in the FMTFIFO, we won't pop any seq_items from the
      //    pending queue until we have finished reading enough data bytes to complete the
      //    length of the read transfer. Once we complete the read and push the item for checking,
      //    'rdata_cnt' is reset to zero, and then we enter this block and pick up the start item
      //    of the next read.
      if (rdata_cnt == 0 ||                        // 1)
          rdata_cnt == rd_pending_item.num_data && // 2)
          !rd_pending_item.stop) begin             // 3)

        // Block until a FMTFIFO-write creates a new item, then update our expectations.
        wait(rd_pending_q.size() > 0 ||
             cfg.under_reset); // for on-the-fly reset, immediately finish task to avoid blocking
        if (cfg.under_reset) return;

        begin
          i2c_item temp_item = rd_pending_q.pop_front();
          if (rdata_cnt == 0) begin
            // If our bytecount is 0, this is the first item created by the FMTFIFO write, so take
            // the item and acculuate read data into it directly. This item contains the address
            // etc., and further items will only contain the expected byte count for chained reads,
            // or a stop-indicator to end the transfer.
            rd_pending_item = temp_item;
          end else begin
            // If 'rdata_cnt' is non_zero, then we have already recevied at least one item from
            // the FMTFIFO, therefore we are in a chain read (RCONT).
            // Update the expected number of bytes (so we keep capturing new bytes into the existing
            // item), and the stop bit if the end of the read has been marked.
            rd_pending_item.num_data = temp_item.num_data;
            rd_pending_item.stop = temp_item.stop;
          end
        end

      end

      rd_pending_item.data_q.push_back(data);
      rdata_cnt++;

      // If we have completed a read transaction, push it to the 'controller_mode_rd_port'
      if (rd_pending_item.num_data == rdata_cnt &&
          rd_pending_item.stop) begin
        rdata_cnt = 0;
        rd_pending_item.data_ack_q.push_back(i2c_pkg::NACK);

        push_complete_dut_controller_xfer(rd_pending_item);

        // Zero-out the pending item, though we will soon drop it for a new
        // item the next time we go around and pick up the new FMTFIFO write.
        rd_pending_item.clear_all();
      end else begin
        rd_pending_item.data_ack_q.push_back(i2c_pkg::ACK);
      end

    end

  endtask: rdata_read


  // Push DUT-Controller completed transfers items to the 'exp_controller_mode_txn_q[$]' once we
  // have completed capturing the transfer expectation based on FMTFIFO/RXFIFO accesses.
  task push_complete_dut_controller_xfer(i2c_item xfer_item);
    `uvm_info(`gfn, $sformatf("csr_pred_xfer: Pushing following transfer to queue :\n%s",
      xfer_item.sprint()), UVM_DEBUG)
    begin
      i2c_item temp_item;
      `downcast(temp_item, xfer_item.clone());
      exp_controller_mode_txn_q.push_back(temp_item);
    end
  endtask : push_complete_dut_controller_xfer


  // Fuse data from both the I2C and TL_UL interface to create predictions for
  // DUT-Controller transfers.
  // TL_UL stimulus is captured via fmtfifo_write()/rdata_read() routines, which form expected
  // transfer items that are pushed to the 'exp_controller_mode_txn_q[$]'. I2C bus inputs are
  // captured via the TLM 'controller_mode_in_progress_fifo' items created by the i2c_agent's
  // monitor.
  //
  virtual task create_controller_exp();
    i2c_item inp_xfer; // in_progress_xfer, from the i2c_monitor

    // Wait until we have captured the entire in-progress transfer from the i2c_monitor.
    // Note. that we could do this by waiting on either of the full-transfer queues
    // 'controller_mode_{wr,rd}_obs_fifo', but in the future we will make use of the
    // intermediate states for prediction.
    controller_mode_in_progress_fifo.get(inp_xfer);
    `DV_CHECK(inp_xfer.state inside {StNone, StStarted})
    `uvm_info(`gfn, $sformatf("create_controller_exp() : Got handle to inp_xfer item :\n%s",
      inp_xfer.sprint()), UVM_DEBUG)

    fork
      begin
        wait(inp_xfer.state == StAddrByteAckRcvd);
        `uvm_info(`gfn, $sformatf(
          "create_controller_exp() got inp_xfer : (address=8'h%2x, rw=1'b%b (%0s))",
          inp_xfer.addr, inp_xfer.dir, inp_xfer.dir.name()), UVM_DEBUG)

        wait(inp_xfer.state == StStopped);
        `uvm_info(`gfn, "create_controller_exp() : Got inp_xfer.state == StStopped.", UVM_DEBUG)
      end
      // Optional (UVM_DEBUG) logging routine to print ongoing transfer state changes.
      while(inp_xfer.state != StStopped) print_inp_xfer_state_changes(inp_xfer);
    join_any

    // At this point, we have captured the observed transfer from the i2c_monitor, but not
    // necessarily the whole csr-predicted transfer as we need to wait for the RXFIFO to be
    // read out to capture any read-data from the transfer.

    // Now spawn a background process that waits for the csr_pred_xfer to complete, then
    // fuses the data together and pushes the result to the scoreboard for comparison.
    fork push_exp_when_ready(inp_xfer); join_none

  endtask : create_controller_exp


  virtual task print_inp_xfer_state_changes(i2c_item inp_xfer);
    @(inp_xfer.state);
    `uvm_info(`gfn, $sformatf("inp_xfer.state moved to %0s.", inp_xfer.state.name()), UVM_DEBUG)
  endtask : print_inp_xfer_state_changes


  virtual task push_exp_when_ready(i2c_item complete_bus_xfer);
    i2c_item csr_pred_xfer; // Prediction created by fmtfifo_write()/rdata_read() accesses

    // Wait until we have made a prediction based on the CSR accesses only.
    wait(exp_controller_mode_txn_q.size > 0);
    csr_pred_xfer = exp_controller_mode_txn_q.pop_front();

    // We now have both bus and csr predictions. Join the data together to create the final
    // expectation.

    // If we see a NACK from the Target on the address byte, then update the prediction
    csr_pred_xfer.addr_ack = complete_bus_xfer.addr_ack;
    // Update the data acks with our observations
    csr_pred_xfer.data_ack_q = complete_bus_xfer.data_ack_q;

    `uvm_info(`gfn, $sformatf("Pushing following transfer to scoreboard :\n%s",
      csr_pred_xfer.sprint()), UVM_DEBUG)

    // Now that we have updated the predicted transfer, push it to the scoreboard for checking
    case (csr_pred_xfer.bus_op)
      BusOpRead: controller_mode_rd_port.write(csr_pred_xfer);
      BusOpWrite: controller_mode_wr_port.write(csr_pred_xfer);
      default: `uvm_fatal(`gfn, "Shouldn't get here!")
    endcase
    void'(prev_item.pop_front());

  endtask : push_exp_when_ready


  // This task generates DUT-Target transfer expectations
  //
  // Previously, these expectations were formed by taking the stimulus items directly from the
  // virtual sequences, which was very limiting.
  //
  // Now, we take input from the i2c_monitor directly, which is how this should have been
  // architected from the start. Note that i2c_item is currently used at a 'transfer' level, which
  // makes modelling sub-transfer behaviours precisely difficult. In the future, we should reduce
  // the granularity down to the byte-level, which will make it possible to model with greater
  // precision.
  //
  virtual task create_target_exp();
    fork
      forever begin
        i2c_item obs_item, obs_item_clone;
        target_mode_wr_obs_fifo.get(obs_item);
        `downcast(obs_item_clone, obs_item.clone());
        create_target_wr_exp(obs_item_clone);
      end
      forever begin
        i2c_item obs_item, obs_item_clone;
        target_mode_rd_obs_fifo.get(obs_item);
        `downcast(obs_item_clone, obs_item.clone());
        create_target_rd_exp(obs_item_clone);
      end
    join
  endtask : create_target_exp

  // Convert DUT-target monitor observations of write transfers into expectations for checking.
  //
  // While less of the DUT is comprehensively modelled here, it makes sense to start
  // with the monitor observation, then to add in data to this item based on our predictions.
  // This also makes sense as a baseline comparison for mis-addressed transfers, as we can also
  // make comparisons based on the same transaction item format, except with explicitly-captured
  // fields to represent NACK-ing the address byte, and NACK-ing any further bytes in the transfer.
  //
  virtual function void create_target_wr_exp(i2c_item obs_xfer);
    i2c_item exp_wr_xfer;

    // To begin with, we start with the monitor's observation as our prediction.
    exp_wr_xfer = obs_xfer;

    // If the address of the transfer did not match the DUT, we don't expect to see any DUT
    // interaction with the remainder of the transfer. In this case, we can pass the i2c monitor
    // observation straight through without modification as the expectation.

    if (is_target_addr(obs_xfer.addr)) begin
      // The address of the transfer matched what is configured into the DUT, so we expect the
      // the transfer to be accepted, and to become visible at the ACQFIFO.

      // Count the number of ACQFIFO items we expect to read to completely observe the transfer.
      cfg.exp_num_acqfifo_reads += 1 /*signal=start/rstart, abyte=addr+dir*/ +
                          obs_xfer.num_data /*signal=none, abyte=data*/ +
                          (obs_xfer.stop ? 1 /*signal=stop, abyte=xx*/ : 0);

      // #TODO Add the captured ACQFIFO write data into the sequence item we got from the monitor
      // exp_wr_xfer.data_q = '{};
      // if (acqdata_rd.size() < exp_wr_xfer.num_data) begin
      //   `uvm_fatal("Too few ACQFIFO reads to complete the expected item!")
      // end
      // repeat (exp_wr_xfer.num_data) exp_wr_xfer.data_q.push_back(acqdata_rd.pop_front());
    end

    target_mode_wr_port.write(exp_wr_xfer);
  endfunction: create_target_wr_exp

  // Convert DUT-target monitor observations of read transfers into expectations for checking.
  //
  virtual task create_target_rd_exp(i2c_item obs_xfer);
    i2c_item exp_rd_xfer;

    exp_rd_xfer = obs_xfer;

    // If the transfer was not addressed to the DUT we can push the item to the scoreboard as
    // our rd_exp item.

    if (is_target_addr(obs_xfer.addr)) begin
      // The address of the transfer matched what is configured into the DUT, so we expect the
      // the transfer to be accepted, and to become visible at the ACQFIFO.
      exp_rd_xfer = obs_xfer;

      // Count the number of ACQFIFO items we expect to read to completely observe the transfer.
      cfg.exp_num_acqfifo_reads += 1 /*signal=start/rstart, abyte=addr+dir*/ +
                                   (exp_rd_xfer.stop ? 1 /*signal=stop, abyte=xx*/ : 0);

      // If we received the item from the monitor, that means the transfer must have already
      // ended. Therefore, we know any data in the item has already been written into the
      // txfifo.
      exp_rd_xfer.data_q = '{};
      repeat (exp_rd_xfer.num_data) exp_rd_xfer.data_q.push_back(txdata_wr.pop_front());
    end

    target_mode_rd_port.write(exp_rd_xfer);

  endtask: create_target_rd_exp


  function bit is_target_addr(bit [6:0] addr);
    return (addr == target_addr0 || addr == target_addr1);
  endfunction


  // Reset local fifos, queues and variables
  virtual function void reset();
    rd_pending_q = {};
    rd_pending_item.clear_all();
    exp_rd_item.clear_all();
    exp_wr_item.clear_all();
    rdata_cnt = 0;
    txdata_wr = '{};
  endfunction : reset

endclass : i2c_reference_model
