// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence that forces internal variables, triggering internal FSM state transition to
// AcquireStart or Idle states
// Check if the state transitions are as expected
// Check if DUT is behaving as expected after glitch using a basic transaction
class i2c_glitch_vseq extends i2c_target_smoke_vseq;

  `uvm_object_utils(i2c_glitch_vseq)
  `uvm_object_new
  // Number of cycles sequence wait before all of the address states are executed
  parameter uint ADDR_STATE_WAIT_TIMEOUT_CYCLES = 20;
  // Number of cycles sequence wait before all of the write states are executed
  parameter uint WRITE_STATE_WAIT_TIMEOUT_CYCLES = 40;
  // Number of cycles sequence wait before all of the read states are executed
  parameter uint READ_STATE_WAIT_TIMEOUT_CYCLES = 40;
  // Period of SCL clock depending on timing parameters
  uint scl_period;

  // Variable used to detect start internally
  string start_detected_path = "tb.dut.i2c_core.u_i2c_target_fsm.start_det";
  // Variable used to detect Stop internally
  string stop_detected_path = "tb.dut.i2c_core.u_i2c_target_fsm.stop_det";
  // Internal FSM variable
  string fsm_state_path = "tb.dut.i2c_core.u_i2c_target_fsm.state_q";

  // State definitions
  typedef enum logic [5:0] {
    Idle,

    /////////////////////////
    // Target function states
    /////////////////////////

    // Target function receives start and address from external host
    AcquireStart, AddrRead,
    // Target function acknowledges the address and returns an ack to external host
    AddrAckWait, AddrAckSetup, AddrAckPulse, AddrAckHold,
    // Target function sends read data to external host-receiver
    TransmitWait, TransmitSetup, TransmitPulse, TransmitHold,
    // Target function receives ack from external host
    TransmitAck, TransmitAckPulse, WaitForStop,
    // Target function receives write data from the external host
    AcquireByte,
    // Target function sends ack to external host
    AcquireAckWait, AcquireAckSetup, AcquireAckPulse, AcquireAckHold,
    // Target function clock stretch handling.
    StretchAddr,
    StretchTx, StretchTxSetup,
    StretchAcqFull, StretchAcqSetup
  } state_e;

  // initialize the states in which glitch is to be introduced
  // Ignore state transitions covered in other testcases
  // WaitForStop -> Idle and WaitForStop -> AcquireStart
  // TransmitAckPulse -> Idle and TransmitAckPulse -> AcquireStart
  // AcquireByte -> Idle and AcquireByte -> AcquireStart
  // StretchAcqSetup is also an invalid start, as a control symbol is impossible
  // in this state.
  state_e read_states[]  = '{TransmitWait, TransmitSetup, TransmitPulse, TransmitHold, TransmitAck,
                            TransmitAckPulse, StretchTx, StretchTxSetup};
  state_e write_states[] = '{AcquireAckWait, AcquireAckSetup, AcquireAckPulse, AcquireAckHold,
                             StretchAcqFull};
  state_e addr_states[]  = '{StretchAddr, AddrAckWait, AddrAckSetup, AddrAckPulse, AddrAckHold};
  // AddrAckSetup is here because SCL and SDA can change simultaneously,
  // leading to failures after the modeled CDC random insertion delay.
  state_e scl_high_states[]  = '{TransmitPulse, AcquireAckPulse, AddrAckSetup, AddrAckPulse};

  // Common steps for DUT initialization
  virtual task setup();
    initialization();
    get_timing_values();
    print_time_property();
    program_registers();
    // Set maximum and minimum number of transactions to 1 since
    // only once sequence can be used to test behaviour of DUT after glitch
    cfg.seq_cfg.i2c_min_num_trans = 1;
    cfg.seq_cfg.i2c_max_num_trans = 1;
    cfg.min_data = 1;
    cfg.max_data = 5;
    cfg.rs_pct = 0;
    scl_period = t_f + t_r + thigh + tlow + tsu_dat + thd_dat;
    `uvm_info(`gfn, $sformatf("Setting scl_period to %0d", scl_period), UVM_MEDIUM)
  endtask

  virtual task body();
    // Initialize DUT in device mode and agent in host mode based on if_mode set using run argument
    if (cfg.m_i2c_agent_cfg.if_mode == Host) begin
      i2c_target_base_seq m_i2c_target_seq;
      i2c_item txn_q[$];
      `uvm_info(`gfn, "Initializing DUT in Target mode", UVM_LOW)
      setup();
      target_mode_address_glitch(start_detected_path, AcquireStart);
      target_mode_address_glitch(stop_detected_path, Idle);
      target_mode_write_glitch(start_detected_path, AcquireStart);
      target_mode_write_glitch(stop_detected_path, Idle);
      target_mode_read_glitch(start_detected_path, AcquireStart);
      target_mode_read_glitch(stop_detected_path, Idle);
    end else begin
      `uvm_fatal(`gfn, "Host mode glitches not supported")
      setup();
    end
  endtask

  // Task to issue a basic smoke test sequence to DUT
  task target_basic_smoke();
    i2c_target_base_seq m_i2c_target_seq;
    i2c_item req;
    uvm_reg_data_t data;
    bit[7:0] wdata;
    bit[6:0] addr;
    int temp;
    state_e state_int;
    cfg.clk_rst_vif.wait_clks(1);
    clear_fifo();
    // Check internal state of DUT
    `DV_CHECK_FATAL(uvm_hdl_read(fsm_state_path, temp), "Failed to read fsm_state")
    state_int = state_e'(temp);
    `uvm_info(`gfn, $sformatf("DUT internal state is %s", state_int.name()), UVM_MEDIUM)
    // Create sequence object
    `uvm_create_obj(i2c_target_base_seq, m_i2c_target_seq)
    // Add start to the transaction
    `uvm_create_obj(i2c_item, req)
    append_start(req, m_i2c_target_seq.req_q);
    // Add address the transaction
    `uvm_create_obj(i2c_item, req)
    append_address(req, m_i2c_target_seq.req_q, 1'b0);
    addr = req.wdata[7:1];
    // Add data item to transaction
    `uvm_create_obj(i2c_item, req)
    append_data(req, m_i2c_target_seq.req_q);
    wdata = req.wdata;
    // Add Stop to the transaction
    `uvm_create_obj(i2c_item, req)
    req.wdata = $urandom_range(1, 127);
    req.drv_type = HostStop;
    m_i2c_target_seq.req_q.push_back(req);
    // Start sequence and inject glitch once the required state is observed
    m_i2c_target_seq.start(p_sequencer.i2c_sequencer_h);
    // Check ACQ FIFO after sequence is completed
    // Read Start address condition
    if (state_int != Idle) begin
      // Check Rstart in case bus wasn't idle
      csr_rd(.ptr(ral.acqdata), .value(data));
      `uvm_info(`gfn, $sformatf("acq_data = %0h", data), UVM_MEDIUM)
      `DV_CHECK_EQ_FATAL(data[9:8], 2'b11, "RStart condition not detected")
    end else begin
      csr_rd(.ptr(ral.acqdata), .value(data));
      `uvm_info(`gfn, $sformatf("acq_data = %0h", data), UVM_MEDIUM)
      `DV_CHECK_EQ_FATAL(data[9:8], 2'b01, "Start condition not detected")
    end
    `DV_CHECK_EQ_FATAL(data[7:1], addr, $sformatf("Incorrect address detected;Expected %0h", addr))
    `DV_CHECK_EQ_FATAL(data[0], 1'b0, "Incorrect RW bit detected")
    // Read Write data
    csr_rd(.ptr(ral.acqdata), .value(data));
    `uvm_info(`gfn, $sformatf("acq_data = %0h", data), UVM_MEDIUM)
    `DV_CHECK_EQ_FATAL(data[7:0], wdata, "Incorrect data detected")
    // Read Stop condition
    csr_rd(.ptr(ral.acqdata), .value(data));
    `uvm_info(`gfn, $sformatf("acq_data = %0h", data), UVM_MEDIUM)
    `DV_CHECK_EQ_FATAL(data[9:8], 2'b10, "Stop condition not detected")
  endtask

  // Task to wait for a particular state to be observed in internal FSM of DUT
  // state_path: Path to internal FSM state variable
  // state_expected: Expected state to be observed
  // wait_timeout: Number of cycles to wait before timeout
  task wait_for_state(string state_path, state_e state_expected, uint wait_timeout);
    bit state_detected = 0;
    // Wait for the required state to be observed
    for(int i = 0; i < wait_timeout; i++) begin
      int temp;
      state_e state_int;
      `DV_CHECK_FATAL(uvm_hdl_read(state_path, temp), "Failed to read fsm_state")
      state_int = state_e'(temp);
      `uvm_info(`gfn, $sformatf("observed State: %s", state_int.name()), UVM_HIGH)
      if (state_int == state_expected) begin
        state_detected = 1;
        break;
      end else begin
        cfg.clk_rst_vif.wait_clks(1);
      end
    end
    if (!state_detected) begin
      `uvm_error(`gfn, $sformatf("timed out waiting for state: %s", state_expected.name()))
    end else begin
      `uvm_info(`gfn, $sformatf("observed State: %s", state_expected.name()), UVM_MEDIUM)
    end
  endtask

  // Task to introduce glitch by forcing internal signal
  // and issue reset to testbench components
  // fsm_state_path: Path to internal FSM state variable
  // var_path: Path to internal signal to be forced
  // timeout: Number of cycles to wait before timeout
  // state_desired: Expected state to be observed after glitch
  task inject_glitch(string fsm_state_path,
    string var_path,
    uint timeout,
    state_e state_desired = AcquireStart);
    int res;
    state_e state_start;
    `DV_CHECK_FATAL(uvm_hdl_read(fsm_state_path, res), "Failed to read fsm_state")
    state_start = state_e'(res);
    // Introduce glitch by forcing internal signal
    `DV_CHECK_FATAL(uvm_hdl_force(var_path, 1'b1), "Failed to force variable")
    cfg.m_i2c_agent_cfg.driver_rst = 1;
    // Reset agent
    cfg.clk_rst_vif.wait_clks(1);
    `DV_CHECK_FATAL(uvm_hdl_release(var_path), "Failed to release variable")
    // Check if FSM transitions to desired_state
    `DV_CHECK_FATAL(uvm_hdl_read(fsm_state_path, res), "Failed to read fsm_state")
    `DV_CHECK_EQ_FATAL(state_e'(res), state_desired,
      $sformatf("FSM did not transition to %s state", state_desired.name()))
    cfg.m_i2c_agent_cfg.driver_rst = 0;
    if (is_scl_high_state(state_start)) begin
      // Need to set SCL low to prevent detection of a stop
      cfg.m_i2c_agent_cfg.vif.scl_o = 1'b0;
      cfg.clk_rst_vif.wait_clks(1);
    end
    // Wait for the DUT to stop driving SDA (1 cycle latency)
    cfg.clk_rst_vif.wait_clks(1);
    `uvm_info(`gfn, "Stop SCL from driver", UVM_MEDIUM)
    // Stop driving SCL from driver
    cfg.m_i2c_agent_cfg.host_scl_stop = 1;
    cfg.m_i2c_agent_cfg.host_scl_force_high = 1;
    cfg.clk_rst_vif.wait_clks(2);
    cfg.m_i2c_agent_cfg.host_scl_stop = 0;
    cfg.m_i2c_agent_cfg.host_scl_force_high = 0;
    // SCL will be driven by Driver once a new transaction is issued
  endtask

  // Task to wait for a particular internal FSM state and introduce a
  // glitch on the provided variable once the state is observed
  // fsm_state_path: Path to internal FSM state variable
  // var_path: Path to internal signal to be forced
  // timeout: Number of cycles to wait before timeout
  // state_expected: Expected state to be observed
  // state_desired: Expected state to be observed after glitch
  task wait_and_inject_glitch(string fsm_state_path,
    string var_path,
    uint timeout,
    state_e state_expected = Idle,
    state_e state_desired = AcquireStart);
    // Wait for the required state to be observed
    wait_for_state(fsm_state_path, state_expected, timeout);
    inject_glitch(fsm_state_path, var_path, timeout, state_desired);
  endtask

  // Task to clear ACQ and TX FIFOs
  task clear_fifo();
    csr_wr(.ptr(ral.fifo_ctrl.acqrst), .value(1'b1));
    csr_wr(.ptr(ral.fifo_ctrl.txrst), .value(1'b1));
  endtask

  // Function to append i2c_item with Start condition to driver queue
  function void append_start(ref i2c_item req, ref i2c_item driver_q[$]);
    req.drv_type = HostStart;
    driver_q.push_back(req);
  endfunction

  // Function to append address such that it always matches target address programmed
  // and read/write bit based on the input value provided
  function void append_address(ref i2c_item req,
                               ref i2c_item driver_q[$],
                               input bit rw_bit);
      req.wdata[7:1] = target_addr0;
      req.drv_type = HostData;
      req.wdata[0] = rw_bit; // Read transaction
      req.read = rw_bit;
      driver_q.push_back(req);
  endfunction

  // Function to append i2c_item with data byte to driver queue
  function void append_data(ref i2c_item req, ref i2c_item driver_q[$]);
    req.wdata = $urandom_range(1, 127);
    req.drv_type = HostData;
    driver_q.push_back(req);
  endfunction

  // Task to force variable in internal FSM that trigger a transition to AcquireStart/Idle
  // Then check if design behaves as expected
  // var_hdl_path: Path to internal signal to be forced
  // state_expected: Expected state to be observed after glitch
  task target_mode_address_glitch(string var_hdl_path,
    state_e target_state = AcquireStart);
    // Update driver request queue with a single address transaction
    // followed by a single data transaction depending on the state
    // in which glitch is to be introduced
    i2c_item req;
    i2c_target_base_seq m_i2c_target_seq;
    // Timeout for state to be observed
    uint timeout = ADDR_STATE_WAIT_TIMEOUT_CYCLES * scl_period;
    // Create sequence object
    `uvm_create_obj(i2c_target_base_seq, m_i2c_target_seq)
    // Inject glitch in address states
    foreach(addr_states[i]) begin
      `uvm_info(`gfn,
        $sformatf("Start: %s -> %s test", addr_states[i].name(), target_state.name()),
        UVM_LOW)
      // Add start to the transaction
      `uvm_create_obj(i2c_item, req)
      append_start(req, m_i2c_target_seq.req_q);
      // Add address to the transaction
      `uvm_create_obj(i2c_item, req)
      append_address(req, m_i2c_target_seq.req_q, 1'b0);
      // Override the driver type based on the state in which glitch is to be introduced
      case (addr_states[i])
        AddrAckWait: req.drv_type = HostDataNoWaitForACK;
        default: req.drv_type = HostData;
      endcase
      // Add data items to transaction enter StretchAddr state
      if (addr_states[i] == StretchAddr) begin
        // one entry each for the last byte to ACK and STOP + one free
        // If there isn't another free slot, the DUT will stretch on the last
        // byte instead.
        repeat(I2C_ACQ_FIFO_DEPTH - 3) begin
          `uvm_create_obj(i2c_item, req)
          append_data(req, m_i2c_target_seq.req_q);
        end
        // Add stop to the transaction
        `uvm_create_obj(i2c_item, req)
        req.drv_type = HostStop;
        m_i2c_target_seq.req_q.push_back(req);
        // Create transaction that triggers StretchAddr state
        // Add Start to the transaction
        `uvm_create_obj(i2c_item, req)
        append_start(req, m_i2c_target_seq.req_q);
        // Add address to the transaction
        `uvm_create_obj(i2c_item, req)
        append_address(req, m_i2c_target_seq.req_q, 1'b0);
        timeout = (((I2C_ACQ_FIFO_DEPTH + 2) * 9) + ADDR_STATE_WAIT_TIMEOUT_CYCLES) * scl_period;
      end
      fork
        begin
          // Start sequence and inject glitch once the required state is observed
          m_i2c_target_seq.start(p_sequencer.i2c_sequencer_h);
        end
        begin
          wait_and_inject_glitch(
            .fsm_state_path(fsm_state_path),
            .var_path(var_hdl_path),
            .timeout(timeout),
            .state_expected(addr_states[i]),
            .state_desired(target_state));
        end
      join
      // Check if ACQ FIFO has any data
      // for address state glitches, there should not be any data in ACQ FIFO
      begin
        bit acq_fifo_empty;
        csr_rd(.ptr(ral.status.acqempty), .value(acq_fifo_empty));
        if (addr_states[i] == StretchAddr) begin
          `DV_CHECK_EQ_FATAL(acq_fifo_empty, 1'b0, "ACQ FIFO is empty for StretchAddr glitch")
        end else if ((addr_states[i] == AddrAckHold) && (thd_dat == 1)) begin
          // If thd_dat is only 1 in this state, the write to the ACQ FIFO
          // will happen immediately.
          `DV_CHECK_EQ_FATAL(acq_fifo_empty, 1'b0, "ACQ FIFO is empty for addressed glitch")
        end else if (target_state == Idle) begin
          // The ACQ FIFO always has room for the Stop, which should get
          // written.
          `DV_CHECK_EQ_FATAL(acq_fifo_empty, 1'b0, "ACQ FIFO is empty for address stop glitch")
        end else begin
          `DV_CHECK_EQ_FATAL(acq_fifo_empty, 1'b1, "ACQ FIFO is not empty for address start glitch")
        end
      end
      `uvm_info(`gfn, $sformatf("Start target smoke after glitch in %s ", addr_states[i].name()),
        UVM_MEDIUM)
      target_basic_smoke();
      `uvm_info(`gfn, $sformatf("End target smoke after glitch in %s ", addr_states[i].name()),
        UVM_MEDIUM)
      `uvm_info(`gfn,
        $sformatf("End: %s -> %s test pass", addr_states[i].name(), target_state.name()),
        UVM_LOW)
      cfg.clk_rst_vif.wait_clks(1);
    end
    clear_fifo();
  endtask

  // Task to force variable in write states of internal FSM that
  // triggers a transition to AcquireStart/Idle state and check if design behaves as expected
  // var_hdl_path: Path to internal signal to be forced
  // state_expected: Expected state to be observed after glitch
  task target_mode_write_glitch(string var_hdl_path,
    state_e target_state = AcquireStart);
    // Update driver request queue with a single address transaction followed by write data
    // transactions depending on the state in which glitch is to be introduced
    i2c_item req;
    i2c_target_base_seq m_i2c_target_seq;
    // Timeout for state to be observed
    uint timeout = WRITE_STATE_WAIT_TIMEOUT_CYCLES * scl_period;
    // Create sequence object
    `uvm_create_obj(i2c_target_base_seq, m_i2c_target_seq)
    // Inject glitch in address states
    foreach(write_states[i]) begin
      `uvm_info(`gfn,
        $sformatf("Start: %s -> %s test", write_states[i].name(), target_state.name()),
        UVM_LOW)
      // Add start to the transaction
      `uvm_create_obj(i2c_item, req)
      append_start(req, m_i2c_target_seq.req_q);
      // Add address to the transaction
      `uvm_create_obj(i2c_item, req)
      append_address(req, m_i2c_target_seq.req_q, 1'b0);
      // Add data items to the transaction
      `uvm_create_obj(i2c_item, req)
      append_data(req, m_i2c_target_seq.req_q);
      if (write_states[i] == StretchAcqFull) begin
        // Create ACQ FIFO full condition
        repeat(I2C_ACQ_FIFO_DEPTH) begin
          `uvm_create_obj(i2c_item, req)
          append_data(req, m_i2c_target_seq.req_q);
        end
        // Each byte requires 9 scl cycles to be transmitted
        timeout = ((I2C_ACQ_FIFO_DEPTH * 9)+ WRITE_STATE_WAIT_TIMEOUT_CYCLES) * scl_period;
      end
      fork
          begin
            // Start sequence and inject glitch once the required state is observed
            m_i2c_target_seq.start(p_sequencer.i2c_sequencer_h);
          end
          begin
            wait_and_inject_glitch(
              .fsm_state_path(fsm_state_path),
              .var_path(var_hdl_path),
              .timeout(timeout),
              .state_expected(write_states[i]),
              .state_desired(target_state));
          end
      join
      `uvm_info(`gfn, $sformatf("Start target smoke after glitch in %s ", write_states[i].name()),
        UVM_MEDIUM)
      target_basic_smoke();
      `uvm_info(`gfn, $sformatf("End target smoke after glitch in %s ", write_states[i].name()),
        UVM_MEDIUM)
      `uvm_info(`gfn,
        $sformatf("End: %s -> %s test pass", write_states[i].name(), target_state.name()),
        UVM_LOW)
      cfg.clk_rst_vif.wait_clks(1);
    end
    clear_fifo();
  endtask

  // Task to force variable in read states of internal FSM that
  // triggers a transition to AcquireStart/Idle state and check if design behaves as expected
  task target_mode_read_glitch(string var_hdl_path,
    state_e target_state = AcquireStart);
    // Update driver request queue with a single address transaction
    // followed by a single data transaction depending on the state
    // in which glitch is to be introduced
    i2c_item req;
    i2c_target_base_seq m_i2c_target_seq;
    // Create sequence object
    `uvm_create_obj(i2c_target_base_seq, m_i2c_target_seq)
    // Inject glitch in read states
    foreach(read_states[i]) begin
      bit sequence_done = 0;
      `uvm_info(`gfn,
        $sformatf("Start: %s -> %s test", read_states[i].name(), target_state.name()),
        UVM_LOW)
      // Add start to the transaction
      `uvm_create_obj(i2c_item, req)
      append_start(req, m_i2c_target_seq.req_q);
      // Add address to the transaction
      `uvm_create_obj(i2c_item, req)
      append_address(req, m_i2c_target_seq.req_q, 1'b1);
      // Add read data items to the transaction
      `uvm_create_obj(i2c_item, req)
      req.drv_type = HostAck;
      m_i2c_target_seq.req_q.push_back(req);
      clear_fifo();
      // Update TXDATA register
      program_tx_fifo(1);
      fork
          begin
            // Start sequence and inject glitch once the required state is observed
            m_i2c_target_seq.start(p_sequencer.i2c_sequencer_h);
            sequence_done = 1;
          end
          begin
            // To transition from StretchTx to StretchSetup
            // Wait for StretchTx state and add entry in TXDATA FIFO
            if (read_states[i] == StretchTxSetup) begin
              // Wait for StretchTx state
              wait_for_state(
                .state_path(fsm_state_path),
                .state_expected(StretchTx),
                .wait_timeout(READ_STATE_WAIT_TIMEOUT_CYCLES * scl_period));
              // Add entry in TXDATA FIFO
              program_tx_fifo(1);
            end
          end
          begin
            wait_and_inject_glitch(
              .fsm_state_path(fsm_state_path),
              .var_path(var_hdl_path),
              .timeout(READ_STATE_WAIT_TIMEOUT_CYCLES * scl_period),
              .state_expected(read_states[i]),
              .state_desired(target_state));
          end
          begin // read ACQ FIFO data
            uvm_reg_data_t data;
            while(!sequence_done) begin
              if (cfg.intr_vif.pins[TxStretch]) begin
                csr_rd(.ptr(ral.acqdata), .value(data));
              end
              cfg.clk_rst_vif.wait_clks(1);
            end
          end
      join
      `uvm_info(`gfn, $sformatf("Start target smoke after glitch in %s ", read_states[i].name()),
        UVM_MEDIUM)
      target_basic_smoke();
      `uvm_info(`gfn, $sformatf("End target smoke after glitch in %s ", read_states[i].name()),
        UVM_MEDIUM)
      `uvm_info(`gfn,
        $sformatf("End: %s -> %s test pass", read_states[i].name(), target_state.name()),
        UVM_LOW)
      cfg.clk_rst_vif.wait_clks(1);
    end
    clear_fifo();
  endtask

  function bit is_scl_high_state(state_e state);
    foreach (scl_high_states[i]) begin
      if (state == scl_high_states[i]) return 1;
    end
    return 0;
  endfunction

endclass : i2c_glitch_vseq
