// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_scoreboard extends cip_base_scoreboard #(
    .CFG_T(mbx_env_cfg),
    .RAL_T(mbx_core_reg_block),
    .COV_T(mbx_env_cov)
  );
  `uvm_component_utils(mbx_scoreboard)

  // Expected Inbound write and Outbound read addresses.
  bit [top_pkg::TL_AW-1:0] m_ibmbx_ptr;
  bit [top_pkg::TL_AW-1:0] m_obmbx_ptr;
  // Expected destination address for WDATA write.
  bit [top_pkg::TL_AW-1:0] m_ib_wdata_ptr;
  // Count of Outbound response words.
  bit [10:0] m_obdwcnt;

  bit exp_mbx_core_irq;
  bit exp_mbx_core_irq_q[$];

  // Expected status; these indications are visible on both register interfaces.
  bit m_mbx_busy = 1'b0;
  bit m_mbx_ready = 1'b0;
  bit m_mbx_error = 1'b0;
  bit m_mbx_abort = 1'b0;
  bit m_mbx_async_msg = 1'b0;

  // local queues to hold incoming packets pending comparison
  bit m_ibmbx_start = 1'b1;
  bit [top_pkg::TL_DW-1:0] m_ib_data_q[$]; // Inbound data (request to RoT).
  bit [top_pkg::TL_DW-1:0] m_ob_data_q[$]; // Outbound data (response from RoT).

  // System RAL model; keep a local handle for cleaner/easier access.
  mbx_soc_reg_block m_mbx_soc_ral;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);

    // Create analysis FIFOs to receive items from the SRAM tl_agent monitor.
    tl_a_chan_fifos["tl_sram_a_chan"] = new("tl_sram_a_chan", this);
    tl_d_chan_fifos["tl_sram_d_chan"] = new("tl_sram_d_chan", this);
    tl_dir_fifos["tl_sram_dir"] = new("tl_sram_dir", this);
  endfunction

  virtual task monitor_core_interrupt();
    `uvm_info(`gfn, "monitor_core_interrupt -- Start", UVM_DEBUG)
    // `DV_CHECK_CASE_EQ(exp_mbx_core_irq, cfg.intr_vif.pins, "Default state of interrupt pin is 0")
    forever begin
      @(cfg.intr_vif.pins);
      `uvm_info(`gfn, $sformatf("Change in interrupt pin('b%b)", cfg.intr_vif.pins), UVM_LOW)
      `DV_CHECK_CASE_EQ(exp_mbx_core_irq, cfg.intr_vif.pins[MbxCoreReady],
                        "Exp. interrupt doesn't match actual")
    end
    `uvm_info(`gfn, "monitor_core_interrupt -- End", UVM_DEBUG)
  endtask: monitor_core_interrupt

  virtual task monitor_exp_core_interrupts();
    `uvm_info(`gfn, "monitor_exp_core_interrupts -- Start", UVM_DEBUG)
    fork
     forever begin
       bit exp_irq;

       wait (exp_mbx_core_irq_q.size() != 0);
       exp_irq = exp_mbx_core_irq_q.pop_front();
       if (exp_irq == 1) begin
         cfg.clk_rst_vif.wait_n_clks(2);
         `DV_CHECK_EQ(exp_irq, cfg.intr_vif.pins[MbxCoreReady],
                      "Expecting interrupt pin to go high")
       end
       if (exp_irq == 0) begin
         // TODO: Earlier it was set to '1', updating it to larger value for the RTL change
         // to go, reduce it once the RTL is fixed.
         cfg.clk_rst_vif.wait_n_clks(5);
         `DV_CHECK_EQ(exp_irq, cfg.intr_vif.pins[MbxCoreReady], "Expecting interrupt pin to go low")
       end
     end
    join_none
    wait fork;
    `uvm_info(`gfn, "monitor_exp_core_interrupts -- End", UVM_DEBUG)
  endtask: monitor_exp_core_interrupts

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `downcast(m_mbx_soc_ral, cfg.ral_models[cfg.mbx_soc_ral_name])
    // We need a process to monitor the TL-UL traffic on the SRAM port.
    //
    // TODO: Since we expect combinational responses and therefore the A/D items arrive
    // unsequenced, we should probably change this to be simply two independent processes at some
    // point, and neither process need concern itself with the `dir_fifo`.
    fork
      begin
        uvm_tlm_analysis_fifo#(tl_seq_item) a_chan_fifo = tl_a_chan_fifos["tl_sram_a_chan"];
        uvm_tlm_analysis_fifo#(tl_seq_item) d_chan_fifo = tl_d_chan_fifos["tl_sram_d_chan"];
        uvm_tlm_analysis_fifo#(tl_channels_e) dir_fifo  = tl_dir_fifos["tl_sram_dir"];

        forever begin
          tl_seq_item   item;
          tl_channels_e dir;

          dir_fifo.get(dir);
          case (dir)
            AddrChannel: begin
              `DV_CHECK_FATAL(a_chan_fifo.try_get(item),
                              "dir_fifo pointed at A channel, but a_chan_fifo empty")
            end
            DataChannel: begin
              `DV_CHECK_FATAL(d_chan_fifo.try_get(item),
                              "dir_fifo pointed at D channel, but d_chan_fifo empty")
            end
            default: `dv_fatal($sformatf("Invalid direction %p from tl_agent monitor", dir))
          endcase
          process_tl_mbx_mem_access(item, dir);
        end
      end
      // TODO: Re-enable interrupt checking once scoreboard is fully functional
      //  monitor_core_interrupt();
      //  monitor_exp_core_interrupts();
    join
  endtask

  // Mailbox becoming Idle. This can occur for a number of reasons:
  // - clearing an abort request.
  // - raising an error condition.
  // - transfer of response completed.
  function void mbx_deactivate();
    m_mbx_busy    = 1'b0;
    m_mbx_ready   = 1'b0;
    m_mbx_error   = 1'b0;
    m_mbx_abort   = 1'b0;
    m_ibmbx_start = 1'b1;
    m_ib_data_q.delete();
    m_ob_data_q.delete();
  endfunction

  // Model TL-UL register accesses. There are two TL-UL register interfaces:
  // - Root of Trust side (a.k.a. `core`)
  // - System On Chip side
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    case (ral_name)
      RAL_T::type_name:     process_tl_mbx_core_access(item, channel);
      cfg.mbx_soc_ral_name: process_tl_mbx_soc_access(item, channel);
      default: `uvm_fatal(`gfn, $sformatf("Invalid RAL: %0s", ral_name))
    endcase
  endtask

  // Model register accesses on the RoT ('core') TL-UL bus.
  virtual function void process_tl_mbx_core_access(tl_seq_item item, tl_channels_e channel);
    uvm_reg csr;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[RAL_T::type_name].get_word_aligned_addr(
                              item.a_addr);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);

    `uvm_info(`gfn, "process_tl_mbx_core_access -- Start", UVM_DEBUG)
    csr = cfg.ral_models[RAL_T::type_name].default_map.get_reg_by_offset(csr_addr);

    if (csr && addr_phase_write) begin
      `uvm_info(`gfn, $sformatf("Core register '%s' write 0x%x", csr.get_name(), item.a_data),
                UVM_MEDIUM)

      // `ADDRESS_RANGE_REGWEN` controls writing to the address-related registers on the RoT side,
      // but if the register write is not gated by that, then perform the update immediately.
      if (prim_mubi_pkg::MuBi4True == `gmv(ral.address_range_regwen) ||
          !ral.address_range_regwen.locks_reg_or_fld(csr)) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end

      case (csr.get_name())
        "intr_test": begin
          uvm_reg_data_t intr_enable = `gmv(ral.intr_enable);
          `uvm_info(`gfn, $sformatf("intr_test write 0x%x with enables 0x%0x", item.a_data,
                                    intr_enable), UVM_HIGH)
          // Sample tested interrupts.
          if (cfg.en_cov) begin
            uvm_reg_data_t intr_state = `gmv(ral.intr_state);
            foreach (item.a_data[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_enable[i], intr_state[i]);
            end
          end
        end

        "control": begin
          if (get_field_val(ral.control.abort, item.a_data)) begin
            // Clearing Abort condition; this also serves as a RoT firmware 'panic' akin to a sw
            // reset of the DUT.
            mbx_deactivate();
          end
          // Setting of error condition.
          if (get_field_val(ral.control.error, item.a_data)) begin
            mbx_deactivate();
            m_mbx_error = 1'b1;
            m_ibmbx_start = 1'b1;
          end
          // Raise asynchronous message notification.
          if (get_field_val(ral.control.sys_async_msg, item.a_data)) m_mbx_async_msg = 1'b1;
          if (cfg.en_cov) begin
            // Collect coverage on stimulation of CONTROL bits.
            cov.rot_control_cg.sample(.abort(get_field_val(ral.control.abort, item.a_data)),
                                      .error(get_field_val(ral.control.error, item.a_data)),
                                      .sys_async_msg(get_field_val(ral.control.sys_async_msg,
                                                                   item.a_data)));
          end
        end

        "outbound_object_size": begin
          m_obdwcnt = get_field_val(ral.outbound_object_size.cnt, item.a_data);
          `uvm_info(`gfn, $sformatf("Updating m_obdwcnt to %0d", m_obdwcnt), UVM_LOW)
          if (cfg.en_cov) cov.object_size_cg.sample(m_obdwcnt);
        end

        // These registers do not require any further modeling.
        "alert_test",
        "intr_state",
        "intr_enable",
        "status",
        "address_range_regwen",
        "address_range_valid",
        "inbound_base_address",
        "inbound_limit_address",
        "inbound_write_ptr",
        "outbound_read_ptr",
        "outbound_base_address",
        "outbound_limit_address",
        "doe_intr_msg_addr",
        "doe_intr_msg_data":; // Do nothing

        default: `dv_fatal($sformatf("Core register '%s' write not modeled", csr.get_name()))
      endcase
    end else if (csr && data_phase_read) begin
      bit do_read_check = 1'b1;

      case (csr.get_name())
        "inbound_write_ptr": begin
          // Update prediction based upon observed traffic to SRAM.
          void'(ral.inbound_write_ptr.predict(.value(m_ibmbx_ptr), .kind(UVM_PREDICT_READ)));
        end
        "outbound_read_ptr": begin
          // Update prediction based upon observed traffic from SRAM.
          void'(ral.outbound_read_ptr.predict(.value(m_obmbx_ptr), .kind(UVM_PREDICT_READ)));
        end
        "outbound_object_size": begin
          // Update prediction based upon observed traffic from SRAM.
          void'(ral.outbound_object_size.predict(.value(m_obdwcnt), .kind(UVM_PREDICT_READ)));
        end

        "status": begin
          // Our expectation of the `busy` indicator.
          void'(ral.status.busy.predict(.value(m_mbx_busy), .kind(UVM_PREDICT_READ)));
          // These fields are aliases of the SoC-side status indicators.
          // TODO: We still need to model interrupts properly.
          //void'(ral.status.sys_intr_state.predict(
          //        .value(`gmv(m_mbx_soc_ral.soc_status.doe_intr_status)), .kind(UVM_PREDICT_READ)));
          void'(ral.status.sys_intr_enable.predict(
                  .value(`gmv(m_mbx_soc_ral.soc_control.doe_intr_en)), .kind(UVM_PREDICT_READ)));
          void'(ral.status.sys_async_enable.predict(
                  .value(`gmv(m_mbx_soc_ral.soc_control.doe_async_msg_en)),
                  .kind(UVM_PREDICT_READ)));
          if (cfg.en_cov) begin
            // Collect coverage for the observed DUT status indicators.
            cov.rot_status_cg.sample(
              .busy(get_field_val(ral.status.busy, item.d_data)),
              .sys_intr_state(get_field_val(ral.status.sys_intr_state, item.d_data)),
              .sys_intr_enable(get_field_val(ral.status.sys_intr_enable, item.d_data)),
              .sys_async_enable(get_field_val(ral.status.busy, item.d_data)));
          end
          // TODO: the scoreboard cannot really check this yet; requires interrupt prediction.
          do_read_check = 1'b0;
        end

        "intr_state": begin
          // TODO: Presently the scoreboard is not up to the task of predicting interrupts.
          do_read_check = 1'b0;

          if (cfg.en_cov) begin
            uvm_reg_data_t intr_enable = `gmv(ral.intr_enable);
            uvm_reg_data_t intr_state = item.d_data;
            foreach (item.d_data[i]) begin
              cov.intr_cg.sample(i, intr_enable[i], intr_state[i]);
              cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
            end
          end
        end

        // These registers do not require any further modeling.
        "alert_test",
        "intr_enable",
        "intr_test",
        "control",
        "address_range_regwen",
        "address_range_valid",
        "inbound_base_address",
        "inbound_limit_address",
        "outbound_base_address",
        "outbound_limit_address":; // Do nothing

        // These registers are aliases of the SoC-side registers; they form a Read Only channel
        // from the SoC side. They have no direct input on the DUT internals or its ports, but are
        // instead intended to be used by firmware via another channel.
        "doe_intr_msg_addr": begin
          uvm_reg_data_t addr = item.d_data;
          // We cannot readily predict this value with accurate timing.
          do_read_check = 1'b0;
          if (cfg.en_cov) begin
            // Collect coverage to be sure that we have seen each of the bits in each of its two
            // possible states.
            foreach (addr[i]) cov.doe_intr_msg_addr_cg.sample(i, addr[i]);
          end
        end
        "doe_intr_msg_data": begin
          uvm_reg_data_t data = item.d_data;
          // We cannot readily predict this value with accurate timing.
          do_read_check = 1'b0;
          if (cfg.en_cov) begin
            foreach (data[i]) cov.doe_intr_msg_data_cg.sample(i, data[i]);
          end
        end
        default: `dv_fatal($sformatf("Core register '%s' read not modeled", csr.get_name()))
      endcase

      if (do_read_check) begin
        // Check read data returned by DUT against the mirrored value.
        `DV_CHECK_EQ(item.d_data, `gmv(csr),
                     $sformatf("Core register '%s' does not have expected value", csr.get_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end

    `uvm_info(`gfn, "process_tl_mbx_core_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_core_access

  // Model register accesses on the SoC TL-UL bus.
  virtual function void process_tl_mbx_soc_access(tl_seq_item item, tl_channels_e channel);
    uvm_reg csr;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = m_mbx_soc_ral.get_word_aligned_addr(item.a_addr);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);

    `uvm_info(`gfn, "process_tl_mbx_soc_access -- Start", UVM_DEBUG)
    csr = m_mbx_soc_ral.default_map.get_reg_by_offset(csr_addr);

    // Note: WDATA and RDATA memory windows exist on the SoC TL-UL interface, and these are not
    //       regular CSRs, so `csr` will be null.

    if (addr_phase_write) begin
      if (csr) begin
        `uvm_info(`gfn, $sformatf("SoC register '%s' write 0x%x", csr.get_name(), item.a_data),
                  UVM_MEDIUM)

        // If incoming access is a write to a valid CSR, then make updates right away.
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

        case (csr.get_name())
          "soc_control": begin
            // Abort requests.
            if (get_field_val(m_mbx_soc_ral.soc_control.abort, item.a_data)) begin
              mbx_deactivate();
              m_mbx_abort = 1'b1;
            end
            // Go bit notifies the RoT side that there is a message available.
            if (get_field_val(m_mbx_soc_ral.soc_control.go, item.a_data)) begin
              // Note that the Inbound mailbox (SoC -> RoT) is already active at this point and
              // will have written (most of) the request into the mailbox SRAM.
              m_mbx_busy = 1'b1;
              // Set the initial expectation of the Outbox read pointer.
              m_obmbx_ptr = `gmv(ral.outbound_base_address);

              if (cfg.en_cov) begin
                cov.mem_range_cg.sample(`gmv(ral.inbound_base_address),
                                        `gmv(ral.outbound_base_address));
              end
            end
            if (cfg.en_cov) begin
              // Collect coverage on stimulation of SOC_CONTROL bits.
              cov.soc_control_cg.sample(
                .abort(get_field_val(m_mbx_soc_ral.soc_control.abort, item.a_data)),
                .doe_intr_en(get_field_val(m_mbx_soc_ral.soc_control.doe_intr_en, item.a_data)),
                .doe_async_msg_en(get_field_val(m_mbx_soc_ral.soc_control.doe_async_msg_en,
                                                item.a_data)),
                .go(get_field_val(m_mbx_soc_ral.soc_control.go, item.a_data)));
            end
          end

          // These registers do not require any further modeling.
          "soc_status",
          "soc_doe_intr_msg_addr",
          "soc_doe_intr_msg_data":; // Do nothing

          default: `dv_fatal($sformatf("SoC register '%s' write not modeled", csr.get_name()))
        endcase
      end else begin
        // DUT has two memory windows on the SoC TL-UL:
        // - WDATA transfers the request from the SoC to the RoT.
        // - RDATA retrieves the response from the RoT.
        uvm_mem mem = m_mbx_soc_ral.default_map.get_mem_by_offset(csr_addr);
        case (mem.get_name())
          "wdata": begin
            `uvm_info(`gfn, $sformatf("WDATA write of 0x%0x (Inbox [0x%0x,0x%0x] wdata_ptr 0x%0x",
                                      item.a_data, `gmv(ral.inbound_base_address),
                                      `gmv(ral.inbound_limit_address), m_ib_wdata_ptr),
                      UVM_MEDIUM)
            // Set the initial expectation of the Inbox write pointer.
            if (m_ibmbx_start) begin
              m_ibmbx_start = 1'b0;
              // Expected address for memory traffic.
              m_ibmbx_ptr = `gmv(ral.inbound_base_address);
              // Expected address at which WDATA would be written, if deemed valid.
              m_ib_wdata_ptr = m_ibmbx_ptr;
            end
            if (m_ib_wdata_ptr <= `gmv(ral.inbound_limit_address)) begin
              // Append this data word to the request.
              m_ib_data_q.push_back(item.a_data);
              m_ib_wdata_ptr += 4;
            end else begin
              // Raise an Inbound mailbox overflow error.
              m_mbx_error = 1'b1;
            end
          end
          "rdata": begin
            // Writing to RDATA pops the most recent data word from the Outbox.
            if (m_ob_data_q.size() > 0) begin
              `uvm_info(`gfn, "RDATA write, popping DWORD", UVM_MEDIUM)
              m_ob_data_q.pop_front();
            end
            // Update our expectation of whether the mailbox is busy.
            if (!m_ob_data_q.size()) begin
              m_mbx_busy = 1'b0;
              m_mbx_ready = 1'b0;
              // Starting a new request on the Inbound side.
              m_ibmbx_start = 1'b1;
            end
          end
          default: `dv_fatal($sformatf("SoC memory '%s' write not handled", mem.get_name()))
        endcase
      end
    end else if (data_phase_read) begin
      if (csr) begin
        bit do_read_check = 1'b1;

        case (csr.get_name())
          "soc_status": begin
            void'(m_mbx_soc_ral.soc_status.busy.predict(.value(m_mbx_busy),
                                                        .kind(UVM_PREDICT_READ)));
            void'(m_mbx_soc_ral.soc_status.doe_intr_status.predict(
                    .value(|{m_mbx_ready, m_mbx_abort, m_mbx_error, m_mbx_async_msg}),
                    .kind(UVM_PREDICT_READ)));
            void'(m_mbx_soc_ral.soc_status.error.predict(.value(m_mbx_error),
                                                         .kind(UVM_PREDICT_READ)));
            void'(m_mbx_soc_ral.soc_status.doe_async_msg_status.predict(.value(m_mbx_async_msg),
                                                                        .kind(UVM_PREDICT_READ)));
            void'(m_mbx_soc_ral.soc_status.ready.predict(.value(m_mbx_ready),
                                                         .kind(UVM_PREDICT_READ)));
            if (cfg.en_cov) begin
              // Collect coverage for the observed DUT status indicators.
              cov.soc_status_cg.sample(
                .busy(get_field_val(m_mbx_soc_ral.soc_status.ready, item.d_data)),
                .doe_intr_status(get_field_val(m_mbx_soc_ral.soc_status.doe_intr_status,
                                               item.d_data)),
                .error(get_field_val(m_mbx_soc_ral.soc_status.error, item.d_data)),
                .doe_async_msg_status(get_field_val(m_mbx_soc_ral.soc_status.doe_async_msg_status,
                                                    item.d_data)),
                .ready(get_field_val(m_mbx_soc_ral.soc_status.ready, item.d_data)));
            end
            // TODO: Modeling is presently not up to the task.
            do_read_check = 1'b0;
          end

          // These registers do not require any further modeling.
          "soc_control",
          "soc_doe_intr_msg_addr",
          "soc_doe_intr_msg_data":; // Do nothing

          default: `dv_fatal($sformatf("SoC register '%s' read not modeled", csr.get_name()))
        endcase

        if (do_read_check) begin
          // Check read data returned by DUT against the mirrored value.
          `DV_CHECK_EQ(item.d_data, `gmv(csr),
                       $sformatf("SoC register '%s' does not have expected value", csr.get_name()))
        end
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end else begin
        // DUT has two memory windows on the SoC TL-UL:
        // - WDATA transfers the request from the SoC to the RoT.
        // - RDATA retrieves the response from the RoT.
        uvm_mem mem = m_mbx_soc_ral.default_map.get_mem_by_offset(csr_addr);
        case (mem.get_name())
          "wdata": begin // Reading WDATA shall always return zero.
            `uvm_info(`gfn, $sformatf("WDATA read of 0x%0x", item.a_data), UVM_MEDIUM)
            `DV_CHECK_EQ(item.d_data, 0, "Read of WDATA returned non-zero value")
          end
          "rdata": begin
            uvm_reg_data_t exp_data = 0;
            if (m_ob_data_q.size() > 0) exp_data = m_ob_data_q[0];
            `DV_CHECK_EQ(item.d_data, exp_data, "RDATA read data mismatched")
          end
          default: `dv_fatal($sformatf("SoC memory '%s' read not handled", mem.get_name()))
        endcase
      end
    end
    `uvm_info(`gfn, "process_tl_mbx_soc_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_soc_access

  virtual function void process_tl_mbx_mem_access(tl_seq_item item, tl_channels_e channel);
    bit write             = item.is_write();
    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    `uvm_info(`gfn, "process_tl_mbx_mem_access -- Start", UVM_DEBUG)
    if (addr_phase_read || addr_phase_write) begin
      // Check for integrity error on Address
      void'(item.is_a_chan_intg_ok(.throw_error(1)));

      // Check the transaction is full 4B access
      `DV_CHECK_EQ(((item.a_size == 2) && (item.a_mask == '1)), 1,
         $sformatf("Incorrect a_size(%0d) or a_mask('b%0b)", item.a_size, item.a_mask))

      // Check the addresses are generated between the configured limits only
      if (addr_phase_write) begin
        bit is_addr_match;

        // Check if address is within IB Mailbox SRAM range
        is_addr_match = (item.a_addr >= ral.inbound_base_address.get()) &&
                        (item.a_addr <= ral.inbound_limit_address.get());
        `DV_CHECK_EQ(is_addr_match, 1,
          $sformatf("Address('h%0h) doesn't match any of inbound mailbox address ranges",
          item.a_addr))

        // Check if the SRAM write is expected or not
        `DV_CHECK_NE(m_ib_data_q.size(), 0, "No write data in WDATA register")

        // Check if the SRAM write address is correct.
        `DV_CHECK_EQ(item.a_addr, m_ibmbx_ptr, "Incorrect address seen on the write to SRAM")
        m_ibmbx_ptr += 4;

        // Check if the data written matches with the data written to WDATA.
        `DV_CHECK_EQ(item.a_data, m_ib_data_q[0],
          "Bus data doesn't match with data written to WDATA")
        void'(m_ib_data_q.pop_front());
      end
    end else if (data_phase_read) begin
      bit is_addr_match;

      // Check if address is within OB Mailbox SRAM range
      is_addr_match = (item.a_addr >= ral.outbound_base_address.get()) &&
                      (item.a_addr <= ral.outbound_limit_address.get());
      `DV_CHECK_EQ(is_addr_match, 1,
        $sformatf("Address('h%0h) out of outbound mailbox address ranges",  item.a_addr))

      // No read should occur when obdwcnt is '0'
      `DV_CHECK_NE(m_obdwcnt, 0, "Illegal read from memory when obdwcnt is 0")

      // Check if the SRAM read address is correct.
      `DV_CHECK_EQ(item.a_addr, m_obmbx_ptr, "Incorrect address seen on the read to SRAM")
      `uvm_info(`gfn, $sformatf("Added data 'h%0h to m_ob_data_q", item.d_data), UVM_LOW)
      m_ob_data_q.push_back(item.d_data);

      // Update Outbound reader state.
      m_mbx_ready = 1'b1;
      m_obmbx_ptr += 4;
      m_obdwcnt--;
    end
    `uvm_info(`gfn, "process_tl_mbx_mem_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_mem_access

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    m_ib_data_q.delete();
    m_ob_data_q.delete();
    m_ibmbx_ptr = 0;
    m_obmbx_ptr = 0;
    m_obdwcnt = 0;
    m_mbx_busy = 1'b0;
    m_mbx_error = 1'b0;
    m_mbx_async_msg = 1'b0;
    m_ibmbx_start = 1'b1;
    exp_mbx_core_irq = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    if(m_ib_data_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("m_ib_data_q is not empty(%0d)", m_ib_data_q.size()))
    end
    if(m_ob_data_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("m_ob_data_q is not empty(%0d)", m_ob_data_q.size()))
    end
    if(exp_mbx_core_irq_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("exp_mbx_core_irq_q is not empty(%0d)", exp_mbx_core_irq_q.size()))
    end
  endfunction

endclass
