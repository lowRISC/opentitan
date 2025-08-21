// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class mbx_scoreboard extends cip_base_scoreboard #(
    .CFG_T(mbx_env_cfg),
    .RAL_T(mbx_core_reg_block),
    .COV_T(mbx_env_cov)
  );
  `uvm_component_utils(mbx_scoreboard)

  // local variables
  bit [top_pkg::TL_AW-1:0] m_ibmbx_ptr;
  bit [top_pkg::TL_AW-1:0] m_obmbx_ptr_q[$];
  bit [top_pkg::TL_AW-1:0] m_obmbx_ptr;
  bit [9:0] m_obdwcnt;
  bit mbxsts_core_wr_in_progress;
  bit mbxsts_system_rd_in_progress;
  bit mbxsts_core_rd_in_progress;
  bit mbxsts_system_wr_in_progress;

  bit skip_read_check;
  bit exp_mbx_core_irq;
  bit exp_mbx_core_irq_q[$];

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison
  bit [top_pkg::TL_DW-1:0] m_ib_q[$];
  bit [top_pkg::TL_DW-1:0] m_ob_q[$];

  // System RAL model
  mbx_soc_reg_block m_mbx_soc_ral;

  `uvm_component_new

  // TODO: Presently no additional work to be done.
  // function void build_phase(uvm_phase phase);
  //   super.build_phase(phase);
  // endfunction
  //
  // function void connect_phase(uvm_phase phase);
  //   super.connect_phase(phase);
  // endfunction

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
    // TODO: Re-enable interrupt checking once scoreboard is fully functional
    //fork
    //  monitor_core_interrupt();
    //  monitor_exp_core_interrupts();
    //join_none
  endtask

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
      // If incoming access is a write to a valid CSR, then make updates right away.
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      case (csr.get_name())
        default:; // Do nothing
        "inbound_write_ptr": m_ibmbx_ptr = item.a_data;
        "outbound_read_ptr": begin
          m_obmbx_ptr_q[0] = item.a_data;
          m_obmbx_ptr = item.a_data;
        end
        "inbound_base_address": begin
          // Do nothing
        end
        "inbound_limit_address": begin
          // Do nothing
        end
        "outbound_base_address": begin
          // Do nothing
        end
        "outbound_limit_address": begin
          // Do nothing
        end
        "outbound_object_size": begin
          m_obdwcnt = item.a_data;
          `uvm_info(`gfn, $sformatf("Updating m_obdwcnt to %0d", m_obdwcnt), UVM_LOW)
        end
        "control": begin
          /* TODO: This looks suspect; confusion over w1c?
          if (ral.control.abort.get_mirrored_value() == 0) begin
            exp_mbx_core_irq = 0;
            exp_mbx_core_irq_q.push_back(0);
          end
          if (ral.control.error.get_mirrored_value() == 1) begin
            // TODO: Check if busy bit is expected to be cleared - RVSCS-491
            void'(ral.status.busy.predict(.value(0), .kind(UVM_PREDICT_READ)));
          end
          */
        end
        "status": begin
          /* TODO: Add the support for async message sts
          if (ral.status.busy.get_mirrored_value() == 0) begin
            exp_mbx_core_irq = 0;
            exp_mbx_core_irq_q.push_back(0);
          end
          */
        end
      endcase
    end else if (csr && data_phase_read) begin
      bit [31:0] mask = 'hffff_ffff;
      bit do_read_check = 1'b1;

      case (csr.get_name())
        default:; // Do nothing
        "inbound_write_ptr": begin
          void'(ral.inbound_write_ptr.predict(
            .value(ral.inbound_base_address.get() + m_ibmbx_ptr),
            .kind(UVM_PREDICT_READ)));
        end
        "outbound_read_ptr": begin
          void'(ral.outbound_read_ptr.predict(
            .value(ral.outbound_base_address.get() + (m_obmbx_ptr_q[0])),
            .kind(UVM_PREDICT_READ)));
        end
        "inbound_base_address": begin
          // Do nothing
        end
        "inbound_limit_address": begin
          // Do nothing
        end
        "outbound_base_address": begin
          // Do nothing
        end
        "outbound_limit_address": begin
          // Do nothing
        end
        "outbound_object_size": begin
          void'(ral.outbound_object_size.predict(.value(m_obdwcnt), .kind(UVM_PREDICT_READ)));
        end
        "control": begin
          // Do nothing
        end
        "status": begin
          //TODO: Review ready field
          mask = 'h7fff_ffff;
        end
      endcase

      if (do_read_check) begin
        // Check mirrored_value against item.d_data
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end
    end

    `uvm_info(`gfn, "process_tl_mbx_core_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_core_access

  // Model register accesses on the SoC TL-UL bus.
  virtual function void process_tl_mbx_soc_access(tl_seq_item item, tl_channels_e channel);
    uvm_reg csr;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr =
      cfg.ral_models[cfg.mbx_soc_ral_name].get_word_aligned_addr(item.a_addr);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);

    `uvm_info(`gfn, "process_tl_mbx_soc_access -- Start", UVM_DEBUG)
    csr = cfg.ral_models[cfg.mbx_soc_ral_name].default_map.get_reg_by_offset(csr_addr);

    // Note: WDATA and RDATA memory windows exist on the SoC TL-UL interface, and these are not
    //       regular CSRs, so `csr` will be null.

    if (addr_phase_write) begin
      if (csr) begin
        // If incoming access is a write to a valid CSR, then make updates right away.
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

        case (csr.get_name())
          default:; // Do nothing
          "soc_control": begin
            mbx_soc_reg_soc_control ctl_reg_h;

            `DV_CHECK_FATAL($cast(ctl_reg_h, csr), "Unable to cast csr handle to MBX control type")

            /* TODO: Fix this.
            if(ctl_reg_h.abort.get() == 1) begin
              exp_mbx_core_irq = 1;
              exp_mbx_core_irq_q.push_back(1);
              // TODO: Check if busy bit also needs to be set
              void'(ral.control.abort.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
              void'(ral.status.busy.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
              if((ral.status.busy.get() == 1) || (ral.control.error.get() == 1) ||
                (m_obdwcnt != 0)) begin
                void'(ral.status.busy.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
              end
            end else if((item.a_data[31] & item.a_mask[3]) == 1) begin
              // if (ctl_reg_h.abort.get() == 1)
              if((ral.status.busy.get() == 0) && (ral.control.error.get() == 0) &&
                (ral.control.abort.get() == 0)) begin
                void'(ral.status.busy.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
                void'(m_mbx_soc_ral.soc_status.busy.predict(.value(1), .kind(UVM_PREDICT_READ)));

                exp_mbx_core_irq = 1;
                exp_mbx_core_irq_q.push_back(1);
              end
            end
            */
            void'(ral.status.sys_intr_enable.predict(
                     .value(ctl_reg_h.doe_intr_en.get()),
                     .kind(UVM_PREDICT_WRITE)));
            // TODO: Add async logic
          end
          "soc_status": begin
            mbx_soc_reg_soc_status soc_sts_reg_h;
            mbx_core_reg_status hst_sts_reg_h;
            mbx_core_reg_control hst_ctl_reg_h;

            `DV_CHECK_FATAL($cast(soc_sts_reg_h, csr),
              "Unable to cast csr handle to soc_status type")
            hst_sts_reg_h = ral.status;
            hst_ctl_reg_h = ral.control;
            if((item.a_data[1] & item.a_mask[0]) == 1) begin
              void'(hst_sts_reg_h.sys_intr_state.predict(.value(0)));
            end
          end
        endcase
      end else begin
        // TODO: else model WDATA / RDATA.
        // WDATA: m_ib_q.push_back(item.a_data);
        // RDATA:
        //  int tmp_ptr=0;
        //  if(m_obmbx_ptr_q.size() == 0)
        //    tmp_ptr = m_obmbx_ptr+4;
        //  else
        //    tmp_ptr = m_obmbx_ptr_q[$]+4;
        //    m_obmbx_ptr_q.push_back(tmp_ptr);
        //    m_obmbx_ptr = tmp_ptr;
        //    m_obdwcnt--;
        //    void'(m_ob_q.pop_front());
      end
    end else if (data_phase_read) begin
      bit do_read_check = 1'b1;

      if (csr) begin
        case (csr.get_name())
          default:; // Do nothing
          "soc_control": begin
            mbx_soc_reg_soc_control ctl_reg_h;
            void'(ctl_reg_h.abort.predict(
                            .value(0),
                            .kind(UVM_PREDICT_READ)));
            void'(ctl_reg_h.doe_intr_en.predict(
                            .value(ral.status.sys_intr_enable.get()),
                            .kind(UVM_PREDICT_READ)));
            void'(ctl_reg_h.go.predict(
                            .value(0),
                            .kind(UVM_PREDICT_READ)));
            // TODO Add async logic
          end
          "soc_status": begin
            mbx_soc_reg_soc_status soc_sts_reg_h;
            mbx_core_reg_status hst_sts_reg_h;
            mbx_core_reg_control hst_ctl_reg_h;

            `DV_CHECK_FATAL($cast(soc_sts_reg_h, csr),
              "Unable to cast csr handle to soc_status type")
            hst_sts_reg_h = ral.status;
            hst_ctl_reg_h = ral.control;

            void'(soc_sts_reg_h.busy.predict(
                               .value(hst_sts_reg_h.busy.get()),
                               .kind(UVM_PREDICT_READ)));
            void'(soc_sts_reg_h.doe_intr_status.predict(
                               .value(hst_sts_reg_h.sys_intr_state.get()),
                               .kind(UVM_PREDICT_READ)));
            void'(soc_sts_reg_h.error.predict(
                               .value(hst_ctl_reg_h.error.get()),
                               .kind(UVM_PREDICT_READ)));
            //TODO: Review new ready field
            void'(soc_sts_reg_h.ready.predict(
                               .value(m_obdwcnt != 0),
                               .kind(UVM_PREDICT_READ)));
          end
        endcase
      end else begin
        // TODO: else model WDATA / RDATA.
        // WDATA: void'(csr.predict(.value(0), .kind(UVM_PREDICT_READ)));
        // RDATA:
        //  if(m_obdwcnt == 0) begin
        //      void'(csr.predict(.value(0), .kind(UVM_PREDICT_READ)));
        //  end else begin
        //       void'(csr.predict(.value(m_ob_q[0]), .kind(UVM_PREDICT_READ)));
        //  end
      end
    end
    `uvm_info(`gfn, "process_tl_mbx_soc_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_soc_access

  // TODO: This is presently unused, but we shall want to check all of the TL-UL traffic to/from
  // the mailbox SRAM as it happens.
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
      if(addr_phase_write) begin
        bit is_addr_match;

        // Check if address is within IB Mailbox SRAM range
        if((item.a_addr >= ral.inbound_base_address.get()) &&
          (item.a_addr < ral.inbound_limit_address.get())) begin
          is_addr_match = 1'b1;
        end
        `DV_CHECK_EQ(is_addr_match, 1,
          $sformatf("Address('h%0h) doesn't match any of inbound mailbox address ranges",
          item.a_addr))

        // Check if the SRAM write is expected or not
        `DV_CHECK_NE(m_ib_q.size(), 0, "No write data in mbxwrdat register")

        // Check if the SRAM write address is correct.
        `DV_CHECK_EQ(item.a_addr, (ral.inbound_base_address.get() + m_ibmbx_ptr),
          "Incorrect address seen on the write to SRAM")
        m_ibmbx_ptr += 4;

        // Check if the data written matches with the data written to wrdat register
        `DV_CHECK_EQ(item.a_data, m_ib_q[0],
          "Bus data doesn't match with data written to wdat")
        void'(m_ib_q.pop_front());
      end
    end
    if (data_phase_read) begin
      bit is_addr_match;

      // Check if address is within OB Mailbox SRAM range
      if((item.a_addr >= ral.outbound_base_address.get()) &&
        (item.a_addr < ral.outbound_limit_address.get())) begin
        is_addr_match = 1'b1;
      end
      `DV_CHECK_EQ(is_addr_match, 1,
        $sformatf("Address('h%0h) out of outbound mailbox address ranges",  item.a_addr))

      // No read should occur when obdwcnt is '0'
      `DV_CHECK_NE(m_obdwcnt, 0, "Illegal read from memory when obdwcnt is 0")

       m_obmbx_ptr = m_obmbx_ptr_q[0];
      // Check if the SRAM read address is correct.
      `DV_CHECK_EQ(item.a_addr, (ral.outbound_base_address.get() + m_obmbx_ptr_q[0]),
        "Incorrect address seen on the read to SRAM")
      `uvm_info(`gfn, $sformatf("Added data 'h%0h to m_ob_q", item.d_data), UVM_LOW)
       m_ob_q.push_back(item.d_data);
       void'(m_obmbx_ptr_q.pop_front());

    end
    `uvm_info(`gfn, "process_tl_mbx_mem_access -- End", UVM_DEBUG)
  endfunction : process_tl_mbx_mem_access

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    m_ib_q.delete();
    m_ob_q.delete();
    m_ibmbx_ptr = 0;
    m_obmbx_ptr = 0;
    m_obdwcnt = 0;
    exp_mbx_core_irq = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    if(m_ib_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("m_ib_q is not empty(%0d)", m_ib_q.size()))
    end
    if(m_ob_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("m_ob_q is not empty(%0d)", m_ob_q.size()))
    end
    if(exp_mbx_core_irq_q.size() > 0) begin
      `uvm_error(`gfn, $sformatf("exp_mbx_core_irq_q is not empty(%0d)", exp_mbx_core_irq_q.size()))
    end
  endfunction

endclass
