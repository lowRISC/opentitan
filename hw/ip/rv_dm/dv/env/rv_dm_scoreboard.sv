// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_scoreboard extends cip_base_scoreboard #(
    .CFG_T(rv_dm_env_cfg),
    .RAL_T(rv_dm_regs_reg_block),
    .COV_T(rv_dm_env_cov)
  );
  `uvm_component_utils(rv_dm_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_sba_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)  tl_sba_d_chan_fifo;
  uvm_tlm_analysis_fifo #(jtag_item)    jtag_non_dmi_dtm_fifo;
  uvm_tlm_analysis_fifo #(jtag_dmi_item)jtag_non_sba_dmi_fifo;

  uvm_tlm_analysis_fifo #(sba_access_item) sba_access_fifo;

  // Items from sba_access_fifo come in much later because the inferred transactions are marked
  // completed only when the JTAG interface actually reads the SBCS register. So we capture and hold
  // the TL accesses over SBA and compare against SBA access whenever they arrive.
  tl_seq_item sba_tl_access_q[$];

  // Currently selected non-DMI DTM CSR.
  uvm_reg selected_dtm_csr;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_non_dmi_dtm_fifo = new("jtag_non_dmi_dtm_fifo", this);
    jtag_non_sba_dmi_fifo = new("jtag_non_sba_dmi_fifo", this);
    sba_access_fifo = new("sba_access_fifo", this);
    tl_sba_a_chan_fifo = new("tl_sba_a_chan_fifo", this);
    tl_sba_d_chan_fifo = new("tl_sba_d_chan_fifo", this);
    // TODO: remove once support alert checking
    do_alert_check = 0;
    selected_dtm_csr = cfg.m_jtag_agent_cfg.jtag_dtm_ral.default_map.get_reg_by_offset(0);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_jtag_non_dmi_dtm_fifo();
      process_jtag_non_sba_dmi_fifo();
      process_sba_access_fifo();
      process_tl_sba_a_chan_fifo();
      process_tl_sba_d_chan_fifo();
    join_none
  endtask

  // Receive and process incoming raw JTAG accesses to non-DMI DTM registers.
  virtual task process_jtag_non_dmi_dtm_fifo();
    jtag_item item;

    forever begin
      jtag_non_dmi_dtm_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received jtag non-DMI DTM item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      if (item.ir_len) begin
        selected_dtm_csr = cfg.m_jtag_agent_cfg.jtag_dtm_ral.default_map.get_reg_by_offset(item.ir);
        continue;
      end

      if (selected_dtm_csr == null) begin
        // Behaviour on unmapped regions of the JTAG DTM register space is not defined. In
        // particular, we don't have an opinion about what dout should contain.
        continue;
      end

      case (selected_dtm_csr.get_name())
        "bypass0", "bypass1": begin
          // TDI gets shifted out of TDO, and appears left-shifted by 1 - new write is ignored.
          uvm_reg_data_t rwdata;
          rwdata = get_field_val(selected_dtm_csr.get_field_by_name("bypass"), item.dout);
          `DV_CHECK_EQ(rwdata, 0)
          void'(selected_dtm_csr.predict(.value(item.dr), .kind(UVM_PREDICT_WRITE)));
        end
        "idcode": begin
          `DV_CHECK_EQ(item.dout[31:0], selected_dtm_csr.get_mirrored_value())
          void'(selected_dtm_csr.predict(.value(item.dr), .kind(UVM_PREDICT_WRITE)));
        end
        "dtmcs": begin
          // DMI traffic is internal to rv_dm module. The stimulus in jtag_dmi_reg_frontdoor reads
          // the dmistat field of dtmcs register to determine if the previous transaction completed.
          // It is not possible to predict the value of this field, unless the internals of the
          // design (dmi_jtag module) is probed. Instead of doing that, checking the correctness of
          // dmistat field can be offloaded to a directed test that generates DMI busy scenarios.
          uvm_reg_data_t mask = ~dv_base_reg_pkg::get_mask_from_fields(
              {cfg.m_jtag_agent_cfg.jtag_dtm_ral.dtmcs.dmistat});
          `DV_CHECK_EQ(item.dout & mask, selected_dtm_csr.get_mirrored_value() & mask)
          void'(selected_dtm_csr.predict(.value(item.dr), .kind(UVM_PREDICT_WRITE)));
        end
        default: `uvm_fatal(`gfn, $sformatf("Unknown DTM CSR: %0s", selected_dtm_csr.get_name()))
      endcase
    end
  endtask

  // Receive and process incoming completed JTAG DMI accesses to non-SBA registers.
  virtual task process_jtag_non_sba_dmi_fifo();
    uvm_reg       csr;
    jtag_dmi_item item;
    bit           do_read_check;

    forever begin
      jtag_non_sba_dmi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received jtag non-SBA DMI item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      if (item.req_op == DmiOpNone) begin
        continue;
      end

      // TODO: effect of lc_hw_debug_en.

      if (item.rsp_op != DmiOpOk) begin
        // TODO: predict error DMI access.
        continue;
      end

      csr = cfg.jtag_dmi_ral.default_map.get_reg_by_offset(item.addr);
      if (csr == null) begin
        // TODO: what should happen here?
        continue;
      end

      if (item.req_op == DmiOpWrite) begin
        void'(csr.predict(.value(item.wdata), .kind(UVM_PREDICT_WRITE)));
      end
      do_read_check = 1'b0;  // TODO.
      case (1)
        (!uvm_re_match("abstractdata_*", csr.get_name())): begin
        end
        (!uvm_re_match("dmcontrol", csr.get_name())): begin
        end
        (!uvm_re_match("dmstatus", csr.get_name())): begin
        end
        (!uvm_re_match("hartinfo", csr.get_name())): begin
        end
        (!uvm_re_match("abstractcs", csr.get_name())): begin
        end
        (!uvm_re_match("command", csr.get_name())): begin
        end
        (!uvm_re_match("abstractauto", csr.get_name())): begin
        end
        (!uvm_re_match("progbuf_*", csr.get_name())): begin
        end
        (!uvm_re_match("haltsum0", csr.get_name())): begin
        end
        (!uvm_re_match("haltsum1", csr.get_name())): begin
        end
        (!uvm_re_match("haltsum2", csr.get_name())): begin
        end
        (!uvm_re_match("haltsum3", csr.get_name())): begin
        end
        (!uvm_re_match("sbaddress*", csr.get_name())): begin
        end
        (!uvm_re_match("sbdata*", csr.get_name())): begin
        end
        default: `uvm_fatal(`gfn, $sformatf("Unknown DMI CSR: %0s", csr.get_name()))
      endcase

      // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
      if (item.req_op == DmiOpRead) begin
        if (do_read_check) begin
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.rdata,
                       $sformatf("reg name: %0s", csr.get_full_name()))
        end
        void'(csr.predict(.value(item.rdata), .kind(UVM_PREDICT_READ)));
      end
    end
  endtask

  // Receive and process incoming predicted complete SBA accesses.
  virtual task process_sba_access_fifo();
    sba_access_item item;
    forever begin
      // Watch SBA access items by listening to sba_access_monitor, which infers SBA transactions by
      // watching how the environment is driving the JTAG interface.
      sba_access_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA access item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)

      // If debug is enabled, check that the JTAG access was indeed translated into a TL access.
      if (is_debug_enabled()) begin
        `DV_CHECK_FATAL(sba_tl_access_q.size() > 0,
                        "Saw SBA access on the JTAG side which didn't translate into TL")
      end

      // If the debugger is not enabled and cfg.sba_tl_tx_requires_debug=1 then we should not have
      // seen the SBA item translate into a TL access.
      if (cfg.sba_tl_tx_requires_debug && cfg.rv_dm_vif.lc_hw_debug_en != lc_ctrl_pkg::On) begin
        `DV_CHECK(sba_tl_access_q.size() == 0)
      end

      // If there has been a translation, check it was correct.
      if (sba_tl_access_q.size() > 0) begin
        compare_sba_access(item, sba_tl_access_q.pop_front());
      end
    end
  endtask

  virtual task process_tl_sba_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_sba_a_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA TL a_chan item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      if (cfg.sba_tl_tx_requires_debug) begin
        `DV_CHECK(cfg.rv_dm_vif.lc_hw_debug_en == lc_ctrl_pkg::On,
                  "Received an SBA TL item when SBA should have been disabled.")
      end

      process_tl_sba_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_sba_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_sba_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA TL d_chan item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      if (cfg.sba_tl_tx_requires_debug) begin
        `DV_CHECK(cfg.rv_dm_vif.lc_hw_debug_en == lc_ctrl_pkg::On,
                  "Received an SBA TL item when SBA should have been disabled.")
      end
      sba_tl_access_q.push_back(item);
      // check tl packet integrity
      if (!item.is_ok()) begin
        // TODO: deal with item not being ok.
      end
      process_tl_sba_access(item, DataChannel);
    end
  endtask

  // task to process tl access
  virtual task process_tl_sba_access(tl_seq_item item, tl_channels_e channel);
  endtask

  virtual function void compare_sba_access(sba_access_item sba_item, tl_seq_item sba_tl_item);
    logic [BUS_AW-1:0] word_aligned_addr;
    logic [BUS_DW-1:0] data, shift;
    string msg;

    msg = $sformatf("\nSBA item:\n%0sSBA TL item:\n%0s",
                    sba_item.sprint(uvm_default_line_printer),
                    sba_tl_item.sprint(uvm_default_line_printer));

    // TLUL address will always be word-aligned.
    shift = 8 * sba_item.addr[BUS_SZW-1:0];
    word_aligned_addr = sba_item.addr & ('1 << BUS_SZW);
    `DV_CHECK_EQ(word_aligned_addr, sba_tl_item.a_addr, msg)

    // TLUL access size will always be full word.
    `DV_CHECK_EQ(sba_tl_item.a_size, $clog2(bus_params_pkg::BUS_DBW), msg)

    if (sba_item.bus_op == BusOpRead) begin
      `DV_CHECK_EQ(sba_tl_item.a_opcode, tlul_pkg::Get, msg)
      // SBA system shifts the read data based on transfer size. The higher order bits that are
      // don't care are left alone. The RISCV debug spec does not mandate that they be masked.
      data = sba_tl_item.d_data >> shift;
      `DV_CHECK_EQ(sba_item.rdata[0], data, msg)
      // TLUL adapter host does full word reads with all byte lanes enabled.
      `DV_CHECK_EQ(sba_tl_item.a_mask, '1, msg)
    end else begin
      bit [BUS_DW-1:0] word_mask;
      bit [BUS_DBW-1:0] byte_mask;
      logic [BUS_DW-1:0] act_data;

      // Anything less than word access should be PutPartialData.
      if (sba_item.size < SbaAccessSize32b) begin
        `DV_CHECK_EQ(sba_tl_item.a_opcode, tlul_pkg::PutPartialData, msg)
      end else begin
        `DV_CHECK_EQ(sba_tl_item.a_opcode, tlul_pkg::PutFullData, msg)
      end

      // SBA system shifts the write data based on transfer size. TLUL adapter further masks the
      // don't care higher order bits for correct ECC computation.
      for (int i = 0; i < (1 << sba_item.size); i++) begin
        word_mask[i*8 +: 8] = 8'hff;
        byte_mask[i] = 1'b1;
      end
      data = (sba_item.wdata[0] & word_mask) << shift;
      act_data = sba_tl_item.a_data & (word_mask << shift);
      `DV_CHECK_EQ(data, act_data, msg)
      byte_mask <<= sba_item.addr[BUS_SZW-1:0];
      `DV_CHECK_EQ(byte_mask, sba_tl_item.a_mask, msg)
    end

    // d_chan intg error is reported as "other" error and takes precedence over transaction error.
    if (!sba_tl_item.is_d_chan_intg_ok(.throw_error(0))) begin
      `DV_CHECK_EQ(sba_item.is_err, jtag_rv_debugger_pkg::SbaErrOther)
    end else if (sba_tl_item.d_error) begin
      `DV_CHECK_EQ(sba_item.is_err, jtag_rv_debugger_pkg::SbaErrBadAddr)
    end
    `DV_CHECK_EQ(sba_tl_item.a_source, 0, msg)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    // We only track D channel items (responses to reads or writes)
    if (channel != DataChannel) return;

    case (ral_name)
      "rv_dm_regs_reg_block": on_regs_access_d(item);
      "rv_dm_mem_reg_block":  on_mem_access_d(item);
      default: begin
        `uvm_fatal(get_full_name(), $sformatf("Unknown RAL name: %0s", ral_name))
      end
    endcase
  endtask

  // A function called by process_tl_access when we see a D-channel item which is a response on the
  // regs interface.
  local function void on_regs_access_d(tl_seq_item item);
    dv_base_reg_block    ral_model = cfg.ral_models["rv_dm_regs_reg_block"];
    rv_dm_regs_reg_block blk;
    uvm_reg_addr_t       csr_addr;
    uvm_reg              csr;
    bit                  is_write = item.is_write();

    if (!$cast(blk, ral_model)) `uvm_fatal(get_full_name(), "Wrong type for regs reg block")

    csr_addr = ral_model.get_word_aligned_addr(item.a_addr);
    csr      = ral_model.get_default_map().get_root_map().get_reg_by_offset(csr_addr);

    // If csr is null, the access must have been to an invalid address. We expect an error response
    // and d_data = '1. After checking that this has happened, return: the access should not have
    // had any other effect.
    if (csr == null) begin
      if (!item.d_error || ~&item.d_data) begin
        `uvm_error(get_full_name(),
                   $sformatf({"Access to non-existant register at address 0x%0h should have got ",
                              "a d_error response and d_data = '1. We actually got ",
                              "d_error=%0d; d_data=0x%0h."},
                             item.a_addr, item.d_error, item.d_data))
      end
      return;
    end

    if (csr == blk.alert_test) begin
    end else if (csr == blk.late_debug_enable) begin
    end else if (csr == blk.late_debug_enable_regwen) begin
    end else begin
      `uvm_error(get_full_name(), $sformatf("Unsupported register: %0s", csr.get_name()))
    end

    // We know that csr is not null. If this transaction is a read, check that our manual register
    // prediction is still up to date.
    if (!is_write && csr.get_mirrored_value() != item.d_data) begin
      `uvm_error(get_full_name(),
                 $sformatf({"CSR read mismatch for register %0s. ",
                            "Mirrored value is 0x%0h, but transaction saw 0x%0h."},
                           csr.get_name(),
                           csr.get_mirrored_value(),
                           item.d_data))
    end

    // Update prediction of register contents based on the access we just saw
    if (!item.d_error) begin
      if (!csr.predict(.value(is_write ? item.a_data : item.d_data),
                       .kind(is_write ? UVM_PREDICT_WRITE : UVM_PREDICT_READ))) begin
        `uvm_error(get_full_name(),
                   $sformatf("Failed to update prediction for %0s from an observed %0s.",
                             csr.get_name(),
                             is_write ? "write" : "read"))
      end
    end
  endfunction

  local function void on_mem_access_d(tl_seq_item item);
    dv_base_reg_block   ral_model = cfg.ral_models["rv_dm_mem_reg_block"];
    rv_dm_mem_reg_block blk;
    uvm_reg_addr_t      csr_addr;
    uvm_reg             csr;
    bit                 is_write = item.is_write();
    bit                 do_read_check = 1;

    if (!$cast(blk, ral_model)) `uvm_fatal(get_full_name(), "Wrong type for mem reg block")

    csr_addr = ral_model.get_word_aligned_addr(item.a_addr);
    csr      = ral_model.get_default_map().get_reg_by_offset(csr_addr);

    if (csr == null) begin
      // An unknown CSR for the mem reg block might be absolutely fine: it just means we're
      // accessing an address that lies above the top of our model of the debug memory. The
      // dm_mem implementation ignores that sort of access.
      //
      // Check that the response is not an error and a read has a d_data response of 0
      if (item.d_error || (!is_write && item.d_data != 0)) begin
        string problems[$];
        if (item.d_error) problems.push_back("Expected d_error=0 but it was 1.");
        if (!is_write && item.d_data != 0) begin
          problems.push_back($sformatf("Expected read d_data=0, but it was 0x%0h", item.d_data));
        end

        `uvm_error(get_full_name(),
                   $sformatf({"Unexpected response to %0s address 0x%0h in mem reg block. ",
                              "Problems: %0p. Item: (%0s)."},
                             is_write ? "write to" : "read from", csr_addr, problems,
                             item.sprint(uvm_default_line_printer)))
      end

      // Nothing else to do: we don't have any model that needs updating.
      return;
    end

    if (csr == blk.halted) begin
    end else if (csr == blk.going) begin
    end else if (csr == blk.resuming) begin
    end else if (csr == blk.exception) begin
    end else if (csr == blk.whereto) begin
      do_read_check = 0;
    end else if (csr inside {blk.abstractcmd}) begin
      // Disable the read check. We don't model the contents of abstractcmd registers.
      do_read_check = 0;
    end else if (csr inside {blk.program_buffer}) begin
      // RO registers. Write on DM progbuf registers and read data from these registers manually.
      do_read_check = 0;
    end else if (csr inside {blk.dataaddr}) begin
    end else if (csr inside {blk.flags}) begin
      // HW can update this value and we don't currently expect the scoreboard to keep track of what
      // it should contain in cfg.ral.
      do_read_check = 0;
    end else begin
      `uvm_error(get_full_name(), $sformatf("Unsupported register: %0s", csr.get_name()))
      return;
    end

    // If this is a read of a register whose value is predicted, we expect d_data to match the
    // mirrored value of the register.
    if (!is_write && do_read_check && (item.d_data != csr.get_mirrored_value())) begin
      `uvm_error(get_full_name(),
                 $sformatf({"Debug mem read mismatch at register %0s. ",
                            "Mirrored value is 0x%0h, but transaction saw 0x%0h."},
                           csr.get_name(),
                           csr.get_mirrored_value(),
                           item.d_data))
    end

    // Finally (if no error), update the register prediction with the value that was just read or
    // written
    if (!item.d_error) begin
      if (!csr.predict(.value(is_write ? item.a_data : item.d_data),
                       .kind(is_write ? UVM_PREDICT_WRITE : UVM_PREDICT_READ))) begin
        `uvm_error(get_full_name(),
                   $sformatf("Failed to update prediction for %0s from an observed %0s.",
                             csr.get_name(),
                             is_write ? "write" : "read"))
      end
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    sba_tl_access_q.delete();
    jtag_non_dmi_dtm_fifo.flush();
    jtag_non_sba_dmi_fifo.flush();
    tl_sba_a_chan_fifo.flush();
    tl_sba_d_chan_fifo.flush();
    selected_dtm_csr = cfg.m_jtag_agent_cfg.jtag_dtm_ral.idcode;
    cfg.jtag_dmi_ral.reset(kind);
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_sba_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_sba_d_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(jtag_item, jtag_non_dmi_dtm_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(jtag_dmi_item, jtag_non_sba_dmi_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(sba_access_item, sba_access_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(tl_seq_item, sba_tl_access_q)
  endfunction

  // Return true if we're using late debug enable, based on top-level inputs and register state.
  function logic using_late_debug_enable();
    prim_mubi_pkg::mubi8_t  pin_val = cfg.rv_dm_vif.otp_dis_rv_dm_late_debug;
    prim_mubi_pkg::mubi32_t reg_val = prim_mubi_pkg::mubi32_t'(`gmv(ral.late_debug_enable));
    return (prim_mubi_pkg::mubi8_test_true_strict(pin_val) ||
            prim_mubi_pkg::mubi32_test_true_strict(reg_val));
  endfunction

  // Return whether debug is supposed to be enabled, based on whether we're using late debug enable
  // and on top-level inputs.
  function logic is_debug_enabled();
    return lc_ctrl_pkg::lc_tx_test_true_strict(using_late_debug_enable ?
                                               cfg.rv_dm_vif.lc_hw_debug_en :
                                               cfg.rv_dm_vif.lc_dft_en);
  endfunction

  // This overrides a function in cip_base_scoreboard. The problem is that when debug is not
  // enabled, any TL request will respond with an error. This is what we expect, but the code in
  // cip_base_scoreboard fails because we're responding with an error to an access that would
  // otherwise be perfectly reasonable.
  protected function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    if (!cfg.tl_err_prediction) begin
      return item.d_error;
    end

    if ((ral_name == "rv_dm_mem_reg_block") &&
        (channel == DataChannel) &&
        !is_debug_enabled()) begin

      if (!item.d_error) begin
        `uvm_error(get_full_name(),
                   $sformatf({"Unexpected TL response. The transaction accesses ",
                              "rv_dm_mem_reg_block when debug is disabled, so ",
                              "the d_error response should be asserted. Item: %0s"},
                             item.sprint(uvm_default_line_printer)))
      end

      return 1'b1;
    end

    return super.predict_tl_err(item, channel, ral_name);
  endfunction

endclass
