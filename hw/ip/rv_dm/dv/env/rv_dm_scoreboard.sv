// Copyright lowRISC contributors.
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
        // Unmapped regions of the JTAG DTM register space should exhibit RAZ/WI behavior.
        `DV_CHECK_EQ(item.dout, 0)
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
          `DV_CHECK_EQ(item.dout, selected_dtm_csr.get_mirrored_value())
          void'(selected_dtm_csr.predict(.value(item.dr), .kind(UVM_PREDICT_WRITE)));
        end
        "dtmcs": begin
          `DV_CHECK_EQ(item.dout, selected_dtm_csr.get_mirrored_value())
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
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (item.req_op == DmiOpRead) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.rdata,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.rdata), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // Receive and process incoming predicted complete SBA accesses.
  virtual task process_sba_access_fifo();
    sba_access_item item;
    forever begin
      sba_access_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA access item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      if (sba_tl_access_q.size() > 0) begin
        compare_sba_access(item, sba_tl_access_q.pop_front());
      end else begin
        `uvm_error(`gfn, $sformatf({"Received predicted SBA access but no transaction was seen on ",
                                    "the SBA TL host interface: %0s"},
                                   item.sprint(uvm_default_line_printer)))
      end
    end
  endtask

  virtual task process_tl_sba_a_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_sba_a_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA TL a_chan item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      process_tl_sba_access(item, AddrChannel);
    end
  endtask

  virtual task process_tl_sba_d_chan_fifo();
    tl_seq_item item;
    forever begin
      tl_sba_d_chan_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA TL d_chan item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      sba_tl_access_q.push_back(item);
      // check tl packet integrity
      // TODO: deal with item not being ok.
      void'(item.is_ok(.throw_error(0)));
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
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (ral_name)
      "rv_dm_regs_reg_block": begin
        case (csr.get_name())
          "alert_test": begin
          end
          default: `uvm_fatal(`gfn, $sformatf("Unknown regs CSR: %0s", csr.get_name()))
        endcase
      end
      "rv_dm_mem_reg_block": begin
        case (1)
          (!uvm_re_match("halted", csr.get_name())): begin
          end
          (!uvm_re_match("halted", csr.get_name())): begin
          end
          (!uvm_re_match("going", csr.get_name())): begin
          end
          (!uvm_re_match("resuming", csr.get_name())): begin
          end
          (!uvm_re_match("exception", csr.get_name())): begin
          end
          (!uvm_re_match("whereto", csr.get_name())): begin
          end
          (!uvm_re_match("abstractcmd_*", csr.get_name())): begin
          end
          (!uvm_re_match("program_buffer_*", csr.get_name())): begin
          end
          (!uvm_re_match("dataaddr_*", csr.get_name())): begin
          end
          (!uvm_re_match("flags_*", csr.get_name())): begin
          end
          default: `uvm_fatal(`gfn, $sformatf("Unknown debug mem CSR: %0s", csr.get_name()))
        endcase
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid RAL: %0s", ral_name))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    sba_tl_access_q.delete();
    jtag_non_dmi_dtm_fifo.flush();
    jtag_non_sba_dmi_fifo.flush();
    tl_sba_a_chan_fifo.flush();
    tl_sba_d_chan_fifo.flush();
    selected_dtm_csr = cfg.m_jtag_agent_cfg.jtag_dtm_ral.default_map.get_reg_by_offset(0);
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

endclass
