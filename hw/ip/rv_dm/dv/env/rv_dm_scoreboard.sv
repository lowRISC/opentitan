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
  uvm_tlm_analysis_fifo #(jtag_dmi_item)jtag_non_sba_dmi_fifo;

  uvm_tlm_analysis_fifo #(sba_access_item) sba_access_fifo;

  // Items from sba_access_fifo come in much later because the inferred transactions are marked
  // completed only when the JTAG interface actually reads the SBCS register. So we capture and hold
  // the TL accesses over SBA and compare against SBA access whenever they arrive.
  tl_seq_item sba_tl_access_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_non_sba_dmi_fifo = new("jtag_non_sba_dmi_fifo", this);
    sba_access_fifo = new("sba_access_fifo", this);
    tl_sba_a_chan_fifo = new("tl_sba_a_chan_fifo", this);
    tl_sba_d_chan_fifo = new("tl_sba_d_chan_fifo", this);
    // TODO: remove once support alert checking
    do_alert_check = 0;
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_jtag_non_sba_dmi_fifo();
      process_sba_access_fifo();
      process_tl_sba_a_chan_fifo();
      process_tl_sba_d_chan_fifo();
    join_none
  endtask

  // Receive and process incoming completed JTAG DMI accesses to non-SBA registers.
  virtual task process_jtag_non_sba_dmi_fifo();
    jtag_dmi_item item;
    forever begin
      jtag_non_sba_dmi_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received jtag non-SBA DMI item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
    end
  endtask

  // Receive and process incoming predicted complete SBA accesses.
  virtual task process_sba_access_fifo();
    sba_access_item item;
    forever begin
      sba_access_fifo.get(item);
      `uvm_info(`gfn, $sformatf("Received SBA access item:\n%0s",
                                item.sprint(uvm_default_line_printer)), UVM_HIGH)
      compare_sba_access(item, sba_tl_access_q.pop_front());
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
      `DV_CHECK_EQ(sba_item.rdata, data, msg)
      // TLUL adapter host does full word reads with all byte lanes enabled.
      `DV_CHECK_EQ(sba_tl_item.a_mask, '1, msg)
    end else begin
      logic [BUS_DW-1:0] word_mask;
      logic [BUS_DBW-1:0] byte_mask;

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
      data = (sba_item.wdata & word_mask) << shift;
      `DV_CHECK_EQ(data, sba_tl_item.a_data, msg)
      byte_mask <<= sba_item.addr[BUS_SZW-1:0];
      `DV_CHECK_EQ(byte_mask, sba_tl_item.a_mask, msg)
    end
    // The d_chan may have intg errors and response error (d_error = 1). None of those reflect back
    // in the SBA interface.
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
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
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
    jtag_non_sba_dmi_fifo.flush();
    tl_sba_a_chan_fifo.flush();
    tl_sba_d_chan_fifo.flush();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_sba_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, tl_sba_d_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(jtag_dmi_item, jtag_non_sba_dmi_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(sba_access_item, sba_access_fifo)
    `DV_EOT_PRINT_Q_CONTENTS(tl_seq_item, sba_tl_access_q)
  endfunction

endclass
