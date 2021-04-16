// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_scoreboard extends cip_base_scoreboard #(
    .CFG_T(spi_host_env_cfg),
    .RAL_T(spi_host_reg_block),
    .COV_T(spi_host_env_cov)
  );
  `uvm_component_utils(spi_host_scoreboard)

  // TODO: WiP

  virtual spi_if  spi_vif;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(spi_item) host_spi_data_fifo;
  uvm_tlm_analysis_fifo #(spi_item) device_spi_data_fifo;

  // local variables
  // tx/rx fifo, size is 2 words to hold incoming packets pending comparison
  local bit [31:0] tx_word_q[$];
  local bit [31:0] rx_word_q[$];
  // interrupt bit vector
  local bit [NumSpiHostIntr-1:0] intr_exp;
  
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_spi_data_fifo   = new("host_spi_data_fifo", this);
    device_spi_data_fifo = new("device_spi_data_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_host_spi_fifo();
    join_none
  endtask

  virtual task process_host_spi_fifo();
    spi_item hst_item;
    forever begin
      host_spi_data_fifo.get(hst_item);
      `uvm_info(`gfn, $sformatf("received spi_host item:\n%0s", hst_item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_device_spi_fifo();
    spi_item dev_item;
    forever begin
      device_spi_data_fifo.get(dev_item);
      `uvm_info(`gfn, $sformatf("received spi_device item:\n%0s", dev_item.sprint()), UVM_HIGH)
    end
  endtask : process_device_spi_fifo
  
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit fifos_access;

    string csr_name = "";
    bit do_read_check = 1'b1;
    bit write = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] csr_addr_mask = ral.get_addr_mask();

    bit addr_phase_read  = (!write && channel == AddrChannel);
    bit addr_phase_write = (write && channel  == AddrChannel);
    bit data_phase_read  = (!write && channel == DataChannel);
    bit data_phase_write = (write && channel  == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      csr_name = csr.get_name();

      // if incoming access is a write to a valid csr, then make updates right away
      if (addr_phase_write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end else if ((csr_addr & csr_addr_mask) inside {[SPI_HOST_FIFO_BASE:SPI_HOST_FIFO_END]}) begin
      fifos_access = 1;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
      // add individual case item for each csr
      "intr_state": begin
        // TODO
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // TODO
      end
      "intr_test": begin
        // TODO
      end
      "control": begin
        // TODO
      end
      "configopts": begin
        // TODO
      end
      "command": begin
        // TODO
      end
      "txdata": begin
        // TODO
      end
      "status": begin
        // TODO
      end
      "csid": begin
        // TODO
      end
      "error_enable": begin
        // TODO
      end
    endcase

    if (fifos_access) begin
      if (addr_phase_write) begin
        // TODO: Access TX_FIFO
        // indicate that the txfifo access is now over
        fifos_access = 0;
      end
      if (data_phase_read) begin
        // TODO: Access RX_FIFO
        // indicate that the rxfifo access is now over
        fifos_access = 0;
      end
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
//    if (data_phase_read) begin
//      if (do_read_check) begin
//        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
//                     $sformatf("reg name: %0s", csr.get_full_name()))
//      end
//      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
//    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass : spi_host_scoreboard
