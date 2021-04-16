// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_host_base_vseq extends cip_base_vseq #(
    .RAL_T               (spi_host_reg_block),
    .CFG_T               (spi_host_env_cfg),
    .COV_T               (spi_host_env_cov),
    .VIRTUAL_SEQUENCER_T (spi_host_virtual_sequencer)
  );
  `uvm_object_utils(spi_host_base_vseq)
  `uvm_object_new

  // local variables
  local dv_base_reg    base_reg;

  // random variables
  rand uint             tx_fifo_access_dly;
  rand uint             rx_fifo_access_dly;
  rand uint             clear_intr_dly;
  rand uint             num_runs;
  rand uint             num_wr_bytes;
  rand uint             num_rd_bytes;
  // SPI mode
  rand spi_mode_e spi_mode;
  // CSID register
  rand bit [31:0]       csid;
  // CONTROL register fields
  rand bit [7:0]        tx_watermark;
  rand bit [7:0]        rx_watermark;
  rand bit              passthru;
  // CONFIGOPTS register fields
  rand bit              sck_polarity[SPI_HOST_NUM_CS-1:0];
  rand bit              sck_phase[SPI_HOST_NUM_CS-1:0];
  rand bit              fullcyc[SPI_HOST_NUM_CS-1:0];
  rand bit [3:0]        csnlead[SPI_HOST_NUM_CS-1:0];
  rand bit [3:0]        csntrail[SPI_HOST_NUM_CS-1:0];
  rand bit [3:0]        csnidle[SPI_HOST_NUM_CS-1:0];
  rand bit [15:0]       clkdiv[SPI_HOST_NUM_CS-1:0];
  // COMMAND register fields
  rand spi_dir_e        direction;
  rand spi_mode_e       speed;
  rand bit              csaat;
  rand bit [8:0]        len;
  // FIFO: address used to access fifos
  rand bit [TL_AW:0]    fifo_baddr;
  rand bit [7:0]        data_q[$];

  semaphore             rxtx_atomic = new(1);

  // constraints for simulation loops
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.host_spi_min_trans : cfg.seq_cfg.host_spi_max_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.host_spi_min_runs : cfg.seq_cfg.host_spi_max_runs]};
  }
  constraint num_wr_bytes_c {
    num_wr_bytes inside {[cfg.seq_cfg.host_spi_min_num_wr_bytes :
                          cfg.seq_cfg.host_spi_max_num_wr_bytes]};
  }
  constraint num_rd_bytes_c {
    num_rd_bytes inside {[cfg.seq_cfg.host_spi_min_num_rd_bytes :
                          cfg.seq_cfg.host_spi_max_num_rd_bytes]};
  }
  // contraints for fifos
  constraint fifo_baddr_c {
    fifo_baddr inside {[SPI_HOST_FIFO_BASE : SPI_HOST_FIFO_END]};
  }

  constraint intr_c {
    clear_intr_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint control_reg_c {
    tx_watermark dist {
      [0:7]   :/ 1,
      [8:15]  :/ 2,
      [16:31] :/ 3,
      [32:cfg.seq_cfg.host_spi_max_txwm] :/ 1
    };
    rx_watermark dist {
      [0:7]   :/ 1,
      [8:15]  :/ 2,
      [16:31] :/ 3,
      [32:cfg.seq_cfg.host_spi_max_rxwm] :/ 1
    };
    rx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
    tx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint passthru_c {
    passthru dist {
      1'b0 :/ 1,
      1'b1 :/ 0   // TODO: currently disable passthru mode until specification is updated
    };
  }
  constraint csid_c {
    csid inside {[0 : SPI_HOST_NUM_CS-1]};
  }
  constraint configopts_regs_c {
    foreach (csnlead[i]) {
      csnlead[i] inside {[cfg.seq_cfg.host_spi_min_csn_hcyc : cfg.seq_cfg.host_spi_max_csn_hcyc]};
    }
    foreach (csntrail[i]) {
      csntrail[i] inside {[cfg.seq_cfg.host_spi_min_csn_hcyc : cfg.seq_cfg.host_spi_max_csn_hcyc]};
    }
    foreach (csnidle[i]) {
      csnidle[i] inside {[cfg.seq_cfg.host_spi_min_csn_hcyc : cfg.seq_cfg.host_spi_max_csn_hcyc]};
    }
    foreach (clkdiv[i]) {
      clkdiv[i] inside {[cfg.seq_cfg.host_spi_min_csn_hcyc : cfg.seq_cfg.host_spi_max_csn_hcyc]};
    }
  }
  constraint command_reg_c {
    direction dist {
      DummyCycles :/ 1,
      RxOnly      :/ 1,
      TxOnly      :/ 1,
      RxTx        :/ 1
    };
    speed dist {
      Single :/ 2,
      Dual   :/ 0,  // TODO
      Quad   :/ 0   // TODO
    };
    len inside {[cfg.seq_cfg.host_spi_min_len : cfg.seq_cfg.host_spi_max_len]};
  }

  virtual task body();
    initialization();

    `DV_CHECK_RANDOMIZE_FATAL(this)
    prog_spi_host_reg();
    activate_spi_host();
    `uvm_info(`gfn, "\n  start access fifos", UVM_DEBUG)
    write_tx_data();
  endtask : body

  virtual task bk_body();
    initialization();
    cfg.seq_cfg.host_spi_max_num_wr_bytes = 5;

    rxtx_atomic = new(1);
    for (int trans = 0; trans < num_trans; trans++) begin
      `uvm_info(`gfn, $sformatf("\n--> running tran. %0d/%0d", trans, num_trans), UVM_DEBUG)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      prog_spi_host_reg();
      activate_spi_host();
      `uvm_info(`gfn, "\n  start access fifos", UVM_DEBUG)
      fork
        begin
          //rxtx_atomic.get(1);
          write_tx_data();
          //rxtx_atomic.put(1);
        end
        begin
          //rxtx_atomic.get(1);
          //read_rx_data();
          //cfg.clk_rst_vif.wait_clks(10);
          //rxtx_atomic.put(1);
        end
      join
      wait_for_fifos_empty();
    end
  endtask : body

  virtual task pre_start();
    // sync monitor and scoreboard setting
    cfg.m_spi_agent_cfg.en_monitor_checks = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n  %s monitor and scoreboard",
        cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    num_runs.rand_mode(0);
    num_trans_c.constraint_mode(0);
    super.pre_start();
  endtask : pre_start

  virtual task initialization();
    `uvm_info(`gfn, "\n  initialization spi_host", UVM_LOW)
    wait(cfg.m_spi_agent_cfg.vif.rst_n);
    `uvm_info(`gfn, "\n  initialization, out of reset", UVM_LOW)
    spi_host_init();
    spi_agent_init();
    `uvm_info(`gfn, "\n  spi_host initialization is completed", UVM_LOW)
  endtask : initialization

  // setup basic spi_host features
  virtual task spi_host_init();
    // reset spit_host dut
    ral.control.sw_rst.set(1'b1);
    csr_update(ral.control);
    // make sure data completely drained from fifo then release reset
    wait_for_fifos_empty();
    ral.control.sw_rst.set(1'b0);
    csr_update(ral.control);
    // set passthru mode
    ral.control.passthru.set(passthru);
    csr_update(ral.control);
    // enable then clear interrupts
    csr_wr(.ptr(ral.intr_enable), .value({TL_DW{1'b1}}));
    process_interrupts();
  endtask : spi_host_init

  virtual task spi_agent_init();
    // spi_agent is configured in the Denive mode
    spi_device_seq m_device_seq;
    m_device_seq = spi_device_seq::type_id::create("m_device_seq");
    `uvm_info(`gfn, "\n  start spi_device sequence", UVM_DEBUG)
    fork
      m_device_seq.start(p_sequencer.spi_host_sequencer_h);
    join_none
  endtask : spi_agent_init

  virtual task activate_spi_host();
    // update spi_agent regs
    update_spi_agent_regs();
    // enable one of CS lines
    csr_wr(.ptr(ral.csid), .value(csid));
    // activate spi_host dut
    ral.control.spien.set(1'b1);
    csr_update(ral.control);
  endtask : activate_spi_host

  virtual task prog_spi_host_reg();
    prog_control_reg();
    prog_configopts_reg();
    prog_command_reg();
  endtask : prog_spi_host_regs

  virtual task prog_control_reg();
    ral.control.tx_watermark.set(tx_watermark);
    ral.control.rx_watermark.set(rx_watermark);
    csr_update(ral.control);
  endtask : prog_control_reg

  virtual task prog_configopts_reg();
    // CONFIGOPTS register fields
    base_reg = get_dv_base_reg_by_name("configopts");
    for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
      set_dv_base_reg_field_by_name(base_reg, "cpol",     sck_polarity[i], i);
      set_dv_base_reg_field_by_name(base_reg, "cpha",     sck_phase[i], i);
      set_dv_base_reg_field_by_name(base_reg, "fullcyc",  fullcyc[i], i);
      set_dv_base_reg_field_by_name(base_reg, "csnlead",  csnlead[i], i);
      set_dv_base_reg_field_by_name(base_reg, "csntrail", csntrail[i], i);
      set_dv_base_reg_field_by_name(base_reg, "csnidle",  csnidle[i], i);
      set_dv_base_reg_field_by_name(base_reg, "clkdiv",   clkdiv[i], i);
      csr_update(base_reg);
    end
  endtask : prog_configopts_reg

  virtual task prog_command_reg();
    // COMMAND register fields
    ral.command.set(direction);
    ral.command.set(speed);
    ral.command.set(csaat);
    ral.command.set(len);
    csr_update(ral.command);
  endtask : prog_command_reg

  virtual task write_tx_data();
    bit [TL_DW-1:0] tx_wdata;
    bit [TL_AW-1:0] fifo_waddr;

    //uvm_reg_map map = ral.get_default_map();
    //uvm_reg_addr_t reg_base_addr = map.get_base_addr();
    //`uvm_info(`gfn, $sformatf("\n base_vseq, base_addr: 0x%0x", int'(reg_base_addr)), UVM_LOW)

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fifo_baddr)
    fifo_waddr = ral.get_addr_from_offset(fifo_baddr);
    `uvm_info(`gfn, $sformatf("\n base_vseq, tx_byte_addr: 0x%0x", fifo_baddr), UVM_LOW)
    `uvm_info(`gfn, $sformatf("\n base_vseq, tx_word_addr: 0x%0x", fifo_waddr), UVM_LOW)
    `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(data_q,
                                          data_q.size() == num_wr_bytes;
                                         )
    swap_array_byte_order(data_q);

    // iterate through the data queue and pop off bytes to write to tx_fifo
    while (data_q.size() > 0) begin
      wait_for_fifos_available(TxFifo);
      tx_wdata = '0;
      for (int i = 0; i < TL_DBW; i++) begin
        if (data_q.size() > 0) begin
          tx_wdata[8*i +: 8] = data_q.pop_front();
        end
      end
      tx_wdata = 32'hcafecafe; //TODO: override random value for debug
      send_tl_access(.addr(fifo_waddr), .data(tx_wdata), .write(1'b1), .blocking(1'b0));
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
      cfg.clk_rst_vif.wait_clks(rx_fifo_access_dly);
    end
    // wait for all accesses to complete
    wait_no_outstanding_access();
    // read out status/intr_state CSRs to check
    check_status_and_clear_intrs();
  endtask : write_tx_data

  virtual task send_tl_access(bit [TL_AW-1:0] addr, bit [TL_DW-1:0] data, bit write,
                              bit [TL_DBW-1:0] mask = {TL_DBW{1'b1}},
                              bit blocking = $urandom_range(0, 1));
    tl_access(.addr(addr), .write(write), .data(data), .mask(mask), .blocking(blocking));
    `uvm_info(`gfn, $sformatf("\n base_vseq, %s to address 0x%0x, data: 0x%0x, mask %b, blk %b",
          write ? "write" : "read", data, addr, mask, blocking), UVM_LOW)
  endtask : send_tl_access

  virtual task read_rx_data();
    bit [TL_DW-1:0] rx_data;
    bit [TL_AW-1:0] fifo_waddr;
    uint cnt_rx_bytes = 0;

    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fifo_baddr)
    fifo_waddr = ral.get_addr_from_offset(fifo_baddr);
    `uvm_info(`gfn, $sformatf("\n  base_vseq, rx_byte_addr 0x%0x", fifo_baddr), UVM_LOW)
    `uvm_info(`gfn, $sformatf("\n  base_vseq, rx_word_addr 0x%0x", fifo_waddr), UVM_LOW)
    while (cnt_rx_bytes < num_rd_bytes) begin
      send_tl_access(.addr(fifo_waddr), .data(rx_data), .write(1'b0));
      cnt_rx_bytes += 4;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rx_fifo_access_dly)
      cfg.clk_rst_vif.wait_clks(rx_fifo_access_dly);
    end
    // wait for all accesses to complete
    wait_no_outstanding_access();
    // read out status/intr_state CSRs to check
    check_status_and_clear_intrs();
  endtask : read_rx_data

  // read interrupts and randomly clear interrupts if set
  virtual task process_interrupts();
    bit [TL_DW-1:0] intr_state, intr_clear;

    // read interrupt
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    // clear interrupt if it is set
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(intr_clear,
                                       foreach (intr_clear[i]) {
                                         intr_state[i] -> intr_clear[i] == 1;
                                       })
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(clear_intr_dly)
    cfg.clk_rst_vif.wait_clks(clear_intr_dly);
    csr_wr(.ptr(ral.intr_state), .value(intr_clear));
  endtask : process_interrupts

  // override apply_reset to handle core_reset domain
  virtual task apply_reset(string kind = "HARD");
    fork
      super.apply_reset(kind);
      begin
        if (kind == "HARD") begin
          cfg.clk_rst_core_vif.apply_reset();
        end
      end
    join
  endtask : apply_reset

  // override wait_for_reset to to handle core_reset domain
  virtual task wait_for_reset(string reset_kind = "HARD",
                              bit wait_for_assert = 1'b1,
                              bit wait_for_deassert = 1'b1);

    fork
      super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
      begin
        if (wait_for_assert) begin
          `uvm_info(`gfn, "waiting for core rst_n assertion...", UVM_MEDIUM)
          @(negedge cfg.clk_rst_core_vif.rst_n);
        end
        if (wait_for_deassert) begin
          `uvm_info(`gfn, "waiting for core rst_n de-assertion...", UVM_MEDIUM)
          @(posedge cfg.clk_rst_core_vif.rst_n);
        end
        `uvm_info(`gfn, "core wait_for_reset done", UVM_LOW)
      end
    join
  endtask : wait_for_reset

  // wait until fifos empty
  virtual task wait_for_fifos_empty(spi_host_fifo_e fifo = AllFifos);
    if (fifo == TxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.txempty), .exp_data(1'b1));
    end
    if (fifo == RxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
    end
  endtask : wait_for_fifos_empty

  // reads out the STATUS and INTR_STATE csrs so scb can check the status
  virtual task check_status_and_clear_intrs();
    bit [TL_DW-1:0] data;

    // read then clear interrupts
    csr_rd(.ptr(ral.intr_state), .value(data));
    csr_wr(.ptr(ral.intr_state), .value(data));
    // read status register
    csr_rd(.ptr(ral.status), .value(data));
  endtask : check_status_and_clear_intrs

  // wait until fifos has available entries to read/write
  virtual task wait_for_fifos_available(spi_host_fifo_e fifo = AllFifos);
    if (fifo == TxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0));
    end
    if (fifo == RxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.rxfull), .exp_data(1'b0));
    end
  endtask

  // update spi_agent registers
  virtual function void update_spi_agent_regs();
    for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
      cfg.m_spi_agent_cfg.sck_polarity[i] = sck_polarity[i];
      cfg.m_spi_agent_cfg.sck_phase[i]    = sck_phase[i];
      cfg.m_spi_agent_cfg.fullcyc[i]      = fullcyc[i];
      cfg.m_spi_agent_cfg.csnlead[i]      = csnlead[i];
    end
    cfg.m_spi_agent_cfg.csid              = csid;
    cfg.m_spi_agent_cfg.direction         = direction;
    cfg.m_spi_agent_cfg.spi_mode          = speed;
    cfg.m_spi_agent_cfg.csaat             = csaat;
    cfg.m_spi_agent_cfg.len               = len;
  endfunction : update_spi_agent_regs

  // set reg/mreg using name and index
  virtual function dv_base_reg get_dv_base_reg_by_name(string csr_name,
                                               int    csr_idx = -1);
    string  reg_name;
    uvm_reg reg_uvm;

    reg_name = (csr_idx == -1) ? csr_name : $sformatf("%s_%0d", csr_name, csr_idx);
    reg_uvm  = ral.get_reg_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_uvm, null, reg_name)
    `downcast(get_dv_base_reg_by_name, reg_uvm)
  endfunction

  // set field of reg/mreg using name and index, need to call csr_update after setting
  virtual function void set_dv_base_reg_field_by_name(dv_base_reg csr_reg,
                                              string      csr_field,
                                              uint        value,
                                              int         csr_idx = -1);
    uvm_reg_field reg_field;
    string reg_name;

    reg_name = (csr_idx == -1) ? csr_field : $sformatf("%s_%0d", csr_field, csr_idx);
    reg_field = csr_reg.get_field_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_field, null, reg_name)
    reg_field.set(value);
  endfunction

  virtual function void swap_array_byte_order(ref bit [7:0] data[$]);
    if (SPI_HOST_BYTEORDER) begin
      bit [7:0] data_arr[];
      data_arr = data;
      `uvm_info(`gfn, $sformatf("\n base_vseq, data_q_baseline: %0p", data), UVM_LOW)
      dv_utils_pkg::endian_swap_byte_arr(data_arr);
      data = data_arr;
      `uvm_info(`gfn, $sformatf("\n base_vseq, data_q_swapped:  %0p", data), UVM_LOW)
    end
  endfunction : swap_array_byte_order

  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit en_phase_align_reset = 1'b0);
    if (en_phase_align_reset) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.clk_rst_core_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset

endclass : spi_host_base_vseq
