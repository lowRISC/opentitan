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


  // spi registers
  rand spi_host_command_t    spi_host_command_reg;
  rand spi_host_ctrl_t       spi_host_ctrl_reg;
  rand spi_host_configopts_t spi_config_regs;
  rand spi_host_event_enable_t event_enable;
  rand spi_host_intr_enable_t intr_enable;
  rand spi_host_error_enable_t error_enable;
  // random variables
  rand uint                  num_runs;
  rand uint                  tx_fifo_access_dly;
  rand uint                  rx_fifo_access_dly;
  rand uint                  clear_intr_dly;
  // transaction item contains a full spi transaction
  spi_transaction_item       transaction;

  // re-active sequence
  spi_device_cmd_rsp_seq m_spi_device_seq[SPI_HOST_NUM_CS];

  // constraints for simulation loops
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.host_spi_min_trans : cfg.seq_cfg.host_spi_max_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.host_spi_min_runs : cfg.seq_cfg.host_spi_max_runs]};
  }


  constraint intr_dly_c {
    clear_intr_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }
  constraint fifo_dly_c {
    rx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
    tx_fifo_access_dly inside {[cfg.seq_cfg.host_spi_min_dly : cfg.seq_cfg.host_spi_max_dly]};
  }

  constraint spi_config_regs_c {
      // configopts regs
      foreach (spi_config_regs.cpol[i]) {
        spi_config_regs.cpol[i] dist {
          1'b0 :/ 1,
          1'b1 :/ 1
        };
      }
      foreach (spi_config_regs.cpha[i]) {
        spi_config_regs.cpha[i] dist {
          1'b0 :/ 1,
          1'b1 :/ 1
        };
      }
      foreach (spi_config_regs.csnlead[i]) {
        spi_config_regs.csnlead[i] inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                          cfg.seq_cfg.host_spi_max_csn_latency]};
      }
      foreach (spi_config_regs.csntrail[i]) {
        spi_config_regs.csntrail[i] inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                           cfg.seq_cfg.host_spi_max_csn_latency]};
      }
      foreach (spi_config_regs.csnidle[i]) {
        spi_config_regs.csnidle[i] inside {[cfg.seq_cfg.host_spi_min_csn_latency :
                                          cfg.seq_cfg.host_spi_max_csn_latency]};
      }
      foreach (spi_config_regs.clkdiv[i]) {
        spi_config_regs.clkdiv[i] inside {[cfg.seq_cfg.host_spi_min_clkdiv :
                                         cfg.seq_cfg.host_spi_max_clkdiv]};
      }
  }

  constraint spi_ctrl_regs_c {
    // csid reg
    spi_host_ctrl_reg.csid inside {[0 : SPI_HOST_NUM_CS-1]};
    // control reg
    spi_host_ctrl_reg.tx_watermark dist {
      [1:7]   :/ 1,
      [8:15]  :/ 1,
      [16:31] :/ 1,
      [32:cfg.seq_cfg.host_spi_max_txwm] :/ 1
      };
    spi_host_ctrl_reg.rx_watermark dist {
      [1:7]   :/ 1,
      [8:15]  :/ 1,
      [16:31] :/ 1,
      [32:cfg.seq_cfg.host_spi_max_rxwm] :/ 1
      };
  }


  virtual task pre_start();
    // sync monitor and scoreboard setting
    cfg.m_spi_agent_cfg.en_monitor_checks = cfg.en_scb;
    `uvm_info(`gfn, $sformatf("\n  base_vseq, %s monitor and scoreboard",
                              cfg.en_scb ? "enable" : "disable"), UVM_DEBUG)
    num_runs.rand_mode(0);
    num_trans_c.constraint_mode(0);
    transaction = new();
    super.pre_start();
  endtask : pre_start

  virtual task start_reactive_seq();
    // start device seq's
    fork
      for( int i = 0; i < SPI_HOST_NUM_CS; i++) begin
        m_spi_device_seq[i] = spi_device_cmd_rsp_seq::type_id::create($sformatf("spi_host[%0d]",i));
        m_spi_device_seq[i].start(p_sequencer.spi_sequencer_h);
      end
    join
  endtask // start_reactive_seq

  // Call this function to cleanup the above started reactive-sequences, such as if we
  // exit early, or are running sequences back-to-back.
  virtual task cleanup_reactive_seq();
    p_sequencer.spi_sequencer_h.stop_sequences();
    if (cfg.m_spi_agent_cfg.has_req_fifo) p_sequencer.spi_sequencer_h.req_analysis_fifo.flush();
    if (cfg.m_spi_agent_cfg.has_rsp_fifo) p_sequencer.spi_sequencer_h.rsp_analysis_fifo.flush();
  endtask // cleanup_reactive_seq

  task post_start();
    super.post_start();
    cleanup_reactive_seq();
  endtask

  function void transaction_init();
    transaction = new();

    transaction.read_weight     = cfg.seq_cfg.read_pct;
    transaction.write_weight    = cfg.seq_cfg.write_pct;
    transaction.std_en          = cfg.seq_cfg.std_en;
    transaction.dual_en         = cfg.seq_cfg.dual_en;
    transaction.quad_en         = cfg.seq_cfg.quad_en;
    transaction.rx_only_weight  = cfg.seq_cfg.rx_only_weight;
    transaction.tx_only_weight  = cfg.seq_cfg.tx_only_weight;
    transaction.spi_len_min     = cfg.seq_cfg.host_spi_min_len;
    transaction.spi_len_max     = cfg.seq_cfg.host_spi_max_len;
    transaction.spi_num_seg_min = cfg.seq_cfg.host_spi_min_num_seg;
    transaction.spi_num_seg_max = cfg.seq_cfg.host_spi_max_num_seg;
    transaction.num_cmd_bytes   = cfg.num_cmd_bytes;
  endfunction



  // setup basic spi_host features
  virtual task spi_host_init();
    bit [TL_DW-1:0] intr_state;

    wait(cfg.m_spi_agent_cfg.vif.rst_n);
    // program sw_reset for spi_host dut
    program_spi_host_sw_reset();
    // enable then clear interrupt
    csr_wr(.ptr(ral.intr_enable), .value({TL_DW{1'b1}}));
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    csr_wr(.ptr(ral.intr_state), .value(intr_state));
  endtask : spi_host_init

  virtual task program_spi_host_sw_reset(int drain_cycles = SPI_HOST_RX_DEPTH);
    ral.control.sw_rst.set(1'b1);
    csr_update(ral.control);
    // make sure data completely drained from fifo then release reset
    wait_for_fifos_empty(AllFifos);
    ral.control.sw_rst.set(1'b0);
    csr_update(ral.control);
  endtask : program_spi_host_sw_reset

  virtual task program_spi_host_regs();
    // IMPORTANT: configopt regs must be programmed before command reg
    program_configopt_regs();
    program_control_reg();
    program_csid_reg();
    csr_wr(.ptr(ral.error_enable), .value(error_enable));
    csr_wr(.ptr(ral.event_enable), .value(event_enable));
    csr_wr(.ptr(ral.intr_enable), .value(intr_enable));
    // TODO
    update_spi_agent_regs();
  endtask : program_spi_host_regs

  virtual task program_csid_reg();
    // enable one of CS lines
    csr_wr(.ptr(ral.csid), .value(spi_host_ctrl_reg.csid));
  endtask : program_csid_reg

  virtual task program_control_reg();
    ral.control.tx_watermark.set(spi_host_ctrl_reg.tx_watermark);
    ral.control.rx_watermark.set(spi_host_ctrl_reg.rx_watermark);
    // activate spi_host dut
    ral.control.spien.set(1'b1);
    ral.control.output_en.set(1'b1);
    csr_update(ral.control);
  endtask : program_control_reg


  // CONFIGOPTS register fields
  virtual task program_configopt_regs();
    for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
      ral.configopts[i].cpol.set(spi_config_regs.cpol[0]);
      ral.configopts[i].cpha.set(spi_config_regs.cpha[0]);
      ral.configopts[i].fullcyc.set(spi_config_regs.fullcyc[0]);
      ral.configopts[i].csnlead.set(spi_config_regs.csnlead[0]);
      ral.configopts[i].csntrail.set(spi_config_regs.csntrail[0]);
      ral.configopts[i].csnidle.set(spi_config_regs.csnidle[0]);
      ral.configopts[i].clkdiv.set(spi_config_regs.clkdiv[0]);
      csr_wr(ral.configopts[i], .value(ral.configopts[i].get()));
    end
  endtask : program_configopt_regs


  virtual task program_command_reg(spi_host_command_t cmd);
    // COMMAND register fields
    ral.command.direction.set(cmd.direction);
    ral.command.speed.set(cmd.mode);
    ral.command.csaat.set(cmd.csaat);
    ral.command.len.set(cmd.len);
    // ensure a write - even if values didn't change
    csr_wr(ral.command, .value(ral.command.get()));
  endtask : program_command_reg


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
      super.apply_reset(kind);
  endtask


  // wait until fifos empty
  virtual task wait_for_fifos_empty(spi_host_fifo_e fifo = AllFifos);
    if (fifo == TxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.txempty), .exp_data(1'b1));
    end
    if (fifo == RxFifo || TxFifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b1));
    end
  endtask : wait_for_fifos_empty


  // wait dut ready for new command
  virtual task wait_ready_for_command(bit backdoor = 1'b0);
    csr_spinwait(.ptr(ral.status.ready), .exp_data(1'b1), .backdoor(backdoor));
  endtask : wait_ready_for_command


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
    if (fifo == TxFifo || fifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.txfull), .exp_data(1'b0));
    end
    if (fifo == RxFifo || fifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.rxempty), .exp_data(1'b0));
    end
  endtask


  // wait until no rx/tx_trans stalled
  virtual task wait_for_trans_complete(spi_host_fifo_e fifo = AllFifos);
    if (fifo == TxFifo || fifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.txstall), .exp_data(1'b0));
      `uvm_info(`gfn, $sformatf("\n  base_vseq: tx_trans is not stalled"), UVM_DEBUG)
    end
    if (fifo == RxFifo || fifo == AllFifos) begin
      csr_spinwait(.ptr(ral.status.rxstall), .exp_data(1'b0));
      `uvm_info(`gfn, $sformatf("\n  base_vseq: rx_trans is not stalled"), UVM_DEBUG)
    end
  endtask : wait_for_trans_complete


  // update spi_agent registers
  virtual function void update_spi_agent_regs();
    for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
      cfg.m_spi_agent_cfg.sck_polarity[i] = spi_config_regs.cpol[i];
      cfg.m_spi_agent_cfg.sck_phase[i]    = spi_config_regs.cpha[i];
      cfg.m_spi_agent_cfg.full_cyc[i]      = spi_config_regs.fullcyc[i];
      cfg.m_spi_agent_cfg.csn_lead[i]      = spi_config_regs.csnlead[i];
    end
    cfg.m_spi_agent_cfg.csid              = spi_host_ctrl_reg.csid;
    cfg.m_spi_agent_cfg.spi_mode          = spi_host_command_reg.mode;
    cfg.m_spi_agent_cfg.decode_commands   = 1'b1;
    print_spi_host_regs();
  endfunction : update_spi_agent_regs


  virtual function bit [TL_AW-1:0] get_aligned_tl_addr(spi_host_fifo_e fifo);
    bit [TL_AW-1:0] fifo_addr;
    if (fifo == TxFifo) begin
      fifo_addr = SPI_HOST_TXDATA_OFFSET;
    end else if (fifo == RxFifo) begin
      fifo_addr = SPI_HOST_RXDATA_OFFSET;
    end
    return fifo_addr;
  endfunction : get_aligned_tl_addr


  // print the content of spi_host_regs[channel]
  virtual function void print_spi_host_regs(uint en_print = 1);
    if (en_print) begin
      string str = "";

      str = {str, "\n  base_vseq, values programed to the dut registers:"};
      str = {str, $sformatf("\n    csid         %0d", spi_host_ctrl_reg.csid)};
      str = {str, $sformatf("\n    tx_watermark         %0b", spi_host_ctrl_reg.tx_watermark)};
      str = {str, $sformatf("\n    rx_watermark         %0b", spi_host_ctrl_reg.rx_watermark)};
      str = {str, $sformatf("\n    Mode        %s",  spi_host_command_reg.mode.name())};
      str = {str, $sformatf("\n    direction    %s",  spi_host_command_reg.direction.name())};
      str = {str, $sformatf("\n    csaat        %b",  spi_host_command_reg.csaat)};
      str = {str, $sformatf("\n    len          %0d", spi_host_command_reg.len)};
      for (int i = 0; i < SPI_HOST_NUM_CS; i++) begin
        str = {str, $sformatf("\n    config[%0d]", i)};
        str = {str, $sformatf("\n      cpol       %b", spi_config_regs.cpol[i])};
        str = {str, $sformatf("\n      cpha       %b", spi_config_regs.cpha[i])};
        str = {str, $sformatf("\n      fullcyc    %b", spi_config_regs.fullcyc[i])};
        str = {str, $sformatf("\n      csnlead    %0d", spi_config_regs.csnlead[i])};
        str = {str, $sformatf("\n      csntrail   %0d", spi_config_regs.csntrail[i])};
        str = {str, $sformatf("\n      csnidle    %0d", spi_config_regs.csnidle[i])};
        str = {str, $sformatf("\n      clkdiv     %0d\n", spi_config_regs.clkdiv[i])};
      end
      `uvm_info(`gfn, str, UVM_LOW)
    end
  endfunction : print_spi_host_regs


  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit en_phase_align_reset = 1'b0);
    if (en_phase_align_reset) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset


  // send tl read/write request to a memory address (window type)
  virtual task send_tl_access(bit [TL_AW-1:0]  addr,
                              bit [TL_DW-1:0]  data,
                              bit              write,
                              bit [TL_DBW-1:0] mask = {TL_DBW{1'b1}},
                              bit              blocking = $urandom_range(0, 1));
    tl_access(.addr(addr), .write(write), .data(data), .mask(mask), .blocking(blocking));
    `uvm_info(`gfn, $sformatf("\n  rxtx_vseq, TL_%s to addr 0x%0x, data: 0x%8x, blk %b, mask %b",
        write ? "WRITE" : "READ", addr, data, blocking, mask), UVM_HIGH)
  endtask : send_tl_access

  virtual task access_data_fifo(ref bit [7:0] data_q[$], input spi_host_fifo_e fifo,
                                    bit fifo_avail_chk = 1'b1);
    bit [TL_DBW-1:0][7:0]   data          = '0;
    int                     cnt           =  0;
    bit [TL_DBW-1:0]        mask          = '0;
    bit                     wr_en         = 1;
    bit [TL_AW-1:0]         align_addr;
    // check free space in fifo
    if (fifo_avail_chk) wait_for_fifos_available(fifo);
    //TODO add interrupt handling if FIFO overflow

    align_addr = get_aligned_tl_addr(fifo);
    wr_en      = (fifo != RxFifo);
    if (wr_en) begin
      while (data_q.size() > 0) begin
        data[cnt] = data_q.pop_front();
        mask[cnt] = 1'b1;
        if (cnt == 3) begin
          send_tl_access(.addr(align_addr), .data(data), .write(wr_en),
                         .mask(mask), .blocking(1'b1));
          cnt  = 0;
          data = '0;
          mask = '0;
        end else begin
          cnt++;
        end
      end
      // add runts
      if (cnt != 0) begin
        send_tl_access(.addr(align_addr), .data(data), .write(wr_en), .mask(mask), .blocking(1'b1));
      end
    end else begin
      send_tl_access(.addr(align_addr), .data(data), .write(wr_en), .mask(mask), .blocking(1'b1));
      data_q = {<<8{data}};
    end
  endtask
endclass : spi_host_base_vseq
