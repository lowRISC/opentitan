// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Covergoups that are dependent on run-time parameters that may be available
 * only in build_phase can be defined here
 * Covergroups may also be wrapped inside helper classes if needed.
 */
//TODO we only support SPI_HOST_NUM_CS=1

class spi_host_env_cov extends cip_base_env_cov #(.CFG_T(spi_host_env_cfg));
  `uvm_component_utils(spi_host_env_cov)

  // Sample this covergroup upon writes to the TXFIFO register window.
  covergroup tx_fifo_overflow_cg with function sample(spi_host_status_t spi_status_reg);
    tx_fifo_overflow_txfull_cp : coverpoint spi_status_reg.txfull {
      // Trying to write to TXFIFO while status.txfull = 1'b1 indicates an overflow event.
      bins try_overflow = {1};
    }
  endgroup : tx_fifo_overflow_cg

  // Sample this covergroup upon reads from the RXFIFO register window.
  covergroup rx_fifo_underflow_cg with function sample(spi_host_status_t spi_status_reg);
    rx_fifo_underflow_rxempty_cp : coverpoint spi_status_reg.rxempty {
      // Trying to read from RXFIFO while status.rxempty = 1'b1 indicates an underflow event.
      bins try_underflow = {1};
    }
  endgroup : rx_fifo_underflow_cg

  covergroup config_opts_cg with function sample(spi_host_configopts_t spi_configopts);
    cpol_cp : coverpoint spi_configopts.cpol[SPI_HOST_NUM_CS-1]{ bins cpol[] = {[0:1]}; }
    cpha_cp : coverpoint spi_configopts.cpha[SPI_HOST_NUM_CS-1]{ bins cpha[] = {[0:1]}; }
    fullcyc_cp : coverpoint spi_configopts.fullcyc[SPI_HOST_NUM_CS-1]{
    bins fullcyc[] = {[0:1]};
    }
    csnlead_cp : coverpoint spi_configopts.csnlead[SPI_HOST_NUM_CS-1]{
    bins csnlead[] = {[0:15]};
    }
    csnidle_cp : coverpoint spi_configopts.csnidle[SPI_HOST_NUM_CS-1]{
    bins csnidle[] = {[0:15]};
    }
    clkdiv_cp : coverpoint spi_configopts.clkdiv[SPI_HOST_NUM_CS-1]{
    // (Period) T_sck = 2*(clkdiv+1)*T_core
    // If clkdiv == 16'h00fe, F_sck = F_core / 254
    bins clk_divl = {0};
    bins clk_divm[30] = {[16'h1:16'h00fe]};
    }
    csntrail_cp : coverpoint spi_configopts.csntrail[SPI_HOST_NUM_CS-1]{
      bins csntrail[] = {[0:15]};
    }
    cpol_cpha_cross :  cross cpol_cp, cpha_cp;
    csnlead_csnidle_csntrail_cross: cross csnlead_cp, csnidle_cp, csntrail_cp{
      bins csncross = binsof(csnlead_cp) && binsof(csnidle_cp) && binsof(csntrail_cp);
    }
  endgroup

  covergroup unaligned_data_cg with function sample(bit [3:0] mask);
    unaligned_data_cp: coverpoint mask{ bins mask = {[0:15]}; }
  endgroup

  covergroup duplex_cg with function sample(spi_dir_e  direction);
    duplex_cp : coverpoint direction{ ignore_bins unsupported_dir = {None}; }
  endgroup

  covergroup control_cg with function sample(spi_host_ctrl_t spi_ctrl_reg, bit active);
    tx_watermark_cp : coverpoint spi_ctrl_reg.tx_watermark{
      bins lower[10] = {[1:30]};
      bins upper[20] = {[31:SPI_HOST_TX_DEPTH]};
    }
    rx_watermark_cp : coverpoint spi_ctrl_reg.rx_watermark{
      bins lower[10] = {[1:30]};
      bins upper[20] = {[31:SPI_HOST_RX_DEPTH]};
    }
    spien_cp : coverpoint spi_ctrl_reg.spien { bins spien = {1}; }
    output_en_cp : coverpoint spi_ctrl_reg.output_en { bins output_en = {1}; }
    sw_rst_cp : coverpoint spi_ctrl_reg.sw_rst { bins sw_rst = {1}; }
    sw_rst_active_cross : cross sw_rst_cp, active;
  endgroup

  covergroup status_cg with function sample(spi_host_status_t spi_status_reg);
    ready_cp : coverpoint spi_status_reg.ready;
    active_cp : coverpoint spi_status_reg.active;
    txfull_cp : coverpoint spi_status_reg.txfull;
    txempty_cp : coverpoint spi_status_reg.txempty;
    txstall_cp : coverpoint spi_status_reg.txstall;
    tx_wm_cp : coverpoint spi_status_reg.tx_wm;
    rxfull_cp : coverpoint spi_status_reg.rxfull;
    rxempty_cp : coverpoint spi_status_reg.rxempty;
    rxstall_cp : coverpoint spi_status_reg.rxstall;
    byteorder_cp : coverpoint spi_status_reg.byteorder;
    rx_wm_cp : coverpoint spi_status_reg.rx_wm;
    cmd_qd_cp : coverpoint spi_status_reg.cmd_qd;
    rx_qd_cp : coverpoint spi_status_reg.rx_qd;
    tx_qd_cp : coverpoint spi_status_reg.tx_qd;
  endgroup

  covergroup csid_cg with function sample(spi_host_ctrl_t spi_ctrl_reg);
    csid_cp : coverpoint spi_ctrl_reg.csid {
      bins csids = {[0:SPI_HOST_NUM_CS-1]};
    }
  endgroup

  covergroup command_cg with function sample(spi_host_command_t spi_cmd_reg);
    direction_cp : coverpoint spi_cmd_reg.direction;
    mode_cp : coverpoint spi_cmd_reg.mode {
      ignore_bins unsupported_mode = {RsvdSpd};
      }
    csaat_cp : coverpoint spi_cmd_reg.csaat;
    len_cp : coverpoint spi_cmd_reg.len{
      bins lenl[5] = {[1:3]};
      bins lenh[10] = {[4:$]};
      }
    direction_mode_cross: cross  direction_cp, mode_cp;
    csaat_mode_cross: cross csaat_cp, mode_cp;
  endgroup

  covergroup error_en_cg with function sample(spi_host_error_enable_t spi_error_enable_reg);
    ere_csidinval_cp : coverpoint spi_error_enable_reg.csidinval;
    ere_cmdinval_cp : coverpoint spi_error_enable_reg.cmdinval;
    ere_underflow_cp : coverpoint spi_error_enable_reg.underflow;
    ere_overflow_cp : coverpoint spi_error_enable_reg.overflow;
    ere_cmdbusy_cp : coverpoint spi_error_enable_reg.cmdbusy;
  endgroup

  covergroup error_status_cg with function sample(spi_host_error_status_t spi_error_status_reg,
                                                  spi_host_error_enable_t spi_error_enable_reg);
    es_accessinval_cp : coverpoint spi_error_status_reg.accessinval;
    es_csidinval_cp : coverpoint spi_error_status_reg.csidinval;
    es_cmdinval_cp : coverpoint spi_error_status_reg.cmdinval;
    es_underflow_cp : coverpoint spi_error_status_reg.underflow;
    es_overflow_cp : coverpoint spi_error_status_reg.overflow;
    es_cmdbusy_cp : coverpoint spi_error_status_reg.cmdbusy;
    ere_csidinval_cp : coverpoint spi_error_enable_reg.csidinval;
    ere_cmdinval_cp : coverpoint spi_error_enable_reg.cmdinval;
    ere_underflow_cp : coverpoint spi_error_enable_reg.underflow;
    ere_overflow_cp : coverpoint spi_error_enable_reg.overflow;
    ere_cmdbusy_cp : coverpoint spi_error_enable_reg.cmdbusy;
    err_csidinval_cross: cross ere_csidinval_cp, es_csidinval_cp;
    err_cmdinval_cross: cross ere_cmdinval_cp, es_cmdinval_cp;
    err_underflow_cross: cross ere_underflow_cp, es_underflow_cp;
    err_overflow_cross: cross ere_overflow_cp, es_overflow_cp;
    err_cmdbusy_cross: cross ere_cmdbusy_cp, es_cmdbusy_cp;
  endgroup

  covergroup event_en_cg with function sample(spi_host_event_enable_t spi_event_enable_reg);
    idle_cp : coverpoint spi_event_enable_reg.idle;
    ready_cp : coverpoint spi_event_enable_reg.ready;
    txwm_cp : coverpoint spi_event_enable_reg.txwm;
    rxwm_cp : coverpoint spi_event_enable_reg.rxwm;
    txempty_cp : coverpoint spi_event_enable_reg.txempty;
    rxfull_cp : coverpoint spi_event_enable_reg.rxfull;
  endgroup

  covergroup segment_speed_cg with function sample(spi_host_command_t spi_cmd_reg);
    mode_trans_cp : coverpoint spi_cmd_reg.mode {
      bins std_dual = (Standard=>Dual);
      bins std_quad = (Standard=>Quad);
      }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);

    tx_fifo_overflow_cg = new();
    rx_fifo_underflow_cg = new();
    config_opts_cg = new();
    unaligned_data_cg = new();
    duplex_cg = new();
    control_cg = new();
    status_cg = new();
    csid_cg = new();
    command_cg = new();
    error_en_cg = new();
    error_status_cg = new();
    event_en_cg = new();
    segment_speed_cg = new();

  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
