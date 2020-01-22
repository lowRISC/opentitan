// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// test with more dummy csk/csb and more extra delay btw csk/word
class spi_device_dummy_item_extra_dly_vseq extends spi_device_txrx_vseq;
  `uvm_object_utils(spi_device_dummy_item_extra_dly_vseq)
  `uvm_object_new

  constraint en_dummy_host_xfer_c {
    en_dummy_host_xfer == 1;
  }

  constraint en_extra_dly_c {
    en_extra_dly == 1;
  }

  virtual task spi_device_init();
    super.spi_device_init();
    // use more aggressive delay, but if higher than below values, timeout may happen
    randcase
      1: begin
        cfg.m_spi_agent_cfg.max_extra_dly_ns_btw_sck    = 100;
        cfg.m_spi_agent_cfg.extra_dly_chance_pc_btw_sck = 20;
      end
      1: begin
        cfg.m_spi_agent_cfg.max_extra_dly_ns_btw_sck    = 50;
        cfg.m_spi_agent_cfg.extra_dly_chance_pc_btw_sck = 50;
      end
    endcase
    // no timeout concern for delay between word
    cfg.m_spi_agent_cfg.max_extra_dly_ns_btw_word = 10000;
    cfg.m_spi_agent_cfg.extra_dly_chance_pc_btw_word = 20;
  endtask

endclass : spi_device_dummy_item_extra_dly_vseq
