// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_host_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_host_tx_rx_vseq)

  `uvm_object_new

  rand int spi_host_idx;

  constraint spi_host_idx_c {
    spi_host_idx inside {[0 : 0]};
  }

  task pre_start();
    // Select the first Csb for communication.
    cfg.m_spi_device_agent_cfgs[spi_host_idx].csid = '0;

    // While the selection of this value seems arbitrary, it is not.
    // The spi agent has a concept of "transaction size" that is used by the
    // monitor / driver to determine how it should view the number of collected
    // bytes.
    // The value 4 is chosen because the corresponding C test case does the following:
    // Transmit 4 bytes
    // Transmit and receive N bytes
    // Receive 4 bytes
    // This sequence, when paired with the agent's 4 byte granularity playback,
    // works well as a smoke test case for spi host activity.
    cfg.m_spi_device_agent_cfgs[spi_host_idx].num_bytes_per_trans_in_mon = 4;

    // Setting the byte order to 0 ensures that the 4 byte transaction sent to
    // the agent from the DUT is played back in exactly the same order, thus
    // making things easy to compare.
    cfg.m_spi_device_agent_cfgs[spi_host_idx].byte_order = '0;
    super.pre_start();
  endtask

  virtual task body();
    spi_device_seq m_device_seq;
    super.body();
    `uvm_info(`gfn, $sformatf("Testing with spi host %d", spi_host_idx), UVM_LOW)

    // enable interface
    cfg.chip_vif.enable_spi_device(spi_host_idx, 1);

    // create and start the spi_device sequence
    m_device_seq = spi_device_seq::type_id::create("m_device_seq");

    fork begin
       m_device_seq.start(p_sequencer.spi_device_sequencer_hs[spi_host_idx]);
    end
    join_none
  endtask


endclass : chip_sw_spi_host_tx_rx_vseq
