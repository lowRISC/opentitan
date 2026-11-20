// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_host_tx_rx_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_host_tx_rx_vseq)

  `uvm_object_new

  rand int spi_host_idx;
  rand int spi_host_csid;

  constraint spi_host_idx_c {
    spi_host_idx inside {[0:NUM_SPI_HOSTS-1]};
  }

  constraint spi_host_csid_c {
    spi_host_csid inside {[0:NUM_SPI_HOST_CSBS-1]};
  }

  task pre_start();
    // Use plusargs '+spi_host_idx' and '+spi_host_csid' to choose a spi_host instance and chip
    // select line explicitly if required, otherwise they will be chosen randomly.
    void'($value$plusargs("spi_host_idx=%0d", spi_host_idx));
    `DV_CHECK_FATAL(spi_host_idx inside {[0:NUM_SPI_HOSTS-1]})
    void'($value$plusargs("spi_host_csid=%0d", spi_host_csid));
    `DV_CHECK_FATAL(spi_host_csid inside {[0:NUM_SPI_HOST_CSBS-1]})

    // Select the chip select line for communication.
    cfg.m_spi_device_agent_cfgs[spi_host_idx].csid = spi_host_csid;

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

  virtual task cpu_init();
    // sw_symbol_backdoor_overwrite takes an array as the input
    bit [7:0] spi_host_idx_data[] = {spi_host_idx};
    bit [7:0] spi_host_csid_data[] = {spi_host_csid};

    super.cpu_init();
    sw_symbol_backdoor_overwrite("kSPIHostIdx", spi_host_idx_data);
    sw_symbol_backdoor_overwrite("kSPIHostCsid", spi_host_csid_data);
  endtask

  virtual task body();
    spi_device_seq m_device_seq;
    super.body();
    `uvm_info(`gfn, $sformatf("Testing with spi host %0d, csid %0d", spi_host_idx, spi_host_csid),
              UVM_LOW)

    // enable spi agent
    cfg.chip_vif.enable_spi_device(.inst_num(spi_host_idx), .enable(1));

    // Wait for the sw to finish configuring the spi_host DUT
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "spi host configuration complete",
             "Timedout waiting for spi host c configuration.")

    // create and start the spi_device sequence
    m_device_seq = spi_device_seq::type_id::create("m_device_seq");
    fork m_device_seq.start(p_sequencer.spi_device_sequencer_hs[spi_host_idx]); join_none
  endtask


endclass : chip_sw_spi_host_tx_rx_vseq
