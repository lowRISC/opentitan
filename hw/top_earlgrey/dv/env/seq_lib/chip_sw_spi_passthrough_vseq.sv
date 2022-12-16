// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_spi_passthrough_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_spi_passthrough_vseq)

  `uvm_object_new

  // The sequence of opcodes used for the test.
  spi_flash_cmd_e test_opcodes[$];
  // Whether to check for transactions appearing on the unused spi_host.
  bit en_unused_spi_host_monitoring = 1'b1;
  // Frequencies to use for testing the sequences.
  time sck_periods_ps[] = '{
    41_000, // 24 MHz
    33_000, // 30 MHz
    167_000 // 6 MHz
  };
  // A bit map of command slots that will have passthrough filters enabled.
  rand bit [spi_device_pkg::NumTotalCmdInfo-1:0] passthrough_filters;

  // Generate a random permutation of the following opcodes, and place them in
  // the test_opcodes queue:
  //   - SpiFlashReadNormal
  //   - SpiFlashReadFast
  //   - SpiFlashReadDual
  //   - SpiFlashReadQuad
  //   - SpiFlashChipErase
  //   - SpiFlashPageProgram
  virtual function void generate_spi_flash_sequence();
    test_opcodes = '{
      SpiFlashReadNormal,
      SpiFlashReadFast,
      SpiFlashReadDual,
      SpiFlashReadQuad,
      SpiFlashChipErase,
      SpiFlashPageProgram
    };
    test_opcodes.shuffle();
  endfunction

  // Assert that spi_host does not send any transactions.
  virtual task monitor_unused_spi_host();
    spi_agent_cfg agent_cfg = cfg.m_spi_device_agent_cfgs[1];
    // CSB should never assert
    wait (agent_cfg.vif.rst_n && !agent_cfg.vif.csb[0]);
    `uvm_fatal(`gfn, $sformatf(
      "Observed SPI transaction on spi_host1, which should be inactive"));
  endtask

  task get_filtered_commands(output bit [255:0] filter_map);
    filter_map = '0;
    for (int i = 0; i < spi_device_pkg::NumTotalCmdInfo; i++) begin
      uvm_object csr;
      uvm_reg_data_t opcode;
      case (spi_device_pkg::cmd_info_index_e'(i))
        spi_device_pkg::CmdInfoEn4B:  csr = ral.spi_device.cmd_info_en4b.opcode;
        spi_device_pkg::CmdInfoEx4B:  csr = ral.spi_device.cmd_info_ex4b.opcode;
        spi_device_pkg::CmdInfoWrEn:  csr = ral.spi_device.cmd_info_wren.opcode;
        spi_device_pkg::CmdInfoWrDi:  csr = ral.spi_device.cmd_info_wrdi.opcode;
        default:                      csr = ral.spi_device.cmd_info[i].opcode;
      endcase
      if (passthrough_filters[i]) begin
        csr_rd(.ptr(csr), .value(opcode), .backdoor(1));
        filter_map[8'(opcode)] = 1'b1;
      end
    end
  endtask

  // Send the sequence of commands indicated by the `test_opcodes` member.
  // These commands must be registered with the host and device agents, as the
  // command info determines the actions takes for each opcode. Random data of
  // random size will be generated for each command that has a payload phase.
  virtual task execute_spi_flash_sequence();
    const int max_payload_size = 1024;
    spi_device_flash_seq m_spi_device_seq;
    spi_host_flash_seq m_spi_host_seq;
    spi_item host_rsp, device_rsp;
    spi_item device_rsp_q[$];
    spi_agent_cfg agent_cfg = cfg.m_spi_host_agent_cfg;
    bit [255:0] filter_map;
    get_filtered_commands(filter_map);

    fork begin : isolation_fork
      // The device agent handles the incoming command, if it is not filtered.
      fork
        forever begin
          `uvm_create_on(m_spi_device_seq, p_sequencer.spi_device_sequencer_hs[0]);
          `uvm_send(m_spi_device_seq);
          device_rsp_q.push_back(m_spi_device_seq.rsp);
        end
      join_none

      while (test_opcodes.size() > 0) begin
        bit [7:0] opcode = test_opcodes.pop_front();

        `uvm_create_on(m_spi_host_seq, p_sequencer.spi_host_sequencer_h);
        // Prepare for specific opcode. The address_q is kept empty, which will
        // trigger m_spi_host_seq to do the lookup and supply a random value.
        `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                       opcode == local::opcode;
                                       address_q.size() == 0;
                                       payload_q.size() <= local::max_payload_size;
                                       read_size == payload_q.size(););
        `uvm_send(m_spi_host_seq);
        // Wait for a small delay to allow the device agent to push the response
        // into the queue.
        #1ps;
        if (!filter_map[opcode]) begin
          // Check that the command, address, and data sent matches on both sides.
          `DV_CHECK_EQ(device_rsp_q.size(), 1);
          host_rsp = m_spi_host_seq.rsp;
          device_rsp = device_rsp_q.pop_front();
          if (!host_rsp.compare(device_rsp)) begin
            `uvm_error(`gfn, $sformatf("Compare mismatch\nhost_rsp:\n%sdevice_rsp:\n%s",
                                       host_rsp.sprint(), device_rsp.sprint()))
          end
        end else begin
          `DV_CHECK_EQ(device_rsp_q.size(), 0);
        end
      end
      disable fork;
    end join
  endtask

  virtual task cpu_init();
    bit [7:0] sw_filter_config[4];
    super.cpu_init();
    `DV_CHECK_MEMBER_RANDOMIZE_FATAL(passthrough_filters);
    sw_filter_config = {<<byte{passthrough_filters}};
    sw_symbol_backdoor_overwrite("kFilteredCommands", sw_filter_config);
  endtask

  virtual task body();
    // Turn off the FIFO data output assertion, as spi_device issues a read
    // before it knows whether it needs the data.
    $assertoff(0, "tb.dut.top_earlgrey.u_spi_device.u_readcmd.u_readsram.u_sram_fifo.DataKnown_A");
    $assertoff(0, "tb.dut.top_earlgrey.u_spi_device.u_readcmd.u_readsram.u_fifo.DataKnown_A");

    super.body();

    cfg.m_spi_device_agent_cfgs[0].byte_order = '0;

    // Set CSB inactive times to reasonable values. sys_clk is at 24 MHz, and
    // it needs to capture CSB pulses.
    cfg.m_spi_host_agent_cfg.min_idle_ns_after_csb_drop = 50;
    cfg.m_spi_host_agent_cfg.max_idle_ns_after_csb_drop = 200;

    spi_agent_configure_flash_cmds(cfg.m_spi_host_agent_cfg);
    spi_agent_configure_flash_cmds(cfg.m_spi_device_agent_cfgs[0]);
    // Enable the spi agents.
    cfg.chip_vif.enable_spi_host = 1;
    cfg.chip_vif.enable_spi_device(.inst_num(0), .enable(1));
    cfg.chip_vif.enable_spi_device(.inst_num(1), .enable(1));

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest,
             "Timed out waiting for SwTestStatusInTest",
             10_000_000)
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "Test setup complete.",
             "Timeout waiting for software to complete setup.")

    if (en_unused_spi_host_monitoring) begin
      fork
        monitor_unused_spi_host();
      join_none
    end
    foreach (sck_periods_ps[i]) begin
      cfg.m_spi_host_agent_cfg.sck_period_ps = sck_periods_ps[i];
      generate_spi_flash_sequence();
      execute_spi_flash_sequence();
    end
    override_test_status_and_finish(1'b1);
  endtask

endclass : chip_sw_spi_passthrough_vseq
