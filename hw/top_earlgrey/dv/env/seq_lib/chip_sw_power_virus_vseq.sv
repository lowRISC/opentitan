// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_power_virus_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_power_virus_vseq)

  `uvm_object_new

  virtual function int sw_symbol_backdoor_read32(string symbol);
    bit [7:0] byte_array[4];
    sw_symbol_backdoor_read(symbol, byte_array);
    return {<<byte{byte_array}};
  endfunction

  virtual task i2c_device_autoresponder(int i2c_idx);
    i2c_device_response_seq seq = i2c_device_response_seq::type_id::create("seq");
    fork seq.start(p_sequencer.i2c_sequencer_hs[i2c_idx]); join_none
  endtask

  // Utility task to configure the I2C agents
  virtual task configure_i2c_agents();
    bit [31:0] i2c_scl_period_ns;          // `kI2cSclPeriodNs` in SW
    bit [31:0] peripheral_clock_freq_hz;   // `kClockFreqPeripheralHz` in SW
    bit [31:0] peripheral_clock_period_ns; // `peripheral_clock_period_ns` in SW
    bit [31:0] half_cycles_in_i2c_period;
    // Hard-coded from `sw/device/lib/arch/device_sim_dv.c`.
    peripheral_clock_freq_hz = 24 * 1000 * 1000;
    peripheral_clock_period_ns = 1_000_000_000 / peripheral_clock_freq_hz;
    `uvm_info(`gfn, $sformatf("peripheral_clock_period_ns = %0d", peripheral_clock_period_ns),
      UVM_LOW);

    // Hard-coded from `sw/device/tests/power_virus_systemtest.c`.
    i2c_scl_period_ns = 1000;
    half_cycles_in_i2c_period = ((int'(i2c_scl_period_ns) / 2 - 1) /
      int'(peripheral_clock_period_ns)) + 1;
    `uvm_info(`gfn, $sformatf("Half (peripheral) cycles in I2C clock period: %d",
      half_cycles_in_i2c_period), UVM_LOW);

    foreach (cfg.m_i2c_agent_cfgs[i]) begin
      cfg.m_i2c_agent_cfgs[i].if_mode = Device;
      cfg.m_i2c_agent_cfgs[i].target_addr0 = i + 1;
      cfg.m_i2c_agent_cfgs[i].timing_cfg.tClockLow = half_cycles_in_i2c_period - 2;
      cfg.m_i2c_agent_cfgs[i].timing_cfg.tClockPulse = half_cycles_in_i2c_period + 1;
    end
  endtask

  // Utility task to handle the spi_host1 transmission
  // It continuosly reads the data as long as CSb[0] is 0.
  virtual task read_spi_host1_bytes();
    bit [7:0] data; // holds the spi_host1 TX bytes
    fork
        begin: spi_host1_isolation_fork
          // enable spi agent and monitor
          cfg.chip_vif.enable_spi_device(.inst_num(1), .enable(1));
          cfg.m_spi_device_agent_cfgs[1].en_monitor = 1;
          fork
            begin : spi_host1_csb_deassert_thread
              // Wait until the transmission ends (i.e, CSb[0] = 1)
              wait(cfg.m_spi_device_agent_cfgs[1].vif.csb[0] == 1'b1);
            end
            begin: spi_host1_read_byte_thread
              // Continously read the bytes as long as transmission is on going (i.e, CSb[0] = 0)
              forever begin
                cfg.m_spi_device_agent_cfgs[1].read_byte(.num_lanes(4), .is_device_rsp(0), .csb_id(0), .data(data));
                `uvm_info(`gfn, $sformatf("spi host 1 data_byte = %0h", data), UVM_LOW)
                `DV_CHECK_EQ(data, 8'haa);
              end
            end
          join_any;
          disable fork;
        end // spi_host1_isolation_fork
      join
  endtask

  task pre_start();
    // i2c_agent configs
    configure_i2c_agents();

    // Spi_device_agent1 config to handle spi_host1 TX bytes
    cfg.m_spi_device_agent_cfgs[1].csid = '0;
    cfg.m_spi_device_agent_cfgs[1].num_bytes_per_trans_in_mon = 4;
    cfg.m_spi_device_agent_cfgs[1].spi_mode = Quad;
    cfg.m_spi_device_agent_cfgs[1].if_mode = dv_utils_pkg::Device;
    cfg.m_spi_device_agent_cfgs[1].is_active = 0;
    super.pre_start();
  endtask

  virtual task body();
    super.body();
    // Wait for test_main() to start and configurations to be computed.
    `DV_WAIT(cfg.sw_logger_vif.printed_log == "All IPs configured.");

    // Main fork-join block to handle IP-specific threads
    fork
      begin: i2c_agent_thread
        // Enable I2C monitors and sequences.
        foreach (cfg.m_i2c_agent_cfgs[i]) begin
          cfg.m_i2c_agent_cfgs[i].en_monitor = 1'b1;
          cfg.chip_vif.enable_i2c(.inst_num(i), .enable(1));
          i2c_device_autoresponder(i);
        end
      end
      // Read bytes transmitted from spi_host1.
      begin: spi_host_1_thread
        read_spi_host1_bytes();
      end
    join
  endtask

endclass : chip_sw_power_virus_vseq
