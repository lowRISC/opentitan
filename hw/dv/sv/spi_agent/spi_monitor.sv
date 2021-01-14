// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_monitor extends dv_base_monitor#(
    .ITEM_T (spi_item),
    .CFG_T  (spi_agent_cfg),
    .COV_T  (spi_agent_cov)
  );
  `uvm_component_utils(spi_monitor)

  spi_item host_item;
  spi_item device_item;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(spi_item) host_analysis_port;
  uvm_analysis_port #(spi_item) device_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_analysis_port = new("host_analysis_port", this);
    device_analysis_port = new("device_analysis_port", this);
  endfunction

  virtual task run_phase(uvm_phase phase);
    collect_trans(phase);
  endtask

  // collect transactions forever
  virtual protected task collect_trans(uvm_phase phase);
    host_item   = spi_item::type_id::create("host_item", this);
    device_item = spi_item::type_id::create("device_item", this);

    forever begin
      @(negedge cfg.vif.csb);
      if (cfg.en_monitor_collect_trans) collect_curr_trans();
    end
  endtask

  virtual protected task collect_curr_trans();

    fork
      begin: isolation_thread
        fork
          begin: csb_deassert_thread
            wait(cfg.vif.csb == 1'b1);
          end
          begin: sample_thread
            // for mode 1 and 3, get the leading edges out of the way
            cfg.wait_sck_edge(LeadingEdge);
            forever begin
              bit [7:0] host_byte;    // from sdi
              bit [7:0] device_byte;  // from sdo
              int       which_bit;
              for (int i = 0; i < 8; i++) begin
                // wait for the sampling edge
                cfg.wait_sck_edge(SamplingEdge);
                // check sdi/sdo not x or z
                if (cfg.en_monitor_checks) begin
                  `DV_CHECK_CASE_NE(cfg.vif.sdi, 1'bx)
                  `DV_CHECK_CASE_NE(cfg.vif.sdi, 1'bz)
                  `DV_CHECK_CASE_NE(cfg.vif.sdo, 1'bx)
                  `DV_CHECK_CASE_NE(cfg.vif.sdo, 1'bz)
                end
                // sample sdi
                which_bit = cfg.host_bit_dir ? i : 7 - i;
                host_byte[which_bit] = cfg.vif.sdi;
                cfg.vif.host_bit = which_bit;
                cfg.vif.host_byte = host_byte;
                // sample sdo
                which_bit = cfg.device_bit_dir ? i : 7 - i;
                device_byte[which_bit] = cfg.vif.sdo;
                cfg.vif.device_bit = which_bit;
                cfg.vif.device_byte = device_byte;
              end
              host_item.data.push_back(host_byte);
              device_item.data.push_back(device_byte);

              // sending transactions when collect a word data
              if (host_item.data.size == cfg.num_bytes_per_trans_in_mon &&
                  device_item.data.size == cfg.num_bytes_per_trans_in_mon) begin
                `uvm_info(`gfn, $sformatf("spi_monitor: host packet:\n%0s", host_item.sprint()),
                          UVM_HIGH)
                `uvm_info(`gfn, $sformatf("spi_monitor: device packet:\n%0s", device_item.sprint()),
                          UVM_HIGH)
                host_analysis_port.write(host_item);
                device_analysis_port.write(device_item);
                host_item   = spi_item::type_id::create("host_item", this);
                device_item = spi_item::type_id::create("device_item", this);
              end
            end // forever
          end: sample_thread
        join_any
        disable fork;
      end
    join
  endtask

  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.csb);
      ok_to_end = !cfg.vif.csb;
    end
  endtask

endclass
