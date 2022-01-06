// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_monitor extends dv_base_monitor#(
    .ITEM_T (spi_item),
    .CFG_T  (spi_agent_cfg),
    .COV_T  (spi_agent_cov)
  );
  `uvm_component_utils(spi_monitor)

  spi_item host_item, host_clone;
  spi_item device_item, device_clone;

  // Analysis port for the collected transfer.
  uvm_analysis_port #(spi_item) host_analysis_port;
  uvm_analysis_port #(spi_item) device_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    host_analysis_port   = new("host_analysis_port", this);
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
      // indicate that this the first byte in a spi transaction
      host_item.first_byte = 1;
      collect_curr_trans();
    end
  endtask : collect_trans

  virtual protected task collect_curr_trans();
    fork
      begin: isolation_thread
        fork
          begin: csb_deassert_thread
            wait(cfg.vif.csb[cfg.csb_sel] == 1'b1);
          end
          begin: sample_thread
            // for mode 1 and 3, get the leading edges out of the way
            cfg.wait_sck_edge(LeadingEdge);
            forever begin
              bit [7:0] host_byte;    // from sio
              bit [7:0] device_byte;  // from sio
              int       which_bit;
              bit [3:0] num_bits;
              if (cfg.partial_byte == 1) begin
                num_bits = cfg.bits_to_transfer;
              end else begin
                num_bits = 8;
              end
              for (int i = 0; i < num_bits; i++) begin
                // wait for the sampling edge
                cfg.wait_sck_edge(SamplingEdge);
                // check sio not x or z
                if (cfg.en_monitor_checks) begin
                  `DV_CHECK_CASE_NE(cfg.vif.sio[1:0], 2'bxx)
                  `DV_CHECK_CASE_NE(cfg.vif.sio[1:0], 2'bxx)
                end
                // sample sio[0] for tx
                which_bit = cfg.host_bit_dir ? i : 7 - i;
                host_byte[which_bit] = cfg.vif.sio[0];
                cfg.vif.host_bit  = which_bit;
                cfg.vif.host_byte = host_byte;
                // sample sio[1] for rx
                which_bit = cfg.device_bit_dir ? i : 7 - i;
                device_byte[which_bit] = cfg.vif.sio[1];
                // sending 7 bits will be padded with 0 for the last bit
                if (i == 6 && num_bits == 7) begin
                  which_bit = cfg.device_bit_dir ? 7 : 0;
                  device_byte[which_bit] = 0;
                end
                cfg.vif.device_bit = which_bit;
                cfg.vif.device_byte = device_byte;
              end
              // sending less than 7 bits will not be captured, byte to be re-sent
              if (num_bits >= 7) begin
                host_item.data.push_back(host_byte);
                device_item.data.push_back(device_byte);
              end

              // sending transactions when collect a word data
              if (host_item.data.size == cfg.num_bytes_per_trans_in_mon &&
                  device_item.data.size == cfg.num_bytes_per_trans_in_mon) begin
                `uvm_info(`gfn, $sformatf("spi_monitor: host packet:\n%0s", host_item.sprint()),
                          UVM_DEBUG)
                `uvm_info(`gfn, $sformatf("spi_monitor: device packet:\n%0s", device_item.sprint()),
                          UVM_DEBUG)
                `downcast(host_clone, host_item.clone());
                `downcast(device_clone, device_item.clone());
                host_analysis_port.write(host_clone);
                device_analysis_port.write(device_clone);
                // write to fifo for re-active env
                req_analysis_port.write(host_clone);
                rsp_analysis_port.write(device_clone);
                // clean items
                host_item   = spi_item::type_id::create("host_item", this);
                device_item = spi_item::type_id::create("device_item", this);
              end
            end // forever
          end: sample_thread
        join_any
        disable fork;
      end
    join
  endtask : collect_curr_trans

  virtual task monitor_ready_to_end();
    ok_to_end = cfg.vif.csb[cfg.csb_sel];
    forever begin
      @(cfg.vif.csb[cfg.csb_sel]);
      ok_to_end = cfg.vif.csb[cfg.csb_sel];
    end
  endtask : monitor_ready_to_end

endclass : spi_monitor
