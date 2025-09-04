`ifndef _HMAC_MSG_DRIVER_SV_
`define _HMAC_MSG_DRIVER_SV_

class hmac_msg_driver extends uvm_driver #(hmac_msg_item);
  `uvm_component_utils(hmac_msg_driver)
  `uvm_component_new

  // Handles provided via uvm_config_db
  hmac_reg_block ral;
  hmac_if        hmac_vif; // optional, for idle checks

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    if (!uvm_config_db#(hmac_reg_block)::get(this, "", "ral", ral)) begin
      `uvm_fatal(get_full_name(), "hmac_msg_driver requires ral via config_db key 'ral'")
    end
    void'(uvm_config_db#(hmac_if)::get(this, "", "hmac_vif", hmac_vif));
  endfunction

  task run_phase(uvm_phase phase);
    hmac_msg_item item;
    forever begin
      seq_item_port.get_next_item(item);
      `uvm_info(get_type_name(), $sformatf("Driving: %s", item.convert2string()), UVM_MEDIUM)
      drive_item(item);
      seq_item_port.item_done();
    end
  endtask

  protected task drive_item(hmac_msg_item item);
    uvm_status_e  status;

    // Optionally program key
    if (item.program_key) begin
      foreach (item.key_words[i]) begin
        ral.key[i].write(status, item.key_words[i]);
      end
    end

    // Start
    if (item.do_start) begin
      ral.cmd.write(status, 32'(1 << hmac_env_pkg::HashStart));
    end

    // Push payload bytes into MSG_FIFO as words
    if (item.payload.size() > 0) begin
      int idx = 0;
      bit [31:0] word;
      uvm_mem msg_fifo;
      // Get mem by name (generated from HJSON 'MSG_FIFO')
      msg_fifo = ral.get_mem_by_name("MSG_FIFO");
      if (msg_fifo == null) begin
        `uvm_fatal(get_full_name(), "RAL mem 'MSG_FIFO' not found")
      end
      while (idx < item.payload.size()) begin
        // pack up to 4 bytes in little-endian byte order
        word = '0;
        for (int b = 0; b < 4; b++) begin
          if (idx < item.payload.size()) begin
            word |= (item.payload[idx] << (8*b));
            idx++;
          end
        end
        msg_fifo.write(status, 0, word, UVM_FRONTDOOR, this);
      end
    end

    // Optional continue
    if (item.do_continue) begin
      ral.cmd.write(status, 32'(1 << hmac_env_pkg::HashContinue));
    end

    // Process
    if (item.do_process) begin
      ral.cmd.write(status, 32'(1 << hmac_env_pkg::HashProcess));
    end

    // Stop
    if (item.do_stop) begin
      ral.cmd.write(status, 32'(1 << hmac_env_pkg::HashStop));
    end

    // If virtual interface is available, wait for idle when appropriate
    if (hmac_vif != null) begin
      // Wait until idle is asserted
      wait (hmac_vif.is_idle());
    end
  endtask
endclass

`endif // _HMAC_MSG_DRIVER_SV_

