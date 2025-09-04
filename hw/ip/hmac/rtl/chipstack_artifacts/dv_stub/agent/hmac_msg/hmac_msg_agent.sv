`ifndef _HMAC_MSG_AGENT_SV_
`define _HMAC_MSG_AGENT_SV_

class hmac_msg_agent extends uvm_agent;
  `uvm_component_utils(hmac_msg_agent)
  `uvm_component_new

  uvm_active_passive_enum is_active = UVM_ACTIVE;

  hmac_msg_sequencer m_sequencer;
  hmac_msg_driver    m_driver;

  // RAL and optional interface are plumbed via config_db
  hmac_reg_block ral;
  hmac_if        hmac_vif;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    void'(uvm_config_db#(hmac_reg_block)::get(this, "", "ral", ral));
    void'(uvm_config_db#(hmac_if)::get(this, "", "hmac_vif", hmac_vif));
    if (is_active == UVM_ACTIVE) begin
      m_sequencer = hmac_msg_sequencer::type_id::create("m_sequencer", this);
      m_driver    = hmac_msg_driver   ::type_id::create("m_driver", this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    if (is_active == UVM_ACTIVE) begin
      m_driver.seq_item_port.connect(m_sequencer.seq_item_export);
      if (ral != null) begin
        uvm_config_db#(hmac_reg_block)::set(this, "m_driver", "ral", ral);
      end
      if (hmac_vif != null) begin
        uvm_config_db#(hmac_if)::set(this, "m_driver", "hmac_vif", hmac_vif);
      end
    end
  endfunction
endclass

`endif // _HMAC_MSG_AGENT_SV_

