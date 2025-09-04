// Example virtual sequence using the hmac_msg_agent
`ifndef _HMAC_MSG_SMOKE_VSEQ_SV_
`define _HMAC_MSG_SMOKE_VSEQ_SV_

class hmac_msg_smoke_vseq extends hmac_base_vseq;
  `uvm_object_utils(hmac_msg_smoke_vseq)
  `uvm_object_new

  virtual task body();
    // Basic init
    hmac_init(.sha_en(1'b1), .hmac_en(1'b0)); // SHA-only for a smoke test

    // Prepare a short message: "abc"
    hmac_msg_item it = hmac_msg_item::type_id::create("it");
    it.do_start    = 1'b1;
    it.do_process  = 1'b1;
    it.payload     = new[3];
    it.payload[0]  = "a";
    it.payload[1]  = "b";
    it.payload[2]  = "c";

    // NOTE: Actual driving via hmac_msg_agent will be added once
    // the agent is integrated and its sequencer handle is plumbed
    // into the virtual sequencer. For now, rely on base_vseq helpers.
    wr_msg({"a","b","c"}, 1);

    // Read digest via existing helper
    bit [TL_DW-1:0] digest[16];
    csr_rd_digest(digest);
  endtask
endclass

`endif // _HMAC_MSG_SMOKE_VSEQ_SV_
