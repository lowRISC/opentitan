// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class dma_pull_seq #(int AddrWidth = 32) extends tl_device_seq#(.AddrWidth(AddrWidth));

  `uvm_object_param_utils(dma_pull_seq#(AddrWidth))

  // FIFO enable bits
  bit read_fifo_en;
  bit write_fifo_en;
  // FIFO instance
  dma_handshake_mode_fifo #(AddrWidth) fifo;

  function new (string name = "");
    super.new(name);
    min_rsp_delay = 1;
    max_rsp_delay = 4;
  endfunction: new

  virtual function void update_mem(REQ rsp);
    bit [65:0] intg;
    if (mem != null) begin
      if (rsp.a_opcode inside {PutFullData, PutPartialData}) begin
        bit [tl_agent_pkg::DataWidth-1:0] data;
        data = rsp.a_data;
        for (int i = 0; i < $bits(rsp.a_mask); i++) begin
          if (rsp.a_mask[i]) begin
            if (write_fifo_en) begin
              fifo.write_byte(rsp.a_addr + i, data[7:0]);
            end else begin
              mem.write_byte(rsp.a_addr + i, data[7:0]);
            end
          end
          data = data >> 8;
        end
      end else begin
        for (int i = 2**rsp.a_size - 1; i >= 0; i--) begin
          rsp.d_data = rsp.d_data << 8;
          if (read_fifo_en) begin
            rsp.d_data[7:0] = fifo.read_byte(rsp.a_addr+i);
          end else begin
            rsp.d_data[7:0] = mem.read_byte(rsp.a_addr+i);
          end
        end
      end
    end
    intg = prim_secded_pkg::prim_secded_inv_64_57_enc({51'b0,
                                                       rsp.d_opcode,
                                                       rsp.d_size,
                                                       rsp.d_error});
    rsp.d_user[13:7] = intg[63:57];
  endfunction: update_mem

  virtual function void randomize_rsp(REQ rsp);
    rsp.disable_a_chan_randomization();
    if (d_error_pct > 0) rsp.no_d_error_c.constraint_mode(0);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(rsp,
      rsp.d_valid_delay inside {[min_rsp_delay : max_rsp_delay]};
      if (rsp.a_opcode == tlul_pkg::Get) {
        rsp.d_opcode == tlul_pkg::AccessAckData;
      } else {
        rsp.d_opcode == tlul_pkg::AccessAck;
      }
      rsp.d_size == rsp.a_size;
      rsp.d_source == rsp.a_source;
      d_error dist {0 :/ (100 - d_error_pct), 1 :/ d_error_pct};
    )
    `uvm_info("dma_pull_seq",
              $sformatf("[check][d_chan] : a_address=0x%08h d_valid_delay=%0d",
                        rsp.a_addr, rsp.d_valid_delay),
              UVM_HIGH)
  endfunction
endclass
