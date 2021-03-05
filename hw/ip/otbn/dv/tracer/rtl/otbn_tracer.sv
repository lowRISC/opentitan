// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifndef SYNTHESIS

/**
 * Tracer module for OTBN. This produces a multi-line string as trace output at most once every
 * cycle and provides it to the simulation environment via a DPI call. It uses `otbn_trace_if` to
 * get the information it needs. For further information see `hw/ip/otbn/dv/tracer/README.md`.
 */
module otbn_tracer
(
  input  logic  clk_i,
  input  logic  rst_ni,

  otbn_trace_if otbn_trace
);
  import otbn_pkg::*;

  // Prefixes used in trace lines. Formats are documented in `hw/ip/otbn/dv/tracer/README.md`
  parameter string InsnExecutePrefix = "E";
  parameter string InsnStallPrefix = "S";
  parameter string RegReadPrefix = "<";
  parameter string RegWritePrefix = ">";
  parameter string MemWritePrefix = "W";
  parameter string MemReadPrefix = "R";

  string trace_output_buffer;

  logic [31:0] cycle_count;

  // Given a WLEN size word output a hex string with the data split into 32-bit chunks separated
  // with '_'. WLEN must be a multiple of 32.
  function automatic string otbn_wlen_data_str(logic [WLEN-1:0] data);
    string data_str;

    assert ((WLEN % 32) == 0) else $error("WLEN must be a multiple of 32 in otbn_wlen_data_str");

    for (int i = WLEN; i > 0; i-= 32) begin
      if (i != WLEN) begin
        data_str = $sformatf("%s_", data_str);
      end else begin
        data_str = "0x";
      end

      data_str = $sformatf("%s%08x", data_str, data[i-1 -: 32]);
    end

    return data_str;
  endfunction

  // Produce trace output string for dmem writes. For a 256-bit write, the address and full data is
  // output. For 32-bit writes (determined by looking at the mask) only the relevant 32-bit chunk is
  // output along with the address modified so it refers to that chunk.
  function automatic string otbn_dmem_write_str(logic [31:0] addr,
                                                logic [WLEN-1:0] data,
                                                logic [WLEN-1:0] wmask);

    logic [WLEN-1:0] cur_base_mask;

    // For a full WLEN write output all of the data.
    if (wmask == '1) begin
      return $sformatf("[0x%08x]: %s", addr, otbn_wlen_data_str(data));
    end

    // Iterate through the possible 32-bit chunks
    cur_base_mask = {{(WLEN-32){1'b0}}, 32'hFFFF_FFFF};

    for (int i = 0; i < WLEN; i += 32) begin
      // If mask matches current chunk alone output trace indicating a single 32-bit write.
      if (wmask == cur_base_mask) begin
        return $sformatf("[0x%08x]: 0x%08x", addr + (i / 8), data[i*32 +: 32]);
      end

      cur_base_mask = cur_base_mask << 32;
    end

    // Fallback where mask isn't as expected, indicate ERR in the trace and provide both full mask
    // and data.
    return $sformatf("[0x%08x]: Mask ERR Mask: %s Data: %s", addr, otbn_wlen_data_str(wmask),
      otbn_wlen_data_str(data));
  endfunction

  // Determine name for an ISPR
  function automatic string otbn_ispr_name_str(ispr_e ispr);
    unique case (ispr)
      IsprMod: return "MOD";
      IsprAcc: return "ACC";
      IsprRnd: return "RND";
      IsprFlags: return "FLAGS";
      default: return "UNKNOWN_ISPR";
    endcase
  endfunction

  // Format flag information into a string
  function automatic string otbn_flags_str(flags_t f);
    return $sformatf("{C: %d, M: %d, L: %d, Z: %d}", f.C, f.M, f.L, f.Z);
  endfunction

  // Called by other trace functions to append their trace lines to the output buffer
  function automatic void output_trace(string prefix, string trace_line);
    trace_output_buffer = $sformatf("%s%s %s\n", trace_output_buffer, prefix, trace_line);
  endfunction

  function automatic void trace_base_rf();
    if (otbn_trace.rf_base_rd_en_a) begin
      output_trace(RegReadPrefix, $sformatf("x%02d: 0x%08x", otbn_trace.rf_base_rd_addr_a,
                                            otbn_trace.rf_base_rd_data_a));
    end

    if (otbn_trace.rf_base_rd_en_b) begin
      output_trace(RegReadPrefix, $sformatf("x%02d: 0x%08x", otbn_trace.rf_base_rd_addr_b,
                                            otbn_trace.rf_base_rd_data_b));
    end

    if (otbn_trace.rf_base_wr_en && otbn_trace.rf_base_wr_commit &&
        otbn_trace.rf_base_wr_addr != '0) begin
      output_trace(RegWritePrefix, $sformatf("x%02d: 0x%08x", otbn_trace.rf_base_wr_addr,
                                             otbn_trace.rf_base_wr_data));
    end
  endfunction

  function automatic void trace_bignum_rf();
    if (otbn_trace.rf_ren_a_bignum) begin
      output_trace(RegReadPrefix, $sformatf("w%02d: %s", otbn_trace.rf_bignum_rd_addr_a,
                                            otbn_wlen_data_str(otbn_trace.rf_bignum_rd_data_a)));
    end

    if (otbn_trace.rf_ren_b_bignum) begin
      output_trace(RegReadPrefix, $sformatf("w%02d: %s", otbn_trace.rf_bignum_rd_addr_b,
                                            otbn_wlen_data_str(otbn_trace.rf_bignum_rd_data_b)));
    end

    if (otbn_trace.rf_bignum_wr_en) begin
      output_trace(RegWritePrefix, $sformatf("w%02d: %s", otbn_trace.rf_bignum_wr_addr,
                                             otbn_wlen_data_str(otbn_trace.rf_bignum_wr_data)));
    end
  endfunction

  function automatic void trace_bignum_mem();
    if (otbn_trace.dmem_write) begin
      output_trace(MemWritePrefix, otbn_dmem_write_str(otbn_trace.dmem_write_addr,
                                                       otbn_trace.dmem_write_data,
                                                       otbn_trace.dmem_write_mask));
    end

    if (otbn_trace.dmem_read) begin
      output_trace(MemReadPrefix, $sformatf("[0x%08x]: %s", otbn_trace.dmem_read_addr,
                                            otbn_wlen_data_str(otbn_trace.dmem_read_data)));
    end
  endfunction

  function automatic void trace_ispr_accesses();
    // Iterate through all ISPRs outputting reg reads and writes where ISPR accesses have occurred
    for (int i_ispr = 0; i_ispr < NIspr; i_ispr++) begin
      if (ispr_e'(i_ispr) == IsprFlags) begin
        // Special handling for flags ISPR to provide per flag field output
        for (int i_fg = 0; i_fg < NFlagGroups; i_fg++) begin
          if (otbn_trace.flags_read[i_fg]) begin
            output_trace(RegReadPrefix,
                         $sformatf("%s%1d: %s", otbn_ispr_name_str(ispr_e'(i_ispr)), i_fg,
                                   otbn_flags_str(otbn_trace.flags_read_data[i_fg])));
          end

          if (otbn_trace.flags_write[i_fg]) begin
            output_trace(RegWritePrefix,
                         $sformatf("%s%1d: %s", otbn_ispr_name_str(ispr_e'(i_ispr)), i_fg,
                                   otbn_flags_str(otbn_trace.flags_write_data[i_fg])));
          end
        end
      end else begin
        // For all other ISPRs just dump out the full 256-bits of data being read/written
        if (otbn_trace.ispr_read[i_ispr]) begin
          output_trace(RegReadPrefix,
                       $sformatf("%s: %s", otbn_ispr_name_str(ispr_e'(i_ispr)),
                                 otbn_wlen_data_str(otbn_trace.ispr_read_data[i_ispr])));
        end

        if (otbn_trace.ispr_write[i_ispr]) begin
          output_trace(RegWritePrefix,
                       $sformatf("%s: %s", otbn_ispr_name_str(ispr_e'(i_ispr)),
                                 otbn_wlen_data_str(otbn_trace.ispr_write_data[i_ispr])));
        end
      end
    end
  endfunction

  function automatic void trace_insn();
    if (otbn_trace.insn_valid) begin
      output_trace(otbn_trace.insn_stall ? InsnStallPrefix : InsnExecutePrefix,
                   $sformatf("PC: 0x%08x, insn: 0x%08x", otbn_trace.insn_addr,
                             otbn_trace.insn_data));
    end
  endfunction

  import "DPI-C" function void accept_otbn_trace_string(string trace, int unsigned cycle_count);

  function automatic void do_trace();
    trace_output_buffer = "";

    trace_insn();
    trace_bignum_rf();
    trace_base_rf();
    trace_bignum_mem();
    trace_ispr_accesses();

    if (trace_output_buffer != "") begin
      accept_otbn_trace_string(trace_output_buffer, cycle_count);
    end
  endfunction

  always @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      cycle_count <= '0;
    end else begin
      cycle_count <= cycle_count + 1'b1;
      do_trace();
    end
  end
endmodule

`endif // SYNTHESIS
