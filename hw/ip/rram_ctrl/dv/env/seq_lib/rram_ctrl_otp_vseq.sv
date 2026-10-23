// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Issues random commands on the OTP macro interface and checks their results against the
// backdoor contents of the OTP region.
class rram_ctrl_otp_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_otp_vseq)

  // Number of OTP commands.
  rand int unsigned num_cmds;
  constraint num_cmds_c { num_cmds inside {[400:600]}; }

  rand otp_ctrl_macro_pkg::otp_macro_data_t wdata;
  rand otp_ctrl_macro_pkg::otp_macro_addr_t addr;
  rand otp_ctrl_macro_pkg::otp_macro_size_t size;
  rand otp_ctrl_macro_pkg::cmd_e            otp_cmd;

  // Legal sizes are 0, 1 and 3 for 16b, 32b and 64b transactions
  constraint size_c {
    size inside {2'b00, 2'b01, 2'b11};
  }

  constraint otp_cmd_c {
    otp_cmd != otp_ctrl_macro_pkg::Init;
  }

  // Only the transferred words carry data
  constraint data_c {
    solve size before wdata;
    if (size == 0) {
      wdata[otp_ctrl_macro_pkg::OtpIfWidth-1:16] == '0;
    } else if (size == 1) {
      wdata[otp_ctrl_macro_pkg::OtpIfWidth-1:32] == '0;
    }
  }

  // Transfers are aligned to their size and stay within the OTP
  constraint addr_c {
    solve size before addr;
    int'(addr) + int'(size) < otp_ctrl_macro_pkg::OtpDepth;
    if (size == 1) {
      addr[0] == 1'b0;
    } else if (size == 3) {
      addr[1:0] == 2'b0;
    }
  }

  // Concentrate half of the commands on the lowest 10% of the OTP region, so that writes often
  // hit previously written data.
  localparam int unsigned OtpWords = otp_ctrl_macro_pkg::OtpDepth;
  constraint addr_dist_c {
    addr dist {
      [0 : OtpWords / 10 - 1]        :/ 50,
      [OtpWords / 10 : OtpWords - 1] :/ 50
    };
  }

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_otp_vseq


function rram_ctrl_otp_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_otp_vseq::body();
  otp_ctrl_macro_pkg::otp_macro_data_t rdata;

  repeat (num_cmds) begin
    `DV_CHECK_FATAL(randomize(wdata, addr, size, otp_cmd))
    case (otp_cmd)
      otp_ctrl_macro_pkg::Write:    otp_write(addr, size, 1'b0, 1'b1, wdata);
      otp_ctrl_macro_pkg::Read:     otp_read(addr, size, 1'b0, 1'b1, rdata);
      otp_ctrl_macro_pkg::WriteRaw: otp_write(addr, size, 1'b1, 1'b1, wdata);
      otp_ctrl_macro_pkg::ReadRaw:  otp_read(addr, size, 1'b1, 1'b1, rdata);
      otp_ctrl_macro_pkg::Zeroize:  otp_zeroize(addr, size, 1'b1, rdata);
      default: `uvm_fatal(`gfn, $sformatf("Unexpected OTP command %s", otp_cmd.name()))
    endcase
  end
endtask : body
