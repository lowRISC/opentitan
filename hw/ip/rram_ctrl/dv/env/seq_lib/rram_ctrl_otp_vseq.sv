// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_otp_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_otp_vseq)

  rand otp_ctrl_macro_pkg::otp_macro_data_t wdata;
  rand otp_ctrl_macro_pkg::otp_macro_addr_t addr;
  rand otp_ctrl_macro_pkg::otp_macro_size_t size;
  rand otp_ctrl_macro_pkg::cmd_e otp_cmd;

  // legal sizes are 0, 1, 3 for 16b, 32b, 64b transactions
  constraint size_c {
    size inside {2'b00, 2'b01, 2'b11};
  }

  // solve size before data
  constraint data_c {
    solve size before wdata;
    if (size == 0) {
      // Mask for 16b: e.g., mask out upper bits
      wdata[otp_ctrl_macro_pkg::OtpIfWidth-1 : 16] == '0;
    } else if (size == 1) {
      // Mask for 32b
      wdata[otp_ctrl_macro_pkg::OtpIfWidth-1 : 32] == '0;
    }
  }

  // solve size before addr
  constraint addr_c {
    solve size before addr;
    if (size == 1) {
      addr[0] == 1'b0;
    } else if (size == 3) {
      addr[1:0] == 2'b0;
    }
  }

  // to create more OTP writes with previously written data,
  // bottom addresses are more likely
  localparam int OtpAddrSize = (TotalOtpBytes << otp_ctrl_macro_pkg::OtpAddrShift);
  constraint addr_dist_c {
    addr dist {
      [0 : OtpAddrSize/10 - 1]           := 50, // Bottom 10% gets 50% weight
      [OtpAddrSize/10 : OtpAddrSize - 1] := 50  // Remaining 90% gets 50% weight
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

  for (int k = 0; k < 500; k++) begin
    case (otp_cmd)
      otp_ctrl_macro_pkg::Write:    rram_ctrl_base_vseq::otp_write(addr, size, 1'b0, 1'b1, wdata);
      otp_ctrl_macro_pkg::Read:     rram_ctrl_base_vseq::otp_read(addr, size, 1'b0, 1'b1, rdata);
      otp_ctrl_macro_pkg::WriteRaw: rram_ctrl_base_vseq::otp_write(addr, size, 1'b1, 1'b1, wdata);
      otp_ctrl_macro_pkg::ReadRaw:  rram_ctrl_base_vseq::otp_read(addr, size, 1'b1, 1'b1, rdata);
      otp_ctrl_macro_pkg::Zeroize:  rram_ctrl_base_vseq::otp_zeroize(addr, size, 1'b1, rdata);
      default:;
    endcase

    // Rerandomize variables for next iteration
    if (!randomize()) begin
      `uvm_fatal(`gfn, "Randomization failed!")
    end
  end

  #1ms;

endtask : body
