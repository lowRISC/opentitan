// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

package ascon_tl_ul_stim_pkg;

  import ascon_reg_pkg::*;
  import tlul_pkg::*;


  function automatic tl_h2d_t put_full_data (logic [31:0] data, logic [7:0] address);
    tl_h2d_t stimulus = '{
        a_valid:   1'b1,
        a_opcode:  PutFullData,
        a_size:    2'b10,
        a_address: {24'h0, address},
        a_mask:    4'b1111,
        a_data:    data,
        d_ready:   1'b1,
        a_user:    TL_A_USER_DEFAULT,
        default:   '0
    };
    return stimulus;
  endfunction

  function automatic tl_h2d_t get_full_data (logic [7:0] address);
    tl_h2d_t stimulus = '{
        a_valid:   1'b1,
        a_opcode:  Get,
        a_size:    2'b10,
        a_address: {24'h0, address},
        a_mask:    4'b1111,
        a_data:    32'h0,
        d_ready:   1'b1,
        a_user:    TL_A_USER_DEFAULT,
        default:   '0
    };
    return stimulus;
  endfunction

  function automatic tl_d2h_t expect_full_data (logic [31:0] data);
    tl_d2h_t stimulus = '{
        d_valid:  1'b1,
        d_opcode: AccessAckData,
        d_size:   2'b10,
        d_data:   data,
        a_ready:  1'b1,
        d_user:   TL_D_USER_DEFAULT,
        default:  '0
    };
    return stimulus;
  endfunction

//TODO: explain size and mask
//   function automatic tl_h2d_t put_partial_data (logic [31:0] data, logic [7:0] address, int num_bytes);
//     logic [3:0] mask; //= {{(4-num_bytes){1'b0}}, {num_bytes{1'b1}}};
//     logic [1:0] size; // = 2'($clog2(num_bytes));
//     tl_h2d_t stimulus;

//     case (num_bytes)
//         1 : begin
//             mask = 4'b0001;
//             size = 2'b00;
//         end
//         2 : begin
//             mask = 4'b0011;
//             size = 2'b01;
//         end
//         3 : begin
//             mask = 4'b0111;
//             size = 2'b10; //TODO - EXPLAIN ME
//         end
//         default : begin
//             mask = 4'b1111;
//             size = 2'b10;
//         end
//     endcase

//     stimulus = '{
//         a_valid:   1'b1,
//         a_opcode:  PutPartialData,
//         a_size:    size,
//         a_address: {24'h0, address},
//         a_mask:    mask,
//         a_data:    data,
//         d_ready:   1'b1,
//         a_user:    TL_A_USER_DEFAULT,
//         default:   '0
//     };
//     return stimulus;
//   endfunction

endpackage
