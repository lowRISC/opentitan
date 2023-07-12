// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

module pad_alsaqr_pd (
  input logic      OEN,
  input logic      I,
  output logic     O,
  inout wire       PAD,
  input wire [1:0] DRV,
  input wire       SLW,
  input wire       SMT,
  inout wire       PWROK,
  inout wire       IOPWROK,
  inout wire       BIAS,
  inout wire       RETC 
);

/*
    X Unknown
    Z Hi-Z
    H Pull High
    L Pull Low
*/

/*
    OEN I   PAD PEN | PAD O
                    |
    0   0   -   0/1 | 0   0
    0   1   -   0/1 | 1   1
    1   0/1 0   0/1 | -   0
    1   0/1 1   0/1 | -   1
    1   0/1 Z   0   | L   L
    1   0/1 Z   1   | -   X
*/

  wire   PAD_wi;

  bufif0 (PAD, I, OEN);
  buf    (O, PAD);
  bufif0 (PAD_wi, 1'b0, 1'b0);
  rpmos  (PAD, PAD_wi, 1'b0);

endmodule

module pad_alsaqr_pu (
  input logic      OEN,
  input logic      I,
  output logic     O,
  inout wire       PAD,
  input wire [1:0] DRV,
  input wire       SLW,
  input wire       SMT,
  inout wire       PWROK,
  inout wire       IOPWROK,
  inout wire       BIAS,
  inout wire       RETC 
);

/*
    X Unknown
    Z Hi-Z
    H Pull High
    L Pull Low
*/

/*
    OEN I   PAD PEN | PAD O
                    |
    0   0   -   0/1 | 0   0
    0   1   -   0/1 | 1   1
    1   0/1 0   0/1 | -   0
    1   0/1 1   0/1 | -   1
    1   0/1 Z   0   | H   H
    1   0/1 Z   1   | -   X
*/

  wire   PAD_wi;

  bufif0 (PAD, I, OEN);
  buf    (O, PAD);
  bufif0 (PAD_wi, 1'b1, 1'b0);
  rpmos  (PAD, PAD_wi, 1'b0);

endmodule

module pad_alsaqr (
  input logic      OEN,
  input logic      I,
  output logic     O,
  inout wire       PAD,
  input wire [1:0] DRV,
  input wire       PUEN,                       
  input wire       SLW,
  input wire       SMT,
  inout wire       PWROK,
  inout wire       IOPWROK,
  inout wire       BIAS,
  inout wire       RETC 
);

/*
    X Unknown
    Z Hi-Z
    H Pull High
    L Pull Low
*/

/*
    OEN I   PAD PEN | PAD O
                    |
    0   0   -   0/1 | 0   0
    0   1   -   0/1 | 1   1
    1   0/1 0   0/1 | -   0
    1   0/1 1   0/1 | -   1
    1   0/1 Z   0   | H   H
    1   0/1 Z   1   | -   X
*/

  wire   PAD_wi;

  bufif0 (PAD, I, OEN);
  buf    (O, PAD);
  bufif0 (PAD_wi, ~PUEN, 1'b0);
  rpmos  (PAD, PAD_wi, 1'b0);

endmodule
