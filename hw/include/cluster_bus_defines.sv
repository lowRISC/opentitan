/*
 * pulp_cluster_defines.sv
 *
 * Copyright (C) 2013-2018 ETH Zurich, University of Bologna.
 *
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the "License"); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 */

/*
 * Collection of legacy pulp cluster defines.
 *
 */

`define NB_SLAVE  4
`define NB_MASTER 4  // Added one master for C2H TLB configuration port

`define NB_REGION 1

// MSTER PORT TO TCDM
`define MASTER_0_START_ADDR 32'h1000_0000
`define MASTER_0_END_ADDR   32'h101F_FFFF

// MASTER PORT TO PERIPHERAL INTERCONNECT
`define MASTER_1_START_ADDR 32'h1020_0000
`define MASTER_1_END_ADDR   32'h103F_FFFF

`define TCDM_ASSIGN_MASTER(lhs, rhs)       \
    assign lhs.req       = rhs.req;       \
    assign lhs.add       = rhs.add;       \
    assign lhs.wen       = rhs.wen;       \
    assign lhs.wdata     = rhs.wdata;     \
    assign lhs.be        = rhs.be;        \
                                          \
    assign rhs.gnt       = lhs.gnt;       \
    assign rhs.r_valid   = lhs.r_valid;   \
    assign rhs.r_opc     = lhs.r_opc;     \
    assign rhs.r_rdata   = lhs.r_rdata;

`define TCDM_ASSIGN_SLAVE(lhs, rhs)  `TCDM_ASSIGN_MASTER(rhs, lhs)
