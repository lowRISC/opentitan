/*
 * pulp_soc_defines.sv
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
 *  Activate this define to exclude the cluster and speed up the FPGA deployement
 */

// `define EXCLUDE_CLUSTER

/*
 * Collection of legacy pulp cluster defines.
 *
 */

`define CLUSTER_ALIAS
`define PRIVATE_ICACHE
`define HIERARCHY_ICACHE_32BIT
`define FEATURE_ICACHE_STAT

`define FC_FPU 1
`define FC_FP_DIVSQRT 1

// Remove the FPUs in the cluster for FPGA SYNTHESIS
`ifdef FPGA_TARGET_XILINX
  `define CLUST_FPU 0
  `define CLUST_FP_DIVSQRT 0
  `define CLUST_SHARED_FP 0
  `define CLUST_SHARED_FP_DIVSQRT 0
`else
  `define CLUST_FPU 1
  `define CLUST_FP_DIVSQRT 1
  `define CLUST_SHARED_FP 0
  `define CLUST_SHARED_FP_DIVSQRT 0
`endif

//PARAMETRES
`define NB_CLUSTERS   1
`define NB_CORES      8
`define NB_DMAS       4
`define NB_MPERIPHS   1
`define NB_SPERIPHS   10
`define REDMULE       0
