// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "sram_ctrl_base_vseq.sv"
`include "sram_ctrl_smoke_vseq.sv"
`include "sram_ctrl_common_vseq.sv"
`include "sram_ctrl_throughput_vseq.sv"
`include "sram_ctrl_multiple_keys_vseq.sv"
`include "sram_ctrl_bijection_vseq.sv"
`include "sram_ctrl_stress_pipeline_vseq.sv"
`include "sram_ctrl_lc_escalation_vseq.sv"
`include "sram_ctrl_access_during_key_req_vseq.sv"
`include "sram_ctrl_executable_vseq.sv"
`include "sram_ctrl_regwen_vseq.sv"
`include "sram_ctrl_ram_cfg_vseq.sv"
`include "sram_ctrl_stress_all_vseq.sv"
`include "sram_ctrl_readback_err_vseq.sv"
