// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "region_cfg_setting_base.svh"
`include "region_cfg_setting.svh"
`include "region_setting.svh"

`include "rram_ctrl_randomize_vseq.svh"
`include "rram_ctrl_fifo_read_vseq.svh"
`include "rram_ctrl_fifo_write_vseq.svh"

`include "rram_ctrl_sw_vseq.svh"
`include "rram_ctrl_sw_burst_vseq.svh"

`include "rram_ctrl_host_vseq.svh"
`include "rram_ctrl_host_burst_vseq.svh"

`include "rram_ctrl_base_vseq.sv"
`include "rram_ctrl_common_vseq.sv"
`include "rram_ctrl_smoke_vseq.sv"
