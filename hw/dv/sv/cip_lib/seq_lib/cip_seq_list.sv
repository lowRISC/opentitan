// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// customized tl_seq_item for cmd integrity
`include "cip_tl_seq_item.sv"

// customized tl sequences to address integrity
`include "cip_tl_host_single_seq.sv"
`include "cip_tl_device_seq.sv"

// vseqs
`include "cip_base_vseq.sv"
