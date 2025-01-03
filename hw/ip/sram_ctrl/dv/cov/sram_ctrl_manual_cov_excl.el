// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// The following exclusions were manually added.

// The `pending_txn_cnt` never can have a other value than 1 in the `StByteWrReadBackInit` state.
// The FSM follows the following path: `StWaitRd` -> `StWriteCmd` -> `StByteWrReadBackInit`.
// Observations:
// - In all of these states, we are stalling the host with `stall_host = 1'b1`.
// - When switching from `StWaitRd` -> `StWriteCmd`, `pending_txn_cnt == 1`.
// - `pending_txn_cnt` is the depth of the `u_sync_fifo_a_size` FIFO
//
// As we are stalling the host, we cannot push to the  `u_sync_fifo_a_size` FIFO to increment
// `pending_txn_cnt`. Stalling the host puts a_ack, which is the push port of the FIFO, to 1'b0
// as tl_o.a_ready = ~stall_host.
//
// Popping the FIFO in the `StWaitRd` state is not possible as we set `rd_wait = 1'b1`, which
// puts `tl_o.d_valid = 1'b0` and therefore also `d_ack = 1'b0`.
// Popping the FIFO in the `StWriteCmd` state is not possible as we trigger a write in this
// state and immediately get the `sram_a_ack` (the SRAM always can accept a read/write operation)
// and the response `tl_sram_i.d_valid` cannot be in the same cycle. This again puts
// `tl_o.d_valid = 1'b0` and therefore also `d_ack = 1'b0`.
//
// Hence, when we are entering the `StByteWrReadBackInit` state, `pending_txn_cnt == 1`. In this
// state, we immediately switch to the `StByteWrReadBack` or `StByteWrReadBackDWait` state.
CHECKSUM: "432309571 3872208598"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
Condition 4 "2750535368" "(gen_integ_handling.pending_txn_cnt == 2'(1)) 1 -1"
CHECKSUM: "432309571 1160560609"
INSTANCE: tb.dut.u_tlul_adapter_sram.u_sram_byte
Branch 1 "2309313685" "gen_integ_handling.state_q" (30) "gen_integ_handling.state_q StByteWrReadBackInit ,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,-,0,-,-,-,-,-,-,-,-,-"
