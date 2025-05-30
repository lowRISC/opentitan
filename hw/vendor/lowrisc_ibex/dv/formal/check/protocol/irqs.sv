// Copyright lowRISC contributors.
// Copyright 2024 University of Oxford, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// Original author: Louis-Emile Ploix
// SPDX-License-Identifier: Apache-2.0

/*
The following give the protocol that IRQs must follow.
*/

// The Sail does not specify either of these
NoNMI: assume property (~irq_nm_i);
NoFastIRQ: assume property (~(|irq_fast_i));

// IRQs must remain active until they are cleared by some MMIO memory request
// The alternative is that IRQs disappear after just one cycle or something
MIPFair: assume property (
	(|`CSR.mip) |=>
		$past(`CSR.mip) == ($past(`CSR.mip) & `CSR.mip) || data_gnt_i
);

`define WFI_BOUND 20
// If we are asleep we must eventually wake up. This is validated by the WFIStart assumption,
// which ensures that this is actually possible. We make the time bounded instead of s_eventually
// for conclusivity purposes. This can be commented out if you don't care about liveness.
WFIWakeUp: assume property (`IDC.ctrl_fsm_cs == SLEEP |-> ##[0:`WFI_BOUND] `IDC.irq_pending_i);
