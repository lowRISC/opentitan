# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is used as an "after_load" file for the otbn_sec_cm job

proc move_to_task {task_name assert_name} {
    task -edit ${task_name} -copy "${assert_name}*"
    assert -disable ${assert_name}
}

# There are various request and response FIFOs in the design and there are top-level checks (in
# otbn.sv) that make sure that if any of those FIFOs reports an error then an alert comes out.
#
# These errors are generated if the counter in the FIFO gets corrupted. Normally, this is made
# possible by black-boxing the contents of prim_count (which gets done in fpv.tcl if the TASK
# environment variable is FpvSecCm). Unfortunately, that doesn't work if you have a one-entry FIFO.
#
# Rather than trying to black-box the (rather trivial) body of the counter in this case, use a
# stopat on the err_o signals.
#
# Call the task "pre0", which means that fpv.tcl will try to prove it, before just proving the
# FpvSecCm task that it would do otherwise.
task -create pre0
stopat -task pre0 "u_tlul_adapter_sram_dmem.u_rspfifo.err_o"
move_to_task pre0 "otbn.FpvSecCmDmemRspFifoFullCheck_A"
stopat -task pre0 "u_tlul_adapter_sram_dmem.u_sramreqfifo"
move_to_task pre0 "otbn.FpvSecCmDmemSramReqFifoFullCheck_A"
stopat -task pre0 "u_tlul_adapter_sram_dmem.u_reqfifo"
move_to_task pre0 "otbn.FpvSecCmDmemReqFifoFullCheck_A"
stopat -task pre0 "u_tlul_adapter_sram_imem.u_rspfifo.err_o"
move_to_task pre0 "otbn.FpvSecCmImemRspFifoFullCheck_A"
stopat -task pre0 "u_tlul_adapter_sram_imem.u_sramreqfifo"
move_to_task pre0 "otbn.FpvSecCmImemSramReqFifoFullCheck_A"
stopat -task pre0 "u_tlul_adapter_sram_imem.u_reqfifo"
move_to_task pre0 "otbn.FpvSecCmImemReqFifoFullCheck_A"

# Make the runner try to prove these assertions too
set pre_phases 1
