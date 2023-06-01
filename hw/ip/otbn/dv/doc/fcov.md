# OTBN functional coverage

We distinguish between *architectural* and *micro-architectural* functional coverage.
The idea is that the points that go into architectural coverage are those that a DV engineer could derive by reading the block specification.
The points that go into micro-architectural coverage are those that require knowledge of the block's micro-architecture.
Some of these will come from DV engineers; others from the block's designers.
These two views are complementary and will probably duplicate coverage points.
For example, an architectural coverage point might be "the processor executed `ADDI` and the result overflowed".
This might overlap with something like "the `overflow` signal in the ALU was true when adding".

# Block-based coverage

## Call stack

The [call stack](../README.md#call-stack) is exposed as a special register behind `x1`.
It has a bounded depth of 8 elements.
We expect to see the following events:

- Push to the call stack
- Pop from the call stack
- Push and pop from the call stack on a single instruction
- An instruction with multiple reads from `x1`

All four of these events should be crossed with the three states of the call stack: empty, partially full, and full.

> Coverage for these points is tracked in the `call_stack_cg` covergroup.
> We track all possible combinations of push/pop flags (8 possibilities) in `flags_cp`.
> The 3 different fullness states are tracked as `fullness_cp`.
> These are then crossed to give `flags_fullness_cross`.

## Loop stack

The [loop stack](../README.md#loop-stack) is accessed by executing `LOOP` and `LOOPI` instructions.
Events concerning the start of loops are tracked at those instructions, but we can't track things like loop completion there.

> Coverage for these points is tracked with cover properties in the `otbn_loop_if` interface.

We expect to:
- Complete a loop.
  Tracked as `LoopEnd_C`.
- Complete the last loop on the stack (emptying it) after the stack has been full.
  Tracked as `FullToEmpty_C`.
- Complete a loop with one instruction and an iteration count of one.
  Tracked as `ShortestLoop_C`.
- Complete a loop with the maximal number of iterations.
  Obviously, this isn't a reasonable thing to do for real in a test (there's a 32-bit iteration counter!).
  The testbench will have to force a signal to skip past some iterations.
  Tracked as `MaximalLoop_C`.
- Run through a "badly nested" loop, where the body contains the final instruction from an outer loop (checking that we don't wrongly skip back).
  Tracked as `BadNestingEnd_C` and `BadNestingMiddle_C`.
- Jump into a loop body from outside.
  Tracked as `JumpIntoLoop_C`.
- Jump/branch to the final instruction of a loop
  Tracked as `JumpToLoopEnd_C`.

## CSRs and WSRs

Accesses to CSRs and WSRs are tracked in the coverage for the instructions that access them.
See [CSRRS](#csrrs) and [CSRRW](#csrrw) for CSRs; [BN.WSRR](#bnwsrr) and [BN.WSRW](#bnwsrw) for WSRs.

## Random numbers

Random numbers are exposed to OTBN code through the `RND` and `URND` CSRs and WSRs.
A new random number can be prefetched for `RND` with the `RND_PREFETCH` CSR.

We track uses of each of these CSRs and WSRs in the instructions that access them.
See [CSRRS](#csrrs) and [CSRRW](#csrrw) for CSRs; [BN.WSRR](#bnwsrr) and [BN.WSRW](#bnwsrw) for WSRs.
However, we also want to see some interactions between `RND` and `RND_PREFETCH`.
These are all tracked with cover properties in `otbn_rnd_if.sv`.

Specifically, we expect to see:

- An read of `RND` (either CSR or WSR) before any write to `RND_PREFETCH`.
  This is tracked with the `RndWithNoPrefetch_C` cover property.
- Two consecutive writes to `RND_PREFETCH` without a random value arriving between.
  This is tracked with the `PrefetchPrefetch_C` cover property.
- Two consecutive writes to `RND_PREFETCH`, where a random value arrives between them.
  This is tracked with the `FullPrefetch_C` cover property.
- A write to `RND_PREFETCH` followed by a read from `RND` after the random value has arrived.
  This is tracked with the `FullRead_C` cover property.
- A write to `RND_PREFETCH` followed by a read from `RND` before the random value has arrived.
  This is tracked with the `PrefetchingRead_C` cover property.



## Flags

Each flag in each flag group should be set to one from zero by some instruction.
Similarly, each flag in each flag group should be cleared to zero from one by some instruction.

> These events are tracked in `flag_write_cg`.
> This is called from `on_insn()` once for each flag group that is being written.
> The covergroup contains eight coverpoints (for each flag set and cleared).
> These are then crossed with the flag group.

## Instruction counter

See the instruction counter saturate.

> This is tracked in the `insn_cnt_if` interface with the `InsnCntSaturated_C` cover property.

## Key sideload interface

We expect to see reads from this interface (both when a key is present and when it is not).
The coverage for these reads is tracked in the [BN.WSRR](#bnwsrr) instruction which does the reading.

## Integrity protection

The contents of IMEM and DMEM, the register file, and other pieces of internal state are protected by ECC integrity bits.
We want to see errors/alerts caused by corrupting each of these pieces of state.
Rather than tracking this with functional coverage, we rely on testplan entries.

See the `mem_integrity` and `internal_integrity` entries in the testplan for more details.

## Lifecycle escalation

The lifecycle controller can send a "lifecycle escalation" signal to tell OTBN to clear its internal state and to raise its own fatal error.

We expect to see this happen.
However, we don't track coverage for this explicitly since it's handled at the testplan level (with the `lc_escalation` testpoint).

## Error promotion

If the `CTRL.software_errs_fatal` field is set then a software error which would normally trigger a recoverable alert will trigger a fatal alert.
We expect to see each software error triggered and upgraded to a fatal alert.

This is tracked in the `promoted_err_cg` covergroup.

Note that we already track seeing each software error triggered (but not upgraded) with the coverage for `ERR_BITS` in the [external
CSRs](#external-bus-accessible-csrs) section below.

## Scratchpad memory

A portion of DMEM is inaccessible from the bus.
We want to see accesses (read and write) to both endpoints of the inaccessible portion of DMEM when OTBN is in an idle state (so would otherwise allow them).
These are tracked in the `addr_cp` coverpoint in `scratchpad_writes_cg`.

We also want to see a successful write to the top word of accessible DMEM.
We don't track that explicitly, since it is covered by the `otbn_mem_walk` test.

## External (bus-accessible) CSRs

The OTBN block exposes functionality to a bus host through bus-accessible CSRs.
Behavior of some CSRs depends on [OTBN's operational state](../../doc/theory_of_operation.md#operational-states).

For every CSR (no matter its access restrictions), we want to see an attempt to read it and an attempt to write it.
The CSRs are tracked in covergroups based on the CSR name, with the format: `ext_csr_<name>_cg`.
Each has an `access_type_cp` coverpoint which will track read and write attempts.

If writes to the CSR behave differently depending on the operational state, we cross attempts to write with the operational state.
For CSRs like `CMD`, which have an immediate effect, this is easy to handle.
For CSRs that need a follow-up read to check their value, this is handled with the `ext_csr_wr_operational_state_cg` covergroup.
We track the last write state for a CSR and then sample that covergroup when the value is read back.

### CMD

Coverage is tracked in the `ext_csr_cmd_cg` covergroup.

We want to see all valid commands (plus at least one invalid command) being written in each operational state.
This ensures commands are ignored as expected when OTBN is busy or locked.
It also ensures that bad commands are ignored as expected.

The `cmd_cp` bin covers the different types of commands.
It is crossed with the operational state in `cmd_state_cross`.
We check that we see a read (as well as a write) with the `access_type_cp` coverpoint.

### CTRL

Coverage is tracked in the `ext_csr_ctrl_cg` covergroup.

We expect to see this written with each of zero and one in the idle state (where it should take an effect).
This is tracked in `value_cp`.

We check that we see a read (as well as a write) with the `access_type_cp` coverpoint.

We expect to see this written in each operational state, tracked with the `ext_csr_wr_operational_state_cg` covergroup.

We also want to see this be set back to zero after an operation has run with it set to one, then trigger a software error.
This ensures that we can indeed disable the fatal error promotion mechanism.

**TODO: This part is not currently tracked.**

### STATUS

Coverage is tracked in the `ext_csr_status_cg` covergroup.

We want to see a read of all valid status codes.
This is tracked in `status_cp`.
We check that we see a write (as well as a read) with the `access_type_cp` coverpoint.

### ERR_BITS

Coverage is tracked in the `ext_csr_err_bits_cg` covergroup.

We want to see that every valid bit is read at least once.
This is tracked in coverpoints with names of the form `err_bits_<errcode>_cp`.
We also want to see a read in each operational state.
This is tracked in `state_cp`.

We want to see a write to this register in each operational state when it was previously nonzero.
This checks that the clearing behaviour works properly.
We don't have to follow up with another read because we've got continuous checks that the RTL value of this register matches the ISS.
This is tracked in `clear_state_cross`.

We want to see both reads and writes.
This is tracked in `access_type_cp`.

### FATAL\_ALERT_CAUSE

Coverage is tracked in the `ext_csr_fatal_alert_cause_cg` covergroup.

We want to see that every valid bit is read at least once.
This is tracked in coverpoints with names of the form `fatal_alert_cause_<errcode>_cp`.
We also want to see a read in each operational state.
This is tracked in `state_cp`.

We check that we see a write (as well as a read) with the `access_type_cp` coverpoint.

### INSN_CNT

Coverage is tracked in the `ext_csr_insn_cnt_cg` covergroup.

We want to see a read returning a zero and a non-zero value.
This is tracked in `insn_cnt_cp`.
We also want to see a read in every operational state.
This is tracked in `state_cp`.

We want to see a write to this register in each operational state when it was previously nonzero.
This checks that the clearing behaviour works properly.
We don't have to follow up with another read because we've got continuous checks that the RTL value of this register matches the ISS.
This is tracked in `clear_state_cross`.

### LOAD_CHECKSUM

We want to see a write to the register (that changes its value), followed by an update caused by writing to memory, finally followed by a read of the register value.
This is tracked in the `ext_csr_load_checksum_wur_cg` covergroup.

We also want to see a write in every operational state, followed by a read before the next write.
This is tracked in the `ext_csr_wr_operational_state_cg` covergroup.

# Instruction-based coverage

As a processor, much of OTBN's coverage points are described in terms of instructions being executed.
Because OTBN doesn't have a complicated multi-stage pipeline or any real exception handling, we don't track much temporal information (such as sequences of instructions).

As well as instruction-specific coverage points detailed below, we include a requirement that each instruction is executed at least once.

For any instruction with one or more immediate fields, we require "toggle coverage" for those fields.
That is, we expect to see execution with each bit of each immediate field being zero and one.
We also expect to see each field with values `'0` and `'1` (all zeros and all ones).
If the field is treated as a signed number, we also expect to see it with the extremal values for its range (just the MSB set, for the most negative value; all but the MSB set, for the most positive value).

> The code to track this is split by encoding schema in `otbn_env_cov`.
> Each instruction listed below will specify its encoding schema.
> Each encoding schema then has its own covergroup.
> Rather than tracking toggle coverage as described above, we just track extremal values in a coverpoint.
> This also implies toggle coverage for both signed and unsigned fields.
> For unsigned fields of width `N`, the extremal values are `0` and `(1 << N) - 1`, represented by the bits `'0` and `'1` respectively.
> For signed fields of width `N+1`, the extremal values are `-(1 << N)` and `(1 << N) - 1`.
> These are represented by `{1'b1, {N{1'b0}}}` and `{1'b0, {N{1'b1}}}`: again, these toggle all the bits.
> For example, `beq` uses the `B` schema, which then maps to the `enc_b_cg` covergroup.
> This encoding schema's `OFF` field is tracked with the `off_cp` coverpoint.
> Finally, the relevant cross is called `off_cross`.

For any instruction that reads from or writes to a GPR, we expect to see that operand equal to `x0`, `x1` and an arbitrary register in the range `x2 .. x31`.
We don't have any particular coverage requirements for WDRs (since all of them work essentially the same).

> As for immediates, the code to track this is split by encoding schema in `otbn_env_cov`.
> Each register field gets a coverpoint with the same name, defined with the `DEF_GPR_CP` helper macro.
> If the encoding schema has more than one instruction, the coverpoint is then crossed with the mnemonic, using the `DEF_MNEM_CROSS` helper macro.
> For example, `add` is in the `enc_bnr_cg` covergroup.
> This encoding schema's `GRD` field is tracked with the `grd_cp` coverpoint.
> Finally, the relevant cross is called `grd_cross`.

For any source GPR or WDR, we require "toggle coverage" for its value.
For example, `ADD` reads from its `grs1` operand.
We want to see each of the 32 bits of that operand set and unset (giving 64 coverage points).
Similarly, `BN.ADD` reads from its `wrs1` operand.
We want to see each of the 256 bits of that operand set and unset (giving 512 coverage points).

> Again, the code to track this is split by encoding schema in `otbn_env_cov`.
> The trace interface takes a copy of GPR and WDR read data.
> The relevant register read data are then passed to the encoding schema's covergroup in the `on_insn` method.
> To avoid extremely repetitive code, the actual coverpoints and crosses are defined with the help of macros.
> The coverpoints are named with the base-2 expansion of the bit in question.
> For example, the cross in the `enc_bnr_cg` that tracks whether we've seen both values of bit 12 for the `grs1` operand is called `grs1_01100_cross` (since 12 is `5'b01100`).

If an instruction can generate flag changes, we expect to see each flag that the instruction can change being both set and cleared by the instruction.
This needn't be crossed with the two flag groups (that's tracked separately in the "Flags" block above).
For example, `BN.ADD` can write to each of the flags `C`, `M`, `L` and `Z`.
This paragraph implies eight coverage points (four flags times two values) for that instruction.

> Again, the code to track this is split by encoding schema in `otbn_env_cov`.
> The trace interface takes a copy of flag write data.
> It doesn't bother storing the flag write flags, since these are implied by the instruction anyway.
> There is a coverage coverpoint tracking both values for each of the flags that can be written.
> This is then crossed with the instruction mnemonic.
> For example, the coverpoint for the C flag (bit zero) in the `bnaf` encoding used by `BN.ADD` is called `flags_00_cp`.
> Some instructions only write the `M`, `L` and `Z` flags.
> These are found in the `bna`, `bnan`, `bnaqs` and `bnaqw` encoding groups.
> For these instructions, we only track bits `1`, `2` and `3` of the flags structure.

For any instruction that can cause multiple errors in a single cycle, we expect to see each possible combination of errors.
This is described in more detail in the per-instruction text below.
If an instruction below doesn't describe triggering multiple errors, that means we don't think it's possible.

## ADD

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_addsub_cg` (also used for `SUB`).

- Cross the three possible signs (negative, zero, positive) for each input operand (giving 9 points).
  Tracked as `sign_a_sign_b_cross`.

## ADDI

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_addi_cg`.

- Cross the three possible signs (negative, zero, positive) for each input operand (giving 9 points).
  Tracked as `sign_cross`.

## LUI

This instruction uses the `U` encoding schema, with covergroup `enc_u_cg`.
There are no further coverage points.

## SUB

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_addsub_cg`.

- Cross the three possible signs (negative, zero, positive) for each input operand (giving 9 points).
  Tracked as `sign_a_sign_b_cross`.

## SLL

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_sll_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the top bit set.
  Tracked as `shift15_cp`.

## SLLI

This instruction uses the `Is` encoding schema, with covergroup `enc_is_cg`.
The instruction-specific covergroup is `insn_slli_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the top bit set.
  Tracked as `shift15_cp`.

## SRL

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_srl_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the bottom bit set.
  Tracked as `shift15_cp`.
  Note that this point also checks that we're performing a logical, rather than arithmetic, right shift.

## SRLI

This instruction uses the `Is` encoding schema, with covergroup `enc_is_cg`.
The instruction-specific covergroup is `insn_srli_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the bottom bit set.
  Tracked as `shift15_cp`.
  Note that this point also checks that we're performing a logical, rather than arithmetic, right shift.

## SRA

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_sra_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the bottom bit set.
  Tracked as `shift15_cp`.
  Note that this point also checks that we're performing an arithmetic, rather than logical, right shift.

## SRAI

This instruction uses the `Is` encoding schema, with covergroup `enc_is_cg`.
The instruction-specific covergroup is `insn_srai_cg`.

- A shift of a nonzero value by zero.
  Tracked as `nz_by_z_cp`.
- A shift of a value by `0x1f` which leaves the bottom bit set.
  Tracked as `shift15_cp`.
  Note that this point also checks that we're performing an arithmetic, rather than logical, right shift.

## AND

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just AND'ing things with zero)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## ANDI

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just AND'ing things with zero)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## OR

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just OR'ing things with `'1`)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## ORI

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just OR'ing things with `'1`)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## XOR

This instruction uses the `R` encoding schema, with covergroup `enc_r_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just XOR'ing things with zero)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## XORI

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_log_binop_cg` (shared with other logical binary operations).

- Toggle coverage of the output result, not to `x0` (to ensure we're not just XOR'ing things with zero)
  Tracked as `write_data_XXXXX_cross`, where `XXXXX` is the base-2 representation of the bit being checked.

## LW

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_xw_cg` (shared with `SW`).

- Load from a valid address, where `<grs1>` is above the top of memory and a negative `<offset>` brings the load address in range.
  Tracked as `oob_base_neg_off_cross`.
- Load from a valid address, where `<grs1>` is negative and a positive `<offset>` brings the load address in range.
  Tracked as `neg_base_pos_off_cross`.
- Load from address zero.
  Tracked as `addr0_cross`.
- Load from the top word of memory
  Tracked as `top_addr_cross`.
- Load from an invalid address (aligned but above the top of memory)
  Tracked as `oob_addr_cross`.
- Load from a calculated negative invalid address (aligned but unsigned address exceeds the top of memory)
  Tracked as `oob_addr_neg_cross`.
- Load from a "barely invalid" address (just above the top of memory)
  Tracked as `barely_oob_addr_cross`.
- Misaligned address tracking.
  Track loads from addresses that are in range for the size of the memory.
  Cross the different values modulo 4 for `grs1` and `offset`.
  Tracked as `align_cross`.

It is possible for LW to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, invalid DMEM address, and overflow call stack.
It's not possible to under- and overflow the call stack in a single cycle.
Similarly, if we underflow the call stack, we won't have an address at all (valid or otherwise).
This leaves a single combination to check:

- Overflow the call stack when loading from an invalid address.
  Tracked as `overflow_cs_invalid_addr_cp`.

## SW

This instruction uses the `I` encoding schema, with covergroup `enc_s_cg`.
The instruction-specific covergroup is `insn_xw_cg` (shared with `LW`).

- Store to a valid address, where `<grs1>` is above the top of memory and a negative `<offset>` brings the load address in range.
  Tracked as `oob_base_neg_off_cross`.
- Store to a valid address, where `<grs1>` is negative and a positive `<offset>` brings the load address in range.
  Tracked as `neg_base_pos_off_cross`.
- Store to address zero
  Tracked as `addr0_cross`.
- Store to the top word of memory
  Tracked as `top_addr_cross`.
- Store to an invalid address (aligned but above the top of memory)
  Tracked as `oob_addr_cross`.
- Store to a calculated negative invalid address (aligned but unsigned address exceeds the top of memory)
  Tracked as `oob_addr_neg_cross`.
- Store to a "barely invalid" address (aligned but overlapping the top of memory)
  Tracked as `barely_oob_addr_cross`.
- Misaligned address tracking.
  Track stores from addresses that are in range for the size of the memory.
  Cross the different values modulo 4 for `grs1` and `offset`.
  Tracked as `align_cross`.

It is possible for SW to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack and invalid DMEM address.
These can happen together, giving a single combination to check:

- Underflow the call stack when reading the value to be stored and try to write it to an invalid address.
  Tracked as `underflow_cs_invalid_addr_cp`.

## BEQ

This instruction uses the `B` encoding schema, with covergroup `enc_b_cg`.
The instruction-specific covergroup is `insn_bxx_cg` (shared with `BNE`).

All points should be crossed with branch taken / branch not taken.

- See each branch direction (forwards, backwards, current address).
  Tracked as `eq_dir_cross`.
- Branch to a misaligned address (offset not a multiple of 4)
  PC is always 4-bit aligned and offset is a multiple of 2 by definition.
  Therefore the only misalignment would be by setting the second bit of the offset to 1.
  Offset alignment is tracked in `eq_offset_align_cross`.
- Branch forwards to an invalid address, above the top of memory
  Tracked as `eq_oob_cross`.
- Branch backwards to an invalid address (wrapping past zero)
  Tracked as `eq_neg_cross`.
- Branch instruction at end of a loop.
  Tracked as `eq_at_loop_end_cross` (which also crosses with whether the branch was taken or not).

The "branch to current address" item is problematic if we want to take the branch.
Probably we need some tests with short timeouts to handle this properly.

It is possible for BEQ to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, bad target address, and branch at end of loop.
Since the target address check only triggers if the branch is taken, which requires a value for comparison, it's not possible to underflow the call stack and see a bad target address at the same time.
This leaves two possible combinations:

- Underflow the call stack in a branch at the end of a loop.
  Tracked as `underflow_at_loop_end_cross`.
- Take a branch to an invalid address where the branch instruction is at the end of a loop.
  Tracked as `bad_addr_at_loop_end_cross`.

## BNE

This instruction uses the `B` encoding schema, with covergroup `enc_b_cg`.
The instruction-specific covergroup is `insn_bxx_cg` (shared with `BEQ`).

All points should be crossed with branch taken / branch not taken.

- See each branch direction (forwards, backwards, current address).
  Tracked as `eq_dir_cross`.
- Branch to a misaligned address (offset not a multiple of 4)
  PC is always 4-bit aligned and offset is a multiple of 2 by definition.
  Therefore the only misalignment would be by setting the second bit of the offset to 1.
  Offset alignment is tracked in `eq_offset_align_cross`.
- Branch forwards to an invalid address, above the top of memory
  Tracked as `eq_oob_cross`.
- Branch backwards to an invalid address (wrapping past zero)
  Tracked as `eq_neg_cross`.
- Branch instruction at end of a loop.
  Tracked as `eq_at_loop_end_cross` (which also crosses with whether the branch was taken or not).

The "branch to current address" item is problematic if we want to take the branch.
Probably we need some tests with short timeouts to handle this properly.

It is possible for BNE to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, bad target address, and branch at end of loop.
Since the target address check only triggers if the branch is taken, which requires a value for comparison, it's not possible to underflow the call stack and see a bad target address at the same time.
This leaves two possible combinations:

- Underflow the call stack in a branch at the end of a loop.
  Tracked as `underflow_at_loop_end_cross`.
- Take a branch to an invalid address where the branch instruction is at the end of a loop.
  Tracked as `bad_addr_at_loop_end_cross`.

## JAL

This instruction uses the `J` encoding schema, with covergroup `enc_j_cg`.
The instruction-specific covergroup is `insn_jal_cg`.

- See each jump direction (forwards, backwards, current address).
  Tracked as `dir_cp`.
- Jump to a misaligned address (offset not a multiple of 4)
  Offset alignments are tracked in `offset_align_cp`.
- Jump forwards to an invalid address, above the top of memory
  Tracked as `oob_cp`.
- Jump backwards to an invalid address (wrapping past zero)
  Tracked as `neg_cp`.
- Jump when the current PC is the top word in IMEM.
  Tracked as `from_top_cp`.
- Jump instruction at end of a loop.
  Tracked as `at_loop_end_cp`.

Note that the "jump to current address" item won't be a problem to test since it will quickly overflow the call stack.

It is possible for JAL to trigger multiple errors in a single cycle.
The possible errors are: overflow call stack, bad target address, and jump at end of loop.
All four combinations are possible:

- Overflow call stack when jumping to an invalid address.
  Tracked as `overflow_and_invalid_addr_cp`.
- Overflow call stack from a jump at the end of a loop.
  Tracked as `overflow_at_loop_end_cp`.
- Jump to an invalid address from the end of a loop.
  Tracked as `invalid_addr_at_loop_end_cp`.
- Overflow call stack when jumping to an invalid address from the end of a loop.
  Tracked as `overflow_and_invalid_addr_at_loop_end_cp`.

## JALR

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_jalr_cg`.

- See each jump offset (forwards, backwards, zero).
  Tracked as `off_dir_cp`.
- Jump with a misaligned base address which `<offset>` aligns.
  Pairs of base address / offset alignments tracked in `align_cross`.
- Jump with a large base address which wraps to a valid address by adding a positive `<offset>`.
  Tracked as `pos_wrap_cp`.
- Jump with a base address just above top of IMEM but with a negative `<offset>` to give a valid target.
  Tracked as `sub_cp`.
- Jump with a negative offset, wrapping to give an invalid target.
  Tracked as `neg_wrap_cp`.
- Jump to an aligned address above top of IMEM.
  Tracked as `oob_cp`.
- Jump to current address.
  Tracked as `self_cp`.
- Jump when the current PC is the top word in IMEM.
  Tracked as `from_top_cp`.
- Jump instruction at end of a loop.
  Tracked as `at_loop_end_cp`.

Note that the "jump to current address" item won't be a problem to test since it will quickly over- or underflow the call stack, provided `<grd>` and `<grs1>` aren't both `x1`.

It is possible for JALR to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, overflow call stack, bad target address, and jump at end of loop.
If we underflow the call stack, we can't also overflow it, nor do we have a target address.
This means the only error that can occur in combination with underflowing the call stack is a jump at the end of a loop.
Otherwise, all other combinations are possible.

- Underflow call stack in a jump instruction at the end of a loop.
  Tracked as `underflow_at_loop_end_cp`.
- Overflow call stack when jumping to an invalid address.
  Tracked as `overflow_and_bad_addr_cp`.
- Overflow call stack from a jump at the end of a loop.
  Tracked as `overflow_at_loop_end_cp`.
- Jump to an invalid address from the end of a loop.
  Tracked as `bad_addr_at_loop_end_cp`.
- Overflow call stack when jumping to an invalid address from the end of a loop.
  Tracked as `overflow_and_bad_addr_at_loop_end_cp`.

## CSRRS

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_csrrs_cg`.

- Write with a non-zero `bits_to_set` to each valid CSR.
- Write to an invalid CSR.

These points are tracked with `csr_cross` in `insn_csrrs_cg`.
It crosses `csr_cp` (which tracks each valid CSR, plus an invalid CSR) with `bits_to_set_cp` (which tracks whether `bits_to_set` is nonzero).

It is possible for CSRRS to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, overflow call stack, and invalid CSR.
It's not possible to under- and overflow the call stack in a single cycle.
The other two combinations are possible:

- Underflow the call stack and access an invalid CSR
  Tracked as `underflow_with_bad_csr_cp`.
- Overflow the call stack and access an invalid CSR
  Tracked as `overflow_with_bad_csr_cp`.

## CSRRW

This instruction uses the `I` encoding schema, with covergroup `enc_i_cg`.
The instruction-specific covergroup is `insn_csrrw_cg`.

- Write to every valid CSR with a `<grd>` other than `x0`.
- Write to every valid CSR with `<grd>` equal to `x0`.
- Write to an invalid CSR.

These points are tracked with `csr_cross` in `insn_csrrw_cg`.
It crosses `csr_cp` (which tracks each valid CSR, plus an invalid CSR) with `grd_cp_to_set_cp` (which tracks whether `grd` is equal to `x0`.

It is possible for CSRRW to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, overflow call stack, and invalid CSR.
It's not possible to under- and overflow the call stack in a single cycle.
The other two combinations are possible:

- Underflow the call stack and access an invalid CSR
  Tracked as `underflow_with_bad_csr_cp`.
- Overflow the call stack and access an invalid CSR
  Tracked as `overflow_with_bad_csr_cp`.

## ECALL

This instruction uses the `I` encoding schema, but with every field set to a fixed value.
Encoding-level coverpoints are tracked in covergroup `enc_ecall_cg`.

No special coverage points for this instruction.

## LOOP

This instruction uses the `loop` encoding schema, with covergroup `enc_loop_cg`.
The instruction-specific covergroup is `insn_loop_cg`.

- Loop with a zero iteration count (causing an error)
  Tracked as the `'0` bin of `iterations_cp`.
- Loop with a count of `'1` (the maximal value)
  Tracked as the `'1` bin of `iterations_cp`.
- Loop when the loop end address would be above the top of memory.
  Tracked as `oob_end_addr_cp`.
- Loop when the loop stack is full, causing an overflow.
  Tracked as `loop_stack_fullness_cp`.
- Loop at the end of a loop.
  Tracked as `at_loop_end_cp`.
- Duplicate loop end address, matching top of stack
  Tracked as `duplicate_loop_end_cp`.

It is possible for LOOP to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack, zero loop count, and loop at end of loop.
It's not possible to underflow the call stack and see a zero loop count (because if we underflow the call stack, we have no loop count), so we get two pairs:

- Underflow the call stack and loop at the end of a loop.
  Tracked as `underflow_at_loop_end_cp`.
- Loop with a zero loop count at the end of a loop.
  Tracked as `zero_count_at_loop_end_cp`.

## LOOPI

This instruction uses the `loopi` encoding schema, with covergroup `enc_loopi_cg`.
The instruction-specific covergroup is `insn_loopi_cg`.

- Loop with a zero iteration count (causing an error)
  This is tracked in `enc_loopi_cg` with the `'0` bin of `iterations_cp`.
- Loop when the loop end address would be above the top of memory.
  Tracked as `oob_end_addr_cp`.
- Loop when the loop stack is full, causing an overflow.
  Tracked as `loop_stack_fullness_cp`.
- Loop at the end of a loop.
  Tracked as `at_loop_end_cp`.
- Duplicate loop end address, matching top of stack
  Tracked as `duplicate_loop_end_cp`.

It is possible for LOOPI to trigger multiple errors in a single cycle.
The possible errors are: zero loop count and loop at end of loop.
These can happen together:

- Loop with a zero loop count at the end of a loop.
  Tracked as `zero_count_at_loop_end_cp`.

## BN.ADD

This instruction uses the `bnaf` encoding schema, with covergroup `enc_bnaf_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero.
  This is tracked in `enc_bnaf_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  This is tracked in `enc_bnaf_cg` as `srl_cross`.

## BN.ADDC

This instruction uses the `bnaf` encoding schema, with covergroup `enc_bnaf_cg`.
The instruction-specific covergroup is `insn_bn_addc_cg`.

- Extremal values of shift for both directions where the shifted value is nonzero
  This is tracked in `enc_bnaf_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  This is tracked in `enc_bnaf_cg` as `srl_cross`.
- Execute with both values of the carry flag for both flag groups (to make sure things are wired through properly)
  Tracked as `carry_cross`.

## BN.ADDI

This instruction uses the `bnai` encoding schema, with covergroup `enc_bnai_cg`.
There is no instruction-specific covergroup.

No special coverage.

## BN.ADDM

This instruction uses the `bnam` encoding schema, with covergroup `enc_bnam_cg`.
The instruction-specific covergroup is `insn_bn_addm_cg`.

- Execute with the two extreme values of `MOD` (zero and all ones)
  Tracked as `mod_cp`.
- Don't perform a subtraction (because the sum is less than `MOD`) when `MOD` is nonzero.
  Tracked as `sum_lt_cp`.
- A calculation where the sum exactly equals a nonzero `MOD`
  Tracked as `sum_eq_cp`.
- A calculation where the sum is greater than a nonzero `MOD`.
  Tracked as `sum_gt_cp`.
- Perform a subtraction where the sum is at least twice a nonzero value of `MOD`.
  Tracked as `sum_gt2_cp`.
- A calculation where the intermediate sum is greater than `2^256-1`, crossed with whether the subtraction of `MOD` results in a value that will wrap.
  Tracked as `overflow_wrap_cross`.

## BN.MULQACC

This instruction uses the `bnaq` encoding schema, with covergroup `enc_bnaq_cg`.
The instruction-specific covergroup is `insn_bn_mulqaccx_cg` (shared with the other `BN.MULQACC*` instructions).

- Cross `wrs1_qwsel` with `wrs2_qwsel` to make sure they are applied to the right inputs
  This is tracked in `enc_bnaq_cg` as `qwsel_cross`.
- See the accumulator overflow
  This is tracked in `insn_bnmulqaccx_cg` as `overflow_cross`.

## BN.MULQACC.WO

This instruction uses the `bnaq` encoding schema, with an extra field not present in `bn.mulqacc`.
Encoding-level coverpoints are tracked in covergroup `enc_bnaqw_cg`.
The instruction-specific covergroup is `insn_bn_mulqaccx_cg` (shared with the other `BN.MULQACC*` instructions).

- Cross `wrs1_qwsel` with `wrs2_qwsel` to make sure they are applied to the right inputs
  This is tracked in `enc_bnaqw_cg` as `qwsel_cross`.
- See the accumulator overflow
  This is tracked in `insn_bnmulqaccx_cg` as `overflow_cross`.

## BN.MULQACC.SO

This instruction uses the `bnaq` encoding schema, with an extra field not present in `bn.mulqacc`.
Encoding-level coverpoints are tracked in covergroup `enc_bnaqs_cg`.
The instruction-specific covergroup is `insn_bn_mulqaccx_cg` (shared with the other `BN.MULQACC*` instructions).

- Cross `wrs1_qwsel` with `wrs2_qwsel` to make sure they are applied to the right inputs
  This is tracked in `enc_bnaqs_cg` as `qwsel_cross`.
- See the accumulator overflow
  This is tracked in `insn_bnmulqaccx_cg` as `overflow_cross`.
- Cross the generic flag updates with `wrd_hwsel`, since the flag changes are different in the two modes.
  This is tracked in `enc_bnaqs_cg` as `flags_01_cross`, `flags_10_cross` and `flags_11_cross`.

## BN.SUB

This instruction uses the `bnaf` encoding schema, with covergroup `enc_bnaf_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  This is tracked in `enc_bnaf_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  This is tracked in `enc_bnaf_cg` as `srl_cross`.

## BN.SUBB

This instruction uses the `bnaf` encoding schema, with covergroup `enc_bnaf_cg`.
The instruction-specific covergroup is `insn_bn_subcmpb_cg`.

- Extremal values of shift for both directions where the shifted value is nonzero
  This is tracked in `enc_bnaf_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  This is tracked in `enc_bnaf_cg` as `srl_cross`.
- Execute with both values of the carry flag for both flag groups (to make sure things are wired through properly)
  Tracked as `fg_carry_flag_cross`.

## BN.SUBI

This instruction uses the `bnai` encoding schema, with covergroup `enc_bnai_cg`.
There is no instruction-specific covergroup.

No special coverage.

## BN.SUBM

This instruction uses the `bnam` encoding schema, with covergroup `enc_bnam_cg`.
The instruction-specific covergroup is `insn_bn_subm_cg`.

- Execute with the two extreme values of `MOD` (zero and all ones)
  Tracked as `mod_cp`.
- A non-negative intermediate result with a nonzero `MOD` (so `MOD` is not added).
  Tracked as `diff_nonneg_cp`.
- An intermediate result that exactly equals a nonzero `-MOD`.
  Tracked as `diff_minus_mod_cp`.
- A negative intermediate result with a nonzero `MOD`, so `MOD` is added and the result is positive.
  Tracked as `diff_neg_cp`.
- A very negative intermediate result with a nonzero `MOD` (so `MOD` is added, but the top bit is still set)
  Tracked as `diff_neg2_cp`.

## BN.AND

This instruction uses the `bna` encoding schema, with covergroup `enc_bna_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bna_cg` as `st_sb_nz_shifted_cross`.
- Toggle coverage of the output result (to ensure we're not just AND'ing things with zero)
  Tracked in `enc_bna_cg` as `wrd_XXXXXXXX_cross`, where `XXXXXXXX` is the base-2 representation of the bit being checked.

## BN.OR

This instruction uses the `bna` encoding schema, with covergroup `enc_bna_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bna_cg` as `st_sb_nz_shifted_cross`.
- Toggle coverage of the output result (to ensure we're not just OR'ing things with zero)
  Tracked in `enc_bna_cg` as `wrd_XXXXXXXX_cross`, where `XXXXXXXX` is the base-2 representation of the bit being checked.

## BN.NOT

This instruction uses the `bnan` encoding schema, with covergroup `enc_bnan_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bnan_cg` as `st_sb_nz_shifted_cross`.
- Toggle coverage of the output result (to ensure nothing gets clamped)
  Tracked in `enc_bnan_cg` as `wrd_XXXXXXXX_cp`, where `XXXXXXXX` is the base-2 representation of the bit being checked.

## BN.XOR

This instruction uses the `bna` encoding schema, with covergroup `enc_bna_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bna_cg` as `st_sb_nz_shifted_cross`.
- Toggle coverage of the output result (to ensure we're not just XOR'ing things with zero)
  Tracked in `enc_bna_cg` as `wrd_XXXXXXXX_cross`, where `XXXXXXXX` is the base-2 representation of the bit being checked.

## BN.RSHI

This instruction uses the `bnr` encoding schema, with covergroup `enc_bnr_cg`.
There is no instruction-specific covergroup.

No special coverage.

## BN.SEL

This instruction uses the `bns` encoding schema, with covergroup `enc_bns_cg`.
There is no instruction-specific covergroup.

- Cross flag group, flag and flag value (2 times 4 times 2 points)
  Tracked in `enc_bns_cg` as `flag_cross`.

## BN.CMP

This instruction uses the `bnc` encoding schema, with covergroup `enc_bnc_cg`.
There is no instruction-specific covergroup.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bnc_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  Tracked in `enc_bnc_cg` as `srl_cross`.

## BN.CMPB

This instruction uses the `bnc` encoding schema, with covergroup `enc_bnc_cg`.
The instruction-specific covergroup is `insn_bn_subcmpb_cg`.

- Extremal values of shift for both directions where the shifted value is nonzero
  Tracked in `enc_bnc_cg` as `st_sb_nz_shifted_cross`.
- A nonzero right shift with a value in `wrs2` whose top bit is set
  Tracked in `enc_bnc_cg` as `srl_cross`.
- Execute with both values of the carry flag for both flag groups (to make sure things are wired through properly)
  Tracked as `fg_carry_flag_cross`.

## BN.LID

This instruction uses the `bnxid` encoding schema, with covergroup `enc_bnxid_cg`.
The instruction-specific covergroup is `insn_bn_xid_cg` (shared with `BN.SID`).

- Load from a valid address, where `grs1` is above the top of memory and a negative `offset` brings the load address in range.
  Tracked as `oob_base_neg_off_cross`.
- Load from a valid address, where `grs1` is negative and a positive `offset` brings the load address in range.
  Tracked as `neg_base_pos_off_cross`.
- Load from address zero
  Tracked as `addr0_cross`.
- Load from the top word of memory
  Tracked as `top_addr_cross`.
- Load from an invalid address (aligned but above the top of memory)
  Tracked as `oob_addr_cross`.
- Load from a calculated negative invalid address (aligned but unsigned address exceeds the top of memory)
  Tracked as `oob_addr_neg_cross`.
- Misaligned address tracking.
  Track loads from addresses that are in range for the size of the memory.
  We track all possible alignments of the sum as `addr_align_cross`.
  The reason for not tracking offset and register value misalignments separately is because the offset would always be shifted by 5 bits, which makes it always aligned.
- See an invalid instruction with both increments specified
  Tracked in `enc_bnxid_cg` as a bin of `incd_inc1_cross`.
- See `grd` greater than 31, giving an illegal instruction error
  Tracked as `bigb_cross`.
- Cross the three types of GPR for `grd` with `grd_inc`
  Tracked in `enc_bnxid_cg` as `grx_incd_cross`.
- Cross the three types of GPR for `grs1` with `grd_inc`
  Tracked in `enc_bnxid_cg` as `grs1_inc1_cross`.

It is possible for BN.LID to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack (for `grs1`), underflow call stack (for `grd`), both increments set, invalid WDR index and bad data address.
If we underflow the call stack for `grs1`, there's no architectural address, so that can't happen at the same time as a bad data address.
Similarly, if we underflow the call stack for `grd`, there's no WDR index, so that can't cause an invalid WDR index.
However, every other combination is possible.
Binning together the two underflows unless it makes a difference to the possible behaviour gives the following list:

- Underflow call stack and set both increments.
  Tracked as `underflow_and_inc_both_cross`.
- Underflow call stack for `grs1` and have a bad WDR index in `*grd`.
  Tracked as `underflow_and_badb_cross`.
- Underflow call stack for `grd` and compute a bad address from `*grs1`.
  Tracked as `underflow_and_bad_addr_cross`.
- Set both increments and have a bad WDR index.
  Tracked as `inc_both_and_bad_wdr_cross`.
- Set both increments and load from a bad address.
  Tracked as `inc_both_and_bad_addr_cross`.
- Have a bad WDR index when loading from a bad address.
  Tracked as `bad_wdr_and_bad_addr_cross`.
- Underflow call stack for `grs1`, setting both increments and have a bad WDR index in `*grd`.
  Tracked as `underflow_and_inc_both_and_bad_wdr_cross`.
- Underflow call stack for `grd`, setting both increments and compute a bad address from `*grs1`.
  Tracked as `underflow_and_inc_both_and_bad_addr_cross`.
- Set both increments and have both a bad WDR index and a bad address.
  Tracked as `inc_both_and_bad_wdr_and_bad_addr_cross`.

## BN.SID

This instruction uses the `bnxid` encoding schema, with covergroup `enc_bnxid_cg`.
The instruction-specific covergroup is `insn_bn_xid_cg` (shared with `BN.LID`).

- Store to a valid address, where `grs1` is above the top of memory and a negative `offset` brings the load address in range.
  Tracked as `oob_base_neg_off_cross`.
- Store to a valid address, where `grs1` is negative and a positive `offset` brings the load address in range.
  Tracked as `neg_base_pos_off_cross`.
- Store to address zero
  Tracked as `addr0_cross`.
- Store to the top word of memory
  Tracked as `top_addr_cross`.
- Store to an invalid address (aligned but above the top of memory)
  Tracked as `oob_addr_cross`.
- Store to a calculated negative invalid address (aligned but unsigned address exceeds the top of memory)
  Tracked as `oob_addr_neg_cross`.
- Misaligned address tracking.
  Track stores to addresses that are in range for the size of the memory.
  We track all possible alignments of the sum as `addr_align_cross`.
  The reason for not tracking offset and register value misalignments separately is because the offset would always be shifted by 5 bits, which makes it always aligned.
- See an invalid instruction with both increments specified
  Tracked in `enc_bnxid_cg` as a bin of `incd_inc1_cross`.
- See `grd` greater than 31, giving an illegal instruction error
  Tracked as `bigb_cross`.
- Cross the three types of GPR for `grs2` with `grs2_inc`
  Tracked in `enc_bnxid_cg` as `grx_incd_cross`.
- Cross the three types of GPR for `grs1` with `grd_inc`
  Tracked in `enc_bnxid_cg` as `grs1_inc1_cross`.

It is possible for BN.SID to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack (for `grs1`), underflow call stack (for `grs2`), both increments set, invalid WDR index and bad data address.
If we underflow the call stack for `grs1`, there's no architectural address, so that can't happen at the same time as a bad data address.
Similarly, if we underflow the call stack for `grs2`, there's no WDR index, so that can't cause an invalid WDR index.
However, every other combination is possible.
Binning together the two underflows unless it makes a difference to the possible behaviour gives the following list:

- Underflow call stack and set both increments.
  Tracked as `underflow_and_inc_both_cross`.
- Underflow call stack for `grs1` and have a bad WDR index in `*grs2`.
  Tracked as `underflow_and_badb_cross`.
- Underflow call stack for `grs2` and compute a bad address from `*grs1`.
  Tracked as `underflow_and_bad_addr_cross`.
- Set both increments and have a bad WDR index.
  Tracked as `inc_both_and_bad_wdr_cross`.
- Set both increments and store to a bad address.
  Tracked as `inc_both_and_bad_addr_cross`.
- Have a bad WDR index when storing to a bad address.
  Tracked as `bad_wdr_and_bad_addr_cross`.
- Underflow call stack for `grs1`, setting both increments and have a bad WDR index in `*grs2`.
  Tracked as `underflow_and_inc_both_and_bad_wdr_cross`.
- Underflow call stack for `grs2`, setting both increments and compute a bad address from `*grs1`.
  Tracked as `underflow_and_inc_both_and_bad_addr_cross`.
- Set both increments and have both a bad WDR index and a bad address.
  Tracked as `inc_both_and_bad_wdr_and_bad_addr_cross`.

## BN.MOV

This instruction uses the `bnmov` encoding schema, with covergroup `enc_bnmov_cg`.
There is no instruction-specific covergroup.

No special coverage otherwise.

## BN.MOVR

This instruction uses the `bnmovr` encoding schema, with covergroup `enc_bnmovr_cg`.
The instruction-specific covergroup is `insn_bn_movr_cg`.

- See an invalid instruction with both increments specified
  Tracked in `enc_bnmovr_cg` as a bin of `incd_inc1_cross`.
- Since MOVR signals an error if either of its source registers has a value greater than 31, cross whether the input register value at `grd` is greater than 31 with whether the register value at `grs` is greater than 31
  Tracked in `enc_bnmovr_cg` as `big_gpr_cross`.

It is possible for BN.MOVR to trigger multiple errors in a single cycle.
The possible errors are: underflow call stack (for `grs`), underflow call stack (for `grd`), both increments set, invalid WDR index (from `*grs`) and invalid WDR index (from `*grd`).
If we underflow the call stack for `grs`, there's no WDR index from `*grs`, so it's not also possible to see an invalid WDR index from that.
Similarly, if we underflow the call stack for `grd` then there's no WDR index from `*grd`, so it's not also possible to see an invalid WDR index from that.
Binning together the two underflows and WDR indices unless it makes a difference to the possible behaviour gives the following list:

- Underflow call stack and set both increments.
  Tracked as `underflow_and_inc_both_cp`.
- Underflow call stack for `grs` and have a bad WDR index in `*grd`.
  Tracked as `underflow_and_bad_grd_cp`.
- Underflow call stack for `grd` and have a bad WDR index in `*grs`.
  Tracked as `underflow_and_bad_grs_cp`.
- Set both increments and have a bad WDR index.
  Tracked as `inc_both_and_bad_wdr_cp`.
- Underflow call stack for `grs`, setting both increments and have a bad WDR index in `*grd`.
  Tracked as `underflow_grs_and_inc_both_and_bad_wdr_cp`.
- Underflow call stack for `grd`, setting both increments and have a bad WDR index in `*grs`.
  Tracked as `underflow_grd_and_inc_both_and_bad_wdr_cp`.

## BN.WSRR

This instruction uses the `bnwcsr` encoding schema, with covergroup `enc_wcsr_cg`.
There is no instruction-specific covergroup.

- Read from each valid WSR and an invalid WSR.
  Tracked with `wsr_cross` in `enc_wcsr_cg`.
- Read from each key sideload WSR, getting a valid response.
  Tracked as part of `key_avail_cross` in `insn_bn_wsrr_cg`.
- Read from each key sideload WSR, getting a KEY_INVALID error.
  Tracked as part of `key_avail_cross` in `insn_bn_wsrr_cg`.

These points are tracked with `wsr_cross` in `enc_wcsr_cg`.

## BN.WSRW

This instruction uses the `bnwcsr` encoding schema, with covergroup `enc_wcsr_cg`.
There is no instruction-specific covergroup.

- Write to each valid WSR, including read-only WSRs.
- Write to an invalid WSR

These points are tracked with `wsr_cross` in `enc_wcsr_cg`.
