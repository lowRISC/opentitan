# CSR utilities

This folder implements CSR related methods and test sequences for DV to share across all testbenches.

## CSR utility package

`csr_utils_pkg` provides common methods and properties to support and manage CSR accesses and CSR related test sequences.

### Global types and variables

All common types and variables are defined at this package level. Examples are:
```systemverilog
  uint       outstanding_accesses        = 0;
  uint       default_timeout_ns          = 1_000_000;
```

### Outstanding_accesses

Historically, `csr_utils_pkg` has used an internal variable to count accesses (read or write) that have not yet completed.
One intended use for this was to avoid injecting resets when CSR accesses were in flight.
This didn't really work very well, so most blocks' testbenches are being ported to avoid worrying about that.
The mechanism is also unaware of register accesses that are not made through this package.

Sequences that wish to maintain the counter can do so with the following functions:
```systemverilog
  function automatic void increment_outstanding_access();
    outstanding_accesses++;
  endfunction

  function automatic void decrement_outstanding_access();
    outstanding_accesses--;
  endfunction

  task automatic wait_no_outstanding_access();
    wait(outstanding_accesses == 0);
  endtask

  function automatic void clear_outstanding_access();
    outstanding_accesses = 0;
  endfunction
```

### CSR spinwait

One of the commonly used tasks in `csr_utils_pkg` is `csr_spinwait`.
This task can poll a register or field continuously or periodically until it reads out the expected value.
This task also has a timeout check to fail the test more quickly if the target never returns the expected value.
The following example uses `csr_spinwait` to wait until the `FIFO_FULL` field of the `STATUS` CSR becomes zero:
```systemverilog
csr_spinwait(.ptr(ral.status.fifo_full), .exp_data(1'b0));
```

### Read and check all CSRs

This task reads all the CSRs in a register block and checks they return their predicted values.
It is primarily intended for after reset, to check CSRs are being reset to the correct values.

### Reset state

Because `csr_utils_pkg` is not connected to any interface, methods inside this package are not able to get reset information.
An internal `under_reset` bit can be kept up to date with two functions:
```systemverilog
function automatic void reset_asserted();
  under_reset = 1;
endfunction

function automatic void reset_deasserted();
  under_reset = 0;
endfunction
```
This reset information is tracked by `dv_base_scoreboard` (using its `monitor_reset` task).
When that task sees a reset, it calls `reset_asserted` or `reset_deasserted` in its environment config.
That function, in turn, calls the `csr_utils_pkg` function.

### Global CSR util methods

The CSR access methods are based on `uvm_reg` methods, such as `uvm_reg::read()`, `uvm_reg::write()`, `uvm_reg::update()`.
For all CSR methods, user can pass either a register or a field handle.
Examples are:
 * `csr_rd_check`:
   This task takes a register or field does a register read to get the value.
   The value returned will then be compared against a prediction for the argument field or register.
   To pass the prediction explicitly, leave `compare_vs_ral = 0` and set `compare_value` to the prediction.
   If `compare_vs_ral` is true, the task compares against the prediction the register model.

 * `csr_update`:
   Perform a register write to update a register or field to the desired value.

These tasks can be used in blocking or non-blocking mode and also have timeouts.
 * In blocking mode, the task will not finish until the CSR access completes.
 * Non-blocking mode allows multiple CSR accesses to be issued back-to-back without waiting for responses.
 * The tasks run with a timeout in nanoseconds.
   If the time runs out, the task will disable the thread making the access and will raise a UVM error.

## CSR sequence library

`csr_seq_lib.sv` provides common CSR related test sequences to share across all testbenches.
These test sequences build on the standard sequences provided in UVM1.2 RAL.
The parent class (DUT-specific test or sequence class) that creates them needs to provide a RAL model.
The list of CSRs is extracted from the RAL model to perform the checks.

In addition, the test sequences provide an ability to exclude a CSR from writes or reads (or both).
This is explained more in the [CSR exclusion methodology](#csr-exclusion-methodology) section below.
All CSR accesses in these sequences are non-blocking to ensure back-to-back scenarios are exercised.

Supported CSR test sequences are:
 * `csr_hw_reset_seq`:
   Write all CSRs with random values and then reset the DUT.
   After reset, read all CSRs and compare with expected values

 * `csr_rw`:
   Write random values to each register in a list, then read the registers back again.
   This compares against predictions from the register model.
   The predictions are either generated by the sequence or by an external scoreboard.

 * `csr_bit_bash`:
   Perform a bit-bash test on each register in a list.
   That test, in turn, performs a bit-bash test on each bit in the register.
   The bit-bash test for a bit is to write each value (0 and 1) and read it back to check the write worked.

 * `csr_aliasing`:
   Perform an aliasing test for each register in a list.
   This test writes a random value to the register and then reads every register back again.
   The selected register should have the predicted value after the write.
   All other registers should have the values they had before the write.
   This checks that there is no aliasing between registers in the block.

 * `mem_walk`:
   Run `uvm_mem_walk_seq` on every `dv_base_reg_block`.
