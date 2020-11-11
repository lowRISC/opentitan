# CSR utilities


This csr_utils folder intends to implement CSR related methods and test sequences for DV
to share across all testbenches.

### CSR utility package
`csr_utils_pkg` provides common methods and properties to support and manage CSR accesses
and CSR related test sequences.

#### Global types and variables
All common types and variables are defined at this package level. Examples are:
```systemverilog
  uint       outstanding_accesses        = 0;
  uint       default_timeout_ns          = 1_000_000;
```

##### Outstanding_accesses
`csr_utils_pkg` used an internal variable to store the number of accesses
(read or write) that have not yet completed. This variable is shared among all methods of
register reading and writing. Directly accessing this variable is discouraged. Instead,
the following methods are used to control this variable to keep track of non-blocking
accesses made in the testbench:
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

##### CSR spinwait
One of the commonly used tasks in `csr_utils_pkg` is `csr_spinwait`. This task
can poll a CSR or CSR field continuously or periodically until it reads out the
expected value. This task also has a timeout check in case due to DUT or testbench
issue, the CSR or CSR field never returns the expected value.
Example below uses the `csr_spinwait` to wait until the CSR `fifo_status` field
`fifo_full` reaches value bit 1:
```systemverilog
csr_spinwait(.ptr(ral.status.fifo_full), .exp_data(1'b0));
```

##### Read and check all CSRs
The purpose of the `read_and_check_all_csrs` task is to read all valid CSRs from
the given `uvm_reg_block` and check against their expected values from RAL. This
task is primarily implemented to use after reset, to make sure all the CSRs are
being reset to the default value.

##### Under_reset
Due to `csr_utils_pkg` is not connected to any interface, methods inside
this package are not able to get reset information. Current the `under_reset`
bit is declared with two functions:
```systemverilog
function automatic void reset_asserted();
  under_reset = 1;
endfunction

function automatic void reset_deasserted();
  under_reset = 0;
endfunction
```
This reset information is updated in `dv_lib/dv_base_vseq.sv`. When the
`apply_reset` task is triggered, it will set and reset the `under_reset` bit
via the functions above.

#### Global CSR util methods
##### Global methods for CSR and MEM attributes
This package provides methods to access CSR or Memory attributes, such as address,
value, etc. Examples are:
 * `get_csr_addrs`
 * `get_mem_addr_ranges`
 * `decode_csr_or_field`

##### Global methods for CSR access
The CSR access methods are based on `uvm_reg` methods, such as `uvm_reg::read()`,
`uvm_reg::write()`, `uvm_reg::update()`. For all CSR methods, user can
pass either a register or a field handle. Examples are:
 * `csr_rd_check`: Given the uvm_reg or uvm_reg_field object, this method will
   compare the CSR value with the expected value (given as an input) or with
   the RAL mirrored value
 * `csr_update`: Given the uvm_reg object, this method will update the value of the
   register in DUT to match the desired value

To enhance the usability, these methods support CSR blocking, non-blocking
read/write, and a timeout checking.
 * A blocking thread will not execute the next sequence until the current CSR
   access is finished
 * A non-blocking thread allows multiple CSR accesses to be issued back-to-back
   without waiting for the response
 * A timeout check will discard the ongoing CSR access by disabling the forked
   thread and will throw a UVM_ERROR once the process exceeds the max timeout setting

### CSR sequence library
`csr_seq_lib.sv` provides common CSR related test sequences to share across all testbenches.
These test sequences are based off the standard sequences provided in UVM1.2 RAL.
The parent class (DUT-specific test or sequence class) that creates them needs to provide them
with the DUT RAL model. The list of CSRs are then extracted from the RAL model to performs the checks.
In addition, the test sequences provide an ability to exclude a CSR from writes or reads (or both)
depending on the behavior of the CSR in the design. This is explained more in the
[CSR exclusion methodology](#csr-exclusion-methodology) section below.
All CSR accesses in these sequences are made non-blocking to ensure back-to-back scenarios
are exercised.
Supported CSR test sequences are:
 * `csr_hw_reset`: Write all CSRs with random values and then reset the DUT.
   After reset, read all CSRs and compare with expected values
 * `csr_rw`: Write a randomly selected CSRs, then read out the updated
   CSR or CSR field and compare with expected value
 * `csr_bit_bash`: Randomly select a CSR and write 1's and 0's to
   every bit, then read the CSR to compare with expected value
 * `csr_aliasing`: Randomly write a CSR, then read all CSRs to
   verify that only the CSR that was written was updated
 * `mem_walk`: Write and read all valid addresses in the memory. Compare
   the read results with the expected values

### CSR exclusion methodology
The CSR test sequences listed above intend to perform a basic check to CSR
read/write accesses, but do not intend to check specific DUT functionalities. Thus the
sequences might need to exclude reading or writing certain CSRs depending on the
specific testbench.
`csr_excl_item` is a class that supports adding exclusions to CSR test sequences.
Examples of useful functions in this class are:
* `add_excl`: Add exclusions to the CSR test sequences. This function has two inputs:
  - Exclusion scope: A hierarchical path name at all levels including block,
    CSR, and field. This input supports * and ? wildcards for glob style matching
  - CSR_exclude type: An enumeration defined as below:
    ```systemverilog
    typedef enum bit[2:0] {
      CsrNoExcl         = 3'b000, // no exclusions
      CsrExclInitCheck  = 3'b001, // exclude csr from init val check
      CsrExclWriteCheck = 3'b010, // exclude csr from write-read check
      CsrExclCheck      = 3'b011, // exclude csr from init or write-read check
      CsrExclWrite      = 3'b100, // exclude csr from write
      CsrExclAll        = 3'b111  // exclude csr from init or write or write-read check
    } csr_excl_type_e;
    ```

  One example to use this function in HMAC to exclude all CSRs or fields with
  names starting with "key":
  ```systemverilog
  csr_excl.add_excl({scope, ".", "key?"}, CsrExclWrite);
  ```

* `has_excl`: Check if the CSR has a match in the existing exclusions loopup,
  and is not intended to use externally

### CSR sequence framework
The [cip_lib]({{< relref "hw/dv/sv/cip_lib/doc" >}}) includes a virtual sequence named `cip_base_vseq`,
that provides a common framework for all testbenchs to run these CSR test sequences and
add exclusions.
