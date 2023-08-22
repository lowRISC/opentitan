# OpenTitan Assertions

# OpenTitan Assertions


## What Are Assertions?
Assertions are statements about your design that are expected to be always true.
Here are two examples:
*   <code>`ASSERT(grantOneHot, $onehot0(grant), clk, !rst_n)</code>
    <br />This asserts that signal <code>grant</code> will be either
    one-hot encoded or all-zero.
*   <code>`ASSERT(ackTwoClocksAfterReq, req |-> ##2 ack, clk, !rst_n)</code>
    <br />Every time <code>req</code> goes high, <code>ack</code> must be
    high exactly 2 clock cycles later.

Above examples are using the <code>`ASSERT</code> macro defined in [prim_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert.sv),
whose four arguments are assertion name, property, clock, and reset (active-high reset).

Assertions are usually added by the designer in the RTL file.
Assertions can also be added in a separate module, see for example [tlul_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/tlul/rtl/tlul_assert.sv) and its [documentation](../ip/tlul/doc/TlulProtocolChecker.md), which contains a generic protocol checker for the TileLink-UL standard.

## Types of Assertions
There are two types of assertions:
*   **Concurrent assertions** can span time and are triggered by a clock edge.
See the two examples in the previous section.
*   **Immediate assertions** do not depend upon a clock edge.
They are typically used in an initial block to check for correct parameter settings.
Example:
```
initial begin
  checkFifoWidth: assert (FifoDepth > 0) else begin
    $error("FifoDepth parameter should be > 0");
  end
end
```

## Useful Macros
The file [prim_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert.sv) and [prim_assert_standard_macros.svh](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert_standard_macros.svh) define many useful shortcuts that you can use in your RTL code.
Some of them are detailed below:

### ASSERT(__name, __prop, __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
*   This is a shortcut macro for a generic concurrent assignment.
*   The first argument is the assertion name.
    It is recommended to follow the [naming conventions](#naming-conventions).
    The assertion name should be descriptive, which will help during debug.
*   The second argument is the assertion property.
*   The last two are optional arguments to specify the clock and reset signals (active-high reset) if different from default value.
*   Note that this macro doesn't support a custom error message (such as the $error message in the previous section).
    However, the macro will print out the property name and the entire property code such as `req |-> ack`.

For example, <code>`ASSERT(myAssertion, req |-> ack, clk, !rst_n)</code>
is expanded as follows:
```
myAssertion: assert property (
  @(posedge clk) disable iff ((!rst_n) !== 1'b0)
    (req |-> ack)
) else begin
  $error("Assert failed: [%m] %s: %s\n",
      `STRINGIFY(myAssertion), `STRINGIFY(req |-> ack));
end
```
### `ASSERT_INIT(__name, __prop)
Concurrent assertion inside an initial block. It can be used for checking parameters.

### `ASSERT_FINAL(__name, __prop)
Concurrent assertion inside a final block. It can be used e.g. for making sure that a FIFO is empty at the end of each sim.

### `ASSERT_AT_RESET(__name, __prop, __rst = `ASSERT_DEFAULT_RST)
Assertion just before reset. Can be used to check sum-like properties that get cleared at reset.
Note that unless your simulation ends with a reset, the property does not get checked at end of
simulation; use `ASSERT_AT_RESET_AND_FINAL` if the property should also get checked at end of
simulation.

### `ASSERT_AT_RESET_AND_FINAL(__name, __prop, __rst = `ASSERT_DEFAULT_RST)
Assertion just before reset and in final block. Can be used to check sum-like properties before
every reset and at the end of simulation.

### `ASSERT_NEVER(__name, __prop,  __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
Assert that a concurrent property never happens.

### `ASSERT_KNOWN(__name, __signal,  __clk = `ASSERT_DEFAULT_CLK, __rst = `ASSERT_DEFAULT_RST)
Assert that `signal` has a known value after reset, where "known" refers to a value that is not X.

### More Macros and Examples
*   For more macros see file [prim_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert.sv) and [prim_assert_standard_macros.svh](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert_standard_macros.svh).
*   For more examples, search the repository for ASSERT by typing `grep -r ASSERT .`
*   Also see [tlul_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/tlul/rtl/tlul_assert.sv) and its [documentation](../ip/tlul/doc/TlulProtocolChecker.md).

## Useful SVA System Functions
Below table lists useful SVA (SystemVerilog assertion) functions that can be used for assertion properties.

<table>
  <tr>
   <td><strong>System Function</strong>
   </td>
   <td><strong>Description</strong>
   </td>
  </tr>
  <tr>
   <td>$rose()
   </td>
   <td>True if LSB of expression changed to 1
   </td>
  </tr>
  <tr>
   <td>$fell()
   </td>
   <td>True if LSB of expression changed to 0
   </td>
  </tr>
  <tr>
   <td>$stable()
   </td>
   <td>True if the value of expression didn't change
   </td>
  </tr>
  <tr>
   <td>$past()
   </td>
   <td>Value of expression of previous clock cycle
   </td>
  </tr>
  <tr>
   <td>$past( , n_cycles)
   </td>
   <td>Value of expression n_cycles clocks ago
   </td>
  </tr>
  <tr>
   <td>$countones()
   </td>
   <td>Number of ones in the expression
   </td>
  </tr>
  <tr>
   <td>$onehot()
   </td>
   <td>True if exactly one bit is 1
   </td>
  </tr>
  <tr>
   <td>$onehot0()
   </td>
   <td>True if no bits or only one bit is 1
   </td>
  </tr>
  <tr>
   <td>$isunknown()
   </td>
   <td>True if any bit in the expression is 'X' or 'Z'
   </td>
  </tr>
</table>

## Useful SVA Operators
Below table lists useful operators that can be used for assertion properties.

<table>
  <tr>
   <td><strong>Operator</strong>
   </td>
   <td><strong>Description</strong>
   </td>
  </tr>
  <tr>
   <td>##n
   </td>
   <td>Delay operator, fixed time interval of n clock cycles
   </td>
  </tr>
  <tr>
   <td>##[m:n]
   </td>
   <td>Delay operator, time interval range between m and n clocks
   </td>
  </tr>
  <tr>
   <td>|->
   </td>
   <td>"Overlapping" implication (same cycle)
   </td>
  </tr>
  <tr>
   <td>|=>
   </td>
   <td>"Non-overlapping" implication (next cycle)
     <br /> <code>a |=> b</code> is equivalent to <code>a |-> ##1 b</code>
   </td>
  </tr>
  <tr>
   <td>not, or, and
   </td>
   <td>Property operators
   </td>
  </tr>
</table>

There are also powerful repetition operators, see [here](https://www.systemverilog.io/sva-basics) for more details.

## Symbolic Variables

When design has a set of modules or signals that share same properties, symbolic variables can be used to reduce duplicated assertions.
For example, in the [rv_plic design](../ip_templates/rv_plic/README.md), the array of input `intr_src_i` are signals sharing the same properties.
Each `intr_src_i[index]` will trigger the interrupt pending (`ip`) signal depending on the corresponding level indicator (`le`) is set to level triggered or edge triggered.
Without symbolic variables, the above assertions can be implemented as below:
```systemverilog
  genvar i;
  generate for (i = 0; i < N_SOURCE; i++) begin : gen_rv_plic_fpv
    `ASSERT(LevelTriggeredIp_A, $rose(rv_plic.ip[i]) |->
            $past(rv_plic.le[i]) || $past(intr_src_i[i]), clk_i, !rst_ni)
  end
```

In contrast, symbolic variable can abstract the design by declaring the index with constraints.
To ensure the symbolic variable performs the expected behaviors, two assumptions need to be written:
* Constraint the symbolic variable with the correct bound.
* Randomize the variable at the beginning of the simulation, then keep it stable throughout the rest of the simulation.
```systemverilog
  logic [$clog2(N_SOURCE)-1:0] src_sel;
  `ASSUME_FPV(IsrcRange_M, src_sel >= 0 && src_sel < N_SOURCE, clk_i, !rst_ni)
  `ASSUME_FPV(IsrcStable_M, ##1 $stable(src_sel), clk_i, !rst_ni)
  `ASSERT(LevelTriggeredIp_A, $rose(rv_plic.ip[src_sel]) |->
          $past(rv_plic.le[src_sel]) || $past(intr_src_i[src_sel]), clk_i, !rst_ni)
```

## Coverpoints
Coverpoints are used for properties and corner cases that the designer wants to make sure are being exercised by the testbench (e.g. FIFO-full checks).
The code coverage tool then reports the coverage percentage of these coverpoints together with the other cover metrics (such as line coverage and branch coverage).

The macro <code>`COVER(name, prop, clk, rst)</code> of [prim_assert.sv](https://github.com/lowRISC/opentitan/blob/master/hw/ip/prim/rtl/prim_assert.sv) can be used to add coverpoints to your design, where the cover property uses the same SVA syntax, operators, and system functions as the assert properties.

## Running FPV on DVSim

### Cadence JasperGold
If you have access to JasperGold from Cadence, you can formally verify your assertions.
Before running FPV, please make sure the target has been added to one of the [three batch scripts](../../doc/getting_started/setup_formal.md#formal-property-verification-fpv).

For example, to run formal property verification (FPV) using JasperGold on the prim module `prim_arbiter_fixed`, type:
```
  $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/top_earlgrey/formal/top_earlgrey_prim_fpv_cfgs.hjson --select-cfgs prim_arbiter_fixed_fpv
```
JasperGold will then report which assertions have been proven or disproven, and whether or not there are any unreachable assertions or coverpoints.
Adding a `--gui` option will open the JasperGold GUI.

To run formal property verification for all prim modules, type:
```
  $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/top_earlgrey/formal/top_earlgrey_prim_fpv_cfgs.hjson
```

### Synopsys VC Formal

If you have access to VC Formal from Synopsys, you can formally verify your assertions.
For example, to run formal property verification (FPV) using VC Formal on module `gpio`, type:
```
  $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/top_earlgrey/formal/top_earlgrey_prim_fpv_cfgs.hjson --select-cfgs prim_arbiter_fixed_fpv -t vcformal
```
VC Formal will then report which assertions have been proven or disproven, and whether or not there are any unreachable assertions or coverpoints.
Adding a `--gui` option will open the VCFormal GUI.

To run formal property verification for all prim modules, type:
```
  $REPO_TOP/util/dvsim/dvsim.py $REPO_TOP/hw/top_earlgrey/formal/top_earlgrey_prim_fpv_cfgs.hjson -t vcformal
```
This script generates a report of all FPV runs.
The report is printed at the end of the run, which lists the total number of assertions and the number of proven, vacuous, covered and failing assertions for each block. CRASH identifies modules that fail to run VC Formal.

## Running Connectivity Tests
Connectivity tests use formal method to exhaustively verify system-level connections, which are specified in a high-level format (for example: CSV format for JasperGold).

### Cadence JasperGold on dvsim
The `dvsim` formal flow supports connectivity test. Each top-level can create its own connectivity setting with a customized Hjson file.
For example, `top_earlgrey` has `hw/top_earlgrey/formal/chip_conn_cfgs.hjson` that specifies its top_level name, fusesoc_core file, and csv file path.
You can trigger top_earlgrey's connectivity test using `dvsim`:
```
  util/dvsim/dvsim.py hw/top_earlgrey/formal/chip_conn_cfgs.hjson
```
Adding a `--gui` option will open the JaperGold GUI.

## Running FPV on security blocks for common countermeasure primitives
A [security countermeasure verification framework](../../doc/contributing/dv/sec_cm_dv_framework/README.md) is implemented in design and fpv tcl script to verify common countermeasure primitives in a semi-automated way.

### Common security assertion macros
OpenTitan's security IP blocks have implemented assertions to check against common fault injections.
These assertions ensure if the security prim module returns an error, a corresponding alert should fire immediately without any gating conditions.
There are three pre-defined assertion macros under file `hw/ip/prim/rtl/prim_assert_sec_cm.svh`:
* ASSERT_PRIM_FSM_TRIGGER_ALERT: if design module `prim_sparse_fsm_flop` returns `state_o` value that is not one of the defined FSM states, which means the FSM state might be attacked, a fatal alert is expected to fire.
* ASSERT_PRIM_COUNT_TRIGGER_ALERT: if design module `prim_count` sets `err_o` to 1, which means the two counters do not match, a fatal alert is expected to fire.
* ASSERT_PRIM_DOUBLE_LFSR_TRIGGER_ALERT: if design module `prim_double_lfsr` sets `err_o` to 1, which means two LFSR states do not match, a fatal alert is expected to fire.
Note that assertions defined with these macros will have a common prefix name `FpvSecCm`, which will help the FPV tcl file to group them in a specific task.

### FPV fault injection
The above security assertions are expected to be unreachable in normal design environment.
They are only reachable if a fault is injected.
To create a FPV environment that has fault injections, the `stopat` command and black-box methods are used.
* FSM fault injection: a `stopat` is placed at `state_o` output.
* Counter fault injection: black-box the prim_count module.
* Double LFSR fault injection: black-box the prim_double_lfsr module.
Then we will let formal environment to randomly drive these outputs and run security assertions to ensure these error cases will trigger alerts under any circumstances.

### Set up FPV security check environment
To set up the FPV security check environment, please follow the steps below:
1. Add an item under `hw/top_earlgrey/formal/top_earlgrey_sec_cm_fpv_cfgs.hjson` with the naming convention "{ip_name}_sec_cm".
2. Under the item add an entry "task" with value "FpvSecCm".
This entry tells the tcl file to black-box security prim modules in the FPV environment, and define required macros.
This "task" entry also tells the tcl file to disable regular assertions and only analyze macro defined security assertions with prefix `FpvSecCm`.
3. Under the item add an entry "stopats" if design has sparse FSMs.
This is an optional step. Because some designs contain more than one stopat path, the entry "stopats" is declared as a list of strings.

Here is an example on csrng module:
```
{
  name: csrng_sec_cm
  dut: csrng
  fusesoc_core: lowrisc:dv:csrng_sva
  import_cfgs: ["{proj_root}/hw/formal/tools/dvsim/common_fpv_cfg.hjson"]
  rel_path: "hw/ip/csrng/{sub_flow}/{tool}"
  cov: false
  task: "FpvSecCm"
  stopats: ["*u_state_regs.state_o"]
}
```

## Naming Conventions
For assertions, it is preferred to use postfix `_A` for assertions, `_M` for assumptions, `_P` for properties, and `_S` for sequences.
For example:
```systemverilog
  `ASSUME_FPV(IsrcRange_M, src_sel >= 0 && src_sel < N_SOURCE, clk_i, !rst_ni)
  `ASSERT(LevelTriggeredIp_A, $rose(rv_plic.ip[src_sel]) |->
          $past(rv_plic.le[src_sel]) || $past(intr_src_i[src_sel]), clk_i, !rst_ni)
```

## Implementation Guidelines
The recommended guidelines for where to implement assertions are as follows:
* Basic assertions should be implemented directly in the RTL file.
  These basic functional assertions are often inserted by designers to act as a smoke check.
* Assertions used for the testbench to achieve verification goals should be implemented under the `ip/hw/module_name/fpv/vip` folder.
  This FPV environment can be automatically generated by the [`fpvgen.py` script](../../util/fpvgen/README.md).
* Portable assertions written for common interfaces or submodules should also be implemented under the `ip/hw/submodule_or_interface/fpv/vip` folder.
  These portable assertion collections can be easily reused by other testbench via a bind file.

## References
*   [SVA Basics](https://www.systemverilog.io/sva-basics)
*   [SVA Tutorial](https://www.doulos.com/knowhow/sysverilog/tutorial/assertions/)
*   "SystemVerilog Assertions Design Tricks and SVA Bind Files", SNUG 2009,
Clifford E. Cummings,
[paper](http://www.sunburst-design.com/papers/CummingsSNUG2009SJ_SVA_Bind.pdf)
