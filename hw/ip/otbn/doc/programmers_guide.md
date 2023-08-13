# Programmer's Guide

## Running applications on OTBN

OTBN is a specialized coprocessor which is used from the host CPU.
This section describes how to interact with OTBN from the host CPU to execute an existing OTBN application.
The section [Writing OTBN applications](#writing-otbn-applications) describes how to write such applications.

### High-level operation sequence

The high-level sequence by which the host processor should use OTBN is as follows.

1. Optional: Initialise [`LOAD_CHECKSUM`](registers.md#load_checksum).
1. Write the OTBN application binary to [`IMEM`](registers.md#imem), starting at address 0.
1. Optional: Write constants and input arguments, as mandated by the calling convention of the loaded application, to the half of DMEM accessible through the [`DMEM`](registers.md#dmem) window.
1. Optional: Read back [`LOAD_CHECKSUM`](registers.md#load_checksum) and perform an integrity check.
1. Start the operation on OTBN by [issuing the `EXECUTE` command](./theory_of_operation.md#operations-and-commands).
   Now neither data nor instruction memory may be accessed from the host CPU.
   After it has been started the OTBN application runs to completion without further interaction with the host.
1. Wait for the operation to complete (see below).
   As soon as the OTBN operation has completed the data and instruction memories can be accessed again from the host CPU.
1. Check if the operation was successful by reading the [`ERR_BITS`](registers.md#err_bits) register.
1. Optional: Retrieve results by reading [`DMEM`](registers.md#dmem), as mandated by the calling convention of the loaded application.

OTBN applications are run to completion.
The host CPU can determine if an application has completed by either polling [`STATUS`](registers.md#status) or listening for an interrupt.

* To poll for a completed operation, software should repeatedly read the [`STATUS`](registers.md#status) register.
  The operation is complete if [`STATUS`](registers.md#status) is `IDLE` or `LOCKED`, otherwise the operation is in progress.
  When [`STATUS`](registers.md#status) has become `LOCKED` a fatal error has occurred and OTBN must be reset to perform further operations.
* Alternatively, software can listen for the `done` interrupt to determine if the operation has completed.
  The standard sequence of working with interrupts has to be followed, i.e. the interrupt has to be enabled, an interrupt service routine has to be registered, etc.
  The [DIF](#device-interface-functions-difs) contains helpers to do so conveniently.

Note: This operation sequence only covers functional aspects.
Depending on the application additional steps might be necessary, such as deleting secrets from the memories.

## Writing OTBN applications

OTBN applications are (small) pieces of software written in OTBN assembly.
The full instruction set is described in the [ISA manual](./isa.md), and example software is available in the `sw/otbn` directory of the OpenTitan source tree.

A hands-on user guide to develop OTBN software can be found in the section [Writing and building software for OTBN](../../../../doc/contributing/sw/otbn_sw.md).

### Toolchain support

OTBN comes with a toolchain consisting of an assembler, a linker, and helper tools such as objdump.
The toolchain wraps a RV32 GCC toolchain and supports many of its features.

The following tools are available:
* `otbn_as.py`: The OTBN assembler.
* `otbn_ld.py`: The OTBN linker.
* `otbn_objdump.py`: objdump for OTBN.

Other tools from the RV32 toolchain can be used directly, such as objcopy.

### Passing of data between the host CPU and OTBN

Passing data between the host CPU and OTBN is done through the first 2kiB of data memory (DMEM).
No standard or required calling convention exists, every application is free to pass data in and out of OTBN in whatever format it finds convenient.
All data passing must be done when OTBN [is idle](./theory_of_operation.md#operational-states); otherwise both the instruction and the data memory are inaccessible from the host CPU.

### Returning from an application

The software running on OTBN signals completion by executing the {{#otbn-insn-ref ECALL}} instruction.

Once OTBN has executed the {{#otbn-insn-ref ECALL}} instruction, the following things happen:

- No more instructions are fetched or executed.
- A [secure wipe of internal state](./theory_of_operation.md#internal-state-secure-wipe) is performed.
- The [`ERR_BITS`](registers.md#err_bits) register is set to 0, indicating a successful operation.
- The current operation is marked as complete by setting [`INTR_STATE.done`](registers.md#intr_state) and clearing [`STATUS`](registers.md#status).

The first 2kiB of DMEM can be used to pass data back to the host processor, e.g. a "return value" or an "exit code".
Refer to the section [Passing of data between the host CPU and OTBN](#passing-of-data-between-the-host-cpu-and-otbn) for more information.

### Using hardware loops

OTBN provides two hardware loop instructions: {{#otbn-insn-ref LOOP}} and {{#otbn-insn-ref LOOPI}}.

#### Loop nesting

OTBN permits loop nesting and branches and jumps inside loops.
However, it doesn't have support for early termination of loops: there's no way to pop an entry from the loop stack without executing the last instruction of the loop the correct number of times.
It can also only pop one level of the loop stack per instruction.

To avoid polluting the loop stack and avoid surprising behaviour, the programmer must ensure that:
* Even if there are branches and jumps within a loop body, the final instruction of the loop body gets executed exactly once per iteration.
* Nested loops have distinct end addresses.
* The end instruction of an outer loop is not executed before an inner loop finishes.

OTBN does not detect these conditions being violated, so no error will be signaled should they occur.

(Note indentation in the code examples is for clarity and has no functional impact.)

The following loops are *well nested*:

```
LOOP x2, 3
  LOOP x3, 1
    ADDI x4, x4, 1
  # The NOP ensures that the outer and inner loops end on different instructions
  NOP

# Both inner and outer loops call some_fn, which returns to
# the body of the loop
LOOP x2, 5
  JAL x1, some_fn
  LOOP x3, 2
    JAL x1, some_fn
    ADDI x4, x4, 1
  NOP

# Control flow leaves the immediate body of the outer loop but eventually
# returns to it
LOOP x2, 4
  BEQ x4, x5, some_label
branch_back:
  LOOP x3, 1
    ADDI x6, x6, 1
  NOP

some_label:
  ...
  JAL x0, branch_back
```

The following loops are not well nested:

```
# Both loops end on the same instruction
LOOP x2, 2
  LOOP x3, 1
    ADDI x4, x4, 1

# Inner loop jumps into outer loop body (executing the outer loop end
# instruction before the inner loop has finished)
LOOP x2, 5
  LOOP x3, 3
    ADDI x4, x4 ,1
    BEQ  x4, x5, outer_body
    ADD  x6, x7, x8
outer_body:
  SUBI  x9, x9, 1
```

### Algorithic Examples: Multiplication with BN.MULQACC

The big number instruction subset of OTBN generally operates on WLEN bit numbers.
{{#otbn-insn-ref BN.MULQACC}} operates with WLEN/4 bit operands (with a full WLEN accumulator).
This section outlines two techniques to perform larger multiplies by composing multiple {{#otbn-insn-ref BN.MULQACC}} instructions.

#### Multiplying two WLEN/2 numbers with BN.MULQACC

This instruction sequence multiplies the lower half of `w0` by the upper half of
`w0` placing the result in `w1`.

```
BN.MULQACC.Z      w0.0, w0.2, 0
BN.MULQACC        w0.0, w0.3, 64
BN.MULQACC        w0.1, w0.2, 64
BN.MULQACC.WO w1, w0.1, w0.3, 128
```

#### Multiplying two WLEN numbers with BN.MULQACC

The shift out functionality can be used to perform larger multiplications without extra adds.
The table below shows how two registers `w0` and `w1` can be multiplied together to give a result in `w2` and `w3`.
The cells on the right show how the result is built up `a0:a3 = w0.0:w0.3` and `b0:b3 = w1.0:w1.3`.
The sum of a column represents WLEN/4 bits of a destination register, where `c0:c3 = w2.0:w2.3` and `d0:d3 = w3.0:w3.3`.
Each cell with a multiply in takes up two WLEN/4-bit columns to represent the WLEN/2-bit multiply result.
The current accumulator in each instruction is represented by highlighted cells where the accumulator value will be the sum of the highlighted cell and all cells above it.

The outlined technique can be extended to arbitrary bit widths but requires unrolled code with all operands in registers.

<table>
  <thead>
    <tr>
      <th></th>
      <th>d3</th>
      <th>d2</th>
      <th>d1</th>
      <th>d0</th>
      <th>c3</th>
      <th>c2</th>
      <th>c1</th>
      <th>c0</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td><code>BN.MULQACC.Z w0.0, w1.0, 0</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b0</code></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.0, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a1 * b0</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w2.l, w0.0, w1.1, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b1</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.0, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b0</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.1, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b1</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.0, w1.2, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b2</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.0, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a3 * b0</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.1, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b1</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.2, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b2</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w2.u, w0.0, w1.3, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b3</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.1, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b1</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.2, w1.2, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b2</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.1, w1.3, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a1 * b3</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC w0.3, w1.2, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b2</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w3.l, w0.2, w1.3, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b3</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO w3.u, w0.3, w1.3, 0</code></td>
      <td style="background-color: lightblue" colspan="2" rowspan="1"><code>a3 * b3</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
  </tbody>
</table>

Code snippets giving examples of 256x256 and 384x384 multiplies can be found in `sw/otbn/code-snippets/mul256.s` and `sw/otbn/code-snippets/mul384.s`.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_otbn.h)

## Driver

A higher-level driver for the OTBN block is available at `sw/device/lib/runtime/otbn.h`.

Another driver for OTBN is part of the silicon creator code at `sw/device/silicon_creator/lib/drivers/otbn.h`.
