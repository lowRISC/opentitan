---
title: OpenTitan Big Number Accelerator (OTBN) Technical Specification
---

<div class="bd-callout bd-callout-warning">
  <h5>Note on the status of this document</h5>

  **This specification is work in progress and will see significant changes before it can be considered final.**
  We invite input of all kind through the standard means of the OpenTitan project; a good starting point is filing an issue in our [GitHub issue tracker](https://github.com/lowRISC/opentitan/issues).
</div>

# Overview

This document specifies functionality of the OpenTitan Big Number Accelerator, or OTBN.
OTBN is a coprocessor for asymmetric cryptographic operations like RSA or Elliptic Curve Cryptography (ECC).

This module conforms to the [Comportable guideline for peripheral functionality]({{< relref "doc/rm/comportability_specification" >}}).
See that document for integration overview within the broader top level system.

## Features

* Processor optimized for wide integer arithmetic
* 32b wide control path with 32 32b wide registers
* 256b wide data path with 32 256b wide registers
* Full control-flow support with conditional branch and unconditional jump instructions, hardware loops, and hardware-managed call/return stacks.
* Reduced, security-focused instruction set architecture for easier verification and the prevention of data leaks.
* Built-in access to random numbers.
  Note: The (quality) properties of the provided random numbers it not specified currently; this gap in the specification will be addressed in a future revision.

## Description

OTBN is a processor, specialized for the execution of security-sensitive asymmetric (public-key) cryptography code, such as RSA or ECC.
Such algorithms are dominated by wide integer arithmetic, which are supported by OTBN's 256b wide data path, registers, and instructions which operate these wide data words.
On the other hand, the control flow is clearly separated from the data, and reduced to a minimum to avoid data leakage.

The data OTBN processes is security-sensitive, and the processor design centers around that.
The design is kept as simple as possible to reduce the attack surface and aid verification and testing.
For example, no interrupts or exceptions are included in the design, and all instructions are designed to be executable within a single cycle.

OTBN is designed as a self-contained co-processor with its own instruction and data memory, which is accessible as a bus device.

## Compatibility

OTBN is not designed to be compatible with other cryptographic accelerators.
Its design is inspired by dcrypto, the cryptographic accelerator used in Google’s Titan chips, which itself is inspired by the [Fiat Crypto Machine](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf).

# Instruction Set

OTBN is a processor with a custom instruction set, which is described in this section.
The instruction set is split into two groups:

* The **base instruction subset** operates on the 32b General Purpose Registers (GPRs).
  Its instructions are used for the control flow of a OTBN application.
  The base instructions are inspired by RISC-V’s RV32I instruction set, but not compatible with it.
* The **big number instruction subset** operates on 256b Wide Data Registers (WDRs).
  Its instructions are used for data processing.
  Also included are compare and select instructions to perform data-dependent control flow in a safe and constant time fashion.

The subsequent sections describe first the processor state, followed by a description of the base and big number instruction subsets.

## Processor State

### General Purpose Registers (GPRs)

OTBN has 32 General Purpose Registers (GPRs).
Each GPR is 32b wide.
General Purpose Registers in OTBN are mainly used for control flow.
The GPRs are defined in line with RV32I.

Note: GPRs and Wide Data Registers (WDRs) are separate register files.
They are only accessible through their respective instruction subset:
GPRs are accessible from the base instruction subset, and WDRs are accessible from the big number instruction subset (`BN` instructions).

<table>
  <tr>
    <td><code>x0</code></td>
    <td><strong>Zero</strong>. Always reads 0. Writes are ignored.</td>
  </tr>
  <tr>
    <td><code>x1</code></td>
    <td>
      <strong>Return address</strong>.
      Access to the call stack.
      Reading <code>x1</code> pops an address from the call stack.
      Writing <code>x1</code> pushes a return address to the call stack.
      Reading from an empty call stack results in an alert.
    </td>
  </tr>
  <tr>
    <td><code>x2</code></td>
    <td><strong>General Purpose Register 2</strong>.</td>
  </tr>
  <tr>
    <td>...</td>
    <td></td>
  </tr>
  <tr>
    <td><code>x31</code></td>
    <td><strong>General Purpose Register 31</strong>.</td>
  </tr>
</table>

Note: Currently, OTBN has no "standard calling convention," and GPRs except for `x0` and `x1` can be used for any purpose.
If, at one point, a calling convention is needed, it is expected to be aligned with the RISC-V standard calling conventions, and the roles assigned to registers in that convention.
Even without a agreed-on calling convention, software authors are encouraged to follow the RISC-V calling convention where it makes sense.
For example, good choices for temporary registers are `x6`, `x7`, `x28`, `x29`, `x30`, and `x31`.

### Control and Status Registers (CSRs)

Control and Status Registers (CSRs) are 32b wide registers used for "special" purposes, as detailed in their description;
they are not related to the GPRs.
CSRs can be accessed through dedicated instructions, `CSRRS` and `CSRRW`.

<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Privilege</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x7C0</td>
      <td>RW</td>
      <td>
        <strong>FLAGS</strong>.
        Wide arithmetic flags.
        This CSR provides access to the flags used in wide integer arithmetic.
        <table>
          <thead>
            <tr><th>Bit</th><th>Description</th></tr>
          </thead>
          <tbody>
            <tr><td>0</td><td>Carry of Flag Group 0</td></tr>
            <tr><td>1</td><td>LSb of Flag Group 0</td></tr>
            <tr><td>2</td><td>MSb of Flag Group 0</td></tr>
            <tr><td>3</td><td>Zero of Flag Group 0</td></tr>
            <tr><td>4</td><td>Carry of Flag Group 1</td></tr>
            <tr><td>5</td><td>LSb of Flag Group 1</td></tr>
            <tr><td>6</td><td>MSb of Flag Group 1</td></tr>
            <tr><td>7</td><td>Zero of Flag Group 1</td></tr>
          </tbody>
        </table>
      </td>
    </tr>
    <tr>
      <td>0x7D0</td>
      <td>RW</td>
      <td>
        <strong>MOD0</strong>.
        Bits [31:0] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D1</td>
      <td>RW</td>
      <td>
        <strong>MOD1</strong>.
        Bits [63:32] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D2</td>
      <td>RW</td>
      <td>
        <strong>MOD2</strong>.
        Bits [95:64] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D3</td>
      <td>RW</td>
      <td>
        <strong>MOD3</strong>.
        Bits [127:96] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D4</td>
      <td>RW</td>
      <td>
        <strong>MOD4</strong>.
        Bits [159:128] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D5</td>
      <td>RW</td>
      <td>
        <strong>MOD5</strong>.
        Bits [191:160] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D6</td>
      <td>RW</td>
      <td>
        <strong>MOD6</strong>.
        Bits [223:192] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0x7D7</td>
      <td>RW</td>
      <td>
        <strong>MOD7</strong>.
        Bits [255:224] of the modulus operand, used in the BN.ADDM/BN.SUBM instructions.
        This CSR is mapped to the MOD WSR.
      </td>
    </tr>
    <tr>
      <td>0xFC0</td>
      <td>R</td>
      <td>
        <strong>RND</strong>.
        A random number.
      </td>
    </tr>
  </tbody>
</table>

### Wide Data Registers (WDRs)

In addition to the 32b wide GPRs, OTBN has a second "wide" register file, which is used by the big number instruction subset.
This register file consists of NWDR = 32 Wide Data Registers (WDRs).
Each WDR is WLEN = 256b wide.

Wide Data Registers (WDRs) and the 32b General Purpose Registers (GPRs) are separate register files.
They are only accessible through their respective instruction subset:
GPRs are accessible from the base instruction subset, and WDRs are accessible from the big number instruction subset (`BN` instructions).

| Register |
|----------|
| w0       |
| w1       |
| ...      |
| w31      |

### Wide Special Purpose Registers (WSRs)

In addition to the Wide Data Registers, BN instructions can also access WLEN-sized special purpose registers, short WSRs.

<table>
  <thead>
    <tr>
      <th>Number</th>
      <th>Privilege</th>
      <th>Description</th>
    </tr>
  </thead>
  <tbody>
    <tr>
      <td>0x1</td>
      <td>RW</td>
      <td>
        <strong>MOD</strong>
        Modulus.
        To be used in the BN.ADDM and BN.SUBM instructions.
        This WSR is mapped to the MOD0 to MOD7 CSRs.
      </td>
    </tr>
    <tr>
      <td>0x2</td>
      <td>R</td>
      <td>
        <strong>RND</strong>
        A random number.
      </td>
    </tr>
  </tbody>
</table>

### Flags

In addition to the wide register file, OTBN maintains global state in two groups of flags for the use by wide integer operations.
Flag groups are named Flag Group 0 (`FG0`), and Flag Group 1 (`FG1`).
Each group consists of four flags.
Each flag is a single bit.

- `C` (Carry flag).
  Set to 1 an overflow occurred in the last arithmetic instruction.

- `L` (LSb flag).
  The least significant bit of the result of the last arithmetic or shift instruction.

- `M` (MSb flag)
  The most significant bit of the result of the last arithmetic or shift instruction.

- `Z` (Zero Flag)
  Set to 1 if the result of the last operation was zero; otherwise 0.

### Loop Stack

The LOOP instruction allows for nested loops; the active loops are stored on the loop stack.
Each loop stack entry is a tuple of loop count, start address, and end address.
The number of entries in the loop stack is implementation-dependent.

### Call Stack

A stack (LIFO) of function call return addresses (also known as "return address stack").
The number of entries in this stack is implementation-dependent.

The call stack is accessed through the `x1` GPR (return address).
Writing to `x1` pushes to the call stack, reading from it pops an item.

### Accumulator

A WLEN bit wide accumulator used by the BN.MULQACC instruction.

## Instruction Format

All instructions are a fixed 32b in length and must be aligned on a four byte-boundary in memory.

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The instruction encoding has not been finalized yet.
  See [issue #2391](https://github.com/lowRISC/opentitan/issues/2391) for the current status.
</div>

## Base Instruction Subset

The base instruction set of OTBN is a limited 32b instruction set.
It is used together with the 32b wide General Purpose Register file.
The primary use of the base instruction set is the control flow in applications.

The base instruction set is an extended subset of [RISC-V's RV32I_Zcsr](https://riscv.org/specifications/isa-spec-pdf/).
Refer to the [RISC-V Unprivileged Specification](https://riscv.org/specifications/isa-spec-pdf/) for a detailed instruction specification.
Not all RV32 instructions are implemented.
The implemented subset is shown below.
Many instructions in the base instruction set have an equivalent in the big number instruction subset, enabling processor logic to be shared between the instruction subsets.

### ADD

**Add.**

```
ADD <grd>, <grs1>, <grs2>
```

This instruction is defined in the RV32I instruction set.

### ADDI

**Add Immediate.**

```
ADDI <grd>, <grs1>, <imm>
```

This instruction is defined in the RV32I instruction set.

### LUI

**Load Upper Immediate.**

```
LUI <grd>, <imm>
```

This instruction is defined in the RV32I instruction set.

### SUB

**Subtract.**

```
SUB <grd>, <grs1>, <grs2>
```

This instruction is defined in the RV32I instruction set.

### AND

**Bitwise AND.**

```
AND <grd>, <grs1>, <grs2>
```

This instruction is defined in the RV32I instruction set.

### ANDI

**Bitwise AND (immediate).**

```
ANDI <grd>, <grs1>, <imm>
```

This instruction is defined in the RV32I instruction set.

### OR

**Bitwise OR.**

```
OR <grd>, <grs1>, <grs2>
```

This instruction is defined in the RV32I instruction set.

### ORI

**Bitwise OR (immediate).**

```
ORI <grd>, <grs1>, <imm>
```

This instruction is defined in the RV32I instruction set.

### XOR

**Bitwise XOR.**

```
XOR <grd>, <grs1>, <rs2>
```

This instruction is defined in the RV32I instruction set.

### XORI

**Bitwise XOR (immediate).**

```
XORI <grd>, <grs1>, <imm>
```

This instruction is defined in the RV32I instruction set.

### LW

**Load Word.**

```
LW <grd>,<offset>(<grs1>)
```

This instruction is defined in the RV32I instruction set.

### SW

**Store Word.**

```
SW <grs2>, <offset>(<grs1>)
```

This instruction is defined in the RV32I instruction set.

### BEQ

**Branch Equal.**

```
BEQ <grs1>, <grs2>, <offset>
```

This instruction is defined in the RV32I instruction set.

### BNE

**Branch Not Equal.**

```
BNE <grs1>, <grs2>, <offset>
```

This instruction is defined in the RV32I instruction set.

### LOOP

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The LOOP and LOOPI instructions are under-specified, and improvements to it are being discussed.
  See https://github.com/lowRISC/opentitan/issues/2496 for up-to-date information.
</div>

**Loop (indirect).**
Repeat a sequence of code multiple times.
The number of iterations is a GPR value.
The length of the loop is given as immediate.

```
LOOP <grs>, <bodysize>
```

Alternative assembly notation:
The size of the loop body is given by the number of instructions in the parentheses.

```
LOOP <grs> (
  # loop body
)
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;grs&gt;</code></td>
      <td>Name of the GPR containing the number of iterations, encoded in the "grs" field.</td>
    </tr>
    <tr>
      <td><code>&lt;bodysize&gt;</code></td>
      <td>Number of instructions in the loop body (immediate).</td>
    </tr>
  </tbody>
</table>

### LOOPI

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The LOOP and LOOPI instructions are under-specified, and improvements to it are being discussed.
  See https://github.com/lowRISC/opentitan/issues/2496 for up-to-date information.
</div>

**Loop Immediate.**
Repeat a sequence of code multiple times.
The number of iterations is given as an immediate, as is the length of the loop.
The number of iterations must be larger than zero.

```
LOOPI <iterations>, <bodysize>
```

Alternative assembly notation.
The size of the loop body is given by the number of instructions in the parentheses.

```
LOOPI <iterations> (
  # loop body
)
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;iterations&gt;</code></td>
      <td>Number of iterations (immediate).</td>
    </tr>
    <tr>
      <td><code>&lt;bodysize&gt;</code></td>
      <td>Number of instructions in the loop body (immediate).</td>
    </tr>
  </tbody>
</table>

### JAL

**Jump and Link.**

```
JAL <grd>, <offset>
```

This instruction is defined in the RV32I instruction set.

Unlike in RV32I, the `x1` (return address) GPR is hard-wired to the call stack.
To call a subroutine use `jal x1, <offset>`.

### JALR

**Jump and Link Register.**

```
JALR <grd>, <grs1>, <offset>
```

This instruction is defined in the RV32I instruction set.

Unlike in RV32I, the `x1` (return address) GPR is hard-wired to the call stack.
To return from a subroutine, use `jalr x0, x1, 0`.

### CSRRS

**Atomic Read and Set Bits in CSR.**

```
CSRRS <grd>, <csr>, <grs>
```

This instruction is defined in the RV32I instruction set.

### CSRRW

**Atomic Read/Write CSR.**

```
CSRRW <grd>, <csr>, <grs>
```

This instruction is defined in the RV32I instruction set.

### ECALL

**Environment Call.**
Triggers the `done` interrupt to indicate the completion of the operation.

This instruction is defined in the RV32I instruction set.

## Big Number Instruction Subset

All Big Number (BN) instructions operate on the wide register file WREG.

### BN.ADD

**Add.**
Adds two WDR values, writes the result to the destination WDR and updates flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.ADD <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B] [, FG<flag_group>]
```


<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
(result, flags_out) = AddWithCarry(a, b_shifted, "0")

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.ADDC

**Add with Carry.**
Adds two WDR values and the Carry flag value, writes the result to the destination WDR, and updates the flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.ADDC <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B] [, FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```
b_shifted = ShiftReg(b, st, sb)
(result, flags_out) = AddWithCarry(a, b_shifted, FLAGS[flag_group].C)

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.ADDI

**Add Immediate.**
Adds a zero-extended immediate to the value of a WDR, writes the result to the destination WDR, and updates the flags.

```
BN.ADDI <wrd>, <wrs1>, <imm> [, FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs" field.</td>
    </tr>
    <tr>
      <td><code>&lt;imm&gt;</code></td>
      <td>Immediate value.</td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)

fg = DecodeFlagGroup(flag_group)
i = ZeroExtend(imm, WLEN)
```

#### Operation

```python3
(result, flags_out) = AddWithCarry(a, i, "0")

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.ADDM

**Pseudo-Modulo Add.**
Adds two WDR values, subtracts the value of the MOD WSR once if the result is equal or larger than MOD, and writes the result to the destination WDR.
This operation is a modulo addition if the sum of the two input registers is smaller than twice the value of the MOD WSR.
Flags are not used or saved.

```
BN.ADDM <wrd>, <wrs1>, <wrs2>
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)
```

#### Operation

```python3
(result, ) = AddWithCarry(a, b, "0")

if result >= MOD:
  result = result - MOD

WDR[d] = result
```

### BN.MULQACC

**Quarter-Word Multiply and Accumulate.**
Multiplies two WLEN/4 WDR values and adds the result to an accumulator after shifting it.
Optionally shift some/all of the resulting accumulator value out to a destination WDR.

```
BN.MULQACC[<wb_variant>][<zero_acc>] [<wrd><wrd_hwsel>,] <wrs1><wrs1_qwsel>, <wrs2><wrs_qwsel>, <acc_shift_imm>
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wb_variant&gt;</code></td>
      <td>
        Result writeback instruction variant.
        Optional.
        If no writeback variant is chosen, no destination register is written, and the multiplication result is only stored in the accumulator.
        Valid values:
        <ul>
          <li>
            <code>.SO</code> -
            Shift out the lower half-word of the value stored in the accumulator to a WLEN/2-sized half-word of the destination WDR.
            The destination half-word is selected by the "wrd_hwsel" field.
          </li>
          <li>
            <code>.WO</code> -
            Write the value stored in the accumulator to the destination WDR.
          </li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;zero_acc&gt;</code></td>
      <td>
        Zero the accumulator before accumulating the multiply result.
        Optional.
        Valid value: <code>.Z</code>
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>
        Name of the destination WDR, encoded in the "wrd" field.
        Only required for .SO/.WO instruction variant.
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrd_hwsel&gt;</code></td>
      <td>
        Half-word select for &lt;wrd&gt.
        Only required for the <code>.SO</code> instruction variant.
        Valid values:
        <ul>
          <li><code>L</code> (less significant half-word)</li>
          <li><code>U</code> (more significant half-word)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1_qwsel&gt;</code></td>
      <td>
        Quarter-word select for &lt;wrs1&gt.
        Valid values:
        <ul>
          <li><code>.0</code>: Select <code>wrs1[WLEN/4-1:0]</code> (least significant quarter-word)</li>
          <li><code>.1</code>: Select <code>wrs1[WLEN/2:WLEN/4]</code></li>
          <li><code>.2</code>: Select <code>wrs1[WLEN/4*3-1:WLEN/2]</code></li>
          <li><code>.3</code>: Select <code>wrs1[WLEN-1:WLEN/4*3]</code> (most significant quarter-word)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2_qwsel&gt;</code></td>
      <td>
        Quarter-word select for &lt;wrs2&gt.
        Valid values:
        <ul>
          <li><code>.0</code>: Select <code>wrs2[WLEN/4-1:0]</code> (least significant quarter-word)</li>
          <li><code>.1</code>: Select <code>wrs2[WLEN/2:WLEN/4]</code></li>
          <li><code>.2</code>: Select <code>wrs2[WLEN/4*3-1:WLEN/2]</code></li>
          <li><code>.3</code>: Select <code>wrs2[WLEN-1:WLEN/4*3]</code> (most significant quarter-word)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;acc_shift_imm&gt;</code></td>
      <td>
        How many quarter-words (WLEN/4 bit) to shift the WLEN/2 multiply result before accumulating.
        Valid values: 0, 1, 2, 3
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
writeback_variant = DecodeMulqaccVariant(wb_variant)
zero_accumulator = DecodeMulqaccZeroacc(zero_acc)

d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

d_hwsel = DecodeHalfWordSelect(wrd_hwsel)
a_qwsel = DecodeQuarterWordSelect(wrs1_qwsel)
b_qwsel = DecodeQuarterWordSelect(wrs2_qwsel)
```

#### Operation

```python3
a_qw = GetQuarterWord(a, a_qwsel)
b_qw = GetQuarterWord(b, b_qwsel)

mul_res = a_qw * b_qw

if zero_accumulator:
  ACC = 0

ACC = ACC + (mul_res << (acc_shift_imm * WLEN / 4))

if writeback_variant == 'shiftout':
  if d_hwsel == 'L':
    WDR[d][WLEN/2-1:0] = ACC[WLEN/2-1:0]
  elif d_hwsel == 'U':
    WDR[d][WLEN-1:WLEN/2] = ACC[WLEN/2-1:0]
  ACC = ACC >> (WLEN/2)

elif writeback_variant == 'writeout':
  WDR[d] = ACC
```

### BN.MULH

**Half-Word Multiply.**
Multiplies two unsigned WLEN/2 WDR values, and writes the result to a WLEN destination WDR.

This instruction is optional and implementations may not provide it;
`BN.MULQACC` can be used instead.

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The BN.MULH instruction is a 128x128 multiplier with WLEN = 256.
  We currently *do not* plan to implement it for OpenTitan.
</div>


```
BN.MULH <wrd>, <wrs1><wrs1_hwsel>, <wrs2><wrs2_hwsel>
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>
        Name of the destination WDR, encoded in the "wrd" field.
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1_hwsel&gt;</code></td>
      <td>
        Half-word select for &lt;wrs1&gt.
        Valid values:
        <ul>
          <li><code>L</code> (less significant half-word)</li>
          <li><code>U</code> (more significant half-word)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2_hwsel&gt;</code></td>
      <td>
        Half-word select for &lt;wrs2&gt.
        Valid values:
        <ul>
          <li><code>L</code> (less significant half-word)</li>
          <li><code>U</code> (more significant half-word)</li>
        </ul>
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

a_hwsel = DecodeHalfWordSelect(wrs1_hwsel)
b_hwsel = DecodeHalfWordSelect(wrs2_hwsel)
```

#### Operation

```python3
a_hw = GetHalfWord(a, a_hwsel)
b_hw = GetHalfWord(b, b_hwsel)

WDR[d] = a_hw * b_hw
```

### BN.SUB

**Subtraction.**
Subtracts the second WDR value from the first one, writes the result to the destination WDR and updates flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.SUB <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B] [, FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
(result, flags_out) = AddWithCarry(a, -b_shifted, "0")

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.SUBB

**Subtract with Borrow.**
Subtracts the second WDR value and the Carry from the first one, writes the result to the destination WDR, and updates the flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.SUBB <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B] [, FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
(result, flags_out) = AddWithCarry(a, -b_shifted, ~FLAGS[flag_group].C)

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.SUBI

**Subtract Immediate.**
Subtracts a zero-extended immediate from the value of a WDR, writes the result to the destination WDR, and updates the flags.

```
BN.SUBI <wrd>, <wrs1>, <imm> [, FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;imm&gt;</code></td>
      <td>Immediate value.</td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)

fg = DecodeFlagGroup(flag_group)
i = ZeroExtend(imm, WLEN)
```

#### Operation

```python3
(result, flags_out) = AddWithCarry(a, -i, "0")

WDR[d] = result
FLAGS[flag_group] = flags_out
```

### BN.SUBM

**Pseudo-Modulo Subtraction.**
Subtracts the second WDR value from the first WDR value, performs a modulo operation with the MOD WSR, and writes the result to the destination WDR.
This operation is equivalent to a modulo subtraction as long as `wrs1 - wrs2 >= -MOD` holds.
This constraint is not checked in hardware.
Flags are not used or saved.

```
BN.SUBM <wrd>, <wrs1>, <wrs2>
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)
```

#### Operation

```python3
(result, ) = AddWithCarry(a, -b, "0")

if result >= MOD:
  result = result - MOD

WDR[d] = result
```

### BN.AND

**Bitwise AND.**
Performs a bitwise and operation.
Takes the values stored in registers referenced by `wrs1` and `wrs2` and stores the result in the register referenced by `wrd`.
The content of the second source register can be shifted by an immediate before it is consumed by the operation.

```
BN.AND <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
result = a & b_shifted

WDR[d] = result
```

### BN.OR

**Bitwise OR.**
Performs a bitwise or operation.
Takes the values stored in WDRs referenced by `wrs1` and `wrs2` and stores the result in the WDR referenced by `wrd`.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.OR <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
result = a | b_shifted

WDR[d] = result
```

### BN.NOT

**Bitwise NOT.**
Performs a bitwise negation.
Takes the value stored in the WDR referenced by `wrs` and stores the result in the WDR referenced by `wrd`.
The content of the source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.NOT <wrd>, <wrs> [, <shift_type> <shift_bytes>B]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)

sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
a_shifted = ShiftReg(a, st, sb)
result = ~a_shifted

WDR[d] = result
```

### BN.XOR

**Bitwise XOR.**
Performs a bitwise xor operation.
Takes the values stored in WDRs referenced by `wrs1` and `wrs2` and stores the result in the WDR referenced by `wrd`.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.

```
BN.XOR <wrd>, <wrs1>, <wrs2> [, <shift_type> <shift_bytes>B]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)

sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```
b_shifted = ShiftReg(b, st, sb)
result = a ^ b_shifted

WDR[d] = result
```

### BN.RSHI

**Concatenate and right shift immediate.**
The concatenation of the content from the WDRs referenced by `wrs1` and `wrs2` (`wrs1` forms the upper part) is right shifted by an immediate value and truncated to WLEN bit.
The result is stored in the WDR referenced by `wrd`.

```
BN.RSHI <wrd>, <wrs1>, <wrs2> >> imm
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;imm&gt;</code></td>
      <td>Number of bits to shift the second source register by. Valid range: 0 .. (WLEN-1)</td>
    </tr>
  </tbody>
</table>

#### Decode

```
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)
imm = Uint(imm)
```

#### Operation

```
WDR[d] = ((rs1 | rs2) >> im)[WLEN-1:0]
```

### BN.SEL

**Flag Select.**
Returns in the destination WDR the value of the first source WDR if the flag in the chosen flag group is set, otherwise returns the value of the second source WDR.

```
BN.SEL <wrd>, <wrs1>, <wrs2>, [FG<flag_group>.]<flag>
```


<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag&gt;</code></td>
      <td>
        Flag to check, encoded in the flag field.
        Valid values:
        <ul>
          <li><code>C</code> if <code>flag == 0</code> (Carry flag)</li>
          <li><code>M</code> if <code>flag == 1</code> (MSb flag)</li>
          <li><code>L</code> if <code>flag == 2</code> (LSb flag)</li>
          <li><code>Z</code> if <code>flag == 3</code> (Zero flag)</li>
        </ul>
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
d = UInt(wrd)
a = UInt(wrs1)
b = UInt(wrs2)
fg = DecodeFlagGroup(flag_group)
flag = DecodeFlag(flag)
```

#### Operation

```
flag_is_set = FLAGS[fg].get(flag)

WDR[d] = wrs1 if flag_is_set else wrs2
```

### BN.CMP

**Compare.**
Subtracts the second WDR value from the first one and updates flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.
This instruction is identical to BN.SUB, except that no result register is written.

```
BN.CMP <wrs1>, <wrs2>, [FG<flag_group>]
```


<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```
b_shifted = ShiftReg(b, st, sb)
(, flags_out) = AddWithCarry(a, -b_shifted, "0")

FLAGS[flag_group] = flags_out
```

### BN.CMPB

**Compare with Borrow.**
Subtracts the second WDR value and the Carry from the first one, and updates the flags.
The content of the second source WDR can be shifted by an immediate before it is consumed by the operation.
This instruction is identical to BN.SUBB, except that no result register is written.

```
BN.CMPB <wrs1>, <wrs2>, [FG<flag_group>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrs1&gt;</code></td>
      <td>Name of the first source WDR, encoded in the "wrs1" field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs2&gt;</code></td>
      <td>Name of the second source WDR, encoded in the "wrs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;shift_type&gt;</code></td>
      <td>
        Optional shift type applied to the second source WDR, defaulting to <code>&lt;&lt;</code>, encoded in the <code>shift_type</code> field.
        It can have the following values:
        <ul>
          <li><code>&lt;&lt;</code> if <code>shift_type == 1</code> (logical shift left)</li>
          <li><code>&gt;&gt;</code> if <code>shift_type == 0</code> (logical shift right)</li>
        </ul>
      </td>
    </tr>
    <tr>
      <td><code>&lt;shift_bytes&gt;</code></td>
      <td>
        Number of bytes to shift the second source WDR by.
        Optional, defaulting to 0.
        Valid values: 0..31
      </td>
    </tr>
    <tr>
      <td><code>&lt;flag_group&gt;</code></td>
      <td>
        Flag group to use.
        Optional, defaulting to 0.
        Valid values: 0, 1
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
a = UInt(wrs1)
b = UInt(wrs2)

fg = DecodeFlagGroup(flag_group)
sb = UInt(shift_bytes)
st = DecodeShiftType(shift_type)
```

#### Operation

```python3
b_shifted = ShiftReg(b, st, sb)
(, flags_out) = AddWithCarry(a, -b_shifted, ~FLAGS[flag_group].C)

FLAGS[flag_group] = flags_out
```

### BN.LID

**Load Word (indirect source, indirect destination).**
Calculates a byte memory address by adding the offset to the value in the GPR `grs1`.
The value from this memory address is then copied into the WDR pointed to by the value in GPR `grd`.

After the operation, either the value in the GPR `grs1`, or the value in `grd` can be optionally incremented.

- If `grs1_inc` is set, the value in `grs1` is incremented by the value WLEN/8 (one word).
- If `grd_inc` is set, the value in `grd` is incremented by the value 1.

TODO: how to handle overflows?

```
BN.LID <grd>[<grd_inc>], <offset>(<grs1>[<grs1_inc>])
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;grd&gt;</code></td>
      <td>Name of the GPR referencing the destination WDR, encoded in the "grd" field.</td>
    </tr>
    <tr>
      <td><code>&lt;grs1&gt;</code></td>
      <td>
        Name of the GPR containing the memory byte address, encoded in the "grs1" field.
        The value contained in the referenced GPR must be WLEN-aligned.
      </td>
    </tr>
    <tr>
      <td><code>&lt;offset&gt;</code></td>
      <td>
        Offset value.
        Must be WLEN-aligned.
      </td>
    </tr>
    <tr>
      <td><code>&lt;grs1_inc&gt;</code></td>
      <td>
        Increment the value in "grs1" by WLEN/8 (one word).
        Cannot be specified together with "grd_inc".
      </td>
    </tr>
    <tr>
      <td><code>&lt;grd_inc&gt;</code></td>
      <td>
        Increment the value in "grd" by 1.
        Cannot be specified together with "grs1_inc".
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
rd = UInt(grd)
rs1 = UInt(grs1)
offset = UInt(offset)
```

#### Operation

```python3
memaddr = GPR[rs1] + (offset / WLEN / 8)
wdr_dest = GPR[rd]

WDR[wdr_dest] = LoadWlenWordFromMemory(memaddr)

if grs1_inc and grd_inc:
    raise Unsupported() # prevented in encoding
if grs1_inc:
    GPR[rs1] = GPR[rs1] + (WLEN / 8)
if grd_inc:
    GPR[rd] = GPR[rd] + 1
```

### BN.SID

**Store Word (indirect source, indirect destination).**
Calculates a byte memory address by adding the offset to the value in the GPR `grs1`.
The value from the WDR pointed to by `grs2` is then copied into the memory.

After the operation, either the value in the GPR `grs1`, or the value in `grs2` can be optionally incremented.

- If `grs1_inc` is set, the value in `grs1` is incremented by the value WLEN/8 (one word).
- If `grs2_inc` is set, the value in `grs2` is incremented by the value 1.

```
BN.SID <grs1>[<grs1_inc>], <offset>(<grs2>[<grs2_inc>])
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;grs1&gt;</code></td>
      <td>
        Name of the GPR containing the memory byte address, encoded in the "grs1" field.
        The value contained in the referenced GPR must be WLEN-aligned.
      </td>
    </tr>
    <tr>
      <td><code>&lt;grs2&gt;</code></td>
      <td>Name of the GPR referencing the source WDR, encoded in the "grs2" field.</td>
    </tr>
    <tr>
      <td><code>&lt;offset&gt;</code></td>
      <td>
        Offset value.
        Must be WLEN-aligned.
      </td>
    </tr>
    <tr>
      <td><code>&lt;grs1_inc&gt;</code></td>
      <td>
        Increment the value in "grs1" by WLEN/8 (one word).
        Cannot be specified together with "grs2_inc".
      </td>
    </tr>
    <tr>
      <td><code>&lt;grs2_inc&gt;</code></td>
      <td>
        Increment the value in "grs2" by 1.
        Cannot be specified together with "grs1_inc".
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
rs1 = UInt(grs1)
rs2 = UInt(grs2)
offset = UInt(offset)
```

#### Operation

```python3
memaddr = GPR[rs1] + offset / WLEN / 8
wdr_src = GPR[rs2]

StoreWlenWordToMemory(memaddr, WDR[wdr_src])

if grs1_inc and grs2_inc:
    raise Unsupported() # prevented in encoding
if grs1_inc:
    GPR[rs1] = GPR[rs1] + (WLEN / 8)
if grs2_inc:
    GPR[rs2] = GPR[rs2] + 1
```

### BN.MOV

**Copy content between WDRs (direct addressing).**

```
BN.MOV <wrd>, <wrs>
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;wrd&gt;</code></td>
      <td>Name of the destination WDR, encoded in the "wrd field.</td>
    </tr>
    <tr>
      <td><code>&lt;wrs&gt;</code></td>
      <td>Name of the source WDR, encoded in the "wrs" field.</td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
s = UInt(wrs)
d = UInt(wrd)
```

#### Operation

```
WDR[d] = WDR[s]
```

### BN.MOVR

**Copy content between WDRs (register-indirect addressing).**

Copy WDR contents between registers with indirect addressing.
Optionally, either the source or the destination register address can be incremented by 1.

```
BN.MOVR <grd>[<grd_inc>], <grs>[<grs_inc>]
```

<table>
  <thead>
    <tr><th>Assembly symbol</th><th>Description</th></tr>
  </thead>
  <tbody>
    <tr>
      <td><code>&lt;grd&gt;</code></td>
      <td>Name of the GPR containing the destination WDR, encoded in the "grd" field.</td>
    </tr>
    <tr>
      <td><code>&lt;grs&gt;</code></td>
      <td>Name of the GPR containing the source WDR, encoded in the "grs" field.</td>
    </tr>
    <tr>
      <td><code>&lt;grd_inc&gt;</code></td>
      <td>
        Increment the value in "grd" by 1.
        Cannot be specified together with "grs_inc".
      </td>
    </tr>
    <tr>
      <td><code>&lt;grs_inc&gt;</code></td>
      <td>
        Increment the value in "grs" by 1.
        Cannot be specified together with "grd_inc".
      </td>
    </tr>
  </tbody>
</table>

#### Decode

```python3
s = UInt(grs)
d = UInt(grd)
```

#### Operation

```python3
WDR[GPR[d]] = WDR[GPR[s]]

if grs_inc:
  GPR[s] = GPR[s] + 1
if grd_inc:
  GPR[d] = GPR[d] + 1
```

### BN.WSRRS

**Atomic Read and Set Bits in WSR.**

```python3
BN.WSRRS <wrd>, <wsr>, <wrs>
```

### BN.WSRRW

**Atomic Read/Write WSR.**

```python3
BN.WSRRW <wrd>, <csr>, <wrs>
```

## Pseudo-Code Functions for BN Instructions

The instruction description uses Python-based pseudocode.
Commonly used functions are defined once below.

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  This "pseudo-code" is intended to be Python 3, and contains known inconsistencies at the moment.
  It will be further refined as we make progress in the implementation of a simulator using this syntax.
</div>

```python3
class Flag(Enum):
  C: Bits[1]
  M: Bits[1]
  L: Bits[1]
  Z: Bits[1]

class FlagGroup:
  C: Bits[1]
  M: Bits[1]
  L: Bits[1]
  Z: Bits[1]

  def set(self, flag: Flag, value: Bits[1]):
    assert flag in Flag

    if flag == Flag.C:
      self.C = value
    elif flag == Flag.M:
      self.M = value
    elif flag == Flag.L:
      self.L = value
    elif flag == Flag.Z:
      self.Z = value

  def get(self, flag: Flag):
    assert flag in Flag

    if flag == Flag.C:
      return self.C
    elif flag == Flag.M:
      return self.M
    elif flag == Flag.L:
      return self.L
    elif flag == Flag.Z:
      return self.Z


class ShiftType(Enum):
  LSL = 0 # logical shift left
  LSR = 1 # logical shift right

class HalfWord(Enum):
  LOWER = 0 # lower or less significant half-word
  UPPER = 1 # upper or more significant half-word

def DecodeShiftType(st: Bits(1)) -> ShiftType:
  if st == 0:
    return ShiftType.LSL
  elif st == 1:
    return ShiftType.LSR
  else:
    raise UndefinedException()

def DecodeFlagGroup(flag_group: Bits(1)) -> UInt:
  if flag_group > 1:
    raise UndefinedException()
  return UInt(flag_group)

def DecodeFlag(flag: Bits(1)) -> Flag:
  if flag == 0:
    return ShiftType.C
  elif flag == 1:
    return ShiftType.M
  elif flag == 2:
    return ShiftType.L
  elif flag == 3:
    return ShiftType.Z
  else:
    raise UndefinedException()


def ShiftReg(reg, shift_type, shift_bytes) -> Bits(N):
  if ShiftType == ShiftType.LSL:
    return GPR[reg] << shift_bytes << 3
  elif ShiftType == ShiftType.LSR:
    return GPR[reg] >> shift_bytes >> 3

def AddWithCarry(a: Bits(WLEN), b: Bits(WLEN), carry_in: Bits(1)) -> (Bits(WLEN), FlagGroup):
  result: Bits[WLEN+1] = a + b + carry_in

  flags_out = FlagGroup()
  flags_out.C = result[WLEN]
  flags_out.L = result[0]
  flags_out.M = result[WLEN-1]
  flags_out.Z = (result == 0)

  return (result[WLEN-1:0], flags_out)

def DecodeHalfWordSelect(hwsel: Bits(1)) -> HalfWord:
  if hwsel == 0:
    return HalfWord.LOWER
  elif hwsel == 1:
    return HalfWord.UPPER
  else:
    raise UndefinedException()

def GetHalfWord(reg: integer, hwsel: HalfWord) -> Bits(WLEN/2):
  if hwsel == HalfWord.LOWER:
    return GPR[reg][WLEN/2-1:0]
  elif hwsel == HalfWord.UPPER:
    return GPR[reg][WLEN-1:WLEN/2]

def LoadWlenWordFromMemory(byteaddr: integer) -> Bits(WLEN):
  wordaddr = byteaddr >> 5
  return DMEM[wordaddr]

def StoreWlenWordToMemory(byteaddr: integer, storedata: Bits(WLEN)):
  wordaddr = byteaddr >> 5
  DMEM[wordaddr] = storedata
```

# Theory of Operations

## Block Diagram

![OTBN architecture block diagram](otbn_blockarch.svg)

## Hardware Interfaces

{{< hwcfg "hw/ip/otbn/data/otbn.hjson" >}}

## Design Details

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  To be filled in as we create the implementation.
</div>

# Programmers Guide

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  This section will be written as we move on in the design and implementation process.
</div>

## Operation

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  The exact sequence of operations is not yet finalized.
</div>

Rough expected process:

* Write {{< regref "IMEM" >}}
* Write {{< regref "DMEM" >}}
* Write `1` to {{< regref "CMD.start" >}}
* Wait for `done` interrupt
* Retrieve results by reading {{< regref "DMEM" >}}

## Error conditions

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  To be filled in as we create the implementation.
</div>

## Register Table

{{< registers "hw/ip/otbn/data/otbn.hjson" >}}

## Algorithic Example: Replacing BN.MULH with BN.MULQACC

This specification gives the implementers the option to provide either a quarter-word multiply-accumulate instruction, `BN.MULQADD`, or a half-word multiply instruction, `BN.MULH`.
Four `BN.MULQACC` can be used to replace one `BN.MULH` instruction, which is able to operate on twice the data size.

`BN.MULH r1, r0.l, r0.u` becomes

```
BN.MULQACC.Z      r0.0, r0.2, 0
BN.MULQACC        r0.1, r0.0, 64
BN.MULQACC        r0.0, r0.3, 64
BN.MULQACC.WO r1, r0.1, r0.3, 128
```

## Algorithmic Example: Multiplying two WLEN numbers with BN.MULQACC

The big number instruction subset of OTBN generally operates on WLEN bit numbers.
However, the multiplication instructions only operate on half or quarter-words of WLEN bit.
This section outlines a technique to multiply two WLEN-bit numbers with the use of the quarter-word multiply-accumulate instruction `BN.MULQACC`.

The shift out functionality can be used to perform larger multiplications without extra adds.
The table below shows how two registers `wr0` and `wr1` can be multiplied together to give a result in `wr2` and `wr3`.
The cells on the right show how the result is built up `a0:a3 = wr0.0:wr0.3` and `b0:b3 = wr1.0:wr1.3`.
The sum of a column represents WLEN/4 bits of a destination register, where `c0:c3 = wr2.0:wr2.3` and `d0:d3 = wr3.0:wr3.3`.
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
      <td><code>BN.MULQACC.Z wr0.0, wr1.0, 0</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b0</code></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.1, w1.0, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a1 * b0</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO wr2.l, wr0.0, wr1.1, 64</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
      <td style="background-color: orange"></td>
      <td style="background-color: orange" colspan="2" rowspan="1"><code>a0 * b1</code></td>
      <td style="background-color: orange"></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.2, wr1.0, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b0</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.1, wr1.1, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b1</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.0, wr1.2, 0</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b2</code></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.3, wr1.0, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a3 * b0</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.2, wr1.1, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a2 * b1</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.1, wr1.2, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a1 * b2</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO wr2.u, wr0.0, wr1.3, 64</code></td>
      <td></td>
      <td></td>
      <td style="background-color: yellow"></td>
      <td style="background-color: yellow" colspan="2" rowspan="1"><code>a0 * b3</code></td>
      <td style="background-color: yellow"></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.3, wr1.1, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b1</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.2, wr1.2, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b2</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.1, wr1.3, 0</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a1 * b3</code></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC wr0.3, wr1.2, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a3 * b2</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO wr3.l, wr0.2, wr1.3, 64</code></td>
      <td style="background-color: olive"></td>
      <td style="background-color: olive" colspan="2" rowspan="1"><code>a2 * b3</code></td>
      <td style="background-color: olive"></td>
      <td></td>
      <td></td>
      <td></td>
      <td></td>
    </tr>
    <tr>
      <td><code>BN.MULQACC.SO wr3.u, wr0.3, wr1.3, 0</code></td>
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
