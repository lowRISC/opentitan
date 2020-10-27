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
It received some inspiration from assembly code available from the [Chromium EC project](https://chromium.googlesource.com/chromiumos/platform/ec/),
which has been formally verified within the [Fiat Crypto project](http://adam.chlipala.net/papers/FiatCryptoSP19/FiatCryptoSP19.pdf).

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
            <tr><td>1</td><td>MSb of Flag Group 0</td></tr>
            <tr><td>2</td><td>LSb of Flag Group 0</td></tr>
            <tr><td>3</td><td>Zero of Flag Group 0</td></tr>
            <tr><td>4</td><td>Carry of Flag Group 1</td></tr>
            <tr><td>5</td><td>MSb of Flag Group 1</td></tr>
            <tr><td>6</td><td>LSb of Flag Group 1</td></tr>
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
      <td>0x0</td>
      <td>RW</td>
      <td>
        <strong>MOD</strong>
        Modulus.
        To be used in the BN.ADDM and BN.SUBM instructions.
        This WSR is mapped to the MOD0 to MOD7 CSRs.
      </td>
    </tr>
    <tr>
      <td>0x1</td>
      <td>R</td>
      <td>
        <strong>RND</strong>
        A random number.
      </td>
    </tr>
    <tr>
      <td>0x2</td>
      <td>RW</td>
      <td>
        <strong>ACC</strong>
        MAC Accumulator.
        This gives direct access to the accumulator register used by the BN.MULQACC instruction.
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

The `L`, `M`, and `Z` flags are determined based on the result of the operation as it is written back into the result register, without considering the overflow bit.

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

<!-- Documentation for the instructions in the ISA. Generated from ../data/insns.yml. -->
## Base Instruction Subset

{{< otbn_isa base >}}

## Big Number Instruction Subset

{{< otbn_isa bignum >}}

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
  flags_out.Z = (result[WLEN-1:0] == 0)

  return (result[WLEN-1:0], flags_out)

def SubtractWithBorrow(a: Bits(WLEN), b: Bits(WLEN), borrow_in: Bits(1)) -> (Bits(WLEN), FlagGroup):
  result: Bits[WLEN+1] = a - b - borrow_in

  flags_out = FlagGroup()
  flags_out.C = result[WLEN]
  flags_out.L = result[0]
  flags_out.M = result[WLEN-1]
  flags_out.Z = (result[WLEN-1:0] == 0)

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

By design, OTBN is a simple processor and has essentially no error handling support.
When anything goes wrong (an out-of-bounds memory operation, an invalid instruction encoding, etc.), OTBN will stop fetching instructions, and set the `ERR_CODE` register and the `err` bit of the `INTR_STATE` register.

# Programmers Guide

<div class="bd-callout bd-callout-warning">
  <h5>Note</h5>

  This section will be written as we move on in the design and implementation process.
</div>

## Memories

The OTBN processor core has access to two dedicated memories:
an instruction memory (IMEM), and a data memory (DMEM).
Each memory is 4 kiB in size.

The memory layout follows the Harvard architecture.
Both memories are byte-addressed, with addresses starting at 0.

The instruction memory (IMEM) is 32b wide and provides the instruction stream to the OTBN processor;
it cannot be read or written from user code through load or store instructions.

The data memory (DMEM) is 256b wide and read-write accessible from the base and big number instruction subsets of the OTBN processor core.
When accessed from the base instruction subset through the `LW` or `SW` instructions, accesses must read or write 32b-aligned 32b words.
When accessed from the big number instruction subset through the `BN.LID` or `BN.SID` instructions, accesses must read or write 256b-aligned 256b words.

Both memories can be accessed through OTBN's register interface ({{< regref "DMEM" >}} and {{< regref "IMEM" >}}) only when OTBN is idle, as indicated by the {{< regref "STATUS.busy">}} flag.
All memory accesses through the register interface must be word-aligned 32b word accesses.

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

`BN.MULH w1, w0.l, w0.u` becomes

```
BN.MULQACC.Z      w0.0, w0.2, 0
BN.MULQACC        w0.0, w0.3, 64
BN.MULQACC        w0.1, w0.2, 64
BN.MULQACC.WO r1, w0.1, w0.3, 128
```

## Algorithmic Example: Multiplying two WLEN numbers with BN.MULQACC

The big number instruction subset of OTBN generally operates on WLEN bit numbers.
However, the multiplication instructions only operate on half or quarter-words of WLEN bit.
This section outlines a technique to multiply two WLEN-bit numbers with the use of the quarter-word multiply-accumulate instruction `BN.MULQACC`.

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
