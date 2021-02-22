---
title: OpenTitan Big Number Accelerator (OTBN) Instruction Set Architecture
---

This document describes the instruction set for OTBN.
For more details about the processor itself, see the [OTBN Technical Specification]({{< relref "hw/ip/otbn/doc" >}}).
In particular, this document assumes knowledge of the *Processor State* section from that guide.

The instruction set is split into *base* and *big number* subsets.
The base subset (described first) is similar to RISC-V's RV32I instruction set.
It also includes a hardware call stack and hardware loop instructions.
The big number subset is designed to operate on 256b WDRs.
It doesn't include any control flow instructions, and just supports load/store, logical and arithmetic operations.

In the instruction documentation that follows, each instruction has a syntax example.
For example, the `SW` instruction has syntax:
```
  SW <grs2>, <offset>(<grs1>)
```
This means that it takes three operands, called `grs2`, `offset` and `grs1`.
These operands are further documented in a table.
Immediate operands like `offset` show their valid range of values.

Below the table of operands is an encoding table.
This shows how the 32 bits of the instruction word are filled in.
Ranges of bits that map to an operand are named (in capitals) and those names are used in the operand table.
For example, the `SW` instruction's `offset` operand is split across two ranges of bits (31:25 and 11:7) called `OFF_1` and `OFF_0`, respectively.

# Pseudo-code for operation descriptions

Each instruction has an Operation section.
This is written in a Python-like pseudo-code, generated from the instruction set simulator (which can be found at `hw/ip/otbn/dv/otbnsim`).
The code is generated from Python, but there are some extra changes made to aid readability.

All instruction operands are considered to be in scope and have integer values.
These values come from the encoded bits in the instruction and the operand table for the instruction describes exactly how they are decoded.
Some operands are encoded PC-relative.
Such an operand has its absolute value (an address) when it appears in the Operation section.

Some state updates are represented as an assignment, but take effect at the end of the instruction.
This includes register updates or jumps and branches (updating the PC).
To denote this, we use the &#x21d0; symbol, reminiscent of Verilog's non-blocking assignment.

The program counter (PC) is represented as a variable called `PC`.

Machine registers are accessed with an array syntax.
These arrays are:

- `GPRs`: General purpose registers
- `WDRs`: Wide data registers
- `CSRs`: Control and status registers
- `WSRs`: Wide special purpose registers

Accesses to these arrays are as unsigned integers.
The instruction descriptions are written to ensure that any value written to a register is representable.
For example, a write to `GPRs[2]` will always have a non-negative value less than `1 << 32`.

Memory accesses are represented as function calls.
This is because the memory can be accessed on either the narrow or the wide side, which isn't easy to represent with an array syntax.
Memory loads are represented as `DMEM.load_u32(addr)`, `DMEM.load_u256(addr)`.
Memory stores are represented as `DMEM.store_u32(addr, value)` and `DMEM.store_u256(addr, value)`.
In all cases, memory values are interpreted as unsigned integers and, as for register accesses, the instruction descriptions are written to ensure that any value stored to memory is representable.

There are a few other helper functions, defined here to avoid having to inline their bodies into each instruction.
```python3
def from_2s_complement(n: int) -> int:
    '''Interpret the bits of unsigned integer n as a 32-bit signed integer'''
    assert 0 <= n < (1 << 32)
    return n if n < (1 << 31) else n - (1 << 32)


def to_2s_complement(n: int) -> int:
    '''Interpret the bits of signed integer n as a 32-bit unsigned integer'''
    assert -(1 << 31) <= n < (1 << 31)
    return (1 << 32) + n if n < 0 else n

def logical_byte_shift(value: int, shift_type: int, shift_bytes: int) -> int:
    '''Logical shift value by shift_bytes to the left or right.

    value should be an unsigned 256-bit value. shift_type should be 0 (shift
    left) or 1 (shift right), matching the encoding of the big number
    instructions. shift_bytes should be a non-negative number of bytes to shift
    by.

    Returns an unsigned 256-bit value, truncating on an overflowing left shift.

    '''
    mask256 = (1 << 256) - 1
    assert 0 <= value <= mask256
    assert 0 <= shift_type <= 1
    assert 0 <= shift_bytes

    shift_bits = 8 * shift_bytes
    shifted = value << shift_bits if shift_type == 0 else value >> shift_bits
    return shifted & mask256

def extract_quarter_word(value: int, qwsel: int) -> int:
    '''Extract a 64-bit quarter word from a 256-bit value.'''
    assert 0 <= value < (1 << 256)
    assert 0 <= qwsel <= 3
    return (value >> (qwsel * 64)) & ((1 << 64) - 1)
```

<!-- Documentation for the instructions in the ISA. Generated from ../data/insns.yml. -->
# Base Instruction Subset

{{< otbn_isa base >}}

# Big Number Instruction Subset

{{< otbn_isa bignum >}}
