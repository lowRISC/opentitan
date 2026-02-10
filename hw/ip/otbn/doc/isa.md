# OpenTitan Big Number Accelerator (OTBN) Instruction Set Architecture

This document describes the instruction set for OTBN.
For more details about the processor itself, see the [OTBN Technical Specification](../README.md).
In particular, this document assumes knowledge of the *Processor State* section from that guide.

The instruction set is split into *base* and *big number* subsets.
The base subset (described first) is similar to RISC-V's RV32I instruction set.
It also includes a hardware call stack and hardware loop instructions.
The big number subset is designed to operate on 256b WDRs.
It doesn't include any control flow instructions, and just supports load/store, logical and arithmetic operations.
For some of the logical and arithmetic big number operations exist SIMD variants which interpret the WDRs as vectors.

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

Some instructions can stall for one or more cycles (those instructions that access memory, CSRs or WSRs).
To represent this precisely in the pseudo-code, and the simulator reference model, such instructions execute a `yield` statement to stall the processor for a cycle.

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

def shift_vec_elem(value: int, size: int, shift_type: int, shift_bits: int) -> int:
    '''Performs a logical bit shift on an unsigned integer confined to the given bit width.

    With shift_type = 0, the value is shifted left by shift_bits; with shift_type = 1,
    the value is shifted right by shift_bits.

    The resulting shifted value is truncated to size bits.
    '''
    maskSize = (1 << size) - 1
    assert 0 <= value <= maskSize
    assert 0 <= shift_type <= 1
    assert 0 <= shift_bits

    if shift_type == 0:
        result = (value << shift_bits) & maskSize
    else:
        result = (value >> shift_bits) & maskSize

    return result

def extract_vec_elem(value: int, elem: int, size: int) -> int:
    '''Returns the elem-th vector element from a 256-bit vector of size-bit elements interpreted as
    unsigned integer.
    '''
    assert 0 <= value < (1 << 256)
    assert 0 <= elem < (256 // size)
    return (value >> (elem * size)) & ((1 << size) - 1)

def extract_quarter_word(value: int, qwsel: int) -> int:
    '''Extracts a 64-bit quarter word from a 256-bit value.'''
    assert 0 <= qwsel <= 3
    return extract_vec_elem(value, qwsel, 64)

def lower_d_bits(value: int, d: int) -> int:
    '''Extracts the lower d bits of the value.'''
    assert 0 <= d
    assert 0 <= value
    return value & ((1 << d) - 1)

def upper_d_bits(value: int, d: int) -> int:
    '''Extracts the upper d bits of the value and shifts them down by d.'''
    assert 0 <= d
    assert 0 <= value
    return lower_d_bits(value >> d, d)

def element_length_in_bits(elen: int) -> int:
    '''Returns the corresponding bit width for a given ELEN encoding.

    Encoding | ELEN | Size in bits
    0        | .8s  |  32
    1        | .4d  |  64
    2        | .2q  | 128
    '''
    assert 0 <= elen <= 2
    return 32 * (1 << elen)

def map_elems(op: Callable[[int, int], int], size: int, vec_a: int, vec_b: int) -> int:
    '''Applies the operation op to each pair of elements for the given element size.

    The vectors are expected to be 256-bit numbers where the elements are extracted from.
    The op function takes two vector elements, performs the desired operation and is expected to
    return a non-negative value.

    The results are concatenated and returned as a 256-bit number.'''
    result = 0
    for elem in range(256 // size):
        elem_a = extract_vec_elem(vec_a, elem, size)
        elem_b = extract_vec_elem(vec_b, elem, size)

        elem_c = op(elem_a, elem_b)
        elem_c = elem_c & ((1 << size) - 1)
        result |= elem_c << (elem * size)
    return result

def montgomery_mul_no_cond_subtraction(a: int, b: int, q: int, mu: int, size: int) -> int:
    '''Performs a Montgomery multiplication but without the final conditional subtraction.

    The inputs a and b are in Montgomery space.
    The result is also in Montgomery space.

    Algorithm (where []_d are the lower d bits, []^d are the higher d bits):
       r = [c + [[c]_d * mu]_d * q]^d
       # Skipped conditional subtraction step:
       # if r >= q:
       #     r -= q
       return r
    '''
    reg_c = a * b
    reg_tmp = lower_d_bits(reg_c, size)
    reg_tmp = lower_d_bits(reg_tmp * mu, size)
    r = upper_d_bits(reg_c + reg_tmp * q, size)
    return r
```

# Errors

OTBN can detect various errors when it is operating.
For details about OTBN's approach to error handling, see the [Errors section](../README.md#design-details-errors) of the Technical Specification.
The instruction descriptions below describe any software errors that executing the instruction can cause.
These errors are listed explicitly and also appear in the pseudo-code description, where the code sets a bit in the `ERR_BITS` register with a call to `state.stop_at_end_of_cycle()`.

Other errors are possible at runtime.
Specifically, any instruction that reads from a GPR or WDR might detect a register integrity error.
In this case, OTBN will set the `REG_INTG_VIOLATION` bit.
Similarly, an instruction that loads from memory might detect a DMEM integrity error.
In this case, OTBN will set the `DMEM_INTG_VIOLATION` bit.

TODO:
Specify interactions between these fatal errors and any other errors.
In particular, how do they interact with instructions that could cause other errors as well?

<!-- Documentation for the instructions in the ISA. Generated from ../data/insns.yml. -->
# Base Instruction Subset

{{#otbn-isa base }}

# Big Number Instruction Subset

{{#otbn-isa bignum }}

# Encoding overview
The following tables show the encodings of all instructions.

## Base Instruction Subset
{{#otbn-isa base_encoding }}

## Big Number Instruction Subset
{{#otbn-isa bignum_encoding }}
