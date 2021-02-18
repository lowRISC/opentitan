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

In the pseudo-code in the Operation sections, all operands have integer values.
These values come from the encoded bits in the instruction and the operand table describes exactly how.
The `signed()` and `unsigned()` functions denote signed and unsigned extension from raw bits to an integer.
Signed values are encoded 2's complement.
Some operands are encoded PC-relative and have their absolute values when they appear in the Operation section.
To show this, the operand table's description includes `PC` to denote the current value of the program counter as an integer.

Below the table of operands is an encoding table.
This shows how the 32 bits of the instruction word are filled in.
Ranges of bits that map to an operand are named (in capitals) and those names are used in the operand table.
For example, the `SW` instruction's `offset` operand is split across two ranges of bits (31:25 and 11:7) called `OFF_1` and `OFF_0`, respectively.

<!-- Documentation for the instructions in the ISA. Generated from ../data/insns.yml. -->
# Base Instruction Subset

{{< otbn_isa base >}}

# Big Number Instruction Subset

{{< otbn_isa bignum >}}

# Pseudo-Code Functions for BN Instructions

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
