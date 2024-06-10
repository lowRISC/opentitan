# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum


class Cmd(IntEnum):
    '''Permitted values of the CMD register.'''
    EXECUTE = 0xd8
    SEC_WIPE_DMEM = 0xc3
    SEC_WIPE_IMEM = 0x1e


class Status(IntEnum):
    '''Permitted values of the STATUS register.'''
    IDLE = 0x00
    BUSY_EXECUTE = 0x01
    BUSY_SEC_WIPE_DMEM = 0x02
    BUSY_SEC_WIPE_IMEM = 0x03
    BUSY_SEC_WIPE_INT = 0x04
    LOCKED = 0xFF


class ErrBits(IntEnum):
    '''A copy of the list of bits in the ERR_BITS register.'''
    BAD_DATA_ADDR = 1 << 0
    BAD_INSN_ADDR = 1 << 1
    CALL_STACK = 1 << 2
    ILLEGAL_INSN = 1 << 3
    LOOP = 1 << 4
    KEY_INVALID = 1 << 5
    RND_REP_CHK_FAIL = 1 << 6
    RND_FIPS_CHK_FAIL = 1 << 7
    IMEM_INTG_VIOLATION = 1 << 16
    DMEM_INTG_VIOLATION = 1 << 17
    REG_INTG_VIOLATION = 1 << 18
    BUS_INTG_VIOLATION = 1 << 19
    BAD_INTERNAL_STATE = 1 << 20
    ILLEGAL_BUS_ACCESS = 1 << 21
    LIFECYCLE_ESCALATION = 1 << 22
    FATAL_SOFTWARE = 1 << 23
    MASK = (1 << 24) - 1


class LcTx(IntEnum):
    r'''The same encoding as lc_tx_t in the RTL'''
    ON = 0b0101
    OFF = 0b1010
    INVALID = 0


def read_lc_tx_t(value: int) -> LcTx:
    assert 0 <= value <= 15
    if value == LcTx.ON:
        return LcTx.ON
    elif value == LcTx.OFF:
        return LcTx.OFF
    else:
        return LcTx.INVALID
