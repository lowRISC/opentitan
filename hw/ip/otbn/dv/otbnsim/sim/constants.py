# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from enum import IntEnum, unique


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
    MAI_ERROR = 1 << 8
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


@unique
class CsrAddrs(IntEnum):
    '''All CSR addresses. Keep in sync with csr.yml'''
    FG0 = 0x7c0
    FG1 = 0x7c1
    FLAGS = 0x7c8
    MOD0 = 0x7d0
    MOD1 = 0x7d1
    MOD2 = 0x7d2
    MOD3 = 0x7d3
    MOD4 = 0x7d4
    MOD5 = 0x7d5
    MOD6 = 0x7d6
    MOD7 = 0x7d7
    RND_PREFETCH = 0x7d8
    KMAC_IF_STATUS = 0x7d9
    KMAC_INTR = 0x7da
    KMAC_CFG = 0x7db
    KMAC_MSG_SEND = 0x7dc
    KMAC_CMD = 0x7dd
    KMAC_BYTE_STROBE = 0x7de
    MAI_CTRL = 0x7e0
    RND = 0xfc0
    URND = 0xfc1
    KMAC_STATUS = 0xfc2
    KMAC_ERROR = 0xfc3
    MAI_STATUS = 0xfca


@unique
class WsrAddrs(IntEnum):
    '''All WSR addresses. Keep in sync with wsr.yml'''
    MOD = 0
    RND = 1
    URND = 2
    ACC = 3
    KEY_S0_L = 4
    KEY_S0_H = 5
    KEY_S1_L = 6
    KEY_S1_H = 7
    KMAC_DATA_S0 = 8
    KMAC_DATA_S1 = 9
    MAI_RES_S0 = 10
    MAI_RES_S1 = 11
    MAI_IN0_S0 = 12
    MAI_IN0_S1 = 13
    MAI_IN1_S0 = 14
    MAI_IN1_S1 = 15
