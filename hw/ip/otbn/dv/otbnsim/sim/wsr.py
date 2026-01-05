# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple
from .ext_regs import OTBNExtRegs
from .ispr import ISPR, DumbISPR, ISPRChange
from .kmac_ispr import KmacDataWSRs
from .trace import Trace


class RandWSR(ISPR):
    '''The magic RND WSR

    RND is special as OTBN can stall on reads to it. A read from RND either
    immediately returns data from a cache of a previous EDN request (triggered
    by writing to the RND_PREFETCH CSR) or waits for data from the EDN. To
    model this, anything reading from RND must first call `request_value` which
    returns True if the value is available.

    '''
    def __init__(self, name: str, ext_regs: OTBNExtRegs):
        super().__init__(name, 256)

        self._random_value: Optional[int] = None
        self._next_random_value: Optional[int] = None
        self._ext_regs = ext_regs

        # The pending_request flag says that we've started an instruction that
        # reads from RND. Using it means that we can avoid repeated requests
        # from the EdnClient which is important because it avoids a request on
        # the single cycle where the EdnClient has passed data back to us but
        # that data hasn't yet been committed. If we sent another request on
        # that cycle, the EdnClient would start another transaction.
        self._pending_request = False
        self._next_pending_request = False

        self._fips_err = False
        self.fips_err_escalate = False

        self._rep_err = False
        self.rep_err_escalate = False

    def read_unsigned(self) -> int:
        assert self._random_value is not None
        self._next_random_value = None
        self.rep_err_escalate = self._rep_err
        self.fips_err_escalate = self._fips_err
        return self._random_value

    def read_u32(self) -> int:
        '''Read a 32-bit unsigned result'''
        self.rep_err_escalate = self._rep_err
        self.fips_err_escalate = self._fips_err
        return self.read_unsigned() & ((1 << 32) - 1)

    def write_unsigned(self, value: int) -> None:
        '''Writes to RND are ignored

        Note this is different to `set_unsigned`. This is used by executing
        instruction, see `set_unsigned` docstring for more details
        '''
        return

    def on_start(self) -> None:
        self._next_random_value = None
        self._next_pending_request = False
        self.fips_err_escalate = False
        self.rep_err_escalate = False

    def commit(self) -> None:
        self._random_value = self._next_random_value
        self._pending_request = self._next_pending_request

    def request_value(self) -> bool:
        '''Signals intent to read RND, returns True if a value is available'''
        if self._random_value is not None:
            return True
        if not self._pending_request:
            self._next_pending_request = True
            self._ext_regs.rnd_request()
        return False

    def set_unsigned(self, value: int, fips_err: bool, rep_err: bool) -> None:
        '''Sets a random value that can be read by a future `read_unsigned`

        This is different to `write_unsigned`, that is used by an executing
        instruction to write to RND. This is used by the simulation environment
        to provide a value that is later read by `read_unsigned` and doesn't
        relate to instruction execution (e.g. in an RTL simulation it monitors
        the EDN bus and supplies the simulator with an RND value when a fresh
        one is seen on the EDN bus).
        '''
        assert 0 <= value < (1 << 256)
        self._fips_err = fips_err
        self._rep_err = rep_err
        self.fips_err_escalate = False
        self.rep_err_escalate = False
        self._next_random_value = value
        self._next_pending_request = False


class URNDWSR(ISPR):
    '''Models URND PRNG Structure'''
    def __init__(self, name: str):
        super().__init__(name, 256)
        seed = [0x84ddfadaf7e1134d, 0x70aa1c59de6197ff,
                0x25a4fe335d095f1e, 0x2cba89acbe4a07e9]
        self._state = [seed, 4 * [0], 4 * [0], 4 * [0], 4 * [0]]
        self._next_value = 0
        self._value = 0
        self.running = False

    def rol(self, n: int, d: int) -> int:
        '''Rotate n left by d bits'''
        return ((n << d) & ((1 << 64) - 1)) | (n >> (64 - d))

    def read_u32(self) -> int:
        '''Read a 32-bit unsigned result'''
        return self.read_unsigned() & ((1 << 32) - 1)

    def write_unsigned(self, value: int) -> None:
        '''Writes to URND are ignored'''
        return

    def on_start(self) -> None:
        self.running = False

    def read_unsigned(self) -> int:
        return self._value

    def state_update(self, data_in: List[int]) -> List[int]:
        a_in = data_in[3]
        b_in = data_in[2]
        c_in = data_in[1]
        d_in = data_in[0]

        a_out = a_in ^ b_in ^ d_in
        b_out = a_in ^ b_in ^ c_in
        c_out = a_in ^ ((b_in << 17) & ((1 << 64) - 1)) ^ c_in
        d_out = self.rol(d_in ^ b_in, 45)
        assert a_out < (1 << 64)
        assert b_out < (1 << 64)
        assert c_out < (1 << 64)
        assert d_out < (1 << 64)
        return [d_out, c_out, b_out, a_out]

    def set_seed(self, value: List[int]) -> None:
        assert len(value) == 4
        self.running = True
        self._state[0] = value
        # Step immediately to update the internal state with the new seed
        self.step()

    def step(self) -> None:
        if self.running:
            mask64 = (1 << 64) - 1
            mid = 4 * [0]
            nv = 0
            for i in range(4):
                st_i = self._state[i]
                self._state[(i + 1) & 3] = self.state_update(st_i)
                mid[i] = (st_i[3] + st_i[0]) & mask64
                nv |= ((self.rol(mid[i], 23) + st_i[3]) & mask64) << (64 * i)
            self._next_value = nv

    def commit(self) -> None:
        self._value = self._next_value

    def changes(self) -> List[ISPRChange]:
        # Our URND model doesn't track (or report) changes to its internal
        # state.
        raise NotImplementedError


class KeyTrace(Trace):
    def __init__(self, name: str, new_value: Optional[int]):
        self.name = name
        self.new_value = new_value

    def trace(self) -> str:
        val_desc = '(unset)' if self.new_value is None else self.new_value
        return '{} = {}'.format(self.name, val_desc)


class SideloadKey:
    '''Represents a sideloaded key, with 384 bits of data and a valid signal'''
    def __init__(self, name: str):
        self.name = name
        self._value: Optional[int] = None
        self._new_value: Optional[Tuple[bool, int]] = None

    def has_value(self) -> bool:
        return self._value is not None

    def read_unsigned(self, shift: int) -> int:
        # The simulator should be careful not to call read_unsigned() unless it
        # has first checked that the value exists.
        assert self._value is not None

        mask256 = (1 << 256) - 1
        return (self._value >> shift) & mask256

    def set_unsigned(self, value: Optional[int]) -> None:
        '''Unlike the WSR write_unsigned, this takes effect immediately

        That way, we can correctly model the combinatorial path from sideload
        keys to the WSR file in the RTL. Note that we do still report the
        change until the next commit.
        '''
        assert value is None or (0 <= value < (1 << 384))
        self._value = value
        self._new_value = (False, 0) if value is None else (True, value)

    def changes(self) -> List[KeyTrace]:
        if self._new_value is not None:
            vld, value = self._new_value
            return [KeyTrace(self.name, value if vld else None)]
        else:
            return []

    def commit(self) -> None:
        self._new_value = None


class KeyWSR(ISPR):
    def __init__(self, name: str, shift: int, key_reg: SideloadKey):
        assert 0 <= shift < 384
        super().__init__(name, 256)
        self._shift = shift
        self._key_reg = key_reg

    def has_value(self) -> bool:
        return self._key_reg.has_value()

    def read_unsigned(self) -> int:
        return self._key_reg.read_unsigned(self._shift)

    def write_unsigned(self, value: int) -> None:
        return


class WSRFile:
    '''A model of the WSR file'''
    def __init__(self, ext_regs: OTBNExtRegs) -> None:
        self.KeyS0 = SideloadKey('KeyS0')
        self.KeyS1 = SideloadKey('KeyS1')

        self.MOD = DumbISPR('MOD', 256)
        self.RND = RandWSR('RND', ext_regs)
        self.URND = URNDWSR('URND')
        self.ACC = DumbISPR('ACC', 256)
        self.KeyS0L = KeyWSR('KeyS0L', 0, self.KeyS0)
        self.KeyS0H = KeyWSR('KeyS0H', 256, self.KeyS0)
        self.KeyS1L = KeyWSR('KeyS1L', 0, self.KeyS1)
        self.KeyS1H = KeyWSR('KeyS1H', 256, self.KeyS1)
        self.KMAC_DATA = KmacDataWSRs(['KMAC_DATA_S0', 'KMAC_DATA_S1'])

        self._by_idx = {
            0: self.MOD,
            1: self.RND,
            2: self.URND,
            3: self.ACC,
            4: self.KeyS0L,
            5: self.KeyS0H,
            6: self.KeyS1L,
            7: self.KeyS1H,
            8: self.KMAC_DATA.shares[0],
            9: self.KMAC_DATA.shares[1],
        }

    def on_start(self) -> None:
        '''Called at the start of an operation

        This clears values that don't persist between runs (everything except
        RND and the key registers)
        '''
        for reg in self._by_idx.values():
            reg.on_start()

    def check_idx(self, idx: int) -> bool:
        '''Return True if idx is a valid WSR index'''
        return idx in self._by_idx

    def has_value_at_idx(self, idx: int) -> int:
        '''Return True if the WSR at idx has a valid valu.

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        return self._by_idx[idx].has_value()

    def read_at_idx(self, idx: int) -> int:
        '''Read the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        # KMAC_DATA_S0/1 should only be accessed through the wrapper class.
        if idx == 0x8:
            return self.KMAC_DATA.read_unsigned(share_idx=0)

        elif idx == 0x9:
            return self.KMAC_DATA.read_unsigned(share_idx=1)

        return self._by_idx[idx].read_unsigned()

    def write_at_idx(self, idx: int, value: int) -> None:
        '''Write the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        if idx == 0x8:
            self.KMAC_DATA.write_unsigned(share_idx=0, value=value)
            return

        elif idx == 0x9:
            self.KMAC_DATA.write_unsigned(share_idx=1, value=value)
            return

        self._by_idx[idx].write_unsigned(value)

    def commit(self) -> None:
        self.MOD.commit()
        self.RND.commit()
        self.URND.commit()
        self.ACC.commit()
        self.KeyS0.commit()
        self.KeyS1.commit()
        self.KMAC_DATA.commit()

    def abort(self) -> None:
        self.MOD.abort()
        self.RND.abort()
        self.URND.abort()
        self.ACC.abort()
        self.KMAC_DATA.abort()
        # We commit changes to the sideloaded keys from outside, even if the
        # instruction itself gets aborted.
        self.KeyS0.commit()
        self.KeyS1.commit()

    def changes(self) -> List[Trace]:
        ret: List[Trace] = []
        ret += self.MOD.changes()
        ret += self.RND.changes()
        ret += self.ACC.changes()
        ret += self.KeyS0.changes()
        ret += self.KeyS1.changes()
        ret += self.KMAC_DATA.changes()
        return ret

    def set_sideload_keys(self,
                          key0: Optional[int],
                          key1: Optional[int]) -> None:
        self.KeyS0.set_unsigned(key0)
        self.KeyS1.set_unsigned(key1)

    def wipe(self) -> None:
        self.MOD.write_invalid()
        self.ACC.write_invalid()
