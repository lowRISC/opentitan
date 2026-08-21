# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple
from .constants import WsrAddrs
from .ext_regs import OTBNExtRegs
from .ispr import ISPR, DumbISPR, ISPRChange
from .kmac_ispr import KmacDataWSR
from .mai_ispr import MaiInputWSR, MaiOutputWSR
from .trace import Trace
from .trivium import CipherType, SeedType, Trivium


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
    '''Models URND PRNG Structure. Includes the URND control interface logic as well as the
    urnd_ctrl_enabled bit from the CTRL register.
    '''

    _BIVIUM_OUTPUT_WIDTH = 389

    def __init__(self, name: str):
        super().__init__(name, 256)

        self.URND_CTRL_ENABLED_OFFSET = 0
        self.STOPPED_OFFSET = 1
        self.RESTORING_OFFSET = 2
        self.USED_WHILE_STOPPED_OFFSET = 3
        self.STATE_SIZE_OFFSET = 16
        self.STATE_SIZE_MASK = 0x3ff  # 10 bits
        self.PART_SEED_SIZE_OFFSET = 26
        self.PART_SEED_SIZE_MASK = 0x3f  # 6 bits

        self._trivium = Trivium(
            CipherType.BIVIUM,
            SeedType.STATE_PARTIAL,
            self._BIVIUM_OUTPUT_WIDTH,
        )

        self._next_value: int = 0
        self._value: int = 0

        # Running is not the opposite of stopped. It indicates that the first seeding is done.
        self.running = False
        self.requesting = False
        self.reseed_done = False

        # URND control state and flags.
        self.stopped = False
        self.restoring = False
        self._restore_words_written = 0
        self.used_while_stopped = False

        # This represents the URND enable bit from the CTRL. It must persist across secure wipes.
        # Ensure that the URND WSR is not recreated in these cases.
        self.urnd_ctrl_enabled = False

        # Commands / writes issued by an instruction. Handled when it commits.
        self._cmd_stop = False
        self._cmd_start = False
        self._cmd_restore = False
        self._pending_restore_word: Optional[int] = None

        # Tracks when URND is used in the current cycle. If used, the PRNG is advanced even if
        # stopped.
        self._urnd_consumed = False

    def read_u32(self) -> int:
        '''Read a 32-bit unsigned result'''
        return self.read_unsigned() & ((1 << 32) - 1)

    def write_unsigned(self, value: int) -> None:
        '''Writes to URND are ignored'''
        return

    def on_start(self) -> None:
        self.running = False
        self.reseed_done = False
        self.stopped = False
        self.restoring = False
        self._restore_words_written = 0
        self.used_while_stopped = False
        self._cmd_stop = False
        self._cmd_start = False
        self._cmd_restore = False
        self._pending_restore_word = None
        self._urnd_consumed = False

    def read_unsigned(self) -> int:
        # Return the lower self.width bits of the registered Bivium output.
        return self._value & ((1 << self.width) - 1)

    def set_seed(self, value: int) -> None:
        assert value >= 0 and value < 2**Trivium.PART_SEED_SIZE
        self.reseed_done = False
        self._trivium.seed(value)
        # Upon seeing the first seed value the PRNG can be used to
        # generate a keystream.
        self.running = True

    def pending_value(self) -> int:
        '''Return the Bivium output scheduled by step(), before it is updated at the end of the
        cycle.'''
        # This is used for the MAI counter init during secure wipe. There the count must be loaded
        # with the next URND value. And in the sim this comes after URND commits. So we peek at the
        # next value here.
        return self._next_value

    def write_urnd_ctrl(self, value: int) -> None:
        '''A write to the URND_CTRL CSR.
        This registers any issued commands so that if the instruction commits these can be handled
        in the next cycle.'''
        if not self.urnd_ctrl_enabled:
            return
        self._cmd_stop = bool(value & 0x1)
        self._cmd_start = bool(value & 0x2)
        self._cmd_restore = bool(value & 0x4)

    def read_urnd_status(self) -> int:
        '''Return the current URND_STATUS CSR value.'''
        val = ((self.urnd_ctrl_enabled << self.URND_CTRL_ENABLED_OFFSET) |
               (self.stopped << self.STOPPED_OFFSET) |
               (self.restoring << self.RESTORING_OFFSET) |
               (self.used_while_stopped << self.USED_WHILE_STOPPED_OFFSET) |
               ((Trivium.BIVIUM_STATE_SIZE & self.STATE_SIZE_MASK) << self.STATE_SIZE_OFFSET) |
               ((Trivium.PART_SEED_SIZE & self.PART_SEED_SIZE_MASK) << self.PART_SEED_SIZE_OFFSET))
        return val

    def get_state(self) -> int:
        '''Return the the current PRNG state if URND control is enabled. Otherwise return zero.'''
        if not self.urnd_ctrl_enabled:
            return 0
        return self._trivium.get_state()

    def provide_restore_word(self, value: int) -> None:
        '''Provide one restore word during a restore process. Must be reverted if the instruction
        aborts.'''
        if not self.urnd_ctrl_enabled or not self.restoring:
            # A write to URND_STATE when not restoring is ignored.
            return
        self._pending_restore_word = value & ((1 << Trivium.PART_SEED_SIZE) - 1)

    def mark_consumed(self) -> None:
        # Force the PRNG to advance this cycle even when stopped.
        self._urnd_consumed = True

    def step(self, predec_read: bool = False) -> None:
        # We must advance the stopped PRNG if the current instruction uses URND. This advance is
        # actually issued when the instruction is predecoded (URND is flopped). We model this by
        # executing an additional state advance here.
        if predec_read and self.stopped:
            self._trivium.update()
            self._trivium.step()
            self.used_while_stopped = True
        # Schedule a state update and compute the keystream for the current state.
        # The state update is always speculatively. The URND commit()/abort() decide whether the
        # state update actually takes effect.
        self._trivium.update()
        # The URND value is the registered output of the PRNG, so we latch it here.
        self._next_value = self._trivium.keystream()

    def _advance(self, commit: bool) -> None:
        '''Model the advances of the PRNG and URND control logic when an instruction ends by either
        committing or aborting.'''
        # If the instruction commits, accept any restore words. Must be done before the PRNG
        # advances.
        if commit and self._pending_restore_word is not None:
            self._trivium.seed(self._pending_restore_word)
            self._pending_restore_word = None
            self._restore_words_written += 1
        else:
            # If the instruction aborts, discard any restore words.
            self._pending_restore_word = None

        # The PRNG advances unless software stopped it. However, it still advances if URND is used.
        # Even an aborted instruction consumes URND if it reads from it.
        forced = self._urnd_consumed
        self._urnd_consumed = False

        # The start and stop commands have immediate effect on the PRNG advance. Factor these in
        # but don't update the state yet. The current state (stopped) is still required.
        advance = not self.stopped
        if commit:
            if self._cmd_start:
                advance = True
            elif self._cmd_stop:
                advance = False

        advance = advance or forced

        # The URND is the registered output of the PRNG. The keystream is computed in step() based
        # on the current state. Independently of whether the PRNG state is advanced, we must update
        # the register.
        self._value = self._next_value

        if not advance:
            # If the PRNG is stopped, we discard the scheduled PRNG state update. This keeps the
            # PRNG state unchanged and the next step() computes the same keystream again.
            self._trivium.discard_update()

        # Perform the finally scheduled updates of Trivium.
        self._trivium.step()

        if self.stopped and forced:
            self.used_while_stopped = True

        # Stop requesting EDN seeds once all the seed rounds have been completed.
        if self._trivium.seed_done() and self.running:
            self.requesting = False

        if self.restoring:
            # A restore completes once all state words have been provided.
            if self._restore_words_written >= self._trivium.seed_rounds:
                self.restoring = False
        elif self._cmd_restore and commit:
            # Handle restore command. A restore command is ignored if we are restoring.
            self.restoring = True
            self._restore_words_written = 0

        # Handle start/stop commands once the current state is no longer required.
        if commit:
            # START takes priority over STOP.
            if self._cmd_start:
                self.stopped = False
            elif self._cmd_stop:
                self.stopped = True
                # STOP clears the sticky flag unless the state was forced to advance in this cycle.
                if not forced:
                    self.used_while_stopped = False

        # Prepare the flags to track the next instruction.
        self._cmd_stop = False
        self._cmd_start = False
        self._cmd_restore = False

    def commit(self) -> None:
        '''Commits the state of the URND WSR.
        Note this is called twice per cycle during execution. In commit() of state.py the URND
        commit is extracted for some "idle-ish" cycles. And then whilst executing all WSRs are
        committed again. Make sure this doesn't break the model.
        '''
        self._advance(commit=True)

    def abort(self) -> None:
        self._advance(commit=False)

    def changes(self) -> List[ISPRChange]:
        # Our URND model doesn't track (or report) changes to its internal
        # state.
        raise NotImplementedError


class UrndStateWSR(DumbISPR):
    '''The URND_STATE WSR.

    This gives access to the PRNG state and accepts restore values. The PRNG is modelled in the
    URND WSR.
    '''
    def __init__(self, name: str, urnd: URNDWSR):
        super().__init__(name, 256)
        self._urnd = urnd
        self.on_start()

    def read_unsigned(self) -> int:
        # The URND control enable check is implemented in the URND WSR.
        return self._urnd.get_state()

    def write_unsigned(self, value: int) -> None:
        # SW can write a full WLEN value but the HW only considers the lowest partial seed width
        # bits. We trace only the actual register value.
        super().write_unsigned(value & ((1 << Trivium.PART_SEED_SIZE) - 1))
        # An aborted write to URND_STATE should not provide any restore words. This is handled by
        # calling abort() on URND when an instruction is aborted.
        self._urnd.provide_restore_word(value)


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
        self.KMAC_DATA_S0 = KmacDataWSR('KMAC_DATA_S0')
        self.KMAC_DATA_S1 = KmacDataWSR('KMAC_DATA_S1')
        self.MAI_RES_S0 = MaiOutputWSR('MAI_RES_S0')
        self.MAI_RES_S1 = MaiOutputWSR('MAI_RES_S1')
        self.MAI_IN0_S0 = MaiInputWSR('MAI_IN0_S0')
        self.MAI_IN0_S1 = MaiInputWSR('MAI_IN0_S1')
        self.MAI_IN1_S0 = MaiInputWSR('MAI_IN1_S0')
        self.MAI_IN1_S1 = MaiInputWSR('MAI_IN1_S1')
        self.URND_STATE = UrndStateWSR('URND_STATE', self.URND)

        self._by_addr = {
            WsrAddrs.MOD: self.MOD,
            WsrAddrs.RND: self.RND,
            WsrAddrs.URND: self.URND,
            WsrAddrs.ACC: self.ACC,
            WsrAddrs.KEY_S0_L: self.KeyS0L,
            WsrAddrs.KEY_S0_H: self.KeyS0H,
            WsrAddrs.KEY_S1_L: self.KeyS1L,
            WsrAddrs.KEY_S1_H: self.KeyS1H,
            WsrAddrs.KMAC_DATA_S0: self.KMAC_DATA_S0,
            WsrAddrs.KMAC_DATA_S1: self.KMAC_DATA_S1,
            WsrAddrs.MAI_RES_S0: self.MAI_RES_S0,
            WsrAddrs.MAI_RES_S1: self.MAI_RES_S1,
            WsrAddrs.MAI_IN0_S0: self.MAI_IN0_S0,
            WsrAddrs.MAI_IN0_S1: self.MAI_IN0_S1,
            WsrAddrs.MAI_IN1_S0: self.MAI_IN1_S0,
            WsrAddrs.MAI_IN1_S1: self.MAI_IN1_S1,
            WsrAddrs.URND_STATE: self.URND_STATE,
        }

    def on_start(self) -> None:
        '''Called at the start of an operation

        This clears values that don't persist between runs (everything except
        RND and the key registers)
        '''
        for reg in self._by_addr.values():
            reg.on_start()

    def check_idx(self, idx: int) -> bool:
        '''Return True if idx is a valid WSR index'''
        # TODO: Clean this up once we have python 3.12+
        return idx in WsrAddrs._value2member_map_

    def has_value_at_idx(self, idx: int) -> int:
        '''Return True if the WSR at idx has a valid value.

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        return self._by_addr[WsrAddrs(idx)].has_value()

    def read_at_idx(self, idx: int) -> int:
        '''Read the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        wsr_addr = WsrAddrs(idx)
        # KMAC_DATA_S0/1 track read/write events themselves; the generic path
        # below dispatches to them like any other WSR.
        return self._by_addr[wsr_addr].read_unsigned()

    def write_at_idx(self, idx: int, value: int) -> None:
        '''Write the WSR at idx as an unsigned 256-bit value

        Assumes that idx is a valid index (call check_idx to ensure this).

        '''
        wsr_addr = WsrAddrs(idx)
        self._by_addr[wsr_addr].write_unsigned(value)

    def commit(self) -> None:
        self.MOD.commit()
        self.RND.commit()
        self.URND.commit()
        self.ACC.commit()
        self.KeyS0.commit()
        self.KeyS1.commit()
        self.KMAC_DATA_S0.commit()
        self.KMAC_DATA_S1.commit()
        self.MAI_RES_S0.commit()
        self.MAI_RES_S1.commit()
        self.MAI_IN0_S0.commit()
        self.MAI_IN0_S1.commit()
        self.MAI_IN1_S0.commit()
        self.MAI_IN1_S1.commit()
        self.URND_STATE.commit()

    def abort(self) -> None:
        self.MOD.abort()
        self.RND.abort()
        self.URND.abort()
        self.ACC.abort()
        self.KMAC_DATA_S0.abort()
        self.KMAC_DATA_S1.abort()
        # We commit changes to the sideloaded keys from outside, even if the
        # instruction itself gets aborted.
        self.KeyS0.commit()
        self.KeyS1.commit()
        # We commit changes to the MAI output registers from outside, even if
        # the instruction itself gets aborted (there is never a write to these
        # WSRs from an instruction).
        self.MAI_RES_S0.commit()
        self.MAI_RES_S1.commit()
        self.MAI_IN0_S0.abort()
        self.MAI_IN0_S1.abort()
        self.MAI_IN1_S0.abort()
        self.MAI_IN1_S1.abort()
        self.URND_STATE.abort()

    def changes(self) -> List[Trace]:
        ret: List[Trace] = []
        ret += self.MOD.changes()
        ret += self.RND.changes()
        ret += self.ACC.changes()
        ret += self.KeyS0.changes()
        ret += self.KeyS1.changes()
        ret += self.KMAC_DATA_S0.changes()
        ret += self.KMAC_DATA_S1.changes()
        ret += self.MAI_RES_S0.changes()
        ret += self.MAI_RES_S1.changes()
        ret += self.MAI_IN0_S0.changes()
        ret += self.MAI_IN0_S1.changes()
        ret += self.MAI_IN1_S0.changes()
        ret += self.MAI_IN1_S1.changes()
        ret += self.URND_STATE.changes()
        return ret

    def set_sideload_keys(self,
                          key0: Optional[int],
                          key1: Optional[int]) -> None:
        self.KeyS0.set_unsigned(key0)
        self.KeyS1.set_unsigned(key1)

    def wipe(self) -> None:
        self.MOD.write_invalid()
        self.ACC.write_invalid()
        self.KMAC_DATA_S0.write_invalid()
        self.KMAC_DATA_S1.write_invalid()
        self.MAI_RES_S0.write_invalid()
        self.MAI_RES_S1.write_invalid()
        self.MAI_IN0_S0.write_invalid()
        self.MAI_IN0_S1.write_invalid()
        self.MAI_IN1_S0.write_invalid()
        self.MAI_IN1_S1.write_invalid()
