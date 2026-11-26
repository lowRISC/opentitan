# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# A model of the keymgr interface.
#
# Depending if the simulator is run standalone or as co-sim, the details of the model should be set
# differently.
# - For standalone, the interface is fully functional and returns a fixed message.
# - For co-sim, the interface should only accepts the start command and set the flags but never
#   model a session. This is because the RTL testbench also has no actual keymgr connected.
# The operation mode can be controlled by a flag which can be set when the OTBN sim object is
# created.

from enum import IntEnum, unique

from .csr import CSRFile
from .wsr import WSRFile


# We do not model the secure wipe states.
@unique
class _State(IntEnum):
    Idle = 0
    Receiving = 1
    ResponsePending = 2
    SendingResponse = 3


# The bitpositions of the commands. Note using IntFlag is slow, so we use a raw int value for
# commands.
CMD_START = 0x1
CMD_SEND = 0x2
CMD_SEND_ERROR = 0x8


# The message the keymgr sends to OTBN. Beats are precomputed for performance. The last beat can be
# partial.
_KEYMGR_BEAT_SIZE_BITS = 64
_KEYMGR_MSG = [
    '0011223344556677', '8899AABBCCDDEEFF', '0011223344556677', '8899AABBCCDDEEFF',
    'DEADBEAFDEADBEEF', 'DEADBEEFDEADBEEF', 'DEADBEEFDEADBEEF', 'DEADBEEFDEADBEEF',
    'FADEFADE00'
]
_KEYMGR_BEATS = [(int.from_bytes(bytes.fromhex(msg), byteorder='little'),
                  (1 << len(bytes.fromhex(msg))) - 1)
                 for msg in _KEYMGR_MSG]

assert all(beat < (1 << _KEYMGR_BEAT_SIZE_BITS) for beat, _ in _KEYMGR_BEATS)

_KEYMGR_NUM_BEATS = len(_KEYMGR_BEATS)


class KeymgrRequest:
    '''Models a keymgr request such that the Keymgr model can consume the message data.'''

    def __init__(self) -> None:
        self._index = 0

    def complete(self) -> bool:
        '''Return whether the request has been fully consumed.'''
        return self._index >= _KEYMGR_NUM_BEATS

    def take_beat(self) -> tuple[int, int]:
        '''Return the next beat of the message and its byte strobe.'''

        if self.complete():
            raise RuntimeError('Keymgr request has no more beats to take.')

        msg_int, byte_strobe = _KEYMGR_BEATS[self._index]
        self._index += 1

        return msg_int, byte_strobe


class Keymgr:
    '''Model of the keymgr interface.'''

    # A flag to set the mode to operate. For co-sim, set it to False. Standalone can set it to True
    # to enable a dummy keymgr request.
    fully_functional: bool = False

    _state: _State = _State.Idle

    # The current keymgr request being 'served'. Is None if no session is active.
    _keymgr_request: KeymgrRequest = KeymgrRequest()

    # Whether a pending message is in the WSR.
    _pending_msg = False

    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.on_start(csrs, wsrs)

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self._csrs = csrs
        self._wsrs = wsrs
        # Cache the ISPR objects to avoid the repeated container lookups.
        self._ctrl = csrs.KEYMGR_CTRL
        self._status = csrs.KEYMGR_STATUS
        self._msg_s0_l = wsrs.KEYMGR_MSG_S0_L
        self._msg_s0_h = wsrs.KEYMGR_MSG_S0_H
        self._msg_s1_l = wsrs.KEYMGR_MSG_S1_L
        self._msg_s1_h = wsrs.KEYMGR_MSG_S1_H
        self._reset()

    def _reset(self) -> None:
        self._pending_msg = False
        self._state = _State.Idle
        self._keymgr_request = KeymgrRequest()
        pass

    def step(self) -> None:
        '''Advance the model by one cycle. Called before the instruction executes.'''

        # Extract the possible commands issued by the previous instruction.
        cmd = self._ctrl.take_cmd()

        # Detect any command from the previous instruction.
        cmd_start_issued = cmd & CMD_START
        cmd_send_issued = cmd & CMD_SEND
        cmd_send_error_issued = cmd & CMD_SEND_ERROR
        any_send_cmd_issued = cmd_send_issued or cmd_send_error_issued

        # Detect if SW read a response. Must be called every cycle to keep the flag up to date.
        msg_read = self._msg_s0_l.was_read()

        # Early exit if nothing is to do.
        if self._state == _State.Idle and cmd == 0:
            return

        if msg_read and self._status.msg_valid():
            self._pending_msg = False
            # Immediately clear the MSG_VALID flag for this instruction.
            self._status.set_msg_valid(False)

        next_state = self._state
        match self._state:
            case _State.Idle:
                if cmd_start_issued:
                    next_state = _State.Receiving
                    self._keymgr_request = KeymgrRequest()
                    self._status.stage_receiving(True)
            case _State.Receiving:
                # In co-sim mode, we don't model a keymgr session. Just expose the state bits as
                # receiving and hang here.
                if self.fully_functional:
                    if not self._pending_msg:
                        # Stage the next beat such that SW can read it in the NEXT cycle.
                        beat, strobe = self._keymgr_request.take_beat()
                        self._msg_s0_l.stage_msg(beat)
                        self._pending_msg = True
                        self._status.stage_msg_valid(True)
                        self._status.stage_strobe(strobe)
                    if (self._keymgr_request.complete()):
                        next_state = _State.ResponsePending
                        self._status.stage_receiving(False)
                        self._status.stage_msg_complete(True)
            case _State.ResponsePending:
                if any_send_cmd_issued:
                    next_state = _State.SendingResponse
                    self._status.stage_sending(True)
            case _State.SendingResponse:
                # The keymgr may delay to accept the response. For now, model an immediate
                # acceptance.
                self._pending_msg = False
                next_state = _State.Idle
                self._status.stage_sending(False)
                self._status.stage_msg_complete(False)
                self._status.stage_msg_valid(False)

        self._state = next_state
