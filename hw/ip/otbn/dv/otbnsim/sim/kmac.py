# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

'''Model of the OTBN-KMAC interface for the standalone ISS.

This models what OTBN software can observe through the CSR/WSR interface. The timing is modelled
coarsely. The message is shifted out one 64-bit beat per cycle (up to 4 per 256-bit WSR), and the
external KMAC's processing latency is fixed to PERM_CYCLES.

The model requires two calls per cycle. The step() method is called at the start of every cycle
(before the instruction executes) and detect_errors() is called at the end of every cycle (after
the instruction commits or aborts).
'''

from enum import IntEnum, IntFlag, unique
from typing import Any, Optional
from Crypto.Hash import (SHA3_224, SHA3_256, SHA3_384, SHA3_512,
                         SHAKE128, SHAKE256, cSHAKE128, cSHAKE256,
                         KMAC128, KMAC256)
from .csr import CSRFile
from .wsr import WSRFile

# Coarse masked Keccak-f[1600] permutation latency: one masked round takes KECCAK_ROUND_CYCLES.
KECCAK_ROUNDS = 24
KECCAK_ROUND_CYCLES = 4
PERM_CYCLES = KECCAK_ROUNDS * KECCAK_ROUND_CYCLES

# Number of 64-bit message beats in a 256-bit KMAC_DATA WSR.
MSG_PARTS = 4

# Coarse latency from a PROCESS request to the error response of a rejected
# configuration: no permutation runs, but the request still has to be accepted
# and the error returned, so the response cannot appear in the same cycle.
REJECT_CYCLES = 2

# The KMAC HWIP uses a fixed key and output length (in bits).
KMAC_KEY_LENGTH = 384

# The KMAC HWIP outputs the digest in masked form. The standalone sim uses a fixed value to
# make the output masking deterministic.
KMAC_DIGEST_MASK = 0xdeadbeefdeadbeef

# One KMAC_STRB bit per message byte, so 8 strobe bits cover a 64-bit beat.
STRB_BITS_PER_BEAT = 8
# Strobe value of a fully populated beat (all 8 bytes valid).
STRB_BEAT_FULL = (1 << STRB_BITS_PER_BEAT) - 1


@unique
class _State(IntEnum):
    IDLE = 0
    STARTING = 1
    WAIT_FOR_MSG = 2
    SENDING = 3
    PROCESSING = 4
    RECEIVING = 5
    TERMINATING = 6
    WAIT_FOR_CLOSE = 7


@unique
class _Cmd(IntFlag):
    START = 0x1
    SEND = 0x2
    PROCESS = 0x4
    DONE = 0x8
    CLOSE = 0x10


@unique
class _Mode(IntEnum):
    SHA3 = 0
    SHAKE = 1
    CSHAKE = 2
    KMAC = 3


@unique
class _Strength(IntEnum):
    L128 = 0
    L224 = 1
    L256 = 2
    L384 = 3
    L512 = 4


# Keccak capacity in bits indexed by strength (capacity = 2 * security level).
_CAP_BITS = {
    _Strength.L128: 256,
    _Strength.L224: 448,
    _Strength.L256: 512,
    _Strength.L384: 768,
    _Strength.L512: 1024,
}


MODE_STRENGTH_TABLE = {
    (_Mode.SHA3, _Strength.L224): SHA3_224,
    (_Mode.SHA3, _Strength.L256): SHA3_256,
    (_Mode.SHA3, _Strength.L384): SHA3_384,
    (_Mode.SHA3, _Strength.L512): SHA3_512,
    (_Mode.SHAKE, _Strength.L128): SHAKE128,
    (_Mode.SHAKE, _Strength.L256): SHAKE256,
    (_Mode.CSHAKE, _Strength.L128): cSHAKE128,
    (_Mode.CSHAKE, _Strength.L256): cSHAKE256,
    (_Mode.KMAC, _Strength.L128): KMAC128,
    (_Mode.KMAC, _Strength.L256): KMAC256,
}


class Kmac:
    '''Model of the OTBN-KMAC interface.'''

    _state: _State
    _no_more_msg_allowed: bool
    _msg_beat_idx: int
    _ready: bool
    _rsp_valid: bool
    _s0_pending: bool
    _s1_pending: bool
    _app_mode: _Mode
    _app_strength: _Strength
    _app_en_xof: bool
    _service_rejected: bool
    _app_msg: bytearray
    # A cycle timer to model either the Keccak permutation delay or any request/response latency.
    _latency_timer: int
    # Number of full 64-bit message words absorbed into the current rate block. Every time it
    # reaches the rate the KMAC runs a permutation and back-pressures any message requests.
    _msg_block_words: int
    _beats_pushed: int
    _beat_in_rate: int
    # Either a pycryptodome XOF hash object (SHAKE/cSHAKE) or None for fixed-length digests.
    _xof: Optional[Any]
    _fixed_digest: bytes

    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.on_start(csrs, wsrs)

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self._csrs = csrs
        self._wsrs = wsrs
        self._reset()

    def step(self) -> None:
        '''Advance the model by one cycle. Called before the instruction executes.'''

        # Extract the possible commands issued by the previous instruction.
        cmd = self._csrs.KMAC_CTRL.take_cmd()
        cmd_start_issued = bool(cmd & _Cmd.START)
        cmd_send_issued = bool(cmd & _Cmd.SEND)
        cmd_process_issued = bool(cmd & _Cmd.PROCESS)
        cmd_done_issued = bool(cmd & _Cmd.DONE)
        cmd_close_issued = bool(cmd & _Cmd.CLOSE)

        # Check if a KMAC_DATA WSRs is read in the last cycle. Update pending flags accordingly.
        if self._wsrs.KMAC_DATA_S0.was_read():
            self._s0_pending = False
        if self._wsrs.KMAC_DATA_S1.was_read():
            self._s1_pending = False

        # Reset the read flags such that the current instruction is tracked.
        self._wsrs.KMAC_DATA_S0.clr_read()
        self._wsrs.KMAC_DATA_S1.clr_read()

        # Extract state information from the current latency timer so that we can directly
        # manipulate the timer instead of having a "next" value.
        kmac_busy = self._latency_timer != 0
        kmac_idle = not kmac_busy

        # Advance the timer if absorbing/squeezing or modelling a request/response timing.
        if kmac_busy:
            self._latency_timer -= 1

        match self._state:
            case _State.IDLE:
                if cmd_start_issued:
                    self._state = _State.STARTING

            case _State.STARTING:
                # Decode configuration and emulate sending the request. The standalone sim does
                # not model backpressure on the request channel, so immediately wait for messages.
                self._service_rejected = not self._decode_config()
                self._latency_timer = 0
                self._state = _State.WAIT_FOR_MSG

                # Prepare the message buffer and the send control logic.
                self._app_msg = bytearray()
                self._msg_block_words = 0
                self._no_more_msg_allowed = False

            case _State.WAIT_FOR_MSG:
                if cmd_send_issued and not self._no_more_msg_allowed:
                    # Start sending a message only if the last message has not yet been sent.
                    self._state = _State.SENDING
                    self._msg_beat_idx = 0
                elif cmd_process_issued:
                    if not self._service_rejected:
                        # Start the processing. There is no backpressure modelled for the request
                        # channel.
                        self._start_digest()
                        # The process round runs after any absorb permutation is still in flight.
                        self._latency_timer += PERM_CYCLES
                    else:
                        # A rejected config results in no hashing operation and returns an error
                        # response. The delay models the latency of the response channel.
                        self._latency_timer = REJECT_CYCLES
                    self._state = _State.PROCESSING

            case _State.SENDING:
                # The message is sent in 64-bit beats, i.e., a full WSR takes 4 cycles. Any message
                # always starts at a rate block boundary because the cSHAKE/KMAC prefix and key are
                # bytepad-ed to the rate. So a single per-session word counter is sufficient. While
                # the permutation runs the interface is back-pressured, so we stall.
                if kmac_idle:
                    (end_phase, no_more_msg_allowed,
                     absorbed_full_word) = self._send_beat(self._msg_beat_idx)

                    if no_more_msg_allowed:
                        self._no_more_msg_allowed = True

                    if absorbed_full_word:
                        # A full word was absorbed into the current rate block. Once the block is
                        # full the KMAC runs a permutation before it can accept the next beat.
                        self._msg_block_words += 1
                        if self._msg_block_words >= self._rate_beats():
                            self._msg_block_words = 0
                            self._latency_timer = PERM_CYCLES

                    if end_phase:
                        # The full message is sent, wait for next message or a process command.
                        self._state = _State.WAIT_FOR_MSG
                    else:
                        # Another part of the message is sent, keep sending the next parts.
                        self._msg_beat_idx += 1

            case _State.PROCESSING:
                # The process request is being sent and the interface is not ready, so a write to
                # KMAC_DATA / KMAC_STRB / KMAC_CFG here raises MSG_WRITE_ERROR. The in-flight Keccak
                # round keeps running via the background timer.
                self._state = _State.RECEIVING

            case _State.RECEIVING:
                if cmd_done_issued:
                    # Terminate and clear RSP_VALID independently of whether the current digest is
                    # read. Discard pending response tracking as well so a leftover beat cannot keep
                    # RSP_VALID asserted into the next session.
                    self._state = _State.TERMINATING
                    self._rsp_valid = False
                    self._s0_pending = False
                    self._s1_pending = False

                    # The interface captures the error flags also in the cycle where the DONE
                    # command is issued. The error flags are still relevant and will be checked
                    # when checking the finish response. The valid flag is however cleared until
                    # the finish response arrives.
                    if self._service_rejected:
                        self._csrs.KMAC_STATUS.hw_set_rsp_error()
                elif kmac_busy:
                    # Wait until the KMAC computed the digest.
                    pass
                elif self._service_rejected:
                    # Expose the error response.
                    self._csrs.KMAC_STATUS.hw_set_rsp_error()
                    self._rsp_valid = True
                elif not self._s0_pending and not self._s1_pending:
                    # The previous response was consumed, so the interface immediately accepts the
                    # next one. While a response is still pending we just keep RSP_VALID high.
                    if self._rsp_valid and self._digest_exhausted() and self._app_en_xof:
                        # The previous digest part is consumed but the current squeeze is exhausted.
                        # With EN_XOF=1 the KMAC HWIP permutes the state once more and exposes
                        # another squeeze. EN_XOF is only ever set for SHAKE and cSHAKE.
                        assert self._app_mode in (_Mode.SHAKE, _Mode.CSHAKE)
                        self._beat_in_rate = 0
                        self._latency_timer = PERM_CYCLES
                        self._rsp_valid = False
                    elif not self._digest_exhausted():
                        # Stage the next beat in the same cycle the previous one is consumed.
                        self._emit_beat()
                        self._rsp_valid = True
                        self._s0_pending = True
                        self._s1_pending = True
                    else:
                        # Digest exhausted (non-XOF): drop RSP_VALID and wait for DONE.
                        self._rsp_valid = False

            case _State.TERMINATING:
                # The KMAC acknowledges the termination with a finish response. This response is
                # sent as soon as any ongoing permutation completes.
                if kmac_idle:
                    self._rsp_valid = True
                    self._state = _State.WAIT_FOR_CLOSE

            case _State.WAIT_FOR_CLOSE:
                # The finish response is exposed until SW has handled it and ends the session with
                # the CLOSE command. Error bits are cleared on CLOSE command.
                if cmd_close_issued:
                    self._rsp_valid = False
                    self._s0_pending = False
                    self._s1_pending = False
                    self._csrs.KMAC_STATUS.hw_clr_error_bits()
                    self._state = _State.IDLE

        # Drive the HW status bits based on the updated state because a CSR read after a command
        # sees the new value.
        self._ready = self._state in (_State.IDLE, _State.WAIT_FOR_MSG, _State.RECEIVING)
        self._csrs.KMAC_STATUS.hw_set_ready(self._ready)
        self._csrs.KMAC_STATUS.hw_set_rsp_valid(self._rsp_valid)

    def detect_errors(self) -> None:
        '''Detect errors caused by the current instruction.

        This does not commit any internal KMAC state but updates the error flags. It detects the
        two SW-visible KMAC_STATUS errors that depend on the current instruction.
        It consumes the staged command and the DATA/STRB/CFG write flags and stages the KMAC_STATUS
        error bits. It must run before the register commit/abort that clears those flags and
        commits KMAC_STATUS. It must be called on commit and abort because the error bits are
        sticky and commit even if the instruction aborts.'''

        # CTRL_ERROR:
        # - A command issued out of order for the current state
        # - A written command value has more than one bit set.
        cmd = self._csrs.KMAC_CTRL.peek_pending_cmd()
        multiple_cmds = (cmd & (cmd - 1)) != 0
        unexpected_cmd = self._unexpected_cmd(self._state, cmd)

        if multiple_cmds or unexpected_cmd:
            # Here we can use _set which immediately sets the bit because this is after the current
            # instruction read the status flags.
            self._csrs.KMAC_STATUS.hw_set_ctrl_error()

        # MSG_WRITE_ERROR has two sources:
        # - SW writes to KMAC_DATA, KMAC_STRB or KMAC_CFG while not ready.
        # - SW writes to KMAC_DATA when the HW is receiving a response.
        data_written = (self._wsrs.KMAC_DATA_S0.is_written() or
                        self._wsrs.KMAC_DATA_S1.is_written())
        strb_written = self._csrs.KMAC_STRB.is_written()
        cfg_written = self._csrs.KMAC_CFG.is_written()
        hw_written = (self._wsrs.KMAC_DATA_S0.is_hw_written() or
                      self._wsrs.KMAC_DATA_S1.is_hw_written())

        not_ready_write = (data_written or strb_written or cfg_written) and not self._ready
        collision = data_written and hw_written
        if not_ready_write or collision:
            # Here we can use _set which immediately sets the bit because this is after the current
            # instruction read the status flags.
            self._csrs.KMAC_STATUS.hw_set_msg_write_error()

    def _reset(self) -> None:
        self._state = _State.IDLE
        self._no_more_msg_allowed = False
        self._msg_beat_idx = 0
        self._ready = False
        self._rsp_valid = False
        self._s0_pending = False
        self._s1_pending = False

        self._app_mode = _Mode.SHA3
        self._app_strength = _Strength.L256
        self._app_en_xof = False
        self._service_rejected = False
        self._app_msg = bytearray()
        self._latency_timer = 0
        self._msg_block_words = 0
        self._beats_pushed = 0
        self._beat_in_rate = 0
        self._xof = None
        self._fixed_digest = b''

    def _unexpected_cmd(self, st: _State, cmd: int) -> bool:
        '''Return True if any issued command is out of order for the state.'''
        # Commands accepted in each state. Any issued command outside this mask is out of order.
        allowed_cmds = {
            _State.IDLE: _Cmd.START,
            _State.STARTING: _Cmd(0),
            _State.WAIT_FOR_MSG: _Cmd.PROCESS |
                                 (_Cmd.SEND if not self._no_more_msg_allowed else _Cmd(0)),
            _State.SENDING: _Cmd(0),
            _State.PROCESSING: _Cmd(0),
            _State.RECEIVING: _Cmd.DONE,
            _State.TERMINATING: _Cmd(0),
            _State.WAIT_FOR_CLOSE: _Cmd.CLOSE,
        }

        return bool(cmd & ~allowed_cmds[st])

    def _send_beat(self, idx: int) -> tuple[bool, bool, bool]:
        '''Send one 64-bit message beat (index idx) from the WSRs.

        Returns (end_phase, no_more_send_allowed, absorbed_full_word) where:
          end_phase:
            The message phase ends after this beat because either an empty beat, a partial beat, or
            the 4th and last beat of the WSR was sent.
          no_more_send_allowed:
            True if no further SEND commands are allowed afterwards because an empty beat or a
            partial beat is detected.
          absorbed_full_word:
            True if a full 64-bit message word (strb == 0xff) was absorbed. Only full words fill the
            sponge rate. An empty beat absorbs nothing and a partial beat is the final beat (the pad
            and final permutation happen at PROCESS), so neither triggers a mid-absorption
            permutation.
        '''
        # Select this beat's slice of the WSR shares and its byte strobe.
        share0 = (self._wsrs.KMAC_DATA_S0.get_unsigned() >> (idx * 64)) & ((1 << 64) - 1)
        share1 = (self._wsrs.KMAC_DATA_S1.get_unsigned() >> (idx * 64)) & ((1 << 64) - 1)
        strb_word = self._csrs.KMAC_STRB.read_unsigned()
        strb = (strb_word >> (idx * STRB_BITS_PER_BEAT)) & STRB_BEAT_FULL

        if strb == 0:
            # An empty beat does not send anything and ends the message phase.
            return True, True, False

        # Unmask the beat and append only the valid (strobed) bytes for the hashing model.
        beat = share0 ^ share1
        valid_bytes = strb.bit_count()
        self._app_msg += beat.to_bytes(8, 'little')[:valid_bytes]

        if strb != STRB_BEAT_FULL:
            # Partial beat detected, this is the last beat of the message phase.
            return True, True, False
        # If the strobe is full, keep going unless this was the 4th (last) beat of the message.
        return idx == MSG_PARTS - 1, False, True

    # Parse the received session configuration and check it.
    def _decode_config(self) -> bool:
        # The upper fields must hold the bitwise inverted values of the lower fields.
        if not self._csrs.KMAC_CFG.redundancy_valid():
            return False

        mode_raw = self._csrs.KMAC_CFG.get_mode()
        try:
            mode = _Mode(mode_raw)
        except ValueError:
            return False

        strength_raw = self._csrs.KMAC_CFG.get_strength()
        try:
            strength = _Strength(strength_raw)
        except ValueError:
            return False

        self._app_en_xof = self._csrs.KMAC_CFG.get_en_xof()
        self._app_mode = mode
        self._app_strength = strength

        return self._config_valid()

    def _config_valid(self) -> bool:
        # XOF operation is not supported for SHA3 or KMAC.
        if self._app_en_xof and self._app_mode in (_Mode.SHA3, _Mode.KMAC):
            return False
        if self._app_mode == _Mode.SHA3:
            return self._app_strength in (_Strength.L224, _Strength.L256,
                                          _Strength.L384, _Strength.L512)
        # SHAKE / cSHAKE / KMAC support only L128 and L256.
        return self._app_strength in (_Strength.L128, _Strength.L256)

    def _rate_beats(self) -> int:
        '''Number of 64-bit beats squeezed per permutation (the rate).'''
        return (1600 - _CAP_BITS[self._app_strength]) // 64

    def _digest_exhausted(self) -> bool:
        '''True when no further beats are available without re-squeezing.'''
        if self._xof is None:
            # Fixed-length digest (SHA3, KMAC): exhausted once every beat has been pushed.
            return self._beats_pushed * 8 >= len(self._fixed_digest)
        # XOF (SHAKE, cSHAKE): rate depends on strength.
        return self._beat_in_rate >= self._rate_beats()

    def _start_digest(self) -> None:
        msg = bytes(self._app_msg)
        self._fixed_digest = b''
        self._xof = None
        self._beats_pushed = 0
        self._beat_in_rate = 0

        hash_type = MODE_STRENGTH_TABLE[self._app_mode, self._app_strength]

        if self._app_mode == _Mode.SHA3:
            hash_engine = hash_type.new()
            hash_engine.update(msg)
            self._fixed_digest = hash_engine.digest()
        elif self._app_mode == _Mode.SHAKE:
            self._xof = hash_type.new()
            self._xof.update(msg)
        elif self._app_mode == _Mode.CSHAKE:
            # cSHAKE uses empty strings because the prefixes are configured via KMAC CSRs. This is
            # ignored for the standalone sim.
            self._xof = hash_type.new(custom=b'', function=b'')
            self._xof.update(msg)
        elif self._app_mode == _Mode.KMAC:
            # The KMAC HWIP produces a fixed-length digest. It uses an empty customization string.
            # The actual key is provided via the keymgr but for the standalone sim we use a fixed
            # key. We take it from test case 192 of:
            # https://raw.githubusercontent.com/usnistgov/ACVP-Server/refs/heads/master/gen-val/
            # json-files/KMAC-256-1.0/internalProjection.json
            key = b'B2A3DA3797DA3C7353F4F612F5A244E66F4DCDD9B31BFE3A5EA88C93DEA1ACF13DEB1E635951365A8BC5A7141066AAF9'  # noqa: E501
            kmac_engine = hash_type.new(key=key, mac_len=KMAC_KEY_LENGTH // 8, custom=b'')
            kmac_engine.update(msg)
            self._fixed_digest = kmac_engine.digest()

    def _digest_value(self, idx: int) -> int:
        '''Return the 64-bit digest beat at index idx (Keccak lane order).
        For SHA3-224, the last response contains only 32 bits of output. The upper 32 bits are
        zeros. '''
        lo = idx * 8
        if self._xof is not None:
            chunk = self._xof.read(8)
        else:
            chunk = self._fixed_digest[lo:lo + 8]
            if len(chunk) < 8:
                # Pad the chunk to 64 bits. Required for the last beat of SHA3-224.
                chunk = chunk + b'\x00' * (8 - len(chunk))
        return int.from_bytes(chunk, 'little')

    def _emit_beat(self) -> None:
        '''Mask the next digest beat and write it to the KMAC_DATA WSRs.'''
        val = self._digest_value(self._beats_pushed)
        # Mask the digest with a fixed value to make the simulator deterministic.
        self._wsrs.KMAC_DATA_S0.hw_write(val ^ KMAC_DIGEST_MASK)
        self._wsrs.KMAC_DATA_S1.hw_write(KMAC_DIGEST_MASK)
        self._beats_pushed += 1
        self._beat_in_rate += 1
