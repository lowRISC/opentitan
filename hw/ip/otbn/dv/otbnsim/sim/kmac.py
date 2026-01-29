# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Any, Optional
from enum import Enum, auto
from Crypto.Hash import SHAKE128, SHAKE256, SHA3_224, SHA3_256, SHA3_384, SHA3_512
import secrets
from .csr import CSRFile
from .wsr import WSRFile
from .kmac_ispr import KmacDataWSR

# Masking constants
NUM_SHARES = 2

# Timing constants
KECCAK_ROUNDS = 24
KECCAK_ROUND_CYCLES = 4
KECCAK_PROCESS_CYCLES = KECCAK_ROUNDS * KECCAK_ROUND_CYCLES

# Data sizes
KMAC_WORD_BITS = 64
KMAC_WORD_BYTES = 8
KMAC_WSR_BITS = 256
KMAC_WSR_WORDS = KMAC_WSR_BITS // KMAC_WORD_BITS

# Error codes
KMAC_ERR_UNEXPECTED_MODE_STRENGTH = 0x6
KMAC_ERR_SW_CMD_SEQUENCE = 0x8

KMAC_CFG_MODE = {
    0: "SHA3",
    2: "SHAKE",
    3: "cSHAKE",
}

KMAC_CFG_KSTRENGTH = {
    0: "L128",
    1: "L224",
    2: "L256",
    3: "L384",
    4: "L512",
}

MODE_STRENGTH_TABLE = {
    ("SHA3", "L224"): (SHA3_224, 224),
    ("SHA3", "L256"): (SHA3_256, 256),
    ("SHA3", "L384"): (SHA3_384, 384),
    ("SHA3", "L512"): (SHA3_512, 512),
    ("SHAKE", "L128"): (SHAKE128, 128),
    ("SHAKE", "L256"): (SHAKE256, 256),
}

KMAC_CMD = {
    0x00: "none",
    0x1d: "start",
    0x2e: "process",
    0x31: "run",
    0x16: "done",
}


class KmacState(Enum):
    IDLE = auto()
    MSG_FEED = auto()
    PROCESSING = auto()
    ABSORBED = auto()
    SQUEEZING = auto()


class Kmac():
    '''A model of the KMAC HW IP.
    '''
    # Declare the variable types.
    csrs: CSRFile
    wsrs: WSRFile
    state: KmacState
    state_next: KmacState
    kmac_msg_send_words_left: int
    kmac_msg_send_words_left_next: int
    keccak_round_ctr: int
    keccak_round_ctr_next: int
    keccak_absorbed_cnt: int
    keccak_absorbed_cnt_next: int
    keccak_squeezed_cnt: int
    keccak_squeezed_cnt_next: int
    sha3_digest: bytes
    keccak_state: Any
    keccak_rate_words: int
    keccak_cap_bits: int
    flush_cycle: bool
    err_sw_cmd_seq: bool
    err_sw_mode_strength: bool
    data_share_read: list[bool]

    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.csrs = csrs
        self.wsrs = wsrs
        self._reset_state()

        self.SET_WRITE_WSR_BY_IDX = {
            0x8: self.set_data_s0,
            0x9: self.set_data_s1,
        }

        self.SET_READ_WSR_BY_IDX = {
            0x8: self.get_data_s0,
            0x9: self.get_data_s1,
        }

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.csrs = csrs
        self.wsrs = wsrs

    def read_wsr(self, idx: int) -> int:
        func = self.SET_READ_WSR_BY_IDX.get(idx)

        if func is None:
            raise RuntimeError(f"Invalid KMAC reg index: {hex(idx)}")

        # Call the getter function corresponding to the index.
        return func()

    def write_wsr(self, idx: int, value: int) -> None:
        func = self.SET_WRITE_WSR_BY_IDX.get(idx)

        if func is None:
            raise RuntimeError(f"Invalid KMAC reg index: {hex(idx)}")

        # Call the setter function corresponding to the index.
        func(value)

    def _set_data(self, wsr: KmacDataWSR, value: int) -> None:
        if not (0 <= value < (1 << KMAC_WSR_BITS)):
            raise RuntimeError(
                f"Message value {hex(value)} exceeds the allowed {KMAC_WSR_BITS}-bit range."
            )

        if not self.csrs.KMAC_IF_STATUS.get_msg_write_rdy():
            self.csrs.KMAC_IF_STATUS.set_msg_write_error()

        wsr.write_unsigned(value, abortable=True)
        return

    def get_data_s0(self) -> int:
        # Mark share as read.
        self.data_share_read[0] = True

        # Invalidate the digest data if both shares were read.
        if all(self.data_share_read):
            self.csrs.KMAC_IF_STATUS.clr_digest_valid()

        return self.wsrs.KMAC_DATA_S0.read_unsigned()

    def get_data_s1(self) -> int:
        # Mark share as read.
        self.data_share_read[1] = True

        # Invalidate the digest data if both shares were read.
        if all(self.data_share_read):
            self.csrs.KMAC_IF_STATUS.clr_digest_valid()

        return self.wsrs.KMAC_DATA_S1.read_unsigned()

    def set_data_s0(self, value: int) -> None:
        self._set_data(self.wsrs.KMAC_DATA_S0, value)
        return

    def set_data_s1(self, value: int) -> None:
        self._set_data(self.wsrs.KMAC_DATA_S1, value)
        return

    def squeeze(self) -> int:
        self.keccak_round_ctr_next = KECCAK_ROUND_CYCLES
        return 0

    def step(self) -> None:
        """Advance the KMAC state by one cycle."""

        # Advance the KMAC FSM.
        self._step_fsm()

        # Update KMAC error status based on FSM-detected conditions
        # (e.g., err_sw_cmd_seq, err_sw_mode_strength).
        self._update_kmac_error()

        # Decrement keccak counter if keccak is running.
        if self.keccak_round_ctr > 0:
            self.keccak_round_ctr_next = self.keccak_round_ctr - 1

        # Handle KMAC_MSG_SEND command.
        kmac_msg_send = bool(self.csrs.KMAC_MSG_SEND.read_unsigned())
        if kmac_msg_send:
            if self.state == KmacState.MSG_FEED and self.csrs.KMAC_IF_STATUS.get_msg_write_rdy():
                # Valid MSG_SEND: start absorbing the next KMAC_WSR_WORDS words.
                self.kmac_msg_send_words_left_next = KMAC_WSR_WORDS
            else:
                # MSG_SEND issued in an invalid state or while busy.
                # Trigger sticky send error and ignore the command.
                self.csrs.KMAC_IF_STATUS.set_msg_send_error()

        # Absorb any available message words if the keccak core is not busy.
        if self.kmac_msg_send_words_left > 0 and self.keccak_round_ctr == 0:
            word_index = KMAC_WSR_WORDS - self.kmac_msg_send_words_left
            self._absorb(word_index)
            self.kmac_msg_send_words_left_next = self.kmac_msg_send_words_left - 1

        # MSG write interface is ready only when the FSM is in MSG_FEED
        # and KMAC is not currently absorbing another message.
        msg_write_rdy = (
            self.state == KmacState.MSG_FEED
            and self.kmac_msg_send_words_left == 0
            and kmac_msg_send is False
        )

        if msg_write_rdy:
            self.csrs.KMAC_IF_STATUS.set_msg_write_rdy()
        else:
            self.csrs.KMAC_IF_STATUS.clr_msg_write_rdy()

        # If KMAC is in the squeeze state, check if KMAC_DATA can be populated.
        if self.csrs.KMAC_STATUS.is_squeezing():
            self._squeeze()

        return

    def abort(self) -> None:
        # Keep state on abort.
        self.commit()

    def commit(self) -> None:
        # Commit state transition
        self.state = self.state_next
        self.keccak_round_ctr = self.keccak_round_ctr_next
        self.keccak_absorbed_cnt = self.keccak_absorbed_cnt_next
        self.keccak_squeezed_cnt = self.keccak_squeezed_cnt_next
        self.kmac_msg_send_words_left = self.kmac_msg_send_words_left_next

    def _check_cmd(self, command: Optional[str], allowed: set[Optional[str]]) -> None:
        if command not in allowed:
            self.csrs.KMAC_INTR.set_error()
            self.err_sw_cmd_seq = True

    def _step_fsm(self) -> None:
        self.state_next = self.state
        # Flush cycle is only True 1 cycle after the done command.
        self.flush_cycle_next = False
        # Set command/config error checker signals to false by default.
        # err_sw_cmd_seq might be set to True in _check_cmd().
        self.err_sw_cmd_seq = False
        # err_sw_mode_strength might be set to True in _start().
        self.err_sw_mode_strength = False
        # Get the next command.
        command = KMAC_CMD.get(self.csrs.KMAC_CMD.read_unsigned())
        # Get cfg mode.
        mode = KMAC_CFG_MODE.get(self.csrs.KMAC_CFG.get_mode())

        # This state machine simulates the FSM inside kmac_errchk.sv.
        match self.state:

            # ---------------------- IDLE -------------------------
            case KmacState.IDLE:
                self._check_cmd(command, {"none", "start"})

                if not self.flush_cycle:
                    self.csrs.KMAC_STATUS.set_idle()
                    if command == "start":
                        self.state_next = self._start()

            # ---------------------- MSG_FEED ---------------------
            case KmacState.MSG_FEED:
                self._check_cmd(command, {"none", "process"})
                self.csrs.KMAC_STATUS.set_absorb()
                if command == "process":
                    # TODO set the number of process cycles properly
                    self.keccak_round_ctr_next = KECCAK_PROCESS_CYCLES
                    self.state_next = KmacState.PROCESSING

            # ---------------------- PROCESSING -------------------
            case KmacState.PROCESSING:
                self._check_cmd(command, {"none"})
                if self.keccak_round_ctr == 0 and self.kmac_msg_send_words_left == 0:
                    self.state_next = KmacState.ABSORBED
                    self.csrs.KMAC_STATUS.set_squeeze()

            # ---------------------- ABSORBED ---------------------
            case KmacState.ABSORBED:
                self._check_cmd(command, {"none", "run", "done"})
                self.csrs.KMAC_STATUS.set_squeeze()

                if command == "run" and mode != "SHA3":
                    self.state_next = KmacState.SQUEEZING
                    # TODO set the number of process cycles properly
                    self.keccak_round_ctr_next = KECCAK_PROCESS_CYCLES
                elif command == "done":
                    self.state_next = KmacState.IDLE
                    self.flush_cycle_next = True
                    self._done()

            # ---------------------- SQUEEZING --------------------
            case KmacState.SQUEEZING:
                self._check_cmd(command, {"none"})

                if self.keccak_round_ctr == 0:
                    self.state_next = KmacState.ABSORBED
                    self.keccak_squeezed_cnt_next = 0
        return

    def _start(self) -> KmacState:
        # Get cfg mode and kStrength.
        mode = KMAC_CFG_MODE.get(self.csrs.KMAC_CFG.get_mode())
        strength = KMAC_CFG_KSTRENGTH.get(self.csrs.KMAC_CFG.get_kstrength())

        # Validate supported mode/strength combos
        entry = None
        if mode is not None and strength is not None:
            entry = MODE_STRENGTH_TABLE.get((mode, strength))

        if entry is None:
            self.csrs.KMAC_INTR.set_error()
            self.err_sw_mode_strength = True
            return KmacState.IDLE

        # Instantiate state object
        constructor, cap_bits = entry
        self.keccak_state = constructor.new()
        self.keccak_rate_words = (1600 - 2 * cap_bits) // KMAC_WORD_BITS
        self.keccak_cap_bits = cap_bits

        return KmacState.MSG_FEED

    def _absorb(self, index: int) -> None:
        """Absorb one 64-bit word into the Keccak state.

        Args:
            index: Word index within the 256-bit data block (0..3), where 0 is the 64 LSB.
        """
        if not (0 <= index < 4):
            raise ValueError(f"Word index {index} out of range [0..3].")

        # Select word: index 0 = least-significant 64 bits.
        shift = index * KMAC_WORD_BITS
        word_mask = (1 << KMAC_WORD_BITS) - 1

        # Set strobe mask and shift.
        strobe_shift = index * KMAC_WORD_BYTES
        strobe_mask = (1 << KMAC_WORD_BYTES) - 1

        # Determine how many bytes are valid for this word from BYTE_STROBE.
        byte_strobe = self.csrs.KMAC_BYTE_STROBE.read_unsigned()
        byte_mask = (byte_strobe >> strobe_shift) & strobe_mask
        num_bytes = byte_mask.bit_count()

        # Unmask the data shares and extract this word.
        share0 = self.wsrs.KMAC_DATA_S0.read_unsigned()
        share1 = self.wsrs.KMAC_DATA_S1.read_unsigned()
        data_unmasked = (share0 ^ share1) >> shift
        data_word = data_unmasked & word_mask

        # Convert to bytes (little-endian) and absorb.
        data_bytes = data_word.to_bytes(num_bytes, byteorder="little")
        self.keccak_state.update(data_bytes)

        # Track absorbed words and trigger keccak round when rate is full.
        self.keccak_absorbed_cnt_next += 1
        if self.keccak_absorbed_cnt_next >= self.keccak_rate_words:
            self.keccak_round_ctr_next = KECCAK_ROUND_CYCLES
            self.keccak_absorbed_cnt_next = 0

    def _squeeze(self) -> None:
        """Squeeze one 64-bit word of output into KMAC_DATA."""

        # Stop if KMAC_DATA is already valid.
        if self.csrs.KMAC_IF_STATUS.get_digest_valid():
            return

        mode = KMAC_CFG_MODE.get(self.csrs.KMAC_CFG.get_mode())
        if mode == "SHA3":
            # Stop if we've already squeezed the maximum number of bits.
            if self.keccak_squeezed_cnt >= self.keccak_cap_bits:
                return

            # Initialize digest on first squeeze.
            if self.keccak_squeezed_cnt == 0:
                digest = self.keccak_state.digest()
                # Pad to a multiple of 8 bytes for 64-bit words.
                rem = len(digest) % KMAC_WORD_BYTES
                if rem:
                    digest += b'\x00' * (KMAC_WORD_BYTES - rem)
                self.sha3_digest = digest

            # Pop the next 64-bit word from the digest.
            chunk, self.sha3_digest = (
                self.sha3_digest[:KMAC_WORD_BYTES],
                self.sha3_digest[KMAC_WORD_BYTES:]
            )
            value = int.from_bytes(chunk, byteorder="little")

        else:
            # Stop if a run command is needed for more digest data.
            if self.keccak_squeezed_cnt >= self.keccak_rate_words * KMAC_WORD_BITS:
                return

            # Generic squeeze path: read directly from _state.
            value = int.from_bytes(
                self.keccak_state.read(KMAC_WORD_BYTES), byteorder="little"
            )

        # Write the word into the masked data registers.
        self._write_digest(value)

        # Advance squeezed bit counter.
        self.keccak_squeezed_cnt_next += KMAC_WORD_BITS

    def _done(self) -> None:
        """Handle DONE command by resetting internal state."""
        self._reset_state()

    def _update_kmac_error(self) -> None:
        """Update KMAC error code based on detected software error conditions."""
        if self.err_sw_cmd_seq:
            code = KMAC_ERR_SW_CMD_SEQUENCE
        elif self.err_sw_mode_strength:
            code = KMAC_ERR_UNEXPECTED_MODE_STRENGTH
        else:
            # No new error detected, keep existing value.
            return

        self.csrs.KMAC_ERROR.write_unsigned(code)

    def _write_digest(self, data: int) -> None:
        """Write one 64-bit digest word into the KMAC_DATA shares.

        Args:
            data: 64-bit data word to write.
        """
        if not (0 <= data < (1 << KMAC_WORD_BITS)):
            raise RuntimeError(
                f"Data value {hex(data)} exceeds the allowed {KMAC_WORD_BITS}-bit range."
            )

        # Generate random mask and split into two shares.
        rand64 = secrets.randbits(KMAC_WORD_BITS)
        share0 = data ^ rand64
        share1 = rand64

        # Set the two shares to the new values.
        self.wsrs.KMAC_DATA_S0.write_unsigned(share0, abortable=False)
        self.wsrs.KMAC_DATA_S1.write_unsigned(share1, abortable=False)

        # Mark the data as valid.
        self.csrs.KMAC_IF_STATUS.set_digest_valid()

        # Reset read flags since new data has been written.
        self.data_share_read = [False] * NUM_SHARES

    def _update_latch(self, value_attr: str, next_attr: str,
                      set_attr: str, clear_attr: str) -> None:
        """Update a sticky latch with set/clear strobes (set has priority)."""
        if getattr(self, set_attr):
            setattr(self, next_attr, True)

        elif getattr(self, clear_attr):
            setattr(self, next_attr, False)

        # Commit and clear strobes.
        setattr(self, value_attr, getattr(self, next_attr))
        setattr(self, set_attr, False)
        setattr(self, clear_attr, False)

    def _reset_state(self) -> None:
        """Initialize or reset internal state to defaults."""
        #############################
        # KMAC/OTBN REGISTER VALUES #
        #############################

        # KMAC_STATUS CSR
        self.csrs.KMAC_STATUS.on_start()

        # KMAC_IF_STATUS CSR
        self.csrs.KMAC_IF_STATUS.on_start()

        # KMAC_INTR CSR
        self.csrs.KMAC_INTR.on_start()

        # KMAC_ERROR CSR
        self.csrs.KMAC_ERROR.on_start()

        # Writable KMAC CFG CSR
        self.csrs.KMAC_CFG.on_start()

        # BYTE_STROBE CSR
        self.csrs.KMAC_BYTE_STROBE.on_start()

        # KMAC_DATA WSRs
        self.wsrs.KMAC_DATA_S0.write_unsigned(0, abortable=False)
        self.wsrs.KMAC_DATA_S1.write_unsigned(0, abortable=False)

        #############################
        # KMAC MODEL CONTROL VALUES #
        #############################
        # Kmac FSM state variables
        self.state = KmacState.IDLE
        self.state_next = KmacState.IDLE
        # Number of words keccak has left to absorb per kmac_msg_send command.
        self.kmac_msg_send_words_left = 0
        self.kmac_msg_send_words_left_next = 0
        # Keccak round counter to keep track how long until the keccak round is over.
        # A keccak round takes KECCAK_ROUND_CYCLES cycles.
        self.keccak_round_ctr = 0
        self.keccak_round_ctr_next = 0
        # Count of absorbed words, used to determine when Keccak should start processing.
        self.keccak_absorbed_cnt = 0
        self.keccak_absorbed_cnt_next = 0
        # Count of squeezed words, used to determine how much data is left to squeeze.
        self.keccak_squeezed_cnt = 0
        self.keccak_squeezed_cnt_next = 0
        # In SHA3 mode, Crypto.Hash returns the whole digest at once.
        # This variable stores the whole digest.
        self.sha3_digest = bytes()
        # Instance of a Keccak-based hash (SHA3, SHAKE, or cSHAKE) from the crypto.hash library.
        self.keccak_state = None
        # Rate of the Keccak sponge in 64 bit words.
        self.keccak_rate_words = 0
        # Capacity of the Keccak sponge in bits.
        self.keccak_cap_bits = 0
        # When the FSM returns to IDLE the SHA3 is still in the FLUSH state for 1 cycle.
        self.flush_cycle = False
        # Error signals
        self.err_sw_cmd_seq = False
        self.err_sw_mode_strength = False
        # Track whether each data share has been read since the last write.
        self.data_share_read = [False] * NUM_SHARES
