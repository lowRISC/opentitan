# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from dataclasses import dataclass
from typing import Any, Optional
from enum import Enum, auto, unique
from Crypto.Hash import SHAKE128, SHAKE256, SHA3_224, SHA3_256, SHA3_384, SHA3_512
import secrets
from .csr import CSRFile
from .wsr import WSRFile

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


@unique
class KmacMode(Enum):
    """KMAC modes."""
    SHA3 = 0x0
    SHAKE = 0x2
    CSHAKE = 0x3
    INVALID = -1  # Internal use only for unknown values

    @classmethod
    def _missing_(cls, value: object) -> "KmacMode":
        """Map any unknown integer value to INVALID."""
        return cls.INVALID


@unique
class KmacStrength(Enum):
    """Kmac strengths."""
    L128 = 0x0
    L224 = 0x1
    L256 = 0x2
    L384 = 0x3
    L512 = 0x4
    INVALID = -1  # Internal use only for unknown values

    @classmethod
    def _missing_(cls, value: object) -> "KmacStrength":
        """Map any unknown integer value to INVALID."""
        return cls.INVALID


# Create a tuple key using the Enums
MODE_STRENGTH_TABLE = {
    # (Mode, Strength): (Implementation Class, Bit Width)
    (KmacMode.SHA3, KmacStrength.L224): (SHA3_224, 224),
    (KmacMode.SHA3, KmacStrength.L256): (SHA3_256, 256),
    (KmacMode.SHA3, KmacStrength.L384): (SHA3_384, 384),
    (KmacMode.SHA3, KmacStrength.L512): (SHA3_512, 512),
    (KmacMode.SHAKE, KmacStrength.L128): (SHAKE128, 128),
    (KmacMode.SHAKE, KmacStrength.L256): (SHAKE256, 256),
    # cSHAKE usually shares the SHAKE implementations but with customization strings
    (KmacMode.CSHAKE, KmacStrength.L128): (SHAKE128, 128),
    (KmacMode.CSHAKE, KmacStrength.L256): (SHAKE256, 256),
}


@unique
class KmacCmd(Enum):
    """Kmac commands."""
    NONE = 0x00
    START = 0x1d
    PROCESS = 0x2e
    RUN = 0x31
    DONE = 0x16
    INVALID = -1  # Internal use only for unknown values

    @classmethod
    def _missing_(cls, value: object) -> "KmacCmd":
        """Map any unknown integer value to INVALID."""
        return cls.INVALID


class KmacState(Enum):
    IDLE = auto()
    MSG_FEED = auto()
    PROCESSING = auto()
    ABSORBED = auto()
    SQUEEZING = auto()


class Counter():
    """A hardware-like counter model with separate Next (D) and Current (Q) states.

    This prevents updates within a cycle from taking effect until end_cycle() is called.
    This class also asserts that the counter value always stays between 0 and the max value.
    """

    def __init__(self, max_val: Optional[int] = None) -> None:
        # Assign the counter boundaries
        self._max_val = max_val
        # Initialize counter values
        self.reset()

    def _check_bounds(self, val: int) -> None:
        # Only check max if it is not None
        if self._max_val is not None:
            assert val <= self._max_val
        assert val >= 0

    def reset(self) -> None:
        # Initialize state to the minimum value
        self._next_val = 0
        self._curr_val = 0

    @property
    def value(self) -> int:
        """Returns the current counter value."""
        return self._curr_val

    def set_next(self, val: int) -> None:
        """Sets the next value directly."""
        self._check_bounds(val)
        self._next_val = val

    def increment(self, step: int = 1) -> int:
        """Calculates D = Q + step."""
        self._next_val = self._curr_val + step
        return self._next_val

    def decrement(self, step: int = 1) -> int:
        """Calculates D = Q - step."""
        self._next_val = self._curr_val - step
        return self._next_val

    def end_cycle(self) -> None:
        """Commits the next value to the current state."""
        # Verify the transition is legal before updating state
        self._check_bounds(self._next_val)
        self._curr_val = self._next_val


@dataclass
class Kmac():
    '''A model of the KMAC HW IP.
    '''
    # Declare the variable types.
    _csrs: CSRFile
    _wsrs: WSRFile
    _state: KmacState
    _state_next: KmacState
    _kmac_msg_send_words_left: Counter
    _keccak_round_ctr: Counter
    _keccak_absorbed_cnt: Counter
    _keccak_squeezed_cnt: Counter
    _sha3_digest: bytes
    _keccak_state: Any
    _keccak_rate_words: int
    _keccak_cap_bits: int
    _flush_cycle: bool
    _err_sw_cmd_seq: bool
    _err_sw_mode_strength: bool

    def __init__(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self.on_start(csrs, wsrs)
        self._reset_state()

    def on_start(self, csrs: CSRFile, wsrs: WSRFile) -> None:
        self._csrs = csrs
        self._wsrs = wsrs

    def step(self) -> None:
        """Advance the KMAC state by one cycle."""

        # Check if KMAC_DATA_S0/1 were accessed in the last cycle.
        self._step_kmac_data()

        # Advance the KMAC FSM.
        self._step_fsm()

        # Update KMAC error status based on FSM-detected conditions
        # (e.g., err_sw_cmd_seq, err_sw_mode_strength).
        self._update_kmac_error()

        # Decrement Keccak counter if Keccak is running.
        if self._keccak_round_ctr.value:
            self._keccak_round_ctr.decrement()

        # Handle KMAC_MSG_SEND command.
        kmac_msg_send = self._csrs.KMAC_MSG_SEND.read_unsigned()
        if kmac_msg_send:
            if self._state == KmacState.MSG_FEED and self._csrs.KMAC_IF_STATUS.get_msg_write_rdy():
                # Valid MSG_SEND: start absorbing the next KMAC_WSR_WORDS words.
                self._kmac_msg_send_words_left.set_next(KMAC_WSR_WORDS)
            else:
                # MSG_SEND issued in an invalid state or while busy.
                # Trigger sticky send error and ignore the command.
                self._csrs.KMAC_IF_STATUS.set_msg_send_error()

        # Absorb any available message words if the Keccak core is not busy.
        if self._kmac_msg_send_words_left.value and not self._keccak_round_ctr.value:
            word_index = KMAC_WSR_WORDS - self._kmac_msg_send_words_left.value
            self._absorb(word_index)
            self._kmac_msg_send_words_left.decrement()

        # MSG write interface is ready only when the FSM is in MSG_FEED
        # and KMAC is not currently absorbing another message.
        self._csrs.KMAC_IF_STATUS.update_msg_write_rdy(self._state == KmacState.MSG_FEED
                                                       and not self._kmac_msg_send_words_left.value
                                                       and not kmac_msg_send)

        # If KMAC is in the squeeze state, check if KMAC_DATA can be populated.
        if self._csrs.KMAC_STATUS.is_squeezing():
            self._squeeze()

        return

    def end_cycle(self) -> None:
        # Commit state transition
        self._state = self._state_next
        self._keccak_round_ctr.end_cycle()
        self._keccak_absorbed_cnt.end_cycle()
        self._keccak_squeezed_cnt.end_cycle()
        self._kmac_msg_send_words_left.end_cycle()

    def _step_kmac_data(self) -> None:
        # Set the message write error if an illegal write to KMAC_DATA_S0/1 happened.
        if (self._wsrs.KMAC_DATA.shares_dirty() and
                not self._csrs.KMAC_IF_STATUS.get_msg_write_rdy()):
            self._csrs.KMAC_IF_STATUS.set_msg_write_error()

        # Reset the dirty bits.
        self._wsrs.KMAC_DATA.clean_shares()

        # Invalidate the digest data if both shares were read.
        if self._wsrs.KMAC_DATA.all_shares_read():
            self._csrs.KMAC_IF_STATUS.clr_digest_valid()
            self._wsrs.KMAC_DATA.mark_all_unread()

    def _check_cmd(self, command: Optional[KmacCmd], allowed: set[KmacCmd]) -> None:
        if command not in allowed:
            self._csrs.KMAC_INTR.set_error()
            self._err_sw_cmd_seq = True

    def _step_fsm(self) -> None:
        self._state_next = self._state
        # Flush cycle is only True one cycle after the done command.
        self._flush_cycle_next = False
        # Set command/config error checker signals to false by default.
        # err_sw_cmd_seq might be set to True in _check_cmd().
        self._err_sw_cmd_seq = False
        # err_sw_mode_strength might be set to True in _start().
        self._err_sw_mode_strength = False
        # Get the next command.
        command = KmacCmd(self._csrs.KMAC_CMD.read_unsigned())
        # Get cfg mode.
        mode = KmacMode(self._csrs.KMAC_CFG.get_mode())

        # This state machine simulates the FSM inside kmac_errchk.sv.
        match self._state:
            case KmacState.IDLE:
                self._check_cmd(command, {KmacCmd.NONE, KmacCmd.START})

                if not self._flush_cycle:
                    self._csrs.KMAC_STATUS.set_idle()
                    if command == KmacCmd.START:
                        self._state_next = self._start()

            case KmacState.MSG_FEED:
                self._check_cmd(command, {KmacCmd.NONE, KmacCmd.PROCESS})
                self._csrs.KMAC_STATUS.set_absorb()
                if command == KmacCmd.PROCESS:
                    # TODO set the number of process cycles properly
                    self._keccak_round_ctr.set_next(KECCAK_PROCESS_CYCLES)
                    self._state_next = KmacState.PROCESSING

            case KmacState.PROCESSING:
                self._check_cmd(command, {KmacCmd.NONE})
                if not self._keccak_round_ctr.value and not self._kmac_msg_send_words_left.value:
                    self._state_next = KmacState.ABSORBED
                    self._csrs.KMAC_STATUS.set_squeeze()

            case KmacState.ABSORBED:
                self._check_cmd(command, {KmacCmd.NONE, KmacCmd.RUN, KmacCmd.DONE})
                self._csrs.KMAC_STATUS.set_squeeze()

                if command == KmacCmd.RUN and mode != KmacMode.SHA3:
                    self._state_next = KmacState.SQUEEZING
                    # TODO set the number of process cycles properly
                    self._keccak_round_ctr.set_next(KECCAK_PROCESS_CYCLES)
                elif command == KmacCmd.DONE:
                    self._state_next = KmacState.IDLE
                    self._flush_cycle_next = True
                    self._done()

            case KmacState.SQUEEZING:
                self._check_cmd(command, {KmacCmd.NONE})

                if self._keccak_round_ctr.value:
                    self._state_next = KmacState.ABSORBED
                    self._keccak_squeezed_cnt.set_next(0)
        return

    def _start(self) -> KmacState:
        # Get cfg mode and kStrength.
        mode = KmacMode(self._csrs.KMAC_CFG.get_mode())
        strength = KmacStrength(self._csrs.KMAC_CFG.get_kstrength())

        # Validate supported mode/strength combos
        entry = MODE_STRENGTH_TABLE.get((mode, strength))

        if entry is None:
            self._csrs.KMAC_INTR.set_error()
            self._err_sw_mode_strength = True
            return KmacState.IDLE

        # Instantiate state object
        constructor, cap_bits = entry
        self._keccak_state = constructor.new()
        self._keccak_rate_words = (1600 - 2 * cap_bits) // KMAC_WORD_BITS
        self._keccak_cap_bits = cap_bits

        return KmacState.MSG_FEED

    def _absorb(self, index: int) -> None:
        """Absorb one 64-bit word into the Keccak state.
        """
        if not (0 <= index < 4):
            raise ValueError(f"Word index {index} out of range [0..3].")

        # Select word: index 0 = least-significant 64 bits.
        shift = index * KMAC_WORD_BITS
        word_mask = (1 << KMAC_WORD_BITS) - 1

        # Determine how many bytes are valid for this word from BYTE_STROBE.
        num_bytes = self._get_num_bytes_from_byte_strobe(index)

        # Unmask the data shares and extract this word.
        share0 = self._wsrs.KMAC_DATA.get_unsigned(0)
        share1 = self._wsrs.KMAC_DATA.get_unsigned(1)
        data_unmasked = share0 ^ share1
        data_word = (data_unmasked >> shift) & word_mask

        # Convert to bytes (little-endian) and absorb.
        data_bytes = data_word.to_bytes(num_bytes, byteorder="little")
        self._keccak_state.update(data_bytes)

        # Track absorbed words and trigger Keccak round when rate is full.
        if self._keccak_absorbed_cnt.increment() >= self._keccak_rate_words:
            self._keccak_round_ctr.set_next(KECCAK_ROUND_CYCLES)
            self._keccak_absorbed_cnt.set_next(0)

    def _squeeze(self) -> None:
        """Squeeze one 64-bit word of output into KMAC_DATA."""

        # Stop if KMAC_DATA is already valid.
        if self._csrs.KMAC_IF_STATUS.get_digest_valid():
            return

        mode = KmacMode(self._csrs.KMAC_CFG.get_mode())
        if mode == KmacMode.SHA3:
            # Stop if we've already squeezed the maximum number of bits.
            if self._keccak_squeezed_cnt.value >= self._keccak_cap_bits:
                return

            # Initialize digest on first squeeze.
            if not self._keccak_squeezed_cnt.value:
                digest = self._keccak_state.digest()
                # Pad to a multiple of 8 bytes for 64-bit words.
                rem = len(digest) % KMAC_WORD_BYTES
                if rem:
                    digest += b'\x00' * (KMAC_WORD_BYTES - rem)
                self._sha3_digest = digest

            # Pop the next 64-bit word from the digest.
            chunk = self._sha3_digest[:KMAC_WORD_BYTES]
            self._sha3_digest = self._sha3_digest[KMAC_WORD_BYTES:]

        else:
            # Stop if a run command is needed for more digest data.
            if self._keccak_squeezed_cnt.value >= self._keccak_rate_words * KMAC_WORD_BITS:
                return

            # Generic squeeze path: read directly from _state.
            chunk = self._keccak_state.read(KMAC_WORD_BYTES)

        # Write the word into the masked data registers.
        value = int.from_bytes(chunk, byteorder="little")
        self._write_digest(value)

        # Advance squeezed bit counter.
        self._keccak_squeezed_cnt.increment(step=KMAC_WORD_BITS)

    def _done(self) -> None:
        """Handle DONE command by resetting internal state."""
        self._reset_state()

    def _get_num_bytes_from_byte_strobe(self, index: int) -> int:
        """Extracts the strobe bits corresponding to a specific word index
        and calculates the number of bytes that need to be absorbed.

        The BYTE_STROBE CSR must contain a value with contiguous ones starting
        from the LSB (e.g., 00111 is valid, 00101 is invalid).
        If the strobe is non-contiguous, the HW treats it as 0 (no bytes valid).
        """
        # Read the strobe configuration
        byte_strobe = self._csrs.KMAC_BYTE_STROBE.read_unsigned()

        # Check validity: Must be contiguous ones starting at LSB (2^k - 1).
        # Trick: x & (x + 1) is always 0 for values like 0, 1, 3, 7, 15...
        if (byte_strobe & (byte_strobe + 1)) != 0:
            return 0

        # Calculate shift/mask to extract bits for this specific word.
        shift = index * KMAC_WORD_BYTES
        strobe_mask = (1 << KMAC_WORD_BYTES) - 1

        # Extract the slice and return the number of bytes.
        word_strobe_slice = (byte_strobe >> shift) & strobe_mask
        num_bytes = word_strobe_slice.bit_count()
        return num_bytes

    def _update_kmac_error(self) -> None:
        """Update KMAC error code based on detected software error conditions."""
        code = None
        if self._err_sw_cmd_seq:
            code = KMAC_ERR_SW_CMD_SEQUENCE
        elif self._err_sw_mode_strength:
            code = KMAC_ERR_UNEXPECTED_MODE_STRENGTH

        if code is not None:
            self._csrs.KMAC_ERROR.write_error(code)

    def _write_digest(self, data: int) -> None:
        """Write one 64-bit digest word into the KMAC_DATA shares.
        """
        if not (0 <= data < (1 << KMAC_WORD_BITS)):
            raise RuntimeError(f"Data value {hex(data)} doesn't fit in "
                               f"{KMAC_WORD_BITS} unsigned bits.")

        # Generate random mask and split into two shares.
        rand64 = secrets.randbits(KMAC_WORD_BITS)
        share0 = data ^ rand64
        share1 = rand64

        # Set the two shares to the new values.
        self._wsrs.KMAC_DATA.set_unsigned(share_idx=0, value=share0)
        self._wsrs.KMAC_DATA.set_unsigned(share_idx=1, value=share1)

        # Mark the data as valid.
        self._csrs.KMAC_IF_STATUS.set_digest_valid()

        # Reset read flags since new data has been written.
        self._data_share_read = [False, False]

    def _reset_state(self) -> None:
        """Initialize or reset internal state to defaults."""
        #############################
        # KMAC/OTBN REGISTER VALUES #
        #############################

        # KMAC_STATUS CSR
        self._csrs.KMAC_STATUS.on_start()

        # KMAC_IF_STATUS CSR
        self._csrs.KMAC_IF_STATUS.on_start()

        # KMAC_INTR CSR
        self._csrs.KMAC_INTR.on_start()

        # KMAC_ERROR CSR
        self._csrs.KMAC_ERROR.on_start()

        # Writable KMAC CFG CSR
        self._csrs.KMAC_CFG.on_start()

        # BYTE_STROBE CSR
        self._csrs.KMAC_BYTE_STROBE.on_start()

        # KMAC_DATA WSRs
        self._wsrs.KMAC_DATA.set_unsigned(share_idx=0, value=0)
        self._wsrs.KMAC_DATA.set_unsigned(share_idx=1, value=0)

        #############################
        # KMAC MODEL CONTROL VALUES #
        #############################
        # Kmac FSM state variables
        self._state = KmacState.IDLE
        self._state_next = KmacState.IDLE
        # Number of words Keccak has left to absorb per kmac_msg_send command.
        self._kmac_msg_send_words_left = Counter(max_val=KMAC_WSR_WORDS)
        # Keccak round counter to keep track how long until the Keccak round is over.
        # A Keccak round takes KECCAK_ROUND_CYCLES cycles.
        self._keccak_round_ctr = Counter(max_val=KECCAK_PROCESS_CYCLES)
        # Count of absorbed words, used to determine when Keccak should start processing.
        self._keccak_absorbed_cnt = Counter()
        # Count of squeezed words, used to determine how much data is left to squeeze.
        self._keccak_squeezed_cnt = Counter()
        # In SHA3 mode, Crypto.Hash returns the whole digest at once.
        # This variable stores the whole digest.
        self._sha3_digest = bytes()
        # Instance of a Keccak-based hash (SHA3, SHAKE, or cSHAKE) from the crypto.hash library.
        self._keccak_state = None
        # Rate of the Keccak sponge in 64 bit words.
        self._keccak_rate_words = 0
        # Capacity of the Keccak sponge in bits.
        self._keccak_cap_bits = 0
        # When the FSM returns to IDLE the SHA3 is still in the FLUSH state for 1 cycle.
        self._flush_cycle = False
        # Error signals
        self._err_sw_cmd_seq = False
        self._err_sw_mode_strength = False
        # Track whether each data share has been read since the last write.
        self._data_share_read = [False, False]
