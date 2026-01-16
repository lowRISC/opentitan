# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Any, Optional
from enum import Enum, auto
from Crypto.Hash import SHAKE128, SHAKE256, SHA3_224, SHA3_256, SHA3_384, SHA3_512
import secrets

# Timing constants
KECCAK_ROUNDS = 24
KECCAK_ROUND_CYCLES = 4
KECCAK_PROCESS_CYCLES = KECCAK_ROUNDS * KECCAK_ROUND_CYCLES

# Register sizes
KMAC_CFG_BITS = 6
KMAC_INTR_BITS = 1
KMAC_MSG_SEND_BITS = 6
KMAC_CMD_BITS = 6
KMAC_CSR_BITS = 32
KMAC_WORD_BITS = 64
KMAC_WORD_BYTES = 8
KMAC_WSR_BITS = 256
KMAC_WSR_WORDS = KMAC_WSR_BITS // KMAC_WORD_BITS

# Field/Bit positions
KMAC_CFG_KMAC_EN_POS = 0
KMAC_CFG_KSTRENGTH_POS = 1
KMAC_CFG_MODE_POS = 4
KMAC_STATUS_SHA3_IDLE_POS = 0
KMAC_STATUS_SHA3_ABSORB_POS = 1
KMAC_STATUS_SHA3_SQUEEZE_POS = 2
KMAC_STATUS_IF_MSG_WRITE_RDY_POS = 0
KMAC_STATUS_IF_MSG_SEND_ERROR_POS = 1
KMAC_STATUS_IF_MSG_WRITE_ERROR_POS = 2
KMAC_STATUS_IF_DIGEST_VALID_POS = 3
KMAC_INTR_ERROR_POS = 0
KMAC_ERR_CODE_POS = 24

# Field masks
KMAC_BOOL_MASK = 0b1
KMAC_CFG_KSTRENGTH_MASK = 0b111
KMAC_CFG_MODE_MASK = 0b11

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
    status_sha3_idle: bool
    status_sha3_absorb: bool
    status_sha3_squeeze: bool
    status_sha3_idle_next: bool
    status_sha3_absorb_next: bool
    status_sha3_squeeze_next: bool
    status_if_msg_write_rdy: bool
    status_if_msg_write_rdy_next: bool
    status_if_msg_send_error: bool
    status_if_msg_send_error_next: bool
    status_if_msg_send_error_set: bool
    status_if_msg_send_error_clear: bool
    status_if_msg_write_error: bool
    status_if_msg_write_error_next: bool
    status_if_msg_write_error_set: bool
    status_if_msg_write_error_clear: bool
    status_if_digest_valid: bool
    status_if_digest_valid_next: bool
    kmac_error_intr: bool
    kmac_error_intr_next: bool
    kmac_error_intr_clear: bool
    kmac_error_intr_set: bool
    kmac_error: int
    kmac_error_next: int
    kmac_en: int
    kstrength: int
    mode: int
    kmac_en_next: int
    kstrength_next: int
    mode_next: int
    kmac_msg_send: bool
    kmac_msg_send_next: bool
    command: Optional[str]
    command_next: Optional[str]
    byte_strobe: int
    byte_strobe_next: int
    data: list[int]
    data_next: list[int]
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
    _keccak_state: Any
    _keccak_rate_words: int
    _keccak_cap_bits: int
    flush_cycle: bool
    err_sw_cmd_seq: bool
    err_sw_mode_strength: bool
    data_share_read: list[bool]

    def __init__(self) -> None:
        self._reset_state()

    def get_status(self) -> int:
        # Construct the status register value from the individual status flags.
        status = int(self.status_sha3_idle) << KMAC_STATUS_SHA3_IDLE_POS
        status |= int(self.status_sha3_absorb) << KMAC_STATUS_SHA3_ABSORB_POS
        status |= int(self.status_sha3_squeeze) << KMAC_STATUS_SHA3_SQUEEZE_POS
        return status

    def get_if_status(self) -> int:
        # Construct the IF status register value from the individual status flags.
        if_status = int(self.status_if_msg_write_rdy) << KMAC_STATUS_IF_MSG_WRITE_RDY_POS
        if_status |= int(self.status_if_msg_send_error) << KMAC_STATUS_IF_MSG_SEND_ERROR_POS
        if_status |= int(self.status_if_msg_write_error) << KMAC_STATUS_IF_MSG_WRITE_ERROR_POS
        if_status |= int(self.status_if_digest_valid) << KMAC_STATUS_IF_DIGEST_VALID_POS
        return if_status

    def set_if_status(self, mask: int) -> None:
        """Clear IF error bits according to the input mask (write-1-to-clear)."""

        if not (0 <= mask < (1 << KMAC_CSR_BITS)):
            raise RuntimeError(
                f"IF status value {hex(mask)} exceeds the allowed {KMAC_CSR_BITS}-bit range."
            )

        # Set clear signals for requested IF error bits.
        self.status_if_msg_send_error_clear = bool(
            self._field_from_int(mask, KMAC_STATUS_IF_MSG_SEND_ERROR_POS, KMAC_BOOL_MASK)
        )
        self.status_if_msg_write_error_clear = bool(
            self._field_from_int(mask, KMAC_STATUS_IF_MSG_WRITE_ERROR_POS, KMAC_BOOL_MASK)
        )

    def get_intr(self) -> int:
        # Construct the status register value from the interrupt flags.
        intr_status = int(self.kmac_error_intr)
        return intr_status

    def set_intr(self, mask: int) -> None:
        """Clear interrupt bits according to the input mask."""

        if not (0 <= mask < (1 << KMAC_CSR_BITS)):
            raise RuntimeError(
                f"Interrupt clear value {hex(mask)} exceeds the allowed {KMAC_CSR_BITS}-bit range."
            )

        # Clear the KMAC_ERROR interrupt bit if requested.
        self.kmac_error_intr_clear = bool(
            self._field_from_int(mask, KMAC_INTR_ERROR_POS, KMAC_BOOL_MASK)
        )
        return

    def get_error(self) -> int:
        return self.kmac_error

    def get_cfg(self) -> int:
        # Construct the config register value from the individual config values.
        cfg = int(self.kmac_en) << KMAC_CFG_KMAC_EN_POS
        cfg |= int(self.kstrength) << KMAC_CFG_KSTRENGTH_POS
        cfg |= int(self.mode) << KMAC_CFG_MODE_POS
        return cfg

    def set_cfg(self, value: int) -> None:
        if not (0 <= value < (1 << KMAC_CSR_BITS)):
            raise RuntimeError(
                f"Configuration value {hex(value)} exceeds the allowed {KMAC_CSR_BITS}-bit range."
            )

        if self.state == KmacState.IDLE:
            # Update the config values.
            self.kmac_en_next = bool(
                self._field_from_int(value, KMAC_CFG_KMAC_EN_POS, KMAC_BOOL_MASK)
            )
            self.kstrength_next = self._field_from_int(
                value,
                KMAC_CFG_KSTRENGTH_POS,
                KMAC_CFG_KSTRENGTH_MASK
            )
            self.mode_next = self._field_from_int(
                value,
                KMAC_CFG_MODE_POS,
                KMAC_CFG_MODE_MASK
            )

        return

    def set_msg_send(self) -> None:
        self.kmac_msg_send_next = True

    def set_cmd(self, value: int) -> None:
        if not (0 <= value < (1 << KMAC_CSR_BITS)):
            raise RuntimeError(
                f"Command value {hex(value)} exceeds the allowed {KMAC_CSR_BITS}-bit range."
            )

        self.command_next = KMAC_CMD.get(value)
        return

    def get_strobe(self) -> int:
        return self.byte_strobe

    def set_strobe(self, value: int) -> None:
        if not (0 <= value < (1 << KMAC_CSR_BITS)):
            raise RuntimeError(
                f"Strobe value {hex(value)} exceeds the allowed {KMAC_CSR_BITS}-bit range."
            )

        self.byte_strobe_next = value
        return

    def _get_data(self, share: int) -> int:
        if share not in (0, 1):
            raise RuntimeError("Share must be 0 or 1.")

        # Mark share as read.
        self.data_share_read[share] = True

        # Invalidate the digest data if both shares were read.
        if all(self.data_share_read):
            self.status_if_digest_valid_next = False

        return self.data[share]

    def _set_data(self, share: int, value: int) -> None:
        if not (0 <= value < (1 << KMAC_WSR_BITS)):
            raise RuntimeError(
                f"Message value {hex(value)} exceeds the allowed {KMAC_WSR_BITS}-bit range."
            )

        if share not in (0, 1):
            raise RuntimeError("Share must be 0 or 1.")

        if not self.status_if_msg_write_rdy:
            self.status_if_msg_write_error_next = True
            return

        self.data_next[share] = value
        return

    def get_data_s0(self) -> int:
        return self._get_data(0)

    def set_data_s0(self, value: int) -> None:
        self._set_data(0, value)
        return

    def get_data_s1(self) -> int:
        return self._get_data(1)

    def set_data_s1(self, value: int) -> None:
        self._set_data(1, value)
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
        if self.kmac_msg_send:
            if self.state == KmacState.MSG_FEED and self.status_if_msg_write_rdy:
                # Valid MSG_SEND: start absorbing the next KMAC_WSR_WORDS words.
                self.kmac_msg_send_words_left_next = KMAC_WSR_WORDS
            else:
                # MSG_SEND issued in an invalid state or while busy.
                # Trigger sticky send error and ignore the command.
                self.status_if_msg_send_error_set = True

        # Absorb any available message words if the keccak core is not busy.
        if self.kmac_msg_send_words_left > 0 and self.keccak_round_ctr == 0:
            word_index = KMAC_WSR_WORDS - self.kmac_msg_send_words_left
            self._absorb(word_index)
            self.kmac_msg_send_words_left_next = self.kmac_msg_send_words_left - 1

        # MSG write interface is ready only when the FSM is in MSG_FEED
        # and KMAC is not currently absorbing another message.
        self.status_if_msg_write_rdy_next = (
            self.state == KmacState.MSG_FEED
            and self.kmac_msg_send_words_left == 0
            and self.kmac_msg_send is False
        )

        # If KMAC is in the squeeze state, check if KMAC_DATA can be populated.
        if self.status_sha3_squeeze:
            self._squeeze()

        return

    def abort(self) -> None:
        # Abort state transition
        self.kmac_error_intr_clear = False
        self.status_if_msg_send_error_clear = False
        self.status_if_msg_write_error_clear = False
        self.kmac_en_next = self.kmac_en
        self.kstrength_next = self.kstrength
        self.mode_next = self.mode
        self.kmac_msg_send_next = self.kmac_msg_send
        self.command_next = self.command
        self.byte_strobe_next = self.byte_strobe
        # Only abort when the register is SW writable.
        if self.status_if_msg_write_rdy:
            self.data_next = self.data

    def commit(self) -> None:
        # Commit state transition
        self.status_sha3_idle = self.status_sha3_idle_next
        self.status_sha3_absorb = self.status_sha3_absorb_next
        self.status_sha3_squeeze = self.status_sha3_squeeze_next
        self.status_if_msg_write_rdy = self.status_if_msg_write_rdy_next
        self.status_if_digest_valid = self.status_if_digest_valid_next
        self.kmac_error = self.kmac_error_next
        self.kmac_en = self.kmac_en_next
        self.kstrength = self.kstrength_next
        self.mode = self.mode_next
        self.kmac_msg_send = self.kmac_msg_send_next
        self.command = self.command_next
        self.byte_strobe = self.byte_strobe_next
        self.data = self.data_next
        self.state = self.state_next
        self.keccak_round_ctr = self.keccak_round_ctr_next
        self.keccak_absorbed_cnt = self.keccak_absorbed_cnt_next
        self.keccak_squeezed_cnt = self.keccak_squeezed_cnt_next
        self.kmac_msg_send_words_left = self.kmac_msg_send_words_left_next

        # Update KMAC error interrupt latch.
        self._update_latch(
            value_attr="kmac_error_intr",
            next_attr="kmac_error_intr_next",
            set_attr="kmac_error_intr_set",
            clear_attr="kmac_error_intr_clear",
        )
        # Update IF status message send error latch.
        self._update_latch(
            value_attr="status_if_msg_send_error",
            next_attr="status_if_msg_send_error_next",
            set_attr="status_if_msg_send_error_set",
            clear_attr="status_if_msg_send_error_clear",
        )
        # Update IF status message write error latch.
        self._update_latch(
            value_attr="status_if_msg_write_error",
            next_attr="status_if_msg_write_error_next",
            set_attr="status_if_msg_write_error_set",
            clear_attr="status_if_msg_write_error_clear",
        )

        # Clear after write signals
        self.command_next = None
        self.kmac_msg_send_next = False

    def changes(self) -> None:
        # Our KMAC model doesn't track (or report) changes to its internal
        # state.
        raise NotImplementedError

    def _check_cmd(self, allowed: set[Optional[str]], state: str) -> None:
        if self.command not in allowed:
            self.kmac_error_intr_set = True
            self.err_sw_cmd_seq = True

    def _step_fsm(self) -> None:
        self.state_next = self.state
        self.status_sha3_idle_next = False
        self.status_sha3_absorb_next = False
        self.status_sha3_squeeze_next = False
        # Flush cycle is only True 1 cycle after the done command.
        self.flush_cycle_next = False
        # Set command/config error checker signals to false by default.
        # err_sw_cmd_seq might be set to True in _check_cmd().
        self.err_sw_cmd_seq = False
        # err_sw_mode_strength might be set to True in _start().
        self.err_sw_mode_strength = False

        # This state machine simulates the FSM inside kmac_errchk.sv.
        match self.state:

            # ---------------------- IDLE -------------------------
            case KmacState.IDLE:
                self._check_cmd({None, "start"}, "IDLE")

                if not self.flush_cycle:
                    self.status_sha3_idle_next = True

                    if self.command == "start":
                        self.state_next = self._start()

            # ---------------------- MSG_FEED ---------------------
            case KmacState.MSG_FEED:
                self._check_cmd({None, "process"}, "MSG_FEED")
                self.status_sha3_absorb_next = True
                if self.command == "process":
                    # TODO set the number of process cycles properly
                    self.keccak_round_ctr_next = KECCAK_PROCESS_CYCLES
                    self.state_next = KmacState.PROCESSING

            # ---------------------- PROCESSING -------------------
            case KmacState.PROCESSING:
                self._check_cmd({None}, "PROCESSING")
                if self.keccak_round_ctr == 0 and self.kmac_msg_send_words_left == 0:
                    self.state_next = KmacState.ABSORBED
                    self.status_sha3_squeeze_next = True

            # ---------------------- ABSORBED ---------------------
            case KmacState.ABSORBED:
                self._check_cmd({None, "run", "done"}, "ABSORBED")
                self.status_sha3_squeeze_next = True

                if self.command == "run" and KMAC_CFG_MODE.get(self.mode) != "SHA3":
                    self.state_next = KmacState.SQUEEZING
                    # TODO set the number of process cycles properly
                    self.keccak_round_ctr_next = KECCAK_PROCESS_CYCLES
                elif self.command == "done":
                    self.state_next = KmacState.IDLE
                    self.flush_cycle_next = True
                    self._done()

            # ---------------------- SQUEEZING --------------------
            case KmacState.SQUEEZING:
                self._check_cmd({None}, "SQUEEZING")

                if self.keccak_round_ctr == 0:
                    self.state_next = KmacState.ABSORBED
                    self.keccak_squeezed_cnt_next = 0
        return

    def _start(self) -> KmacState:
        mode = KMAC_CFG_MODE.get(self.mode)
        strength = KMAC_CFG_KSTRENGTH.get(self.kstrength)

        # Validate supported mode/strength combos
        entry = None
        if mode is not None and strength is not None:
            entry = MODE_STRENGTH_TABLE.get((mode, strength))

        if entry is None:
            self.kmac_error_intr_set = True
            self.err_sw_mode_strength = True
            return KmacState.IDLE

        # Instantiate state object
        constructor, cap_bits = entry
        self._keccak_state = constructor.new()
        self._keccak_rate_words = (1600 - 2 * cap_bits) // KMAC_WORD_BITS
        self._keccak_cap_bits = cap_bits

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
        byte_mask = (self.byte_strobe >> strobe_shift) & strobe_mask
        num_bytes = byte_mask.bit_count()

        # Unmask the data shares and extract this word.
        data_unmasked = (self.data[0] ^ self.data[1]) >> shift
        data_word = data_unmasked & word_mask

        # Convert to bytes (little-endian) and absorb.
        data_bytes = data_word.to_bytes(num_bytes, byteorder="little")
        self._keccak_state.update(data_bytes)

        # Track absorbed words and trigger keccak round when rate is full.
        self.keccak_absorbed_cnt_next += 1
        if self.keccak_absorbed_cnt_next >= self._keccak_rate_words:
            self.keccak_round_ctr_next = KECCAK_ROUND_CYCLES
            self.keccak_absorbed_cnt_next = 0

    def _squeeze(self) -> None:
        """Squeeze one 64-bit word of output into KMAC_DATA."""
        # Stop if KMAC_DATA is already valid.
        if self.status_if_digest_valid:
            return

        mode = KMAC_CFG_MODE.get(self.mode)

        if mode == "SHA3":
            # Stop if we've already squeezed the maximum number of bits.
            if self.keccak_squeezed_cnt >= self._keccak_cap_bits:
                return

            # Initialize digest on first squeeze.
            if self.keccak_squeezed_cnt == 0:
                digest = self._keccak_state.digest()
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
            if self.keccak_squeezed_cnt >= self._keccak_rate_words * KMAC_WORD_BITS:
                return

            # Generic squeeze path: read directly from _state.
            value = int.from_bytes(
                self._keccak_state.read(KMAC_WORD_BYTES), byteorder="little"
            )

        # Write the word into the masked data registers.
        self._write_data(value)

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

        self.kmac_error_next = code << KMAC_ERR_CODE_POS

    def _write_data(self, data: int) -> None:
        """Write one 64-bit word into the KMAC_DATA shares.

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
        self.data_next[0] = share0
        self.data_next[1] = share1

        # Mark this the data as valid.
        self.status_if_digest_valid_next = True

        # Reset read flags since new data has been written.
        self.data_share_read = [False] * len(self.data)

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

    def _field_from_int(self, value: int, pos: int, mask: int) -> int:
        return (value >> pos) & mask

    def _reset_state(self) -> None:
        """Initialize or reset internal state to defaults."""
        #############################
        # KMAC/OTBN REGISTER VALUES #
        #############################

        # KMAC_STATUS CSR
        self.status_sha3_idle = True
        self.status_sha3_absorb = False
        self.status_sha3_squeeze = False
        self.status_sha3_idle_next = False
        self.status_sha3_absorb_next = False
        self.status_sha3_squeeze_next = False

        # KMAC_IF_STATUS CSR
        self.status_if_msg_write_rdy = False
        self.status_if_msg_write_rdy_next = False
        self.status_if_msg_send_error = False
        self.status_if_msg_send_error_next = False
        self.status_if_msg_send_error_set = False
        self.status_if_msg_send_error_clear = False
        self.status_if_msg_write_error = False
        self.status_if_msg_write_error_next = False
        self.status_if_msg_write_error_set = False
        self.status_if_msg_write_error_clear = False
        self.status_if_digest_valid = False
        self.status_if_digest_valid_next = False

        # KMAC_INTR CSR
        self.kmac_error_intr = False
        self.kmac_error_intr_next = False
        self.kmac_error_intr_clear = False
        self.kmac_error_intr_set = False

        # KMAC_ERROR CSR
        self.kmac_error = False
        self.kmac_error_next = False

        # Writable KMAC CFG CSR
        self.kmac_en = 0
        self.kstrength = 0
        self.mode = 0
        self.kmac_en_next = 0
        self.kstrength_next = 0
        self.mode_next = 0

        # KMAC_MSG_SEND CSR
        self.kmac_msg_send = False
        self.kmac_msg_send_next = False

        # KMAC_CMD CSR
        self.command = None
        self.command_next = None

        # BYTE_STROBE CSR
        self.byte_strobe = 0
        self.byte_strobe_next = 0

        # KMAC_DATA WSRs
        self.data = [0, 0]
        self.data_next = [0, 0]

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
        self._keccak_state = None
        # Rate of the Keccak sponge in 64 bit words.
        self._keccak_rate_words = 0
        # Capacity of the Keccak sponge in bits.
        self._keccak_cap_bits = 0
        # When the FSM returns to IDLE the SHA3 is still in the FLUSH state for 1 cycle.
        self.flush_cycle = False
        # Error signals
        self.err_sw_cmd_seq = False
        self.err_sw_mode_strength = False
        # Track whether each data share has been read since the last write.
        self.data_share_read = [False] * len(self.data)
