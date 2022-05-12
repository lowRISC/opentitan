# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
"""Utilities used to download firmware images into the OpenTitan system."""

import time
import hashlib
from functools import partial
from collections import namedtuple


def _uint_to_le(val, length):
    """Returns a byte array that represents an unsigned integer in little-endian format.

    Args:
      val: Unsigned integer to convert.
      length: Number of bytes.

    Returns:
      A byte array of ``length`` bytes that represents ``val`` in little-endian format.
    """
    return val.to_bytes(length=length, byteorder='little')


def _le_to_uint(val):
    """Returns the unsigned integer represented by the given byte array in little-endian format.

    Args:
      val: Byte array in little-endian format that represents an unsigned integer.

    Returns:
      The unsigned integer represented by the byte array ``val``.
    """
    return int.from_bytes(val, byteorder='little')


class _SpiFlashFrame:
    """A frame used for programming OpenTitan over the SPI interface.

    In order to program OpenTitan with a binary image, the image is broken into ``PAYLOAD_SIZE``
    byte chunks, each of which is transmitted as a frame over the SPI interface. A frame consists
    of four parts:
    * Digest: A ``DIGEST_SIZE`` byte digest of the rest of the frame,
    * Frame number: A ``FRAME_NUMBER_SIZE`` byte little-endian representation of the frame number.
      MSB of the last frame's frame number is set to 1 to indicate the end of the image.
    * Flash offset: A ``FLASH_OFFSET_SIZE`` byte little-endian representation of the flash offset
      to start writing the payload of the frame.
    * Payload: ``PAYLOAD_SIZE`` byte actual binary payload in little-endian format.

    OpenTitan signals correct transmission of frame N-1 by transmitting its digest (computed over
    the entire frame, i.e. including the digest field of the frame) while it receives frame N.

    Attributes:
      HASH_FUNCTION: Hash function to use for digest computations.
      DIGEST_SIZE: Size of digests (inferred from ``HASH_FUNCTION``).
      FRAME_NUMBER_SIZE: Size of the frame number field in bytes.
      FLASH_OFFSET_SIZE: Size of the flash offset field in bytes.
      PAYLOAD_SIZE: Size of the frame payload in bytes.
      FRAME_SIZE: Size of the SPI Flash frame, depends on the Boot ROM, see spiflash_frame.h.
      is_second_frame: Indicates if this is the second frame.
      expected_ack: Expected acknowledgement value for a frame.
    """
    HASH_FUNCTION = hashlib.sha256
    DIGEST_SIZE = HASH_FUNCTION().digest_size
    FRAME_NUMBER_SIZE = 4
    FLASH_OFFSET_SIZE = 4
    FRAME_SIZE = 2048
    PAYLOAD_SIZE = FRAME_SIZE - DIGEST_SIZE - FRAME_NUMBER_SIZE - FLASH_OFFSET_SIZE

    def __init__(self, frame_number, flash_offset, payload):
        """Inits a _SpiFlashFrame.

        Also pads frame payload to ``PAYLOAD_SIZE`` bytes if needed.

        Args:
          frame_numer: Frame number.
          flash_offset: Flash offset.
          payload: Frame payload.
        """
        self._frame_number = _uint_to_le(frame_number, self.FRAME_NUMBER_SIZE)
        self._flash_offset = _uint_to_le(flash_offset, self.FLASH_OFFSET_SIZE)
        self._payload = payload
        padding = self.PAYLOAD_SIZE - len(self._payload)
        if padding > 0:
            self._payload = b''.join([self._payload, b'\xFF' * padding])

        # Reverse the order of the bytes to make them little-endian and be
        # consistent with the code signing tool.
        self._digest = self.HASH_FUNCTION(b''.join([
            self._frame_number,
            self._flash_offset,
            self._payload,
        ])).digest()[::-1]

    def __bytes__(self):
        return b''.join([
            self._digest,
            self._frame_number,
            self._flash_offset,
            self._payload,
        ])

    def __repr__(self):
        return f'frame 0x{_le_to_uint(self._frame_number):08X} @ \
            0x{_le_to_uint(self._flash_offset):08X}'

    @property
    def is_second_frame(self):
        """Indicates if this is the second frame."""
        return _le_to_uint(self._frame_number) == 1

    @property
    def expected_ack(self):
        """Expected acknowledgement value for the frame."""
        # Reverse the order of the bytes to make them little-endian and be
        # consistent with the code signing tool.
        return self.HASH_FUNCTION(bytes(self)).digest()[::-1]


class _Bootstrap:
    """Handles low-level details during programming OpenTitan using SAM3X/U on CW310/305.

    Initializes pins, resets OpenTitan, transmits frames, and receives acknowledgements.

    To use:
    >>> with _Bootstrap(fpga) as bootstrap:
    >>>   ...
    >>>   ack = bootstrap.transfer(frame)
    >>>   ...
    """
    # Pin mappings for CW305/CW310 boards.
    PinMapping = namedtuple('PinMapping', ['PIN_SCK',
                                           'PIN_SDI',
                                           'PIN_SDO',
                                           'PIN_CS',
                                           'PIN_TRST',
                                           'PIN_SRST',
                                           'PIN_SW_STRAP0',
                                           'PIN_SW_STRAP1',
                                           'PIN_SW_STRAP2',
                                           'PIN_TAP_STRAP0',
                                           'PIN_TAP_STRAP1'
                                           ])
    _PIN_MAPPINGS = {}
    _PIN_MAPPINGS['CW305'] = PinMapping('USB_A9',
                                        'USB_A10',
                                        'USB_A11',
                                        'USB_A12',
                                        'USB_A13',
                                        'USB_A14',
                                        'USB_A15',
                                        'USB_A16',
                                        'USB_A17',
                                        'USB_A18',
                                        'USB_A19')
    _PIN_MAPPINGS['CW310'] = PinMapping('USB_SPI_SCK',
                                        'USB_SPI_COPI',
                                        'USB_SPI_CIPO',
                                        'USB_SPI_CS',
                                        'USB_A13',
                                        'USB_A14',
                                        'USB_A15',
                                        'USB_A16',
                                        'USB_A17',
                                        'USB_A18',
                                        'USB_A19')
    _board = 'CW305'

    # Delays below are in seconds.
    _BOOTSTRAP_DELAY = 0.1
    _SECOND_FRAME_DELAY = 0.2
    _INTER_FRAME_DELAY = 0.02

    def __init__(self, fpga, board='CW305'):
        """Inits a _Bootstrap with a CW310/305.

        Args:
          fpga: CW310/305 to be programmed, a ``cw.capture.targets.CW310/305`` instance.
          board: can be ``CW310`` or ``CW305`` to distinguish the different board types.
        """

        # Check board type.
        if board in ['CW305', 'CW310']:
            self._board = board
        else:
            raise ValueError('board must be either CW305 or CW310, got ' + board)

        # Configure JTAG and bootstrap pins.
        self._fpga_io = fpga.gpio_mode()
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_TRST)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_SRST)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP0)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP1)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP2)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP0)
        self._fpga_io.pin_set_output(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TRST, 1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SRST, 1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP0, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP1, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP2, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP0, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP1, 1)
        # Initialize SPI pins.
        self._fpga_io.spi1_setpins(sck=self._PIN_MAPPINGS[self._board].PIN_SCK,
                                   sdo=self._PIN_MAPPINGS[self._board].PIN_SDI,
                                   sdi=self._PIN_MAPPINGS[self._board].PIN_SDO,
                                   cs=self._PIN_MAPPINGS[self._board].PIN_CS)
        self._fpga_io.spi1_enable(True)

    def _reset_opentitan(self):
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP1, 1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SRST, 0)
        time.sleep(self._BOOTSTRAP_DELAY)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SRST, 1)
        time.sleep(self._BOOTSTRAP_DELAY)

    def __enter__(self):
        """Starts bootstrapping."""
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP0, 1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP1, 1)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP2, 1)
        self._reset_opentitan()
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP1, 0)
        time.sleep(self._BOOTSTRAP_DELAY)
        return self

    def __exit__(self, exc_type, exc_value, traceback):
        """Ends bootstrapping."""
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP0, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP1, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_SW_STRAP2, 0)
        self._fpga_io.pin_set_state(self._PIN_MAPPINGS[self._board].PIN_TAP_STRAP1, 1)
        time.sleep(self._BOOTSTRAP_DELAY)

    def transfer(self, frame):
        """Transmits a frame over SPI and receives the acknowledgement for the previous frame."""
        # Wait longer after the first frame since it triggers a flash erase operation.
        if frame.is_second_frame:
            time.sleep(self._SECOND_FRAME_DELAY)
        else:
            time.sleep(self._INTER_FRAME_DELAY)
        print(f'Transferring {frame}.')
        # Acknowledgement is the same size as digests.
        return bytes(
            self._fpga_io.spi1_transfer(
                bytes(frame))[:_SpiFlashFrame.DIGEST_SIZE])


class SPIProgrammer:
    """Class for programming OpenTitan over the SPI interface of SAM3X/U on CW310/305."""
    def __init__(self, firmware_path, board='CW305'):
        """Inits SPIProgrammer with the path of a firmware image and board name."""
        self._firmware_path = firmware_path
        self._board = board

    def run(self, fpga):
        """Programs OpenTitan over the SPI interface of SAM3X/U on CW310/305.

        This implementation has two improvements over the `spiflash` tool under
        sw/host/spiflash:
        * Optimizes the happy path by checking the acknowledgement of frame N-1
          after transmitting frame N instead of transmitting an extra frame to check
          each frame's acknowledgement.
        * Sends an all 0xFF frame as the last frame to avoid cases where the last
          frame gets corrupted and halts the bootstrapping process.

        Args:
          fpga: CW310/305 to be programmed, a ``cw.capture.targets.CW310/305`` instance.
        """
        with _Bootstrap(fpga, self._board) as bootstrap:
            frame_number = 0
            flash_offset = 0
            prev_frame = None
            print(f'Programming OpenTitan with "{self._firmware_path}"...')
            with open(self._firmware_path, mode='rb') as fw:
                # Read fixed-size blocks from the firmware image.
                # Note: The second argument ``b''`` to ``iter`` below is the sentinel value that
                # ends the loop, i.e. the value returned by ``fw.read`` at EOF.
                for payload in iter(
                        partial(fw.read, _SpiFlashFrame.PAYLOAD_SIZE), b''):
                    frame = _SpiFlashFrame(frame_number, flash_offset, payload)
                    # We need to make sure that the previous frame is transmitted correctly before
                    # proceeding with the next frame.
                    while True:
                        # Transmit frame N, receive acknowledgement for frame N-1.
                        ack = bootstrap.transfer(frame)
                        if prev_frame and prev_frame.expected_ack != ack:
                            # When OpenTitan encounters a transmission error or an out of
                            # sequence frame, it ignores the current frame and sends the ack of
                            # the last successfully received frame. Since transmission errors
                            # can occur in both directions, i.e. the previous frame sent by
                            # SAM3U or the ack sent by OpenTitan, and we can't tell them
                            # apart, we should re-transmit the previous frame and check the
                            # ack sent by OpenTitan.
                            print(f'Error transferring {prev_frame}.')
                            ack = bootstrap.transfer(prev_frame)
                            if ack == frame.expected_ack:
                                # Ack sent by OpenTitan was corrupted. Proceed with the next frame.
                                break
                            else:
                                # Previous frame sent by SAM3U was corrupted. Send current frame
                                # again.
                                pass
                        else:
                            # Correct acknowledgement received or this is the first frame.
                            break
                    prev_frame = frame
                    frame_number += 1
                    flash_offset += _SpiFlashFrame.PAYLOAD_SIZE
            # Transmit an all 0xFF frame with the expected frame number to finish bootstrapping.
            bootstrap.transfer(
                _SpiFlashFrame(frame_number | (1 << 31), flash_offset, b''))
