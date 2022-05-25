# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional

# The number of words to accumulate
ACC_LEN = 8

# The maximum of beats we allow between when we get the last word and are told
# that CDC has finished.
MAX_CDC_WAIT = 5


class EdnClient:
    def __init__(self) -> None:
        # An accumulator of 32-bit values that we've read so far. This is
        # non-None if we're in the middle of reading a value from the EDN. This
        # should always have length <= ACC_LEN (sending an extra beat of data
        # causes an error).
        self._acc = None  # type: Optional[List[int]]

        # A counter of the number of beats we've been waiting since self._acc
        # became full before being told that CDC was done. This is None unless
        # self._acc contains a list of ACC_LEN values.
        self._cdc_counter = None  # type: Optional[int]

    def request(self) -> None:
        '''Start a request if there isn't one pending'''
        if self._acc is None:
            assert self._cdc_counter is None
            self._acc = []

    def take_word(self, word: int) -> None:
        '''Take a 32-bit data word that we've been waiting for'''
        assert 0 <= word < (1 << 32)
        assert self._acc is not None
        assert len(self._acc) < ACC_LEN
        assert self._cdc_counter is None

        self._acc.append(word)

        if len(self._acc) == ACC_LEN:
            self._cdc_counter = 0

    def edn_reset(self) -> None:
        '''Called on a reset signal on the EDN clock domain'''
        self._acc = None
        self._cdc_counter = None

    def cdc_complete(self) -> int:
        '''Called when CDC completes for a transfer'''
        assert self._acc is not None
        assert len(self._acc) == ACC_LEN
        assert self._cdc_counter is not None
        assert self._cdc_counter <= MAX_CDC_WAIT

        # Assemble the ACC_LEN words into a single integer in a "little-endian"
        # fashion (so the first word that came in is the bottom 32 bits).
        acc = 0
        for word in reversed(self._acc):
            acc = (acc << 32) | word

        self._acc = None
        self._cdc_counter = None

        return acc

    def step(self) -> None:
        '''Called on each main clock cycle. Increment and check CDC counter'''
        if self._cdc_counter is not None:
            assert self._acc is not None
            assert len(self._acc) == ACC_LEN

            self._cdc_counter += 1
            assert self._cdc_counter <= MAX_CDC_WAIT
