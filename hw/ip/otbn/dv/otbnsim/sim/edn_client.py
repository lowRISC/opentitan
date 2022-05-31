# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import List, Optional, Tuple

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

        # If true, the next transaction that completes will be discarded.
        self._poisoned = False

        # If true, self._poisoned should also be true. In this case, after we
        # discard the next transaction that completes, we should re-try it.
        self._retry = False

    def request(self) -> None:
        '''Start a request if there isn't one pending'''
        if self._acc is None:
            assert self._cdc_counter is None
            self._acc = []
        elif self._poisoned:
            # This is a request when there was a RND fetch pending (from the
            # previous OTBN run), but we now actually want the results.
            self._retry = True

    def poison(self) -> None:
        '''Mark any current request as "poisoned" and clear the retry flag'''
        if self._acc is not None:
            self._poisoned = True
            self._retry = False

    def forget(self) -> None:
        '''Clear the retry flag, if set.

        This is used at the end of an operation to model the situation where a
        previous run had started a prefetch that we're still waiting for. In
        the meantime, we started an operation that also requested a prefetch.
        Normally, we'd want to make sure to send out *that* request as soon as
        the first (ignored) result came in. But maybe we've actually finished
        this run as well! In that case, we don't care about the prefetch that
        was pending and should just discard it.
        '''
        self._retry = False

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
        self._poisoned = False
        self._retry = False

    def cdc_complete(self) -> Tuple[Optional[int], bool]:
        '''Called when CDC completes for a transfer

        This returns a pair (data, retry). In normal operation (where the
        client hasn't been poisoned), data is the 256b word we received and
        retry is False.

        If the client was poisoned then data is None (meaning that we should
        discard the result). In this case, retry might be True, which means
        that we are going to retry the operation.
        '''
        assert self._acc is not None
        assert len(self._acc) == ACC_LEN
        assert self._cdc_counter is not None
        assert self._cdc_counter <= MAX_CDC_WAIT

        poisoned = self._poisoned
        retry = self._retry

        if poisoned:
            data = None
        else:
            # Assemble the ACC_LEN words into a single integer "little-endian"
            # (so the first word that came in is the bottom 32 bits).
            data = 0
            for word in reversed(self._acc):
                data = (data << 32) | word

        self._acc = None
        self._cdc_counter = None
        self._poisoned = False
        self._retry = False

        if retry:
            assert poisoned
            self.request()

        return (data, retry)

    def step(self) -> None:
        '''Called on each main clock cycle. Increment and check CDC counter'''
        if self._cdc_counter is not None:
            assert self._acc is not None
            assert len(self._acc) == ACC_LEN

            self._cdc_counter += 1
            assert self._cdc_counter <= MAX_CDC_WAIT
