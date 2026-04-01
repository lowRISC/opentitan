# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

from typing import Optional

# Number of required EDN transfers to fully seed the URND PRNG Bivium. This
# PRNG has a state size of 177 bits hence 6 32-bit seed words are neccessary to
# fully seed its state.
SEED_ROUNDS = 6

# The maximum of beats we allow between seed word transfers.
MAX_CDC_WAIT = 5


class EdnClientUrnd:
    """This is the EDN client that seeds the URND PRNG. It is a stripped-down
    variant of the RND EDN client (see `EdnClient`) that simply tracks how many
    EDN words have already received."""

    def __init__(self) -> None:
        # Counter of many seed words the client has received so far.
        self._seed_counter: Optional[int] = None

        # Counter of how many beats we've been waiting since receiving a seed
        # word.
        self._cdc_counter: Optional[int] = None

        # If true, the next transaction that completes will be discarded.
        self._poisoned = False

        # If true, self._poisoned should also be true. In this case, after we
        # discard the next transaction that completes, we should re-try it.
        self._retry = False

    def request(self) -> None:
        '''Start a request if there isn't one pending'''
        if self._seed_counter is None:
            assert self._cdc_counter is None
            self._seed_counter = 0
            self._cdc_counter = 0
        elif self._poisoned:
            # This is a request when there was a RND fetch pending (from the
            # previous OTBN run), but we now actually want the results.
            self._retry = True

    def poison(self) -> None:
        '''Mark any current request as "poisoned" and clear the retry flag'''
        if self._seed_counter is not None:
            self._poisoned = True
            self._retry = False

    def forget(self) -> None:
        '''Clear the retry flag, if set.'''
        self._retry = False

    def take_word(self) -> None:
        '''Register the requested with the client.'''

        if self._seed_counter is None:
            return
        else:
            assert self._seed_counter < SEED_ROUNDS
            assert self._cdc_counter <= MAX_CDC_WAIT

            self._seed_counter += 1
            self._cdc_counter = 0

    def edn_reset(self) -> None:
        '''Called on a reset signal on the EDN clock domain'''
        self._seed_counter = None
        self._cdc_counter = None
        self._poisoned = False
        self._retry = False

    def cdc_complete(self) -> bool:
        '''Called when CDC completes `SEED_ROUNDS` transfers.'''
        assert self._seed_counter is not None
        assert len(self._seed_counter) == SEED_ROUNDS
        assert self._cdc_counter is not None
        assert self._cdc_counter <= MAX_CDC_WAIT

        self._seed_counter = None
        self._cdc_counter = None
        self._poisoned = False
        self._retry = False

        if self._retry:
            assert self._poisoned
            self.request()

        return self._retry

    def step(self) -> None:
        '''Called on each main clock cycle. Increment and check CDC counter'''
        if self._cdc_counter is not None:
            assert self._seed_counter is not None

            self._cdc_counter += 1
            assert self._cdc_counter <= MAX_CDC_WAIT
