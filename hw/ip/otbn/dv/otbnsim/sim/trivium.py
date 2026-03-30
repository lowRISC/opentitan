# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import math
from enum import IntEnum
from typing import List


class SeedType(IntEnum):
    # This is the regular (standardized for Trivium) method for seeding the
    # cipher whereby an 80-bit key and 80-bit IV are injected into the state
    # before the initialization rounds are executed.
    KEY_IV = 0
    # The entire state is seeded once with a seed of the same length. No
    # initialization rounds are executed.
    STATE_FULL = 1
    # Every seed operation fills a chunk of predefined size of the state
    # starting with the least significant region until every bit of the state
    # has been seeded. The seed operations can be interspersed with update
    # invocations such that keystream and seeding can take place concurrently.
    # Seeding and updating at the same time should only be done if the output
    # width is larger than the smallest state register (84 bits for Trivium and
    # Bivium) since only then we can be sure that a partial seed has diffused
    # sufficiently into the state between two seed calls. See `prim_trivium.sv`
    # for more details.
    STATE_PARTIAL = 2


class CipherType(IntEnum):
    # Both Trivium and its simpler variant Bivium can be instantiated. Note
    # only Trivium is a standardized cipher while Bivium serves a vehicule to
    # study the cryptanalytic properties of this family of ciphers. Both
    # primitives can be used to instantiate a PRNG.
    TRIVIUM = 0
    BIVIUM = 1


def i2b(i: int, n: int) -> List[int]:
    """Convert a little endian integer `i` to a `n`-bit array with the LSB at
    idx 0. The resulting bit array is padded with 0s if log2(i) < `n` until its
    size is `n` bits. Regardless of `n` there will always be at least
    ceil(log2(i)) bits"""
    return [int(b) for b in bin(i)[2:].zfill(n)][::-1]


def b2i(b: List[int]) -> int:
    """Convert a bit array `b` with the LSB at idx 0 to a little endian
    integer."""
    return int("".join(str(d) for d in b[::-1]), 2)


class Trivium:
    """This is a cycle-accurate model of the OpenTitan Trivium primitive.

    Instantiating this class corresponds to the cipher state after the reset.
    Subsequently, two operations can be scheduled in a cycle interval, i.e.,
    between calls to `step`.

      - `seed`: Pass a seed to the cipher that will appear in the state after
          the next `step` call. Depending on the seed type different update
          sequences are necessary to complete the initialization routines.

          - KEY_IV: The entire state needs to be updated 4 times over which
              means ceil(4 * `STATE_SIZE` / `OUTPUT_WIDTH`) calls to `update`
              and `step`.
          - STATE_FULL: Having called `step` after `seed` immediately readies
              the cipher for the generation of keystream bits.
          - STATE_PARTIAL: ceil(`STATE_SIZE` / `PART_SEED_SIZE`) step
              intervals with `seed` are required before the cipher is ready.
              There can intervals without `seed` calls. This models stall in
              the generation of seed bits from entropy complex.

      - `update`: Run the state update function and generate an updated state
          that replaces the current state at the end of the cycle interval,
          i.e., after the `step` call.
    """

    TRIVIUM_STATE_SIZE = 288
    BIVIUM_STATE_SIZE = 177

    PART_SEED_SIZE = 32
    TRIVIUM_LAST_PART_SEED_SIZE = 32
    BIVIUM_LAST_PART_SEED_SIZE = 17

    # Initial state after reset (see `prim_trivium_pkg.sv`).
    TRIVIUM_INIT_SEED = i2b(
        0x758A442031E1C4616EA343EC153282A30C132B5723C5A4CF4743B3C7C32D580F74F1713A,
        TRIVIUM_STATE_SIZE,
    )
    BIVIUM_INIT_SEED = TRIVIUM_INIT_SEED[0:BIVIUM_STATE_SIZE]

    def __init__(
        self,
        cipher_type: CipherType,
        seed_type: SeedType,
        output_width: int,
        init_seed: List[int] = [],
    ):
        """The cipher is defined by its cipher type (see `CipherType`), its
        seed type (see `SeedType`), the output (keystream) width and an
        optional initialization seed."""

        if cipher_type == CipherType.TRIVIUM:
            self.state_size = self.TRIVIUM_STATE_SIZE
            self.update_func = self._trivium_update
            self.last_part_seed_size = self.TRIVIUM_LAST_PART_SEED_SIZE
            self.state = self.TRIVIUM_INIT_SEED[:]

        elif cipher_type == CipherType.BIVIUM:
            self.state_size = self.BIVIUM_STATE_SIZE
            self.update_func = self._bivium_update
            self.last_part_seed_size = self.BIVIUM_LAST_PART_SEED_SIZE
            self.state = self.BIVIUM_INIT_SEED[:]

        else:
            raise ValueError("unknown cipher type:", cipher_type)

        if init_seed != []:
            if len(init_seed) != self.state_size:
                raise ValueError(
                    f"{cipher_type.name} init seed must be the same size as the state"
                )
            self.state = init_seed

        # Depending on cipher and seed type, a different number of seed rounds
        # have to be run.
        if seed_type == SeedType.KEY_IV:
            self.seed_rounds = math.ceil(4 * self.state_size / output_width)
            self.seed_counter = 0
        elif seed_type == SeedType.STATE_FULL:
            self.seed_rounds = 1
            self.seed_counter = 0
        elif seed_type == SeedType.STATE_PARTIAL:
            self.seed_rounds = math.ceil(self.state_size / self.PART_SEED_SIZE)
            self.seed_counter = 0
        else:
            raise ValueError("unknown seed type:", seed_type)

        self.cipher_type = cipher_type
        self.seed_type = seed_type
        self.output_width = output_width

        # Scheduled state and seed for the current cycle interval.
        self.next_state: List[int] = []
        self.next_seed: List[int] = []

        self.ks = [0] * output_width

    def update(self) -> None:
        """Run the state update function `OUTPUT_WIDTH`-many times and schedule
        the new state to replace the current state at end of the cycle interval.
        This will also generate the keystream that can be read via
        `keystream`."""

        if self.next_state != []:
            raise Exception("cannot update more than once per cycle interval")

        self.next_state = self.state[:]
        for i in range(self.output_width):
            self.ks[i] = self.update_func(self.next_state)

    def seed(self, seed: List[int]) -> None:
        """Schedule a new seed that depending on the seed type will be injected
        into the state at the end of the cycle interval."""

        if self.next_seed != []:
            raise Exception("cannot seed more than once per cycle interval")

        if self.seed_type == SeedType.KEY_IV:
            assert len(seed) == 160

            key = seed[0:80]
            iv = seed[80:160]

            if self.cipher_type == CipherType.TRIVIUM:
                self.next_seed = (
                    (key + [0] * 13) + (iv + [0] * 4) + ([0] * 108 + [1, 1, 1])
                )
            else:
                self.next_seed = (key + [0] * 13) + (iv + [0] * 4)

            if self.seed_done():
                self.seed_counter = 0

        elif self.seed_type == SeedType.STATE_FULL:
            assert len(seed) == self.state_size
            self.next_seed = seed
            self.seed_counter = 0

        else:
            assert len(seed) == self.PART_SEED_SIZE
            self.next_seed = seed

            if self.seed_done():
                self.seed_counter = 0

    def step(self) -> None:
        """Advance the state by one clock cycle. Depending on the
        scheduled state and seed this will alter the current state."""

        if self.next_state == [] and self.next_seed == []:
            # Do nothing when neither an update nor reseed is scheduled.
            return

        if self.seed_type == SeedType.KEY_IV:
            # Seeding takes precedence over updating.
            if self.next_seed != []:
                self.state = self.next_seed

            elif self.next_state != []:
                self.state = self.next_state
                if not self.seed_done():
                    self.seed_counter += 1

        elif self.seed_type == SeedType.STATE_FULL:
            # Seeding takes precedence over updating.
            if self.next_seed != []:
                self.state = self.next_seed
                self.seed_counter += 1

            elif self.next_state != []:
                self.state = self.next_state

        else:
            # Update and seeding in the same cycle interval is allowed. In this
            # case the state is first updated, then partially overwritten with
            # the seed bits.
            if self.next_state != []:
                self.state = self.next_state
            if self.next_seed != []:
                if self.seed_counter == self.seed_rounds - 1:
                    self.state[self.state_size - self.last_part_seed_size:] = (
                        self.next_seed[: self.last_part_seed_size]
                    )
                else:
                    self.state[
                        self.PART_SEED_SIZE * self.seed_counter:
                        self.PART_SEED_SIZE * (self.seed_counter + 1)
                    ] = self.next_seed

                self.seed_counter += 1

        self.next_state = []
        self.next_seed = []

    def keystream(self) -> List[int]:
        """Returns the generated keystream for the current cycle interval. Note
        that an `update` call is necessary to populate the keystream."""
        return self.ks

    def seed_done(self) -> bool:
        """Returns true if the seeding procedure has been completed."""
        return self.seed_rounds == self.seed_counter

    def _trivium_update(self, state: List[int]) -> int:
        mul_90_91 = state[90] & state[91]
        add_65_92 = state[65] ^ state[92]

        mul_174_175 = state[174] & state[175]
        add_161_176 = state[161] ^ state[176]

        mul_285_286 = state[285] & state[286]
        add_242_287 = state[242] ^ state[287]

        t0 = state[68] ^ (mul_285_286 ^ add_242_287)
        t1 = state[170] ^ (add_65_92 ^ mul_90_91)
        t2 = state[263] ^ (mul_174_175 ^ add_161_176)

        state[0:93] = [t0] + state[0:92]
        state[93:177] = [t1] + state[93:176]
        state[177:288] = [t2] + state[177:287]

        return add_65_92 ^ add_161_176 ^ add_242_287

    def _bivium_update(self, state: List[int]) -> int:
        mul_90_91 = state[90] & state[91]
        add_65_92 = state[65] ^ state[92]

        mul_174_175 = state[174] & state[175]
        add_161_176 = state[161] ^ state[176]

        t0 = state[68] ^ (mul_174_175 ^ add_161_176)
        t1 = state[170] ^ (add_65_92 ^ mul_90_91)

        state[0:93] = [t0] + state[0:92]
        state[93:177] = [t1] + state[93:176]

        return add_65_92 ^ add_161_176


_OUTPUT_WIDTH = 64


def check_keystream(trivium: Trivium, ref: List[int]) -> None:
    """Draw keystream bits and compare them against a test vector."""
    assert trivium.seed_done()

    # Draw (512 / 8)-many `_OUTPUT_WIDTH`-size words from the cipher.
    keystream = []
    for _ in range(_OUTPUT_WIDTH >> 3):
        trivium.update()
        trivium.step()
        keystream.extend(trivium.keystream())

    assert keystream == ref


if __name__ == "__main__":
    # Key-IV seed:
    #
    # Use the first key-iv test vector of the AVR cryptolib Trivium
    # implementation and generate 512 bits of keystream.

    # AVR cryptolib: Set 1, vector 0
    ref = i2b(
        int(
            """
F980FC5474EFE87BB9626ACCCC20FF98
807FCFCE928F6CE0EB21096115F5FBD2
649AF249C24120550175C86414657BBB
0D5420443AF18DAF9C7A0D73FF86EB38""".replace("\n", ""),
            16,
        ),
        288,
    )

    trivium = Trivium(CipherType.TRIVIUM, SeedType.KEY_IV, _OUTPUT_WIDTH)

    key = i2b(0x01000000000000000000, 80)
    iv = [0] * 80

    # Reseed twice.
    for _ in range(2):
        trivium.seed(key + iv)
        trivium.step()

        while not trivium.seed_done():
            trivium.update()
            trivium.step()

        check_keystream(trivium, ref)

    # Full state seed:
    #
    # Use the state after the init rounds of the first test as a full state seed.

    seed = i2b(
        0xC7D7C89BCC06725B3D94718106F2A0656422AF1FA457B81F0D2516A9D565893A64C1E50E, 288
    )

    trivium = Trivium(CipherType.TRIVIUM, SeedType.STATE_FULL, _OUTPUT_WIDTH)

    # Reseed twice.
    for _ in range(2):
        trivium.seed(seed)
        trivium.step()

        check_keystream(trivium, ref)

    # Partial state seed
    #
    # Use the state after the init rounds of the first test as a partial state seed.

    seeds = [
        i2b(0x64C1E50E, Trivium.PART_SEED_SIZE),
        i2b(0xD565893A, Trivium.PART_SEED_SIZE),
        i2b(0x0D2516A9, Trivium.PART_SEED_SIZE),
        i2b(0xA457B81F, Trivium.PART_SEED_SIZE),
        i2b(0x6422AF1F, Trivium.PART_SEED_SIZE),
        i2b(0x06F2A065, Trivium.PART_SEED_SIZE),
        i2b(0x3D947181, Trivium.PART_SEED_SIZE),
        i2b(0xCC06725B, Trivium.PART_SEED_SIZE),
        i2b(0xC7D7C89B, Trivium.PART_SEED_SIZE),
    ]

    trivium = Trivium(CipherType.TRIVIUM, SeedType.STATE_PARTIAL, _OUTPUT_WIDTH)

    # Reseed twice.
    for _ in range(2):
        # Need ceil(288/32) seed calls to fill every bit of the state.
        for i in range(9):
            trivium.seed(seeds[i])
            trivium.step()

        check_keystream(trivium, ref)
