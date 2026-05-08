# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

import math
from enum import IntEnum
from typing import Optional, Tuple, Union


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
    # only Trivium is a standardized cipher while Bivium serves a vehicle to
    # study the cryptanalytic properties of this family of ciphers. Both
    # primitives can be used to instantiate a PRNG.
    TRIVIUM = 0
    BIVIUM = 1


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

    # Initial state after reset as a little-endian integer (bit j = state[j]).
    # See `prim_trivium_pkg.sv`.
    TRIVIUM_INIT_SEED = 0x758A442031E1C4616EA343EC153282A30C132B5723C5A4CF4743B3C7C32D580F74F1713A
    BIVIUM_INIT_SEED = TRIVIUM_INIT_SEED & ((1 << BIVIUM_STATE_SIZE) - 1)

    def __init__(
        self,
        cipher_type: CipherType,
        seed_type: SeedType,
        output_width: int,
        init_seed: Optional[int] = None,
    ):
        """The cipher is defined by its cipher type (see `CipherType`), its
        seed type (see `SeedType`), the output (keystream) width and an
        optional initialization seed."""

        if cipher_type == CipherType.TRIVIUM:
            self.state_size = self.TRIVIUM_STATE_SIZE
            self.last_part_seed_size = self.TRIVIUM_LAST_PART_SEED_SIZE
        elif cipher_type == CipherType.BIVIUM:
            self.state_size = self.BIVIUM_STATE_SIZE
            self.last_part_seed_size = self.BIVIUM_LAST_PART_SEED_SIZE
        else:
            raise ValueError(f"unknown cipher type: {cipher_type}")

        if init_seed is not None:
            if not (0 <= init_seed < (1 << self.state_size)):
                raise ValueError(
                    f"{cipher_type.name} init seed must fit in {self.state_size} bits"
                )
            seed_int = init_seed
        elif cipher_type == CipherType.TRIVIUM:
            seed_int = self.TRIVIUM_INIT_SEED
        else:
            seed_int = self.BIVIUM_INIT_SEED

        # Cipher state is a tuple of Python integers using reversed-bit storage
        # (bit N-1-j of reg = state[j]). This allows updates to run as pure integer arithmetic.
        self.state = self._int_to_regs(seed_int, cipher_type)

        # Depending on cipher and seed type, a different number of seed rounds
        # have to be run.
        if seed_type == SeedType.KEY_IV:
            self.seed_rounds = math.ceil(4 * self.state_size / output_width)
        elif seed_type == SeedType.STATE_FULL:
            self.seed_rounds = 1
        elif seed_type == SeedType.STATE_PARTIAL:
            self.seed_rounds = math.ceil(self.state_size / self.PART_SEED_SIZE)
        else:
            raise ValueError(f"unknown seed type: {seed_type}")

        self.seed_counter = 0
        self.cipher_type = cipher_type
        self.seed_type = seed_type
        self.output_width = output_width

        # Scheduled state and seed for the current cycle interval. Next seed can be a full state
        # (multiple ints) or a partial seed (single int).
        self.next_state: Optional[Tuple[int, ...]] = None
        self.next_seed: Optional[Union[Tuple[int, ...], int]] = None

        self.ks: int = 0

    def update(self) -> None:
        """Run the state update function `OUTPUT_WIDTH`-many times and schedule
        the new state to replace the current state at end of the cycle interval.
        This will also generate the keystream that can be read via
        `keystream`."""

        if self.next_state is not None:
            raise Exception("cannot update more than once per cycle interval")

        self.next_state = self._update(*self.state)

    def seed(self, seed: int) -> None:
        """Schedule a new seed that depending on the seed type will be injected
        into the state at the end of the cycle interval."""

        if self.next_seed is not None:
            raise Exception("cannot seed more than once per cycle interval")

        if self.seed_type == SeedType.KEY_IV:
            # seed encodes key in bits [0, 80) and IV in bits [80, 160).
            assert 0 <= seed < (1 << 160)
            key = seed & ((1 << 80) - 1)
            iv = (seed >> 80) & ((1 << 80) - 1)
            if self.cipher_type == CipherType.TRIVIUM:
                state_int = key | (iv << 93) | (7 << 285)
            else:
                state_int = key | (iv << 93)
            self.next_seed = self._int_to_regs(state_int, self.cipher_type)
            if self.seed_done():
                self.seed_counter = 0

        elif self.seed_type == SeedType.STATE_FULL:
            assert 0 <= seed < (1 << self.state_size)
            self.next_seed = self._int_to_regs(seed, self.cipher_type)
            self.seed_counter = 0

        else:
            assert 0 <= seed < (1 << self.PART_SEED_SIZE)
            self.next_seed = seed
            if self.seed_done():
                self.seed_counter = 0

    def step(self) -> None:
        """Advance the state by one clock cycle. Depending on the
        scheduled state and seed this will alter the current state."""

        if self.next_state is None and self.next_seed is None:
            return

        if self.seed_type == SeedType.KEY_IV or self.seed_type == SeedType.STATE_FULL:
            # Seeding takes precedence over updating.
            if self.next_seed is not None:
                assert isinstance(self.next_seed, tuple)
                self.state = self.next_seed
                if self.seed_type == SeedType.STATE_FULL:
                    self.seed_counter += 1
            elif self.next_state is not None:
                self.state = self.next_state
                if not self.seed_done():
                    self.seed_counter += 1
        else:
            # STATE_PARTIAL: update and seeding in the same cycle interval is allowed.
            if self.next_state is not None:
                self.state = self.next_state
            if self.next_seed is not None:
                start = (self.state_size - self.last_part_seed_size
                         if self.seed_counter == self.seed_rounds - 1
                         else self.PART_SEED_SIZE * self.seed_counter)
                n = (self.last_part_seed_size
                     if self.seed_counter == self.seed_rounds - 1
                     else self.PART_SEED_SIZE)
                assert isinstance(self.next_seed, int)
                self._inject_partial_seed(self.next_seed, start, n)
                self.seed_counter += 1

        self.next_state = None
        self.next_seed = None

    def keystream(self) -> int:
        """Returns the generated keystream for the current cycle interval. Note
        that an `update` call is necessary to populate the keystream."""
        return self.ks

    def seed_done(self) -> bool:
        """Returns true if the seeding procedure has been completed."""
        return self.seed_rounds == self.seed_counter

    @staticmethod
    def _int_to_regs(val: int, cipher_type: CipherType) -> Tuple[int, ...]:
        """Convert a little-endian integer (bit j = state[j]) to a register
        tuple using reversed-bit storage: bit (N-1-j) of reg = state[j]."""
        reg1 = sum(((val >> j) & 1) << (92 - j) for j in range(93))
        reg2 = sum(((val >> (93 + j)) & 1) << (83 - j) for j in range(84))
        if cipher_type == CipherType.TRIVIUM:
            reg3 = sum(((val >> (177 + j)) & 1) << (110 - j) for j in range(111))
            return reg1, reg2, reg3
        return reg1, reg2

    def _inject_partial_seed(self, val: int, start: int, n: int) -> None:
        """Overwrite n state bits at flat offset `start` with the low n bits of val."""
        regs = list(self.state)
        for i in range(n):
            b, pos = (val >> i) & 1, start + i
            if pos < 93:
                k = 92 - pos
                regs[0] = (regs[0] & ~(1 << k)) | (b << k)
            elif pos < 177:
                k = 83 - (pos - 93)
                regs[1] = (regs[1] & ~(1 << k)) | (b << k)
            else:
                k = 110 - (pos - 177)
                regs[2] = (regs[2] & ~(1 << k)) | (b << k)
        self.state = tuple(regs)

    def _update(self, *regs: int) -> Tuple[int, ...]:
        """Advance the state by output_width cycles using integer arithmetic.
        Updates self.ks and returns the new register state tuple."""
        w = self.output_width
        ks_int = 0
        processed = 0
        mask93 = (1 << 93) - 1
        mask84 = (1 << 84) - 1
        new_state: Tuple[int, ...]

        if self.cipher_type == CipherType.TRIVIUM:
            reg1, reg2, reg3 = regs
            mask111 = (1 << 111) - 1
            while processed < w:
                chunk = min(w - processed, 64)
                mask = (1 << chunk) - 1
                v65 = (reg1 >> 27) & mask
                v68 = (reg1 >> 24) & mask
                v90 = (reg1 >> 2) & mask
                v91 = (reg1 >> 1) & mask
                v92 = reg1 & mask

                v161 = (reg2 >> 15) & mask
                v170 = (reg2 >> 6) & mask
                v174 = (reg2 >> 2) & mask
                v175 = (reg2 >> 1) & mask
                v176 = reg2 & mask

                v242 = (reg3 >> 45) & mask
                v263 = (reg3 >> 24) & mask
                v285 = (reg3 >> 2) & mask
                v286 = (reg3 >> 1) & mask
                v287 = reg3 & mask

                t0 = (v68 ^ (v285 & v286) ^ v242 ^ v287) & mask
                t1 = (v170 ^ (v65 ^ v92) ^ (v90 & v91)) & mask
                t2 = (v263 ^ (v174 & v175) ^ v161 ^ v176) & mask

                ks_int |= ((v65 ^ v92 ^ v161 ^ v176 ^ v242 ^ v287) & mask) << processed
                reg1 = ((reg1 >> chunk) | (t0 << (93 - chunk))) & mask93
                reg2 = ((reg2 >> chunk) | (t1 << (84 - chunk))) & mask84
                reg3 = ((reg3 >> chunk) | (t2 << (111 - chunk))) & mask111
                processed += chunk
            new_state = (reg1, reg2, reg3)
        else:
            reg1, reg2 = regs
            while processed < w:
                chunk = min(w - processed, 64)
                mask = (1 << chunk) - 1
                v65 = (reg1 >> 27) & mask
                v68 = (reg1 >> 24) & mask
                v90 = (reg1 >> 2) & mask
                v91 = (reg1 >> 1) & mask
                v92 = reg1 & mask

                v161 = (reg2 >> 15) & mask
                v170 = (reg2 >> 6) & mask
                v174 = (reg2 >> 2) & mask
                v175 = (reg2 >> 1) & mask
                v176 = reg2 & mask

                t0 = (v68 ^ (v174 & v175) ^ v161 ^ v176) & mask
                t1 = (v170 ^ (v65 ^ v92) ^ (v90 & v91)) & mask

                ks_int |= ((v65 ^ v92 ^ v161 ^ v176) & mask) << processed
                reg1 = ((reg1 >> chunk) | (t0 << (93 - chunk))) & mask93
                reg2 = ((reg2 >> chunk) | (t1 << (84 - chunk))) & mask84
                processed += chunk
            new_state = (reg1, reg2)

        self.ks = ks_int
        return new_state


_OUTPUT_WIDTH = 64


def check_keystream(trivium: Trivium, reference: int) -> None:
    """Draw keystream bits and compare them against a test vector."""
    assert trivium.seed_done()

    # Draw (_OUTPUT_WIDTH / 8)-many `_OUTPUT_WIDTH`-size words from the cipher.
    ks_int = 0
    for i in range(_OUTPUT_WIDTH >> 3):
        trivium.update()
        trivium.step()
        ks_int |= trivium.keystream() << (i * _OUTPUT_WIDTH)

    assert ks_int == reference


if __name__ == "__main__":
    # Key-IV seed:
    #
    # Use the first key-iv test vector of the AVR cryptolib Trivium
    # implementation and generate 512 bits of keystream.

    # AVR cryptolib: Set 1, vector 0
    # Bytewise in little endian order
    stream_str = """
38EB86FF730D7A9CAF8DF13A4420540D
BB7B651464C87501552041C249F29A64
D2FBF515610921EBE06C8F92CECF7F80
98FF20CCCC6A62B97BE8EF7454FC80F9""".replace("\n", "")
    stream = int.from_bytes(bytes.fromhex(stream_str), 'little')

    trivium = Trivium(CipherType.TRIVIUM, SeedType.KEY_IV, _OUTPUT_WIDTH)

    # KEY_IV seed: key in bits [0, 80), IV in bits [80, 160).
    key_iv_seed = 0x01000000000000000000  # key=0x010...0, IV=0

    # Reseed twice.
    for _ in range(2):
        trivium.seed(key_iv_seed)
        trivium.step()

        while not trivium.seed_done():
            trivium.update()
            trivium.step()

        check_keystream(trivium, stream)

    # Full state seed:
    #
    # Use the state after the init rounds of the first test as a full state seed.

    trivium = Trivium(CipherType.TRIVIUM, SeedType.STATE_FULL, _OUTPUT_WIDTH)

    # Reseed twice.
    for _ in range(2):
        trivium.seed(
            0xC7D7C89BCC06725B3D94718106F2A0656422AF1FA457B81F0D2516A9D565893A64C1E50E
        )
        trivium.step()

        check_keystream(trivium, stream)

    # Partial state seed
    #
    # Use the state after the init rounds of the first test as a partial state seed.

    seeds = [
        0x64C1E50E, 0xD565893A, 0x0D2516A9, 0xA457B81F, 0x6422AF1F,
        0x06F2A065, 0x3D947181, 0xCC06725B, 0xC7D7C89B,
    ]

    trivium = Trivium(CipherType.TRIVIUM, SeedType.STATE_PARTIAL, _OUTPUT_WIDTH)

    # Reseed twice.
    for _ in range(2):
        # Need ceil(288/32) seed calls to fill every bit of the state.
        for s in seeds:
            trivium.seed(s)
            trivium.step()

        check_keystream(trivium, stream)
