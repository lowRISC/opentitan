#! /usr/bin/env python3

import argparse
import random

CURVE = 'ECDSA-P256'
KEY_SIZE = 256
SEED_SIZE = 320
CURVE_ORDER = 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

def key_from_seed(seed0, seed1):
    '''Mimics the behavior of the secret-key derivation algorithm.'''
    # The modulus is the curve order (n) shifted by the number of extra bits in
    # the seed compared to the key.
    mod = CURVE_ORDER << (SEED_SIZE - KEY_SIZE)
    # The computation of d0 is more complex in the masked version, but here we
    # can simply combine shares and compute based on the real seed.
    d0 = ((seed0 ^ seed1) - seed1) % mod
    d1 = seed1 % mod
    return d0, d1


def seed_size_int_from_arg(seed):
    '''Parses the input argument into a valid SEED_SIZE-bit number.

    If `seed` is None, generates a random number. If `seed` is out of the range
    [0, 2^SEED_SIZE), prints a warning and reduces modulo (2^SEED_SIZE).
    '''
    if seed is None:
        seed = random.randrange(1 << SEED_SIZE)
    elif int.bit_length(seed) > SEED_SIZE:
        seed = seed & ((1 << SEED_SIZE) - 1)
        print(f'WARNING: seed is too large. Reducing to {SEED_SIZE} bits.')
    return seed

def print_int(name, value, nbits):
    '''Prints an integer with `nbits` bits in hexadecimal form.'''
    # Size of the number in hex is 2 characters for the `0x` prefix plus the
    # number of nibbles (size / 4 rounded up).
    length = ((nbits + 3) // 4) + 2
    print('{name}={value:#0{length}x}'
          .format(name=name, value=value, length=length))

if __name__ == "__main__":
    parser = argparse.ArgumentParser(
            description=('Mimics the behavior of an OTBN routine '
                         'that derives a private key from a seed '
                         f'for {CURVE}.'))
    parser.add_argument('-s',
                        '--seed',
                        type=int,
                        required=False,
                        help=f'Real seed value ({SEED_SIZE} bits).')
    parser.add_argument('-m',
                        '--mask',
                        type=int,
                        required=False,
                        help=f'Mask value for seed ({SEED_SIZE} bits).')
    args = parser.parse_args()

    # Size for seed print formatting
    seed_print_size = (SEED_SIZE // 4) + 2

    seed = seed_size_int_from_arg(args.seed)
    mask = seed_size_int_from_arg(args.mask)
    print_int('seed', seed, SEED_SIZE)
    print_int('mask', mask, SEED_SIZE)

    # Generate the two shares for the seed.
    seed0 = seed ^ mask
    seed1 = mask
    print_int('seed0', seed0, SEED_SIZE)
    print_int('seed1', seed1, SEED_SIZE)

    # Compute the shares for the resulting key.
    d0, d1 = key_from_seed(seed0, seed1)
    print_int('d0', d0, SEED_SIZE)
    print_int('d1', d1, SEED_SIZE)

    # Compute the real key.
    d = (d0 + d1) % CURVE_ORDER
    print_int('d', d, KEY_SIZE)
