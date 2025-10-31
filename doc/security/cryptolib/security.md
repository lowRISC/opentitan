# OpenTitan Cryptography Library Security Hardening
The library uses a mix of hardware- and software-based countermeasures that aim to mitigate side-channel and fault injection attacks.
For the hardware-based countermeasures, please refer to the documentation of the corresponding IP block.
The software-based countermeasures are listed below:

## Common Countermeasures
Common software-based countermeasures include:

| Countermeasure                                     | Threat Addressed | Description                                                                                                                                                       |
| -------------------------------------------------- | ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Randomized read / write order of sensitive buffers | SCA              | Avoid leaking sensitive values when reading/writing from/to the memory or other IP blocks by randomizing the order. Done using the `hardened_memcpy()` function.  |
| Initialize sensitive buffers with random data      | SCA              | Avoid leaking sensitive values. Done using the `hardened_memshred()` function to avoid leaking values upon writing.                                               |
| Randomized memory compare                          | SCA              | Avoid leaking sensitive values when comparing two buffers by randomizing the comparison order. Done using the `hardened_memcmp()` function.                       |
| Randomized XOR                                     | SCA              | Avoid leaking sensitive values when XORing two buffers by randomizing the order and using randomness. Done using the `hardened_xor()` function.                   |
| If condition hardening                             | FI               | After a security-critical `if` condition, check the condition again using the `HARDENED_CHECK_*` macro.                                                           |
| Switch case hardening                              | FI               | After a security-critical `switch case`, check whether we actually executed the expected `case` statement using the `HARDENED_CHECK_*` macro.                     |
| For loop hardening                                 | FI               | After a `for` loop, check if we have reached the expected number of iterations using the `HARDENED_CHECK_*` macro.                                                |
| Control-flow integrity for function calls          | FI               | Enclosure security-critical function calls in `HARDENED_TRY` macros that check if we got the expected return code.                                                |
| Key integrity check                                | FI               | The integrity of a key passed into the library is checked on the entrance as well as after using the key.                                                         |
| IP configuration read back                         | FI               | Security-sensitive IP configurations are read back from the IP after a write.                                                                                     |

## Common OTBN Countermeasures
Common software-based countermeasures include:

| Countermeasure                                     | Threat Addressed | Description                                                                                                                                                       |
| -------------------------------------------------- | ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Instruction count check                            | FI               | For constant time OTBN applications, check whether the instruction counter read back from OTBN matches the expectation.                                           |
| Instruction memory integrity checksum              | FI               | After writing an OTBN application into IMEM, check whether the load integrity checksum read back from OTBN matches the expectation.                               |
| Data memory integrity checksum                     | FI               | After writing data into DMEM, check whether the load integrity checksum read back from OTBN matches the expectation.                                              |
| For loop hardening when writing into DMEM          | FI               | After executing the loop that writes data into DMEM, check if we have reached the expected number of iterations using the `HARDENED_CHECK_*` macro.               |
| Randomized write order                             | SCA              | Randomize the write order of all data that is written into DMEM to avoid leaking sensitive values.                                                                |

## Algorithm Specific Countermeasures

### AES

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of the AES, a decrypt-after-encrypt or encrypt-after-decrypt strategy is used.

### AES-GCM

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of AES-GCM, a decrypt-after-encrypt or encrypt-after-decrypt strategy is used.
- Masking is offered for the GHASH computation to thwart side-channel attacks.

### ECC

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of ECDSA, a verify-after-sign strategy is used.
  The secret key is additively masked and the modular arithmetic operations modulo the point order to compute s are masked.
- P256:
  - Uses a constant-time square and multiply always algorithm processing an additively shared scalar.
  - Scalars (both ephemeral and secret keys) are additionally always blinded using a 64b multiple of the curve order.
  - For ECDH and key generation from a HW-backed seed, scalars are blinded using a 65b random multiple of the point order (as per [Schindler and Wiemers](https://csrc.nist.gov/csrc/media/events/workshop-on-elliptic-curve-cryptography-standards/documents/papers/session6-schindler-werner.pdf)).
  - The exponentiation operates on projective coordinates with re-randomisation of the used additive points P and 2P on every iteration.
  - Processing of the masked and blinded scalar is hardened against SCA leakage.
  - We check if input points and results of EC scalar multiplications satisfy the curve equation.
  - The base point and curve parameters are protected against manipulation though the CRC check upon loading the OTBN app.
- P384 uses the same countermeasures with a blinding factor of 194b instead of 65b.

### HMAC

The following software-based countermeasures are implemented:
- The HMAC operation is executed twice to mitigate fault injection attacks.
- Shuffling is implemented for the hashing of the key to protect against side-channel analysis attacks.

### RSA
Modular exponentiation is the core operation for both RSA encryption/sign and key generation.
It is implemented as a constant-time Montgomery Ladder with Boolean-masked exponents and blinded message as detailed in the following works:

- https://eprint.iacr.org/2018/1226.pdf
- https://dl.acm.org/doi/10.1145/1873548.1873556

The combination of both countermeasures results in an exponentiation that is resistant against vertical and horizontal power analysis.
This hardened exponentiation is reused in the primality check routine of the key generation algorithm rendering it equally hardened.
The key generation hardening only applies to [otcrypto_rsa_keygen](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto/include/rsa.h#L100) and not [otcrypto_rsa_keypair_from_cofactor](https://github.com/lowRISC/opentitan/tree/master/sw/device/lib/crypto/include/rsa.h#L155).
