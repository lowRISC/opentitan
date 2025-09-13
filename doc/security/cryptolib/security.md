# OpenTitan Cryptography Library Security Hardening
The library uses a mix of hardware- and software-based countermeasures that aim to mitigate side-channel and fault injection attacks.
For the hardware-based countermeasures, please refer to the documentation of the according IP block.
The software-based countermeasures are listed below:

## Common Countermeasures
Common software-based countermeasures include:

| Countermeasure                                     | Threat Addressed | Description                                                                                                                                                       |
| -------------------------------------------------- | ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Randomized read / write order of sensitive buffers | SCA              | Avoid leaking sensitive values when reading/writing from/to the memory or other IP blocks by randomizingg the order. Done using the `hardened_memcpy()` function. |
| Initialize sensitive buffers with random data      | SCA              | Avoid leaking sensitive values. Done using the `hardened_memshred()` function.                                                                                    |
| Randomized memory compare                          | SCA              | Avoid leaking sensitive values when comparing two buffers by randomizing the comparison order. Done using the `hardened_memcmp()` function.                       |
| Randomized XOR                                     | SCA              | Avoid leaking sensitive values when XORing two buffers by randomizing the order and using randomness. Done using the `hardened_xor()` function.                   |
| If condition hardening                             | FI               | After a security-critical if condition, check the condition again using the `HARDENED_CHECK_*` macro.                                                             |
| Switch case hardening                              | FI               | After a security-critical switch case, check whether we actually executed the expected case statement using the `HARDENED_CHECK_*` macro.                         |
| For loop hardening                                 | FI               | After a for loop check if we have reached the expected number of iterations using the `HARDENED_CHECK_*` macro.                                                   |
| Control-flow integrity for function calls          | FI               | Enclosure security-critical function calls in `HARDENED_TRY` macros that check if we got the expected return code.                                                |
| Key integrity check                                | FI               | The integrity of a key passed into the library is checked on the entrace as well as after using the key.                                                          |
| IP configuration read back                         | FI               | Security-sensitive IP configurations are read back from the IP after a write.                                                                                     |

## Common OTBN Countermeasures
Common software-based countermeasures include:

| Countermeasure                                     | Threat Addressed | Description                                                                                                                                                       |
| -------------------------------------------------- | ---------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Instruction count check                            | FI               | For constant time OTBN applications, check whether the instruction counter read back from OTBN matches the expectation.                                           |
| Instruction memory integrity checksum              | FI               | After writing an OTBN application into IMEM, check whether the load integrity checksum read back from OTBN matches the expectation.                               |
| Data memory integrity checksum                     | FI               | After writing data into DMEM, check whether the load integrity checksum read back from OTBN matches the expectation.                                              |
| For loop hardening when writing into DMEM          | FI               | After executing the loop that writes data into DMEM check if we have reached the expected number of iterations using the `HARDENED_CHECK_*` macro.                |
| Randomized write order                             | SCA              | Randomize the write order of all data that is written into DMEM to avoid leaking sensitive values.                                                                |

## Algorithm Specific Countermeasures

### AES

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of the AES, a decrypt-after-encrypt or encrypt-after-decrypt strategy is used.

### AES-GCM

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of AES-GCM, a decrypt-after-encrypt or encrypt-after-decrypt strategy is used.
- Masking is offered for the GHASH computation to thwart side-channel attacks.

### ECDSA

The following software-based countermeasures are implemented:
- To mitigate fault injection attacks on the execution of ECDSA, a verify-after-sign strategy is used.

### HMAC

The following software-based countermeasures are implemented:
- The HMAC operation is executed twice to mitigate fault injection attacks.
