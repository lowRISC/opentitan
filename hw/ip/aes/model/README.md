AES Model & OpenSSL/BoringSSL Interface
=======================================

This directory contains a basic C model of the AES unit's cipher core including
OpenSSL/BoringSSL library interface functions. This infrastructure targets
functional verification of the AES unit during the design phase as well as
actual design verification.

In addition, this directory also contains two example applications.

1. `aes_example`:
- Allows printing of intermediate results for debugging the AES cipher core.
- Shows how to interface the C model and how to use the OpenSSL/BoringSSL
  interface.
- Checks the output of the model versus the expected results.
- Checks the output of the model versus the output of the BoringSSL/OpenSSL
  library.
- Supports ECB mode only.

2. `aes_modes`:
- Shows how to interface the OpenSSL/BoringSSL interface functions.
- Checks the output of BoringSSL/OpenSSL versus expected results.
- Supports ECB, CBC, CTR modes.

How to build and run the examples
---------------------------------

Open the makefile and update the variable BORING_SSL_PATH pointing to the
BoringSSL directory on your machine. If make cannot find the crypto library in
that directory, the example is automatically linked to OpenSSL instead of
BoringSSL.

Simply execute

   ```make```

to build both example applications and

   ```./aes_example KEY_LEN_BYTES```

to run `aes_example`. The optional argument `KEY_LEN_BYTES` determines the key
length in bytes and is either 16, 24, or 32 for AES-128, 192 or 256,
respectively. By default, a key length of 16 Bytes is used (AES-128).

To run the second example, simply type

   ```./aes_modes```

Details of the model
--------------------

- `aes.c/h`: Contains the C model of the AES unit's cipher core.
- `crypto.c/h`: Contains BoringSSL/OpenSSL library interface functions.
- `aes_example.c/h`: Contains the first example application including test input
  and expected output for ECB mode.
- `aes_modes.c/h`: Contains the second example application including test input
  and expected output for ECB, CBC, CTR modes.
