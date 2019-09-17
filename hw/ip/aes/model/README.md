AES Model
=========

This directory contains a basic C model of the AES unit targeting functional
verfication of the AES unit during the design phase as well as later design
verification.

Besides the actual model, this directory also contains an example application
that:
- Shows how to interface the C model.
- Allows printing of intermediate results for debugging.
- Checks the output of the model versus the exptected results.
- Checks the output of the model versus the output of the BoringSSL/OpenSSL
  library.

How to build and run the example
--------------------------------

Open the makefile and update the variable BORING_SSL_PATH pointing to the
BoringSSL directory on your machine. If make cannot find the crypto library
in that directory, the example is automatically linked to OpenSSL instead
of BoringSSL.

Simply execute

   ```make```

to build the example and

   ```./aes_example KEY_LEN_BYTES```

to run the example. The optional argument KEY_LEN_BYTES determines the key
length in bytes and is either 16, 24, or 32 for AES-128, 192 or 256,
respectively. By default, a key length of 16 Bytes is used (AES-128).

Details of the model
--------------------

- aes.c/h: contains the C model of the AES unit
- crypto.c/h: contains BoringSSL/OpenSSL library interface functions
- aes_example.c/h: contains the example application including test
  input and expected output
