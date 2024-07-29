# Theory of Operation

## Block Diagram

![HMAC Block Diagram](../doc/hmac_block_diagram.svg)

The HMAC block diagram above shows that the HMAC core converts the secret key registers into an inner padded key and an outer padded key which are fed to the SHA-2 hash engine (which is a SHA-2 engine primitive instantiated with the multi-mode feature enabled) when appropriate.
The module also feeds the result of the first round message (which uses the inner padded key) from the SHA-2 hash engine into the 32x32b message FIFO for the second round (which uses the outer padded key).
The message length is automatically updated to reflect the size of the outer padded key and first round digest result for the second round.
See [Design Details](#design-details) for more information.

![SHA-2 Block Diagram](../doc/sha2_block_diagram.svg)

[sha256-spec]: https://csrc.nist.gov/publications/detail/fips/180/4/final

The SHA-2 engine block diagram shows the message scheduling FIFO array, hash registers, digest registers, and SHA-2 compression function inside SHA-2 engine.
The message scheduling FIFO is not software accessible but is fed from the 32x32b message FIFO seen in the HMAC block diagram via the HMAC core.
The HMAC core can forward the message directly from the 32x32b message FIFO if HMAC is not enabled.
The message words are padded with the message length appended to fit either the 512-bit or 1024-bit block size (depending on the configured digest size) as described in the [SHA-256
specification][sha256-spec].

With the 512-bit block (for SHA-2 256), the compression function runs 64 rounds to calculate the block hash, which is stored in the hash registers above.
After 64 rounds are completed, the SHA-2 256 updates the digest registers with the addition of the hash result and the previous digest registers.
With the 1024-bit block (for SHA-2 384/512), the compression function runs 80 rounds instead.
SHA-2 384 is a truncated version of SHA-2 512 where the last 128 bits of the final digest output are truncated to reduce the digest size to 384 bits.


## Design Details

### SHA-2 message feed and pad

A message is fed via a memory-mapped message FIFO.
Any write access to the memory-mapped window [`MSG_FIFO`](registers.md#msg_fifo) updates the message FIFO.
If the FIFO is full, the HMAC block will block any writes leading to back-pressure on the interconnect (as opposed to dropping those writes or overwriting existing FIFO contents).
It is recommended to avoid this back-pressure by not writing to the memory-mapped message FIFO when it is full.
To avoid doing so, software can read the [`STATUS.fifo_full`](registers.md#status) register.

The logic assumes the input message is little-endian.
It converts the byte order of the word right before writing to SHA-2 storage as SHA-2 treats the incoming message as big-endian.
If SW wants to convert the message byte order, SW should set [`CFG.endian_swap`](registers.md#cfg) to **1**.
The byte order of the digest registers, from [`DIGEST_0-DIGEST_15`](registers.md#digest) can be configured with [`CFG.digest_swap`](registers.md#cfg--digest_swap).

See the table below:

```
Input Msg #0: 010203h
Input Msg #1: 0405h
```

endian_swap     | 0         | 1
----------------|-----------|-----------
Push to SHA2 #0 | 03020105h | 01020304h
Push to SHA2 #1 | 00000004h | 00000005h


Small writes to [`MSG_FIFO`](registers.md#msg_fifo) are coalesced into 32-bit words by the [packer logic]({{< relref "hw/ip/prim/doc/prim_packer" >}}).
These words are fed into the internal message scheduling FIFO.
While passing writes to the packer logic, the block also counts the number of bytes that are being passed.
This computes the received message length, which is used in the HMAC and SHA-2 hash computation logic.

The SHA-2 engine computes an intermediate hash for every 512-bit or 1024-bit block depending on the configured digest size.
The message must be padded to fill the 512/1024-bit blocks.
This is done with an initial **1** bit after the actual message bits, followed by enough **0** padding bits, and then the 64/128-bit message length at the end of the block.
The number of **0** padding bits should be enough such that the full block size (512 or 1024 bits) is achieved.
The [SHA-256 specification][sha256-spec] describes this in more detail.
An example is shown below.
The padding logic handles this so software only needs to write the actual message bits into the message FIFO.

![SHA-2 Message Padding](../doc/message_padding.svg)

For example, for SHA-2 256, if the message is empty, the message length is 64-bit 0.
In this case, the padding logic gives `0x80000000` into the SHA-2 module first.
Then it sends (512 - 32 - 64)/32, 13 times of `0x00000000` for Padding `0x00`.
Lastly, it returns the message length which is 64-bit `0x00000000_00000000`.
If incomplete words are written, the packet logic appends `0x80` in the proper byte
location, such as `0xXX800000` for the message length % 4B == 1 case.
This similarly occurs for SHA-2 384/512 but with a 128-bit message length and block size of 1024 bits.

### SHA-2 computation

For SHA-2 256, the SHA-2 engine receives 16 32-bit words from the message FIFO or the HMAC core, which get padded into 16 64-bit words for the SHA-2 engine (upper 32 bits of each data word are all-zero padded), and then begin 64 rounds of the hash computation which is also called *compression*.
Alternatively for SHA-2 384/512, the SHA-2 engine receives 32 32-bit words from message FIFO, which get packed into 16 64-bit words for the SHA-2 engine, and then begin the 80 compression rounds.
In each round, the compression function fetches a 64-bit word from the buffer and computes the internal variables.
The first 16 rounds are fed by the words from the message FIFO or the HMAC core.
Input for later rounds comes from shuffling the given 512/1024-bit block.
Details are well described in [Wikipedia][sha2-wikipedia] and the [SHA-256 specification][sha256-spec].

[sha2-wikipedia]: https://en.wikipedia.org/wiki/SHA-2

With the given hash values, 4-byte (or 8-byte) message word, and round constants, the compression function computes the next round hash values.
The round constants for the different digest sizes are hard-wired in the design.
After the compression at the last round is finished, the resulting hash values are added into the digest.
The digest, again, is used as initial hash values for the next block compression.
During the compression rounds, it doesn't fetch data from the message FIFO.
The software can push up to 16 (or 32 for SHA-2 384/512) entries to the FIFO for the next hash computation.

### HMAC computation

![Two steps of HMAC](../doc/hmac_dataflow.svg)

HMAC can be used with any hash algorithm but this version of HMAC IP uses SHA-2 256/384/512.
The first phase of HMAC calculates the SHA-2 hash of the inner secret key concatenated with the actual message to be authenticated.
This inner secret key is created with the 128/256/384/512/1024-bit (hashed) secret key (depending on the configured key length) and `0x36` padding to complete the corresponding block size of the configured digest size.
For example, for SHA-2 256 with 256-bit key, 512-bit inner secret key is created with the 256-bit secret key with 256-bit zero padding, XORed with 64{`0x36`}.

```verilog
    inner_pad_key = {key[255:0], 256'h0} ^ {64{8'h36}} // big-endian
```

The message length used in the SHA-2 module is calculated by the HMAC core by adding the block size to the original message length (to account for the length of `inner_pad_key`, which has been prepended to the message).

The first round digest is fed into the second round in HMAC.
The second round computes the hash of the outer secret key concatenated with the first round digest.
In case of SHA-2 256 with 256-bit key, as the digest result is 256-bit, it must be zero-padded to fit into 512-bit block size.

```verilog
    outer_pad_key = {key[255:0], 256'h0} ^ {64{8'h5c}} // big-endian
```

In the second round, the message length is a fixed 768 bits (512-bit size of outer secret key + 256-bit first round digest size).

HMAC supports a secret key of length 128/256/384/512/1024-bit, so long as the key length does not exceed the block size of the configured digest, i.e., for SHA-2 256 a maximum length of 512-bit key is supported.
The byte order of the key registers is big-endian by default, can be swapped to little endian by setting [`CFG.key_swap`](registers.md#cfg--key_swap) to 1.
To support any arbitrary key length, the software should configure the HMAC to the next largest supported key length, e.g. for an 80-bit key, HMAC should be configured with an 128-bit key length and fed with the 80-bit key.
It is also up to the software to shrink the key to the supported key length (up to 512-bit for SHA-2 256 and up to 1024-bit for SHA-2 384/512) using a hash function when setting up the HMAC.
For example, common key sizes may be 2048-bit or 4096-bit.
Software is expected to hash these into the supported key length and write the hashed result as the configured key to the HMAC IP.

### Performance in SHA-2 mode and HMAC mode

The SHA-2 256 hash algorithm computes 512 bits of data at a time.
The first 16 rounds need the actual 16 x 32-bit message and the following 48 rounds need some value derived from the message.

In these 48 rounds, the software can feed the next 16 x 32-bit message block.
But, once the FIFO gets full, the software cannot push more data until the current block is processed.
This version of the IP fetches the next 16 x 32-bit message into the internal message scheduling array only after completing the current block.
As such, it takes 80 cycles to complete a block.
The effective throughput considering this is `64 byte / 80 clk` or `16 clk / 80 clk`, 20% of the maximum throughput.
For instance, if the clock frequency is 100MHz, the SHA-2 256 can hash out 80MB/s at most.

For SHA-2 384/512, the algorithm computes 1024 bits of data a time and runs for 80 rounds where the first 16 rounds consume the actual 16 x 64-bit message.
It takes 96 cycles to complete a 1024-bit block. If the clock frequency is 100MHz, the SHA-2 384/512 can hash out 133MB/s at most.

This throughput could be enhanced in a future version by feeding the message into the internal buffer when the round hits 48, eliminating the extra 16 cycles to feed the message after completing a block.

If HMAC mode is turned on, it introduces extra latency due to the second round of computing the final hash of the outer key and the result of the first round using the inner key.
This adds an extra 240 cycles (80 for the inner key, 80 for the outer key, and 80 for the result of the first round) to complete a HMAC SHA-2 256 digest of a message.
For instance, if an empty message is given then it takes 360 cycles (80 for msg itself and 240 for the extra) to get the HMAC authentication token.

### MSG_FIFO

The MSG_FIFO in the HMAC IP has a wide address range not just one 4 byte address.
Any writes to the address range go into the single entry point of the `prim_packer`.
Then `prim_packer` compacts the data into the word-size if not a word-write then writes to the MSG_FIFO.
This is different from a conventional memory-mapped FIFO.

By having wide address range pointing to a single entry point, the FIFO can free software from the fixed address restriction.
For instance, the core can use "store multiple" commands to feed the message fifo efficiently.
Also, a DMA engine which might not have the ability to be configured to the fixed write and incremental read may benefit from this behavior.
