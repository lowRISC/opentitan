# Theory of Operation

## Block Diagram

![HMAC Block Diagram](../doc/hmac_block_diagram.svg)

The HMAC block diagram above shows that the HMAC core converts the secret key
registers into an inner padded key and an outer padded key which are fed to the
hash engine when appropriate. The module also feeds the result of the first
round message (which uses the inner padded key) from the SHA-256 hash engine
into the 16x32b FIFO for the second round (which uses the outer padded key).
The message length is automatically updated to reflect the size of the outer
padded key and first round digest result for the second round. See [Design
Details](#design-details) for more information.

![SHA-256 Block Diagram](../doc/sha2_block_diagram.svg)

The SHA-256 (SHA-2) block diagram shows the message FIFO inside SHA-256, hash
registers, digest registers, and SHA-256 compression function. The message FIFO
is not software accessible but is fed from the 16x32b FIFO seen in the HMAC
block diagram via the HMAC core. The HMAC core can forward the message directly
from the 16x32b FIFO if HMAC is not enabled. This message is padded with length
appended to fit the 512-bit block size as described in the [SHA-256
specification][sha256-spec].

With the 512-bit block, the compress function runs 64 rounds to calculate the
block hash, which is stored in the hash registers above. After 64 rounds are
completed, the SHA-256 updates the digest registers with the addition of the
hash result and the previous digest registers.

## Design Details

### SHA-256 message feed and pad

A message is fed via a memory-mapped message FIFO. Any write access to the
memory-mapped window [`MSG_FIFO`](registers.md#msg_fifo) updates the message FIFO. If the FIFO is full,
the HMAC block will block any writes leading to back-pressure on the
interconnect (as opposed to dropping those writes or overwriting existing FIFO
contents). It is recommended this back-pressure is avoided by not writing to the
memory-mapped message FIFO when it is full. To avoid doing so, software can
read the [`STATUS.fifo_full`](registers.md#status) register.

The logic assumes the input message is little-endian.
It converts the byte order of the word right before writing to SHA2 storage as SHA2 treats the incoming message as big-endian.
If SW wants to convert the message byte order, SW should set [`CFG.endian_swap`](registers.md#cfg) to **1**.
The byte order of the digest registers, from [`DIGEST_0`](registers.md#digest) to [`DIGEST_7`](registers.md#digest) can be configured with [`CFG.digest_swap`](registers.md#cfg).

See the table below:

```
Input Msg #0: 010203h
Input Msg #1: 0405h
```

endian_swap     | 0         | 1
----------------|-----------|-----------
Push to SHA2 #0 | 03020105h | 01020304h
Push to SHA2 #1 | 00000004h | 00000005h


Small writes to [`MSG_FIFO`](registers.md#msg_fifo) are coalesced with into 32-bit words by the [packer logic]({{< relref "hw/ip/prim/doc/prim_packer" >}}).
These words are fed into the internal message FIFO.
While passing writes to the packer logic, the block also counts the number of bytes that are being passed.
This gives the received message length, which is used in HMAC and SHA-256 as part of the hash computation.

The SHA-256 module computes an intermediate hash for every 512-bit block.
The message must be padded to fill 512-bit blocks. This is done with an initial
**1** bit after the message bits with a 64-bit message length at the end and
enough **0** bits in the middle to result in a full block.The [SHA-256
specification][sha256-spec] describes this in more detail. An example is shown
below. The padding logic handles this so software only needs to write the actual
message bits into the FIFO.

![SHA-256 Message Padding](../doc/message_padding.svg)

For instance, if the message is empty, the message length is 64-bit 0. In this
case, the padding logic gives `0x80000000` into the SHA-256 module first. Then
it sends (512 - 32 - 64)/32, 13 times of `0x00000000` for Padding `0x00`.
Lastly, it returns the message length which is 64-bit `0x00000000_00000000`. If
incomplete words are written, the packet logic appends `0x80` in the proper byte
location.  Such as `0xXX800000` for the message length % 4B == 1 case.

### SHA-256 computation

The SHA-256 engine receives 16 32-bit words from the message FIFO or the HMAC
core then begins 64 rounds of the hash computation which is also called
*compression*. In each round, the compression function fetches 32 bits from the
buffer and computes the internal variables. The first 16 rounds are fed by the
words from the message FIFO or the HMAC core. Input for later rounds comes from
shuffling the given 512-bit block. Details are well described in
[Wikipedia][sha2-wikipedia] and the [SHA-256 specification][sha256-spec].

[sha2-wikipedia]: https://en.wikipedia.org/wiki/SHA-2

With the given hash values, 4 byte message, and round constants, the compression
function computes the next round hash values. The 64 32-bit round constants
are hard-wired in the design. After the compression at the last round is
finished, the resulting hash values are added into the digest. The digest, again,
is used as initial hash values for the next 512-bit block compression. During
the compression rounds, it doesn't fetch data from the message FIFO. The
software can push up to 16 entries to the FIFO for the next hash computation.

### HMAC computation

![Two steps of HMAC](../doc/hmac_dataflow.svg)

HMAC can be used with any hash algorithm but this version of HMAC IP only uses
SHA-256. The first phase of HMAC calculates the SHA-256 hash of the inner
secret key concatenated with the actual message to be authenticated. This inner
secret key is created with a 256-bit (hashed) secret key and `0x36` pad.

```verilog
    inner_pad_key = {key[255:0], 256'h0} ^ {64{8'h36}} // big-endian
```

The message length used in the SHA-256 module is calculated by the HMAC core by
adding 512 to the original message length (to account for the length of
`inner_pad_key`, which has been prepended to the message).

The first round digest is fed into the second round in HMAC. The second round
computes the hash of the outer secret key concatenated with the first round
digest. As the result of SHA-256 is 256-bits, it must be padded to fit into
512-bit block size.

```verilog
    outer_pad_key = {key[255:0], 256'h0} ^ {64{8'h5c}} // big-endian
```

In the second round, the message length is a fixed 768 bits.

HMAC assumes the secret key is 256-bit. The onus is on software to shrink the
key to 256-bit using a hash function when setting up the HMAC. For example,
common key sizes may be 2048-bit or 4096-bit. Software must hash these and
write the hashed results to the HMAC.

### Performance in SHA-256 mode and HMAC mode

The SHA-256 hash algorithm computes 512 bits of data at a time. The first 16
rounds need the actual 16 x 32-bit message and the following 48 rounds need
some value derived from the message.

In these 48 rounds, the software can feed the next 16 x 32-bit message block.
But, once the FIFO is full, the software cannot push more data until the
current block is processed. This version of the IP fetches the next 16 x 32-bit
message after completing the current block. As such, it takes 80 cycles to
complete a block. The effective throughput considering this is `64 byte / 80
clk` or `16 clk / 80 clk`, 20% of the maximum throughput. For instance, if the
clock frequency is 100MHz, the SHA-256 can hash out 80MB/s at most.

This throughput could be enhanced in a future version by feeding the message
into the internal buffer when the round hits 48, eliminating the extra 16
cycles to feed the message after completing a block.

If HMAC mode is turned on, it introduces extra latency due to the second round
of computing the final hash of the outer key and the result of the first round
using the inner key. This adds an extra 240 cycles (80 for the inner key, 80
for the outer key, and 80 for the result of the first round) to complete a
message. For instance, if an empty message is given then it takes 360 cycles
(80 for msg itself and 240 for the extra) to get the HMAC authentication token.

### MSG_FIFO

The MSG_FIFO in the HMAC IP has a wide address range not just one 4 byte address.
Any writes to the address range go into the single entry point of the `prim_packer`.
Then `prim_packer` compacts the data into the word-size if not a word-write then writes to the MSG_FIFO.
This is different from a conventional memory-mapped FIFO.

By having wide address range pointing to a single entry point, the FIFO can free software from the fixed address restriction.
For instance, the core can use "store multiple" commands to feed the message fifo efficiently.
Also, a DMA engine which might not have the ability to be configured to the fixed write and incremental read may benefit from this behavior.
