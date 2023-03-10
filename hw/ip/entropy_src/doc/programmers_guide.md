# Programmer's Guide

## Initialization

To initialize the ENTROPY_SRC block, see the Device Interface Functions (DIFs) section.


## Entropy Processing

Once entropy has been prepared for delivery, it can be consumed by either hardware (CSRNG block hardware instance) or by a software interface (CSRNG software instance).

Note that when software makes frequent re-seed requests to CSRNG, any stored up entropy seeds in the final entropy FIFO will quickly consumed.
Once the FIFO is empty, subsequent entropy seed requests will have to wait the worst case latency time while new entropy is being created.


## Entropy Source Module Disable

A useful feature for the ENTROPY_SRC block is the ability to disable it in a graceful matter.
Since there exists another feature to avoid power spikes between ENTROPY_SRC and CSRNG, software needs to monitor the disabling process.
Bit 16 in the [`DEBUG_STATUS`](../data/entropy_src.hjson#debug_status) should be polled after the ENTROPY_SRC enable bits are cleared in the [`CONF`](../data/entropy_src.hjson#conf) register.
After the handshakes with CSRNG are finished, the above bit should be set and the ENTROPY_SRC block can be safely enabled again.

ENTROPY_SRC may only be disabled if CSRNG is disabled.


## Error conditions

Need to alert the system of a FIFO overflow condition.

## Device Interface Functions (DIFs)

- [Device Interface Functions](../../../../sw/device/lib/dif/dif_entropy_src.h)

## Register Table

* [Register Table](../data/entropy_src.hjson#registers)
