
# Implementation of Target-side IP <-> SCL traffic.

One of the challenges of driving the Target transceiver logic directly from the I3C SCL signal is the difficulty of receiving information from the IP clock domain (register configuration, software driver etc).
Since the SCL signal changes sporadically and is not a periodic, free-running clock signal, read data must typically be available for collection before the transceiver logic needs it.

Read data is therefore prefetched from the Target transmission buffers and the transceiver logic (`i3c_target_trx`) is able to decide how to respond (ACK/NACK) based on the availabililty or otherwise of suitable read data.

Write data is less problematic and may typically be forwarded into the IP clock domain; the only caveat is that transceiver logic must be presented with information of whether to allow the write transfer to commence, so that it may ACK/NACK the Controller's attempted transfer.
This is particularly true of Private Write traffic where the amount of data being transferred is larger and it must be stored rather than actioned immediately.

```
 -------------------+                       +---------------------------+
 i3c_target_fsm     |                       | i3c_target_trx            |
                    |-----Priv Read Data -->|                 ack/nack  |
                    |                       |      ||            /\     |
 +----------------+ |---- CCC Read Data --->|      \/            ||     |
 | i3c_target_ccc | |                       |   +--------------------+  |
 |                | |---- IBI Arb req ----->|   | i3c_target_trx_ccc |  |
 |                | |                       |   |                    |  |
 |                | |                       |   |                    |  |
 +----------------+ |<-- Priv/CCC Wr Data --|   +--------------------+  |
                    |                       |                           |
  ------------------+                       ----------------------------+
  
```

## Read Data and the CDC.

As mentioned earlier, read data is prefetched from the transmission buffers as soon as there is sufficient data available to commence a transfer.
The transceiver logic will thus be informed, by the information passed through the `i3c_sync_data` instance, that a Private Read may be ACKed and transmission commenced.

One complication of this approach is that sometimes it is necessary to Abort tranfers and/or flush out the transmission buffer/descriptor queue for a Virtual Target.
The CDC into the SCL domain cannot therefore be treated as a regular 'reliable data stream'; instead it is necessary to retract the most recently presented datum, and - some time later - replace it with new data (the start of the next Private Read transfer).
This retraction may only be performed at specific times, since retracting does itself require two SCL edges to address metastability issues.
These edges will typically be the SCL signaling of an I3C address header and, since the transceiver logic is capable of performing the address matching without assistance, the new state information is then available in time to return the ACK/NACK decision.

This rapid turnaround from address header to ACK/NACK bit is one of the awkward cases that this design must handle, but similar situations occur in the handling of CCC traffic.

## Common Command Code (CCC) handling.

To respond sufficiently promptly to the presentation of Direct Read/Write CCC, the validation of the CCC and DEFining Byte (DEFB), if present, cannot be deferred to the IP clock domain.
Instead, the transceiver module contains some combinational logic in a submodule (`i3c_target_trx_ccc`) that vets the CCC and DEFB, such that only acceptable, validated CCC traffic is passed to the IP core (`i3c_target_fsm` and `i3c_target_ccc`).

This does have the unfortunate consequence of distributing across two separate modules the knowledge of which CCCs/DEFBs are supported, but it somewhat simplifies the CCC handling within the IP core.

Most of the decision logic, yielding an 'ACK/NACK' (or perhaps more descriptive error/status code) required in the `i3c_target_trx_ccc` submodule, is static and dependent only upon the CCC and DEFB, and what the Virtual Target supports.
Some of the decision logic may be dynamic, driven by the current register configuration, and some of it driven by the current state.
An example of the latter would be whether a given Virtual Target may be subscribed to an additional Group Address, but the group addressing information is already available in the `i3c_target_trx` parent module for the purposes of address matching.

### CCC Read Data.

Direct Read CCC request are passed from the transceiver logic to the IP core, where they are parsed with the safe assumption of validity and that the CCC/DEFB are recognised and supported.
The appropriate read data - usually direct from the register configuration - is returned via the CDC in preparation for the read phase of the Direct Read CCC.
Read data for all Virtual Targets is supplied because it is not known at this point which - if any - Virtual Target will match the address supplied after the repeated start (Sr).

For simplicity, and to ensure that all of the read data from all Virtual Targets (in practice, this is just 1-4 VTs, and thus channels), is transferred as a single unit across the CDC and _all_ of the read data is consumed simultaneously.
It may therefore be thought of as a single, wide channel of read data, with the transceiver filtering out the required data based upon the matching address.

