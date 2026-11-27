
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
 | i3c_target_ccc | |                       |   +---------------------+ |
 |                | |---- IBI Arb req ----->|   | i3c_target_trx_ccc  | |
 |                | |                       |   | (submodule if reqd) | |
 |                | |                       |   |                     | |
 +----------------+ |<-- Priv/CCC Wr Data --|   +---------------------+ |
                    |                       |                           |
  ------------------+                       ----------------------------+
  
```

## Read Data and the CDC.

As mentioned earlier, read data is prefetched from the transmission buffers as soon as there is sufficient data available to commence a transfer.
The transceiver logic will thus be informed, by the information passed through the `i3c_sync_data` instance, that a Private Read may be ACKed and transmission commenced.

One complication of this approach is that sometimes it is necessary to Abort tranfers and/or flush out the transmission buffer/descriptor queue for a Virtual Target.
The CDC into the SCL domain cannot therefore be treated as a regular 'reliable data stream'; instead it is necessary to retract the most recently presented datum, and - some time later - replace it with new data (the start of the next Private Read transfer).
This retraction may only be performed at specific times, since retracting does itself require two SCL edges to address metastability issues.
These edges will typically be the SCL signaling of an I3C arbitrable address header and, since the transceiver logic is capable of performing the address matching without assistance, the new state information is then available in time to return the ACK/NACK decision.

This rapid turnaround from address header to ACK/NACK bit is one of the awkward cases that this design must handle, and the same is true of handling CCC read requests (see below).

## Transmission suspension and retraction of data.

Architecturally, retraction of the read data occurs only when transmission from the Virtual Target is suspended, in response to a software-initiated use of the 'data sink' mechanism or clearing of the transmission buffers for that Virtual Target.
For this to be safe, suspended Virtual Targets shall not respond to any Private Read transfers, and instead the transceiver logic shall NACK such transfer requests.

## Common Command Code (CCC) handling.

Broadcasts and Group Addresses support only Write transfers, so these are quite simple to implement, but only enabled Virtual Targets shall be considered, and the traffic shall not be forwarded into the IP clock domain if there are no enabled Virtual Targets.
The transceiver logic is responsible for deciding whether to ACK/NACK the arbitrable address header, so it has been presented with the addresses of all Virtual Targets, their enabled/disabled state, and the configuration of all Group Addresses.

### Handling of Direct Read CCCs.

The initial write phase of the Direct Read/Get CCC shall be forwarded to the IP clock domain, and retained in internal registers.

The restart (Sr) following this write phase or shall be forwarded to the core logic on the IP clock domain, as is the stop (P) at the end of CCC transfer.
In response to any Sr that the core logic receives during a CCC transfer, the ACK/NACK signal and - in the case of an ACK - the first unit of read data shall be presented as prefetched data to the transceiver domain, for _all_ Virtual Targets in parallel using a single CDC primitive.
This keeps the logic simpler and more efficient, and eliminate the possibility of any skew among the Virtual Target responses.

The prefeteched read data will be collected during each non-arbitrable address header within the transfer.
It should be noted that different Virtual Targets may yield different ACK/NACK signals, based upon their current configuration.

When the transceiver logic performs the address matching, it then has the information available to proceed during the short interval between capture of the address and presentation of the ACK/NACK response.
When the transceiver collects this ACK/NACK response, which it does even in the event of an address that matches does not match _any_ of the addresses,
the core logic is informed of the ACK/NACK response that was sent to the Controller.

The core may then decide whether to present additional data, which it does only when the response was an ACK.
This avoids the need to retract any read data during a CCC read phase.
It does not need to know which Virtual Target matched; in effect, all are responding, and dropping out with NACK responses at times appropriate to their current configuration and state.

Receipt of a Sr notification by the core shall cause it to restart this process by rewinding its read index to zero, and once again supplying the first item of read data - along with the ACK/NACK indication - for each Virtual Target.
Obviously this process relies upon read operations having no side-effects on the Virtual Target state.

### Handling of Direct Write CCCs.

Direct Write CCCs do not require the presentation of read data to the transceiver logic, but the requirement to provide an ahead-of-time decision on the ACK/NACK response for each Virtual Target still exists.

Most of the decision logic, yielding an 'ACK/NACK' (or perhaps more descriptive error/status code), may be driven on the IP clock.
Most responses are static and dependent only upon the CCC and DEFB, and what the Target peripheral supports.
Some of the decision logic may be dynamic, driven by the current register configuration, and some of it driven by the current state.
An example of the latter would be whether a given Virtual Target may be subscribed to an additional Group Address, but the group addressing information is already available in the `i3c_target_trx` parent module for the purposes of address matching.

The write data that is received is forwarded to the core logic in the same manner as for the setup write phase of the CCC transfer.

## Start requests.

The most awkward case that the Target peripheral logic must handle is the issuing of a Start Request to the Active Controller, for the purposes of sending an In-Band Interrupt (which may be a Standard Hot-Join Request).
In this circumstance, the bus is idle and there are no edges on the SCL line that may be used, so the Target transceiver logic also is inactive.

The IP block addresses this by commencing the Start Request by pulling the SDA line low within the IP clock domain and responding to the first few SCL transitions there, supplying the initial address bits of the IBI request itself.
Once sufficient SCL clocks have been received, the IBI details will also have travelled through the CDC into the transceiver logic, which starts driving SDA too, allowing the logic on the IP clock domain to back off.

If either party detects an arbitration loss during this arbitrable address header, meaning that it attempted to drive SDA high but observed a low SDA line in response, it shall cease arbitration.
