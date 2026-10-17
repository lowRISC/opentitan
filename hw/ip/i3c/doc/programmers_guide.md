# Programmer's Guide

## Buffer allocation

The I3C IP block uses a single shared SRAM, the 'message buffer', to implement all of the logical queues and data FIFOs within the design, including both the Controller and the Target sides.

The allocation of this buffer is entirely under software control, and should be determined by which queues and FIFOs are being used, along with their anticipated data rates.
The configuration must be set before enabling either Controller or Target operation.

The hardware provides a default configuration so that the IP block is operable after coming out of reset, even if the configuration has not been modified.
It should, however, be noted that this configuration is conservative and anticipates the heaviest use case with all supported Virtual Targets configured and used; if fewer Virtual Targets are activated, the configuration should be modified to achieve better use of the memory.

The default buffer allocation, with the queues and FIFOs arranged in ascending order of buffer offset (in DWORDs) is shown below:

| Description        | Register              | Min offset (incl). | Max offset (incl). |
|--------------------|-----------------------|--------------------|--------------------|
| Controller Tx Data | CTRL_TXBUF_CONFIG     | 0x00               | 0x7f               |
| Controller Rx Data | CTRL_RXBUF_CONFIG     | 0x80               | 0xff               |
| Command Queue      | COMMAND_QUEUE_CONFIG  | 0x100              | 0x11f              |
| Response Queue     | RESPONSE_QUEUE_CONFIG | 0x120              | 0x12f              |
| IBI Data Queue     | IBI_CONFIG            | 0x130              | 0x1af              |
| IBI Status Descs   | IBI_STAT_CONFIG       | 0x1b0              | 0x1cf              |
| Target 0 Tx Data   | TARG_TXBUF_CONFIG_0   | 0x1d0              | 0x20f              |
| Target 1 Tx Data   | TARG_TXBUF_CONFIG_1   | 0x210              | 0x24f              |
| Target 2 Tx Data   | TARG_TXBUF_CONFIG_2   | 0x250              | 0x28f              |
| Target 3 Tx Data   | TARG_TXBUF_CONFIG_3   | 0x290              | 0x2cf              |
| Target Rx Data     | TARG_RXBUF_CONFIG     | 0x2d0              | 0x36f              |
| Target IBI Data    | TARG_IBI_CONFIG       | 0x370              | 0x3af              |
| Target 0 Tx Descs  | TARG_TXDESC_CONFIG_0  | 0x3b0              | 0x3b7              |
| Target 1 Tx Descs  | TARG_TXDESC_CONFIG_1  | 0x3b8              | 0x3bf              |
| Target 2 Tx Descs  | TARG_TXDESC_CONFIG_2  | 0x3c0              | 0x3c7              |
| Target 3 Tx Descs  | TARG_TXDESC_CONFIG_3  | 0x3c8              | 0x3cf              |
| Target Rx Descs    | TARG_RXDESC_CONFIG    | 0x3d0              | 0x3df              |
| Target IBI StatD   | TARG_IBIDESC_CONFIG   | 0x3e0              | 0x3ef              |
| Target ASync Event | TARG_ASYNC_CONFIG     | 0x3f0              | 0x3ff              |

Each of the queues/FIFOs has a configuration register that specifies the minimum and maximum offsets, in DWORDs, within the message buffer.
Both offsets are inclusive and it is the responsibility of the software to ensure overlaps do not occur because otherwise undefined behavior will result.

## Timer Intervals

The IP block contains a number of timers for measuring the duration of I3C bus states, such as the 'Bus Available' and 'Bus Idle' conditions.
The longest of these time intervals is the 50 ms 'Dead Bus Recovery' interval, whilst the shortest interval is the 'Bus Available' condition at just 1 microsecond.

In order to support this wide variation in time intervals across the large range of supported IP clock frequencies, the timer granularity (in IP clock cycles) varies on a per-timer basis as illustrated by the following tables, at the extremes of the supported clock frequency range.

Minimum supported clock frequency, 50 MHz:

| Timer            | Default Interval | Width (bits) | Shift amount | Unit at 50 MHz | Max interval |
|------------------|-----------------:|-------------:|-------------:|---------------:|-------------:|
| Command Retrying |           800 us |          s.7 |            8 |         5.1 us |       1.5 ms |
| Targ Bus Idle    |           200 us |          s.7 |            6 |         1.3 us |       360 us |
| TE0 Recovery     |            60 us |          s.7 |            4 |         320 ns |       100 us |
| Targ Reset       |             5 us |          s.7 |            0 |          20 ns |       7.5 us |
| Targ Bus Avail   |             1 us |          s.7 |            0 |          20 ns |       3.5 us |
| Read stalled     |           150 us |          s.7 |            6 |         1.3 us |       310 us |
| Ctrl Bus Avail   |             1 us |          s.7 |            0 |          20 ns |       3.5 us |
| Dead Bus Recov   |            50 ms |          s.7 |           14 |         330 us |        92 ms |

Maximum supported clock frequency, 1.5 GHz

| Timer            | Default Interval | Width (bits) | Shift amount | Unit at 1.5 GHz | Max interval |
|------------------|-----------------:|-------------:|-------------:|----------------:|-------------:|
| Command Retrying |           800 us |          s.7 |           13 |          5.5 us |       1.7 ms |
| Targ Bus Idle    |           200 us |          s.7 |           11 |          1.4 us |       370 us |
| TE0 Recovery     |            60 us |          s.7 |            9 |          340 ns |       100 us |
| Targ Reset       |             5 us |          s.7 |            5 |           21 ns |       7.7 us |
| Targ Bus Avail   |             1 us |          s.7 |            5 |           21 ns |       3.7 us |
| Read stalled     |           150 us |          s.7 |           11 |          1.4 us |       320 us |
| Ctrl Bus Avail   |             1 us |          s.7 |            5 |           21 ns |       3.7 us |
| Dead Bus Recov   |            50 ms |          s.7 |           19 |          350 us |        94 ms |

All times are quoted to two significant figures.
It may be seen from the above tables how the shift amount achieves almost exactly the same granularity of timer adjustment despite the large disparity in IP clock frequency.

The timers are independent of each other and share no logic or synchronization beyond the fact that they are all updated by the single IP clock signal.

If the hardware-calculated default interval is found to be inadequate, e.g. in the event of oscillator frequency inaccuracy, an adjustment may be made by software using the appropriate field of `INTERVAL_TIME0` or `INTERVAL_TIME1` as illustrated below.
The adjustment values are reset to 0, meaning that the unmodified default interval is used.

Time intervals are specified as two's complement 8-bit signed offsets added to the default values calculated by the hardware:

 - interval_clks = (hw_default_us * clks_per_us) + (signed_adj << shift)

The shift values, as illustrated in the tables above, are adjusted according to `log2(clks_per_us)` with the result that the adjustment has about the same time range, irrespective of the IP clock frequency.

Clock frequencies:

 - 50 MHz to 64 MHz, both inclusive: base weighting applies and the shift value are as shown in the 50 MHz table above.
 - From 64 MHz (exclusive) to 128 MHz (inclusive): adjustments have twice the base weighting; shifts are increased by 1.
 - From 128 MHz (excl.) to 256 MHz (incl.): adjustments have 4 times the base weighting; shifts are increased by 2...
 - From 256 MHz (excl.) to 512 MHz (incl.): adjustments have 8 times the base weighting.
 - From 512 MHz (excl.) to 1024 MHz (incl.): adjustments have 16 times the base weighting.
 - From 1024 MHz (excl.) to 1500 MHz (incl.): adjustments have 32 times the base weighting; shifts are increased by 5.

# IBI Payload Fetching

A number of I3C Targets are too slow to be able to return data for Private Read transfers at the full SDR0/HDR-DDR signaling speed.

When the Host Controller is issuing a Private Read transfer, the signaling mode/rate is specified in a Command Descriptor, but when fetching the payload data for an In-Band Interrupt, there is no Command Descriptor available so the hardware cannot determine the required signaling speed.

The HCI Specification does, however, allow the specification of a signaling mode for 'Auto-Command' reads (HCI Table 130, `AUTOCMD_MODE` field), so this IP block also uses the value in that field when fetching the IBI payload data.
If that field has been set to HDR-DDR for Auto-Command operation, the IBI Payload of the device will be fetched with SDR0 signaling, since IBIs are not supported in HDR modes.

If a Target is known, through retrieval of its maxRd value (4.3.7.3.18), to be too slow to support SDR0 signaling, the `AUTOCMD_MODE` of its DAT entry should be set to a lower signaling speed before the collection of In-Band Interrupt payloads from that Target is enabled.
