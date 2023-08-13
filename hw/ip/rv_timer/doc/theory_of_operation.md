# Theory of Operation

## Block Diagram

![Timer Block Diagram](../doc/timer_block_diagram.svg)

The timer module is composed of tick generators, counters, and comparators.
A tick generator creates a tick every time its internal counter hits the
[`CFG0.prescaler`](registers.md#cfg0) value. The tick is used to increment `mtime` by the [`CFG0.step`](registers.md#cfg0)
value. The 64-bit `mtime` value is compared with the 64-bit `mtimecmp`. If
`mtime` is greater than or equal to `mtimecmp`, the timer raises an interrupt.

## Design Details

### Tick Generator

The tick module inside the timer IP is used to generate a fixed period of pulse
signal. This allows creation of a call-clock timer tick such as 1us or 10us
regardless of the system clock period. It is useful if the system has more than
one clock as a clock source. The firmware just needs to adjust the
[`CFG0.prescaler`](registers.md#cfg0) value and the actual timer interrupt handling routine does not
need a variable clock period to update `mtimecmp`.

For instance, if a system switches between 48MHz and 200MHz clocks, a prescaler
value of **47** for 48MHz and **199** for 200MHz will generate a 1us tick.
In this version, the timer only supports a single fixed clock, so the firmware
should change [`CFG0.prescaler`](registers.md#cfg0) appropriately.

### Configurable number of timers and harts

The timer IP supports more than one HART and/or more than one timer per hart.
Each hart has a set of tick generator and counter. It means the timer IP has the
same number of prescalers, steps, and `mtime` registers as the number of harts.

Each hart can have multiple sets of `mtimecmp`, comparator logic, and expire
interrupt signals. This version of the IP is fixed to have one Hart and one
Timer per Hart.

Below is an example configuration file for `N_TIMER` 2 and `N_HARTS` 2.
It has separate interrupts per timer and a set of interrupt enable and state
registers per Hart.

```hjson
{
  // ...
  interrupt_list: [
    { name: "timer_expired_hart0_timer0",
      desc: "raised if hart0's timer0 expired (mtimecmp >= mtime)"
    },
    { name: "timer_expired_hart0_timer1",
      desc: "raised if hart0's timer1 expired (mtimecmp >= mtime)"
    },
    { name: "timer_expired_hart1_timer0",
      desc: "raised if hart1's timer0 expired (mtimecmp >= mtime)"
    },
    { name: "timer_expired_hart1_timer1",
      desc: "raised if hart1's timer1 expired (mtimecmp >= mtime)"
    },
  ],
  //...
  registers: {
    // ...
    { skipto: "0x100" },
    { name: "CFG0",
      desc: "Configuration for Hart 0",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "11:0", name: "prescale", desc: "Prescaler to generate tick" },
        { bits: "23:16", name: "step", resval: "0x1", desc: "Incremental value for each tick" },
      ],
    },
    // ...
    { multireg: {
        name: "INTR_ENABLE0",
        desc: "Interrupt Enable",
        count: 2,
        cname: "TIMER",
        swaccess: "rw",
        hwaccess: "hro",
        fields: [
          { bits: "0", name: "IE", desc: "Interrupt Enable for timer" }
        ]
      }
    },
    { multireg: {
        name: "INTR_STATE0",
        desc: "Interrupt Status",
        count: 2,
        cname: "TIMER",
        swaccess: "ro",
        hwaccess: "hrw",
        fields: [
          { bits: "0", name: "IS", desc: "Interrupt status for timer" }
        ],
      }
    },
    // ...
    { skipto: "0x200" },
    { name: "CFG1",
      desc: "Configuration for Hart 1",
      swaccess: "rw",
      hwaccess: "hro",
      fields: [
        { bits: "11:0", name: "prescale", desc: "Prescaler to generate tick" },
        { bits: "23:16", name: "step", resval: "0x1", desc: "Incremental value for each tick" },
      ],
    },
    // ...
    { name: "TIMER_V_UPPER1",
      desc: "Timer value Upper",
      swaccess: "rw",
      hwaccess: "hrw",
      fields: [
        { bits: "31:0", name: "v", desc: "Timer value [63:32]" },
      ],
    },
    // ...
}
```
