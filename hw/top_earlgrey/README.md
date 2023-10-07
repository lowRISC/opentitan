# Earl Grey

Earl Grey is the first OpenTitan 'top', and is designed as a discrete System-on-Chip (SoC).
It functions as a low-power secure microcontroller that is designed for several use cases requiring hardware security.

- [Datasheet](./doc/datasheet.md)
- [Design Specification](./doc/design/README.md)
- [Design Verification](./dv/README.md)
  - [Verification Dashboard](https://opentitan.org/dashboard/index.html#top)
  - [Chip-Level Simulations](https://reports.opentitan.org/hw/top_earlgrey/dv/latest/report.html)
- [Top Generation](./doc/design/top_generation.md)

It achieved RTL freeze in June, 2023: [opensource.googleblog/opentitan-rtl-freeze.html](https://opensource.googleblog.com/2023/06/opentitan-rtl-freeze.html.html)

More details about Use Cases for OpenTitan can be found [here](../../doc/use_cases/README.md).

![earl_grey](./doc/earlgrey.png)

The Earl Grey SoC is assembled by our in-house tool [topgen](../../util/topgen/README.md).
Details of how this tool is used specifically for Earl Grey can be found [here](./doc/design/top_generation.md).
