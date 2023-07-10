# Earl Grey HWIP

The Earl Grey ASIC is constructed from a number of OpenTitan [HWIP blocks](../../../ip/README.md) which follow the [lowRISC comportability specification](../../../../doc/contributing/hw/comportability/README.md).
An overview of the blocks used for Earl Grey can be found in the [Earl Grey Datasheet](../datasheet.md), and an overview of all the HWIP blocks can be found [on this page](../../../ip/README.md).

However, there are some blocks which are specific to the Earl Grey top-level or are parameterized extensively for Earl Grey in a way that deserves independent documentation.

- [Analog Sensor Top (AST)](../../ip/ast/README.md) : Earl Grey analog and security companion.
- [Sensor Control](../../ip/sensor_ctrl/README.md) : Comportable front-end to the AST.

The pinmux HWIP block is heavily parameterized for the Earl Grey application, and the details of the pinout can be found below.
- [Pinmux Targets](../../ip/pinmux/doc/autogen/targets.md)
