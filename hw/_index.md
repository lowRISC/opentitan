# Hardware Specifications

This is the landing spot for all hardware specifications within the OpenTitan project.
This includes: top level specification(s); processor core(s) specifications; and [Comportable IP]({{< relref "doc/rm/comportability_specification" >}}) specifications.

## Available Top Level Specifications

* [`top_earlgrey` design specification]({{< relref "hw/top_earlgrey/doc" >}})

## Available Processor Core Specifications

* [`core_ibex` user manual](https://ibex-core.readthedocs.io/en/latest)

## Available Comportable IP Block Design Specifications and Verification Plans

| Module | Design Spec | DV Plan |
|--------|-------------|---------|
| aes            | [design spec]({{< relref "hw/ip/aes/doc" >}})
| alert\_handler | [design spec]({{< relref "hw/ip/alert_handler/doc" >}})
| entropy\_src   |
| flash\_ctrl    | [design spec]({{< relref "hw/ip/flash_ctrl/doc" >}})
| gpio           | [design spec]({{< relref "hw/ip/gpio/doc" >}}) | [DV plan]({{< relref "hw/ip/gpio/doc/dv_plan" >}})
| hmac           | [design spec]({{< relref "hw/ip/hmac/doc" >}}) | [DV plan]({{< relref "hw/ip/hmac/doc/dv_plan" >}})
| i2c            | | [DV plan]({{< relref "hw/ip/i2c/doc/dv_plan" >}})
| padctrl        |[design spec]({{< relref "hw/ip/padctrl/doc" >}})
| pinmux         |[design spec]({{< relref "hw/ip/pinmux/doc" >}})
| rv\_core\_ibex |[design spec]({{< relref "hw/ip/rv_core_ibex/doc" >}})
| rv\_dm         |[design spec]({{< relref "hw/ip/rv_dm/doc" >}})
| rv\_plic       |[design spec]({{< relref "hw/ip/rv_plic/doc" >}})
| rv\_timer      |[design spec]({{< relref "hw/ip/rv_timer/doc" >}}) | [DV plan]({{< relref "hw/ip/rv_timer/doc/dv_plan" >}})
| spi\_device    |[design spec]({{< relref "hw/ip/spi_device/doc" >}})
| tlul           |[design spec]({{< relref "hw/ip/tlul/doc" >}})
| uart           |[design spec]({{< relref "hw/ip/uart/doc" >}}) | [DV plan]({{< relref "hw/ip/uart/doc/dv_plan" >}})
