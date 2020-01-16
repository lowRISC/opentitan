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
| `aes`           | [design spec]({{< relref "hw/ip/aes/doc" >}})           | [DV plan]({{< relref "hw/ip/aes/doc/dv_plan" >}}) |
| `alert_handler` | [design spec]({{< relref "hw/ip/alert_handler/doc" >}}) | [DV plan]({{< relref "hw/ip/alert_handler/doc/dv_plan" >}}) |
| `entropy_src`   | [design spec]({{< relref "hw/ip/entropy_src/doc" >}})   | |
| `flash_ctrl`    | [design spec]({{< relref "hw/ip/flash_ctrl/doc" >}})    | |
| `gpio`          | [design spec]({{< relref "hw/ip/gpio/doc" >}})          | [DV plan]({{< relref "hw/ip/gpio/doc/dv_plan" >}}) |
| `hmac`          | [design spec]({{< relref "hw/ip/hmac/doc" >}})          | [DV plan]({{< relref "hw/ip/hmac/doc/dv_plan" >}}) |
| `i2c`           | [design spec]({{< relref "hw/ip/i2c/doc" >}})           | [DV plan]({{< relref "hw/ip/i2c/doc/dv_plan" >}})  |
| `nmi_gen`       | [design spec]({{< relref "hw/ip/nmi_gen/doc" >}})       | |
| `padctrl`       | [design spec]({{< relref "hw/ip/padctrl/doc" >}})       | |
| `pinmux`        | [design spec]({{< relref "hw/ip/pinmux/doc" >}})        | |
| `rv_core_ibex`  | [design spec]({{< relref "hw/ip/rv_core_ibex/doc" >}})  | |
| `rv_dm`         | [design spec]({{< relref "hw/ip/rv_dm/doc" >}})         | |
| `rv_plic`       | [design spec]({{< relref "hw/ip/rv_plic/doc" >}})       | [DV plan]({{< relref "hw/ip/rv_plic/doc/dv_plan" >}}) |
| `rv_timer`      | [design spec]({{< relref "hw/ip/rv_timer/doc" >}})      | [DV plan]({{< relref "hw/ip/rv_timer/doc/dv_plan" >}}) |
| `spi_device`    | [design spec]({{< relref "hw/ip/spi_device/doc" >}})    | [DV plan]({{< relref "hw/ip/spi_device/doc/dv_plan" >}}) |
| `tlul`          | [design spec]({{< relref "hw/ip/tlul/doc" >}})          | [DV plan]({{< relref "hw/ip/tlul/doc/dv_plan" >}})
| `uart`          | [design spec]({{< relref "hw/ip/uart/doc" >}})          | [DV plan]({{< relref "hw/ip/uart/doc/dv_plan" >}}) |
| `usbdev`        | [design spec]({{< relref "hw/ip/usbdev/doc" >}})        | [DV plan]({{< relref "hw/ip/usbdev/doc/dv_plan" >}}) |
