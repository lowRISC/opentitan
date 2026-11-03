# Sensor Control Technical Specification

This IP has been taped out in Earl Grey 1.0.0. The corresponding documentation can be found [here](https://opentitan.org/earlgrey_1.0.0/book/hw/top_earlgrey/ip/sensor_ctrl/index.html).

# Overview

This document specifies the functionality of the `sensor control` module.
The `sensor control` module is a comportable front-end to the [analog sensor top](../ast/README.md).

It provides basic alert functionality, pad debug hook ups, and a small amount of open source visible status readback.
Long term, this is a module that can be absorbed directly into the `analog sensor top`.

## Features

- Alert hand-shake with `analog sensor top`
- Alert forwarding to `alert handler`
- Status readback for `analog sensor top`
- Pad debug hook up for `analog sensor top`
- Wakeup based on alert events
