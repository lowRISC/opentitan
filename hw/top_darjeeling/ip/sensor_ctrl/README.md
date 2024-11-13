# Sensor Control Technical Specification

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
