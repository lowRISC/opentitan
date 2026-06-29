# RRAM CTRL HWIP Technical Specification

# Overview

This document specifies the RRAM Controller hardware IP functionality.
The RRAM Controller is a comportable IP that controls the RRAM macro.
This block can be connected to the bus system, and offers similar functionality to the Flash Controller.
It must be used in conjunction with the RRAM Macro and cannot be used standalone.

## Features

The RRAM Controller supports read, and write commands to the RRAM macro.
It has two TL-UL interfaces. `tl_core` is used to access the register bank and the FIFOs and `tl_host` is a read-only interface to access data stored in the RRAM.
The RRAM Controller interacts with several other hardware IPs such as the life cycle controller, OTP controller, and key manager.
