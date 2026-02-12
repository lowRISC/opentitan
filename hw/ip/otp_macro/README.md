# OTP MACRO HWIP Technical Specification

# Overview

This document specifies the OTP MACRO hardware IP functionality.
The OTP MACRO is a comportable IP that wraps an OTP macro.
This block is expected to be used in conjunction with an OTP Controller, and most of the features of the macro correspond to features of the controller.

## Features

The OTP MACRO wraps a one-time-programmable memory block, which can be either a simulation model, or a vendor specific macro cell.
The wrapper features a CSR block for vendor specific operations.
