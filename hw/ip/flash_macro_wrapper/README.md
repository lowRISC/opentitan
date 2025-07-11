# FLASH MACRO WRAPPER HWIP Technical Specification

# Overview

This document specifies the FLASH MACRO WRAPPER hardware IP functionality.
The FLASH MACRO WRAPPER is a comportable IP that wraps one or more flash bank macros.
This block is expected to be used in conjunction with a Flash Controller, and most of the features of the macro wrapper correspond to features of the controller.

## Features

The FLASH MACRO WRAPPER wraps flash macros, which can be either a simulation model, or vendor specific macro cells.
The wrapper features a CSR block for vendor specific operations.
